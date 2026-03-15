"""Aivelo FTP Vault — Desktop Client.

Standalone desktop app with the full Manus-designed UI.
Backend connects to remote servers via FTP, FTPS, or SFTP.
Uses pywebview for a native window — no browser needed.

Requires: pip install flask paramiko pywebview cryptography
Build:    pyinstaller --onefile --windowed --name "AiveloFTP" aivelo_ftp.py
"""
import ftplib
import json
import os
import re
import ssl
import stat as stat_mod
import sys
import threading
from datetime import datetime
from io import BytesIO
from pathlib import Path, PurePosixPath
import base64
import shlex
import tempfile

try:
    from flask import Flask, request, jsonify, send_file, Response
except ImportError:
    print("ERROR: Flask is required but not installed.")
    print("Install dependencies: pip install flask paramiko pywebview cryptography")
    sys.exit(1)

try:
    import paramiko
    HAS_PARAMIKO = True
except ImportError:
    HAS_PARAMIKO = False

APP_NAME = "Aivelo FTP Vault"
APP_VERSION = "2.1"
PORT = 7719

if getattr(sys, 'frozen', False):
    SCRIPT_DIR = Path(sys.executable).parent
else:
    SCRIPT_DIR = Path(__file__).resolve().parent

if sys.platform == "win32":
    CONFIG_DIR = Path(os.environ.get("APPDATA", Path.home())) / "AiveloFTP"
else:
    CONFIG_DIR = Path.home() / ".aiveloftp"
CONFIG_DIR.mkdir(parents=True, exist_ok=True)

# ── Logging ──
import logging
from logging.handlers import RotatingFileHandler
_log = logging.getLogger("aivelo")
_log.setLevel(logging.DEBUG)
_log_file = CONFIG_DIR / "aivelo.log"
try:
    _fh = RotatingFileHandler(str(_log_file), maxBytes=1_048_576, backupCount=3)
    _fh.setLevel(logging.DEBUG)
    _fh.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s", datefmt="%Y-%m-%d %H:%M:%S"))
    _log.addHandler(_fh)
except Exception:
    pass  # If we can't create a log file, continue without file logging

CONFIG_PATH = CONFIG_DIR / "config.json"

def load_config():
    if CONFIG_PATH.exists():
        try: return json.loads(CONFIG_PATH.read_text())
        except (json.JSONDecodeError, OSError) as e:
            _log.warning("Failed to load config: %s", e)
    return {"bookmarks": [], "launch_count": 0, "pro_key": ""}

def save_config(cfg):
    CONFIG_PATH.write_text(json.dumps(cfg, indent=2))

def increment_launch():
    """Increment launch counter and return current count."""
    c = load_config()
    c["launch_count"] = c.get("launch_count", 0) + 1
    save_config(c)
    return c["launch_count"], c.get("pro_key", "")

import hashlib

def validate_pro_key(key):
    """Validate a license key via server-side check with local cache.

    Security model: the server signs the activation token with an RSA private
    key. The client embeds the corresponding public key and cryptographically
    verifies the signature. A locally forged activation.json will fail the
    RSA signature check because the attacker does not have the private key."""
    if not key or not key.strip():
        return False
    key = key.strip().upper()

    # Check format: AIVELO-XXXX-XXXX-XXXX-XXXX-XXXX
    clean = key.replace("-", "")
    if not clean.startswith("AIVELO") or len(clean) != 26:
        return False

    # Check local activation cache first
    cached = _check_activation_cache(key)
    if cached == "valid":
        return True

    # Attempt server-side validation (always required for fresh activation)
    try:
        import urllib.request
        url = "https://www.martijnbenders.nl/aivelo-api/v1/license/validate"
        payload = json.dumps({"key": key, "machine_id": _get_machine_id()}).encode("utf-8")
        req = urllib.request.Request(url, data=payload,
            headers={"Content-Type": "application/json"}, method="POST")
        with urllib.request.urlopen(req, timeout=10) as resp:
            result = json.loads(resp.read().decode())
            if result.get("valid"):
                server_sig = result.get("signature", "")
                sig_timestamp = result.get("sig_timestamp", "")
                _store_activation_cache(key, server_sig, sig_timestamp)
                return True
            else:
                _clear_activation_cache(key)
                return False
    except Exception:
        # Server unreachable — only grant grace if we have a recent valid cache
        if cached == "expired_recent":
            return True
        return False


# ── Activation cache (RSA-signed tokens verified client-side) ──

_ACTIVATION_CACHE_PATH = CONFIG_DIR / "activation.json"
_CACHE_VALIDITY_DAYS = 30
_CACHE_GRACE_DAYS = 7  # extra days offline tolerance after expiry

# RSA public key for verifying server-signed activation tokens.
# The corresponding private key is held only on the license server.
# Changing this key requires updating both client and server.
_LICENSE_PUBLIC_KEY_PEM = """-----BEGIN PUBLIC KEY-----
MIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEAm1BzqNcNK3Zkx+A5UhW7
lfTUzGFfUirK59gUayoHVCKg0z4lctSp+QBD7HibtAL0/4FuO/huDfSEhpXGrqfe
HN+YZlNh229+ejn+As7+6A1KKXtDjExzjOhCzGKEdR6v4C93iaIO5dr3jJVVvC1L
BUTFy+ZUxUfBq9g4wdeZOobqTWa39OcqDbbKvXErlUibsrUvI6IT/npaayxGI/nv
oSFtqp6dubbaKkVlrM6AN0+V4conlJXNU8nTkEqMZrxAOTUz+jl5XJLTJ2TPavlX
xLkUAKnTnvsuRKkPHBd4Akh+TujCtOLPa5nhaTNqpZOVD24+bXqbxqQ33KU0dGZR
kwIDAQAB
-----END PUBLIC KEY-----"""

def _verify_server_signature(key, sig_timestamp, signature_b64):
    """Verify an RSA signature from the license server.
    The server signs 'KEY:timestamp' with its private key.
    We verify with the embedded public key. Returns True if valid."""
    try:
        import base64
        from cryptography.hazmat.primitives.asymmetric import padding
        from cryptography.hazmat.primitives import hashes, serialization
        pubkey = serialization.load_pem_public_key(_LICENSE_PUBLIC_KEY_PEM.encode())
        message = f"{key.upper()}:{sig_timestamp}".encode()
        sig_bytes = base64.b64decode(signature_b64)
        pubkey.verify(sig_bytes, message, padding.PKCS1v15(), hashes.SHA256())
        return True
    except Exception:
        return False

def _check_activation_cache(key):
    """Check local activation cache. Returns 'valid', 'expired_recent', or 'invalid'.

    The cache contains an RSA signature created by the license server.
    The client verifies this signature using the embedded public key.
    A forged activation.json will fail because the attacker cannot produce
    a valid RSA signature without the server's private key."""
    try:
        if not _ACTIVATION_CACHE_PATH.exists():
            return "invalid"
        cache = json.loads(_ACTIVATION_CACHE_PATH.read_text())
        stored_key = cache.get("key", "")
        if stored_key.upper() != key.upper():
            return "invalid"
        activated_at = cache.get("activated_at", 0)
        signature = cache.get("signature", "")
        sig_timestamp = cache.get("sig_timestamp", "")
        machine_id = cache.get("machine_id", "")

        # Must have a signature
        if not signature or not sig_timestamp:
            return "invalid"

        # Machine binding: cache is only valid on the machine that activated
        if machine_id != _get_machine_id():
            return "invalid"

        # Cryptographic verification: RSA signature must match
        if not _verify_server_signature(stored_key, sig_timestamp, signature):
            return "invalid"

        # Check expiry (based on when the client stored it, not sig_timestamp)
        age_days = (datetime.now().timestamp() - activated_at) / 86400
        if age_days <= _CACHE_VALIDITY_DAYS:
            return "valid"
        elif age_days <= _CACHE_VALIDITY_DAYS + _CACHE_GRACE_DAYS:
            return "expired_recent"
        else:
            return "invalid"
    except Exception:
        return "invalid"

def _get_machine_id():
    """Derive a stable machine identifier for cache binding."""
    import platform, getpass
    material = f"{getpass.getuser()}@{platform.node()}:{platform.system()}"
    return hashlib.sha256(material.encode()).hexdigest()[:16]

def _store_activation_cache(key, signature, sig_timestamp):
    """Store the server-signed activation token locally."""
    cache = {
        "key": key.upper(),
        "activated_at": datetime.now().timestamp(),
        "signature": signature,
        "sig_timestamp": sig_timestamp,
        "machine_id": _get_machine_id(),
    }
    try:
        _ACTIVATION_CACHE_PATH.write_text(json.dumps(cache, indent=2))
    except Exception:
        pass

def _clear_activation_cache(key):
    """Remove activation cache for a key the server rejected."""
    try:
        if _ACTIVATION_CACHE_PATH.exists():
            cache = json.loads(_ACTIVATION_CACHE_PATH.read_text())
            if cache.get("key", "").upper() == key.upper():
                _ACTIVATION_CACHE_PATH.unlink()
    except Exception:
        pass


# ═══════════════════════════════════════════════════════════
#  TRANSLATIONS — 10 Languages
# ═══════════════════════════════════════════════════════════

LANGUAGES = {
    "en": "English",
    "nl": "Nederlands",
    "es": "Español",
    "zh": "中文",
    "hi": "हिन्दी",
    "ar": "العربية",
    "pt": "Português",
    "fr": "Français",
    "ja": "日本語",
    "ru": "Русский",
    "de": "Deutsch",
}

T = {
  "en": {
    "connect_title": "Connect to your server",
    "connect_sub": "FTP, FTPS, or SFTP — your files, your server.",
    "host": "Host", "port": "Port", "username": "Username", "password": "Password",
    "connect": "Connect", "disconnect": "Disconnect",
    "save_vault": "Save to Encrypted Vault",
    "upgrade_pro": "Upgrade to AI Pro — €13.99 one-time",
    "secure_transfer": "Secure File Transfer",
    "secure_desc": "Connect to your own server. Upload, download, and manage files with confidence.",
    "feat_aes": "TLS/SSH encrypted connections",
    "feat_dual": "Dual-pane file browser",
    "feat_chmod": "Set file permissions (chmod)",
    "feat_fast": "Fast uploads and downloads",
    "secure_conn": "Secure connection", "file_integrity": "Encrypted transfer", "perm_ctrl": "Permission control",
    "local": "Local", "remote": "Remote",
    "drop_upload": "Drop files here or click to upload",
    "folder": "Folder", "rename": "Rename", "delete": "Delete",
    "dashboard": "Dashboard", "sync": "Sync", "gallery": "Gallery", "log": "Log", "vault": "Vault",
    "preview_edit": "Preview / Edit", "download_file": "Download file",
    "download_local": "Download to local folder", "upload_server": "Upload to server",
    "set_perms": "Set permissions (chmod)", "copy_path": "Copy path",
    "new_folder": "New folder here", "refresh": "Refresh",
    "zip_files": "Zip selected files", "unzip_here": "Unzip here",
    "open_folder": "Open folder",
    "server_dashboard": "Server Dashboard", "files": "Files", "folders": "Folders",
    "total_size": "Total Size", "file_types": "File Types",
    "largest_files": "Largest Files", "recently_modified": "Recently Modified",
    "server_info": "Server Info", "scan_errors": "Scan Errors",
    "folder_sync": "Folder Sync", "comparing": "Comparing folders...",
    "identical": "identical", "local_only": "local only", "remote_only": "remote only", "different": "different",
    "match": "Match", "local_only_label": "Local only", "remote_only_label": "Remote only", "different_label": "Different",
    "select_all": "Select all", "select_none": "Select none", "sync_selected": "Sync Selected",
    "compare_folders": "Compare local ↔ remote folders",
    "image_gallery": "Image Gallery", "loading_images": "Loading images...",
    "no_images": "No images found in this folder",
    "transfer_history": "Transfer History", "search": "Search...", "clear": "Clear",
    "no_history": "No transfer history yet",
    "create_zip": "Create ZIP Archive", "archive_name": "Archive name",
    "zip_sftp_note": "Zip files on the server (SFTP only)",
    "vault_title": "Encrypted Bookmark Vault",
    "vault_desc": "Enter your master password to unlock saved connections.",
    "master_password": "Master Password", "unlock": "Unlock",
    "vault_unlocked": "Vault unlocked! Your saved connections:",
    "vault_new": "New vault created! Save your first connection.",
    "no_bookmarks": "No saved connections yet. Connect to a server and click \"Save to Vault\".",
    "close": "Close", "cancel": "Cancel", "ok": "OK", "confirm": "Confirm", "apply": "Apply", "save": "Save",
    "edit": "Edit", "view_mode": "View",
    "pro_badge": "PRO UPGRADE AVAILABLE",
    "pro_title": "You're loving Aivelo FTP!",
    "pro_subtitle": "You've used the app {count} times. Unlock the full power with AI Pro.",
    "pro_features_nag": "🤖 AI File Assistant — search, analyze, and manage files with natural language\n🔍 Smart file search across your entire server\n📝 AI-powered code review and suggestions\n🧹 Intelligent cleanup recommendations\n⚡ Unlimited free updates",
    "pro_price": "€13.99", "pro_price_sub": "One-time payment · Lifetime license · No subscription",
    "get_pro": "Get AI Pro", "maybe_later": "Maybe later — continue free version",
    "pro_modal_title": "Aivelo FTP Vault Pro",
    "pro_modal_sub": "AI-powered file management for professionals",
    "feat_ai": "AI File Assistant — natural language file search & management",
    "feat_search": "Smart Search — \"find PHP files with mysql queries\"",
    "feat_review": "Code Review — AI analyzes your code for issues",
    "feat_cleanup": "Smart Cleanup — find unused files, old logs, duplicates",
    "feat_deps": "Dependency Check — find broken references in HTML/CSS",
    "feat_updates": "Lifetime Updates — free updates forever",
    "purchase_key": "Purchase License Key", "have_key": "Already have a key?",
    "activate": "Activate", "pro_active": "Pro Active",
    "owner": "Owner", "group": "Group", "others": "Others",
    "read": "Read", "write": "Write", "execute": "Execute",
    "set_permissions": "Set Permissions", "octal": "Octal",
    "new_folder_title": "New Folder", "enter_folder": "Enter folder name:",
    "delete_file": "Delete File", "delete_confirm": "Are you sure you want to delete \"{name}\"?",
    "delete_multi": "Delete {count} item(s)?",
    "rename_title": "Rename", "enter_name": "Enter new name:",
    "unsaved_title": "Unsaved Changes", "unsaved_msg": "You have unsaved changes. Close anyway?",
    "sync_confirm": "Sync {count} file(s)?\n\n⬆ Upload: {up}\n⬇ Download: {down}",
    "delete_bookmark": "Remove this saved connection from the vault?",
    "clear_history_confirm": "Delete all transfer history?",
    "connected": "Connected", "items_in": "items in",
    "scanning": "Scanning server... this may take a moment",
    "loading_preview": "Loading preview...",
    "binary_no_preview": "Preview not available for this file type",
    "modified": "Modified", "saved": "Saved", "truncated": "Truncated (file too large)",
    "syncing": "Syncing...", "saving": "Saving...",
    "lang_name": "English",
    "choose_language": "Choose Language",
  },
  "nl": {
    "connect_title": "Verbind met je server", "connect_sub": "FTP, FTPS of SFTP — jouw bestanden, jouw server.",
    "host": "Host", "port": "Poort", "username": "Gebruikersnaam", "password": "Wachtwoord",
    "connect": "Verbinden", "disconnect": "Verbreken",
    "save_vault": "Opslaan in versleutelde kluis", "upgrade_pro": "Upgrade naar AI Pro — eenmalig €13,99",
    "secure_transfer": "Veilige bestandsoverdracht", "secure_desc": "Maak veilig verbinding met je server.",
    "feat_aes": "TLS/SSH versleutelde verbindingen", "feat_dual": "Tweepaneel bestandsbrowser",
    "feat_chmod": "Bestandsrechten instellen", "feat_fast": "Snelle uploads en downloads",
    "secure_conn": "Beveiligde verbinding", "file_integrity": "Versleutelde overdracht", "perm_ctrl": "Rechtenbeheer",
    "local": "Lokaal", "remote": "Server", "drop_upload": "Sleep bestanden hierheen of klik om te uploaden",
    "folder": "Map", "rename": "Hernoemen", "delete": "Verwijderen",
    "dashboard": "Dashboard", "sync": "Synchroniseren", "gallery": "Galerij", "log": "Logboek", "vault": "Kluis",
    "preview_edit": "Voorbeeld / Bewerken", "download_file": "Bestand downloaden",
    "download_local": "Naar lokale map downloaden", "upload_server": "Uploaden naar server",
    "set_perms": "Rechten instellen", "copy_path": "Pad kopiëren",
    "new_folder": "Nieuwe map hier", "refresh": "Vernieuwen",
    "zip_files": "Geselecteerde bestanden comprimeren", "unzip_here": "Hier uitpakken",
    "open_folder": "Map openen",
    "server_dashboard": "Serverdashboard", "files": "Bestanden", "folders": "Mappen",
    "total_size": "Totale grootte", "file_types": "Bestandstypen",
    "largest_files": "Grootste bestanden", "recently_modified": "Recent gewijzigd",
    "server_info": "Serverinfo", "scan_errors": "Scanfouten",
    "folder_sync": "Mapsynchronisatie", "comparing": "Mappen worden vergeleken...",
    "identical": "identiek", "local_only": "alleen lokaal", "remote_only": "alleen server", "different": "verschillend",
    "match": "Gelijk", "local_only_label": "Alleen lokaal", "remote_only_label": "Alleen server", "different_label": "Verschil",
    "select_all": "Alles selecteren", "select_none": "Selectie opheffen", "sync_selected": "Geselecteerde synchroniseren",
    "compare_folders": "Lokale ↔ servermappen vergelijken",
    "image_gallery": "Afbeeldingengalerij", "loading_images": "Afbeeldingen laden...",
    "no_images": "Geen afbeeldingen gevonden",
    "transfer_history": "Overdrachtsgeschiedenis", "search": "Zoeken...", "clear": "Wissen",
    "no_history": "Geen overdrachtsgeschiedenis",
    "create_zip": "ZIP-archief maken", "archive_name": "Archiefnaam",
    "zip_sftp_note": "Bestanden comprimeren op de server (alleen SFTP)",
    "vault_title": "Versleutelde bladwijzerkluis",
    "vault_desc": "Voer je hoofdwachtwoord in om opgeslagen verbindingen te ontgrendelen.",
    "master_password": "Hoofdwachtwoord", "unlock": "Ontgrendelen",
    "vault_unlocked": "Kluis ontgrendeld!", "vault_new": "Nieuwe kluis aangemaakt!",
    "no_bookmarks": "Geen opgeslagen verbindingen.",
    "close": "Sluiten", "cancel": "Annuleren", "ok": "OK", "confirm": "Bevestigen", "apply": "Toepassen", "save": "Opslaan",
    "edit": "Bewerken", "view_mode": "Weergave",
    "pro_badge": "PRO-UPGRADE BESCHIKBAAR", "pro_title": "Je bent fan van Aivelo FTP!",
    "pro_subtitle": "Je hebt de app {count} keer gebruikt. Ontgrendel alle functies met AI Pro.",
    "pro_price": "€13,99", "pro_price_sub": "Eenmalige betaling · Levenslange licentie · Geen abonnement",
    "get_pro": "AI Pro kopen", "maybe_later": "Misschien later",
    "purchase_key": "Licentiesleutel kopen", "have_key": "Al een sleutel?",
    "activate": "Activeren", "pro_active": "Pro Actief",
    "owner": "Eigenaar", "group": "Groep", "others": "Overig",
    "read": "Lezen", "write": "Schrijven", "execute": "Uitvoeren",
    "set_permissions": "Rechten instellen", "octal": "Octaal",
    "new_folder_title": "Nieuwe map", "enter_folder": "Voer mapnaam in:",
    "delete_file": "Bestand verwijderen", "delete_confirm": "Weet je zeker dat je \"{name}\" wilt verwijderen?",
    "delete_multi": "{count} item(s) verwijderen?",
    "rename_title": "Hernoemen", "enter_name": "Voer nieuwe naam in:",
    "unsaved_title": "Niet-opgeslagen wijzigingen", "unsaved_msg": "Er zijn niet-opgeslagen wijzigingen. Toch sluiten?",
    "sync_confirm": "{count} bestand(en) synchroniseren?\n\n⬆ Upload: {up}\n⬇ Download: {down}",
    "delete_bookmark": "Deze verbinding uit de kluis verwijderen?", "clear_history_confirm": "Alle geschiedenis wissen?",
    "connected": "Verbonden", "items_in": "items in", "scanning": "Server wordt gescand...",
    "loading_preview": "Voorbeeld laden...", "binary_no_preview": "Voorbeeld niet beschikbaar",
    "modified": "Gewijzigd", "saved": "Opgeslagen", "truncated": "Ingekort",
    "syncing": "Synchroniseren...", "saving": "Opslaan...",
    "lang_name": "Nederlands", "choose_language": "Kies je taal",
    "pro_modal_title": "Aivelo FTP Vault Pro", "pro_modal_sub": "AI-gestuurde bestandsbeheer voor professionals",
    "feat_ai": "AI-bestandsassistent", "feat_search": "Slim zoeken", "feat_review": "Code-review",
    "feat_cleanup": "Slim opruimen", "feat_deps": "Afhankelijkheidscontrole", "feat_updates": "Levenslange updates",
    "saved_logins": "Opgeslagen verbindingen", "select_saved": "Kies een opgeslagen verbinding",
    "connection_saved": "Verbinding opgeslagen (versleuteld)", "fill_host_user": "Vul eerst host en gebruikersnaam in",
  },
  "es": {
    "connect_title": "Conectar a tu servidor",
    "connect_sub": "FTP, FTPS o SFTP — tus archivos, tu servidor.",
    "host": "Servidor", "port": "Puerto", "username": "Usuario", "password": "Contraseña",
    "connect": "Conectar", "disconnect": "Desconectar",
    "save_vault": "Guardar en Bóveda Cifrada",
    "upgrade_pro": "Actualizar a AI Pro — €13,99 único",
    "secure_transfer": "Transferencia Segura",
    "secure_desc": "Conéctate a tu servidor. Sube, descarga y administra archivos con confianza.",
    "feat_aes": "Conexiones cifradas TLS/SSH",
    "feat_dual": "Explorador de archivos dual",
    "feat_chmod": "Establecer permisos (chmod)",
    "feat_fast": "Subidas y descargas rápidas",
    "secure_conn": "Conexión segura", "file_integrity": "Transferencia cifrada", "perm_ctrl": "Control de permisos",
    "local": "Local", "remote": "Remoto",
    "drop_upload": "Arrastra archivos aquí o haz clic para subir",
    "folder": "Carpeta", "rename": "Renombrar", "delete": "Eliminar",
    "dashboard": "Panel", "sync": "Sincronizar", "gallery": "Galería", "log": "Registro", "vault": "Bóveda",
    "preview_edit": "Vista previa / Editar", "download_file": "Descargar archivo",
    "download_local": "Descargar a carpeta local", "upload_server": "Subir al servidor",
    "set_perms": "Establecer permisos (chmod)", "copy_path": "Copiar ruta",
    "new_folder": "Nueva carpeta aquí", "refresh": "Actualizar",
    "zip_files": "Comprimir archivos seleccionados", "unzip_here": "Descomprimir aquí",
    "open_folder": "Abrir carpeta",
    "server_dashboard": "Panel del Servidor", "files": "Archivos", "folders": "Carpetas",
    "total_size": "Tamaño Total", "file_types": "Tipos de Archivo",
    "largest_files": "Archivos Más Grandes", "recently_modified": "Modificados Recientemente",
    "server_info": "Info del Servidor", "scan_errors": "Errores de Escaneo",
    "folder_sync": "Sincronización de Carpetas", "comparing": "Comparando carpetas...",
    "identical": "idénticos", "local_only": "solo local", "remote_only": "solo remoto", "different": "diferentes",
    "match": "Igual", "local_only_label": "Solo local", "remote_only_label": "Solo remoto", "different_label": "Diferente",
    "select_all": "Seleccionar todo", "select_none": "Deseleccionar", "sync_selected": "Sincronizar Selección",
    "compare_folders": "Comparar carpetas local ↔ remoto",
    "image_gallery": "Galería de Imágenes", "loading_images": "Cargando imágenes...",
    "no_images": "No se encontraron imágenes en esta carpeta",
    "transfer_history": "Historial de Transferencias", "search": "Buscar...", "clear": "Limpiar",
    "no_history": "Sin historial de transferencias",
    "create_zip": "Crear Archivo ZIP", "archive_name": "Nombre del archivo",
    "zip_sftp_note": "Comprimir archivos en el servidor (solo SFTP)",
    "vault_title": "Bóveda de Marcadores Cifrada",
    "vault_desc": "Introduce tu contraseña maestra para desbloquear conexiones guardadas.",
    "master_password": "Contraseña Maestra", "unlock": "Desbloquear",
    "vault_unlocked": "¡Bóveda desbloqueada! Tus conexiones guardadas:",
    "vault_new": "¡Nueva bóveda creada! Guarda tu primera conexión.",
    "no_bookmarks": "Sin conexiones guardadas. Conéctate a un servidor y haz clic en \"Guardar en Bóveda\".",
    "close": "Cerrar", "cancel": "Cancelar", "ok": "OK", "confirm": "Confirmar", "apply": "Aplicar", "save": "Guardar",
    "edit": "Editar", "view_mode": "Ver",
    "pro_badge": "ACTUALIZACIÓN PRO DISPONIBLE",
    "pro_title": "¡Te encanta Aivelo FTP!",
    "pro_subtitle": "Has usado la app {count} veces. Desbloquea todo el poder con AI Pro.",
    "pro_price": "€13,99", "pro_price_sub": "Pago único · Licencia de por vida · Sin suscripción",
    "get_pro": "Obtener AI Pro", "maybe_later": "Quizás después — continuar con versión gratuita",
    "pro_modal_title": "Aivelo FTP Vault Pro",
    "pro_modal_sub": "Gestión de archivos con IA para profesionales",
    "feat_ai": "Asistente de Archivos IA", "feat_search": "Búsqueda Inteligente",
    "feat_review": "Revisión de Código", "feat_cleanup": "Limpieza Inteligente",
    "feat_deps": "Verificación de Dependencias", "feat_updates": "Actualizaciones de por vida",
    "purchase_key": "Comprar Clave de Licencia", "have_key": "¿Ya tienes una clave?",
    "activate": "Activar", "pro_active": "Pro Activo",
    "owner": "Propietario", "group": "Grupo", "others": "Otros",
    "read": "Leer", "write": "Escribir", "execute": "Ejecutar",
    "set_permissions": "Establecer Permisos", "octal": "Octal",
    "new_folder_title": "Nueva Carpeta", "enter_folder": "Nombre de la carpeta:",
    "delete_file": "Eliminar Archivo", "delete_confirm": "¿Seguro que quieres eliminar \"{name}\"?",
    "delete_multi": "¿Eliminar {count} elemento(s)?",
    "rename_title": "Renombrar", "enter_name": "Nuevo nombre:",
    "unsaved_title": "Cambios Sin Guardar", "unsaved_msg": "Tienes cambios sin guardar. ¿Cerrar de todos modos?",
    "sync_confirm": "¿Sincronizar {count} archivo(s)?\n\n⬆ Subir: {up}\n⬇ Descargar: {down}",
    "delete_bookmark": "¿Eliminar esta conexión guardada de la bóveda?",
    "clear_history_confirm": "¿Eliminar todo el historial?",
    "connected": "Conectado", "items_in": "elementos en",
    "scanning": "Escaneando servidor... esto puede tomar un momento",
    "loading_preview": "Cargando vista previa...", "binary_no_preview": "Vista previa no disponible",
    "modified": "Modificado", "saved": "Guardado", "truncated": "Truncado (archivo muy grande)",
    "syncing": "Sincronizando...", "saving": "Guardando...",
    "lang_name": "Español", "choose_language": "Elegir Idioma",
  },
  "zh": {
    "connect_title": "连接到您的服务器",
    "connect_sub": "FTP、FTPS 或 SFTP — 您的文件，您的服务器。",
    "host": "主机", "port": "端口", "username": "用户名", "password": "密码",
    "connect": "连接", "disconnect": "断开",
    "save_vault": "保存到加密保管库",
    "upgrade_pro": "升级到 AI Pro — €13.99 一次性",
    "secure_transfer": "安全文件传输",
    "secure_desc": "连接到您的服务器。安全地上传、下载和管理文件。",
    "feat_aes": "TLS/SSH 加密连接", "feat_dual": "双面板文件浏览器",
    "feat_chmod": "设置文件权限 (chmod)", "feat_fast": "快速上传和下载",
    "secure_conn": "安全连接", "file_integrity": "加密传输", "perm_ctrl": "权限控制",
    "local": "本地", "remote": "远程",
    "drop_upload": "拖放文件到此处或点击上传",
    "folder": "文件夹", "rename": "重命名", "delete": "删除",
    "dashboard": "仪表板", "sync": "同步", "gallery": "图库", "log": "日志", "vault": "保管库",
    "preview_edit": "预览 / 编辑", "download_file": "下载文件",
    "download_local": "下载到本地文件夹", "upload_server": "上传到服务器",
    "set_perms": "设置权限 (chmod)", "copy_path": "复制路径",
    "new_folder": "在此新建文件夹", "refresh": "刷新",
    "zip_files": "压缩选中的文件", "unzip_here": "在此解压",
    "open_folder": "打开文件夹",
    "server_dashboard": "服务器仪表板", "files": "文件", "folders": "文件夹",
    "total_size": "总大小", "file_types": "文件类型",
    "largest_files": "最大的文件", "recently_modified": "最近修改",
    "server_info": "服务器信息", "scan_errors": "扫描错误",
    "folder_sync": "文件夹同步", "comparing": "正在比较文件夹...",
    "identical": "相同", "local_only": "仅本地", "remote_only": "仅远程", "different": "不同",
    "match": "匹配", "local_only_label": "仅本地", "remote_only_label": "仅远程", "different_label": "不同",
    "select_all": "全选", "select_none": "取消选择", "sync_selected": "同步所选",
    "compare_folders": "比较本地 ↔ 远程文件夹",
    "image_gallery": "图片库", "loading_images": "加载图片...",
    "no_images": "此文件夹中未找到图片",
    "transfer_history": "传输历史", "search": "搜索...", "clear": "清除",
    "no_history": "暂无传输历史",
    "create_zip": "创建 ZIP 压缩包", "archive_name": "压缩包名称",
    "zip_sftp_note": "在服务器上压缩文件（仅 SFTP）",
    "vault_title": "加密书签保管库",
    "vault_desc": "输入您的主密码以解锁保存的连接。",
    "master_password": "主密码", "unlock": "解锁",
    "vault_unlocked": "保管库已解锁！您保存的连接：",
    "vault_new": "新保管库已创建！保存您的第一个连接。",
    "no_bookmarks": "暂无保存的连接。连接到服务器并点击「保存到保管库」。",
    "close": "关闭", "cancel": "取消", "ok": "确定", "confirm": "确认", "apply": "应用", "save": "保存",
    "edit": "编辑", "view_mode": "查看",
    "pro_badge": "专业版升级可用",
    "pro_title": "您爱上了 Aivelo FTP！",
    "pro_subtitle": "您已使用该应用 {count} 次。使用 AI Pro 解锁全部功能。",
    "pro_price": "€13.99", "pro_price_sub": "一次性付款 · 终身许可 · 无订阅",
    "get_pro": "获取 AI Pro", "maybe_later": "稍后再说 — 继续使用免费版",
    "pro_modal_title": "Aivelo FTP Vault Pro", "pro_modal_sub": "面向专业人士的 AI 文件管理",
    "purchase_key": "购买许可密钥", "have_key": "已有密钥？",
    "activate": "激活", "pro_active": "Pro 已激活",
    "owner": "所有者", "group": "组", "others": "其他",
    "read": "读取", "write": "写入", "execute": "执行",
    "set_permissions": "设置权限", "octal": "八进制",
    "new_folder_title": "新建文件夹", "enter_folder": "输入文件夹名称：",
    "delete_file": "删除文件", "delete_confirm": "确定要删除「{name}」吗？",
    "delete_multi": "删除 {count} 个项目？",
    "rename_title": "重命名", "enter_name": "输入新名称：",
    "unsaved_title": "未保存的更改", "unsaved_msg": "您有未保存的更改。仍然关闭？",
    "sync_confirm": "同步 {count} 个文件？\n\n⬆ 上传：{up}\n⬇ 下载：{down}",
    "delete_bookmark": "从保管库中删除此保存的连接？",
    "clear_history_confirm": "删除所有传输历史？",
    "connected": "已连接", "items_in": "个项目在",
    "scanning": "正在扫描服务器...请稍候", "loading_preview": "加载预览...",
    "binary_no_preview": "此文件类型无法预览",
    "modified": "已修改", "saved": "已保存", "truncated": "已截断（文件过大）",
    "syncing": "同步中...", "saving": "保存中...",
    "lang_name": "中文", "choose_language": "选择语言",
  },
  "hi": {
    "connect_title": "अपने सर्वर से कनेक्ट करें",
    "connect_sub": "FTP, FTPS, या SFTP — आपकी फ़ाइलें, आपका सर्वर।",
    "host": "होस्ट", "port": "पोर्ट", "username": "उपयोगकर्ता नाम", "password": "पासवर्ड",
    "connect": "कनेक्ट", "disconnect": "डिस्कनेक्ट",
    "save_vault": "एन्क्रिप्टेड वॉल्ट में सहेजें",
    "upgrade_pro": "AI Pro में अपग्रेड करें — €13.99 एकमुश्त",
    "secure_transfer": "सुरक्षित फ़ाइल ट्रांसफ़र",
    "secure_desc": "अपने सर्वर से कनेक्ट करें। विश्वास के साथ फ़ाइलें अपलोड, डाउनलोड और प्रबंधित करें।",
    "feat_aes": "TLS/SSH एन्क्रिप्टेड कनेक्शन", "feat_dual": "डुअल-पेन फ़ाइल ब्राउज़र",
    "feat_chmod": "फ़ाइल अनुमतियाँ सेट करें (chmod)", "feat_fast": "तेज़ अपलोड और डाउनलोड",
    "secure_conn": "सुरक्षित कनेक्शन", "file_integrity": "एन्क्रिप्टेड ट्रांसफर", "perm_ctrl": "अनुमति नियंत्रण",
    "local": "स्थानीय", "remote": "रिमोट",
    "drop_upload": "फ़ाइलें यहाँ खींचें या अपलोड करने के लिए क्लिक करें",
    "folder": "फ़ोल्डर", "rename": "नाम बदलें", "delete": "हटाएं",
    "dashboard": "डैशबोर्ड", "sync": "सिंक", "gallery": "गैलरी", "log": "लॉग", "vault": "वॉल्ट",
    "preview_edit": "पूर्वावलोकन / संपादन", "download_file": "फ़ाइल डाउनलोड करें",
    "download_local": "स्थानीय फ़ोल्डर में डाउनलोड", "upload_server": "सर्वर पर अपलोड",
    "set_perms": "अनुमतियाँ सेट करें", "copy_path": "पथ कॉपी करें",
    "new_folder": "यहाँ नया फ़ोल्डर", "refresh": "रिफ़्रेश",
    "zip_files": "चयनित फ़ाइलें ज़िप करें", "unzip_here": "यहाँ अनज़िप करें",
    "open_folder": "फ़ोल्डर खोलें",
    "server_dashboard": "सर्वर डैशबोर्ड", "files": "फ़ाइलें", "folders": "फ़ोल्डर",
    "total_size": "कुल आकार", "file_types": "फ़ाइल प्रकार",
    "largest_files": "सबसे बड़ी फ़ाइलें", "recently_modified": "हाल ही में संशोधित",
    "server_info": "सर्वर जानकारी", "scan_errors": "स्कैन त्रुटियाँ",
    "folder_sync": "फ़ोल्डर सिंक", "comparing": "फ़ोल्डर की तुलना हो रही है...",
    "identical": "समान", "local_only": "केवल स्थानीय", "remote_only": "केवल रिमोट", "different": "भिन्न",
    "match": "मिलान", "local_only_label": "केवल स्थानीय", "remote_only_label": "केवल रिमोट", "different_label": "भिन्न",
    "select_all": "सभी चुनें", "select_none": "कोई नहीं चुनें", "sync_selected": "चयनित सिंक करें",
    "compare_folders": "स्थानीय ↔ रिमोट फ़ोल्डर की तुलना",
    "image_gallery": "छवि गैलरी", "loading_images": "छवियाँ लोड हो रही हैं...",
    "no_images": "इस फ़ोल्डर में कोई छवि नहीं मिली",
    "transfer_history": "ट्रांसफ़र इतिहास", "search": "खोजें...", "clear": "साफ़ करें",
    "no_history": "कोई ट्रांसफ़र इतिहास नहीं",
    "create_zip": "ZIP बनाएं", "archive_name": "आर्काइव नाम",
    "zip_sftp_note": "सर्वर पर फ़ाइलें ज़िप करें (केवल SFTP)",
    "vault_title": "एन्क्रिप्टेड बुकमार्क वॉल्ट",
    "vault_desc": "सहेजे गए कनेक्शन अनलॉक करने के लिए मास्टर पासवर्ड दर्ज करें।",
    "master_password": "मास्टर पासवर्ड", "unlock": "अनलॉक",
    "close": "बंद", "cancel": "रद्द", "ok": "ठीक", "confirm": "पुष्टि", "apply": "लागू", "save": "सहेजें",
    "edit": "संपादन", "view_mode": "देखें",
    "pro_badge": "प्रो अपग्रेड उपलब्ध", "pro_title": "आपको Aivelo FTP पसंद है!",
    "pro_subtitle": "आपने ऐप {count} बार उपयोग किया है। AI Pro से पूरी शक्ति अनलॉक करें।",
    "pro_price": "€13.99", "pro_price_sub": "एकमुश्त भुगतान · आजीवन लाइसेंस · कोई सदस्यता नहीं",
    "get_pro": "AI Pro प्राप्त करें", "maybe_later": "बाद में — मुफ़्त संस्करण जारी रखें",
    "purchase_key": "लाइसेंस कुंजी खरीदें", "have_key": "पहले से कुंजी है?",
    "activate": "सक्रिय करें", "pro_active": "Pro सक्रिय",
    "owner": "स्वामी", "group": "समूह", "others": "अन्य",
    "read": "पढ़ें", "write": "लिखें", "execute": "निष्पादित",
    "set_permissions": "अनुमतियाँ सेट करें", "octal": "ऑक्टल",
    "new_folder_title": "नया फ़ोल्डर", "enter_folder": "फ़ोल्डर नाम दर्ज करें:",
    "delete_file": "फ़ाइल हटाएं", "delete_confirm": "क्या आप \"{name}\" को हटाना चाहते हैं?",
    "rename_title": "नाम बदलें", "enter_name": "नया नाम दर्ज करें:",
    "connected": "कनेक्टेड", "items_in": "आइटम",
    "scanning": "सर्वर स्कैन हो रहा है...", "loading_preview": "पूर्वावलोकन लोड हो रहा है...",
    "modified": "संशोधित", "saved": "सहेजा गया", "syncing": "सिंक हो रहा है...", "saving": "सहेजा जा रहा है...",
    "lang_name": "हिन्दी", "choose_language": "भाषा चुनें",
    "vault_unlocked": "वॉल्ट अनलॉक!", "vault_new": "नया वॉल्ट बनाया!",
    "no_bookmarks": "कोई सहेजा गया कनेक्शन नहीं।", "binary_no_preview": "पूर्वावलोकन उपलब्ध नहीं",
    "delete_multi": "{count} आइटम हटाएं?", "unsaved_title": "सहेजे नहीं गए परिवर्तन",
    "unsaved_msg": "आपके पास सहेजे नहीं गए परिवर्तन हैं। फिर भी बंद करें?",
    "sync_confirm": "{count} फ़ाइलें सिंक करें?\n\n⬆ अपलोड: {up}\n⬇ डाउनलोड: {down}",
    "delete_bookmark": "इस कनेक्शन को वॉल्ट से हटाएं?", "clear_history_confirm": "सभी इतिहास हटाएं?",
    "truncated": "काटा गया (फ़ाइल बहुत बड़ी)", "pro_modal_title": "Aivelo FTP Vault Pro",
    "pro_modal_sub": "पेशेवरों के लिए AI फ़ाइल प्रबंधन",
    "feat_ai": "AI फ़ाइल सहायक", "feat_search": "स्मार्ट खोज", "feat_review": "कोड समीक्षा",
    "feat_cleanup": "स्मार्ट सफ़ाई", "feat_deps": "निर्भरता जांच", "feat_updates": "आजीवन अपडेट",
  },
  "ar": {
    "connect_title": "الاتصال بالخادم",
    "connect_sub": "FTP أو FTPS أو SFTP — ملفاتك، خادمك.",
    "host": "المضيف", "port": "المنفذ", "username": "اسم المستخدم", "password": "كلمة المرور",
    "connect": "اتصال", "disconnect": "قطع الاتصال",
    "save_vault": "حفظ في الخزنة المشفرة",
    "upgrade_pro": "الترقية إلى AI Pro — €13.99 مرة واحدة",
    "secure_transfer": "نقل آمن للملفات",
    "secure_desc": "اتصل بخادمك. ارفع وحمّل وأدر ملفاتك بثقة.",
    "feat_aes": "اتصالات مشفرة TLS/SSH", "feat_dual": "متصفح ملفات مزدوج",
    "feat_chmod": "تعيين أذونات الملفات", "feat_fast": "رفع وتحميل سريع",
    "secure_conn": "اتصال آمن", "file_integrity": "نقل مشفر", "perm_ctrl": "التحكم بالأذونات",
    "local": "محلي", "remote": "بعيد",
    "drop_upload": "اسحب الملفات هنا أو انقر للرفع",
    "folder": "مجلد", "rename": "إعادة تسمية", "delete": "حذف",
    "dashboard": "لوحة التحكم", "sync": "مزامنة", "gallery": "معرض", "log": "سجل", "vault": "خزنة",
    "preview_edit": "معاينة / تحرير", "download_file": "تحميل الملف",
    "download_local": "تحميل إلى مجلد محلي", "upload_server": "رفع إلى الخادم",
    "set_perms": "تعيين الأذونات", "copy_path": "نسخ المسار",
    "new_folder": "مجلد جديد هنا", "refresh": "تحديث",
    "zip_files": "ضغط الملفات المحددة", "unzip_here": "فك الضغط هنا",
    "open_folder": "فتح المجلد",
    "server_dashboard": "لوحة تحكم الخادم", "files": "ملفات", "folders": "مجلدات",
    "total_size": "الحجم الإجمالي", "file_types": "أنواع الملفات",
    "largest_files": "أكبر الملفات", "recently_modified": "المعدلة مؤخراً",
    "server_info": "معلومات الخادم", "scan_errors": "أخطاء الفحص",
    "folder_sync": "مزامنة المجلدات", "comparing": "جارٍ مقارنة المجلدات...",
    "identical": "متطابق", "local_only": "محلي فقط", "remote_only": "بعيد فقط", "different": "مختلف",
    "match": "مطابق", "local_only_label": "محلي فقط", "remote_only_label": "بعيد فقط", "different_label": "مختلف",
    "select_all": "تحديد الكل", "select_none": "إلغاء التحديد", "sync_selected": "مزامنة المحدد",
    "compare_folders": "مقارنة المجلدات المحلية ↔ البعيدة",
    "image_gallery": "معرض الصور", "loading_images": "جارٍ تحميل الصور...",
    "no_images": "لم يتم العثور على صور",
    "transfer_history": "سجل النقل", "search": "بحث...", "clear": "مسح",
    "no_history": "لا يوجد سجل نقل",
    "create_zip": "إنشاء أرشيف ZIP", "archive_name": "اسم الأرشيف",
    "zip_sftp_note": "ضغط الملفات على الخادم (SFTP فقط)",
    "vault_title": "خزنة الإشارات المشفرة",
    "vault_desc": "أدخل كلمة المرور الرئيسية لفتح الاتصالات المحفوظة.",
    "master_password": "كلمة المرور الرئيسية", "unlock": "فتح",
    "close": "إغلاق", "cancel": "إلغاء", "ok": "موافق", "confirm": "تأكيد", "apply": "تطبيق", "save": "حفظ",
    "edit": "تحرير", "view_mode": "عرض",
    "pro_badge": "ترقية PRO متاحة", "pro_title": "أنت تحب Aivelo FTP!",
    "pro_subtitle": "لقد استخدمت التطبيق {count} مرة. افتح كل الإمكانات مع AI Pro.",
    "pro_price": "€13.99", "pro_price_sub": "دفعة واحدة · ترخيص مدى الحياة · بدون اشتراك",
    "get_pro": "احصل على AI Pro", "maybe_later": "ربما لاحقاً",
    "purchase_key": "شراء مفتاح الترخيص", "have_key": "لديك مفتاح؟",
    "activate": "تفعيل", "pro_active": "Pro مفعّل",
    "owner": "المالك", "group": "المجموعة", "others": "آخرون",
    "read": "قراءة", "write": "كتابة", "execute": "تنفيذ",
    "set_permissions": "تعيين الأذونات", "octal": "ثماني",
    "new_folder_title": "مجلد جديد", "enter_folder": "أدخل اسم المجلد:",
    "delete_file": "حذف الملف", "delete_confirm": "هل تريد حذف \"{name}\"؟",
    "rename_title": "إعادة تسمية", "enter_name": "أدخل الاسم الجديد:",
    "connected": "متصل", "items_in": "عنصر في", "scanning": "جارٍ فحص الخادم...",
    "loading_preview": "جارٍ تحميل المعاينة...", "modified": "معدّل", "saved": "محفوظ",
    "syncing": "جارٍ المزامنة...", "saving": "جارٍ الحفظ...",
    "lang_name": "العربية", "choose_language": "اختر اللغة",
    "vault_unlocked": "تم فتح الخزنة!", "vault_new": "تم إنشاء خزنة جديدة!",
    "no_bookmarks": "لا توجد اتصالات محفوظة.", "binary_no_preview": "المعاينة غير متاحة",
    "delete_multi": "حذف {count} عنصر؟", "unsaved_title": "تغييرات غير محفوظة",
    "unsaved_msg": "لديك تغييرات غير محفوظة. هل تريد الإغلاق؟",
    "sync_confirm": "مزامنة {count} ملف؟\n\n⬆ رفع: {up}\n⬇ تحميل: {down}",
    "delete_bookmark": "إزالة هذا الاتصال من الخزنة؟", "clear_history_confirm": "حذف كل السجل؟",
    "truncated": "مقتطع (ملف كبير جداً)",
    "pro_modal_title": "Aivelo FTP Vault Pro", "pro_modal_sub": "إدارة ملفات بالذكاء الاصطناعي",
    "feat_ai": "مساعد الملفات الذكي", "feat_search": "بحث ذكي", "feat_review": "مراجعة الكود",
    "feat_cleanup": "تنظيف ذكي", "feat_deps": "فحص التبعيات", "feat_updates": "تحديثات مدى الحياة",
  },
  "pt": {
    "connect_title": "Conectar ao seu servidor", "connect_sub": "FTP, FTPS ou SFTP — seus arquivos, seu servidor.",
    "host": "Host", "port": "Porta", "username": "Usuário", "password": "Senha",
    "connect": "Conectar", "disconnect": "Desconectar",
    "save_vault": "Salvar no Cofre Criptografado", "upgrade_pro": "Upgrade para AI Pro — €13,99 único",
    "secure_transfer": "Transferência Segura", "secure_desc": "Conecte-se ao seu servidor com confiança.",
    "feat_aes": "Conexões criptografadas TLS/SSH", "feat_dual": "Navegador de arquivos duplo",
    "feat_chmod": "Definir permissões (chmod)", "feat_fast": "Uploads e downloads rápidos",
    "secure_conn": "Conexão segura", "file_integrity": "Transferência criptografada", "perm_ctrl": "Controle de permissões",
    "local": "Local", "remote": "Remoto", "drop_upload": "Arraste arquivos ou clique para enviar",
    "folder": "Pasta", "rename": "Renomear", "delete": "Excluir",
    "dashboard": "Painel", "sync": "Sincronizar", "gallery": "Galeria", "log": "Registro", "vault": "Cofre",
    "preview_edit": "Visualizar / Editar", "download_file": "Baixar arquivo",
    "download_local": "Baixar para pasta local", "upload_server": "Enviar ao servidor",
    "set_perms": "Definir permissões", "copy_path": "Copiar caminho",
    "new_folder": "Nova pasta aqui", "refresh": "Atualizar",
    "zip_files": "Compactar arquivos selecionados", "unzip_here": "Descompactar aqui",
    "open_folder": "Abrir pasta",
    "server_dashboard": "Painel do Servidor", "files": "Arquivos", "folders": "Pastas",
    "total_size": "Tamanho Total", "file_types": "Tipos de Arquivo",
    "largest_files": "Maiores Arquivos", "recently_modified": "Modificados Recentemente",
    "server_info": "Info do Servidor", "scan_errors": "Erros de Varredura",
    "folder_sync": "Sincronização de Pastas", "comparing": "Comparando pastas...",
    "identical": "idênticos", "local_only": "apenas local", "remote_only": "apenas remoto", "different": "diferentes",
    "match": "Igual", "local_only_label": "Apenas local", "remote_only_label": "Apenas remoto", "different_label": "Diferente",
    "select_all": "Selecionar tudo", "select_none": "Desmarcar", "sync_selected": "Sincronizar Seleção",
    "compare_folders": "Comparar pastas local ↔ remoto",
    "image_gallery": "Galeria de Imagens", "loading_images": "Carregando imagens...",
    "no_images": "Nenhuma imagem encontrada",
    "transfer_history": "Histórico de Transferências", "search": "Buscar...", "clear": "Limpar",
    "no_history": "Sem histórico de transferências",
    "create_zip": "Criar Arquivo ZIP", "archive_name": "Nome do arquivo",
    "zip_sftp_note": "Compactar no servidor (apenas SFTP)",
    "vault_title": "Cofre de Favoritos Criptografado",
    "vault_desc": "Digite sua senha mestra para desbloquear conexões salvas.",
    "master_password": "Senha Mestra", "unlock": "Desbloquear",
    "vault_unlocked": "Cofre desbloqueado!", "vault_new": "Novo cofre criado!",
    "no_bookmarks": "Nenhuma conexão salva.",
    "close": "Fechar", "cancel": "Cancelar", "ok": "OK", "confirm": "Confirmar", "apply": "Aplicar", "save": "Salvar",
    "edit": "Editar", "view_mode": "Ver",
    "pro_badge": "UPGRADE PRO DISPONÍVEL", "pro_title": "Você ama o Aivelo FTP!",
    "pro_subtitle": "Você usou o app {count} vezes. Desbloqueie todo o poder com AI Pro.",
    "pro_price": "€13,99", "pro_price_sub": "Pagamento único · Licença vitalícia · Sem assinatura",
    "get_pro": "Obter AI Pro", "maybe_later": "Talvez depois",
    "purchase_key": "Comprar Chave de Licença", "have_key": "Já tem uma chave?",
    "activate": "Ativar", "pro_active": "Pro Ativo",
    "owner": "Proprietário", "group": "Grupo", "others": "Outros",
    "read": "Ler", "write": "Escrever", "execute": "Executar",
    "set_permissions": "Definir Permissões", "octal": "Octal",
    "new_folder_title": "Nova Pasta", "enter_folder": "Nome da pasta:",
    "delete_file": "Excluir Arquivo", "delete_confirm": "Excluir \"{name}\"?",
    "delete_multi": "Excluir {count} item(ns)?",
    "rename_title": "Renomear", "enter_name": "Novo nome:",
    "unsaved_title": "Alterações Não Salvas", "unsaved_msg": "Alterações não salvas. Fechar mesmo assim?",
    "sync_confirm": "Sincronizar {count} arquivo(s)?\n\n⬆ Upload: {up}\n⬇ Download: {down}",
    "delete_bookmark": "Remover esta conexão do cofre?", "clear_history_confirm": "Limpar todo o histórico?",
    "connected": "Conectado", "items_in": "itens em", "scanning": "Verificando servidor...",
    "loading_preview": "Carregando...", "binary_no_preview": "Visualização não disponível",
    "modified": "Modificado", "saved": "Salvo", "truncated": "Truncado",
    "syncing": "Sincronizando...", "saving": "Salvando...",
    "lang_name": "Português", "choose_language": "Escolher Idioma",
    "pro_modal_title": "Aivelo FTP Vault Pro", "pro_modal_sub": "Gestão de arquivos com IA",
    "feat_ai": "Assistente de Arquivos IA", "feat_search": "Busca Inteligente", "feat_review": "Revisão de Código",
    "feat_cleanup": "Limpeza Inteligente", "feat_deps": "Verificação de Dependências", "feat_updates": "Atualizações vitalícias",
  },
  "fr": {
    "connect_title": "Connectez-vous à votre serveur", "connect_sub": "FTP, FTPS ou SFTP — vos fichiers, votre serveur.",
    "host": "Hôte", "port": "Port", "username": "Identifiant", "password": "Mot de passe",
    "connect": "Connexion", "disconnect": "Déconnexion",
    "save_vault": "Enregistrer dans le Coffre Chiffré", "upgrade_pro": "Passer à AI Pro — 13,99 € unique",
    "secure_transfer": "Transfert Sécurisé", "secure_desc": "Connectez-vous à votre serveur en toute confiance.",
    "feat_aes": "Connexions chiffrées TLS/SSH", "feat_dual": "Navigateur double panneau",
    "feat_chmod": "Définir les permissions", "feat_fast": "Uploads et downloads rapides",
    "secure_conn": "Connexion sécurisée", "file_integrity": "Transfert chiffré", "perm_ctrl": "Contrôle des permissions",
    "local": "Local", "remote": "Distant", "drop_upload": "Glissez des fichiers ici ou cliquez pour envoyer",
    "folder": "Dossier", "rename": "Renommer", "delete": "Supprimer",
    "dashboard": "Tableau de bord", "sync": "Synchroniser", "gallery": "Galerie", "log": "Journal", "vault": "Coffre",
    "preview_edit": "Aperçu / Modifier", "download_file": "Télécharger",
    "download_local": "Télécharger vers dossier local", "upload_server": "Envoyer au serveur",
    "set_perms": "Définir les permissions", "copy_path": "Copier le chemin",
    "new_folder": "Nouveau dossier ici", "refresh": "Actualiser",
    "zip_files": "Compresser les fichiers", "unzip_here": "Décompresser ici",
    "open_folder": "Ouvrir le dossier",
    "server_dashboard": "Tableau de Bord Serveur", "files": "Fichiers", "folders": "Dossiers",
    "total_size": "Taille Totale", "file_types": "Types de Fichiers",
    "largest_files": "Plus Gros Fichiers", "recently_modified": "Récemment Modifiés",
    "server_info": "Info Serveur", "scan_errors": "Erreurs d'Analyse",
    "folder_sync": "Synchronisation", "comparing": "Comparaison en cours...",
    "identical": "identiques", "local_only": "local seulement", "remote_only": "distant seulement", "different": "différents",
    "match": "Identique", "local_only_label": "Local seul", "remote_only_label": "Distant seul", "different_label": "Différent",
    "select_all": "Tout sélectionner", "select_none": "Tout désélectionner", "sync_selected": "Synchroniser",
    "compare_folders": "Comparer dossiers local ↔ distant",
    "image_gallery": "Galerie d'Images", "loading_images": "Chargement...",
    "no_images": "Aucune image trouvée",
    "transfer_history": "Historique des Transferts", "search": "Rechercher...", "clear": "Effacer",
    "no_history": "Aucun historique",
    "create_zip": "Créer une Archive ZIP", "archive_name": "Nom de l'archive",
    "zip_sftp_note": "Compresser sur le serveur (SFTP uniquement)",
    "vault_title": "Coffre de Favoris Chiffré",
    "vault_desc": "Entrez votre mot de passe maître pour débloquer les connexions.",
    "master_password": "Mot de Passe Maître", "unlock": "Déverrouiller",
    "vault_unlocked": "Coffre déverrouillé !", "vault_new": "Nouveau coffre créé !",
    "no_bookmarks": "Aucune connexion enregistrée.",
    "close": "Fermer", "cancel": "Annuler", "ok": "OK", "confirm": "Confirmer", "apply": "Appliquer", "save": "Enregistrer",
    "edit": "Modifier", "view_mode": "Voir",
    "pro_badge": "MISE À NIVEAU PRO DISPONIBLE", "pro_title": "Vous adorez Aivelo FTP !",
    "pro_subtitle": "Vous avez utilisé l'app {count} fois. Débloquez toute la puissance avec AI Pro.",
    "pro_price": "13,99 €", "pro_price_sub": "Paiement unique · Licence à vie · Sans abonnement",
    "get_pro": "Obtenir AI Pro", "maybe_later": "Peut-être plus tard",
    "purchase_key": "Acheter une Clé de Licence", "have_key": "Vous avez déjà une clé ?",
    "activate": "Activer", "pro_active": "Pro Actif",
    "owner": "Propriétaire", "group": "Groupe", "others": "Autres",
    "read": "Lecture", "write": "Écriture", "execute": "Exécution",
    "set_permissions": "Définir les Permissions", "octal": "Octal",
    "new_folder_title": "Nouveau Dossier", "enter_folder": "Nom du dossier :",
    "delete_file": "Supprimer le Fichier", "delete_confirm": "Supprimer \"{name}\" ?",
    "delete_multi": "Supprimer {count} élément(s) ?",
    "rename_title": "Renommer", "enter_name": "Nouveau nom :",
    "unsaved_title": "Modifications Non Enregistrées", "unsaved_msg": "Modifications non enregistrées. Fermer quand même ?",
    "sync_confirm": "Synchroniser {count} fichier(s) ?\n\n⬆ Envoi : {up}\n⬇ Téléchargement : {down}",
    "delete_bookmark": "Supprimer cette connexion du coffre ?", "clear_history_confirm": "Effacer tout l'historique ?",
    "connected": "Connecté", "items_in": "éléments dans", "scanning": "Analyse du serveur...",
    "loading_preview": "Chargement...", "binary_no_preview": "Aperçu non disponible",
    "modified": "Modifié", "saved": "Enregistré", "truncated": "Tronqué",
    "syncing": "Synchronisation...", "saving": "Enregistrement...",
    "lang_name": "Français", "choose_language": "Choisir la Langue",
    "pro_modal_title": "Aivelo FTP Vault Pro", "pro_modal_sub": "Gestion de fichiers par IA",
    "feat_ai": "Assistant Fichiers IA", "feat_search": "Recherche Intelligente", "feat_review": "Revue de Code",
    "feat_cleanup": "Nettoyage Intelligent", "feat_deps": "Vérification des Dépendances", "feat_updates": "Mises à jour à vie",
  },
  "ja": {
    "connect_title": "サーバーに接続", "connect_sub": "FTP、FTPS、またはSFTP — あなたのファイル、あなたのサーバー。",
    "host": "ホスト", "port": "ポート", "username": "ユーザー名", "password": "パスワード",
    "connect": "接続", "disconnect": "切断",
    "save_vault": "暗号化保管庫に保存", "upgrade_pro": "AI Proにアップグレード — €13.99 一回払い",
    "secure_transfer": "安全なファイル転送", "secure_desc": "サーバーに安全に接続してファイルを管理。",
    "feat_aes": "TLS/SSH暗号化接続", "feat_dual": "デュアルペインブラウザ",
    "feat_chmod": "ファイル権限の設定", "feat_fast": "高速アップロード・ダウンロード",
    "secure_conn": "安全な接続", "file_integrity": "暗号化転送", "perm_ctrl": "権限制御",
    "local": "ローカル", "remote": "リモート", "drop_upload": "ファイルをドラッグまたはクリックしてアップロード",
    "folder": "フォルダ", "rename": "名前変更", "delete": "削除",
    "dashboard": "ダッシュボード", "sync": "同期", "gallery": "ギャラリー", "log": "ログ", "vault": "保管庫",
    "preview_edit": "プレビュー / 編集", "download_file": "ファイルをダウンロード",
    "download_local": "ローカルフォルダにダウンロード", "upload_server": "サーバーにアップロード",
    "set_perms": "権限を設定", "copy_path": "パスをコピー",
    "new_folder": "ここに新しいフォルダ", "refresh": "更新",
    "zip_files": "選択ファイルを圧縮", "unzip_here": "ここで解凍",
    "open_folder": "フォルダを開く",
    "server_dashboard": "サーバーダッシュボード", "files": "ファイル", "folders": "フォルダ",
    "total_size": "合計サイズ", "file_types": "ファイルの種類",
    "largest_files": "最大のファイル", "recently_modified": "最近の変更",
    "server_info": "サーバー情報", "scan_errors": "スキャンエラー",
    "folder_sync": "フォルダ同期", "comparing": "フォルダを比較中...",
    "identical": "同一", "local_only": "ローカルのみ", "remote_only": "リモートのみ", "different": "異なる",
    "match": "一致", "local_only_label": "ローカルのみ", "remote_only_label": "リモートのみ", "different_label": "異なる",
    "select_all": "すべて選択", "select_none": "選択解除", "sync_selected": "選択を同期",
    "compare_folders": "ローカル ↔ リモートフォルダを比較",
    "image_gallery": "画像ギャラリー", "loading_images": "画像を読み込み中...",
    "no_images": "画像が見つかりません",
    "transfer_history": "転送履歴", "search": "検索...", "clear": "クリア",
    "no_history": "転送履歴はありません",
    "create_zip": "ZIPアーカイブを作成", "archive_name": "アーカイブ名",
    "zip_sftp_note": "サーバーでファイルを圧縮（SFTPのみ）",
    "vault_title": "暗号化ブックマーク保管庫",
    "vault_desc": "マスターパスワードを入力して保存された接続を解除します。",
    "master_password": "マスターパスワード", "unlock": "解除",
    "vault_unlocked": "保管庫を解除しました！", "vault_new": "新しい保管庫を作成しました！",
    "no_bookmarks": "保存された接続はありません。",
    "close": "閉じる", "cancel": "キャンセル", "ok": "OK", "confirm": "確認", "apply": "適用", "save": "保存",
    "edit": "編集", "view_mode": "表示",
    "pro_badge": "PROアップグレード利用可能", "pro_title": "Aivelo FTPをお気に入りです！",
    "pro_subtitle": "アプリを{count}回使用しました。AI Proですべての機能を解放しましょう。",
    "pro_price": "€13.99", "pro_price_sub": "一回払い · 永久ライセンス · サブスク不要",
    "get_pro": "AI Proを取得", "maybe_later": "後で — 無料版を続ける",
    "purchase_key": "ライセンスキーを購入", "have_key": "キーをお持ちですか？",
    "activate": "アクティベート", "pro_active": "Pro有効",
    "owner": "所有者", "group": "グループ", "others": "その他",
    "read": "読み取り", "write": "書き込み", "execute": "実行",
    "set_permissions": "権限を設定", "octal": "8進数",
    "new_folder_title": "新しいフォルダ", "enter_folder": "フォルダ名を入力：",
    "delete_file": "ファイルを削除", "delete_confirm": "「{name}」を削除しますか？",
    "delete_multi": "{count}件を削除しますか？",
    "rename_title": "名前変更", "enter_name": "新しい名前を入力：",
    "unsaved_title": "未保存の変更", "unsaved_msg": "未保存の変更があります。閉じますか？",
    "sync_confirm": "{count}ファイルを同期しますか？\n\n⬆ アップロード：{up}\n⬇ ダウンロード：{down}",
    "delete_bookmark": "この接続を保管庫から削除しますか？", "clear_history_confirm": "すべての履歴を削除しますか？",
    "connected": "接続済み", "items_in": "件（", "scanning": "サーバーをスキャン中...",
    "loading_preview": "プレビューを読み込み中...", "binary_no_preview": "プレビューできません",
    "modified": "変更あり", "saved": "保存済み", "truncated": "切り詰め",
    "syncing": "同期中...", "saving": "保存中...",
    "lang_name": "日本語", "choose_language": "言語を選択",
    "pro_modal_title": "Aivelo FTP Vault Pro", "pro_modal_sub": "AIによるファイル管理",
    "feat_ai": "AIファイルアシスタント", "feat_search": "スマート検索", "feat_review": "コードレビュー",
    "feat_cleanup": "スマートクリーンアップ", "feat_deps": "依存関係チェック", "feat_updates": "永久アップデート",
  },
  "ru": {
    "connect_title": "Подключение к серверу", "connect_sub": "FTP, FTPS или SFTP — ваши файлы, ваш сервер.",
    "host": "Хост", "port": "Порт", "username": "Логин", "password": "Пароль",
    "connect": "Подключить", "disconnect": "Отключить",
    "save_vault": "Сохранить в зашифрованном хранилище", "upgrade_pro": "Обновить до AI Pro — €13,99 разово",
    "secure_transfer": "Безопасная передача файлов", "secure_desc": "Подключайтесь к серверу с уверенностью.",
    "feat_aes": "Шифрование TLS/SSH", "feat_dual": "Двухпанельный проводник",
    "feat_chmod": "Установка прав доступа", "feat_fast": "Быстрая загрузка",
    "secure_conn": "Безопасное соединение", "file_integrity": "Зашифрованная передача", "perm_ctrl": "Контроль прав",
    "local": "Локальный", "remote": "Удалённый", "drop_upload": "Перетащите файлы или нажмите для загрузки",
    "folder": "Папка", "rename": "Переименовать", "delete": "Удалить",
    "dashboard": "Панель", "sync": "Синхронизация", "gallery": "Галерея", "log": "Журнал", "vault": "Хранилище",
    "preview_edit": "Просмотр / Редактирование", "download_file": "Скачать файл",
    "download_local": "Скачать в локальную папку", "upload_server": "Загрузить на сервер",
    "set_perms": "Установить права", "copy_path": "Копировать путь",
    "new_folder": "Новая папка здесь", "refresh": "Обновить",
    "zip_files": "Сжать выбранные файлы", "unzip_here": "Распаковать здесь",
    "open_folder": "Открыть папку",
    "server_dashboard": "Панель сервера", "files": "Файлы", "folders": "Папки",
    "total_size": "Общий размер", "file_types": "Типы файлов",
    "largest_files": "Крупнейшие файлы", "recently_modified": "Недавно изменённые",
    "server_info": "Инфо о сервере", "scan_errors": "Ошибки сканирования",
    "folder_sync": "Синхронизация папок", "comparing": "Сравнение папок...",
    "identical": "идентичные", "local_only": "только локально", "remote_only": "только удалённо", "different": "различные",
    "match": "Совпадение", "local_only_label": "Только локально", "remote_only_label": "Только удалённо", "different_label": "Различие",
    "select_all": "Выбрать все", "select_none": "Снять выбор", "sync_selected": "Синхронизировать",
    "compare_folders": "Сравнить локальные ↔ удалённые папки",
    "image_gallery": "Галерея изображений", "loading_images": "Загрузка изображений...",
    "no_images": "Изображения не найдены",
    "transfer_history": "История передач", "search": "Поиск...", "clear": "Очистить",
    "no_history": "История передач пуста",
    "create_zip": "Создать ZIP-архив", "archive_name": "Имя архива",
    "zip_sftp_note": "Сжать файлы на сервере (только SFTP)",
    "vault_title": "Зашифрованное хранилище",
    "vault_desc": "Введите мастер-пароль для доступа к сохранённым подключениям.",
    "master_password": "Мастер-пароль", "unlock": "Разблокировать",
    "vault_unlocked": "Хранилище разблокировано!", "vault_new": "Новое хранилище создано!",
    "no_bookmarks": "Нет сохранённых подключений.",
    "close": "Закрыть", "cancel": "Отмена", "ok": "OK", "confirm": "Подтвердить", "apply": "Применить", "save": "Сохранить",
    "edit": "Редактировать", "view_mode": "Просмотр",
    "pro_badge": "ДОСТУПНО ОБНОВЛЕНИЕ PRO", "pro_title": "Вам нравится Aivelo FTP!",
    "pro_subtitle": "Вы использовали приложение {count} раз. Разблокируйте всю мощь с AI Pro.",
    "pro_price": "€13,99", "pro_price_sub": "Одноразовый платёж · Пожизненная лицензия · Без подписки",
    "get_pro": "Получить AI Pro", "maybe_later": "Может позже",
    "purchase_key": "Купить лицензионный ключ", "have_key": "Уже есть ключ?",
    "activate": "Активировать", "pro_active": "Pro активен",
    "owner": "Владелец", "group": "Группа", "others": "Другие",
    "read": "Чтение", "write": "Запись", "execute": "Выполнение",
    "set_permissions": "Установить права", "octal": "Восьмеричный",
    "new_folder_title": "Новая папка", "enter_folder": "Имя папки:",
    "delete_file": "Удалить файл", "delete_confirm": "Удалить \"{name}\"?",
    "delete_multi": "Удалить {count} элемент(ов)?",
    "rename_title": "Переименовать", "enter_name": "Новое имя:",
    "unsaved_title": "Несохранённые изменения", "unsaved_msg": "Есть несохранённые изменения. Закрыть?",
    "sync_confirm": "Синхронизировать {count} файл(ов)?\n\n⬆ Загрузка: {up}\n⬇ Скачивание: {down}",
    "delete_bookmark": "Удалить подключение из хранилища?", "clear_history_confirm": "Очистить всю историю?",
    "connected": "Подключено", "items_in": "элементов в", "scanning": "Сканирование сервера...",
    "loading_preview": "Загрузка...", "binary_no_preview": "Предпросмотр недоступен",
    "modified": "Изменён", "saved": "Сохранено", "truncated": "Обрезано",
    "syncing": "Синхронизация...", "saving": "Сохранение...",
    "lang_name": "Русский", "choose_language": "Выбрать язык",
    "pro_modal_title": "Aivelo FTP Vault Pro", "pro_modal_sub": "ИИ-управление файлами для профессионалов",
    "feat_ai": "ИИ-ассистент файлов", "feat_search": "Умный поиск", "feat_review": "Обзор кода",
    "feat_cleanup": "Умная очистка", "feat_deps": "Проверка зависимостей", "feat_updates": "Пожизненные обновления",
  },
  "de": {
    "connect_title": "Mit Server verbinden", "connect_sub": "FTP, FTPS oder SFTP — Ihre Dateien, Ihr Server.",
    "host": "Host", "port": "Port", "username": "Benutzername", "password": "Passwort",
    "connect": "Verbinden", "disconnect": "Trennen",
    "save_vault": "Im verschlüsselten Tresor speichern", "upgrade_pro": "Auf AI Pro upgraden — 13,99 € einmalig",
    "secure_transfer": "Sichere Dateiübertragung", "secure_desc": "Verbinden Sie sich sicher mit Ihrem Server.",
    "feat_aes": "TLS/SSH-verschlüsselte Verbindungen", "feat_dual": "Zwei-Fenster-Dateibrowser",
    "feat_chmod": "Dateiberechtigungen setzen", "feat_fast": "Schnelle Uploads und Downloads",
    "secure_conn": "Sichere Verbindung", "file_integrity": "Verschlüsselte Übertragung", "perm_ctrl": "Berechtigungskontrolle",
    "local": "Lokal", "remote": "Remote", "drop_upload": "Dateien hierher ziehen oder klicken zum Hochladen",
    "folder": "Ordner", "rename": "Umbenennen", "delete": "Löschen",
    "dashboard": "Dashboard", "sync": "Synchronisieren", "gallery": "Galerie", "log": "Protokoll", "vault": "Tresor",
    "preview_edit": "Vorschau / Bearbeiten", "download_file": "Datei herunterladen",
    "download_local": "In lokalen Ordner laden", "upload_server": "Auf Server hochladen",
    "set_perms": "Berechtigungen setzen", "copy_path": "Pfad kopieren",
    "new_folder": "Neuer Ordner hier", "refresh": "Aktualisieren",
    "zip_files": "Ausgewählte Dateien komprimieren", "unzip_here": "Hier entpacken",
    "open_folder": "Ordner öffnen",
    "server_dashboard": "Server-Dashboard", "files": "Dateien", "folders": "Ordner",
    "total_size": "Gesamtgröße", "file_types": "Dateitypen",
    "largest_files": "Größte Dateien", "recently_modified": "Kürzlich Geändert",
    "server_info": "Server-Info", "scan_errors": "Scan-Fehler",
    "folder_sync": "Ordner-Synchronisation", "comparing": "Ordner werden verglichen...",
    "identical": "identisch", "local_only": "nur lokal", "remote_only": "nur remote", "different": "unterschiedlich",
    "match": "Gleich", "local_only_label": "Nur lokal", "remote_only_label": "Nur remote", "different_label": "Unterschied",
    "select_all": "Alle auswählen", "select_none": "Auswahl aufheben", "sync_selected": "Ausgewählte synchronisieren",
    "compare_folders": "Lokale ↔ Remote-Ordner vergleichen",
    "image_gallery": "Bildergalerie", "loading_images": "Bilder werden geladen...",
    "no_images": "Keine Bilder gefunden",
    "transfer_history": "Übertragungsverlauf", "search": "Suchen...", "clear": "Löschen",
    "no_history": "Kein Übertragungsverlauf",
    "create_zip": "ZIP-Archiv erstellen", "archive_name": "Archivname",
    "zip_sftp_note": "Dateien auf dem Server komprimieren (nur SFTP)",
    "vault_title": "Verschlüsselter Lesezeichen-Tresor",
    "vault_desc": "Master-Passwort eingeben, um gespeicherte Verbindungen zu entsperren.",
    "master_password": "Master-Passwort", "unlock": "Entsperren",
    "vault_unlocked": "Tresor entsperrt!", "vault_new": "Neuer Tresor erstellt!",
    "no_bookmarks": "Keine gespeicherten Verbindungen.",
    "close": "Schließen", "cancel": "Abbrechen", "ok": "OK", "confirm": "Bestätigen", "apply": "Anwenden", "save": "Speichern",
    "edit": "Bearbeiten", "view_mode": "Ansicht",
    "pro_badge": "PRO-UPGRADE VERFÜGBAR", "pro_title": "Sie lieben Aivelo FTP!",
    "pro_subtitle": "Sie haben die App {count} Mal genutzt. Schalten Sie alle Funktionen mit AI Pro frei.",
    "pro_price": "13,99 €", "pro_price_sub": "Einmalzahlung · Lebenslange Lizenz · Kein Abo",
    "get_pro": "AI Pro holen", "maybe_later": "Vielleicht später",
    "purchase_key": "Lizenzschlüssel kaufen", "have_key": "Bereits einen Schlüssel?",
    "activate": "Aktivieren", "pro_active": "Pro Aktiv",
    "owner": "Eigentümer", "group": "Gruppe", "others": "Andere",
    "read": "Lesen", "write": "Schreiben", "execute": "Ausführen",
    "set_permissions": "Berechtigungen setzen", "octal": "Oktal",
    "new_folder_title": "Neuer Ordner", "enter_folder": "Ordnername eingeben:",
    "delete_file": "Datei löschen", "delete_confirm": "\"{name}\" wirklich löschen?",
    "delete_multi": "{count} Element(e) löschen?",
    "rename_title": "Umbenennen", "enter_name": "Neuen Namen eingeben:",
    "unsaved_title": "Ungespeicherte Änderungen", "unsaved_msg": "Es gibt ungespeicherte Änderungen. Trotzdem schließen?",
    "sync_confirm": "{count} Datei(en) synchronisieren?\n\n⬆ Upload: {up}\n⬇ Download: {down}",
    "delete_bookmark": "Diese Verbindung aus dem Tresor entfernen?", "clear_history_confirm": "Gesamten Verlauf löschen?",
    "connected": "Verbunden", "items_in": "Elemente in", "scanning": "Server wird gescannt...",
    "loading_preview": "Vorschau wird geladen...", "binary_no_preview": "Vorschau nicht verfügbar",
    "modified": "Geändert", "saved": "Gespeichert", "truncated": "Abgeschnitten",
    "syncing": "Synchronisierung...", "saving": "Speicherung...",
    "lang_name": "Deutsch", "choose_language": "Sprache wählen",
    "pro_modal_title": "Aivelo FTP Vault Pro", "pro_modal_sub": "KI-gestützte Dateiverwaltung für Profis",
    "feat_ai": "KI-Dateiassistent", "feat_search": "Intelligente Suche", "feat_review": "Code-Review",
    "feat_cleanup": "Intelligente Bereinigung", "feat_deps": "Abhängigkeitsprüfung", "feat_updates": "Lebenslange Updates",
  },
}


# ═══════════════════════════════════════════════════════════
#  TRUST STORE — TOFU (Trust On First Use) for FTPS & SFTP
# ═══════════════════════════════════════════════════════════

_TRUST_STORE_PATH = CONFIG_DIR / "trusted_hosts.json"

def _load_trust_store():
    try:
        if _TRUST_STORE_PATH.exists():
            return json.loads(_TRUST_STORE_PATH.read_text())
    except Exception:
        pass
    return {}

def _save_trust_store(store):
    try:
        _TRUST_STORE_PATH.write_text(json.dumps(store, indent=2))
    except Exception:
        pass

def _get_trusted_fingerprint(host, port, proto):
    """Get the stored fingerprint for a host, or None if not yet trusted."""
    store = _load_trust_store()
    key = f"{proto}:{host}:{port}"
    entry = store.get(key)
    if entry:
        return entry.get("fingerprint")
    return None

def _store_trusted_fingerprint(host, port, proto, fingerprint):
    """Store a fingerprint as trusted (TOFU accept)."""
    store = _load_trust_store()
    key = f"{proto}:{host}:{port}"
    store[key] = {
        "fingerprint": fingerprint,
        "host": host,
        "port": port,
        "proto": proto,
        "trusted_at": datetime.now().isoformat(),
    }
    _save_trust_store(store)

def _remove_trusted_fingerprint(host, port, proto):
    """Remove a stored fingerprint (user chose to reject changed key)."""
    store = _load_trust_store()
    key = f"{proto}:{host}:{port}"
    store.pop(key, None)
    _save_trust_store(store)


class CertificateError(Exception):
    """Raised when a server certificate or host key fails verification."""
    def __init__(self, message, fingerprint, is_changed=False):
        super().__init__(message)
        self.fingerprint = fingerprint
        self.is_changed = is_changed


# ═══════════════════════════════════════════════════════════
#  CONNECTION CLASSES
# ═══════════════════════════════════════════════════════════

class FTPConn:
    def __init__(self):
        self.ftp = None
        self.host = self.username = ""
        self.port = 21
        self.proto = "FTP"
        self._password = ""
        self._use_tls = False
        self._trust_fp = None

    def connect(self, host, port, username, password, use_tls=False, trust_fingerprint=None):
        self.host, self.port, self.username = host, port, username
        self._password, self._use_tls, self._trust_fp = password, use_tls, trust_fingerprint
        self.proto = "FTPS" if use_tls else "FTP"
        if use_tls:
            # Step 1: Try with full verification first
            ctx = ssl.create_default_context()
            try:
                self.ftp = ftplib.FTP_TLS(context=ctx)
                self.ftp.connect(host, port, timeout=15)
                self.ftp.login(username, password)
                self.ftp.prot_p()
                # Cert verified by system CA — store fingerprint for reference
                cert_der = self.ftp.sock.getpeercert(binary_form=True)
                if cert_der:
                    fp = hashlib.sha256(cert_der).hexdigest().upper()
                    _store_trusted_fingerprint(host, port, "FTPS", fp)
                try: self.ftp.voidcmd("TYPE I")
                except Exception: pass
                return  # success with full verification
            except ssl.SSLCertVerificationError:
                # Step 2: Cert not trusted by system CA — get fingerprint
                try: self.ftp.close()
                except Exception: pass
                self.ftp = None

                # Connect without verification just to read the cert
                ctx_peek = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
                ctx_peek.check_hostname = False
                ctx_peek.verify_mode = ssl.CERT_NONE
                ftp_peek = ftplib.FTP_TLS(context=ctx_peek)
                try:
                    ftp_peek.connect(host, port, timeout=10)
                    cert_der = ftp_peek.sock.getpeercert(binary_form=True)
                    fp = hashlib.sha256(cert_der).hexdigest().upper() if cert_der else "UNKNOWN"
                finally:
                    try: ftp_peek.close()
                    except Exception: pass

                # Check TOFU trust store
                stored_fp = _get_trusted_fingerprint(host, port, "FTPS")
                if stored_fp and stored_fp == fp:
                    # Previously trusted, same fingerprint — allow
                    pass
                elif stored_fp and stored_fp != fp:
                    # CHANGED fingerprint — warn user
                    raise CertificateError(
                        f"FTPS certificate for {host}:{port} has CHANGED.\n"
                        f"Previous fingerprint: {stored_fp[:16]}...\n"
                        f"Current fingerprint:  {fp[:16]}...\n"
                        f"This could indicate a man-in-the-middle attack.",
                        fingerprint=fp, is_changed=True
                    )
                elif trust_fingerprint and trust_fingerprint == fp:
                    # User explicitly chose to trust this fingerprint
                    _store_trusted_fingerprint(host, port, "FTPS", fp)
                else:
                    # First time — ask user to confirm
                    raise CertificateError(
                        f"FTPS certificate for {host}:{port} is not trusted by your system.\n"
                        f"Fingerprint (SHA-256): {fp[:16]}...\n"
                        f"If you trust this server, you can accept this certificate.",
                        fingerprint=fp, is_changed=False
                    )

                # If we got here, fingerprint is trusted — connect with no-verify ctx
                ctx_trusted = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
                ctx_trusted.check_hostname = False
                ctx_trusted.verify_mode = ssl.CERT_NONE
                self.ftp = ftplib.FTP_TLS(context=ctx_trusted)
                self.ftp.connect(host, port, timeout=15)
                self.ftp.login(username, password)
                self.ftp.prot_p()
                try: self.ftp.voidcmd("TYPE I")
                except Exception: pass
                return
        else:
            self.ftp = ftplib.FTP()
        self.ftp.connect(host, port, timeout=15)
        self.ftp.login(username, password)
        try: self.ftp.voidcmd("TYPE I")
        except Exception: pass

    def disconnect(self):
        try: self.ftp.quit()
        except (OSError, ftplib.error_temp, ftplib.error_perm, AttributeError):
            try: self.ftp.close()
            except (OSError, AttributeError): pass
        self.ftp = None

    def reconnect(self):
        """Silently reconnect using stored credentials."""
        try: self.disconnect()
        except Exception: pass
        self.connect(self.host, self.port, self.username, self._password,
                     use_tls=self._use_tls, trust_fingerprint=self._trust_fp)

    @property
    def connected(self):
        if not self.ftp: return False
        try: self.ftp.voidcmd("NOOP"); return True
        except (OSError, ftplib.error_temp, ftplib.error_perm, AttributeError, EOFError): return False

    def ensure_connected(self):
        """Check connection and auto-reconnect if stale."""
        if self.connected:
            return True
        if self.host and self._password:
            try:
                self.reconnect()
                return True
            except Exception:
                return False
        return False

    def listdir(self, path):
        files = []
        try:
            for name, facts in self.ftp.mlsd(path):
                if name in (".", ".."): continue
                is_dir = facts.get("type", "").lower() in ("dir", "cdir", "pdir")
                size = int(facts.get("size", 0)) if not is_dir else 0
                mtime = ""
                m = facts.get("modify", "")
                if m:
                    try: mtime = datetime.strptime(m[:14], "%Y%m%d%H%M%S").strftime("%Y-%m-%d %H:%M")
                    except Exception: pass
                files.append({"name": name, "size": size, "mtime": mtime,
                              "is_dir": is_dir, "perms": facts.get("unix.mode", "")})
        except (ftplib.error_perm, AttributeError):
            lines = []
            self.ftp.retrlines(f"LIST {path}", lines.append)
            for line in lines:
                parts = line.split(None, 8)
                if len(parts) < 9: continue
                perms, _, _, _, sz, m1, m2, m3, nm = parts
                if nm in (".", ".."): continue
                is_dir = perms.startswith("d")
                try: size = int(sz)
                except (ValueError, TypeError): size = 0
                mtime = f"{m1} {m2} {m3}"
                files.append({"name": nm, "size": size, "mtime": mtime,
                              "is_dir": is_dir, "perms": perms[1:10]})
        files.sort(key=lambda f: (not f["is_dir"], f["name"].lower()))
        return files

    def pwd(self): return self.ftp.pwd()
    def cwd(self, p): self.ftp.cwd(p)

    def download_bytes(self, remote_path):
        buf = BytesIO()
        self.ftp.retrbinary(f"RETR {remote_path}", buf.write, blocksize=65536)
        buf.seek(0)
        return buf

    def download_head(self, remote_path, max_bytes=524288):
        """Download only the first max_bytes of a file (for preview).
        Returns (buf, truncated). truncated is True only if there was
        more data beyond the limit — a file exactly at the limit is NOT truncated."""
        buf = BytesIO()
        received = [0]
        hit_limit = [False]
        class _Abort(Exception): pass
        def _writer(chunk):
            if received[0] + len(chunk) > max_bytes:
                # Write up to the limit
                remaining = max_bytes - received[0]
                buf.write(chunk[:remaining])
                received[0] = max_bytes
                # There's more data in this chunk beyond the limit → truly truncated
                if len(chunk) > remaining:
                    hit_limit[0] = True
                raise _Abort()
            buf.write(chunk)
            received[0] += len(chunk)
        try:
            self.ftp.retrbinary(f"RETR {remote_path}", _writer, blocksize=65536)
            # Transfer completed without hitting limit → not truncated
        except _Abort:
            # We aborted, but was there really more data?
            # If the chunk that triggered _Abort had exactly the remaining bytes,
            # we can't tell yet. But since retrbinary would have sent more chunks
            # if there was more data, and we aborted mid-stream, hit_limit is
            # already set correctly above.
            pass
        except Exception:
            raise
        buf.seek(0)
        return buf, hit_limit[0]

    def upload_stream(self, remote_path, file_obj, progress_cb=None):
        """Upload from a file-like object (streaming, no full read into RAM)."""
        if progress_cb:
            def callback(data):
                progress_cb(len(data))
            self.ftp.storbinary(f"STOR {remote_path}", file_obj, blocksize=65536, callback=callback)
        else:
            self.ftp.storbinary(f"STOR {remote_path}", file_obj, blocksize=65536)

    def download_to_file(self, remote_path, local_path, progress_cb=None):
        """Download a remote file directly to a local file path (streaming)."""
        with open(local_path, "wb") as f:
            def write_cb(data):
                f.write(data)
                if progress_cb: progress_cb(len(data))
            self.ftp.retrbinary(f"RETR {remote_path}", write_cb, blocksize=65536)

    def upload_bytes(self, remote_path, data):
        buf = BytesIO(data)
        self.ftp.storbinary(f"STOR {remote_path}", buf, blocksize=65536)

    def mkdir(self, p): self.ftp.mkd(p)
    def rmdir(self, p): self.ftp.rmd(p)
    def remove(self, p): self.ftp.delete(p)
    def rename(self, o, n): self.ftp.rename(o, n)

    def is_dir(self, path):
        old = self.ftp.pwd()
        try:
            self.ftp.cwd(path)
            self.ftp.cwd(old)
            return True
        except Exception:
            return False


class SFTPConn:
    def __init__(self):
        self.transport = self.sftp = None
        self.host = self.username = ""
        self.port = 22
        self.proto = "SFTP"
        self._password = ""
        self._trust_fp = None

    def connect(self, host, port, username, password=None, trust_fingerprint=None):
        self.host, self.port, self.username = host, port, username
        self._password, self._trust_fp = password, trust_fingerprint

        # Step 1: Open transport to get the host key
        self.transport = paramiko.Transport((host, port))
        self.transport.connect()  # connect transport layer (no auth yet)

        # Step 2: Get the host key and compute fingerprint
        host_key = self.transport.get_remote_server_key()
        key_bytes = host_key.asbytes()
        fp = hashlib.sha256(key_bytes).hexdigest().upper()
        key_type = host_key.get_name()

        # Step 3: TOFU verification
        stored_fp = _get_trusted_fingerprint(host, port, "SFTP")
        if stored_fp and stored_fp == fp:
            # Known host, same key — good
            pass
        elif stored_fp and stored_fp != fp:
            # HOST KEY CHANGED — serious warning
            try: self.transport.close()
            except Exception: pass
            self.transport = None
            raise CertificateError(
                f"SFTP host key for {host}:{port} has CHANGED!\n"
                f"Key type: {key_type}\n"
                f"Previous fingerprint: {stored_fp[:16]}...\n"
                f"Current fingerprint:  {fp[:16]}...\n"
                f"This could indicate a man-in-the-middle attack.\n"
                f"If the server was recently reinstalled, you can accept the new key.",
                fingerprint=fp, is_changed=True
            )
        elif trust_fingerprint and trust_fingerprint == fp:
            # User explicitly accepted this fingerprint
            _store_trusted_fingerprint(host, port, "SFTP", fp)
        elif stored_fp is None:
            # First connection ever — ask user to verify
            try: self.transport.close()
            except Exception: pass
            self.transport = None
            raise CertificateError(
                f"SFTP host key for {host}:{port} is not yet trusted.\n"
                f"Key type: {key_type}\n"
                f"Fingerprint (SHA-256): {fp[:16]}...\n"
                f"If you trust this server, you can accept this key.",
                fingerprint=fp, is_changed=False
            )

        # Step 4: Authenticate
        self.transport.auth_password(username, password)
        self.sftp = paramiko.SFTPClient.from_transport(self.transport)

    def disconnect(self):
        try: self.sftp.close()
        except (OSError, AttributeError): pass
        try: self.transport.close()
        except (OSError, AttributeError): pass
        self.sftp = self.transport = None

    def reconnect(self):
        """Silently reconnect using stored credentials."""
        try: self.disconnect()
        except Exception: pass
        self.connect(self.host, self.port, self.username,
                     password=self._password, trust_fingerprint=self._trust_fp)

    @property
    def connected(self):
        return self.sftp and self.transport and self.transport.is_active()

    def ensure_connected(self):
        """Check connection and auto-reconnect if stale."""
        if self.connected:
            return True
        if self.host and self._password:
            try:
                self.reconnect()
                return True
            except Exception:
                return False
        return False

    def listdir(self, path):
        files = []
        for item in self.sftp.listdir_attr(path):
            is_dir = stat_mod.S_ISDIR(item.st_mode or 0)
            perms = ""
            if item.st_mode:
                m = item.st_mode & 0o777
                p = []
                for w in range(6, -1, -3):
                    p.append(("r" if m&(4<<w) else "-")+("w" if m&(2<<w) else "-")+("x" if m&(1<<w) else "-"))
                perms = "".join(p)
            mtime = ""
            if item.st_mtime:
                try: mtime = datetime.fromtimestamp(item.st_mtime).strftime("%Y-%m-%d %H:%M")
                except Exception: pass
            files.append({"name": item.filename, "size": item.st_size or 0,
                          "mtime": mtime, "is_dir": is_dir, "perms": perms})
        files.sort(key=lambda f: (not f["is_dir"], f["name"].lower()))
        return files

    def pwd(self): return self.sftp.normalize(".")

    def download_bytes(self, remote_path):
        buf = BytesIO()
        with self.sftp.open(remote_path, "rb") as f:
            while True:
                chunk = f.read(65536)
                if not chunk: break
                buf.write(chunk)
        buf.seek(0)
        return buf

    def download_head(self, remote_path, max_bytes=524288):
        """Download only the first max_bytes of a file (for preview)."""
        buf = BytesIO()
        truncated = False
        with self.sftp.open(remote_path, "rb") as f:
            remaining = max_bytes
            while remaining > 0:
                chunk = f.read(min(65536, remaining))
                if not chunk: break
                buf.write(chunk)
                remaining -= len(chunk)
            if remaining <= 0:
                # Check if there's more data
                extra = f.read(1)
                if extra:
                    truncated = True
        buf.seek(0)
        return buf, truncated

    def upload_stream(self, remote_path, file_obj, progress_cb=None):
        """Upload from a file-like object (streaming)."""
        with self.sftp.open(remote_path, "wb") as f:
            while True:
                chunk = file_obj.read(65536)
                if not chunk: break
                f.write(chunk)
                if progress_cb: progress_cb(len(chunk))

    def download_to_file(self, remote_path, local_path, progress_cb=None):
        """Download a remote file directly to a local file path (streaming)."""
        with self.sftp.open(remote_path, "rb") as rf:
            with open(local_path, "wb") as lf:
                while True:
                    chunk = rf.read(65536)
                    if not chunk: break
                    lf.write(chunk)
                    if progress_cb: progress_cb(len(chunk))

    def upload_bytes(self, remote_path, data):
        with self.sftp.open(remote_path, "wb") as f:
            f.write(data)

    def mkdir(self, p): self.sftp.mkdir(p)
    def rmdir(self, p): self.sftp.rmdir(p)
    def remove(self, p): self.sftp.remove(p)
    def rename(self, o, n): self.sftp.rename(o, n)

    def is_dir(self, path):
        try: return stat_mod.S_ISDIR(self.sftp.stat(path).st_mode or 0)
        except Exception: return False


# ═══════════════════════════════════════════════════════════
#  FLASK APP
# ═══════════════════════════════════════════════════════════

app = Flask(__name__)
conn = None  # active connection
_keepalive_timer = None

def _start_keepalive():
    """Send NOOP every 30s to prevent server idle timeout."""
    global _keepalive_timer
    if _keepalive_timer:
        _keepalive_timer.cancel()
    def _ping():
        global _keepalive_timer
        if conn:
            try:
                if hasattr(conn, 'ftp') and conn.ftp:
                    conn.ftp.voidcmd("NOOP")
                elif hasattr(conn, 'sftp') and conn.sftp:
                    conn.sftp.stat(".")
            except Exception:
                pass  # ensure_connected() will handle reconnect on next API call
        _keepalive_timer = threading.Timer(30, _ping)
        _keepalive_timer.daemon = True
        _keepalive_timer.start()
    _ping()

def _stop_keepalive():
    global _keepalive_timer
    if _keepalive_timer:
        _keepalive_timer.cancel()
        _keepalive_timer = None
cfg = load_config()

# ── Session Token (protects local API from unauthorized local processes) ──
import secrets as _secrets
_SESSION_TOKEN = _secrets.token_hex(32)

@app.before_request
def _check_session_token():
    """Require session token on all /api/ endpoints.
    The token is injected into the HTML page at load time. This blocks
    blind unauthenticated requests from other local processes. Note: a
    sophisticated local attacker could still extract the token by fetching
    the page from localhost, so this is a mitigation, not a hard boundary."""
    if request.path.startswith('/api/'):
        token = request.headers.get('X-Session-Token', '')
        if token != _SESSION_TOKEN:
            return jsonify({"error": "Invalid session token"}), 403

# Load logo as base64 for embedding
# Logos hardcoded as base64 — always works, no external files needed
LOGO_FULL = "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"
LOGO_ICON = "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"
LOGO_DECOR = "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"
DWARF_IMG = "R0lGODlhSgOuA/f/AI9WS8aZaWtcZsyMUIJye3x6eVBMTre3t01aZVQ0L+zGg3SCg3Fia2RBN+awc6imqbtzZjMsLO7EpcnHu7iLW2xiaf///6JnW4V4hZxjWOrp6MuDcszJxra2qtrZ2eu+o9qmjLyUan1tedSsad7dzrWNZb2UY8V7a9uocra6rXNJSdibhNy2duXk1JqWl8idc5CEdOvGfLlrYeLf0vTz886ka9bTxnp5dcuCbXlrdct8bIiGhJSJmXJFQnNJRMZ9S7RoXHVzc8ujdX1xfKqIZLNXVXZhTK2ZkhYVFaOXpe/LhOSoisV0anlNSmxDQGxlcnl1dadjTH1TSHNqcNizbHx4jKyts81zanxJQtOJeZ6dpbu7r8p7cufDgWFWXFdkb9vXy+u2mpd3WaWioLh1S4VmSMC+tNrXx2ZzeNHOwbuXe9fWzNWUfea6nMV0ZMZsZfPLhYZPQbCsqDMjHqZ6WLaSY+a1mouDlLaSariKd5teSLR4VSQYFdaDbbOyp+7DnpaTjnRlb+StkpKMjNN9duGfhNF5bYt1XPfHoqiVdea0luvHjYdpV6dpXrGytkc+QKp2ZmlVQXNxbOa9e3R0eX9UT7JrSrSttqKKc+OKcahyTbizr+u1luy6lru8v713bq2Sa72abHpFQvO+n8CaX0BESZ+AXdScYtSsYJZwTxUQDrlpcMTBw8R5ZXFseTc2OQ0KCN6WUr6hb8PDtXBFSdzbyotvTa2xptTP07rExnB6e/nSist7ZfLv7oKCfqGhqr9dWOe7lrSabXllcF9NU/Pz79/j0B8dHvbRmfHLjiEiI7JeXoBNTxkZHM1zZc7QzHV5c+fCjo6PihEMEG1ta5+emhAQEQkKCrSaZbq7pZKRk9Kvc8FudF9fXB4eGXZFSUBAPHVldQsPCuu6nu++n+u6mu+6nu+6muu+nuu+mu++mvv39/v7+/Pv83lleeHg37a6pvv3+65tbdHQ0e/v7+Pj495/c9JvZ9uSTLq2qvf39/O0hPf7+5NcVgEBAf///yH/C1hNUCBEYXRhWE1QPD94cGFja2V0IGJlZ2luPSLvu78iIGlkPSJXNU0wTXBDZWhpSHpyZVN6TlRjemtjOWQiPz4gPHg6eG1wbWV0YSB4bWxuczp4PSJhZG9iZTpuczptZXRhLyIgeDp4bXB0az0iQWRvYmUgWE1QIENvcmUgMTAuMC1jMDAwIDc5LmQyMGU0NjYzMCwgMjAyNS8xMi8wOS0wMjoxMToyMyAgICAgICAgIj4gPHJkZjpSREYgeG1sbnM6cmRmPSJodHRwOi8vd3d3LnczLm9yZy8xOTk5LzAyLzIyLXJkZi1zeW50YXgtbnMjIj4gPHJkZjpEZXNjcmlwdGlvbiByZGY6YWJvdXQ9IiIgeG1sbnM6eG1wPSJodHRwOi8vbnMuYWRvYmUuY29tL3hhcC8xLjAvIiB4bWxuczp4bXBNTT0iaHR0cDovL25zLmFkb2JlLmNvbS94YXAvMS4wL21tLyIgeG1sbnM6c3RSZWY9Imh0dHA6Ly9ucy5hZG9iZS5jb20veGFwLzEuMC9zVHlwZS9SZXNvdXJjZVJlZiMiIHhtcDpDcmVhdG9yVG9vbD0iQWRvYmUgUGhvdG9zaG9wIDI3LjUgKDIwMjYwMzAxLm0uMzQzOCBlYWFhYjY2KSAgKFdpbmRvd3MpIiB4bXBNTTpJbnN0YW5jZUlEPSJ4bXAuaWlkOkE4QjY1OTUyMTdEMjExRjFCMDIwQzg3NTk1RDFCREVGIiB4bXBNTTpEb2N1bWVudElEPSJ4bXAuZGlkOkE4QjY1OTUzMTdEMjExRjFCMDIwQzg3NTk1RDFCREVGIj4gPHhtcE1NOkRlcml2ZWRGcm9tIHN0UmVmOmluc3RhbmNlSUQ9InhtcC5paWQ6QThCNjU5NTAxN0QyMTFGMUIwMjBDODc1OTVEMUJERUYiIHN0UmVmOmRvY3VtZW50SUQ9InhtcC5kaWQ6QThCNjU5NTExN0QyMTFGMUIwMjBDODc1OTVEMUJERUYiLz4gPC9yZGY6RGVzY3JpcHRpb24+IDwvcmRmOlJERj4gPC94OnhtcG1ldGE+IDw/eHBhY2tldCBlbmQ9InIiPz4B//79/Pv6+fj39vX08/Lx8O/u7ezr6uno5+bl5OPi4eDf3t3c29rZ2NfW1dTT0tHQz87NzMvKycjHxsXEw8LBwL++vby7urm4t7a1tLOysbCvrq2sq6qpqKempaSjoqGgn56dnJuamZiXlpWUk5KRkI+OjYyLiomIh4aFhIOCgYB/fn18e3p5eHd2dXRzcnFwb25tbGtqaWhnZmVkY2JhYF9eXVxbWllYV1ZVVFNSUVBPTk1MS0pJSEdGRURDQkFA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2PBzQ5F1Mds9aRc79pEqOarOXzel85dye8TG107v1AacgQcimKCCCzI4lQXr0ENcX8aNxVx/r7HFGn9tKReXhdSplhFHJ4mIkl7koZiiiiuy2OJhczAT2UIhMYRFE5YpVGMTEVmUUIklbjgXdiX6IJ9+161kloY+0DJSgF3t5EGBDVJZpZVXYgkcO1ty2SWX6+gDZphf0tDLOwX8NUdY0bG53H8eCplfdUnCVFZbdOnXnl0FWTaHi38CGqiggxLG/wdYtHzEUWRFFpmRow4dhNCOk+6oQhMjXXrkew3t6MOlmT6kqah3NVEqpQ1982ROO3FQDDsWwMqlBa/CWqutPv1zq61CwZrUrlkCG6ywwwbFASscIIuLssviwgEux7ISrbPKIstKBX9dYxMs2247jbfTwAIut9tme02546Ib7rfgspsuutmOy+6689LrrSrT3Huvt+LQaw24hAIcsMADg4duu92Gq663Cuv7rbsPQ9wtvgkvLC638D68br6qcNwxEh6rYpNspTzgQTH6FENPPRqwTA89Grz8Msstu+wyzDO73E47NOzcMw0/Ax20zjmv0yuxRyOd9G9JMN20008zzf9D1ElIzXQ3BGOdtdZbc9211wTDUooLl+DiAQeeXJK22mk/0PYvSbz9i9twM/12Em2vnbfeard9Nwf0vKq04IMTHhXUhyP+tBdfM964449DHnnW14idxCUHXJLEGEw/QHfin4Nu9+e/4NIOroWjnrrqP4EOutQuJHG15LPTXrvtt+OOEyyPuDB25p173rrwo39e+umrI588scM/DbviuUMfvfTTU48i5UnADvzddWvOvPetk2668uOTj+X3zVMde/Xrs9++++4bgP32wIt+vv2IG1++/vsneL/z8i/ufQIcIAELyLWduKBqTavf/RrotPzxL4IS1I0D/yc7A2Iwgxr/3CB4zGUA52Vuc8FzIOIYWEIP0OB4E1whC1vowhfCMIYynCENa2jDG+IwhzrcIQ976MMfAjGIQhwiEYtoxCMiMYlKXCITm+jEJ0IxilKcIhWraMUrYjGLWtwiF7voxS+CMYxiHCMZy2jGM6IxjWpcIxvb6MY3wjGOcpwjHetoxzviMY963CMf++jHPwIykIIcJCELachDIjKRilwkIxvpyEdCMpKSnCQlK2nJS2Iyk5rcJCc76clPgjKUohwlKUtpylOiMpWqXCUrW+nKV8IylrKcJS1ractb4jKXutwlL3vpy18CM5jCHCYxi2nMYyIzmcpcJjOb6cxnQjOa0pwmHTWrac1rYjOb2twmN7vpzW+CM5ziHCc5y2nOqwQEADs="
DWARF_HAMMER = "iVBORw0KGgoAAAANSUhEUgAAAYAAAABICAYAAAD/CyLSAABRVUlEQVR42u2dZ3iU1daw72f6TCZl0nsCIQkQegm9I0URxUIXUUFRsaAee8eu2AEVGyBI8QiCiPTeSwiBkN57n95nfz84r36+x3OOR7G+c//husg8+9lr7fXstdcua4MfP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378+PHjx48fP378/IZIP+VH77y7WKxa8SFdMjphbrNhMlvZunOH5FefHz9+/Px5UfyUHzXWlXDnHXM4fvwMqcnt8Di8OJwOMeeOO5kxbarfEfj5xdz/8GNCqVAghMDl8fDGyy/47epPwqcffiZmz5n5m7bXLTfPEcJhQalSIgO0ahU5xVVcdf0U5t92s992LlUE8OADd4pXXlv83e9uu/VGERoYRERwBJu27eD6GTO48455foX7+Vnce/+DojzrKB2UHmQqJVGJkbhsbs5Umlizc/df2q7efHuxqCwvoe7saTxeG8iUCAFmo5luQy/j5ddf+0PI/8qLb4oHH7n3X9blb/c8Kl5967dz2NeOHi66h6q4fGQfYqPCaTXZaWoxcby4gJPnykjsPZpXF736l7CdGYP7ixBDAIGhgXicHiqKKhk0eTr3PPjQJZHv3xZy25wbxPsfrpQANm36XEycOE0CuGPeLSI6PJwAZQC79h1m+s2zmDlz+j+V9ebiJaK1pQ2FTI7P50Ot1fDwAwv+zzmLN95ZLJqbmpDJFchkclxuNy8888T/eaf52D03i5MHDqCVdIwf3IOp4wYSoFMjl0mcyy9n4fKtZNWbKSw495fT1SsvPCfaLmxHUijwWTR0T0vkyuG9cbm9eD1ePly3nRyXDkmr47PlH/3u8i//ZLW48abp0o87iLfEg4/c86vX8dHHnhJf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"
ZOPPY_SND = "SUQzBAAAAAIUfFRTU0UAAAAOAAADTGF2ZjYwLjE2LjEwMEdFT0IAAhRaAAADYXBwbGljYXRpb24veC1jMnBhLW1hbmlmZXN0LXN0b3JlAGMycGEAYzJwYSBtYW5pZmVzdCBzdG9yZQAAAIoeanVtYgAAAB5qdW1kYzJwYQARABCAAACqADibcQNjMnBhAAAAQIFqdW1iAAAAR2p1bWRjMm1hABEAEIAAAKoAOJtxA3VybjpjMnBhOmUyZjAzMDc1LWFkYTYtNDYwMi05MzY1LTk4M2ZhMTYzNjU3ZAAAAAJ7anVtYgAAAClqdW1kYzJhcwARABCAAACqADibcQNjMnBhLmFzc2VydGlvbnMAAAAAy2p1bWIAAAApanVtZGNib3IAEQAQgAAAqgA4m3EDYzJwYS5hY3Rpb25zLnYyAAAAAJpjYm9yoWdhY3Rpb25zgaNmYWN0aW9ubGMycGEuY3JlYXRlZG1zb2Z0d2FyZUFnZW50akVsZXZlbkxhYnNxZGlnaXRhbFNvdXJjZVR5cGV4Rmh0dHA6Ly9jdi5pcHRjLm9yZy9uZXdzY29kZXMvZGlnaXRhbHNvdXJjZXR5cGUvdHJhaW5lZEFsZ29yaXRobWljTWVkaWEAAADUanVtYgAAAE5qdW1kanNvbgARABCAAACqADibcRNzdGRzLnNjaGVtYS1vcmcuQ3JlYXRpdmVXb3JrAAAAABhjMnNoXWggF1CHsV0JT9/j9swwwwAAAH5qc29ueyJAY29udGV4dCI6Imh0dHBzOi8vc2NoZW1hLm9yZyIsIkB0eXBlIjoiQ3JlYXRpdmVXb3JrIiwiYXV0aG9yIjpbeyJAdHlwZSI6Ik9yZ2FuaXphdGlvbiIsIm5hbWUiOiJFbGV2ZW4gTGFicyBJbmMuIn1dfQAAAKtqdW1iAAAAKGp1bWRjYm9yABEAEIAAAKoAOJtxA2MycGEuaGFzaC5kYXRhAAAAAHtjYm9ypWpleGNsdXNpb25zgaJlc3RhcnQYaGZsZW5ndGgZQKdkbmFtZW5qdW1iZiBtYW5pZmVzdGNhbGdmc2hhMjU2ZGhhc2hYIMYgUs9teoekybK/sEtcP1hLTLIU1+spntDF3hdaD8tuY3BhZEgAAAAAAAAAAAAAAmRqdW1iAAAAJ2p1bWRjMmNsABEAEIAAAKoAOJtxA2MycGEuY2xhaW0udjIAAAACNWNib3Kmamluc3RhbmNlSUR4LHhtcDppaWQ6OGVmMzMzOTctNGJiZC00ODZlLWFiNmQtOWEzOTc3MDExZDdhdGNsYWltX2dlbmVyYXRvcl9pbmZvv2RuYW1lZ2MycGEtcnNndmVyc2lvbmYwLjY3LjF3b3JnLmNvbnRlbnRhdXRoLmMycGFfcnNmMC42Ny4x/2lzaWduYXR1cmV4TXNlbGYjanVtYmY9L2MycGEvdXJuOmMycGE6ZTJmMDMwNzUtYWRhNi00NjAyLTkzNjUtOTgzZmExNjM2NTdkL2MycGEuc2lnbmF0dXJlcmNyZWF0ZWRfYXNzZXJ0aW9uc4KiY3VybHgqc2VsZiNqdW1iZj1jMnBhLmFzc2VydGlvbnMvYzJwYS5hY3Rpb25zLnYyZGhhc2hYICHbc5hrdJ/6aqyY/PlkMv4eFbzErMSUy2GcAExKiqp+omN1cmx4KXNlbGYjanVtYmY9YzJwYS5hc3NlcnRpb25zL2MycGEuaGFzaC5kYXRhZGhhc2hYIDLskKVbQijzM5oRk8XEH8qljtYiN+Quyg0Hjgz8MsfQc2dhdGhlcmVkX2Fzc2VydGlvbnOBomN1cmx4N3NlbGYjanVtYmY9YzJwYS5hc3NlcnRpb25zL3N0ZHMuc2NoZW1hLW9yZy5DcmVhdGl2ZVdvcmtkaGFzaFgg/BvV5Y1nAcNh7VI65mCnT7INP/cgPdO0g+Zx58cNESpjYWxnZnNoYTI1NgAAO1NqdW1iAAAAKGp1bWRjMmNzABEAEIAAAKoAOJtxA2MycGEuc2lnbmF0dXJlAAAAOyNjYm9y0oRZDmGiATgiGCGDWQQ2MIIEMjCCAxqgAwIBAgIQAluBY3FwrAx/iHkbo8P1zjANBgkqhkiG9w0BAQwFADBmMQswCQYDVQQGEwJVUzEVMBMGA1UEChMMRGlnaUNlcnQgSW5jMRkwFwYDVQQLExB3d3cuZGlnaWNlcnQuY29tMSUwIwYDVQQDExxEaWdpQ2VydCBEb2N1bWVudCBTaWduaW5nIENBMB4XDTI1MTAwNzAwMDAwMFoXDTI2MTAwNjIzNTk1OVowVjELMAkGA1UEBhMCVVMxETAPBgNVBAgTCE5ldyBZb3JrMRkwFwYDVQQKExBFbGV2ZW4gTGFicyBJbmMuMRkwFwYDVQQDExBFbGV2ZW4g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AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD2WGC3R6o2lcrfHX6m5u/zFFOKgOhMQVk8vGtA9jUK/2B/qCxuOSXTlwJNiK4imPcaWBfFJe3zB/32f+Du//siludFy8pMPtNWlDiPrGI+remdv6Ay1lyG6PFBsXBQvkM4E5wAAEl3anVtYgAAAEdqdW1kYzJtYQARABCAAACqADibcQN1cm46YzJwYTo2MTU5N2MwNS1jODlhLTQ0NWYtOWE5Yy1lZmFmZDg1OWM1ZTAAAAALAWp1bWIAAAApanVtZGMyYXMAEQAQgAAAqgA4m3EDYzJwYS5hc3NlcnRpb25zAAAAB+9qdW1iAAAALGp1bWRjYm9yABEAEIAAAKoAOJtxA2MycGEuaW5ncmVkaWVudC52MwAAAAe7Y2JvcqZscmVsYXRpb25zaGlwaHBhcmVudE9maWRjOmZvcm1hdGphdWRpby9tcGVncXZhbGlkYXRpb25SZXN1bHRzoW5hY3RpdmVNYW5pZmVzdKNnc3VjY2Vzc4ejZGNvZGVzdGltZVN0YW1wLnZhbGlkYXRlZGN1cmx4TXNlbGYjanVtYmY9L2MycGEvdXJuOmMycGE6ZTJmMDMwNzUtYWRhNi00NjAyLTkzNjUtOTgzZmExNjM2NTdkL2MycGEuc2lnbmF0dXJla2V4cGxhbmF0aW9ueFR0aW1lc3RhbXAgbWVzc2FnZSBkaWdlc3QgbWF0Y2hlZDogRGlnaUNlcnQgU0hBMjU2IFJTQTQwOTYgVGltZXN0YW1wIFJlc3BvbmRlciAyMDI1IDGjZGNvZGV4HWNsYWltU2lnbmF0dXJlLmluc2lkZVZhbGlkaXR5Y3VybHhNc2VsZiNqdW1iZj0vYzJwYS91cm46YzJwYTplMmYwMzA3NS1hZGE2LTQ2MDItOTM2NS05ODNmYTE2MzY1N2QvYzJwYS5zaWduYXR1cmVrZXhwbGFuYXRpb251Y2xhaW0gc2lnbmF0dXJlIHZhbGlko2Rjb2RleBhjbGFpbVNpZ25hdHVyZS52YWxpZGF0ZWRjdXJseE1zZWxmI2p1bWJmPS9jMnBhL3VybjpjMnBhOmUyZjAzMDc1LWFkYTYtNDYwMi05MzY1LTk4M2ZhMTYzNjU3ZC9jMnBhLnNpZ25hdHVyZWtleHBsYW5hdGlvbnVjbGFpbSBzaWduYXR1cmUgdmFsaWSjZGNvZGV4GWFzc2VydGlvbi5oYXNoZWRVUkkubWF0Y2hjdXJseF5zZWxmI2p1bWJmPS9jMnBhL3VybjpjMnBhOmUyZjAzMDc1LWFkYTYtNDYwMi05MzY1LTk4M2ZhMTYzNjU3ZC9jMnBhLmFzc2VydGlvbnMvYzJwYS5hY3Rpb25zLnYya2V4cGxhbmF0aW9ueD5oYXNoZWQgdXJpIG1hdGNoZWQ6IHNlbGYjanVtYmY9YzJwYS5hc3NlcnRpb25zL2MycGEuYWN0aW9ucy52MqNkY29kZXgZYXNzZXJ0aW9uLmhhc2hlZFVSSS5tYXRjaGN1cmx4XXNlbGYjanVtYmY9L2MycGEvdXJuOmMycGE6ZTJmMDMwNzUtYWRhNi00NjAyLTkzNjUtOTgzZmExNjM2NTdkL2MycGEuYXNzZXJ0aW9ucy9jMnBhLmhhc2guZGF0YWtleHBsYW5hdGlvbng9aGFzaGVkIHVyaSBtYXRjaGVkOiBzZWxmI2p1bWJmPWMycGEuYXNzZXJ0aW9ucy9jMnBhLmhhc2guZGF0YaNkY29kZXgZYXNzZXJ0aW9uLmhhc2hlZFVSSS5tYXRjaGN1cmx4a3NlbGYjanVtYmY9L2MycGEvdXJuOmMycGE6ZTJmMDMwNzUtYWRhNi00NjAyLTkzNjUtOTgzZmExNjM2NTdkL2MycGEuYXNzZXJ0aW9ucy9zdGRzLnNjaGVtYS1vcmcuQ3JlYXRpdmVXb3Jra2V4cGxhbmF0aW9ueEtoYXNoZWQgdXJpIG1hdGNoZWQ6IHNlbGYjanVtYmY9YzJwYS5hc3NlcnRpb25zL3N0ZHMuc2NoZW1hLW9yZy5DcmVhdGl2ZVdvcmujZGNvZGV4GGFzc2VydGlvbi5kYXRhSGFzaC5tYXRjaGN1cmx4XXNlbGYjanVtYmY9L2MycGEvdXJuOmMycGE6ZTJmMDMwNzUtYWRhNi00NjAyLTkzNjUtOTgzZmExNjM2NTdkL2MycGEuYXNzZXJ0aW9ucy9jMnBhLmhhc2guZGF0YWtleHBsYW5hdGlvbm9kYXRhIGhhc2ggdmFsaWRtaW5mb3JtYXRpb25hbIGjZGNvZGVzdGltZVN0YW1wLnVudHJ1c3RlZGN1cmx4TXNlbGYjanVtYmY9L2MycGEvdXJuOmMycGE6ZTJmMDMwNzUtYWRhNi00NjAyLTkzNjUtOTgzZmExNjM2NTdkL2MycGEuc2lnbmF0dXJla2V4cGxhbmF0aW9ueEx0aW1lc3RhbXAgY2VydCB1bnRydXN0ZWQ6IERpZ2lDZXJ0IFNIQTI1NiBSU0E0MDk2IFRpbWVzdGFtcCBSZXNwb25kZXIgMjAyNSAxZ2ZhaWx1cmWAamluc3RhbmNlSUR4LHhtcDppaWQ6NzgzMGIyMGYtZTg0MS00Mzk5LTlhNjMtYTJkMzIwZTA3NzBibmFjdGl2ZU1hbmlmZXN0o2N1cmx4PnNlbGYjanVtYmY9L2MycGEvdXJuOmMycGE6ZTJmMDMwNzUtYWRhNi00NjAyLTkzNjUtOTgzZmExNjM2NTdkY2FsZ2ZzaGEyNTZkaGFzaFgg0501blZurwVAWGfsbH8ZG/CVx7YyTNIEAz4NsQKRMzxuY2xhaW1TaWduYXR1cmWjY3VybHhNc2VsZiNqdW1iZj0vYzJwYS91cm46YzJwYTplMmYwMzA3NS1hZGE2LTQ2MDItOTM2NS05ODNmYTE2MzY1N2QvYzJwYS5zaWduYXR1cmVjYWxnZnNoYTI1NmRoYXNoWCCCkgoN1Bq41iPCtb2h9zTOvMAiFoel/sv5V+ge6HLlmwAAAWBqdW1iAAAAKWp1bWRjYm9yABEAEIAAAKoAOJtxA2MycGEuYWN0aW9ucy52MgAAAAEvY2JvcqFnYWN0aW9uc4KiZmFjdGlvbmtjMnBhLm9wZW5lZGpwYXJhbWV0ZXJzv2tpbmdyZWRpZW50c4GiY3VybHgtc2VsZiNqdW1iZj1jMnBhLmFzc2VydGlvbnMvYzJwYS5pbmdyZWRpZW50LnYzZGhhc2hYIJdwyJiQBNQZWZ5MshN9s7WUae1T9f15GZVWDXdKFdeF/6NmYWN0aW9ua2MycGEuZWRpdGVkbXNvZnR3YXJlQWdlbnRqRWxldmVuTGFic3FkaWdpdGFsU291cmNlVHlwZXhTaHR0cDovL2N2LmlwdGMub3JnL25ld3Njb2Rlcy9kaWdpdGFsc291cmNldHlwZS9jb21wb3NpdGVXaXRoVHJhaW5lZEFsZ29yaXRobWljTWVkaWEAAADUanVtYgAAAE5qdW1kanNvbgARABCAAACqADibcRNzdGRzLnNjaGVtYS1vcmcuQ3JlYXRpdmVXb3JrAAAAABhjMnNoLj0T2rZXV1HVmEHYj2NCCgAAAH5qc29ueyJAY29udGV4dCI6Imh0dHBzOi8vc2NoZW1hLm9yZyIsIkB0eXBlIjoiQ3JlYXRpdmVXb3JrIiwiYXV0aG9yIjpbeyJAdHlwZSI6Ik9yZ2FuaXphdGlvbiIsIm5hbWUiOiJFbGV2ZW4gTGFicyBJbmMuIn1dfQAAAK1qdW1iAAAAKGp1bWRjYm9yABEAEIAAAKoAOJtxA2MycGEuaGFzaC5kYXRhAAAAAH1jYm9ypWpleGNsdXNpb25zgaJlc3RhcnQYaGZsZW5ndGgZih5kbmFtZW5qdW1iZiBtYW5pZmVzdGNhbGdmc2hhMjU2ZGhhc2hYIEHk/FiVMAHy05Qas84hnHXNG7uonfoACZb/SnFYdCtGY3BhZEoAAAAAAAAAAAAAAAAC1Gp1bWIAAAAnanVtZGMyY2wAEQAQgAAAqgA4m3EDYzJwYS5jbGFpbS52MgAAAAKlY2JvcqdqaW5zdGFuY2VJRHgseG1wOmlpZDpkOTRiZWRhNC04ODBlLTRjNTgtOTYwMC05MzZhMDNhYTRlYWV0Y2xhaW1fZ2VuZXJhdG9yX2luZm+/ZG5hbWVnYzJwYS1yc2d2ZXJzaW9uZjAuNjcuMXdvcmcuY29udGVudGF1dGguYzJwYV9yc2YwLjY3LjH/aXNpZ25hdHVyZXhNc2VsZiNqdW1iZj0vYzJwYS91cm46YzJwYTo2MTU5N2MwNS1jODlhLTQ0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AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA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"
SOCK_SPRITE = "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"
ZOPPY_GAME = "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"
ZOPPY_ATK = "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"
ZOPPY_INTRO = "SUQzBAAAAAIUfFRTU0UAAAAOAAADTGF2ZjYwLjE2LjEwMEdFT0IAAhRaAAADYXBwbGljYXRpb24veC1jMnBhLW1hbmlmZXN0LXN0b3JlAGMycGEAYzJwYSBtYW5pZmVzdCBzdG9yZQAAAIoeanVtYgAAAB5qdW1kYzJwYQARABCAAACqADibcQNjMnBhAAAAQIFqdW1iAAAAR2p1bWRjMm1hABEAEIAAAKoAOJtxA3VybjpjMnBhOjFlZjdiMmMyLTMzYmEtNGNlYy1iNzNkLTQ5MGVlOTQ5YzY3YgAAAAJ7anVtYgAAAClqdW1kYzJhcwARABCAAACqADibcQNjMnBhLmFzc2VydGlvbnMAAAAAy2p1bWIAAAApanVtZGNib3IAEQAQgAAAqgA4m3EDYzJwYS5hY3Rpb25zLnYyAAAAAJpjYm9yoWdhY3Rpb25zgaNmYWN0aW9ubGMycGEuY3JlYXRlZG1zb2Z0d2FyZUFnZW50akVsZXZlbkxhYnNxZGlnaXRhbFNvdXJjZVR5cGV4Rmh0dHA6Ly9jdi5pcHRjLm9yZy9uZXdzY29kZXMvZGlnaXRhbHNvdXJjZXR5cGUvdHJhaW5lZEFsZ29yaXRobWljTWVkaWEAAADUanVtYgAAAE5qdW1kanNvbgARABCAAACqADibcRNzdGRzLnNjaGVtYS1vcmcuQ3JlYXRpdmVXb3JrAAAAABhjMnNo9l1sh719BVW82uJtD42iQwAAAH5qc29ueyJAY29udGV4dCI6Imh0dHBzOi8vc2NoZW1hLm9yZyIsIkB0eXBlIjoiQ3JlYXRpdmVXb3JrIiwiYXV0aG9yIjpbeyJAdHlwZSI6Ik9yZ2FuaXphdGlvbiIsIm5hbWUiOiJFbGV2ZW4gTGFicyBJbmMuIn1dfQAAAKtqdW1iAAAAKGp1bWRjYm9yABEAEIAAAKoAOJtxA2MycGEuaGFzaC5kYXRhAAAAAHtjYm9ypWpleGNsdXNpb25zgaJlc3RhcnQYaGZsZW5ndGgZQKdkbmFtZW5qdW1iZiBtYW5pZmVzdGNhbGdmc2hhMjU2ZGhhc2hYIBRe72DsJJ+JZh1sQskFAkIqNZs7XVuVVH+WpUaMrNEQY3BhZEgAAAAAAAAAAAAAAmRqdW1iAAAAJ2p1bWRjMmNsABEAEIAAAKoAOJtxA2MycGEuY2xhaW0udjIAAAACNWNib3Kmamluc3RhbmNlSUR4LHhtcDppaWQ6NTVlMDRmMzEtODc4Zi00OTgzLWEyNTItODM0NmQ2OTNhY2NjdGNsYWltX2dlbmVyYXRvcl9pbmZvv2RuYW1lZ2MycGEtcnNndmVyc2lvbmYwLjY3LjF3b3JnLmNvbnRlbnRhdXRoLmMycGFfcnNmMC42Ny4x/2lzaWduYXR1cmV4TXNlbGYjanVtYmY9L2MycGEvdXJuOmMycGE6MWVmN2IyYzItMzNiYS00Y2VjLWI3M2QtNDkwZWU5NDljNjdiL2MycGEuc2lnbmF0dXJlcmNyZWF0ZWRfYXNzZXJ0aW9uc4KiY3VybHgqc2VsZiNqdW1iZj1jMnBhLmFzc2VydGlvbnMvYzJwYS5hY3Rpb25zLnYyZGhhc2hYICHbc5hrdJ/6aqyY/PlkMv4eFbzErMSUy2GcAExKiqp+omN1cmx4KXNlbGYjanVtYmY9YzJwYS5hc3NlcnRpb25zL2MycGEuaGFzaC5kYXRhZGhhc2hYIDV0FkVKsarlTxWZOrtW+LnylcYdqJeL+/XEeFDR1wA1c2dhdGhlcmVkX2Fzc2VydGlvbnOBomN1cmx4N3NlbGYjanVtYmY9YzJwYS5hc3NlcnRpb25zL3N0ZHMuc2NoZW1hLW9yZy5DcmVhdGl2ZVdvcmtkaGFzaFggmwF4MuNk/6TjAFeia16NB2k5hDFHbPDK4DqS9rnFyJtjYWxnZnNoYTI1NgAAO1NqdW1iAAAAKGp1bWRjMmNzABEAEIAAAKoAOJtxA2MycGEuc2lnbmF0dXJlAAAAOyNjYm9y0oRZDmGiATgiGCGDWQQ2MIIEMjCCAxqgAwIBAgIQAluBY3FwrAx/iHkbo8P1zjANBgkqhkiG9w0BAQwFADBmMQswCQYDVQQGEwJVUzEVMBMGA1UEChMMRGlnaUNlcnQgSW5jMRkwFwYDVQQLExB3d3cuZGlnaWNlcnQuY29tMSUwIwYDVQQDExxEaWdpQ2VydCBEb2N1bWVudCBTaWduaW5nIENBMB4XDTI1MTAwNzAwMDAwMFoXDTI2MTAwNjIzNTk1OVowVjELMAkGA1UEBhMCVVMxETAPBgNVBAgTCE5ldyBZb3JrMRkwFwYDVQQKExBFbGV2ZW4gTGFicyBJbmMuMRkwFwYDVQQDExBFbGV2ZW4g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AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD2WGAUlwInCPbsBCg/q6WaSTtFbPndOdQV/Pl99iJJvx/tLAzmDONT8pqtiwt0C8An4NGEJAPYUO+K+S782HeCDQsz0zOoHo2qkw41vEjIuqbNK5SGuc9RWVNxa1Nqy2XdQ8YAAEl3anVtYgAAAEdqdW1kYzJtYQARABCAAACqADibcQN1cm46YzJwYTo4ZjFhNGI5Yy1kNGVkLTQ2NzUtOWQ4NS1hZjlkMzlmOWZhOTQAAAALAWp1bWIAAAApanVtZGMyYXMAEQAQgAAAqgA4m3EDYzJwYS5hc3NlcnRpb25zAAAAB+9qdW1iAAAALGp1bWRjYm9yABEAEIAAAKoAOJtxA2MycGEuaW5ncmVkaWVudC52MwAAAAe7Y2JvcqZscmVsYXRpb25zaGlwaHBhcmVudE9maWRjOmZvcm1hdGphdWRpby9tcGVncXZhbGlkYXRpb25SZXN1bHRzoW5hY3RpdmVNYW5pZmVzdKNnc3VjY2Vzc4ejZGNvZGVzdGltZVN0YW1wLnZhbGlkYXRlZGN1cmx4TXNlbGYjanVtYmY9L2MycGEvdXJuOmMycGE6MWVmN2IyYzItMzNiYS00Y2VjLWI3M2QtNDkwZWU5NDljNjdiL2MycGEuc2lnbmF0dXJla2V4cGxhbmF0aW9ueFR0aW1lc3RhbXAgbWVzc2FnZSBkaWdlc3QgbWF0Y2hlZDogRGlnaUNlcnQgU0hBMjU2IFJTQTQwOTYgVGltZXN0YW1wIFJlc3BvbmRlciAyMDI1IDGjZGNvZGV4HWNsYWltU2lnbmF0dXJlLmluc2lkZVZhbGlkaXR5Y3VybHhNc2VsZiNqdW1iZj0vYzJwYS91cm46YzJwYToxZWY3YjJjMi0zM2JhLTRjZWMtYjczZC00OTBlZTk0OWM2N2IvYzJwYS5zaWduYXR1cmVrZXhwbGFuYXRpb251Y2xhaW0gc2lnbmF0dXJlIHZhbGlko2Rjb2RleBhjbGFpbVNpZ25hdHVyZS52YWxpZGF0ZWRjdXJseE1zZWxmI2p1bWJmPS9jMnBhL3VybjpjMnBhOjFlZjdiMmMyLTMzYmEtNGNlYy1iNzNkLTQ5MGVlOTQ5YzY3Yi9jMnBhLnNpZ25hdHVyZWtleHBsYW5hdGlvbnVjbGFpbSBzaWduYXR1cmUgdmFsaWSjZGNvZGV4GWFzc2VydGlvbi5oYXNoZWRVUkkubWF0Y2hjdXJseF5zZWxmI2p1bWJmPS9jMnBhL3VybjpjMnBhOjFlZjdiMmMyLTMzYmEtNGNlYy1iNzNkLTQ5MGVlOTQ5YzY3Yi9jMnBhLmFzc2VydGlvbnMvYzJwYS5hY3Rpb25zLnYya2V4cGxhbmF0aW9ueD5oYXNoZWQgdXJpIG1hdGNoZWQ6IHNlbGYjanVtYmY9YzJwYS5hc3NlcnRpb25zL2MycGEuYWN0aW9ucy52MqNkY29kZXgZYXNzZXJ0aW9uLmhhc2hlZFVSSS5tYXRjaGN1cmx4XXNlbGYjanVtYmY9L2MycGEvdXJuOmMycGE6MWVmN2IyYzItMzNiYS00Y2VjLWI3M2QtNDkwZWU5NDljNjdiL2MycGEuYXNzZXJ0aW9ucy9jMnBhLmhhc2guZGF0YWtleHBsYW5hdGlvbng9aGFzaGVkIHVyaSBtYXRjaGVkOiBzZWxmI2p1bWJmPWMycGEuYXNzZXJ0aW9ucy9jMnBhLmhhc2guZGF0YaNkY29kZXgZYXNzZXJ0aW9uLmhhc2hlZFVSSS5tYXRjaGN1cmx4a3NlbGYjanVtYmY9L2MycGEvdXJuOmMycGE6MWVmN2IyYzItMzNiYS00Y2VjLWI3M2QtNDkwZWU5NDljNjdiL2MycGEuYXNzZXJ0aW9ucy9zdGRzLnNjaGVtYS1vcmcuQ3JlYXRpdmVXb3Jra2V4cGxhbmF0aW9ueEtoYXNoZWQgdXJpIG1hdGNoZWQ6IHNlbGYjanVtYmY9YzJwYS5hc3NlcnRpb25zL3N0ZHMuc2NoZW1hLW9yZy5DcmVhdGl2ZVdvcmujZGNvZGV4GGFzc2VydGlvbi5kYXRhSGFzaC5tYXRjaGN1cmx4XXNlbGYjanVtYmY9L2MycGEvdXJuOmMycGE6MWVmN2IyYzItMzNiYS00Y2VjLWI3M2QtNDkwZWU5NDljNjdiL2MycGEuYXNzZXJ0aW9ucy9jMnBhLmhhc2guZGF0YWtleHBsYW5hdGlvbm9kYXRhIGhhc2ggdmFsaWRtaW5mb3JtYXRpb25hbIGjZGNvZGVzdGltZVN0YW1wLnVudHJ1c3RlZGN1cmx4TXNlbGYjanVtYmY9L2MycGEvdXJuOmMycGE6MWVmN2IyYzItMzNiYS00Y2VjLWI3M2QtNDkwZWU5NDljNjdiL2MycGEuc2lnbmF0dXJla2V4cGxhbmF0aW9ueEx0aW1lc3RhbXAgY2VydCB1bnRydXN0ZWQ6IERpZ2lDZXJ0IFNIQTI1NiBSU0E0MDk2IFRpbWVzdGFtcCBSZXNwb25kZXIgMjAyNSAxZ2ZhaWx1cmWAamluc3RhbmNlSUR4LHhtcDppaWQ6YjZlN2I2NTUtYjVlYi00YTQ1LWI3MGEtYmJlNWVjNjMxNTk3bmFjdGl2ZU1hbmlmZXN0o2N1cmx4PnNlbGYjanVtYmY9L2MycGEvdXJuOmMycGE6MWVmN2IyYzItMzNiYS00Y2VjLWI3M2QtNDkwZWU5NDljNjdiY2FsZ2ZzaGEyNTZkaGFzaFggmArsLkkwhHGuE8ZeghGphyf28bQLakekFOoPEsB/GMJuY2xhaW1TaWduYXR1cmWjY3VybHhNc2VsZiNqdW1iZj0vYzJwYS91cm46YzJwYToxZWY3YjJjMi0zM2JhLTRjZWMtYjczZC00OTBlZTk0OWM2N2IvYzJwYS5zaWduYXR1cmVjYWxnZnNoYTI1NmRoYXNoWCAuS7dgSKyz59KXATX7BNJtRHb3S30dQH2AVT52VEm4uQAAAWBqdW1iAAAAKWp1bWRjYm9yABEAEIAAAKoAOJtxA2MycGEuYWN0aW9ucy52MgAAAAEvY2JvcqFnYWN0aW9uc4KiZmFjdGlvbmtjMnBhLm9wZW5lZGpwYXJhbWV0ZXJzv2tpbmdyZWRpZW50c4GiY3VybHgtc2VsZiNqdW1iZj1jMnBhLmFzc2VydGlvbnMvYzJwYS5pbmdyZWRpZW50LnYzZGhhc2hYIF4G7qRQBVEx7IPgRpYLEs5oaX5JkgA8edq4EJoEyvvx/6NmYWN0aW9ua2MycGEuZWRpdGVkbXNvZnR3YXJlQWdlbnRqRWxldmVuTGFic3FkaWdpdGFsU291cmNlVHlwZXhTaHR0cDovL2N2LmlwdGMub3JnL25ld3Njb2Rlcy9kaWdpdGFsc291cmNldHlwZS9jb21wb3NpdGVXaXRoVHJhaW5lZEFsZ29yaXRobWljTWVkaWEAAADUanVtYgAAAE5qdW1kanNvbgARABCAAACqADibcRNzdGRzLnNjaGVtYS1vcmcuQ3JlYXRpdmVXb3JrAAAAABhjMnNoxiBKtRSPvKDqmAdixrTYiAAAAH5qc29ueyJAY29udGV4dCI6Imh0dHBzOi8vc2NoZW1hLm9yZyIsIkB0eXBlIjoiQ3JlYXRpdmVXb3JrIiwiYXV0aG9yIjpbeyJAdHlwZSI6Ik9yZ2FuaXphdGlvbiIsIm5hbWUiOiJFbGV2ZW4gTGFicyBJbmMuIn1dfQAAAK1qdW1iAAAAKGp1bWRjYm9yABEAEIAAAKoAOJtxA2MycGEuaGFzaC5kYXRhAAAAAH1jYm9ypWpleGNsdXNpb25zgaJlc3RhcnQYaGZsZW5ndGgZih5kbmFtZW5qdW1iZiBtYW5pZmVzdGNhbGdmc2hhMjU2ZGhhc2hYIDewl/GR36akpIl1jw8FX8sqKhZB6X6DzLvOaWsfmw/YY3BhZEoAAAAAAAAAAAAAAAAC1Gp1bWIAAAAnanVtZGMyY2wAEQAQgAAAqgA4m3EDYzJwYS5jbGFpbS52MgAAAAKlY2JvcqdqaW5zdGFuY2VJRHgseG1wOmlpZDplN2I0ZDQxOS00YWJhLTRlYjktYWY0NS1lY2FiNTk4N2VmYmV0Y2xhaW1fZ2VuZXJhdG9yX2luZm+/ZG5hbWVnYzJwYS1yc2d2ZXJzaW9uZjAuNjcuMXdvcmcuY29udGVudGF1dGguYzJwYV9yc2YwLjY3LjH/aXNpZ25hdHVyZXhNc2VsZiNqdW1iZj0vYzJwYS91cm46YzJwYTo4ZjFhNGI5Yy1kNGVkLTQ2NzUtOWQ4NS1hZjlkMzlmOWZhOTQvYzJwYS5zaWduYXR1cmVyY3JlYXRlZF9hc3NlcnRpb25zg6JjdXJseC1zZWxmI2p1bWJmPWMycGEuYXNzZXJ0aW9ucy9jMnBhLmluZ3JlZGllbnQudjNkaGFzaFggXgbupFAFUTHsg+BGlgsSzmhpfkmSADx52rgQmgTK+/GiY3VybHgqc2VsZiNqdW1iZj1jMnBhLmFzc2VydGlvbnMvYzJwYS5hY3Rpb25zLnYyZGhhc2hYIOxGlEpbyCpj/poyyEZy9R8YOEM2YP43qrRdq8oiAqNwomN1cmx4KXNlbGYjanVtYmY9YzJwYS5hc3NlcnRpb25zL2MycGEuaGFzaC5kYXRhZGhhc2hYIB0LnM2CdBEveaUqpJJcVIAiAPetGqWIfqYuefnXILiyc2dhdGhlcmVkX2Fzc2VydGlvbnOBomN1cmx4N3NlbGYjanVtYmY9YzJwYS5hc3NlcnRpb25zL3N0ZHMuc2NoZW1hLW9yZy5DcmVhdGl2ZVdvcmtkaGFzaFgg4GSgJ3OwPE/bPOy2mVYfblpjs44fEXLC1TT7yKJjAStzcmVkYWN0ZWRfYXNzZXJ0aW9uc4BjYWxnZnNoYTI1NgAAO1NqdW1iAAAAKGp1bWRjMmNzABEAEIAAAKoAOJtxA2MycGEuc2lnbmF0dXJlAAAAOyNjYm9y0oRZDmGiATgiGCGDWQQ2MIIEMjCCAxqgAwIBAgIQAluBY3FwrAx/iHkbo8P1zjANBgkqhkiG9w0BAQwFADBmMQswCQYDVQQGEwJVUzEVMBMGA1UEChMMRGlnaUNlcnQgSW5jMRkwFwYDVQQLExB3d3cuZGlnaWNlcnQuY29tMSUwIwYDVQQDExxEaWdpQ2VydCBEb2N1bWVudCBTaWduaW5nIENBMB4XDTI1MTAwNzAwMDAwMFoXDTI2MTAwNjIzNTk1OVowVjELMAkGA1UEBhMCVVMxETAPBgNVBAgTCE5ldyBZb3JrMRkwFwYDVQQKExBFbGV2ZW4gTGFicyBJbmMuMRkwFwYDVQQDExBFbGV2ZW4gTGFicyBJbmMuMHYwEAYHKoZIzj0CAQYFK4EEACIDYgAE7fc88mzJsY9a+Dr4lD+POvz4qiOy/nQREUMqNdBX3PjOOySs5cDojJfDlsIC+cbnHbY28KiFQP3FPwkIm6oVric7FHWK4fspQ5nW1OjtydAEJFliyMB51tTcXHYVmWRGo4IBmDCCAZQwHwYDVR0jBBgwFoAU7841k872hsX4hPUM51pv2S9L42QwHQYDVR0OBBYEFIcQJzpvxPt47FHLwoFc0f51yWq9MBYGA1UdIAQPMA0wCwYJYIZIAYb9bAMVMA4GA1UdDwEB/wQEAwIHgDAdBgNVHSUEFjAUBggrBgEFBQcDAgYIKwYBBQUHAwQwgY0GA1UdHwSBhTCBgjA/oD2gO4Y5aHR0cDovL2NybDMuZGlnaWNlcnQuY29tL0RpZ2lDZXJ0RG9jdW1lbnRTaWduaW5nQ0EtZzEuY3JsMD+gPaA7hjlodHRwOi8vY3JsNC5kaWdpY2VydC5jb20vRGlnaUNlcnREb2N1bWVudFNpZ25pbmdDQS1nMS5jcmwwewYIKwYBBQUHAQEEbzBtMCQGCCsGAQUFBzABhhhodHRwOi8vb2NzcC5kaWdpY2VydC5jb20wRQYIKwYBBQUHMAKGOWh0dHA6Ly9jYWNlcnRzLmRpZ2ljZXJ0LmNvbS9EaWdpQ2VydERvY3VtZW50U2lnbmluZ0NBLmNydDANBgkqhkiG9w0BAQwFAAOCAQEAguAdl4dmsvzWFRHG68yh6GVtdeN3ZrWsbL4/C6kE0N9NkY7kntJDlA8D7x+WAD7jc4grRdbMqGDa/l9r8nOi8SSrwvjS1GYyyPLY12V/CahT++gswmmdKDRDeqOLQXSLVBDXZLUr82CKUnDn5EzlIhc9XZIOHhWUeJXfoSlVDPLtcjjlzFvL2H3UyDqQ1brE0VmxiUIpRHaX/tRTkHHqSY8wqwAG+UIA8ZzrRKzliUqJ9InUydLbh5hIMf6/6fCNlf7bG7Zvb3kLYCVyBxrWB+fk2Q+8UoGfA4bHsvWp85meZf1aJD2pR5pgftsIpDr+/jC1EgQ3t6j/1ASlXpg+tFkGYDCCBlwwggVEoAMCAQICEAnHt9uyeCQ3kRlearEzhxAwDQYJKoZIhvcNAQELBQAwZTELMAkGA1UEBhMCVVMxFTATBgNVBAoTDERpZ2lDZXJ0IEluYzEZMBcGA1UECxMQd3d3LmRpZ2ljZXJ0LmNvbTEkMCIGA1UEAxMbRGlnaUNlcnQgQXNzdXJlZCBJRCBSb290IENBMB4XDTEzMTEwNTEyMDAwMFoXDTI4MTEwNTEyMDAwMFowZjELMAkGA1UEBhMCVVMxFTATBgNVBAoTDERpZ2lDZXJ0IEluYzEZMBcGA1UECxMQd3d3LmRpZ2ljZXJ0LmNvbTElMCMGA1UEAxMcRGlnaUNlcnQgRG9jdW1lbnQgU2lnbmluZyBDQTCCASIwDQYJKoZIhvcNAQEBBQADggEPADCCAQoCggEBAMpRFjp3mfUWJKm15ObelXoxDUqdast9JXykm5yE+gg0aPUJJj4xRbAhSEzVmZWGnxqdd/a7Zw+lWpylD/ub5dIYKuvGVAxiiCNiq2GWbk8XYh6BrOkQ5sOdubb25eHsxq5LLZtIh2O8HZ9gpRaP/ZLrcTTIXsYV2IpK/BM2MKoNNhwt0A5PtTHkWU70CzK5Ymx1Zfh6ibOTWzRIsPhL9SBWg6VI9Y2UY0wDJ6kwVWeVFRspQCOdtKjHDWUAsxHoIk9vRJjk/nJ14rqsMU1d4Q+mlCygyCjdqEYFOI4QFJqqP4QW4k5akl+Fs0bNQRRv/sr6r72tNQotgSyftvzNDtMCAwEAAaOCAwUwggMBMBIGA1UdEwEB/wQIMAYBAf8CAQAwDgYDVR0PAQH/BAQDAgGGMDQGCCsGAQUFBwEBBCgwJjAkBggrBgEFBQcwAYYYaHR0cDovL29jc3AuZGlnaWNlcnQuY29tMIGBBgNVHR8EejB4MDqgOKA2hjRodHRwOi8vY3JsNC5kaWdpY2VydC5jb20vRGlnaUNlcnRBc3N1cmVkSURSb290Q0EuY3JsMDqgOKA2hjRodHRwOi8vY3JsMy5kaWdpY2VydC5jb20vRGlnaUNlcnRBc3N1cmVkSURSb290Q0EuY3JsMB0GA1UdJQQWMBQGCCsGAQUFBwMCBggrBgEFBQcDBDCCAcAGA1UdIASCAbcwggGzMIIBogYKYIZIAYb9bAACBDCCAZIwKAYIKwYBBQUHAgEWHGh0dHBzOi8vd3d3LmRpZ2ljZXJ0LmNvbS9DUFMwggFkBggrBgEFBQcCAjCCAVYeggFSAEEAbgB5ACAAdQBzAGUAIABvAGYAIAB0AGgAaQBzACAAQwBlAHIAdABpAGYAaQBjAGEAdABlACAAYwBvAG4AcwB0AGkAdAB1AHQAZQBzACAAYQBjAGMAZQBwAHQAYQBuAGMAZQAgAG8AZgAgAHQAaABlACAARABpAGcAaQBDAGUAcgB0ACAAQwBQAC8AQwBQAFMAIABhAG4AZAAgAHQAaABlACAAUgBlAGwAeQBpAG4AZwAgAFAAYQByAHQAeQAgAEEAZwByAGUAZQBtAGUAbgB0ACAAdwBoAGkAYwBoACAAbABpAG0AaQB0ACAAbABpAGEAYgBpAGwAaQB0AHkAIABhAG4AZAAgAGEAcgBlACAAaQBuAGMAbwByAHAAbwByAGEAdABlAGQAIABoAGUAcgBlAGkAbgAgAGIAeQAgAHIAZQBmAGUAcgBlAG4AYwBlAC4wCwYJYIZIAYb9bAMVMB0GA1UdDgQWBBTvzjWTzvaGxfiE9QznWm/ZL0vjZDAfBgNVHSMEGDAWgBRF66Kv9JLLgjEtUYunpyGd823IDzANBgkqhkiG9w0BAQsFAAOCAQEAWXDN9zDjtPpTy3wBhPIUBgnC+2RLZV6iXvkMVL3dZq1chPjfj3pqd7PoLJIPRZlyofZ1OJIlKYWybkFrBd3/+uGethzEKFwhf6Pn0aEx5gaKn1KLjONM+iHq9a3PH9hVjdzUK7F354MQqbdcwjE5mJgKeXch9ffZcF3FZgIRm5XAy62JNgrAg+sKgZ293bjw0wdREoubbcruRLMI9JF5/vXgYhHy93lp+52ZycevAedOg+2+HcwQgMVvNs81VNGLR4t2WcAMCclqsWTLLfdP6TunNiBJ5PcX8HsPIU9H047SkKRpbU/SFOLHZdI6jLFPlRQfnHEzSfZVrL6gsBHqgFkDuzCCA7cwggKfoAMCAQICEAzn4OUX2Eb+j+Vg/BvwMDkwDQYJKoZIhvcNAQEFBQAwZTELMAkGA1UEBhMCVVMxFTATBgNVBAoTDERpZ2lDZXJ0IEluYzEZMBcGA1UECxMQd3d3LmRpZ2ljZXJ0LmNvbTEkMCIGA1UEAxMbRGlnaUNlcnQgQXNzdXJlZCBJRCBSb290IENBMB4XDTA2MTExMDAwMDAwMFoXDTMxMTExMDAwMDAwMFowZTELMAkGA1UEBhMCVVMxFTATBgNVBAoTDERpZ2lDZXJ0IEluYzEZMBcGA1UECxMQd3d3LmRpZ2ljZXJ0LmNvbTEkMCIGA1UEAxMbRGlnaUNlcnQgQXNzdXJlZCBJRCBSb290IENBMIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEArQ4VzuRDgFyxh/O3YPlxEqWu3CaUiKr0zvUgOShYYAz4gNqpFZUyYTy1sSiEiorcnwoMgxd6j5Csiud5U1wxhCr2D5gyNnbM3t08qKLvavsh8lJh358g1x/isdn+GGTSEltf+VgYNbxHzaE2+Wt/1LA4PsEbw4wz2dgvGP4oD7Ong9bDbkTAYTWWFv5ZnIt2bdfxoksNK/8LctqeYNCOkDXGeFWHIKHP5W0KyEl8MZgzbCLph9AyWqK6E4IR7TkXnZk6cqHm+qTZ1Rcxda6FfSKuPwFGhvYoecix2uRXF8R+HA6wtJKmVrO9spftqqfwt8WoP5UW0P+hlusIXxh3TwIDAQABo2MwYTAOBgNVHQ8BAf8EBAMCAYYwDwYDVR0TAQH/BAUwAwEB/zAdBgNVHQ4EFgQUReuir/SSy4IxLVGLp6chnfNtyA8wHwYDVR0jBBgwFoAUReuir/SSy4IxLVGLp6chnfNtyA8wDQYJKoZIhvcNAQEFBQADggEBAKIOvN/i7fDjcnN6ZJS/93Jm2DLkQnVirofr8tXZ3lazn8zOFCi5DZdgXBJMWOTTPYNJRViXNWkaqEfqVsZ5qxLYZ4GE338JPJTmuCYsIL09syiJ91//IuKXhB/pZe+H4N/BZ0mzXeuyCSrrJu14vn0/K/O3JjVtX4kBtklbnwEFm6s9JcHMtn/C8W+GxvpkaOuBLZTrQrf6jB7dYvG+UGe3bL3z8R9rDDYHFn83fKlbbXrxEkZgg9cnBL5Lzpe+w2cqaBHfgOcMM2a/Ew0UbvN/H2MQHvqNGyVtbI+lt2EBsdKjJqEQcZ2t4sP5w5lRtysHCM4u5lCyp/oKRS+i8PKiZ3NpZ1RzdDKhaXRzdFRva2Vuc4GhY3ZhbFkXbjCCF2oGCSqGSIb3DQEHAqCCF1swghdXAgEDMQ8wDQYJYIZIAWUDBAIBBQAwgYIGCyqGSIb3DQEJEAEEoHMEcTBvAgEBBglghkgBhv1sBwEwMTANBglghkgBZQMEAgEFAAQgqqfYVyuLQuUKBVPNPZZmsVV896dadAaqZl1VCX1mRIYCECKEZ+dEgrHyNcxjqrRmVDIYDzIwMjYwMzE0MTExOTQwWgIJAJoyqry8yZHjoIITOjCCBu0wggTVoAMCAQICEAqA7xhLjfEFgtHEdqeVdGgwDQYJKoZIhvcNAQELBQAwaTELMAkGA1UEBhMCVVMxFzAVBgNVBAoTDkRpZ2lDZXJ0LCBJbmMuMUEwPwYDVQQDEzhEaWdpQ2VydCBUcnVzdGVkIEc0IFRpbWVTdGFtcGluZyBSU0E0MDk2IFNIQTI1NiAyMDI1IENBMTAeFw0yNTA2MDQwMDAwMDBaFw0zNjA5MDMyMzU5NTlaMGMxCzAJBgNVBAYTAlVTMRcwFQYDVQQKEw5EaWdpQ2VydCwgSW5jLjE7MDkGA1UEAxMyRGlnaUNlcnQgU0hBMjU2IFJTQTQwOTYgVGltZXN0YW1wIFJlc3BvbmRlciAyMDI1IDEwggIiMA0GCSqGSIb3DQEBAQUAA4ICDwAwggIKAoICAQDQRqwtEsae0OquYFazK1e6b1H/hnAKAd/KN8wZQjBjMqiZ3xTWcfsLwOvRxUwXcGx8AUjni6bz52fGTfr6PHRNv6T7zsf1Y/E3IU8kgNkeECqVQ+3bzWYesFtkepErvUSbf+EIYLkrLKd6qJnuzK8Vcn0DvbDMemQFoxQ2Dsw4vEjoT1FpS54dNApZfKY61HAldytxNM89PZXUP/5wWWURK+IfxiOg8W9lKMqzdIo7VA1R0V3Zp3DjjANwqAf4lEkTlCDQ0/fKJLKLkzGBTpx6EYevvOi7XOc4zyh1uSqgr6UnbksIcFJqLbkIXIPbcNmA98Oskkkrvt6lPAw/p4oDSRZreiwB7x9ykrjS6GS3NR39iTTFS+ENTqW8m6THuOmHHjQNC3zbJ6nJ6SXiLSvw4Smz8U07hqF+8CTXaETkVWz0dVVZw7knh1WZXOLHgDvundrAtuvz0D3T+dYaNcwafsVCGZKUhQPL1naFKBy1p6llN3QgshRta6Eq4B40h5avMcpi54wm0i2ePZD5pPIssoszQyF4//3DoK2O65Uck5Wggn8O2klETsJ7u8xEehGifgJYi+6I03UuT1j7FnrqVrOzaQoVJOeeStPeldYRNMmSF3voIgMFtNGh86w3ISHNm0IaadCKCkUe2LnwJKa8TIlwCUNVwppwn4D3/Pt5pwIDAQABo4IBlTCCAZEwDAYDVR0TAQH/BAIwADAdBgNVHQ4EFgQU5Dv88jHt/f3X85FxYxlQQ89hjOgwHwYDVR0jBBgwFoAU729TSunkBnx6yuKQVvYv1Ensy04wDgYDVR0PAQH/BAQDAgeAMBYGA1UdJQEB/wQMMAoGCCsGAQUFBwMIMIGVBggrBgEFBQcBAQSBiDCBhTAkBggrBgEFBQcwAYYYaHR0cDovL29jc3AuZGlnaWNlcnQuY29tMF0GCCsGAQUFBzAChlFodHRwOi8vY2FjZXJ0cy5kaWdpY2VydC5jb20vRGlnaUNlcnRUcnVzdGVkRzRUaW1lU3RhbXBpbmdSU0E0MDk2U0hBMjU2MjAyNUNBMS5jcnQwXwYDVR0fBFgwVjBUoFKgUIZOaHR0cDovL2NybDMuZGlnaWNlcnQuY29tL0RpZ2lDZXJ0VHJ1c3RlZEc0VGltZVN0YW1waW5nUlNBNDA5NlNIQTI1NjIwMjVDQTEuY3JsMCAGA1UdIAQZMBcwCAYGZ4EMAQQCMAsGCWCGSAGG/WwHATANBgkqhkiG9w0BAQsFAAOCAgEAZSqt8RwnBLmuYEHs0QhEnmNAciH45PYiT9s1i6UKtW+FERp8FgXRGQ/YAavXzWjZhY+hIfP2JkQ38U+wtJPBVBajYfrbIYG+Dui4I4PCvHpQuPqFgqp1PzC/ZRX4pvP/ciZmUnthfAEP1HShTrY+2DE5qjzvZs7JIIgt0GCFD9ktx0LxxtRQ7vllKluHWiKk6FxRPyUPxAAYH2Vy1lNM4kzekd8oEARzFAWgeW3az2xejEWLNN4eKGxDJ8WDl/FQUSntbjZ80FU3i54tpx5F/0Kr15zW/mJAxZMVBrTE2oi0fcI8VMbtoRAmaaslNXdCG1+lqvP4FbrQ6IwSBXkZagHLhFU9HCrG/syTRLLhAezu/3Lr00GrJzPQFnCEH1Y58678IgmfORBPC1JKkYaEt2OdDh4GmO0/5cHelAK2/gTlQJINqDr6JfwyYHXSd+V08X1JUPvB4ILfJdmL+66Gp3CSBXG6IwXMZUXBhtCyIaehr0XkBoDIGMUG1dUtwq1qmcwbdUfcSYCn+OwncVUXf53VJUNOaMWMts0VlRYxe5nK+At+DI96HAlXHAL5SlfYxJ7La54i71McVWRP66bW+yERNpbJCjyCYG2j+bdpxo/1Cy4uPcU3AWVPGrbn5PhDBf3Froguzzhk++ami+r3Qrx5bIbY3TVzgiFI7Gq3zWcwgga0MIIEnKADAgECAhANx6xXBf8hmS5AQyIMOkmGMA0GCSqGSIb3DQEBCwUAMGIxCzAJBgNVBAYTAlVTMRUwEwYDVQQKEwxEaWdpQ2VydCBJbmMxGTAXBgNVBAsTEHd3dy5kaWdpY2VydC5jb20xITAfBgNVBAMTGERpZ2lDZXJ0IFRydXN0ZWQgUm9vdCBHNDAeFw0yNTA1MDcwMDAwMDBaFw0zODAxMTQyMzU5NTlaMGkxCzAJBgNVBAYTAlVTMRcwFQYDVQQKEw5EaWdpQ2VydCwgSW5jLjFBMD8GA1UEAxM4RGlnaUNlcnQgVHJ1c3RlZCBHNCBUaW1lU3RhbXBpbmcgUlNBNDA5NiBTSEEyNTYgMjAyNSBDQTEwggIiMA0GCSqGSIb3DQEBAQUAA4ICDwAwggIKAoICAQC0eDHTCphBcr48RsAcrHXbo0ZodLRRF51NrY0NlLWZloMsVO1DahGPNRcybEKq+RuwOnPhof6pvF4uGjwjqNjfEvUi6wuim5bap+0lgloM2zX4kftn5B1IpYzTqpyFQ/4Bt0mAxAHeHYNnQxqXmRinvuNgxVBdJkf77S2uPoCj7GH8BLuxBG5AvftBdsOECS1UkxBvMgEdgkFiDNYiOTx4OtiFcMSkqTtF2hfQz3zQSku2Ws3IfDReb6e3mmdglTcaarps0wjUjsZvkgFkriK9tUKJm/s80FiocSk1VYLZlDwFt+cVFBURJg6zMUjZa/zbCclF83bRVFLeGkuAhHiGPMvSGmhgaTzVyhYn4p0+8y9oHRaQT/aofEnS5xLrfxnGpTXiUOeSLsJygoLPp66bkDX1ZlAeSpQl92QOMeRxykvq6gbylsXQskBBBnGy3tW/AMOMCZIVNSaz7BX8VtYGqLt9MmeOreGPRdtBx3yGOP+rx3rKWDEJlIqLXvJWnY0v5ydPpOjL6s36czwzsucuoKs7Yk/ehb//Wx+5kMqIMRvUBDx6z1ev+7psNOdgJMoiwOrUG2ZdSoQbU2rMkpLiQ6bGRinZbI4OLu9BMIFm1UUl9VnePs6BaaeEWvjJSjNm2qA+sdFUeEY0qVjPKOWug/G6X5uAiynM7Bu2ayBjUwIDAQABo4IBXTCCAVkwEgYDVR0TAQH/BAgwBgEB/wIBADAdBgNVHQ4EFgQU729TSunkBnx6yuKQVvYv1Ensy04wHwYDVR0jBBgwFoAU7NfjgtJxXWRM3y5nP+e6mK4cD08wDgYDVR0PAQH/BAQDAgGGMBMGA1UdJQQMMAoGCCsGAQUFBwMIMHcGCCsGAQUFBwEBBGswaTAkBggrBgEFBQcwAYYYaHR0cDovL29jc3AuZGlnaWNlcnQuY29tMEEGCCsGAQUFBzAChjVodHRwOi8vY2FjZXJ0cy5kaWdpY2VydC5jb20vRGlnaUNlcnRUcnVzdGVkUm9vdEc0LmNydDBDBgNVHR8EPDA6MDigNqA0hjJodHRwOi8vY3JsMy5kaWdpY2VydC5jb20vRGlnaUNlcnRUcnVzdGVkUm9vdEc0LmNybDAgBgNVHSAEGTAXMAgGBmeBDAEEAjALBglghkgBhv1sBwEwDQYJKoZIhvcNAQELBQADggIBABfO+xaAHP4HPRF2cTC9vgvItTSmf83Qh8WIGjB/T8ObXAZz8OjuhUxjaaFdleMM0lBryPTQM2qEJPe36zwbSI/mS83afsl3YTj+IQhQE7jU/kXjjytJgnn0hvrV6hqWGd3rLAUt6vJy9lMDPjTLxLgXf9r5nWMQwr8Myb9rEVKChHyfpzee5kH0F8HABBgr0UdqirZ7bowe9Vj2AIMD8liyrukZ2iA/wdG2th9y1IsA0QF8dTXqvcnTmpfeQh35k5zOCPmSNq1UH410ANVko43+Cdmu4y81hjajV/gxdEkMx1NKU4uHQcKfZxAvBAKqMVuqte69M9J6A47OvgRaPs+2ykgcGV00TYr2Lr3ty9qIijanrUR3anzEwlvzZiiyfTPjLbnFRsjsYg39OlV8cipDoq7+qNNjqFzeGxcytL5TTLL4ZaoBdqbhOhZ3ZRDUphPvSRmMThi0vw9vODRzW6AxnJll38F0cuJG7uEBYTptMSbhdhGQDpOXgpIUsWTjd6xpR6oaQf/DJbg3s6KCLPAlZ66RzIg9sC+NJpud/v4+7RWsWCiKi9EOLLHfMR2ZyJ/+xhCx9yHbxtl5TPau1j/1MIDpMPx0LckTetiSuEtQvLsNz3Qbp7wGWqbIiOWCnb5WqxL3/BAPvIXKUjPSxyZsq8WhbaM2tszWkPZPubdcMIIFjTCCBHWgAwIBAgIQDpsYjvnQLefv21DiCEAYWjANBgkqhkiG9w0BAQwFADBlMQswCQYDVQQGEwJVUzEVMBMGA1UEChMMRGlnaUNlcnQgSW5jMRkwFwYDVQQLExB3d3cuZGlnaWNlcnQuY29tMSQwIgYDVQQDExtEaWdpQ2VydCBBc3N1cmVkIElEIFJvb3QgQ0EwHhcNMjIwODAxMDAwMDAwWhcNMzExMTA5MjM1OTU5WjBiMQswCQYDVQQGEwJVUzEVMBMGA1UEChMMRGlnaUNlcnQgSW5jMRkwFwYDVQQLExB3d3cuZGlnaWNlcnQuY29tMSEwHwYDVQQDExhEaWdpQ2VydCBUcnVzdGVkIFJvb3QgRzQwggIiMA0GCSqGSIb3DQEBAQUAA4ICDwAwggIKAoICAQC/5pBzaN675F1KPDAiMGkz7MKnJS7JIT3yithZwuEppz1Yq3aaza57G4QNxDAf8xukOBbrVsaXbR2rsnnyyhHS5F/WBTxSD1Ifxp4VpX6+n6lXFllVcq9ok3DCsrp1mWpzMpTREEQQLt+C8weE5nQ7bXHiLQwb7iDVySAdYyktzuxeTsiT+CFhmzTrBcZe7FsavOvJz82sNEBfsXpm7nfISKhmV1efVFiODCu3T6cw2Vbuyntd463JT17lNecxy9qTXtyOj4DatpGYQJB5w3jHtrHEtWoYOAMQjdjUN6QuBX2I9YI+EJFwq1WCQTLX2wRzKm6RAXwhTNS8rhsDdV14Ztk6MUSaM0C/CNdaSaTC5qmgZ92kJ7yhTzm1EVgX9yRcRo9k98FpiHaYdj1ZXUJ2h4mXaXpI8OCiEhtmmnTK3kse5w5jrubU75KSOp493ADkRSWJtppEGSt+wJS00mFt6zPZxd9LBADMfRyVw4/3IbKyEbe7f/LVjHAsQWCqsWMYRJUadmJ+9oCw++hkpjPRiQfhvbfmQ6QYuKZ3AeEPlAwhHbJUKSWJbOUOUlFHdL4mrLZBdd56rF+NP8m800ERElvlEFDrMcXKchYiCd98THU/Y+whX8QgUWtvsauGi0/C1kVfnSD8oR7FwI+isX4KJpn15GkvmB0t9dmpsh3lGwIDAQABo4IBOjCCATYwDwYDVR0TAQH/BAUwAwEB/zAdBgNVHQ4EFgQU7NfjgtJxXWRM3y5nP+e6mK4cD08wHwYDVR0jBBgwFoAUReuir/SSy4IxLVGLp6chnfNtyA8wDgYDVR0PAQH/BAQDAgGGMHkGCCsGAQUFBwEBBG0wazAkBggrBgEFBQcwAYYYaHR0cDovL29jc3AuZGlnaWNlcnQuY29tMEMGCCsGAQUFBzAChjdodHRwOi8vY2FjZXJ0cy5kaWdpY2VydC5jb20vRGlnaUNlcnRBc3N1cmVkSURSb290Q0EuY3J0MEUGA1UdHwQ+MDwwOqA4oDaGNGh0dHA6Ly9jcmwzLmRpZ2ljZXJ0LmNvbS9EaWdpQ2VydEFzc3VyZWRJRFJvb3RDQS5jcmwwEQYDVR0gBAowCDAGBgRVHSAAMA0GCSqGSIb3DQEBDAUAA4IBAQBwoL9DXFXnOF+go3QbPbYW1/e/Vwe9mqyhhyzshV6pGrsi+IcaaVQi7aSId229GhT0E0p6Ly23OO/0/4C5+KH38nLeJLxSA8hO0Cre+i1Wz/n096wwepqLsl7Uz9FDRJtDIeuWcqFItJnLnU+nBgMTdydE1Od/6Fmo8L8vC6bp8jQ87PcDx4eo0kxAGTVGamlUsLihVo7spNU96LHc/RzY9HdaXFSMb++hUD38dglohJ9vytsgjTVgHAIDyyCwrFigDkBjxZgiwbJZ9VVrzyerbHbObyMt9H5xaiNrIv8SuFQtJ37YOtnwtoeW/VvRXKwYw02fc7cBqZ9Xql4o4rmUMYIDfDCCA3gCAQEwfTBpMQswCQYDVQQGEwJVUzEXMBUGA1UEChMORGlnaUNlcnQsIEluYy4xQTA/BgNVBAMTOERpZ2lDZXJ0IFRydXN0ZWQgRzQgVGltZVN0YW1waW5nIFJTQTQwOTYgU0hBMjU2IDIwMjUgQ0ExAhAKgO8YS43xBYLRxHanlXRoMA0GCWCGSAFlAwQCAQUAoIHRMBoGCSqGSIb3DQEJAzENBgsqhkiG9w0BCRABBDAcBgkqhkiG9w0BCQUxDxcNMjYwMzE0MTExOTQwWjArBgsqhkiG9w0BCRACDDEcMBowGDAWBBTdYjCshgotMGvaOLFoeVIwB/tBfjAvBgkqhkiG9w0BCQQxIgQgniQ2D33gzzNWgaT0OSioT/G6ngCa8liYUg7hqLYEkfowNwYLKoZIhvcNAQkQAi8xKDAmMCQwIgQgSqA/oizXXITFXJOPgo5na5yuyrM/420mmqM08UYRCjMwDQYJKoZIhvcNAQEBBQAEggIAQt5X7q9n8SjL2ZJv5TbGtdsPAUu5LJOnEylrjOff10SmGyTLujvTU3CstYl+M2s7K9QkrE0wGJ5GRxDrVwT51T0jkat0qKoDYHecqXYcRRsDDOjrLWIf4TPEJ4zUkmLddu9Ird1b+4386++P6b6uuXfklAZC11ykmzCIyr6PDWDV71fB+AQoVg0FZhe+B6kXM5WGQK0zxxcTVEWyFH+nl23KewmvO6ykS4eC8bgCFLe/AgNy0Y9gehP0m3gzIgo6zn6qyF+ao5z8ISHrkSdbpyfyIPjVmMAhZczSXyY+xIIY48izvzYvgwAmWIeKht5tPLhPa+A7hsGa+BWj/OE9L73K/EGiu2w6BRlBlIuOVatLpWnOGqWTSeepvOJfTZh4woh9z68XbN9rkD98idn6p7AhjjQGP6TI7HpPKQxsTrRKKTDhMeT4lGDJjzFSkt6var8dMFhe/T1YPb4bX/TkD5bDbhcC8jJCFQMuaAJDlQAXTpc2HJyBAa9WPZfZt7GdBNcQ8MkRDEEAOmv1Lb5j/Fb2pPI7jNzYBjch5REpTJSz/+v1IW1HjkMFr6zSotAucZHtiGwf5cfbm3JlYEXcXnBoyvlX4bT4zKKHzU1l7KuRHaLxjIOnh6Y+rBcNUIDJnqZRCyFmQS9y2XXljHvadNBN5tubjaflwpL7lLrIb3tjcGFkWRTAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA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KRQY3pdh+B4QFysuMSLMMEtTVXHVV92Xu/Cnbp1KBQAX8KCaapjw85Ob5+twOzSxTzD+OINEFh3IkyaCg6Tufd759TupigljT8s3XfSKJIpXrOSyakigv4xYWWU/972xu72nxkVenVOmOyeeWEcRQduQcLL5smVXYOX+MCLApY1BYkGGShbx5OfY/DLL9/n6OCG8BRV++TjkUsbdyPyORSgsBTQCjSlxY+Y8OGP1D0lRGBg8KgVMC7igTc///////////////////sYf////////////////8EyHlAMtBAwBzEfwik2ISXV01phRrcFCE5Z2+hYSKmoIq2p6+798yaTX5rtoeylPo4lxfbOc//uSxLgAJ64PGxm9AAK6s6cvnsABiO46XoveEht48ow3k32hgys5v73mdccxeT3tEs6EsttxkhQV2hIEct83aJfdxIICg7jOCxXP683ml7K1lJusJAiFkkMvjwPi99MVKFc7JZLA+gun4eAcQlhXePEAzaLgHB8WHiKNEuWSvQRINM6MzMztWscvjBxz9337w5pnqIZEXeKEgskjMcKaVyP0lkAiHqfa1e/mYrb1Fl8fMfdp5vEnljw3huh3sSRIc7aX5GZN/H70534dNE4GQeD7hHNvV0bYrChPe+WfzrMwowoKBQSEB02TznSZk2CAEKkeowTFBURm+ujn00cJx31iCfmjRt9UkMFGk0Fa2jldqoz+kjU0AzVKzmOBgzBbILUbhOCLVLNpIKtwO9dG2eEeSBaOShSzMbhHjw6EdVcZEuyJIk0ACG0Xk4144S4pcn5wGQ2n4chKCSHWr4SYWsamYEIxCae3r9/qZWLSZDuxuummYZBH+La0smdfKhgwXhwVIol8BJJ689bVIXRWd/omiCRj8G6N1814xJa4olxeE//7ksSIgBWtl1PnpffKrzNqvPMx6aUDKKJMhD7SOyyGV2N0prD0eLqzSbRe3A1A9aFly779ch6bL9/mVjt2FvTHV3ly1D9ccTZq1eaQVhyRjZVAk/tfPpaophb2jaqciIZkQRgAAIidQsqmExyXF0RurIk/TsVDtk3OrJI15c71iuPT3zu1s0pr3x7+feIMaSHuJ2+KyQY7qOwtjOxs+oUKqTaVXEQ9FeNtjrumYcjOkllEREZg8FOfk6cF4iCBKINhKMa7R86aUUCAwK/axHopXPc+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"


def fmt_size(b):
    if b <= 0: return ""
    if b < 1024: return f"{b} B"
    if b < 1048576: return f"{b/1024:.1f} KB"
    if b < 1073741824: return f"{b/1048576:.1f} MB"
    return f"{b/1073741824:.2f} GB"


@app.route("/")
def index():
    # Inject the session token into the page so JS can use it
    return HTML_PAGE.replace(
        "const API = '';",
        f"const API = '';\nconst SESSION_TOKEN = '{_SESSION_TOKEN}';"
    )


@app.route("/api/connect", methods=["POST"])
def api_connect():
    global conn, cfg
    d = request.json
    host = d.get("host", "")
    user, pw = d.get("username", ""), d.get("password", "")
    proto = d.get("protocol", "FTP")
    trust_fp = d.get("trust_fingerprint")  # set when user accepts a cert/key

    try:
        port = int(d.get("port", 21))
        if port < 1 or port > 65535:
            raise ValueError("out of range")
    except (ValueError, TypeError):
        return jsonify({"error": "Invalid port number"}), 400

    if conn:
        try: conn.disconnect()
        except Exception: pass

    try:
        if proto == "SFTP":
            if not HAS_PARAMIKO:
                return jsonify({"error": "SFTP requires paramiko: pip install paramiko"}), 400
            conn = SFTPConn()
            conn.connect(host, port, user, password=pw, trust_fingerprint=trust_fp)
        else:
            conn = FTPConn()
            conn.connect(host, port, user, pw, use_tls=(proto == "FTPS"), trust_fingerprint=trust_fp)

        cwd = "/"
        try: cwd = conn.pwd()
        except Exception: pass

        # Save bookmark (now including port in dedup check)
        bms = cfg.setdefault("bookmarks", [])
        if not any(b.get("host") == host and b.get("port") == port
                   and b.get("user") == user and b.get("proto") == proto for b in bms):
            bms.append({"host": host, "port": port, "user": user, "proto": proto})
            save_config(cfg)

        _start_keepalive()
        return jsonify({"ok": True, "cwd": cwd, "proto": proto})
    except CertificateError as e:
        conn = None
        return jsonify({
            "error": str(e),
            "cert_error": True,
            "fingerprint": e.fingerprint,
            "is_changed": e.is_changed,
        }), 400
    except Exception as e:
        conn = None
        return jsonify({"error": str(e)}), 400


@app.route("/api/disconnect", methods=["POST"])
def api_disconnect():
    global conn
    _stop_keepalive()
    if conn:
        try: conn.disconnect()
        except Exception: pass
        conn = None
    return jsonify({"ok": True})


@app.route("/api/trust/reset", methods=["POST"])
def api_trust_reset():
    """Remove a stored fingerprint so user can re-accept a changed key."""
    d = request.json
    host = d.get("host", "")
    try:
        port = int(d.get("port", 0))
    except (ValueError, TypeError):
        return jsonify({"error": "Invalid port"}), 400
    proto = d.get("protocol", "")
    if host and port and proto:
        _remove_trusted_fingerprint(host, port, proto)
        return jsonify({"ok": True})
    return jsonify({"error": "Missing host/port/protocol"}), 400


@app.route("/api/list")
def api_list():
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    path = request.args.get("path", "/")
    try:
        files = conn.listdir(path)
        return jsonify({"files": files, "path": path})
    except Exception as e:
        _log.exception("API error")
        return jsonify({"error": str(e)}), 500


@app.route("/api/download")
def api_download():
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    path = request.args.get("path", "")
    if not path:
        return jsonify({"error": "No path"}), 400
    try:
        name = PurePosixPath(path).name
        # Stream to temp file to avoid buffering entire file in RAM
        tmp = tempfile.NamedTemporaryFile(delete=False, dir=str(CONFIG_DIR), suffix="_" + name)
        tmp_path = tmp.name
        tmp.close()
        try:
            conn.download_to_file(path, tmp_path)
            size = os.path.getsize(tmp_path)
            _log_transfer("download", path, size)
            # send_file will stream from disk; we delete after response
            response = send_file(tmp_path, download_name=name, as_attachment=True)
            @response.call_on_close
            def _cleanup():
                try: os.unlink(tmp_path)
                except OSError: pass
            return response
        except Exception:
            try: os.unlink(tmp_path)
            except OSError: pass
            raise
    except Exception as e:
        _log_transfer("download", path, ok=False, detail=str(e))
        return jsonify({"error": str(e)}), 500


@app.route("/api/upload", methods=["POST"])
def api_upload():
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    path = request.form.get("path", "/")
    f = request.files.get("file")
    if not f:
        return jsonify({"error": "No file"}), 400
    remote = str(PurePosixPath(path) / f.filename)
    try:
        conn.upload_stream(remote, f.stream)
        size = f.stream.tell() if hasattr(f.stream, 'tell') else 0
        _log_transfer("upload", remote, size)
        return jsonify({"ok": True, "filename": f.filename})
    except Exception as e:
        _log_transfer("upload", remote, ok=False, detail=str(e))
        return jsonify({"error": str(e)}), 500


@app.route("/api/mkdir", methods=["POST"])
def api_mkdir():
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    path = request.json.get("path", "")
    try:
        conn.mkdir(path)
        return jsonify({"ok": True})
    except Exception as e:
        _log.exception("API error")
        return jsonify({"error": str(e)}), 500


@app.route("/api/delete", methods=["POST"])
def api_delete():
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    path = request.json.get("path", "")
    try:
        try:
            conn.remove(path)
        except Exception:
            # rmdir fails on non-empty dirs, so delete recursively
            _recursive_delete(path)
        _log_transfer("delete", path)
        return jsonify({"ok": True})
    except Exception as e:
        _log.exception("API error")
        return jsonify({"error": str(e)}), 500

def _recursive_delete(path):
    """Recursively delete a remote directory and all its contents."""
    try:
        entries = conn.listdir(path)
    except Exception:
        # If listing fails, try simple rmdir
        conn.rmdir(path)
        return
    for entry in entries:
        if entry.get("name") in (".", ".."):
            continue
        child = path.rstrip("/") + "/" + entry["name"]
        if entry.get("is_dir"):
            _recursive_delete(child)
        else:
            try:
                conn.remove(child)
            except Exception:
                pass
    conn.rmdir(path)


@app.route("/api/rename", methods=["POST"])
def api_rename():
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    d = request.json
    try:
        conn.rename(d["old"], d["new"])
        _log_transfer("rename", d["old"], detail=f"→ {d['new']}")
        return jsonify({"ok": True})
    except Exception as e:
        _log.exception("API error")
        return jsonify({"error": str(e)}), 500


@app.route("/api/bookmarks")
def api_bookmarks():
    return jsonify({"bookmarks": cfg.get("bookmarks", [])})


@app.route("/api/isdir")
def api_isdir():
    if not conn: return jsonify({"is_dir": False})
    path = request.args.get("path", "")
    try:
        return jsonify({"is_dir": conn.is_dir(path)})
    except Exception:
        return jsonify({"is_dir": False})


@app.route("/api/chmod", methods=["POST"])
def api_chmod():
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    d = request.json
    path = d.get("path", "")
    mode = d.get("mode", "")
    if not path or not mode:
        return jsonify({"error": "Path and mode required"}), 400
    try:
        mode_int = int(mode, 8)
        if isinstance(conn, FTPConn):
            conn.ftp.sendcmd(f"SITE CHMOD {mode} {path}")
        else:
            conn.sftp.chmod(path, mode_int)
        return jsonify({"ok": True})
    except Exception as e:
        _log.exception("API error")
        return jsonify({"error": str(e)}), 500


@app.route("/api/local/list")
def api_local_list():
    path = request.args.get("path", str(Path.home()))
    p = Path(path)
    if not p.exists():
        return jsonify({"error": "Path does not exist"}), 400
    files = []
    try:
        for entry in sorted(p.iterdir(), key=lambda e: (not e.is_dir(), e.name.lower())):
            if entry.name.startswith(".aivelo"): continue
            try:
                st = entry.stat()
                files.append({
                    "name": entry.name,
                    "size": st.st_size if not entry.is_dir() else 0,
                    "mtime": datetime.fromtimestamp(st.st_mtime).strftime("%Y-%m-%d %H:%M"),
                    "is_dir": entry.is_dir(),
                    "full_path": str(entry),
                })
            except PermissionError:
                continue
    except PermissionError:
        return jsonify({"error": "Permission denied"}), 403
    return jsonify({"files": files, "path": str(p), "parent": str(p.parent)})


@app.route("/api/local/mkdir", methods=["POST"])
def api_local_mkdir():
    """Create a new folder on the local filesystem."""
    d = request.json
    parent = d.get("parent", "")
    name = d.get("name", "")
    if not parent or not name:
        return jsonify({"error": "Missing parent or name"}), 400
    try:
        new_path = Path(parent) / name
        new_path.mkdir(parents=False, exist_ok=False)
        return jsonify({"ok": True, "path": str(new_path)})
    except FileExistsError:
        return jsonify({"error": "Folder already exists"}), 400
    except Exception as e:
        _log.exception("API error")
        return jsonify({"error": str(e)}), 500


@app.route("/api/local/rename", methods=["POST"])
def api_local_rename():
    """Rename a local file or folder."""
    d = request.json
    old_path = d.get("old", "")
    new_name = d.get("new_name", "")
    if not old_path or not new_name:
        return jsonify({"error": "Missing path or name"}), 400
    try:
        p = Path(old_path)
        new_path = p.parent / new_name
        p.rename(new_path)
        return jsonify({"ok": True})
    except Exception as e:
        _log.exception("API error")
        return jsonify({"error": str(e)}), 500


@app.route("/api/local/delete", methods=["POST"])
def api_local_delete():
    """Delete a local file or folder."""
    d = request.json
    path = d.get("path", "")
    if not path:
        return jsonify({"error": "Missing path"}), 400
    try:
        p = Path(path)
        if p.is_dir():
            import shutil
            shutil.rmtree(str(p))
        else:
            p.unlink()
        return jsonify({"ok": True})
    except Exception as e:
        _log.exception("API error")
        return jsonify({"error": str(e)}), 500


@app.route("/api/local/upload_to_remote", methods=["POST"])
def api_local_upload():
    """Upload a local file OR folder (by path) to the remote server."""
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    d = request.json
    local_path = d.get("local_path", "")
    remote_dir = d.get("remote_dir", "/")
    lp = Path(local_path)
    if not local_path or not lp.exists():
        return jsonify({"error": "Invalid local path"}), 400

    # --- Single file upload ---
    if lp.is_file():
        name = lp.name
        remote_path = str(PurePosixPath(remote_dir) / name)
        try:
            fsize = lp.stat().st_size
            _xfer_start(1)
            _xfer_file(name, fsize, 1)
            with open(lp, "rb") as f:
                conn.upload_stream(remote_path, f, progress_cb=_xfer_chunk)
            _xfer_done()
            _log_transfer("upload", remote_path, fsize, detail=f"from {local_path}")
            return jsonify({"ok": True, "filename": name})
        except Exception as e:
            _xfer_done()
            _log_transfer("upload", remote_path, ok=False, detail=str(e))
            return jsonify({"error": str(e)}), 500

    # --- Folder upload (recursive) ---
    if lp.is_dir():
        uploaded = 0
        errors = []
        base_remote = str(PurePosixPath(remote_dir) / lp.name)
        # Use os.walk for robust cross-platform recursive traversal
        dirs_to_create = [base_remote]
        files_to_upload = []
        for root, dirs, filenames in os.walk(str(lp)):
            root_path = Path(root)
            rel_root = root_path.relative_to(lp)
            remote_root = str(PurePosixPath(base_remote) / str(rel_root).replace("\\", "/")).rstrip("/.")
            if remote_root and remote_root != base_remote:
                dirs_to_create.append(remote_root)
            for fname in filenames:
                local_fp = root_path / fname
                remote_fp = str(PurePosixPath(remote_root) / fname)
                files_to_upload.append((local_fp, remote_fp))
        # Create directories first (sorted by depth)
        for dpath in sorted(set(dirs_to_create), key=lambda x: x.count("/")):
            try:
                conn.mkdir(dpath)
            except Exception:
                pass  # dir may already exist
        # Upload files (streaming with progress)
        _xfer_start(len(files_to_upload))
        for idx_f, (fp, remote_fp) in enumerate(files_to_upload):
            try:
                fsize = fp.stat().st_size
                _xfer_file(fp.name, fsize, idx_f + 1)
                with open(fp, "rb") as f:
                    conn.upload_stream(remote_fp, f, progress_cb=_xfer_chunk)
                _log_transfer("upload", remote_fp, fsize, detail=f"from {fp}")
                uploaded += 1
            except Exception as e:
                errors.append(f"{fp.name}: {e}")
                _log_transfer("upload", remote_fp, ok=False, detail=str(e))
        _xfer_done()
        result = {"ok": True, "uploaded": uploaded, "folder": lp.name,
                  "total_found": len(files_to_upload)}
        if errors:
            result["errors"] = errors
        return jsonify(result)

    return jsonify({"error": "Path is not a file or folder"}), 400


@app.route("/api/local/download_from_remote", methods=["POST"])
def api_local_download():
    """Download a remote file to a specific local directory."""
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    d = request.json
    remote_path = d.get("remote_path", "")
    local_dir = d.get("local_dir", str(Path.home()))
    if not remote_path:
        return jsonify({"error": "No remote path"}), 400
    is_dir = d.get("is_dir", False)

    # --- Recursive directory download ---
    if is_dir:
        name = PurePosixPath(remote_path).name
        base_local = Path(local_dir) / name
        base_local.mkdir(parents=True, exist_ok=True)
        downloaded = 0
        errors = []
        # First scan to count files
        all_files = []
        dirs_to_scan = [(remote_path, base_local)]
        while dirs_to_scan:
            rdir, ldir = dirs_to_scan.pop(0)
            try:
                entries = conn.listdir(rdir)
            except Exception as e:
                errors.append(str(e))
                continue
            for entry in entries:
                rentry = rdir.rstrip("/") + "/" + entry["name"]
                lentry = ldir / entry["name"]
                if entry["is_dir"]:
                    lentry.mkdir(parents=True, exist_ok=True)
                    dirs_to_scan.append((rentry, lentry))
                else:
                    all_files.append((rentry, lentry, entry.get("size", 0)))
        _xfer_start(len(all_files))
        for idx_f, (rentry, lentry, esize) in enumerate(all_files):
            _xfer_file(lentry.name, esize, idx_f + 1)
            try:
                conn.download_to_file(rentry, str(lentry), progress_cb=_xfer_chunk)
                downloaded += 1
            except Exception as e:
                errors.append(str(e))
        _xfer_done()
        total = downloaded + len(errors)
        _log_transfer("download", remote_path, detail=f"folder: {downloaded}/{total} files")
        return jsonify({"ok": True, "downloaded": downloaded, "total": total, "errors": errors})

    name = PurePosixPath(remote_path).name
    local_path = Path(local_dir) / name
    try:
        _xfer_start(1)
        # Try to get remote size for progress
        try:
            rsize = conn.size(remote_path) if hasattr(conn, 'size') else 0
        except Exception:
            rsize = 0
        _xfer_file(name, rsize or 0, 1)
        conn.download_to_file(remote_path, str(local_path), progress_cb=_xfer_chunk)
        _xfer_done()
        size = local_path.stat().st_size
        _log_transfer("download", remote_path, size, detail=f"to {local_path}")
        return jsonify({"ok": True, "filename": name, "local_path": str(local_path)})
    except Exception as e:
        _xfer_done()
        _log_transfer("download", remote_path, ok=False, detail=str(e))
        return jsonify({"error": str(e)}), 500


@app.route("/api/preview")
def api_preview():
    """Preview a remote file: returns content + type info for the UI."""
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    path = request.args.get("path", "")
    if not path:
        return jsonify({"error": "No path"}), 400
    name = PurePosixPath(path).name
    ext = PurePosixPath(name).suffix.lower()

    # Determine file type
    IMAGE_EXTS = {".jpg", ".jpeg", ".png", ".gif", ".bmp", ".webp", ".svg", ".ico"}
    TEXT_EXTS = {
        ".txt", ".md", ".csv", ".json", ".xml", ".yaml", ".yml", ".ini", ".cfg",
        ".log", ".conf", ".env", ".htaccess", ".gitignore",
        ".py", ".js", ".ts", ".jsx", ".tsx", ".html", ".htm", ".css", ".scss",
        ".less", ".php", ".rb", ".java", ".c", ".cpp", ".h", ".hpp", ".cs",
        ".go", ".rs", ".swift", ".kt", ".scala", ".sh", ".bash", ".zsh",
        ".bat", ".ps1", ".sql", ".r", ".m", ".pl", ".lua", ".vim",
        ".toml", ".properties", ".gradle", ".cmake", ".makefile",
        ".dockerfile", ".editorconfig", ".eslintrc", ".prettierrc",
    }
    PDF_EXTS = {".pdf"}
    MAX_PREVIEW = 512 * 1024  # 512KB
    MAX_IMAGE = 8 * 1024 * 1024  # 8MB cap for images

    try:
        # Images and PDFs need full download (but capped)
        if ext in IMAGE_EXTS:
            buf, truncated = conn.download_head(path, MAX_IMAGE)
            if truncated:
                return jsonify({"type": "too_large", "name": name,
                    "message": f"Image too large for preview (>{MAX_IMAGE // 1048576}MB). Use download instead."})
            data = buf.read()
            mime = "image/svg+xml" if ext == ".svg" else f"image/{ext.lstrip('.').replace('jpg','jpeg')}"
            b64 = base64.b64encode(data).decode()
            return jsonify({"type": "image", "mime": mime, "data": b64, "size": len(data), "name": name})

        if ext in PDF_EXTS:
            buf, truncated = conn.download_head(path, MAX_IMAGE)
            if truncated:
                return jsonify({"type": "too_large", "name": name,
                    "message": f"PDF too large for preview (>{MAX_IMAGE // 1048576}MB). Use download instead."})
            data = buf.read()
            b64 = base64.b64encode(data).decode()
            return jsonify({"type": "pdf", "data": b64, "size": len(data), "name": name})

        # Text files: only download first 512KB
        if ext in TEXT_EXTS:
            buf, truncated = conn.download_head(path, MAX_PREVIEW)
            data = buf.read()
            try:
                text = data.decode("utf-8")
            except UnicodeDecodeError:
                try:
                    text = data.decode("latin-1")
                except Exception:
                    return jsonify({"type": "binary", "size": len(data), "name": name})

            lang_map = {
                ".py": "python", ".js": "javascript", ".ts": "typescript",
                ".jsx": "jsx", ".tsx": "tsx", ".html": "html", ".htm": "html",
                ".css": "css", ".scss": "scss", ".less": "less",
                ".php": "php", ".rb": "ruby", ".java": "java",
                ".c": "c", ".cpp": "cpp", ".h": "c", ".hpp": "cpp",
                ".cs": "csharp", ".go": "go", ".rs": "rust",
                ".swift": "swift", ".kt": "kotlin", ".scala": "scala",
                ".sh": "bash", ".bash": "bash", ".zsh": "bash",
                ".bat": "batch", ".ps1": "powershell",
                ".sql": "sql", ".r": "r", ".lua": "lua",
                ".json": "json", ".xml": "xml", ".yaml": "yaml", ".yml": "yaml",
                ".toml": "toml", ".ini": "ini", ".md": "markdown",
                ".csv": "text", ".txt": "text", ".log": "text",
                ".dockerfile": "dockerfile",
            }
            lang = lang_map.get(ext, "text")
            return jsonify({
                "type": "text", "content": text, "language": lang,
                "size": len(data), "name": name, "truncated": truncated,
                "editable": True,
            })

        # Unknown extension: download a small head to check if it's text
        buf, truncated = conn.download_head(path, MAX_PREVIEW)
        data = buf.read()
        try:
            text = data.decode("utf-8")
            return jsonify({
                "type": "text", "content": text, "language": "text",
                "size": len(data), "name": name, "truncated": truncated,
                "editable": True,
            })
        except Exception:
            return jsonify({"type": "binary", "size": len(data), "name": name})

    except Exception as e:
        _log.exception("API error")
        return jsonify({"error": str(e)}), 500


@app.route("/api/save", methods=["POST"])
def api_save():
    """Save edited content back to a remote file. Snapshot should already exist from /api/snapshot.
    If expected_hash is provided, the server compares it against the current file hash
    before writing — this prevents overwriting changes made by another session."""
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    d = request.json
    path = d.get("path", "")
    content = d.get("content", "")
    expected_hash = d.get("expected_hash", "")  # optional: client's last known hash
    if not path:
        return jsonify({"error": "No path"}), 400
    try:
        # Server-side conflict check: if the client sent an expected hash,
        # verify the file hasn't changed since the client loaded it.
        if expected_hash:
            try:
                current_buf = conn.download_bytes(path)
                current_data = current_buf.read()
                current_hash = hashlib.sha256(current_data).hexdigest()
                if current_hash != expected_hash:
                    return jsonify({
                        "error": "conflict",
                        "message": "File was modified on the server since you loaded it",
                        "server_hash": current_hash,
                        "server_size": len(current_data),
                    }), 409
            except Exception:
                pass  # file may not exist yet (new file) — allow save
        data = content.encode("utf-8")
        conn.upload_bytes(path, data)
        new_hash = hashlib.sha256(data).hexdigest()
        return jsonify({"ok": True, "size": len(data), "hash": new_hash})
    except Exception as e:
        _log.exception("API error")
        return jsonify({"error": str(e)}), 500


@app.route("/api/snapshot", methods=["POST"])
def api_snapshot():
    """Create a labeled snapshot of a file. Called automatically when entering
    edit mode (label='auto-edit') or manually via checkpoint button (label='checkpoint').
    Stores the current server version in .aivelo-snapshots/."""
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    d = request.json
    path = d.get("path", "")
    label = d.get("label", "auto-edit")  # auto-edit, checkpoint, pre-rollback
    if not path:
        return jsonify({"error": "No path"}), 400
    # Sanitize label
    label = re.sub(r"[^a-z0-9_-]", "", label.lower())[:20] or "snapshot"
    try:
        existing = conn.download_bytes(path)
        existing_data = existing.read()
        # Allow snapshots of empty files — they still need a restore point

        parent = str(PurePosixPath(path).parent)
        name = PurePosixPath(path).name
        ts = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
        snap_dir = parent.rstrip("/") + "/.aivelo-snapshots"
        try: conn.mkdir(snap_dir)
        except Exception: pass
        # Filename encodes: original.timestamp.label.bak
        snap_name = f"{name}.{ts}.{label}.bak"
        snap_path = snap_dir + "/" + snap_name
        conn.upload_bytes(snap_path, existing_data)
        content_hash = hashlib.sha256(existing_data).hexdigest()
        return jsonify({"ok": True, "snapshot": True,
                        "snapshot_path": snap_path, "size": len(existing_data),
                        "hash": content_hash, "label": label})
    except Exception as e:
        _log.exception("API error")
        return jsonify({"error": str(e)}), 500


@app.route("/api/snapshot/history", methods=["POST"])
def api_snapshot_history():
    """List snapshots for a file, newest first."""
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    d = request.json
    path = d.get("path", "")
    if not path:
        return jsonify({"error": "No path"}), 400
    parent = str(PurePosixPath(path).parent)
    name = PurePosixPath(path).name
    snap_dir = parent.rstrip("/") + "/.aivelo-snapshots"
    snapshots = []
    try:
        entries = conn.listdir(snap_dir)
        prefix = name + "."
        for f in entries:
            if f["name"].startswith(prefix) and f["name"].endswith(".bak"):
                # Parse: filename.TIMESTAMP.LABEL.bak
                middle = f["name"][len(prefix):-4]  # "20260313_120000.auto-edit"
                parts = middle.split(".", 1)
                ts_part = parts[0] if parts else ""
                label = parts[1] if len(parts) > 1 else "snapshot"
                # Format label for display
                label_display = {
                    "auto-edit": "📸 Before editing",
                    "checkpoint": "📌 Manual checkpoint",
                    "pre-rollback": "↩ Before rollback",
                }.get(label, label)
                snapshots.append({
                    "name": f["name"],
                    "path": snap_dir + "/" + f["name"],
                    "timestamp": ts_part,
                    "label": label,
                    "label_display": label_display,
                    "size": f["size"],
                })
        snapshots.sort(key=lambda r: r["timestamp"], reverse=True)
    except Exception:
        pass  # No snapshots dir yet
    # Also check legacy .aivelo-revisions for backward compat
    legacy_dir = parent.rstrip("/") + "/.aivelo-revisions"
    try:
        entries = conn.listdir(legacy_dir)
        prefix = name + "."
        for f in entries:
            if f["name"].startswith(prefix) and f["name"].endswith(".bak"):
                middle = f["name"][len(prefix):-4]
                snapshots.append({
                    "name": f["name"],
                    "path": legacy_dir + "/" + f["name"],
                    "timestamp": middle,
                    "label": "legacy",
                    "label_display": "📁 Legacy revision",
                    "size": f["size"],
                })
        snapshots.sort(key=lambda r: r["timestamp"], reverse=True)
    except Exception:
        pass
    return jsonify({"snapshots": snapshots, "file": name})


@app.route("/api/snapshot/rollback", methods=["POST"])
def api_snapshot_rollback():
    """Restore a file from a snapshot. Creates a pre-rollback snapshot first."""
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    d = request.json
    path = d.get("path", "")
    snapshot_path = d.get("snapshot_path", "")
    if not path or not snapshot_path:
        return jsonify({"error": "Missing path or snapshot"}), 400
    try:
        # Create a pre-rollback snapshot of current state
        try:
            current = conn.download_bytes(path)
            current_data = current.read()
            if current_data:
                parent = str(PurePosixPath(path).parent)
                name = PurePosixPath(path).name
                ts = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
                snap_dir = parent.rstrip("/") + "/.aivelo-snapshots"
                try: conn.mkdir(snap_dir)
                except Exception: pass
                pre_snap = snap_dir + "/" + f"{name}.{ts}.pre-rollback.bak"
                conn.upload_bytes(pre_snap, current_data)
        except Exception:
            pass

        # Restore from snapshot
        buf = conn.download_bytes(snapshot_path)
        data = buf.read()
        conn.upload_bytes(path, data)
        _log_transfer("rollback", path, len(data), detail=f"from {snapshot_path}")
        return jsonify({"ok": True, "restored_size": len(data)})
    except Exception as e:
        _log.exception("API error")
        return jsonify({"error": str(e)}), 500


@app.route("/api/save/check_changed", methods=["POST"])
def api_save_check_changed():
    """Check if a file was modified on the server since it was opened.
    Client sends the original content hash; we compare with current server version."""
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    d = request.json
    path = d.get("path", "")
    original_hash = d.get("original_hash", "")
    if not path:
        return jsonify({"error": "No path"}), 400
    try:
        buf = conn.download_bytes(path)
        current = buf.read()
        current_hash = hashlib.sha256(current).hexdigest()
        changed = current_hash != original_hash
        return jsonify({"changed": changed, "server_hash": current_hash,
                        "server_size": len(current)})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/api/search", methods=["POST"])
def api_search():
    """Search for text across files in a remote directory (recursive).
    Supports plain text and regex search. Returns matching lines with context."""
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    d = request.json
    remote_dir = d.get("path", "/")
    query = d.get("query", "")
    is_regex = d.get("regex", False)
    case_sensitive = d.get("case_sensitive", False)
    recursive = d.get("recursive", True)
    try:
        max_results = min(int(d.get("max_results", 200)), 500)
    except (ValueError, TypeError):
        return jsonify({"error": "Invalid max_results value"}), 400

    if not query:
        return jsonify({"error": "Empty search query"}), 400

    TEXT_EXTS = {
        ".txt", ".md", ".csv", ".json", ".xml", ".yaml", ".yml", ".ini", ".cfg",
        ".log", ".conf", ".env", ".htaccess", ".gitignore",
        ".py", ".js", ".ts", ".jsx", ".tsx", ".html", ".htm", ".css", ".scss",
        ".less", ".php", ".rb", ".java", ".c", ".cpp", ".h", ".hpp", ".cs",
        ".go", ".rs", ".swift", ".kt", ".scala", ".sh", ".bash", ".zsh",
        ".bat", ".ps1", ".sql", ".r", ".m", ".pl", ".lua", ".vim",
        ".toml", ".properties", ".gradle", ".cmake",
    }
    SKIP_DIRS = {"vendor", "node_modules", ".git", "cache", "bower_components",
                 ".aivelo-revisions", ".aivelo-backup"}

    # Compile pattern
    try:
        flags = 0 if case_sensitive else re.IGNORECASE
        if is_regex:
            pattern = re.compile(query, flags)
        else:
            pattern = re.compile(re.escape(query), flags)
    except re.error as e:
        return jsonify({"error": f"Invalid regex: {e}"}), 400

    matches = []
    files_searched = 0
    dirs_to_scan = [(remote_dir, "")]

    while dirs_to_scan and len(matches) < max_results:
        current_remote, current_rel = dirs_to_scan.pop(0)
        try:
            entries = conn.listdir(current_remote)
        except Exception:
            continue
        for entry in entries:
            if entry["is_dir"]:
                if recursive and entry["name"].lower() not in SKIP_DIRS and not entry["name"].startswith(".aivelo-"):
                    rel = (current_rel + "/" + entry["name"]).lstrip("/") if current_rel else entry["name"]
                    dirs_to_scan.append((current_remote.rstrip("/") + "/" + entry["name"], rel))
                continue
            ext = ("." + entry["name"].rsplit(".", 1)[-1]).lower() if "." in entry["name"] else ""
            if ext not in TEXT_EXTS:
                continue
            if entry.get("size", 0) > 2 * 1024 * 1024:  # skip >2MB
                continue
            full_path = current_remote.rstrip("/") + "/" + entry["name"]
            rel_path = (current_rel + "/" + entry["name"]).lstrip("/") if current_rel else entry["name"]
            try:
                buf = conn.download_bytes(full_path)
                content = buf.read().decode("utf-8", errors="ignore")
                files_searched += 1
                lines = content.split("\n")
                for line_num, line in enumerate(lines, 1):
                    if pattern.search(line):
                        # Get context: 1 line before and after
                        ctx_before = lines[line_num - 2].rstrip() if line_num > 1 else ""
                        ctx_after = lines[line_num].rstrip() if line_num < len(lines) else ""
                        matches.append({
                            "file": rel_path,
                            "full_path": full_path,
                            "line": line_num,
                            "text": line.rstrip()[:200],
                            "context_before": ctx_before[:200],
                            "context_after": ctx_after[:200],
                        })
                        if len(matches) >= max_results:
                            break
            except Exception:
                continue

    return jsonify({
        "matches": matches,
        "files_searched": files_searched,
        "total_matches": len(matches),
        "truncated": len(matches) >= max_results,
        "query": query,
    })


@app.route("/api/related", methods=["POST"])
def api_related():
    """Extract references (includes, imports, hrefs, srcs) from a file and resolve them
    to actual paths on the server. Returns a list of clickable related files."""
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    d = request.json
    path = d.get("path", "")
    content = d.get("content", "")
    if not path:
        return jsonify({"error": "No path"}), 400
    parent = str(PurePosixPath(path).parent)

    # Extract references from content
    refs = set()
    # PHP: include/require/include_once/require_once
    for m in re.finditer(r"""(?:include|require)(?:_once)?\s*[\(\s]+['"]([^'"]+)['"]""", content):
        refs.add(m.group(1))
    # Python: import/from
    for m in re.finditer(r"""from\s+(\S+)\s+import|import\s+(\S+)""", content):
        mod = m.group(1) or m.group(2)
        if mod and "." not in mod:
            refs.add(mod + ".py")
    # HTML: href, src, url()
    for m in re.finditer(r"""(?:href|src|action)=["']([^"'#?]+)""", content, re.I):
        ref = m.group(1)
        if not ref.startswith(("http", "//", "data:", "mailto:", "tel:", "javascript:")):
            refs.add(ref)
    # CSS: url(), @import
    for m in re.finditer(r"""url\(\s*['"]?([^'")]+)['"]?\s*\)""", content, re.I):
        ref = m.group(1)
        if not ref.startswith(("http", "//", "data:")):
            refs.add(ref)
    for m in re.finditer(r"""@import\s+['"]([^'"]+)['"]""", content, re.I):
        refs.add(m.group(1))
    # JS/TS: import from
    for m in re.finditer(r"""(?:from|import)\s+['"]([^'"]+)['"]""", content):
        refs.add(m.group(1))

    # Resolve references to actual server paths
    related = []
    for ref in refs:
        if not ref or ref.startswith("#"):
            continue
        # Try resolving relative to parent directory
        if ref.startswith("/"):
            # Absolute from server root — try as-is
            candidates = [ref]
        else:
            candidates = [parent.rstrip("/") + "/" + ref]
        for candidate in candidates:
            # Normalize ../ etc
            parts = candidate.split("/")
            resolved = []
            for p in parts:
                if p == "..":
                    if resolved: resolved.pop()
                elif p and p != ".":
                    resolved.append(p)
            resolved_path = "/" + "/".join(resolved)
            # Check if file exists on server
            try:
                rparent = str(PurePosixPath(resolved_path).parent)
                rname = PurePosixPath(resolved_path).name
                entries = conn.listdir(rparent)
                if any(e["name"] == rname and not e["is_dir"] for e in entries):
                    related.append({
                        "reference": ref,
                        "path": resolved_path,
                        "name": rname,
                    })
                    break
            except Exception:
                continue

    return jsonify({"related": related, "source": path})


@app.route("/api/lock", methods=["POST"])
def api_lock():
    """Create or check an edit lock for a file. Prevents concurrent editing conflicts."""
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    d = request.json
    path = d.get("path", "")
    action = d.get("action", "check")  # "claim", "release", "check"
    if not path:
        return jsonify({"error": "No path"}), 400

    parent = str(PurePosixPath(path).parent)
    name = PurePosixPath(path).name
    lock_dir = parent.rstrip("/") + "/.aivelo-locks"
    lock_path = lock_dir + "/" + name + ".lock"

    import getpass, platform

    if action == "check" or action == "claim":
        # Check existing lock
        try:
            buf = conn.download_bytes(lock_path)
            lock_data = json.loads(buf.read().decode("utf-8", errors="ignore"))
            lock_age = (datetime.now().timestamp() - lock_data.get("timestamp", 0))
            # Locks older than 2 hours are considered stale
            if lock_age > 7200:
                try: conn.remove(lock_path)
                except Exception: pass
            else:
                if action == "claim":
                    return jsonify({"ok": False, "locked": True,
                                    "locked_by": lock_data.get("user", "unknown"),
                                    "locked_host": lock_data.get("host", "unknown"),
                                    "locked_since": lock_data.get("time", ""),
                                    "lock_age_seconds": int(lock_age)})
                else:
                    return jsonify({"locked": True,
                                    "locked_by": lock_data.get("user", "unknown"),
                                    "locked_host": lock_data.get("host", "unknown"),
                                    "locked_since": lock_data.get("time", ""),
                                    "lock_age_seconds": int(lock_age)})
        except Exception:
            pass  # No lock exists

        if action == "claim":
            try:
                try: conn.mkdir(lock_dir)
                except Exception: pass
                lock_info = {
                    "user": getpass.getuser(),
                    "host": platform.node(),
                    "timestamp": datetime.now().timestamp(),
                    "time": datetime.now().strftime("%H:%M:%S"),
                    "file": name,
                }
                conn.upload_bytes(lock_path, json.dumps(lock_info).encode())
                return jsonify({"ok": True, "locked": False})
            except Exception as e:
                return jsonify({"error": str(e)}), 500
        else:
            return jsonify({"locked": False})

    elif action == "release":
        try:
            conn.remove(lock_path)
        except Exception:
            pass
        return jsonify({"ok": True})

    return jsonify({"error": "Invalid action"}), 400


@app.route("/api/save_as", methods=["POST"])
def api_save_as():
    """Save content to a different path (Save as copy / Save as .new)."""
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    d = request.json
    path = d.get("path", "")
    content = d.get("content", "")
    if not path:
        return jsonify({"error": "No path"}), 400
    try:
        data = content.encode("utf-8")
        conn.upload_bytes(path, data)
        _log_transfer("save_as", path, len(data))
        return jsonify({"ok": True, "path": path, "size": len(data)})
    except Exception as e:
        _log.exception("API error")
        return jsonify({"error": str(e)}), 500


@app.route("/api/dashboard")
def api_dashboard():
    """Scan remote server and return dashboard stats."""
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    start_path = request.args.get("path", "/")
    try:
        max_depth = int(request.args.get("depth", 3))
        if max_depth < 1 or max_depth > 10:
            max_depth = 3
    except (ValueError, TypeError):
        max_depth = 3
    max_files = 5000  # safety limit

    all_files = []
    total_size = 0
    dir_count = 0
    errors = []

    def scan(path, depth):
        nonlocal total_size, dir_count
        if depth > max_depth or len(all_files) >= max_files:
            return
        try:
            items = conn.listdir(path)
            for f in items:
                full = (path.rstrip("/") + "/" + f["name"])
                if f["is_dir"]:
                    dir_count += 1
                    scan(full, depth + 1)
                else:
                    total_size += f["size"]
                    all_files.append({
                        "name": f["name"],
                        "path": full,
                        "size": f["size"],
                        "mtime": f["mtime"],
                    })
        except Exception as e:
            errors.append({"path": path, "error": str(e)})

    try:
        scan(start_path, 0)

        # Sort for largest and recent
        by_size = sorted(all_files, key=lambda f: f["size"], reverse=True)[:15]
        by_recent = sorted(all_files, key=lambda f: f["mtime"] or "", reverse=True)[:15]

        # Extension breakdown
        ext_map = {}
        for f in all_files:
            ext = Path(f["name"]).suffix.lower() or "(no ext)"
            if ext not in ext_map:
                ext_map[ext] = {"count": 0, "size": 0}
            ext_map[ext]["count"] += 1
            ext_map[ext]["size"] += f["size"]
        ext_list = sorted(ext_map.items(), key=lambda x: x[1]["size"], reverse=True)[:20]

        # Disk quota via SITE commands (best effort)
        quota = None
        if isinstance(conn, FTPConn):
            for cmd in ["SITE QUOTA", "SITE DF", "FEAT"]:
                try:
                    resp = conn.ftp.sendcmd(cmd)
                    quota = resp
                    break
                except Exception:
                    pass

        return jsonify({
            "total_files": len(all_files),
            "total_dirs": dir_count,
            "total_size": total_size,
            "largest": by_size,
            "recent": by_recent,
            "extensions": [{"ext": e, "count": d["count"], "size": d["size"]} for e, d in ext_list],
            "quota": quota,
            "errors": errors[:5],
            "scanned_path": start_path,
        })
    except Exception as e:
        _log.exception("API error")
        return jsonify({"error": str(e)}), 500


@app.route("/api/sync/diff", methods=["POST"])
def api_sync_diff():
    """Compare local and remote directories recursively, return diff."""
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    d = request.json
    local_dir = d.get("local_dir", "")
    remote_dir = d.get("remote_dir", "/")
    recursive = d.get("recursive", True)
    if not local_dir or not Path(local_dir).is_dir():
        return jsonify({"error": "Invalid local directory"}), 400

    def _parse_mtime(mtime_str):
        """Parse mtime string to timestamp for reliable comparison.
        FTP LIST output uses two formats:
          - "Mar 13 12:00" (recent files, no year → assume current year)
          - "Mar 13  2024" (older files, no time → year is explicit)
        MLSD uses "20240313120000" which we format to "2024-03-13 12:00".
        """
        if not mtime_str:
            return 0.0
        mtime_str = mtime_str.strip()

        # Try full date formats first (from MLSD or formatted sources)
        for fmt in ("%Y-%m-%d %H:%M", "%Y-%m-%d %H:%M:%S"):
            try:
                return datetime.strptime(mtime_str, fmt).timestamp()
            except ValueError:
                continue

        now = datetime.now()

        # FTP LIST format: "Mar 13 12:00" (no year)
        try:
            parsed = datetime.strptime(mtime_str, "%b %d %H:%M")
            # Replace the default 1900 year with current year
            parsed = parsed.replace(year=now.year)
            # If that puts it in the future (e.g. "Dec 25" parsed in January),
            # it's from last year
            if parsed > now:
                parsed = parsed.replace(year=now.year - 1)
            return parsed.timestamp()
        except ValueError:
            pass

        # FTP LIST format: "Mar 13  2024" (explicit year, no time)
        try:
            return datetime.strptime(mtime_str, "%b %d %Y").timestamp()
        except ValueError:
            pass

        return 0.0

    # Directories to skip during sync scan (not individual dotfiles like .htaccess)
    SYNC_SKIP_DIRS = {".git", ".svn", ".hg", ".aivelo-snapshots", ".aivelo-revisions",
                      ".aivelo-backup", ".aivelo-locks", "node_modules", "__pycache__"}

    def _scan_remote(rdir):
        """Scan remote directory, returns {relative_path: {size, mtime, mtime_ts}}."""
        files = {}
        dirs_to_scan = [(rdir, "")]
        while dirs_to_scan:
            current_remote, current_rel = dirs_to_scan.pop(0)
            try:
                entries = conn.listdir(current_remote)
            except Exception:
                continue
            for entry in entries:
                rel_path = (current_rel + "/" + entry["name"]).lstrip("/") if current_rel else entry["name"]
                if entry["is_dir"]:
                    if recursive and entry["name"] not in SYNC_SKIP_DIRS and not entry["name"].startswith(".aivelo"):
                        dirs_to_scan.append((current_remote.rstrip("/") + "/" + entry["name"], rel_path))
                else:
                    files[rel_path] = {
                        "size": entry["size"],
                        "mtime": entry["mtime"],
                        "mtime_ts": _parse_mtime(entry["mtime"]),
                    }
        return files

    def _scan_local(ldir):
        """Scan local directory, returns {relative_path: {size, mtime, mtime_ts}}.
        Includes dotfiles like .htaccess, .env, .gitignore — only skips
        internal dirs like .git, .aivelo-*, node_modules."""
        files = {}
        base = Path(ldir)
        if recursive:
            iterator = (e for e in base.rglob("*") if e.is_file() and not any(
                p.name in SYNC_SKIP_DIRS or p.name.startswith(".aivelo")
                for p in e.relative_to(base).parents))
        else:
            iterator = (e for e in base.iterdir() if e.is_file())
        for entry in iterator:
            if entry.name.startswith(".aivelo"):
                continue
            rel_path = str(entry.relative_to(base)).replace("\\", "/")
            st = entry.stat()
            files[rel_path] = {
                "size": st.st_size,
                "mtime": datetime.fromtimestamp(st.st_mtime).strftime("%Y-%m-%d %H:%M"),
                "mtime_ts": st.st_mtime,
            }
        return files

    try:
        remote_files = _scan_remote(remote_dir)
        local_files = _scan_local(local_dir)

        # Build diff
        all_names = sorted(set(list(local_files.keys()) + list(remote_files.keys())))
        diff = []
        for name in all_names:
            loc = local_files.get(name)
            rem = remote_files.get(name)
            if loc and not rem:
                diff.append({"name": name, "status": "local_only",
                             "local_size": loc["size"], "local_mtime": loc["mtime"],
                             "action": "upload"})
            elif rem and not loc:
                diff.append({"name": name, "status": "remote_only",
                             "remote_size": rem["size"], "remote_mtime": rem["mtime"],
                             "action": "download"})
            else:
                # Both exist — compare size, then mtime numerically
                size_match = loc["size"] == rem["size"]
                status = "match" if size_match else "different"
                action = "none"
                if not size_match:
                    loc_ts = loc["mtime_ts"]
                    rem_ts = rem["mtime_ts"]
                    if loc_ts and rem_ts:
                        action = "upload" if loc_ts > rem_ts else "download"
                    elif loc_ts:
                        action = "upload"
                    else:
                        action = "download"
                diff.append({
                    "name": name, "status": status,
                    "local_size": loc["size"], "local_mtime": loc["mtime"],
                    "remote_size": rem["size"], "remote_mtime": rem["mtime"],
                    "action": action,
                })

        stats = {
            "total": len(diff),
            "match": sum(1 for d in diff if d["status"] == "match"),
            "local_only": sum(1 for d in diff if d["status"] == "local_only"),
            "remote_only": sum(1 for d in diff if d["status"] == "remote_only"),
            "different": sum(1 for d in diff if d["status"] == "different"),
        }

        return jsonify({"diff": diff, "stats": stats,
                         "local_dir": local_dir, "remote_dir": remote_dir,
                         "recursive": recursive})
    except Exception as e:
        _log.exception("API error")
        return jsonify({"error": str(e)}), 500


@app.route("/api/sync/execute", methods=["POST"])
def api_sync_execute():
    """Execute sync actions: upload or download specific files (supports recursive paths)."""
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    d = request.json
    actions = d.get("actions", [])  # [{name, action: "upload"|"download"}]
    local_dir = d.get("local_dir", "")
    remote_dir = d.get("remote_dir", "/")
    results = []

    def _ensure_remote_dirs(rpath):
        """Create remote parent directories if they don't exist."""
        parts = PurePosixPath(rpath).parent.parts
        current = ""
        for part in parts:
            current = current + "/" + part if current else "/" + part
            try:
                conn.listdir(current)
            except Exception:
                try:
                    conn.mkdir(current)
                except Exception:
                    pass

    for item in actions:
        name = item["name"]
        act = item["action"]
        remote_path = remote_dir.rstrip("/") + "/" + name
        local_path = Path(local_dir) / name
        try:
            if act == "upload":
                # Ensure remote subdirectories exist for recursive sync
                if "/" in name:
                    _ensure_remote_dirs(remote_path)
                with open(local_path, "rb") as f:
                    conn.upload_stream(remote_path, f)
                results.append({"name": name, "action": "upload", "ok": True})
            elif act == "download":
                # Ensure local subdirectories exist
                local_path.parent.mkdir(parents=True, exist_ok=True)
                conn.download_to_file(remote_path, str(local_path))
                results.append({"name": name, "action": "download", "ok": True})
        except Exception as e:
            results.append({"name": name, "action": act, "ok": False, "error": str(e)})

    ok = sum(1 for r in results if r["ok"])
    return jsonify({"results": results, "synced": ok, "failed": len(results) - ok})


@app.route("/api/gallery")
def api_gallery():
    """Get thumbnails for all images in a remote directory."""
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    path = request.args.get("path", "/")
    IMAGE_EXTS = {".jpg", ".jpeg", ".png", ".gif", ".bmp", ".webp", ".svg", ".ico"}
    MAX_GALLERY_IMAGE = 2 * 1024 * 1024  # 2MB per image
    try:
        items = conn.listdir(path)
        images = []
        for f in items:
            ext = PurePosixPath(f["name"]).suffix.lower()
            if ext in IMAGE_EXTS and not f["is_dir"]:
                # Skip files listed as >5MB by server
                if f.get("size", 0) > 5 * 1024 * 1024:
                    continue
                full = path.rstrip("/") + "/" + f["name"]
                try:
                    buf, truncated = conn.download_head(full, MAX_GALLERY_IMAGE)
                    if truncated:
                        continue  # too large for gallery thumbnail
                    data = buf.read()
                    mime = f"image/{ext.lstrip('.').replace('jpg','jpeg')}"
                    if ext == ".svg":
                        mime = "image/svg+xml"
                    b64 = base64.b64encode(data).decode()
                    images.append({
                        "name": f["name"], "path": full, "size": f["size"],
                        "mtime": f["mtime"], "mime": mime, "data": b64,
                    })
                except Exception:
                    _log.debug("Gallery: failed to load %s", full)
        return jsonify({"images": images, "path": path, "count": len(images)})
    except Exception as e:
        _log.exception("API error")
        return jsonify({"error": str(e)}), 500


# ── Encrypted Bookmarks ──
_BOOKMARK_FILE = CONFIG_DIR / "bookmarks.enc"
_BOOKMARK_FILE_V2 = CONFIG_DIR / "bookmarks.v2.enc"
_BOOKMARK_KEY = None

# ── Auto-saved Logins (encrypted with machine key) ──
_LOGINS_FILE = CONFIG_DIR / "logins.enc"
_LOGINS_FILE_V2 = CONFIG_DIR / "logins.v2.enc"


# ═══════════════════════════════════════════════════════════
#  CRYPTO — Fernet (AES-128-CBC + HMAC-SHA256)
# ═══════════════════════════════════════════════════════════

try:
    from cryptography.fernet import Fernet, InvalidToken
    from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
    from cryptography.hazmat.primitives import hashes
    HAS_FERNET = True
except ImportError:
    HAS_FERNET = False

def _derive_fernet_key(password_bytes, salt):
    """Derive a Fernet key from password + salt using PBKDF2."""
    if not HAS_FERNET:
        raise RuntimeError("cryptography library not installed")
    kdf = PBKDF2HMAC(algorithm=hashes.SHA256(), length=32,
                     salt=salt, iterations=200000)
    raw = kdf.derive(password_bytes)
    return base64.urlsafe_b64encode(raw)

def _fernet_encrypt(data_bytes, fernet_key):
    """Encrypt bytes with Fernet. Returns salt + ciphertext."""
    f = Fernet(fernet_key)
    return f.encrypt(data_bytes)

def _fernet_decrypt(token, fernet_key):
    """Decrypt Fernet token. Raises InvalidToken on failure."""
    f = Fernet(fernet_key)
    return f.decrypt(token)

def _machine_key_fernet():
    """Derive a Fernet key from machine-specific info (no password needed).
    Uses a per-install random salt stored alongside the logins file."""
    import platform, getpass
    salt_file = CONFIG_DIR / "logins.salt"
    if salt_file.exists():
        salt = salt_file.read_bytes()
    else:
        salt = os.urandom(16)
        salt_file.write_bytes(salt)
    seed = f"AiveloFTP_{getpass.getuser()}_{platform.node()}_{platform.machine()}"
    return _derive_fernet_key(seed.encode(), salt)


# ── Legacy crypto (v1) for migration only ──

def _machine_key_v1():
    """Old machine key derivation (for migrating logins.enc)."""
    import getpass, platform
    seed = f"AiveloFTP_{getpass.getuser()}_{platform.node()}_{platform.machine()}"
    return hashlib.pbkdf2_hmac("sha256", seed.encode(), b"AiveloAutoLogin_v1", 50000)

def _derive_key_v1(password):
    """Old password key derivation (for migrating bookmarks.enc)."""
    return hashlib.pbkdf2_hmac("sha256", password.encode(), b"AiveloFTPVault_v1", 100000)

def _decrypt_v1(blob, key):
    """Decrypt old XOR/HMAC format (v1). For migration only."""
    import struct, hmac as _hmac
    if len(blob) < 28:
        raise ValueError("Invalid v1 data")
    nonce = blob[:12]
    mac = blob[-16:]
    ct = blob[12:-16]
    expected_mac = _hmac.new(key, nonce + ct, hashlib.sha256).digest()[:16]
    if not _hmac.compare_digest(mac, expected_mac):
        raise ValueError("Wrong password or corrupted v1 data")
    decrypted = bytearray()
    for i in range(0, len(ct), 32):
        block_key = _hmac.new(key, nonce + struct.pack(">I", i // 32), hashlib.sha256).digest()
        chunk = ct[i:i+32]
        decrypted.extend(bytes(a ^ b for a, b in zip(chunk, block_key[:len(chunk)])))
    return bytes(decrypted)


# ── Saved Logins ──

def _load_saved_logins():
    """Load auto-saved logins. Migrates v1 -> v2 automatically."""
    if not HAS_FERNET:
        return _load_saved_logins_v1_only()

    # Try v2 first
    if _LOGINS_FILE_V2.exists():
        try:
            token = _LOGINS_FILE_V2.read_bytes()
            decrypted = _fernet_decrypt(token, _machine_key_fernet())
            return json.loads(decrypted.decode())
        except Exception:
            pass

    # Try v1 and migrate
    if _LOGINS_FILE.exists():
        try:
            blob = _LOGINS_FILE.read_bytes()
            decrypted = _decrypt_v1(blob, _machine_key_v1())
            logins = json.loads(decrypted.decode())
            # Migrate to v2
            _save_logins(logins)
            # Remove old file
            try: _LOGINS_FILE.unlink()
            except Exception: pass
            return logins
        except Exception:
            pass

    return []

def _load_saved_logins_v1_only():
    """Fallback if cryptography lib is not installed."""
    if not _LOGINS_FILE.exists():
        return []
    try:
        blob = _LOGINS_FILE.read_bytes()
        decrypted = _decrypt_v1(blob, _machine_key_v1())
        return json.loads(decrypted.decode())
    except Exception:
        return []

def _save_logins(logins):
    """Save logins encrypted with Fernet. Returns True on success, False on failure."""
    if not HAS_FERNET:
        _log.warning("cryptography library not installed — cannot save logins")
        return False
    try:
        data = json.dumps(logins).encode()
        encrypted = _fernet_encrypt(data, _machine_key_fernet())
        _LOGINS_FILE_V2.write_bytes(encrypted)
        return True
    except Exception as e:
        _log.exception("Failed to save logins")
        return False

@app.route("/api/logins")
def api_logins():
    """Get saved logins with passwords masked. Use /api/logins/credentials to get the actual password."""
    logins = _load_saved_logins()
    masked = []
    for login in logins:
        pw = login.get("password", "")
        masked_pw = "••••" + pw[-2:] if len(pw) > 2 else "••••"
        masked.append({
            "host": login.get("host", ""),
            "port": login.get("port", ""),
            "username": login.get("username", ""),
            "password_masked": masked_pw,
            "protocol": login.get("protocol", "FTP"),
        })
    return jsonify({"logins": masked})

@app.route("/api/logins/credentials", methods=["POST"])
def api_logins_credentials():
    """Get the real password for a specific saved login (by index).
    Only called when the user selects a saved connection in the UI."""
    d = request.json or {}
    try:
        idx = int(d.get("index", -1))
    except (ValueError, TypeError):
        return jsonify({"error": "Invalid index"}), 400
    logins = _load_saved_logins()
    if 0 <= idx < len(logins):
        return jsonify({"password": logins[idx].get("password", "")})
    return jsonify({"error": "Invalid index"}), 400

@app.route("/api/logins/save", methods=["POST"])
def api_logins_save():
    """Auto-save a login after successful connection."""
    d = request.json
    host = d.get("host", "")
    port = d.get("port", "")
    username = d.get("username", "")
    password = d.get("password", "")
    protocol = d.get("protocol", "FTP")
    if not host or not username:
        return jsonify({"error": "Host and username required"}), 400
    logins = _load_saved_logins()
    # Update existing or add new (match on host+port+user+proto)
    found = False
    for login in logins:
        if (login["host"] == host and login["username"] == username
                and login["protocol"] == protocol and str(login.get("port","")) == str(port)):
            login["password"] = password
            found = True
            break
    if not found:
        logins.append({"host": host, "port": port, "username": username,
                        "password": password, "protocol": protocol})
    if _save_logins(logins):
        return jsonify({"ok": True, "count": len(logins)})
    else:
        return jsonify({"error": "Failed to save — is the cryptography library installed?"}), 500

@app.route("/api/logins/delete", methods=["POST"])
def api_logins_delete():
    """Delete a saved login."""
    d = request.json or {}
    try:
        idx = int(d.get("index", -1))
    except (ValueError, TypeError):
        return jsonify({"error": "Invalid index"}), 400
    logins = _load_saved_logins()
    if 0 <= idx < len(logins):
        logins.pop(idx)
        _save_logins(logins)
        return jsonify({"ok": True})
    return jsonify({"error": "Invalid index"}), 400


# ── Encrypted Bookmark Vault ──

@app.route("/api/bookmarks/unlock", methods=["POST"])
def api_bookmarks_unlock():
    """Unlock encrypted bookmarks with master password."""
    global _BOOKMARK_KEY
    d = request.json
    password = d.get("password", "")
    if not password:
        return jsonify({"error": "Password required"}), 400

    if not HAS_FERNET:
        return jsonify({"error": "cryptography library not installed"}), 500

    # Generate or load salt for this vault
    salt_file = CONFIG_DIR / "bookmarks.salt"
    if salt_file.exists():
        salt = salt_file.read_bytes()
    else:
        salt = os.urandom(16)

    fernet_key = _derive_fernet_key(password.encode(), salt)

    # Try v2 first
    if _BOOKMARK_FILE_V2.exists():
        try:
            token = _BOOKMARK_FILE_V2.read_bytes()
            decrypted = _fernet_decrypt(token, fernet_key)
            bms = json.loads(decrypted.decode())
            _BOOKMARK_KEY = fernet_key
            if not salt_file.exists():
                salt_file.write_bytes(salt)
            return jsonify({"ok": True, "bookmarks": bms, "existed": True})
        except Exception:
            _BOOKMARK_KEY = None
            return jsonify({"error": "Wrong password"}), 403

    # Try v1 and migrate
    if _BOOKMARK_FILE.exists():
        try:
            blob = _BOOKMARK_FILE.read_bytes()
            old_key = _derive_key_v1(password)
            decrypted = _decrypt_v1(blob, old_key)
            bms = json.loads(decrypted.decode())
            # Migrate to v2
            _BOOKMARK_KEY = fernet_key
            if not salt_file.exists():
                salt_file.write_bytes(salt)
            encrypted = _fernet_encrypt(json.dumps(bms).encode(), fernet_key)
            _BOOKMARK_FILE_V2.write_bytes(encrypted)
            # Remove old file
            try: _BOOKMARK_FILE.unlink()
            except Exception: pass
            return jsonify({"ok": True, "bookmarks": bms, "existed": True})
        except ValueError:
            _BOOKMARK_KEY = None
            return jsonify({"error": "Wrong password"}), 403

    # New vault
    _BOOKMARK_KEY = fernet_key
    if not salt_file.exists():
        salt_file.write_bytes(salt)
    return jsonify({"ok": True, "bookmarks": [], "existed": False})


@app.route("/api/bookmarks/save", methods=["POST"])
def api_bookmarks_save():
    """Save bookmarks encrypted."""
    global _BOOKMARK_KEY
    if not _BOOKMARK_KEY:
        return jsonify({"error": "Vault not unlocked"}), 401
    d = request.json
    bookmarks = d.get("bookmarks", [])
    try:
        data = json.dumps(bookmarks).encode()
        encrypted = _fernet_encrypt(data, _BOOKMARK_KEY)
        _BOOKMARK_FILE_V2.write_bytes(encrypted)
        return jsonify({"ok": True, "count": len(bookmarks)})
    except Exception as e:
        _log.exception("API error")
        return jsonify({"error": str(e)}), 500


@app.route("/api/bookmarks/status")
def api_bookmarks_status():
    """Check if encrypted vault exists and is unlocked."""
    return jsonify({
        "exists": _BOOKMARK_FILE_V2.exists() or _BOOKMARK_FILE.exists(),
        "unlocked": _BOOKMARK_KEY is not None,
    })


# ── Language ──
@app.route("/api/lang")
def api_lang():
    lang = cfg.get("lang", "")
    return jsonify({"lang": lang, "languages": LANGUAGES, "needs_select": lang == ""})

@app.route("/api/lang/set", methods=["POST"])
def api_lang_set():
    global cfg
    lang = request.json.get("lang", "en")
    if lang not in T:
        lang = "en"
    cfg["lang"] = lang
    save_config(cfg)
    return jsonify({"ok": True, "lang": lang})

@app.route("/api/translations")
def api_translations():
    lang = cfg.get("lang", "en")
    if lang not in T:
        lang = "en"
    return jsonify({"lang": lang, "t": T[lang], "rtl": lang == "ar"})


# ── Launch Counter & Pro License ──
@app.route("/api/launch_info")
def api_launch_info():
    count, key = increment_launch()
    is_pro = validate_pro_key(key) if key else False
    return jsonify({
        "launch_count": count,
        "is_pro": is_pro,
        "nag": count > 30 and not is_pro,
    })

@app.route("/api/activate", methods=["POST"])
def api_activate():
    global cfg
    d = request.json
    key = d.get("key", "").strip()
    if validate_pro_key(key):
        cfg["pro_key"] = key
        save_config(cfg)
        return jsonify({"ok": True, "message": "Aivelo FTP Vault Pro activated!"})
    return jsonify({"error": "Invalid license key"}), 400

@app.route("/api/pro_status")
def api_pro_status():
    key = cfg.get("pro_key", "")
    return jsonify({"is_pro": validate_pro_key(key) if key else False})

@app.route("/api/pro_key")
def api_pro_key():
    key = cfg.get("pro_key", "")
    if key and validate_pro_key(key):
        return jsonify({"key": key})
    return jsonify({"key": ""})



# ═══════════════════════════════════════════════════════════



# ═══════════════════════════════════════════════════════════
#  PRO: AI SERVER ASSISTANT
# ═══════════════════════════════════════════════════════════

# Backup state
_backup_state = {"running": False, "cancel": False, "phase": "", "current": "", "done": 0, "total": 0, "error": None, "result": None}

def _backup_worker(remote_dir, conn_info):
    """Background backup worker with its own dedicated connection.
    conn_info = dict with host, port, username, password, protocol."""
    global _backup_state
    _backup_state.update({"running": True, "cancel": False, "phase": "connecting", "current": "", "done": 0, "total": 0, "error": None, "result": None})

    # Open a dedicated connection for this backup
    backup_conn = None
    try:
        proto = conn_info["protocol"]
        if proto == "SFTP":
            backup_conn = SFTPConn()
            # Get stored fingerprint so we don't trigger TOFU dialog
            fp = _get_trusted_fingerprint(conn_info["host"], conn_info["port"], "SFTP")
            backup_conn.connect(conn_info["host"], conn_info["port"],
                                conn_info["username"], password=conn_info["password"],
                                trust_fingerprint=fp)
        else:
            backup_conn = FTPConn()
            fp = _get_trusted_fingerprint(conn_info["host"], conn_info["port"], "FTPS") if proto == "FTPS" else None
            backup_conn.connect(conn_info["host"], conn_info["port"],
                                conn_info["username"], conn_info["password"],
                                use_tls=(proto == "FTPS"), trust_fingerprint=fp)
    except Exception as e:
        _backup_state.update({"running": False, "error": f"Backup connection failed: {e}"})
        return

    try:
        # Phase 1: Scan all files
        _backup_state["phase"] = "scanning"
        all_files = []
        dirs_to_scan = [remote_dir]
        errors = []
        while dirs_to_scan:
            if _backup_state["cancel"]:
                _backup_state.update({"running": False, "phase": "cancelled"})
                return
            current = dirs_to_scan.pop(0)
            _backup_state["current"] = current
            try:
                entries = backup_conn.listdir(current)
            except Exception as e:
                errors.append({"path": current, "error": str(e)})
                continue
            for entry in entries:
                full = current.rstrip("/") + "/" + entry["name"]
                if entry["is_dir"]:
                    dirs_to_scan.append(full)
                else:
                    all_files.append(full)
        if not all_files:
            _backup_state.update({"running": False, "error": "No files found"})
            return
        _backup_state.update({"phase": "zipping", "total": len(all_files), "done": 0})

        # Phase 2: Download + zip to temporary file on disk (not RAM)
        import zipfile, datetime as _dt
        timestamp = _dt.datetime.now().strftime("%Y%m%d_%H%M%S")
        zip_name = f"backup_{timestamp}.zip"
        zip_tmp = tempfile.NamedTemporaryFile(delete=False, suffix=".zip",
                                               dir=str(CONFIG_DIR))
        zip_tmp_path = zip_tmp.name
        backed_up = 0
        try:
            with zipfile.ZipFile(zip_tmp, "w", zipfile.ZIP_DEFLATED) as zf:
                for fpath in all_files:
                    if _backup_state["cancel"]:
                        _backup_state.update({"running": False, "phase": "cancelled"})
                        return
                    _backup_state["current"] = fpath.split("/")[-1]
                    try:
                        # Stream each file through a temp file to avoid holding all in RAM
                        ftmp = tempfile.NamedTemporaryFile(delete=False, dir=str(CONFIG_DIR))
                        ftmp_path = ftmp.name
                        try:
                            backup_conn.download_to_file(fpath, ftmp_path)
                            ftmp.close()
                            rel = fpath
                            if rel.startswith(remote_dir):
                                rel = rel[len(remote_dir):].lstrip("/")
                            zf.write(ftmp_path, rel)
                            backed_up += 1
                        finally:
                            try: os.unlink(ftmp_path)
                            except OSError: pass
                    except Exception as e:
                        errors.append({"path": fpath, "error": str(e)})
                    _backup_state["done"] = backed_up + len(errors)

            # Phase 3: Upload zip from disk file
            zip_size = os.path.getsize(zip_tmp_path)
            zip_path = remote_dir.rstrip("/") + "/" + zip_name
            _backup_state.update({"phase": "uploading", "current": zip_name,
                "upload_size": zip_size, "upload_done": 0})
            try:
                chunk_size = 65536
                uploaded = [0]
                def _upload_callback(chunk):
                    uploaded[0] += len(chunk)
                    _backup_state["upload_done"] = uploaded[0]
                if hasattr(backup_conn, 'ftp'):
                    with open(zip_tmp_path, "rb") as zf_read:
                        backup_conn.ftp.storbinary(f"STOR {zip_path}", zf_read,
                                                    blocksize=chunk_size, callback=_upload_callback)
                elif hasattr(backup_conn, 'sftp'):
                    with open(zip_tmp_path, "rb") as zf_read:
                        with backup_conn.sftp.open(zip_path, "wb") as rf:
                            while True:
                                if _backup_state["cancel"]:
                                    _backup_state.update({"running": False, "phase": "cancelled"})
                                    try: backup_conn.sftp.remove(zip_path)
                                    except Exception: pass
                                    return
                                chunk = zf_read.read(chunk_size)
                                if not chunk:
                                    break
                                rf.write(chunk)
                                uploaded[0] += len(chunk)
                                _backup_state["upload_done"] = uploaded[0]
                else:
                    with open(zip_tmp_path, "rb") as zf_read:
                        backup_conn.upload_stream(zip_path, zf_read)
            except Exception as e:
                _backup_state.update({"running": False, "error": f"Upload failed: {e}"})
                return

            _log_transfer("backup", zip_path, zip_size, detail=f"{backed_up} files")
            _backup_state.update({"running": False, "phase": "done", "result": {
                "zip_name": zip_name, "zip_path": zip_path, "zip_size": zip_size,
                "files_backed_up": backed_up, "total_files": len(all_files), "errors": errors
            }})
        finally:
            # Always clean up the temp zip file
            try: os.unlink(zip_tmp_path)
            except OSError: pass
    except Exception as e:
        _backup_state.update({"running": False, "error": str(e)})
    finally:
        # Always close the dedicated backup connection
        try:
            if backup_conn:
                backup_conn.disconnect()
        except Exception:
            pass


@app.route("/api/pro/backup", methods=["POST"])
def api_backup():
    """Start a background backup with its own connection."""
    key = cfg.get("pro_key", "")
    if not validate_pro_key(key):
        return jsonify({"error": "Pro license required"}), 403
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    if _backup_state["running"]:
        return jsonify({"error": "Backup already running"}), 400
    d = request.json
    remote_dir = d.get("path", "/")
    # Capture connection credentials so the backup thread can open its own connection
    conn_info = {
        "host": conn.host,
        "port": conn.port,
        "username": conn.username,
        "password": d.get("password", ""),  # client must re-send password
        "protocol": conn.proto,
    }
    # If no password provided, try to get it from saved logins
    if not conn_info["password"]:
        for login in _load_saved_logins():
            if (login.get("host") == conn.host
                    and str(login.get("port", "")) == str(conn.port)
                    and login.get("username") == conn.username
                    and login.get("protocol") == conn.proto):
                conn_info["password"] = login.get("password", "")
                break
    if not conn_info["password"]:
        return jsonify({"error": "Password required for backup (re-send in request body)"}), 400
    t = threading.Thread(target=_backup_worker, args=(remote_dir, conn_info), daemon=True)
    t.start()
    return jsonify({"ok": True, "started": True})


@app.route("/api/pro/backup/status")
def api_backup_status():
    return jsonify(_backup_state)


@app.route("/api/pro/backup/cancel", methods=["POST"])
def api_backup_cancel():
    _backup_state["cancel"] = True
    return jsonify({"ok": True})



@app.route("/api/pro/seo_audit", methods=["POST"])
def api_seo_audit():
    key = cfg.get("pro_key", "")
    if not validate_pro_key(key):
        return jsonify({"error": "Pro license required"}), 403
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    d = request.json
    remote_dir = d.get("path", "/")
    issues = []
    try:
        files = conn.listdir(remote_dir)
    except Exception:
        return jsonify({"error": "Cannot list directory"}), 500
    html_files = [f for f in files if not f["is_dir"] and f["name"].lower().endswith((".html", ".htm", ".php"))][:30]
    for f in html_files:
        file_issues = []
        try:
            buf, _ = conn.download_head(remote_dir.rstrip("/") + "/" + f["name"], 32000)
            content = buf.read().decode("utf-8", errors="ignore")
        except Exception:
            continue
        title_m = re.search(r"<title[^>]*>(.*?)</title>", content, re.I | re.DOTALL)
        if not title_m or not title_m.group(1).strip():
            file_issues.append({"type": "error", "msg": "Missing or empty <title> tag"})
        elif len(title_m.group(1).strip()) < 10:
            file_issues.append({"type": "warn", "msg": "Title too short: " + title_m.group(1).strip()})
        elif len(title_m.group(1).strip()) > 60:
            file_issues.append({"type": "warn", "msg": "Title too long (" + str(len(title_m.group(1).strip())) + " chars)"})
        if not re.search(r'<meta[^>]*name=.description', content, re.I):
            file_issues.append({"type": "error", "msg": "Missing meta description"})
        if not re.search(r"<meta[^>]*viewport", content, re.I):
            file_issues.append({"type": "warn", "msg": "Missing viewport meta (mobile unfriendly)"})
        imgs = re.findall(r"<img[^>]*>", content, re.I)
        no_alt = [img for img in imgs if not re.search(r'alt=', img, re.I)]
        if no_alt:
            file_issues.append({"type": "error", "msg": str(len(no_alt)) + " image(s) missing alt attribute"})
        h1s = re.findall(r"<h1[^>]*>", content, re.I)
        if not h1s:
            file_issues.append({"type": "warn", "msg": "No <h1> heading found"})
        elif len(h1s) > 1:
            file_issues.append({"type": "warn", "msg": "Multiple <h1> tags (" + str(len(h1s)) + ")"})
        if not re.search(r'<link[^>]*rel=.canonical', content, re.I):
            file_issues.append({"type": "info", "msg": "No canonical URL set"})
        if not re.search(r"<html[^>]*lang=", content, re.I):
            file_issues.append({"type": "warn", "msg": "Missing lang attribute on <html>"})
        if file_issues:
            issues.append({"file": f["name"], "issues": file_issues})
    score = max(0, 100 - sum(len(f["issues"]) * 5 for f in issues))
    return jsonify({"score": score, "files": issues, "total_scanned": len(html_files)})


@app.route("/api/pro/find_unused", methods=["POST"])
def api_find_unused():
    key = cfg.get("pro_key", "")
    if not validate_pro_key(key):
        return jsonify({"error": "Pro license required"}), 403
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    d = request.json
    remote_dir = d.get("path", "/")
    try:
        files = conn.listdir(remote_dir)
    except Exception:
        return jsonify({"error": "Cannot list directory"}), 500
    all_names = {f["name"] for f in files}
    html_files = [f for f in files if not f["is_dir"] and f["name"].lower().endswith((".html", ".htm", ".php"))][:30]
    css_files = {f["name"] for f in files if f["name"].lower().endswith(".css")}
    js_files = {f["name"] for f in files if f["name"].lower().endswith(".js")}
    referenced_files = set()
    all_html_content = ""
    for f in html_files:
        try:
            buf, _ = conn.download_head(remote_dir.rstrip("/") + "/" + f["name"], 32000)
            content = buf.read().decode("utf-8", errors="ignore")
            all_html_content += content
        except Exception:
            continue
        for m in re.finditer(r'(?:href|src)=["\'](.*?)["\'\?#]', content, re.I):
            ref = m.group(1).split("/")[-1]
            referenced_files.add(ref)
    unused_css = css_files - referenced_files
    unused_js = js_files - referenced_files
    broken = []
    for m in re.finditer(r'(?:href|src)=["\'](.*?)["\'\?#]', all_html_content, re.I):
        ref = m.group(1)
        if ref.startswith(("http", "//", "mailto:", "tel:", "javascript:", "#", "data:")):
            continue
        local_name = ref.split("/")[-1]
        if local_name and local_name not in all_names:
            broken.append(ref)
    broken = list(set(broken))[:20]
    return jsonify({"unused_css": sorted(unused_css), "unused_js": sorted(unused_js), "broken_refs": broken, "total_css": len(css_files), "total_js": len(js_files)})


@app.route("/api/pro/optimize/scan", methods=["POST"])
def api_optimize_scan():
    """Scan files for optimization potential. Returns preview without applying changes."""
    key = cfg.get("pro_key", "")
    if not validate_pro_key(key):
        return jsonify({"error": "Pro license required"}), 403
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    d = request.json
    remote_dir = d.get("path", "/")
    mode = d.get("mode", "safe")  # "safe" or "aggressive"
    try:
        files = conn.listdir(remote_dir)
    except Exception:
        return jsonify({"error": "Cannot list directory"}), 500

    OPTIMIZE_EXTS = {".html", ".htm", ".css", ".js", ".php"}
    SKIP_DIRS = {"vendor", "node_modules", "cache", ".git", "bower_components"}
    candidates = []
    for f in files:
        if f["is_dir"] and f["name"].lower() in SKIP_DIRS:
            continue
        if f["is_dir"]:
            continue
        ext = ("." + f["name"].rsplit(".", 1)[-1]).lower() if "." in f["name"] else ""
        if ext not in OPTIMIZE_EXTS:
            continue
        candidates.append({"name": f["name"], "size": f["size"], "ext": ext})

    results = []
    total_potential = 0

    for cand in candidates[:30]:
        name = cand["name"]
        ext = cand["ext"]
        rpath = remote_dir.rstrip("/") + "/" + name

        # Detect already minified
        if ".min." in name.lower():
            results.append({"file": name, "status": "skipped", "reason": "Already minified (.min. in name)",
                            "risk": "none", "orig": cand["size"], "new": cand["size"], "saved": 0, "pct": 0})
            continue

        try:
            buf = conn.download_bytes(rpath)
            original = buf.read().decode("utf-8", errors="ignore")
            orig_size = len(original.encode("utf-8"))

            # Detect already minified by content analysis
            lines = original.split("\n")
            avg_line_len = sum(len(l) for l in lines) / max(len(lines), 1)
            whitespace_ratio = original.count(" ") / max(len(original), 1)
            if avg_line_len > 500 and whitespace_ratio < 0.05:
                results.append({"file": name, "status": "skipped", "reason": "Already optimized (detected by content analysis)",
                                "risk": "none", "orig": orig_size, "new": orig_size, "saved": 0, "pct": 0})
                continue

            # Determine risk level
            risk = "low"
            if ext in (".html", ".htm", ".php"):
                # Check for risky patterns
                has_inline_js = bool(re.search(r"<script[^>]*>(?![\s]*</script>)", original, re.I))
                has_templates = bool(re.search(r"<%|{{|{%|\$\{|<\?(?!xml)", original))
                has_pre_code = bool(re.search(r"<(pre|code|textarea)", original, re.I))
                if has_templates:
                    risk = "high"
                elif has_inline_js or has_pre_code:
                    risk = "medium"
            elif ext == ".js":
                risk = "medium" if mode == "safe" else "low"
                has_regex = bool(re.search(r"/[^/\n]+/[gimsuy]", original))
                has_template_str = "`" in original
                if has_regex or has_template_str:
                    risk = "high"

            # Calculate minified version (without applying)
            minified = _optimize_content(original, ext, mode)
            new_size = len(minified.encode("utf-8"))
            saved = orig_size - new_size
            pct = round((saved / orig_size * 100) if orig_size > 0 else 0, 1)

            status = "ready"
            if saved <= 50:
                status = "skipped"
                reason = "Savings too small (<50 bytes)"
            elif risk == "high" and mode == "safe":
                status = "risky"
                reason = "Contains templates, regex, or complex patterns — use aggressive mode or skip"
            else:
                reason = ""
                total_potential += saved

            results.append({
                "file": name, "status": status, "reason": reason,
                "risk": risk, "orig": orig_size, "new": new_size,
                "saved": saved, "pct": pct,
            })
        except Exception as e:
            results.append({"file": name, "status": "error", "reason": str(e),
                            "risk": "unknown", "orig": 0, "new": 0, "saved": 0, "pct": 0})

    scan_summary = {
        "total_scanned": len(results),
        "ready": sum(1 for r in results if r["status"] == "ready"),
        "skipped": sum(1 for r in results if r["status"] == "skipped"),
        "risky": sum(1 for r in results if r["status"] == "risky"),
        "errors": sum(1 for r in results if r["status"] == "error"),
        "total_potential_savings": total_potential,
    }
    return jsonify({"results": results, "summary": scan_summary, "mode": mode,
                     "path": remote_dir})


def _optimize_content(original, ext, mode="safe"):
    """Apply optimization to content. Returns minified string."""
    if ext in (".html", ".htm", ".php"):
        minified = original
        # Remove HTML comments (preserve IE conditionals)
        minified = re.sub(r"<!--(?!\[if)(?!-->).*?-->", "", minified, flags=re.DOTALL)
        # Collapse whitespace between tags (but NOT inside pre/code/textarea/script)
        # Safe approach: only collapse whitespace that's purely between > and <
        minified = re.sub(r">\s+<", "> <", minified)  # keep single space for inline elements
        if mode == "aggressive":
            minified = re.sub(r"> <", "><", minified)
        # Normalize runs of whitespace (but not inside pre/code/script blocks)
        minified = re.sub(r"[ \t]+", " ", minified)
        # Remove blank lines
        minified = "\n".join(line for line in minified.split("\n") if line.strip())
        return minified.strip()

    elif ext == ".css":
        minified = original
        # Remove CSS comments
        minified = re.sub(r"/\*.*?\*/", "", minified, flags=re.DOTALL)
        # Normalize whitespace
        minified = re.sub(r"\s+", " ", minified)
        # Remove whitespace around structural characters
        minified = re.sub(r"\s*([{}:;,>~+])\s*", r"\1", minified)
        # Remove trailing semicolons before closing braces
        minified = re.sub(r";}", "}", minified)
        if mode == "aggressive":
            # Shorten zero values: 0px -> 0, 0em -> 0
            minified = re.sub(r"\b0(px|em|rem|%|pt|ex|ch|vw|vh)\b", "0", minified)
            # Shorten hex colors: #aabbcc -> #abc
            def _shorten_hex(m):
                h = m.group(1)
                if len(h) == 6 and h[0]==h[1] and h[2]==h[3] and h[4]==h[5]:
                    return f"#{h[0]}{h[2]}{h[4]}"
                return m.group(0)
            minified = re.sub(r"#([0-9a-fA-F]{6})\b", _shorten_hex, minified)
        return minified.strip()

    elif ext == ".js":
        minified = original
        # JS: conservative only — remove block comments (NOT regex-safe for all cases)
        # Only remove obvious /* ... */ comments that start at line beginning or after whitespace
        minified = re.sub(r"(?m)^\s*/\*.*?\*/\s*$", "", minified, flags=re.DOTALL)
        # Remove single-line // comments that take a full line
        minified = re.sub(r"(?m)^\s*//.*$", "", minified)
        # Remove empty lines
        lines = [line.rstrip() for line in minified.split("\n") if line.strip()]
        minified = "\n".join(lines)
        if mode == "aggressive":
            # Strip trailing whitespace more aggressively
            minified = re.sub(r"[ \t]+\n", "\n", minified)
        return minified

    return original


@app.route("/api/pro/optimize/apply", methods=["POST"])
def api_optimize_apply():
    """Apply optimizations. Creates backups first, then applies."""
    key = cfg.get("pro_key", "")
    if not validate_pro_key(key):
        return jsonify({"error": "Pro license required"}), 403
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    d = request.json
    remote_dir = d.get("path", "/")
    file_list = d.get("files", [])  # list of filenames to optimize
    mode = d.get("mode", "safe")

    if not file_list:
        return jsonify({"error": "No files selected"}), 400

    # Phase 1: Create backup directory
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    backup_dir = remote_dir.rstrip("/") + "/.aivelo-backup-" + timestamp
    try:
        conn.mkdir(backup_dir)
    except Exception:
        pass  # May already exist

    results = []
    total_saved = 0
    backed_up = []

    for name in file_list[:30]:
        rpath = remote_dir.rstrip("/") + "/" + name
        ext = ("." + name.rsplit(".", 1)[-1]).lower() if "." in name else ""
        try:
            # Download original
            buf = conn.download_bytes(rpath)
            original = buf.read().decode("utf-8", errors="ignore")
            orig_size = len(original.encode("utf-8"))

            # Backup original
            backup_path = backup_dir + "/" + name
            conn.upload_bytes(backup_path, original.encode("utf-8"))
            backed_up.append(name)

            # Optimize
            minified = _optimize_content(original, ext, mode)
            new_size = len(minified.encode("utf-8"))
            saved = orig_size - new_size

            if saved > 50:
                conn.upload_bytes(rpath, minified.encode("utf-8"))
                results.append({"file": name, "applied": True, "orig": orig_size,
                                "new": new_size, "saved": saved,
                                "pct": round((saved/orig_size*100) if orig_size else 0, 1)})
                total_saved += saved
            else:
                results.append({"file": name, "applied": False, "orig": orig_size,
                                "new": new_size, "saved": saved, "pct": 0,
                                "reason": "Savings too small"})
        except Exception as e:
            results.append({"file": name, "applied": False, "error": str(e)})

    _log_transfer("optimize", remote_dir, total_saved,
                  detail=f"{sum(1 for r in results if r.get('applied'))} files, backup: {backup_dir}")

    return jsonify({
        "results": results,
        "total_saved": total_saved,
        "backup_dir": backup_dir,
        "backed_up": len(backed_up),
        "mode": mode,
    })


@app.route("/api/pro/optimize/rollback", methods=["POST"])
def api_optimize_rollback():
    """Rollback optimizations by restoring from backup directory."""
    key = cfg.get("pro_key", "")
    if not validate_pro_key(key):
        return jsonify({"error": "Pro license required"}), 403
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    d = request.json
    remote_dir = d.get("path", "/")
    backup_dir = d.get("backup_dir", "")
    if not backup_dir:
        return jsonify({"error": "No backup directory specified"}), 400

    restored = 0
    errors = []
    try:
        backup_files = conn.listdir(backup_dir)
        for f in backup_files:
            if f["is_dir"]:
                continue
            backup_path = backup_dir + "/" + f["name"]
            restore_path = remote_dir.rstrip("/") + "/" + f["name"]
            try:
                buf = conn.download_bytes(backup_path)
                conn.upload_bytes(restore_path, buf.read())
                restored += 1
            except Exception as e:
                errors.append({"file": f["name"], "error": str(e)})
        # Remove backup dir after successful restore
        if not errors:
            for f in backup_files:
                try:
                    conn.remove(backup_dir + "/" + f["name"])
                except Exception:
                    pass
            try:
                conn.rmdir(backup_dir)
            except Exception:
                pass
    except Exception as e:
        return jsonify({"error": f"Cannot read backup directory: {e}"}), 500

    _log_transfer("rollback", backup_dir, detail=f"restored {restored} files")
    return jsonify({"ok": True, "restored": restored, "errors": errors})


@app.route("/api/upload_guard", methods=["POST"])
def api_upload_guard():
    """Smart Upload Guard - compares file content to detect wrong overwrites."""
    if not conn or not conn.ensure_connected():
        return jsonify({"safe": True, "files_at_risk": []})

    d = request.json
    local_files = d.get("files", [])  # [{name, full_path, size, is_dir}]
    remote_dir = d.get("remote_dir", "/")

    TEXT_EXT = {".html", ".htm", ".php", ".txt", ".css", ".js", ".xml", ".json", ".md", ".svg"}
    warnings = []

    def extract_meta(content):
        """Extract title, meta description, and first text chunk from HTML-like content."""
        title = ""
        desc = ""
        m = re.search(r"<title[^>]*>(.*?)</title>", content, re.IGNORECASE | re.DOTALL)
        if m:
            title = re.sub(r"\s+", " ", m.group(1)).strip()[:200]
        m = re.search(r"""<meta[^>]*name=["']description["'][^>]*content=["']([^"']*)["']""", content, re.IGNORECASE)
        if m:
            desc = m.group(1).strip()[:200]
        # Strip all HTML tags to get text body
        body = re.sub(r"<[^>]+>", " ", content)
        body = re.sub(r"\s+", " ", body).strip()[:500]
        return title, desc, body

    def similarity(a, b):
        """Simple word overlap ratio."""
        if not a or not b:
            return 1.0  # no data to compare, assume safe
        wa = set(a.lower().split())
        wb = set(b.lower().split())
        if not wa or not wb:
            return 1.0
        overlap = len(wa & wb)
        return overlap / max(len(wa), len(wb))

    try:
        remote_files = conn.listdir(remote_dir)
        remote_names = {f["name"]: f for f in remote_files}
    except Exception:
        return jsonify({"safe": True, "files_at_risk": []})

    for lf in local_files[:20]:
        name = lf.get("name", "")
        ext = ("." + name.rsplit(".", 1)[-1]).lower() if "." in name else ""
        if lf.get("is_dir") or ext not in TEXT_EXT:
            continue
        if name not in remote_names:
            continue  # new file, no overwrite risk

        # Read local file
        local_path = lf.get("full_path", "")
        if not local_path:
            continue
        try:
            with open(local_path, "r", encoding="utf-8", errors="ignore") as f:
                local_content = f.read(16000)
        except Exception:
            continue

        # Read remote file
        try:
            rpath = remote_dir.rstrip("/") + "/" + name
            buf = conn.download_bytes(rpath)
            remote_content = buf.read(16000).decode("utf-8", errors="ignore")
        except Exception:
            continue

        # Compare
        local_title, local_desc, local_body = extract_meta(local_content)
        remote_title, remote_desc, remote_body = extract_meta(remote_content)

        risk = False
        reason = ""

        # Title mismatch is strongest signal
        if local_title and remote_title and local_title.lower() != remote_title.lower():
            sim = similarity(local_title, remote_title)
            if sim < 0.6:
                risk = True
                reason = f"Different page: \"{local_title}\" would overwrite \"{remote_title}\""

        # Body content very different
        if not risk and local_body and remote_body:
            sim = similarity(local_body, remote_body)
            if sim < 0.4:
                risk = True
                reason = f"Content is very different from existing file on server"

        if risk:
            warnings.append({"name": name, "reason": reason})

    if warnings:
        return jsonify({
            "safe": False,
            "risk_level": "high" if len(warnings) > 1 else "medium",
            "warning": warnings[0]["reason"],
            "files_at_risk": [w["name"] for w in warnings],
            "details": warnings,
        })
    return jsonify({"safe": True, "files_at_risk": []})



# ── Transfer History ──
_HISTORY_FILE = CONFIG_DIR / "history.json"
_transfer_history = []

def _load_history():
    global _transfer_history
    try:
        if _HISTORY_FILE.exists():
            _transfer_history = json.loads(_HISTORY_FILE.read_text())[-500:]
    except Exception:
        _transfer_history = []

def _save_history():
    try:
        _HISTORY_FILE.write_text(json.dumps(_transfer_history[-500:]))
    except Exception:
        pass

# ── Transfer progress tracking ──
_xfer_progress = {"active": False, "current_file": "", "file_index": 0, "file_total": 0, "bytes_sent": 0, "bytes_total": 0}

def _xfer_start(total_files):
    _xfer_progress["active"] = True
    _xfer_progress["file_index"] = 0
    _xfer_progress["file_total"] = total_files
    _xfer_progress["current_file"] = ""
    _xfer_progress["bytes_sent"] = 0
    _xfer_progress["bytes_total"] = 0

def _xfer_file(name, size, index):
    _xfer_progress["current_file"] = name
    _xfer_progress["file_index"] = index
    _xfer_progress["bytes_sent"] = 0
    _xfer_progress["bytes_total"] = size

def _xfer_chunk(n):
    _xfer_progress["bytes_sent"] = min(_xfer_progress["bytes_sent"] + n, _xfer_progress["bytes_total"])

def _xfer_done():
    _xfer_progress["active"] = False

@app.route("/api/xfer_progress")
def api_xfer_progress():
    return jsonify(_xfer_progress)

def _log_transfer(action, path, size=0, ok=True, detail=""):
    _transfer_history.append({
        "time": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        "action": action,
        "path": path,
        "size": size,
        "ok": ok,
        "detail": detail,
    })
    _save_history()

_load_history()


@app.route("/api/history")
def api_history():
    q = request.args.get("q", "").lower()
    items = _transfer_history
    if q:
        items = [h for h in items if q in h["path"].lower() or q in h["action"].lower() or q in h.get("detail","").lower()]
    return jsonify({"history": list(reversed(items[-200:])), "total": len(items)})


@app.route("/api/history/clear", methods=["POST"])
def api_history_clear():
    global _transfer_history
    _transfer_history = []
    _save_history()
    return jsonify({"ok": True})


# ── Remote ZIP/Unzip ──
@app.route("/api/zip", methods=["POST"])
def api_zip():
    """Zip files on the remote server using server-side commands."""
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    d = request.json
    files = d.get("files", [])
    zip_name = d.get("zip_name", "archive.zip")
    directory = d.get("directory", "/")

    if not files:
        return jsonify({"error": "No files selected"}), 400

    try:
        if isinstance(conn, SFTPConn):
            # SFTP: execute zip command via separate SSH channel
            transport = conn.sftp.get_channel().get_transport()
            chan = transport.open_session()
            file_args = " ".join(shlex.quote(f) for f in files)
            cmd = f'cd {shlex.quote(directory)} && zip -j {shlex.quote(zip_name)} {file_args}'
            chan.exec_command(cmd)
            exit_code = chan.recv_exit_status()
            stdout = chan.recv(4096).decode(errors="replace")
            stderr = chan.recv_stderr(4096).decode(errors="replace")
            chan.close()
            if exit_code != 0:
                return jsonify({"error": f"zip failed: {stderr or stdout}"}), 500
            _log_transfer("zip", f"{directory}/{zip_name}", detail=f"{len(files)} files")
            return jsonify({"ok": True, "zip": zip_name, "output": stdout})
        else:
            # FTP: try SITE EXEC or just return not supported
            return jsonify({"error": "ZIP on FTP requires SFTP connection (server-side commands need SSH)"}), 400
    except Exception as e:
        _log.exception("API error")
        return jsonify({"error": str(e)}), 500


@app.route("/api/unzip", methods=["POST"])
def api_unzip():
    """Unzip a file on the remote server."""
    if not conn or not conn.ensure_connected():
        return jsonify({"error": "Not connected"}), 401
    d = request.json
    zip_path = d.get("path", "")
    dest = d.get("dest", "")

    if not zip_path:
        return jsonify({"error": "No zip file specified"}), 400
    if not dest:
        dest = str(PurePosixPath(zip_path).parent)

    try:
        if isinstance(conn, SFTPConn):
            transport = conn.sftp.get_channel().get_transport()
            chan = transport.open_session()
            cmd = f'unzip -o {shlex.quote(zip_path)} -d {shlex.quote(dest)}'
            chan.exec_command(cmd)
            exit_code = chan.recv_exit_status()
            stdout = chan.recv(8192).decode(errors="replace")
            stderr = chan.recv_stderr(4096).decode(errors="replace")
            chan.close()
            if exit_code != 0:
                return jsonify({"error": f"unzip failed: {stderr or stdout}"}), 500
            _log_transfer("unzip", zip_path, detail=f"to {dest}")
            return jsonify({"ok": True, "output": stdout})
        else:
            return jsonify({"error": "Unzip on FTP requires SFTP connection (server-side commands need SSH)"}), 400
    except Exception as e:
        _log.exception("API error")
        return jsonify({"error": str(e)}), 500


# ═══════════════════════════════════════════════════════════
#  HTML — Full Manus-quality UI
# ═══════════════════════════════════════════════════════════


HTML_PAGE = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Aivelo FTP Vault</title>
<link href="https://fonts.googleapis.com/css2?family=Playfair+Display:wght@700;800;900&family=Inter:wght@300;400;500;600;700;800&family=JetBrains+Mono:wght@400;500;600&display=swap" rel="stylesheet">
<style>
:root {
  --brand-50: #faf7f5; --brand-100: #f0ebe6; --brand-200: #e0d5cc;
  --brand-300: #cbb8a9; --brand-400: #b39685; --brand-500: #8b6f5e;
  --brand-600: #6b5548; --brand-700: #5a4840; --brand-800: #4a3d37; --brand-900: #3d332f;
  --gray-50: #fafafa; --gray-100: #f4f4f5; --gray-200: #e4e4e7;
  --gray-300: #d4d4d8; --gray-400: #a1a1aa; --gray-500: #71717a;
  --gray-600: #52525b; --gray-700: #3f3f46; --gray-800: #27272a; --gray-900: #18181b;
  --success: #22c55e; --danger: #ef4444; --info: #3b82f6;
  --radius: 10px; --radius-lg: 16px;
  --shadow: 0 1px 3px rgba(0,0,0,.1); --shadow-lg: 0 10px 15px -3px rgba(0,0,0,.1);
  --font-sans: 'Inter', -apple-system, sans-serif; --font-mono: 'JetBrains Mono', monospace;
}
*,*::before,*::after{margin:0;padding:0;box-sizing:border-box}
html{font-size:16px;-webkit-font-smoothing:antialiased}
body{font-family:var(--font-sans);background:var(--gray-50);color:var(--gray-900);min-height:100vh;overflow:hidden}
button{font-family:inherit;cursor:pointer}
::-webkit-scrollbar{width:10px;height:10px}::-webkit-scrollbar-thumb{background:var(--gray-300);border-radius:5px}::-webkit-scrollbar-thumb:hover{background:var(--gray-400)}

/* Auth */
.auth-screen{display:flex;min-height:100vh;background:linear-gradient(135deg,var(--brand-50),var(--gray-50) 50%,var(--brand-100))}
.auth-left{flex:1;display:flex;align-items:center;justify-content:center;padding:48px}
.auth-right{flex:1;display:none;align-items:center;justify-content:center;background:linear-gradient(135deg,var(--brand-700),var(--brand-900));position:relative;overflow:hidden}
.auth-right::before{display:none}
.auth-right-content{position:relative;z-index:1;text-align:center;color:#fff;padding:48px}
.auth-right-content h2{font-size:28px;font-weight:700;margin-bottom:12px}
.auth-right-content p{font-size:15px;opacity:.8;max-width:340px;line-height:1.6}
.auth-features{display:flex;flex-direction:column;gap:12px;margin-top:24px;text-align:left;font-size:13px}
.auth-feature{display:flex;align-items:center;gap:10px;opacity:.85}
.auth-feature span:first-child{width:28px;height:28px;border-radius:6px;background:rgba(255,255,255,.12);display:flex;align-items:center;justify-content:center;font-size:14px;flex-shrink:0}
@media(min-width:950px){.auth-right{display:flex}}
.auth-card{width:100%;max-width:400px}
.auth-logo{display:flex;align-items:center;gap:14px;margin-bottom:36px}
.auth-logo img{width:52px;height:52px;object-fit:contain}
.auth-logo-text .brand{font-size:20px;font-weight:800;color:var(--brand-800);letter-spacing:-.5px}
.auth-logo-text .sub{font-size:11px;font-weight:600;color:var(--brand-500);text-transform:uppercase;letter-spacing:1.5px}
.auth-card h1{font-size:24px;font-weight:700;margin-bottom:6px}
.auth-card .subtitle{font-size:14px;color:var(--gray-500);margin-bottom:28px}
.form-group{margin-bottom:16px}
.form-group label{display:block;font-size:12px;font-weight:600;color:var(--gray-700);margin-bottom:5px;text-transform:uppercase;letter-spacing:.3px}
.form-input{width:100%;padding:10px 13px;font-size:14px;border:1.5px solid var(--gray-200);border-radius:var(--radius);background:#fff;color:var(--gray-900);transition:all .2s;outline:none;font-family:var(--font-sans)}
.form-input:focus{border-color:var(--brand-500);box-shadow:0 0 0 3px rgba(139,111,94,.1)}
.form-row{display:flex;gap:10px}.form-row .form-group{flex:1}.form-row .form-group.small{flex:0 0 80px}
.proto-group{display:flex;gap:6px;margin-bottom:18px}
.proto-btn{flex:1;padding:9px;border:1.5px solid var(--gray-200);border-radius:var(--radius);background:#fff;font-size:13px;font-weight:600;color:var(--gray-600);transition:all .2s}
.proto-btn.active{border-color:var(--brand-500);background:var(--brand-100);color:var(--brand-800)}
.proto-btn:hover{border-color:var(--brand-400)}
.auth-error{margin-top:14px;padding:9px 12px;background:#fef2f2;border:1px solid #fecaca;border-radius:6px;color:var(--danger);font-size:13px;display:none}
.auth-error.visible{display:block}
.bookmarks-row{margin-top:14px;font-size:12px;color:var(--gray-500)}
.bookmarks-row a{color:var(--brand-600);cursor:pointer;text-decoration:underline;margin-left:6px}

/* Buttons */
.btn{display:inline-flex;align-items:center;justify-content:center;gap:6px;font-size:13px;font-weight:600;padding:8px 16px;border:none;border-radius:var(--radius);transition:all .15s;white-space:nowrap}
.btn-primary{background:var(--brand-700);color:#fff}.btn-primary:hover{background:var(--brand-800)}
.btn-secondary{background:#fff;color:var(--gray-700);border:1.5px solid var(--gray-200)}.btn-secondary:hover{background:var(--gray-50)}
.btn-sm{font-size:12px;padding:5px 11px}.btn-full{width:100%}
.btn-lg{font-size:15px;padding:11px 22px}
.btn-danger{background:transparent;color:var(--danger);border:1.5px solid #fecaca}.btn-danger:hover{background:#fef2f2}

/* App */
.app-layout{display:flex;flex-direction:column;height:100vh}
.topbar{height:52px;background:var(--brand-800);display:flex;align-items:center;padding:0 16px;gap:12px;flex-shrink:0}
.topbar-logo{display:flex;align-items:center;gap:8px}
.topbar-logo img{width:36px;height:36px;object-fit:contain}
.topbar-logo .brand{font-size:14px;font-weight:800;color:#fff}
.conn-badge{padding:4px 14px;background:rgba(255,255,255,.12);border-radius:20px;font-size:11px;font-weight:600;color:rgba(255,255,255,.9);font-family:var(--font-mono);display:flex;align-items:center;gap:6px}
.conn-badge::before{content:'';width:7px;height:7px;border-radius:50%;background:#22c55e;flex-shrink:0}

.topbar-right{margin-left:auto;display:flex;gap:6px;align-items:center}
.tb-btn-dark{padding:5px 12px;background:rgba(255,255,255,.08);border:1px solid rgba(255,255,255,.12);border-radius:8px;color:rgba(255,255,255,.85);font-size:12px;font-weight:600;cursor:pointer;transition:all .15s;display:flex;align-items:center;gap:5px}
.tb-btn-dark:hover{background:rgba(255,255,255,.15);border-color:rgba(255,255,255,.25)}
.tb-btn-dark.disconnect{color:#f87171;border-color:rgba(248,113,113,.25)}
.tb-btn-dark.disconnect:hover{background:rgba(248,113,113,.12)}
.sec-strip{background:var(--brand-50);border-bottom:1px solid var(--brand-200);padding:4px 16px;display:flex;gap:20px;font-size:11px;color:var(--brand-600);font-weight:500;flex-shrink:0}
.sec-strip span{display:flex;align-items:center;gap:5px}
.sec-strip span::before{content:'';width:6px;height:6px;border-radius:50%;background:var(--brand-500);flex-shrink:0}

/* Menu Bar */
.menubar{background:#2c2c2c;display:flex;padding:0;margin:0;flex-shrink:0;font-size:12.5px;font-family:var(--font-sans);user-select:none;position:relative;z-index:200}
.menubar-item{position:relative;padding:4px 12px;color:rgba(255,255,255,.85);cursor:default;white-space:nowrap}
.menubar-item:hover,.menubar-item.open{background:rgba(255,255,255,.12)}
.menu-dropdown{display:none;position:absolute;top:100%;left:0;background:#2c2c2c;border:1px solid rgba(255,255,255,.1);border-radius:0 0 4px 4px;min-width:200px;padding:4px 0;box-shadow:0 6px 20px rgba(0,0,0,.4);z-index:201}
.menubar-item.open .menu-dropdown{display:block}
.menu-dropdown .menu-item{padding:5px 24px 5px 12px;color:rgba(255,255,255,.85);cursor:default;display:flex;align-items:center;gap:8px;white-space:nowrap}
.menu-dropdown .menu-item:hover{background:rgba(255,255,255,.1)}
.menu-dropdown .menu-item.disabled{opacity:.35;pointer-events:none}
.menu-dropdown .menu-item .shortcut{margin-left:auto;font-size:11px;opacity:.5;padding-left:24px}
.menu-dropdown .menu-sep{height:1px;background:rgba(255,255,255,.1);margin:4px 0}
.menu-dropdown .menu-item .pro-tag{font-size:9px;background:rgba(212,175,55,.25);color:#d4af37;padding:1px 5px;border-radius:3px;font-weight:700;letter-spacing:.5px}
.menu-dropdown .menu-item .lang-check{width:14px;text-align:center;flex-shrink:0}

/* Dual Pane */
.dual-pane{flex:1;display:flex;gap:0;overflow:hidden;min-height:0}
.pane{flex:1;display:flex;flex-direction:column;min-width:0;overflow:hidden}
.pane-header{padding:6px 12px;background:#fff;border-bottom:1px solid var(--gray-200);display:flex;align-items:center;gap:6px;flex-shrink:0}
.pane-header h3{font-size:13px;font-weight:700;color:var(--brand-800);display:flex;align-items:center;gap:6px}
.pane-path{flex:1;font-family:var(--font-mono);font-size:12px;color:var(--brand-600);background:var(--brand-50);padding:4px 10px;border-radius:6px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.pane-toolbar{padding:4px 12px;background:#fff;border-bottom:1px solid var(--gray-100);display:flex;gap:4px;flex-shrink:0;flex-wrap:wrap}
.pane-body{flex:1;overflow-y:auto;background:#fff}

/* Center column */
.transfer-col{width:48px;display:flex;flex-direction:column;align-items:center;justify-content:center;gap:6px;background:var(--gray-50);border-left:1px solid var(--gray-200);border-right:1px solid var(--gray-200);flex-shrink:0}
.transfer-col button{width:36px;height:36px;border:none;border-radius:8px;background:var(--brand-700);color:#fff;font-size:16px;display:flex;align-items:center;justify-content:center;transition:all .15s}
.transfer-col button:hover{background:var(--brand-800);transform:scale(1.05)}

/* File rows */
.file-row{display:flex;align-items:center;padding:6px 12px;border-bottom:1px solid var(--gray-100);cursor:default;transition:background .1s;font-size:13px}
.file-row:hover{background:var(--gray-50)}
.file-row.selected{background:var(--brand-50)}
.file-icon{width:28px;text-align:center;font-size:15px;flex-shrink:0}
.file-name{flex:1;font-family:var(--font-mono);font-size:12px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;min-width:0}
.file-size{width:70px;text-align:right;font-family:var(--font-mono);font-size:11px;color:var(--gray-500);flex-shrink:0}
.file-time{width:110px;text-align:right;font-family:var(--font-mono);font-size:11px;color:var(--gray-400);flex-shrink:0;padding-left:8px}
.file-perms{width:75px;text-align:center;font-family:var(--font-mono);font-size:11px;color:var(--gray-400);flex-shrink:0;cursor:pointer}
.file-perms:hover{color:var(--brand-700);text-decoration:underline}
.file-actions-cell{width:60px;display:flex;gap:1px;flex-shrink:0;justify-content:flex-end}
.fa-btn{width:28px;height:28px;border:none;border-radius:6px;background:transparent;color:var(--gray-400);font-size:18px;font-weight:700;display:flex;align-items:center;justify-content:center;transition:all .15s}
.fa-btn:hover{background:var(--brand-100);color:var(--brand-700)}
.empty{text-align:center;padding:32px;color:var(--gray-400);font-size:13px}

/* Dropzone */
.dropzone{border:2px dashed var(--gray-300);border-radius:var(--radius);padding:16px;text-align:center;cursor:pointer;margin:8px 12px;transition:all .2s;font-size:13px;color:var(--gray-500)}
.dropzone:hover,.dropzone.dragover{border-color:var(--brand-400);background:var(--brand-50);color:var(--brand-700)}

/* Transfer panel */
.xfer-bar{height:32px;background:var(--brand-50);border-top:1px solid var(--brand-200);display:flex;align-items:center;padding:0 16px;font-size:12px;color:var(--brand-700);gap:12px;flex-shrink:0}
.xfer-bar .xfer-prog{flex:1;height:4px;background:var(--gray-200);border-radius:2px;overflow:hidden}
.xfer-bar .xfer-fill{height:100%;background:var(--brand-500);transition:width .2s;width:0%}

/* Status bar */
.status-bar{height:26px;background:var(--gray-50);border-top:1px solid var(--gray-200);display:flex;align-items:center;padding:0 16px;font-size:11px;color:var(--gray-500);flex-shrink:0;gap:20px}

/* Modal */
.modal-overlay{position:fixed;inset:0;background:rgba(0,0,0,.35);backdrop-filter:blur(3px);z-index:1000;display:flex;align-items:center;justify-content:center}
.modal{background:#fff;border-radius:var(--radius-lg);padding:28px;width:380px;box-shadow:var(--shadow-lg);animation:modalIn .2s}
@keyframes modalIn{from{transform:scale(.95) translateY(8px);opacity:0}}
.modal h3{font-size:17px;font-weight:700;margin-bottom:6px}
.modal .desc{font-size:13px;color:var(--gray-500);margin-bottom:18px}
.modal .chmod-grid{display:grid;grid-template-columns:auto 1fr 1fr 1fr;gap:8px 16px;margin-bottom:18px;font-size:13px}
.modal .chmod-grid label{display:flex;align-items:center;gap:4px;cursor:pointer}
.modal .chmod-preview{font-family:var(--font-mono);font-size:18px;text-align:center;padding:10px;background:var(--gray-50);border-radius:var(--radius);margin-bottom:18px;font-weight:600;color:var(--brand-700)}
.modal-actions{display:flex;gap:8px;justify-content:flex-end}

/* Context Menu */
.ctx-menu{position:fixed;z-index:2000;background:#fff;border:1px solid var(--gray-200);border-radius:var(--radius);box-shadow:var(--shadow-lg);min-width:180px;padding:4px 0;animation:ctxIn .12s}
@keyframes ctxIn{from{opacity:0;transform:scale(.95)}}
.ctx-menu .ctx-item{display:flex;align-items:center;gap:10px;padding:8px 16px;font-size:13px;cursor:pointer;color:var(--gray-700);transition:background .1s}
.ctx-menu .ctx-item:hover{background:var(--brand-50);color:var(--brand-800)}
.ctx-menu .ctx-item.danger{color:var(--danger)}.ctx-menu .ctx-item.danger:hover{background:#fef2f2}
.ctx-menu .ctx-sep{height:1px;background:var(--gray-100);margin:4px 0}
.ctx-menu .ctx-item .ctx-icon{width:20px;text-align:center;font-size:14px;flex-shrink:0}

/* Toast */
.toast-wrap{position:fixed;bottom:16px;right:16px;z-index:9999;display:flex;flex-direction:column;gap:6px}
.toast{background:#fff;border:1px solid var(--gray-200);border-radius:var(--radius);padding:10px 16px;font-size:13px;box-shadow:var(--shadow-lg);animation:slideIn .25s;display:flex;align-items:center;gap:6px}
.toast.ok{border-left:3px solid var(--success)}.toast.err{border-left:3px solid var(--danger)}
@keyframes slideIn{from{transform:translateX(100%);opacity:0}}

/* Preview Panel */
.preview-overlay{position:fixed;inset:0;background:rgba(0,0,0,.4);backdrop-filter:blur(2px);z-index:500;display:flex;justify-content:flex-end}
.preview-panel{width:55%;max-width:720px;min-width:400px;background:#fff;height:100%;display:flex;flex-direction:column;box-shadow:-4px 0 20px rgba(0,0,0,.15);animation:slidePanel .2s}
@keyframes slidePanel{from{transform:translateX(100%)}}
.preview-header{padding:12px 16px;border-bottom:1px solid var(--gray-200);display:flex;align-items:center;gap:10px;flex-shrink:0;background:var(--gray-50)}
.preview-header .preview-icon{font-size:20px}
.preview-header .preview-title{flex:1;font-family:var(--font-mono);font-size:13px;font-weight:600;color:var(--brand-800);overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.preview-header .preview-meta{font-size:11px;color:var(--gray-500);font-family:var(--font-mono)}
.preview-toolbar{padding:6px 16px;border-bottom:1px solid var(--gray-100);display:flex;gap:6px;align-items:center;flex-shrink:0;background:#fff}
.preview-toolbar .lang-badge{padding:2px 8px;background:var(--brand-100);border-radius:4px;font-size:11px;font-weight:600;color:var(--brand-700);font-family:var(--font-mono)}
.preview-toolbar .edit-indicator{font-size:11px;color:var(--gray-500);margin-left:auto}
.preview-toolbar .edit-indicator.modified{color:var(--danger);font-weight:600}
.preview-body{flex:1;overflow:auto;position:relative;min-height:0}
.preview-body img{max-width:100%;height:auto;display:block;margin:20px auto;border-radius:6px;box-shadow:0 2px 8px rgba(0,0,0,.1)}
.preview-body iframe{width:100%;height:100%;border:none}
.preview-body .binary-info{display:flex;flex-direction:column;align-items:center;justify-content:center;height:100%;color:var(--gray-400);font-size:15px;gap:12px}
.preview-body .binary-info .binary-icon{font-size:48px}

/* Code Editor */
.code-editor{width:100%;height:100%;padding:0;margin:0;border:none;outline:none;font-family:var(--font-mono);font-size:13px;line-height:1.6;color:var(--gray-900);background:#fafafa;resize:none;tab-size:4;-moz-tab-size:4}
.code-wrap{display:flex;height:100%;overflow:auto}
.line-numbers{padding:12px 8px 12px 12px;background:var(--gray-50);border-right:1px solid var(--gray-200);font-family:var(--font-mono);font-size:13px;line-height:1.6;color:var(--gray-400);text-align:right;user-select:none;overflow:hidden;min-width:40px;flex-shrink:0;white-space:pre}
.code-area{flex:1;overflow:auto}
.code-area textarea{width:100%;min-height:100%;padding:12px;border:none;outline:none;font-family:var(--font-mono);font-size:13px;line-height:1.6;color:var(--gray-900);background:transparent;resize:none;tab-size:4;-moz-tab-size:4}
/* Syntax highlighted view (read-only) */
.code-highlighted{padding:12px;font-family:var(--font-mono);font-size:13px;line-height:1.6;white-space:pre-wrap;word-wrap:break-word;color:var(--gray-900)}
.code-highlighted .kw{color:#8b5cf6;font-weight:600}
.code-highlighted .str{color:#059669}
.code-highlighted .num{color:#d97706}
.code-highlighted .cmt{color:#9ca3af;font-style:italic}
.code-highlighted .fn{color:#2563eb}
.code-highlighted .tag{color:#dc2626}
.code-highlighted .attr{color:#d97706}
.code-highlighted .val{color:#059669}
.code-highlighted .op{color:#6b7280}

/* Pro Version Styling */

.pro-tool-btn{padding:5px 12px;border:1px solid rgba(212,175,55,.3);border-radius:8px;background:rgba(212,175,55,.1);color:#d4af37;font-size:11px;font-weight:600;cursor:pointer;transition:all .2s;display:flex;align-items:center;gap:5px;letter-spacing:.3px}
.pro-tool-btn:hover{background:rgba(212,175,55,.2);border-color:rgba(212,175,55,.5)}
.pro-tool-btn .pro-tool-icon{font-size:12px}

.decor-logo{position:fixed;bottom:30px;right:10px;width:80px;height:80px;opacity:.15;pointer-events:none;z-index:0;background-size:contain;background-repeat:no-repeat;background-position:center}

/* Guard Dwarf */
.guard-dwarf-wrap{position:fixed;bottom:26px;left:50%;transform:translateX(calc(-50% - 4px));z-index:50;pointer-events:none;transition:opacity .3s}
.guard-dwarf-wrap.off{opacity:0;pointer-events:none}
.guard-dwarf-img{width:64px;height:auto;image-rendering:pixelated;filter:drop-shadow(0 2px 4px rgba(0,0,0,.3));transition:transform .2s}
.guard-dwarf-wrap.idle .guard-dwarf-img{animation:dwarfBob 2s ease-in-out infinite;display:block}
.guard-dwarf-wrap.alert .guard-dwarf-img{animation:dwarfAlert .3s ease-in-out 4;display:block}
.guard-dwarf-wrap.working .guard-dwarf-img{display:none}
.guard-dwarf-hammer{width:64px;height:72px;image-rendering:pixelated;filter:drop-shadow(0 2px 4px rgba(0,0,0,.3));display:none;background-size:384px 72px;background-repeat:no-repeat}
.guard-dwarf-wrap.working .guard-dwarf-hammer{display:block;animation:dwarfHammerSprite .6s steps(5) infinite}
.guard-dwarf-wrap.alert::after{content:'⚠️';position:absolute;top:-12px;right:-8px;font-size:20px;animation:guardWarn .3s ease-in-out 4}
.guard-speech{position:absolute;bottom:100%;left:50%;transform:translateX(-50%);background:#fff;border:2px solid var(--brand-700);border-radius:10px 10px 10px 2px;padding:6px 10px;font-size:11px;font-weight:600;color:var(--brand-800);white-space:nowrap;opacity:0;transition:opacity .3s;pointer-events:none;box-shadow:var(--shadow-lg)}
.guard-dwarf-wrap.alert .guard-speech{opacity:1}
@keyframes dwarfBob{0%,100%{transform:translateY(0)}50%{transform:translateY(-3px)}}
@keyframes dwarfAlert{0%{transform:rotate(0) scale(1)}25%{transform:rotate(-12deg) scale(1.05)}50%{transform:rotate(8deg) scale(1.1)}75%{transform:rotate(-5deg) scale(1.05)}100%{transform:rotate(0) scale(1)}}
@keyframes dwarfHammerSprite{from{background-position:0 0}to{background-position:-320px 0}}
@keyframes guardWarn{0%{transform:scale(1);opacity:1}50%{transform:scale(1.4);opacity:1}100%{transform:scale(1);opacity:0}}

.guard-toggle{position:fixed;bottom:6px;left:50%;transform:translateX(-50%);z-index:51;display:flex;align-items:center;gap:4px;font-size:10px;color:var(--gray-400);cursor:pointer;background:rgba(255,255,255,.8);padding:1px 6px;border-radius:8px;border:1px solid var(--gray-200)}
.guard-toggle input{width:12px;height:12px;cursor:pointer}

.hidden{display:none!important}

/* Styled Dialog (replaces prompt/confirm) */
.dialog-overlay{position:fixed;inset:0;background:rgba(0,0,0,.4);backdrop-filter:blur(2px);z-index:9000;display:flex;align-items:center;justify-content:center}
.dialog{background:#fff;border-radius:var(--radius-lg);padding:24px;width:380px;box-shadow:var(--shadow-lg);animation:modalIn .2s}
.dialog h3{font-size:16px;font-weight:700;color:var(--brand-800);margin-bottom:8px}
.dialog p{font-size:13px;color:var(--gray-600);margin-bottom:16px;line-height:1.5;white-space:pre-line}
.dialog input{width:100%;padding:10px 13px;font-size:14px;border:1.5px solid var(--gray-200);border-radius:var(--radius);background:#fff;outline:none;font-family:var(--font-mono);margin-bottom:16px}
.dialog input:focus{border-color:var(--brand-500);box-shadow:0 0 0 3px rgba(139,111,94,.1)}
.dialog-btns{display:flex;gap:8px;justify-content:flex-end}

/* Gallery */
.gallery-overlay{position:fixed;inset:0;background:rgba(0,0,0,.4);backdrop-filter:blur(2px);z-index:600;display:flex;align-items:center;justify-content:center}
.gallery-panel{width:90%;max-width:900px;max-height:85vh;background:#fff;border-radius:var(--radius-lg);box-shadow:var(--shadow-lg);display:flex;flex-direction:column;animation:modalIn .2s;overflow:hidden}
.gallery-header{padding:14px 20px;border-bottom:1px solid var(--gray-200);display:flex;align-items:center;gap:12px;flex-shrink:0}
.gallery-header h2{font-size:18px;font-weight:700;color:var(--brand-800);flex:1}
.gallery-body{flex:1;overflow-y:auto;padding:16px}
.gallery-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(140px,1fr));gap:12px}
.gallery-item{border:1px solid var(--gray-200);border-radius:var(--radius);overflow:hidden;cursor:pointer;transition:all .15s;background:#fff}
.gallery-item:hover{border-color:var(--brand-400);box-shadow:var(--shadow);transform:translateY(-2px)}
.gallery-item img{width:100%;height:110px;object-fit:cover;display:block;background:var(--gray-100)}
.gallery-item .gallery-info{padding:6px 8px}
.gallery-item .gallery-name{font-family:var(--font-mono);font-size:11px;color:var(--gray-700);overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.gallery-item .gallery-size{font-size:10px;color:var(--gray-400)}
.gallery-lightbox{position:fixed;inset:0;background:rgba(0,0,0,.85);z-index:700;display:flex;align-items:center;justify-content:center;cursor:pointer}
.gallery-lightbox img{max-width:90%;max-height:90%;object-fit:contain;border-radius:8px;box-shadow:0 4px 30px rgba(0,0,0,.4)}
.gallery-lightbox .lb-info{position:fixed;bottom:20px;left:50%;transform:translateX(-50%);color:#fff;font-size:13px;font-family:var(--font-mono);background:rgba(0,0,0,.5);padding:6px 16px;border-radius:8px}
.gallery-loading{text-align:center;padding:40px;color:var(--gray-400);font-size:14px}

/* Vault */
.vault-badge{display:flex;align-items:center;gap:4px;padding:2px 8px;border-radius:12px;font-size:11px;font-weight:600;cursor:pointer}
.vault-badge.locked{background:#fef2f2;color:var(--danger)}
.vault-badge.unlocked{background:#f0fdf4;color:#16a34a}
.vault-unlocked-dark{color:#4ade80!important;border-color:rgba(74,222,128,.3)!important}

/* History Log */
.history-overlay{position:fixed;inset:0;background:rgba(0,0,0,.4);backdrop-filter:blur(2px);z-index:600;display:flex;align-items:center;justify-content:center}
.history-panel{width:90%;max-width:800px;max-height:85vh;background:#fff;border-radius:var(--radius-lg);box-shadow:var(--shadow-lg);display:flex;flex-direction:column;animation:modalIn .2s;overflow:hidden}
.history-header{padding:14px 20px;border-bottom:1px solid var(--gray-200);display:flex;align-items:center;gap:10px;flex-shrink:0}
.history-header h2{flex:1;font-size:18px;font-weight:700;color:var(--brand-800)}
.history-search{padding:8px 13px;font-size:13px;border:1.5px solid var(--gray-200);border-radius:var(--radius);width:220px;outline:none;font-family:var(--font-sans)}
.history-search:focus{border-color:var(--brand-500)}
.history-body{flex:1;overflow-y:auto}
.history-row{display:flex;align-items:center;padding:8px 20px;border-bottom:1px solid var(--gray-100);font-size:12px;gap:10px}
.history-row:hover{background:var(--gray-50)}
.history-row .h-icon{width:24px;text-align:center;font-size:15px;flex-shrink:0}
.history-row .h-action{width:70px;font-weight:600;text-transform:uppercase;font-size:10px;letter-spacing:.5px;flex-shrink:0}
.history-row .h-action.upload{color:#2563eb}.history-row .h-action.download{color:#16a34a}
.history-row .h-action.zip{color:#d97706}.history-row .h-action.unzip{color:#7c3aed}
.history-row .h-action.delete{color:var(--danger)}.history-row .h-action.rename{color:var(--gray-600)}
.history-row .h-path{flex:1;font-family:var(--font-mono);font-size:11px;color:var(--gray-700);overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.history-row .h-size{width:65px;text-align:right;font-family:var(--font-mono);font-size:11px;color:var(--gray-400);flex-shrink:0}
.history-row .h-time{width:130px;text-align:right;font-family:var(--font-mono);font-size:11px;color:var(--gray-400);flex-shrink:0}
.history-row .h-status{width:18px;text-align:center;flex-shrink:0}

/* Zip Modal */
.zip-overlay{position:fixed;inset:0;background:rgba(0,0,0,.4);backdrop-filter:blur(2px);z-index:600;display:flex;align-items:center;justify-content:center}
.zip-panel{width:420px;background:#fff;border-radius:var(--radius-lg);box-shadow:var(--shadow-lg);padding:24px;animation:modalIn .2s}

/* Pro Nag & Modal */
.pro-nag{position:fixed;inset:0;background:rgba(0,0,0,.5);backdrop-filter:blur(3px);z-index:8000;display:flex;align-items:center;justify-content:center}
.pro-nag-card{background:#fff;border-radius:16px;padding:32px;width:440px;text-align:center;box-shadow:0 20px 60px rgba(0,0,0,.2);animation:modalIn .3s}
.pro-nag-card .pro-badge{display:inline-block;background:linear-gradient(135deg,#d97706,#b45309);color:#fff;font-size:11px;font-weight:700;padding:4px 12px;border-radius:20px;letter-spacing:.5px;margin-bottom:16px}
.pro-nag-card h2{font-size:22px;font-weight:800;color:var(--brand-800);margin-bottom:8px}
.pro-nag-card .pro-subtitle{font-size:14px;color:var(--gray-600);margin-bottom:20px;line-height:1.5}
.pro-nag-card .pro-price{font-size:36px;font-weight:800;color:var(--brand-800);margin-bottom:4px}
.pro-nag-card .pro-price-sub{font-size:13px;color:var(--gray-500);margin-bottom:20px}
.pro-nag-card .pro-features{text-align:left;margin:0 auto 20px;max-width:320px;font-size:13px;color:var(--gray-700);line-height:2}
.pro-btn-ai{background:linear-gradient(135deg,#d97706,#92400e);color:#fff;border:none;padding:12px 28px;border-radius:var(--radius);font-size:14px;font-weight:700;cursor:pointer;transition:all .15s;display:inline-block}
.pro-btn-ai:hover{transform:translateY(-1px);box-shadow:0 4px 12px rgba(217,119,6,.3)}
.pro-later{background:none;border:none;color:var(--gray-400);font-size:12px;cursor:pointer;margin-top:12px;padding:8px}
.pro-later:hover{color:var(--gray-600)}
.topbar-pro{background:linear-gradient(135deg,#d4af37,#b8960c);color:#fff;border:none;padding:5px 14px;border-radius:8px;font-size:11px;font-weight:700;cursor:pointer;transition:all .15s;display:flex;align-items:center;gap:4px;letter-spacing:.5px}
.topbar-pro:hover{background:linear-gradient(135deg,#e5c04b,#c9a61d);box-shadow:0 2px 8px rgba(212,175,55,.3)}
.auth-pro-link{display:inline-flex;align-items:center;gap:4px;color:#d97706;font-size:12px;font-weight:600;cursor:pointer;margin-top:12px;text-decoration:none;transition:color .15s}
.auth-pro-link:hover{color:#92400e}
.saved-logins-box{margin-bottom:16px;padding:14px;background:var(--brand-50);border:1px solid var(--brand-200);border-radius:10px}
.saved-logins-box select{width:100%;margin-top:6px;border:1px solid var(--brand-200);border-radius:8px;background:#fff}

/* Pro Modal */
.pro-overlay{position:fixed;inset:0;background:rgba(0,0,0,.4);backdrop-filter:blur(2px);z-index:700;display:flex;align-items:center;justify-content:center}
.pro-panel{width:460px;background:#fff;border-radius:16px;box-shadow:var(--shadow-lg);overflow:hidden;animation:modalIn .2s}
.pro-panel-header{background:linear-gradient(135deg,#d97706,#92400e);padding:24px;text-align:center;color:#fff}
.pro-panel-header h2{font-size:22px;font-weight:800;margin-bottom:4px}
.pro-panel-header p{font-size:13px;opacity:.85}
.pro-panel-body{padding:24px}
.pro-feature-list{list-style:none;padding:0;margin:0 0 20px}
.pro-feature-list li{padding:8px 0;border-bottom:1px solid var(--gray-100);font-size:13px;color:var(--gray-700);display:flex;align-items:center;gap:8px}
.pro-feature-list li span{font-size:16px}
.pro-key-group{margin-bottom:16px}
.pro-key-group label{font-size:12px;font-weight:600;color:var(--gray-500);text-transform:uppercase;letter-spacing:.5px;display:block;margin-bottom:6px}
.pro-key-input{width:100%;padding:10px 13px;font-size:14px;font-family:var(--font-mono);border:1.5px solid var(--gray-200);border-radius:var(--radius);outline:none;text-align:center;letter-spacing:1px}
.pro-key-input:focus{border-color:#d97706;box-shadow:0 0 0 3px rgba(217,119,6,.1)}

/* Language Selector */
.lang-overlay{position:fixed;inset:0;background:rgba(0,0,0,.5);backdrop-filter:blur(3px);z-index:9500;display:flex;align-items:center;justify-content:center}
.lang-card{background:#fff;border-radius:16px;padding:32px;width:460px;box-shadow:0 20px 60px rgba(0,0,0,.2);animation:modalIn .3s;text-align:center}
.lang-card h2{font-size:20px;font-weight:800;color:var(--brand-800);margin-bottom:4px}
.lang-card p{font-size:13px;color:var(--gray-500);margin-bottom:20px}
.lang-grid{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin-bottom:12px;text-align:left}
.lang-opt{padding:10px 14px;border:1.5px solid var(--gray-200);border-radius:var(--radius);cursor:pointer;transition:all .15s;display:flex;align-items:center;gap:10px}
.lang-opt:hover{border-color:var(--brand-400);background:var(--brand-50)}
.lang-opt.active{border-color:var(--brand-500);background:var(--brand-50);box-shadow:0 0 0 3px rgba(139,111,94,.1)}
.lang-opt .lang-flag{font-size:20px}
.lang-opt .lang-label{font-size:13px;font-weight:600;color:var(--gray-700)}
.lang-btn{display:flex;align-items:center;gap:4px;padding:3px 10px;border:1px solid var(--gray-200);border-radius:var(--radius);font-size:12px;cursor:pointer;background:#fff;color:var(--gray-600);transition:all .15s}
.lang-btn:hover{border-color:var(--brand-400);background:var(--brand-50)}

/* RTL support */
html[dir="rtl"] .main{flex-direction:row-reverse}
html[dir="rtl"] .file-row{flex-direction:row-reverse}
html[dir="rtl"] .ctx-menu{text-align:right}
html[dir="rtl"] .topbar-right{margin-left:0;margin-right:auto}
html[dir="rtl"] .breadcrumb{direction:ltr}
html[dir="rtl"] .history-row{flex-direction:row-reverse}
html[dir="rtl"] .preview-panel{right:auto;left:0}

/* Dashboard */
.dash-overlay{position:fixed;inset:0;background:rgba(0,0,0,.4);backdrop-filter:blur(2px);z-index:600;display:flex;align-items:center;justify-content:center}
.dash-panel{width:90%;max-width:800px;max-height:85vh;background:#fff;border-radius:var(--radius-lg);box-shadow:var(--shadow-lg);display:flex;flex-direction:column;animation:modalIn .2s;overflow:hidden}
.dash-header{padding:16px 20px;border-bottom:1px solid var(--gray-200);display:flex;align-items:center;gap:12px;flex-shrink:0}
.dash-header h2{font-size:18px;font-weight:700;color:var(--brand-800);flex:1}
.dash-body{flex:1;overflow-y:auto;padding:20px}
.dash-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(160px,1fr));gap:12px;margin-bottom:20px}
.dash-card{background:var(--gray-50);border:1px solid var(--gray-200);border-radius:var(--radius);padding:16px;text-align:center}
.dash-card .dash-val{font-size:24px;font-weight:700;color:var(--brand-800);font-family:var(--font-mono)}
.dash-card .dash-label{font-size:12px;color:var(--gray-500);margin-top:4px}
.dash-section{margin-bottom:20px}
.dash-section h3{font-size:14px;font-weight:700;color:var(--brand-800);margin-bottom:8px;display:flex;align-items:center;gap:6px}
.dash-table{width:100%;font-size:12px;border-collapse:collapse}
.dash-table th{text-align:left;font-weight:600;color:var(--gray-500);padding:6px 8px;border-bottom:1px solid var(--gray-200);text-transform:uppercase;letter-spacing:.3px;font-size:11px}
.dash-table td{padding:6px 8px;border-bottom:1px solid var(--gray-100);font-family:var(--font-mono);font-size:12px}
.dash-table tr:hover td{background:var(--gray-50)}
.ext-bar{display:flex;align-items:center;gap:8px;margin-bottom:4px;font-size:12px}
.ext-bar .ext-name{width:60px;text-align:right;font-family:var(--font-mono);color:var(--gray-600);font-weight:600}
.ext-bar .ext-fill{height:18px;border-radius:3px;background:var(--brand-400);min-width:2px;transition:width .3s}
.ext-bar .ext-info{color:var(--gray-500);font-size:11px;white-space:nowrap}
.dash-loading{text-align:center;padding:40px;color:var(--gray-400);font-size:14px}

/* Sync */
.sync-overlay{position:fixed;inset:0;background:rgba(0,0,0,.4);backdrop-filter:blur(2px);z-index:600;display:flex;align-items:center;justify-content:center}
.sync-panel{width:90%;max-width:820px;max-height:85vh;background:#fff;border-radius:var(--radius-lg);box-shadow:var(--shadow-lg);display:flex;flex-direction:column;animation:modalIn .2s;overflow:hidden}
.sync-header{padding:16px 20px;border-bottom:1px solid var(--gray-200);display:flex;align-items:center;gap:12px;flex-shrink:0}
.sync-header h2{font-size:18px;font-weight:700;color:var(--brand-800);flex:1}
.sync-stats{display:flex;gap:12px;padding:12px 20px;background:var(--gray-50);border-bottom:1px solid var(--gray-200);flex-shrink:0;flex-wrap:wrap}
.sync-stat{padding:4px 10px;border-radius:12px;font-size:12px;font-weight:600}
.sync-stat.match{background:#f0fdf4;color:#16a34a}
.sync-stat.local{background:#eff6ff;color:#2563eb}
.sync-stat.remote{background:#fef3c7;color:#d97706}
.sync-stat.diff{background:#fef2f2;color:#dc2626}
.sync-body{flex:1;overflow-y:auto}
.sync-row{display:flex;align-items:center;padding:8px 20px;border-bottom:1px solid var(--gray-100);font-size:13px;gap:8px}
.sync-row:hover{background:var(--gray-50)}
.sync-row .sync-check{flex-shrink:0}
.sync-row .sync-icon{width:20px;text-align:center;font-size:14px;flex-shrink:0}
.sync-row .sync-name{flex:1;font-family:var(--font-mono);font-size:12px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.sync-row .sync-detail{font-size:11px;color:var(--gray-500);font-family:var(--font-mono);width:100px;text-align:right;flex-shrink:0}
.sync-row .sync-arrow{width:30px;text-align:center;font-size:16px;flex-shrink:0}
.sync-row .sync-status{width:80px;font-size:11px;font-weight:600;text-align:center;flex-shrink:0;padding:2px 6px;border-radius:4px}
.sync-row .sync-status.match{background:#f0fdf4;color:#16a34a}
.sync-row .sync-status.local_only{background:#eff6ff;color:#2563eb}
.sync-row .sync-status.remote_only{background:#fef3c7;color:#d97706}
.sync-row .sync-status.different{background:#fef2f2;color:#dc2626}
.sync-footer{padding:12px 20px;border-top:1px solid var(--gray-200);display:flex;gap:8px;align-items:center;flex-shrink:0;background:var(--gray-50)}
.sync-footer .sync-summary{flex:1;font-size:12px;color:var(--gray-500)}
</style>
</head>
<body>

<!-- AUTH -->
<div id="authScreen" class="auth-screen">
  <div class="auth-left">
    <div class="auth-card">
      <div class="auth-logo">
        """ + (f'<img src="data:image/png;base64,{LOGO_FULL}" alt="Aivelo FTP Vault" style="height:56px;width:auto">' if LOGO_FULL else '') + r"""
      </div>
      <h1 data-t="connect_title">Connect to your server</h1>
      <p class="subtitle" data-t="connect_sub">FTP, FTPS, or SFTP — your files, your server.</p>
      <div id="savedLoginsBox" class="saved-logins-box hidden">
        <label style="font-size:12px;font-weight:600;color:var(--gray-600);margin-bottom:4px;display:block" data-t="saved_logins">Saved Logins</label>
        <select id="savedLoginsSelect" class="form-input" onchange="selectSavedLogin()" style="font-family:var(--font-mono);font-size:13px;padding:10px 12px;cursor:pointer">
          <option value="">— Select a saved connection —</option>
        </select>
      </div>
      <div class="proto-group">
        <button class="proto-btn active" data-proto="FTP" data-port="21" onclick="selProto(this)">FTP</button>
        <button class="proto-btn" data-proto="FTPS" data-port="21" onclick="selProto(this)">FTPS</button>
        <button class="proto-btn" data-proto="SFTP" data-port="22" onclick="selProto(this)">SFTP</button>
      </div>
      <div class="form-row">
        <div class="form-group"><label data-t="host">Host</label><input class="form-input" id="inHost" placeholder="ftp.example.com"></div>
        <div class="form-group small"><label data-t="port">Port</label><input class="form-input" id="inPort" value="21"></div>
      </div>
      <div class="form-group"><label data-t="username">Username</label><input class="form-input" id="inUser" placeholder="username"></div>
      <div class="form-group"><label data-t="password">Password</label><input class="form-input" id="inPass" type="password" placeholder="••••••••"></div>
      <button class="btn btn-primary btn-lg btn-full" onclick="doConnect()" data-t="connect">Connect</button>
      <button class="btn btn-secondary btn-sm btn-full" onclick="saveToVault()" style="margin-top:8px" data-t="save_vault">🔐 Save to Encrypted Vault</button>
      <div id="authError" class="auth-error"></div>
      <div id="bookmarksRow" class="bookmarks-row hidden"></div>
    </div>
  </div>
  <div class="auth-right">
    <div class="auth-right-content">
      <h2 data-t="secure_transfer">Secure File Transfer</h2>
      <p data-t="secure_desc">Connect to your own server. Upload, download, and manage files with confidence.</p>
      <div class="auth-features">
        <div class="auth-feature"><span>🔐</span> <span data-t="feat_aes">TLS/SSH encrypted connections</span></div>
        <div class="auth-feature"><span>📁</span> <span data-t="feat_dual">Dual-pane file browser</span></div>
        <div class="auth-feature"><span>🔑</span> <span data-t="feat_chmod">Set file permissions (chmod)</span></div>
        <div class="auth-feature"><span>⚡</span> <span data-t="feat_fast">Fast uploads and downloads</span></div>
      </div>
      <div style="margin-top:24px"><a onclick="openProModal()" style="color:#fbbf24;font-size:14px;font-weight:700;cursor:pointer;text-decoration:none" data-t="upgrade_pro">✨ Upgrade to AI Pro — €13.99 one-time</a></div>
    </div>
  </div>
</div>

<!-- APP -->
<div id="appScreen" class="app-layout hidden">
  <div class="topbar">
    <div class="topbar-logo">
      """ + (f'<img src="data:image/png;base64,{LOGO_ICON}" style="height:32px;width:auto">' if LOGO_ICON else '') + r"""
    </div>
    <div class="conn-badge" id="connBadge">FTP</div>
    <div class="topbar-right">
      <button class="tb-btn-dark" onclick="openDashboard()">📊 <span data-t="dashboard">Dashboard</span></button>
      <button class="pro-tool-btn" id="btnProBackup" onclick="runBackup()" style="display:none"><span class="pro-tool-icon">💾</span> Backup</button>
      <button class="pro-tool-btn" id="btnProSeo" onclick="runSeoAudit()" style="display:none"><span class="pro-tool-icon">🔍</span> SEO</button>
      <button class="pro-tool-btn" id="btnProDead" onclick="runFindUnused()" style="display:none"><span class="pro-tool-icon">🧹</span> Dead Code</button>
      <button class="pro-tool-btn" id="btnProMin" onclick="runOptimize()" style="display:none"><span class="pro-tool-icon">⚡</span> Optimize</button>
      <button class="tb-btn-dark" onclick="openVault()" id="vaultBadge">🔒 <span data-t="vault">Vault</span></button>
      <button class="topbar-pro" onclick="openProModal()" id="topbarPro">✨ Pro</button>
      <button class="tb-btn-dark disconnect" onclick="doDisconnect()">⏻ <span data-t="disconnect">Disconnect</span></button>
    </div>
  </div>

  <!-- MENU BAR -->
  <div class="menubar" id="menuBar">
    <div class="menubar-item" data-menu="file">File
      <div class="menu-dropdown">
        <div class="menu-item" onclick="menuAction('connect')">🔌 Connect…</div>
        <div class="menu-item" onclick="menuAction('disconnect')">⏻ Disconnect</div>
        <div class="menu-sep"></div>
        <div class="menu-item" onclick="menuAction('vault')">🔒 Open Vault</div>
        <div class="menu-sep"></div>
        <div class="menu-item" onclick="menuAction('close')">✕ Close File</div>
      </div>
    </div>
    <div class="menubar-item" data-menu="edit">Edit
      <div class="menu-dropdown">
        <div class="menu-item" id="menuEdit" onclick="menuAction('edit')">✏️ Toggle Edit Mode</div>
        <div class="menu-item" id="menuSave" onclick="menuAction('save')">💾 Save<span class="shortcut">Ctrl+S</span></div>
        <div class="menu-item" onclick="menuAction('saveas')">📋 Save As Copy…</div>
        <div class="menu-sep"></div>
        <div class="menu-item" onclick="menuAction('checkpoint')">📸 Create Checkpoint</div>
        <div class="menu-item" onclick="menuAction('diff')">🔀 Diff Before Save</div>
      </div>
    </div>
    <div class="menubar-item" data-menu="server">Server
      <div class="menu-dropdown">
        <div class="menu-item" onclick="menuAction('search')">🔎 Search Files<span class="shortcut">Ctrl+F</span></div>
        <div class="menu-item" onclick="menuAction('dashboard')">📊 Dashboard</div>
        <div class="menu-sep"></div>
        <div class="menu-item" id="menuBackup" onclick="menuAction('backup')">💾 Site Backup<span class="pro-tag">PRO</span></div>
        <div class="menu-item" id="menuSeo" onclick="menuAction('seo')">🔍 SEO Audit<span class="pro-tag">PRO</span></div>
        <div class="menu-item" id="menuDead" onclick="menuAction('deadcode')">🧹 Dead Code Finder<span class="pro-tag">PRO</span></div>
        <div class="menu-item" id="menuOptimize" onclick="menuAction('optimize')">⚡ Optimize<span class="pro-tag">PRO</span></div>
      </div>
    </div>
    <div class="menubar-item" data-menu="language">Language
      <div class="menu-dropdown" id="menuLangList"></div>
    </div>
    <div class="menubar-item" data-menu="zoppy">Zoppy
      <div class="menu-dropdown">
        <div class="menu-item" onclick="menuAction('whozoppy')">🪓 Who is Zoppy?</div>
        <div class="menu-item" onclick="menuAction('zoppymaze')">🏆 Help Zoppy Find Treasure</div>
        <div class="menu-sep"></div>
        <div class="menu-item" id="menuSoundToggle" onclick="menuAction('togglesound')">🔊 Zoppy Sounds: ON</div>
      </div>
    </div>
    <div class="menubar-item" data-menu="help">Help
      <div class="menu-dropdown">
        <div class="menu-item" onclick="menuAction('register')">🔑 Register Pro…</div>
        <div class="menu-sep"></div>
        <div class="menu-item" onclick="menuAction('about')">ℹ️ About Aivelo FTP Vault</div>
      </div>
    </div>
  </div>

  <div class="sec-strip">
    <span data-t="secure_conn">Secure connection</span><span data-t="file_integrity">Encrypted transfer</span><span data-t="perm_ctrl">Permission control</span><span id="proBadgeMenu" style="margin-left:auto;color:#d4af37;font-weight:700;display:none" data-t="pro_active">Pro Active</span>
  </div>

  <!-- DUAL PANE -->
  <div class="dual-pane">
    <!-- LOCAL -->
    <div class="pane" id="localPane">
      <div class="pane-header">
        <h3>📁 <span data-t="local">Local</span></h3>
        <button class="btn btn-secondary btn-sm" onclick="localUp()" style="padding:3px 8px;font-size:11px">↑</button>
        <div class="pane-path" id="localPath">~</div>
      </div>
      <div class="pane-body" id="localBody"></div>
    </div>

    <!-- TRANSFER ARROWS -->
    <div class="transfer-col">
      <button onclick="uploadSelected()" title="Upload →">➡</button>
      <button onclick="downloadSelected()" title="← Download">⬅</button>
    </div>

    <!-- REMOTE -->
    <div class="pane" id="remotePane">
      <div class="pane-header">
        <h3>🌐 <span data-t="remote">Remote</span></h3>
        <button class="btn btn-secondary btn-sm" onclick="remoteUp()" style="padding:3px 8px;font-size:11px">↑</button>
        <div class="pane-path" id="remotePath">/</div>
        <button class="btn btn-secondary btn-sm" onclick="openSync()">🔄 <span data-t="sync">Sync</span></button>
        <button class="btn btn-secondary btn-sm" onclick="openHistory()">🕐 <span data-t="log">Log</span></button>
        <button class="btn btn-secondary btn-sm" onclick="openGallery()">📸 <span data-t="gallery">Gallery</span></button>
        <button class="btn btn-secondary btn-sm" onclick="loadRemote()">↻</button>
      </div>
      <div class="pane-toolbar">
        <button class="btn btn-sm" onclick="newFolder()" style="background:var(--brand-700);color:#fff;border:none">+ <span data-t="folder">Folder</span></button>
        <button class="btn btn-secondary btn-sm" onclick="renameSelected()">✏ <span data-t="rename">Rename</span></button>
        <button class="btn btn-sm" onclick="deleteSelected()" style="background:#fef2f2;color:var(--danger);border:1px solid #fecaca">🗑 <span data-t="delete">Delete</span></button>
      </div>
      <div class="dropzone" id="dropzone"><div style="font-size:24px;opacity:.4;margin-bottom:4px">☁</div><span data-t="drop_upload">Drop files here or click to upload</span><input type="file" id="fileInput" multiple style="display:none"></div>
      <div class="pane-body" id="remoteBody"></div>
    </div>
  </div>

  <div class="xfer-bar" id="xferBar" style="display:none">
    <span id="xferText">Transferring...</span>
    <div class="xfer-prog"><div class="xfer-fill" id="xferFill"></div></div>
  </div>
  <div class="status-bar"><span id="statusText">Connected</span></div>

  """ + (f'<div class="decor-logo" style="background-image:url(data:image/gif;base64,{LOGO_DECOR})"></div>' if LOGO_DECOR else '<div class="decor-logo"></div>') + r"""
</div>

<!-- PREVIEW / EDITOR PANEL -->
<div id="previewOverlay" class="preview-overlay hidden" onclick="if(event.target===this)closePreview()">
  <div class="preview-panel" onclick="event.stopPropagation()">
    <div class="preview-header">
      <span class="preview-icon" id="previewIcon">📄</span>
      <span class="preview-title" id="previewTitle">file.txt</span>
      <span class="preview-meta" id="previewMeta">0 B</span>
      <button class="btn btn-secondary btn-sm" id="btnEdit" onclick="toggleEdit()" style="display:none">✏ Edit</button>
      <button class="btn btn-secondary btn-sm" id="btnDiff" onclick="showDiffBeforeSave()" style="display:none">⇄ Diff</button>
      <button class="btn btn-secondary btn-sm" id="btnRelated" onclick="showRelatedFiles()" style="display:none" title="Open related files">🔗</button>
      <button class="btn btn-secondary btn-sm" id="btnCheckpoint" onclick="createCheckpoint()" style="display:none">📌</button>
      <button class="btn btn-secondary btn-sm" id="btnHistory" onclick="showFileHistory()" style="display:none">🕐</button>
      <button class="btn btn-secondary btn-sm" id="btnSaveAs" onclick="saveAsCopy()" style="display:none" title="Save as copy">📋</button>
      <button class="btn btn-primary btn-sm" id="btnSave" onclick="saveFile()" style="display:none">💾 Save</button>
      <button class="btn btn-secondary btn-sm" onclick="closePreview()">✕</button>
    </div>
    <div class="preview-toolbar" id="previewToolbar" style="display:none">
      <span class="lang-badge" id="previewLang">text</span>
      <span class="edit-indicator" id="editIndicator"></span>
    </div>
    <div class="preview-body" id="previewBody">
      <div class="binary-info">
        <div class="binary-icon">📄</div>
        <div>Select a file to preview</div>
      </div>
    </div>
  </div>
</div>

<!-- CHMOD MODAL -->
<div id="chmodModal" class="modal-overlay hidden" onclick="if(event.target===this)closeChmod()">
  <div class="modal">
    <h3>Set Permissions</h3>
    <p class="desc" id="chmodFile">file.txt</p>
    <div class="chmod-preview" id="chmodPreview">755</div>
    <div class="chmod-grid">
      <div></div><div style="text-align:center;font-weight:600">Read</div><div style="text-align:center;font-weight:600">Write</div><div style="text-align:center;font-weight:600">Execute</div>
      <div style="font-weight:600">Owner</div>
      <label><input type="checkbox" class="chmod-cb" data-bit="256" checked onchange="updateChmod()"></label>
      <label><input type="checkbox" class="chmod-cb" data-bit="128" checked onchange="updateChmod()"></label>
      <label><input type="checkbox" class="chmod-cb" data-bit="64" checked onchange="updateChmod()"></label>
      <div style="font-weight:600">Group</div>
      <label><input type="checkbox" class="chmod-cb" data-bit="32" checked onchange="updateChmod()"></label>
      <label><input type="checkbox" class="chmod-cb" data-bit="16" onchange="updateChmod()"></label>
      <label><input type="checkbox" class="chmod-cb" data-bit="8" checked onchange="updateChmod()"></label>
      <div style="font-weight:600">Others</div>
      <label><input type="checkbox" class="chmod-cb" data-bit="4" checked onchange="updateChmod()"></label>
      <label><input type="checkbox" class="chmod-cb" data-bit="2" onchange="updateChmod()"></label>
      <label><input type="checkbox" class="chmod-cb" data-bit="1" checked onchange="updateChmod()"></label>
    </div>
    <div style="margin-bottom:16px">
      <label style="font-size:12px;font-weight:600;color:var(--gray-700)">Or enter octal:</label>
      <input class="form-input" id="chmodInput" value="755" maxlength="4" style="font-family:var(--font-mono);font-size:16px;text-align:center;margin-top:4px" oninput="chmodFromInput()">
    </div>
    <div class="modal-actions">
      <button class="btn btn-secondary btn-sm" onclick="closeChmod()">Cancel</button>
      <button class="btn btn-primary btn-sm" onclick="applyChmod()">Apply</button>
    </div>
  </div>
</div>

<!-- LOCAL CONTEXT MENU -->
<div id="localCtx" class="ctx-menu hidden">
  <div class="ctx-item" onmousedown="menuAction('ctxUploadSelected')"><span class="ctx-icon">➡</span> <span data-t="upload_server">Upload to server</span></div>
  <div class="ctx-sep"></div>
  <div class="ctx-item" onmousedown="menuAction('ctxOpenLocal')"><span class="ctx-icon">📂</span> <span data-t="open_folder">Open folder</span></div>
  <div class="ctx-item" onmousedown="menuAction('ctxNewLocalFolder')"><span class="ctx-icon">📁</span> <span data-t="new_folder">New folder</span></div>
  <div class="ctx-item" onmousedown="menuAction('ctxRenameLocal')"><span class="ctx-icon">✏</span> <span data-t="rename">Rename</span></div>
  <div class="ctx-item" onmousedown="menuAction('ctxDeleteLocal')"><span class="ctx-icon">🗑</span> <span data-t="delete">Delete</span></div>
  <div class="ctx-sep"></div>
  <div class="ctx-item" onmousedown="menuAction('ctxCopyPathLocal')"><span class="ctx-icon">📋</span> <span data-t="copy_path">Copy path</span></div>
</div>

<!-- REMOTE CONTEXT MENU -->
<div id="remoteCtx" class="ctx-menu hidden">
  <div class="ctx-item" onmousedown="menuAction('ctxPreview')"><span class="ctx-icon">👁</span> <span data-t="preview_edit">Preview / Edit</span></div>
  <div class="ctx-item" onmousedown="menuAction('ctxDownload')"><span class="ctx-icon">⬇</span> <span data-t="download_file">Download file</span></div>
  <div class="ctx-item" onmousedown="menuAction('ctxDownloadSelected')"><span class="ctx-icon">⬅</span> <span data-t="download_local">Download to local folder</span></div>
  <div class="ctx-sep"></div>
  <div class="ctx-item" onmousedown="menuAction('ctxRename')"><span class="ctx-icon">✏</span> <span data-t="rename">Rename</span></div>
  <div class="ctx-item" onmousedown="menuAction('ctxChmod')"><span class="ctx-icon">🔑</span> <span data-t="set_perms">Set permissions (chmod)</span></div>
  <div class="ctx-item" onmousedown="menuAction('ctxCopyPathRemote')"><span class="ctx-icon">📋</span> <span data-t="copy_path">Copy path</span></div>
  <div class="ctx-sep"></div>
  <div class="ctx-item" onmousedown="menuAction('ctxNewFolder')"><span class="ctx-icon">📁</span> <span data-t="new_folder">New folder here</span></div>
  <div class="ctx-item" onmousedown="menuAction('ctxNewFile')"><span class="ctx-icon">📄</span> <span data-t="new_file">New file</span></div>
  <div class="ctx-item" onmousedown="menuAction('ctxZip')"><span class="ctx-icon">📦</span> <span data-t="zip_files">Zip selected files</span></div>
  <div class="ctx-item" onmousedown="menuAction('ctxUnzip')"><span class="ctx-icon">📂</span> <span data-t="unzip_here">Unzip here</span></div>
  <div class="ctx-item" onmousedown="menuAction('ctxRefresh')"><span class="ctx-icon">🔄</span> <span data-t="refresh">Refresh</span></div>
  <div class="ctx-sep"></div>
  <div class="ctx-item danger" onmousedown="menuAction('ctxDelete')"><span class="ctx-icon">🗑</span> <span data-t="delete">Delete</span></div>
</div>

<!-- DASHBOARD MODAL -->
<div id="dashOverlay" class="dash-overlay hidden" onclick="if(event.target===this)closeDash()">
  <div class="dash-panel" onclick="event.stopPropagation()">
    <div class="dash-header">
      <span style="font-size:22px">📊</span>
      <h2>Server Dashboard</h2>
      <button class="btn btn-secondary btn-sm" onclick="closeDash()">✕</button>
    </div>
    <div class="dash-body" id="dashBody">
      <div class="dash-loading">⏳ Scanning server...</div>
    </div>
  </div>
</div>

<!-- SYNC MODAL -->
<div id="syncOverlay" class="sync-overlay hidden" onclick="if(event.target===this)closeSync()">
  <div class="sync-panel" onclick="event.stopPropagation()">
    <div class="sync-header">
      <span style="font-size:22px">🔄</span>
      <h2>Folder Sync</h2>
      <button class="btn btn-secondary btn-sm" id="btnSyncRefresh" onclick="runSyncDiff()">⟳ Refresh</button>
      <button class="btn btn-secondary btn-sm" onclick="closeSync()">✕</button>
    </div>
    <div class="sync-stats" id="syncStats"></div>
    <div class="sync-body" id="syncBody">
      <div class="dash-loading">Click ⟳ Refresh to compare folders</div>
    </div>
    <div class="sync-footer">
      <div class="sync-summary" id="syncSummary">Compare local ↔ remote folders</div>
      <button class="btn btn-secondary btn-sm" onclick="syncSelectAll()">Select all</button>
      <button class="btn btn-secondary btn-sm" onclick="syncSelectNone()">Select none</button>
      <button class="btn btn-primary btn-sm" onclick="executeSync()">⚡ Sync Selected</button>
    </div>
  </div>
</div>

<div class="toast-wrap" id="toasts"></div>

<!-- LANGUAGE SELECTOR -->
<div id="langOverlay" class="lang-overlay hidden">
  <div class="lang-card">
    <div style="font-size:32px;margin-bottom:8px">🌐</div>
    <h2 id="langTitle">Choose Your Language</h2>
    <p>Select your preferred language for the interface</p>
    <div class="lang-grid" id="langGrid"></div>
    <button class="btn btn-primary btn-lg btn-full" onclick="confirmLang()" id="langConfirmBtn">Continue</button>
  </div>
</div>

<!-- NAG POPUP (after 30 launches) -->
<div id="proNag" class="pro-nag hidden">
  <div class="pro-nag-card">
    <div class="pro-badge">PRO UPGRADE AVAILABLE</div>
    <h2>You're loving Aivelo FTP!</h2>
    <p class="pro-subtitle">You've used the app <strong id="nagCount">30</strong> times. Unlock the full power with AI Pro.</p>
    <div class="pro-features">
      🤖 AI File Assistant — search, analyze, and manage files with natural language<br>
      🔍 Smart file search across your entire server<br>
      📝 AI-powered code review and suggestions<br>
      🧹 Intelligent cleanup recommendations<br>
      ⚡ Unlimited free updates
    </div>
    <div class="pro-price">€13.99</div>
    <div class="pro-price-sub">One-time payment · Lifetime license · No subscription</div>
    <button class="pro-btn-ai" onclick="openProModal();closeNag()">✨ Get AI Pro</button><br>
    <button class="pro-later" onclick="closeNag()">Maybe later — continue free version</button>
  </div>
</div>

<!-- PRO MODAL -->
<div id="proOverlay" class="pro-overlay hidden" onclick="if(event.target===this)closeProModal()">
  <div class="pro-panel" onclick="event.stopPropagation()">
    <div class="pro-panel-header">
      <h2>✨ Aivelo FTP Vault Pro</h2>
      <p>AI-powered file management for professionals</p>
    </div>
    <div class="pro-panel-body">
      <ul class="pro-feature-list">
        <li><span>🤖</span> <strong>AI File Assistant</strong> — natural language file search & management</li>
        <li><span>🔍</span> <strong>Smart Search</strong> — "find PHP files with mysql queries"</li>
        <li><span>📝</span> <strong>Code Review</strong> — AI analyzes your code for issues</li>
        <li><span>🧹</span> <strong>Smart Cleanup</strong> — find unused files, old logs, duplicates</li>
        <li><span>🔗</span> <strong>Dependency Check</strong> — find broken references in HTML/CSS</li>
        <li><span>⚡</span> <strong>Lifetime Updates</strong> — free updates forever</li>
      </ul>
      <div style="text-align:center;margin-bottom:16px">
        <div class="pro-price" style="font-size:28px">€13.99</div>
        <div style="font-size:12px;color:var(--gray-500)">One-time · No subscription · 30-day money-back guarantee</div>
      </div>
      <a href="https://buy.stripe.com/4gMfZidtmcwgcUI5Nea3u00" target="_blank" style="display:block;text-align:center;margin-bottom:16px">
        <button class="pro-btn-ai" style="width:100%">🛒 Purchase License Key</button>
      </a>
      <div class="pro-key-group">
        <label>Already have a key?</label>
        <input class="pro-key-input" id="proKeyInput" placeholder="AIVELO-XXXX-XXXX-XXXX-XXXX-XXXX" maxlength="31" onkeydown="if(event.key==='Enter')activateKey()">
      </div>
      <div id="proKeyError" class="auth-error"></div>
      <div class="modal-actions" style="margin-top:12px">
        <button class="btn btn-secondary btn-sm" onclick="closeProModal()">Close</button>
        <button class="btn btn-primary btn-sm" onclick="activateKey()">🔑 Activate</button>
      </div>
    </div>
  </div>
</div>

<!-- STYLED DIALOG (replaces prompt/confirm) -->
<div id="dialogOverlay" class="dialog-overlay hidden">
  <div class="dialog">
    <h3 id="dialogTitle">Confirm</h3>
    <p id="dialogMsg"></p>
    <input type="text" id="dialogInput" class="hidden" autocomplete="off">
    <div class="dialog-btns">
      <button class="btn btn-secondary btn-sm" id="dialogCancel" onclick="dialogResolve(null)">Cancel</button>
      <button class="btn btn-primary btn-sm" id="dialogOk" onclick="dialogResolve(true)">OK</button>
    </div>
  </div>
</div>

<!-- GALLERY -->
<div id="galleryOverlay" class="gallery-overlay hidden" onclick="if(event.target===this)closeGallery()">
  <div class="gallery-panel" onclick="event.stopPropagation()">
    <div class="gallery-header">
      <span style="font-size:22px">📸</span>
      <h2>Image Gallery</h2>
      <span style="font-size:12px;color:var(--gray-500)" id="galleryCount"></span>
      <button class="btn btn-secondary btn-sm" onclick="closeGallery()">✕</button>
    </div>
    <div class="gallery-body" id="galleryBody">
      <div class="gallery-loading">Loading images...</div>
    </div>
  </div>
</div>

<!-- LIGHTBOX -->
<div id="lightbox" class="gallery-lightbox hidden" onclick="closeLightbox()">
  <img id="lbImg" src="">
  <div class="lb-info" id="lbInfo"></div>
</div>

<!-- TRANSFER HISTORY -->
<div id="historyOverlay" class="history-overlay hidden" onclick="if(event.target===this)closeHistory()">
  <div class="history-panel" onclick="event.stopPropagation()">
    <div class="history-header">
      <span style="font-size:22px">🕐</span>
      <h2>Transfer History</h2>
      <input class="history-search" id="historySearch" placeholder="Search..." oninput="loadHistory()">
      <button class="btn btn-danger btn-sm" onclick="clearHistory()">Clear</button>
      <button class="btn btn-secondary btn-sm" onclick="closeHistory()">✕</button>
    </div>
    <div class="history-body" id="historyBody"></div>
  </div>
</div>

<!-- ZIP DIALOG -->
<div id="zipOverlay" class="zip-overlay hidden" onclick="if(event.target===this)closeZip()">
  <div class="zip-panel" onclick="event.stopPropagation()">
    <h3 style="margin-bottom:6px">📦 Create ZIP Archive</h3>
    <p style="font-size:13px;color:var(--gray-500);margin-bottom:16px" id="zipInfo">Zip selected files on the server (SFTP only)</p>
    <div class="form-group">
      <label>Archive name</label>
      <input class="form-input" id="zipName" value="archive.zip" style="font-family:var(--font-mono)">
    </div>
    <div id="zipFileList" style="max-height:150px;overflow-y:auto;margin-bottom:16px;font-size:12px;font-family:var(--font-mono);color:var(--gray-600)"></div>
    <div class="modal-actions">
      <button class="btn btn-secondary btn-sm" onclick="closeZip()">Cancel</button>
      <button class="btn btn-primary btn-sm" onclick="doZip()">📦 Create ZIP</button>
    </div>
  </div>
</div>

<!-- VAULT UNLOCK -->
<div id="vaultOverlay" class="modal-overlay hidden" onclick="if(event.target===this)closeVault()">
  <div class="modal" onclick="event.stopPropagation()">
    <h3>🔐 Encrypted Bookmark Vault</h3>
    <p class="desc" id="vaultDesc">Enter your master password to unlock saved connections.</p>
    <div class="form-group">
      <label>Master Password</label>
      <input class="form-input" id="vaultPass" type="password" placeholder="••••••••" onkeydown="if(event.key==='Enter')unlockVault()">
    </div>
    <div id="vaultError" class="auth-error"></div>
    <div id="vaultList" style="margin-top:12px"></div>
    <div class="modal-actions" style="margin-top:16px">
      <button class="btn btn-secondary btn-sm" onclick="closeVault()">Close</button>
      <button class="btn btn-primary btn-sm" id="vaultUnlockBtn" onclick="unlockVault()">🔓 Unlock</button>
    </div>
  </div>
</div>

<script>
const API = '';
let localPath = '', remotePath = '/', proto = 'FTP';
let localFiles = [], remoteFiles = [];
let localSelected = new Set(), remoteSelected = new Set();
let chmodTarget = '';

// Wrap fetch to always include session token
const _origFetch = window.fetch;
window.fetch = function(url, opts = {}) {
  if (typeof SESSION_TOKEN !== 'undefined' && SESSION_TOKEN) {
    opts.headers = opts.headers || {};
    if (opts.headers instanceof Headers) {
      opts.headers.set('X-Session-Token', SESSION_TOKEN);
    } else {
      opts.headers['X-Session-Token'] = SESSION_TOKEN;
    }
  }
  return _origFetch.call(this, url, opts);
};

// === AUTH ===
function selProto(btn) {
  document.querySelectorAll('.proto-btn').forEach(b => b.classList.remove('active'));
  btn.classList.add('active'); proto = btn.dataset.proto;
  document.getElementById('inPort').value = btn.dataset.port;
}

async function doConnect(trustFingerprint) {
  const host=document.getElementById('inHost').value.trim(), port=document.getElementById('inPort').value.trim();
  const user=document.getElementById('inUser').value.trim(), pass=document.getElementById('inPass').value;
  const err=document.getElementById('authError'); err.classList.remove('visible');
  if(!host||!user){err.textContent='Host and username required';err.classList.add('visible');return}
  // Hide any previous trust dialog
  const trustBox = document.getElementById('trustDialog');
  if(trustBox) trustBox.remove();
  try {
    const body = {host,port,username:user,password:pass,protocol:proto};
    if(trustFingerprint) body.trust_fingerprint = trustFingerprint;
    const r = await fetch(API+'/api/connect',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify(body)});
    const d = await r.json();
    if(!r.ok) {
      if(d.cert_error) {
        // Show trust dialog
        _showTrustDialog(d, host, port, user, pass);
        return;
      }
      throw new Error(d.error);
    }
    remotePath = d.cwd||'/';
    document.getElementById('connBadge').textContent = `${d.proto}  ${user}@${host}`;
    document.getElementById('authScreen').classList.add('hidden');
    document.getElementById('guardDwarfWrap').classList.remove('hidden');
    document.getElementById('guardToggle').classList.remove('hidden');
    document.getElementById('appScreen').classList.remove('hidden');
    loadLocal(); loadRemote();
    // Auto-save login (encrypted) and refresh dropdown
    fetch(API+'/api/logins/save',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({host,port,username:user,password:pass,protocol:proto})}).then(()=>refreshSavedLogins());
  } catch(e){err.textContent=e.message;err.classList.add('visible')}
}

function _showTrustDialog(d, host, port, user, pass) {
  // Remove any existing trust dialog
  const old = document.getElementById('trustDialog');
  if(old) old.remove();

  const isChanged = d.is_changed;
  const fp = d.fingerprint || 'UNKNOWN';
  const fpShort = fp.substring(0,4)+':'+fp.substring(4,8)+':'+fp.substring(8,12)+':'+fp.substring(12,16);

  const div = document.createElement('div');
  div.id = 'trustDialog';
  div.style.cssText = 'position:fixed;top:0;left:0;right:0;bottom:0;background:rgba(0,0,0,.6);z-index:9999;display:flex;align-items:center;justify-content:center';
  div.innerHTML = `
    <div style="background:var(--bg);border-radius:12px;padding:28px 32px;max-width:480px;width:90%;box-shadow:0 8px 32px rgba(0,0,0,.3)">
      <div style="font-size:18px;font-weight:700;color:${isChanged?'#DC2626':'#D97706'};margin-bottom:12px">
        ${isChanged ? '⚠️ Host Key Changed' : '🔐 Unknown Server'}
      </div>
      <div style="font-size:13px;line-height:1.6;color:var(--text);margin-bottom:16px;white-space:pre-wrap">${d.error.replace(/</g,'&lt;')}</div>
      <div style="background:var(--bg-alt,#F5F0EB);border-radius:8px;padding:12px;margin-bottom:20px;font-family:monospace;font-size:12px;word-break:break-all;color:var(--text-sec)">
        SHA-256: ${fp}
      </div>
      <div style="display:flex;gap:10px;justify-content:flex-end">
        <button onclick="document.getElementById('trustDialog').remove()" 
          style="padding:8px 18px;border-radius:8px;border:1px solid var(--border);background:var(--bg);cursor:pointer;font-size:13px">
          Cancel
        </button>
        ${isChanged ? `<button onclick="_resetAndTrust('${fp}','${host}',${port})" 
          style="padding:8px 18px;border-radius:8px;border:none;background:#DC2626;color:#fff;cursor:pointer;font-size:13px">
          Accept New Key
        </button>` : `<button onclick="document.getElementById('trustDialog').remove();doConnect('${fp}')" 
          style="padding:8px 18px;border-radius:8px;border:none;background:var(--brand);color:#fff;cursor:pointer;font-size:13px">
          Trust This Server
        </button>`}
      </div>
    </div>`;
  document.body.appendChild(div);
}

async function _resetAndTrust(fp, host, port) {
  // First remove the old stored fingerprint, then reconnect with trust
  await fetch(API+'/api/trust/reset',{method:'POST',headers:{'Content-Type':'application/json'},
    body:JSON.stringify({host, port, protocol:proto})});
  document.getElementById('trustDialog').remove();
  doConnect(fp);
}
document.getElementById('inPass').addEventListener('keydown',e=>{if(e.key==='Enter')doConnect()});

async function doDisconnect() {
  await fetch(API+'/api/disconnect',{method:'POST'});
  document.getElementById('authScreen').classList.remove('hidden');
    document.getElementById('guardDwarfWrap').classList.add('hidden');
    document.getElementById('guardToggle').classList.add('hidden');
  document.getElementById('appScreen').classList.add('hidden');
}

// === LOCAL FILES ===
async function loadLocal(path) {
  if(path !== undefined) localPath = path;
  try {
    const q = localPath ? '?path='+encodeURIComponent(localPath) : '';
    const r = await fetch(API+'/api/local/list'+q); const d = await r.json();
    if(!r.ok) throw new Error(d.error);
    localPath = d.path; localFiles = d.files; localSelected.clear();
    document.getElementById('localPath').textContent = localPath;
    renderLocal();
  } catch(e){status('Error: '+e.message)}
}

function renderLocal() {
  const body = document.getElementById('localBody');
  if(!localFiles.length){body.innerHTML='<div class="empty">Empty folder</div>';return}
  body.innerHTML = localFiles.map((f,i)=>{
    const icon = f.is_dir ? '📁' : fileEmoji(f.name);
    return `<div class="file-row${localSelected.has(i)?' selected':''}" data-idx="${i}"
      onclick="selLocal(event,${i})" ondblclick="dblLocal(${i})">
      <div class="file-icon">${icon}</div>
      <div class="file-name">${esc(f.name)}</div>
      <div class="file-size">${f.is_dir?'':fmtSize(f.size)}</div>
      <div class="file-time">${f.mtime||''}</div>
    </div>`;
  }).join('');
}

function selLocal(e,idx){
  if(e.ctrlKey||e.metaKey){localSelected.has(idx)?localSelected.delete(idx):localSelected.add(idx)}
  else if(e.shiftKey&&localSelected.size){const last=[...localSelected].pop();const[a,b]=[Math.min(last,idx),Math.max(last,idx)];for(let i=a;i<=b;i++)localSelected.add(i)}
  else{localSelected.clear();localSelected.add(idx)}
  renderLocal();
}
function dblLocal(idx){const f=localFiles[idx];if(f.is_dir)loadLocal(f.full_path)}
function localUp(){const parts=localPath.replace(/\\/g,'/').split('/');parts.pop();const p=parts.join('/')||'/';loadLocal(p)}

// === REMOTE FILES ===
async function loadRemote() {
  try {
    const r = await fetch(API+'/api/list?path='+encodeURIComponent(remotePath));
    const d = await r.json(); if(!r.ok) throw new Error(d.error);
    remoteFiles = d.files; remoteSelected.clear();
    document.getElementById('remotePath').textContent = remotePath;
    renderRemote(); status(`${remoteFiles.length} items in ${remotePath}`);
  } catch(e){status('Error: '+e.message)}
}

function renderRemote() {
  const body = document.getElementById('remoteBody');
  if(!remoteFiles.length){body.innerHTML='<div class="empty">Empty folder</div>';return}
  body.innerHTML = remoteFiles.map((f,i)=>{
    const icon = f.is_dir ? '📁' : fileEmoji(f.name);
    const fullPath = remotePath.replace(/\/+$/,'') + '/' + f.name;
    return `<div class="file-row${remoteSelected.has(i)?' selected':''}" data-idx="${i}"
      onclick="selRemote(event,${i})" ondblclick="dblRemote(${i})">
      <div class="file-icon">${icon}</div>
      <div class="file-name">${esc(f.name)}</div>
      <div class="file-size">${f.is_dir?'':fmtSize(f.size)}</div>
      <div class="file-time">${f.mtime||''}</div>
      <div class="file-perms" onclick="event.stopPropagation();openChmod('${esc(fullPath)}','${esc(f.name)}','${f.perms||''}')" title="Click to change permissions">${f.perms||''}</div>
      <div class="file-actions-cell">
        ${f.is_dir ? '' : `<button class="fa-btn" onclick="event.stopPropagation();openPreview('${esc(fullPath)}','${esc(f.name)}')" title="Preview" style="font-size:14px">👁</button>`}
        <button class="fa-btn dots" onclick="event.stopPropagation();showRowMenu(event,'${esc(fullPath)}','${esc(f.name)}',${f.is_dir},'${f.perms||''}')" title="More actions">⋮</button>
      </div>
    </div>`;
  }).join('');
}

function selRemote(e,idx){
  if(e.ctrlKey||e.metaKey){remoteSelected.has(idx)?remoteSelected.delete(idx):remoteSelected.add(idx)}
  else if(e.shiftKey&&remoteSelected.size){const last=[...remoteSelected].pop();const[a,b]=[Math.min(last,idx),Math.max(last,idx)];for(let i=a;i<=b;i++)remoteSelected.add(i)}
  else{remoteSelected.clear();remoteSelected.add(idx)}
  renderRemote();
}
function dblRemote(idx){
  const f=remoteFiles[idx];
  if(f.is_dir){remotePath=remotePath.replace(/\/+$/,'')+'/'+f.name;loadRemote()}
  else { openPreview(remotePath.replace(/\/+$/,'')+'/'+f.name, f.name); }
}
function remoteUp(){const parts=remotePath.split('/').filter(Boolean);parts.pop();remotePath='/'+parts.join('/');loadRemote()}

// === TRANSFERS ===
let _pendingUploadItems = [];

function dwarfWave() {
  var dw = document.getElementById('guardDwarfWrap');
  if (!dw || dw.classList.contains('hidden') || dw.classList.contains('off')) return;
  dw.classList.remove('idle', 'alert');
  dw.classList.add('working');
  if (zoppySoundEnabled) {
    playHammerSound();
    setTimeout(function(){ zoppySpeak(); }, 300);
  }
  setTimeout(function(){ dw.classList.remove('working'); dw.classList.add('idle'); }, 2500);
}

async function uploadSelected() {
  dwarfWave();
  const items = [...localSelected].map(i=>localFiles[i]);
  if(!items.length){status('Select local files or folders first');return}

  // Smart Upload Guard
  if (_guardEnabled) {
    try {
      var checkR = await fetch(API+'/api/upload_guard',{method:'POST',headers:{'Content-Type':'application/json'},
        body:JSON.stringify({files: items.map(function(f){return {name:f.name,full_path:f.full_path,size:f.size,is_dir:f.is_dir}}), remote_dir: remotePath})});
      var check = await checkR.json();
      if(check.safe === false) {
        _pendingUploadItems = items;
        showUploadGuard(check);
        return;
      }
    } catch(e) { /* guard check failed, proceed */ }
  }

  await doUploadItems(items);
}

function showUploadGuard(check) {
  // Trigger guard dwarf alert
  triggerGuardDwarf(check.warning || 'Careful!');
  document.getElementById('uploadGuardTitle').textContent = check.risk_level === 'high' ? 'High Risk Upload!' : 'Upload Warning';
  document.getElementById('uploadGuardMsg').textContent = check.warning || 'The AI detected a potential issue with this upload.';
  var filesDiv = document.getElementById('uploadGuardFiles');
  if(check.files_at_risk && check.files_at_risk.length) {
    filesDiv.style.display = 'block';
    filesDiv.innerHTML = '<strong>Files at risk:</strong> ' + check.files_at_risk.map(function(f){ return '<span style="background:#fef2f2;padding:2px 6px;border-radius:4px;margin:2px">' + f + '</span>'; }).join(' ');
  } else {
    filesDiv.style.display = 'none';
  }
  document.getElementById('uploadGuardOverlay').classList.remove('hidden');
}

function dismissUploadGuard() {
  document.getElementById('uploadGuardOverlay').classList.add('hidden');
  _pendingUploadItems = [];
}

async function forceUpload() {
  document.getElementById('uploadGuardOverlay').classList.add('hidden');
  var items = _pendingUploadItems;
  _pendingUploadItems = [];
  await doUploadItems(items);
}

async function doUploadItems(items) {
  var total = 0;
  showXfer('Preparing upload...');
  var pollId = setInterval(pollXferProgress, 400);
  for(var i = 0; i < items.length; i++) {
    var f = items[i];
    updateXfer('Uploading ' + f.name + '...', 0);
    try {
      var r = await fetch(API+'/api/local/upload_to_remote',{method:'POST',headers:{'Content-Type':'application/json'},
        body:JSON.stringify({local_path:f.full_path, remote_dir:remotePath})});
      var d = await r.json(); if(!r.ok) throw new Error(d.error);
      if(d.uploaded !== undefined) {
        var info = d.errors ? ' (' + d.errors.length + ' failed)' : '';
        toast('Uploaded folder: ' + f.name + ' — ' + d.uploaded + '/' + d.total_found + ' files' + info,'ok');
        total += d.uploaded;
      } else {
        toast('Uploaded: ' + f.name,'ok');
        total++;
      }
    } catch(e){toast('Failed: ' + e.message,'err')}
  }
  clearInterval(pollId);
  hideXfer(); loadRemote();
}

function pollXferProgress() {
  fetch(API+'/api/xfer_progress').then(function(r){return r.json()}).then(function(d){
    if(!d.active) return;
    var filePct = d.bytes_total > 0 ? Math.round(d.bytes_sent / d.bytes_total * 100) : 0;
    var fileInfo = d.file_index + '/' + d.file_total;
    var sizeSent = formatSize(d.bytes_sent);
    var sizeTotal = formatSize(d.bytes_total);
    updateXfer(fileInfo + ' — ' + (d.current_file||'') + ' (' + sizeSent + ' / ' + sizeTotal + ')', filePct);
  }).catch(function(){});
}

function formatSize(b) {
  if(b<1024) return b+'B';
  if(b<1048576) return (b/1024).toFixed(1)+'KB';
  if(b<1073741824) return (b/1048576).toFixed(1)+'MB';
  return (b/1073741824).toFixed(1)+'GB';
}

function updateXfer(msg, pct) {
  document.getElementById('xferText').textContent = msg;
  var fill = document.getElementById('xferFill');
  if(fill) fill.style.width = Math.min(100, pct) + '%';
}




// === GUARD DWARF ===
let _guardEnabled = true;

function toggleGuard() {
  _guardEnabled = document.getElementById('guardEnabled').checked;
  var wrap = document.getElementById('guardDwarfWrap');
  if (wrap) {
    wrap.classList.toggle('off', !_guardEnabled);
  }
}

function triggerGuardDwarf(msg) {
  var wrap = document.getElementById('guardDwarfWrap');
  var speech = document.getElementById('guardSpeech');
  if (!wrap) return;
  // Short message for speech bubble
  var short = msg.length > 30 ? msg.substring(0, 28) + '...' : msg;
  if (speech) speech.textContent = short;
  wrap.classList.remove('idle', 'alert', 'working');
  void wrap.offsetWidth;
  wrap.classList.add('alert');
  playHammerSound();
  setTimeout(function() {
    wrap.classList.remove('alert');
    wrap.classList.add('idle');
  }, 2000);
}

// === GUARD DWARF SOUND ===
// === ZOPPY SOUND SYSTEM ===
var zoppySoundEnabled = true;

function toggleZoppySound() {
  zoppySoundEnabled = !zoppySoundEnabled;
  var el = document.getElementById('menuSoundToggle');
  if (el) el.textContent = zoppySoundEnabled ? '🔊 Zoppy Sounds: ON' : '🔇 Zoppy Sounds: OFF';
  toast(zoppySoundEnabled ? '🔊 Zoppy unmuted' : '🔇 Zoppy muted', 'ok');
}

function playHammerSound() {
  if (!zoppySoundEnabled) return;
  try {
    var ctx = new (window.AudioContext || window.webkitAudioContext)();
    [0, 0.4, 0.8].forEach(function(t) {
      var osc = ctx.createOscillator();
      var gain = ctx.createGain();
      osc.type = 'square';
      osc.frequency.setValueAtTime(800, ctx.currentTime + t);
      osc.frequency.exponentialRampToValueAtTime(200, ctx.currentTime + t + 0.1);
      gain.gain.setValueAtTime(0.15, ctx.currentTime + t);
      gain.gain.exponentialRampToValueAtTime(0.001, ctx.currentTime + t + 0.15);
      osc.connect(gain);
      gain.connect(ctx.destination);
      osc.start(ctx.currentTime + t);
      osc.stop(ctx.currentTime + t + 0.15);
      var osc2 = ctx.createOscillator();
      var gain2 = ctx.createGain();
      osc2.type = 'sine';
      osc2.frequency.setValueAtTime(1200, ctx.currentTime + t + 0.02);
      osc2.frequency.exponentialRampToValueAtTime(600, ctx.currentTime + t + 0.2);
      gain2.gain.setValueAtTime(0.08, ctx.currentTime + t + 0.02);
      gain2.gain.exponentialRampToValueAtTime(0.001, ctx.currentTime + t + 0.25);
      osc2.connect(gain2);
      gain2.connect(ctx.destination);
      osc2.start(ctx.currentTime + t + 0.02);
      osc2.stop(ctx.currentTime + t + 0.25);
    });
  } catch(e) {}
}

function zoppySpeak() {
  if (!zoppySoundEnabled || !ZOPPY_SND) return;
  try {
    var audio = new Audio('data:audio/mp3;base64,' + ZOPPY_SND);
    audio.volume = 0.8;
    audio.play();
  } catch(e) {}
}

// === PRO TOOLS ===
async function runBackup() {
  var ok = await styledConfirm('Site Backup', 'Create a full backup of ' + remotePath + '?\nThis zips all files and saves the archive on the server.');
  if (!ok) return;

  // Start backup
  try {
    var r = await fetch(API+'/api/pro/backup',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({path:remotePath})});
    var d = await r.json();
    if(d.error){toast(d.error,'err');return}
  } catch(e){toast('Failed: '+e.message,'err');return}

  // Show progress overlay
  var ov = document.getElementById('backupOverlay');
  if(!ov) {
    ov = document.createElement('div');
    ov.id = 'backupOverlay';
    ov.className = 'modal-overlay';
    document.body.appendChild(ov);
  }
  ov.innerHTML = '<div class="modal" style="width:400px;text-align:center">' +
    '<div style="font-size:32px;margin-bottom:8px">\uD83D\uDCBE</div>' +
    '<h3 id="backupTitle" style="margin:0 0 12px">Backing up...</h3>' +
    '<div style="background:#f3f4f6;border-radius:8px;height:20px;overflow:hidden;margin-bottom:8px">' +
    '<div id="backupBar" style="height:100%;background:linear-gradient(90deg,var(--brand-700),var(--brand-500));border-radius:8px;transition:width .5s;width:0%"></div></div>' +
    '<div id="backupInfo" style="font-size:12px;color:#6b7280;margin-bottom:12px">Scanning files...</div>' +
    '<button class="btn btn-danger btn-sm" onclick="cancelBackup()" id="backupCancelBtn">Cancel</button>' +
    '<button class="btn btn-primary btn-sm" onclick="document.getElementById(\x27backupOverlay\x27).classList.add(\x27hidden\x27)" id="backupCloseBtn" style="display:none;margin-left:6px">OK</button>' +
    '</div>';
  ov.classList.remove('hidden');
  document.getElementById('backupBar').style.width = '0%';
  document.getElementById('backupCancelBtn').style.display = '';

  // Animate dwarf
  var dwarf = document.getElementById('guardDwarfWrap');
  if(dwarf) { dwarf.classList.remove('idle', 'alert'); dwarf.classList.add('working'); }

  // Poll for progress
  _backupPolling = setInterval(async function() {
    try {
      var r = await fetch(API+'/api/pro/backup/status');
      var s = await r.json();
      var bar = document.getElementById('backupBar');
      var info = document.getElementById('backupInfo');
      var title = document.getElementById('backupTitle');

      if(s.phase === 'scanning') {
        bar.style.width = '5%';
        info.textContent = 'Scanning: ' + (s.current || '...');
      } else if(s.phase === 'zipping') {
        var pct = s.total > 0 ? Math.round((s.done / s.total) * 85) + 5 : 10;
        bar.style.width = pct + '%';
        info.textContent = s.done + '/' + s.total + ' files \u2014 ' + (s.current || '');
      } else if(s.phase === 'uploading') {
        var upPct = 90;
        if(s.upload_size > 0 && s.upload_done > 0) {
          upPct = 90 + Math.round((s.upload_done / s.upload_size) * 10);
        }
        bar.style.width = Math.min(upPct, 99) + '%';
        var upSize = s.upload_size > 1048576 ? (s.upload_size/1048576).toFixed(1)+' MB' : (s.upload_size/1024).toFixed(0)+' KB';
        var upDone = s.upload_done > 1048576 ? (s.upload_done/1048576).toFixed(1)+' MB' : (s.upload_done/1024).toFixed(0)+' KB';
        info.textContent = 'Uploading ' + s.current + ' (' + upDone + ' / ' + upSize + ')';
      } else if(s.phase === 'done') {
        clearInterval(_backupPolling);
        bar.style.width = '100%';
        title.textContent = '\u2705 Backup Complete';
        document.getElementById('backupCancelBtn').style.display = 'none';
        setTimeout(function(){ ov.classList.add('hidden'); }, 3000);
        var res = s.result;
        var sizeStr = res.zip_size < 1048576 ? (res.zip_size/1024).toFixed(1)+' KB' : (res.zip_size/1048576).toFixed(1)+' MB';
        info.innerHTML = '<strong>' + res.zip_name + '</strong><br>' + sizeStr + ' \u00b7 ' + res.files_backed_up + ' files';
        toast('Backup: ' + res.zip_name + ' (' + sizeStr + ')','ok');
        loadRemote();
        if(dwarf) { dwarf.classList.remove('alert','working'); dwarf.classList.add('idle'); }
      } else if(s.phase === 'cancelled') {
        clearInterval(_backupPolling);
        title.textContent = 'Backup Cancelled';
        info.textContent = 'Cancelled by user';
        bar.style.width = '0%';
        document.getElementById('backupCancelBtn').style.display = 'none';
        if(dwarf) { dwarf.classList.remove('alert','working'); dwarf.classList.add('idle'); }
        setTimeout(function(){ ov.classList.add('hidden'); }, 1500);
      } else if(s.error) {
        clearInterval(_backupPolling);
        title.textContent = '\u274c Backup Failed';
        info.textContent = s.error;
        bar.style.width = '0%';
        document.getElementById('backupCancelBtn').style.display = 'none';
        toast(s.error,'err');
        setTimeout(function(){ ov.classList.add('hidden'); }, 3000);
        if(dwarf) { dwarf.classList.remove('alert','working'); dwarf.classList.add('idle'); }
      } else if(!s.running && !s.phase) {
        // Not started yet
      }
    } catch(e){}
  }, 800);
}

var _backupPolling = null;

async function cancelBackup() {
  try {
    await fetch(API+'/api/pro/backup/cancel',{method:'POST'});
    toast('Cancelling backup...','ok');
  } catch(e){}
}

function proToolStatus(msg) {
  var el = document.getElementById('proToolResult');
  if (el) el.textContent = msg;
}

async function runSeoAudit() {
  proToolStatus('Scanning pages...');
  try {
    var r = await fetch(API+'/api/pro/seo_audit',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({path:remotePath})});
    var d = await r.json();
    if(d.error){proToolStatus(d.error);toast(d.error,'err');return}
    var scoreColor = d.score >= 80 ? '#22c55e' : d.score >= 50 ? '#d97706' : '#ef4444';
    var html = '<div style="text-align:center;margin-bottom:16px"><div style="font-size:56px;font-weight:800;color:'+scoreColor+';font-family:Playfair Display,serif">'+d.score+'</div><div style="font-size:12px;color:#6b7280">SEO Score ('+d.total_scanned+' pages)</div></div>';
    if(!d.files.length) html += '<div style="text-align:center;color:#22c55e;font-weight:600">All clear!</div>';
    for(var i=0;i<d.files.length;i++){
      var f=d.files[i];
      html+='<div style="margin-bottom:10px;padding:10px;background:#f9fafb;border-radius:8px;border:1px solid #e5e7eb"><div style="font-weight:600;font-size:13px;margin-bottom:4px">'+f.file+'</div>';
      for(var j=0;j<f.issues.length;j++){
        var iss=f.issues[j];
        var icon=iss.type==='error'?'\u274c':iss.type==='warn'?'\u26a0\ufe0f':'\u2139\ufe0f';
        html+='<div style="font-size:12px;padding:2px 0">'+icon+' '+iss.msg+'</div>';
      }
      html+='</div>';
    }
    showProResults('SEO Audit', html);
    proToolStatus('SEO: ' + d.score + '/100');
  } catch(e){proToolStatus('Error');toast(e.message,'err')}
}

async function runFindUnused() {
  proToolStatus('Analyzing...');
  try {
    var r = await fetch(API+'/api/pro/find_unused',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({path:remotePath})});
    var d = await r.json();
    if(d.error){proToolStatus(d.error);toast(d.error,'err');return}
    var html = '';
    var total = d.unused_css.length + d.unused_js.length + d.broken_refs.length;
    if(d.unused_css.length){
      html+='<div style="margin-bottom:12px"><div style="font-weight:600;font-size:13px;color:#dc2626;margin-bottom:6px">Unused CSS ('+d.unused_css.length+')</div>';
      for(var i=0;i<d.unused_css.length;i++) html+='<div style="font-size:12px;padding:3px 8px;background:#fef2f2;border-radius:4px;margin:2px 0">'+d.unused_css[i]+'</div>';
      html+='</div>';
    }
    if(d.unused_js.length){
      html+='<div style="margin-bottom:12px"><div style="font-weight:600;font-size:13px;color:#dc2626;margin-bottom:6px">Unused JS ('+d.unused_js.length+')</div>';
      for(var i=0;i<d.unused_js.length;i++) html+='<div style="font-size:12px;padding:3px 8px;background:#fef2f2;border-radius:4px;margin:2px 0">'+d.unused_js[i]+'</div>';
      html+='</div>';
    }
    if(d.broken_refs.length){
      html+='<div style="margin-bottom:12px"><div style="font-weight:600;font-size:13px;color:#d97706;margin-bottom:6px">Broken Refs ('+d.broken_refs.length+')</div>';
      for(var i=0;i<d.broken_refs.length;i++) html+='<div style="font-size:12px;padding:3px 8px;background:#fffbeb;border-radius:4px;margin:2px 0">'+d.broken_refs[i]+'</div>';
      html+='</div>';
    }
    if(!html) html='<div style="text-align:center;color:#22c55e;font-weight:600">All clean!</div>';
    showProResults('Dead Code Finder', html);
    proToolStatus(total ? total + ' issues' : 'Clean');
  } catch(e){proToolStatus('Error');toast(e.message,'err')}
}

let _optimizeMode = 'safe';
let _optimizeScanResults = null;
let _lastBackupDir = null;

async function runOptimize() {
  proToolStatus('Scanning files...');
  try {
    const r = await fetch(API+'/api/pro/optimize/scan',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({path:remotePath, mode:_optimizeMode})});
    const d = await r.json();
    if(d.error){proToolStatus(d.error);toast(d.error,'err');return}
    _optimizeScanResults = d;
    _showOptimizePreview(d);
    proToolStatus(d.summary.ready+' files ready');
  } catch(e){proToolStatus('Error');toast(e.message,'err')}
}

function _showOptimizePreview(d) {
  const s = d.summary;
  let html = `
    <div style="text-align:center;margin-bottom:16px">
      <div style="font-size:24px;font-weight:700;color:#22c55e">${(s.total_potential_savings/1024).toFixed(1)} KB</div>
      <div style="font-size:12px;color:#9ca3af">potential savings</div>
    </div>
    <div style="display:flex;gap:8px;justify-content:center;margin-bottom:16px">
      <span style="background:#dcfce7;color:#16a34a;padding:3px 10px;border-radius:12px;font-size:11px;font-weight:600">${s.ready} ready</span>
      <span style="background:#f3f4f6;color:#6b7280;padding:3px 10px;border-radius:12px;font-size:11px;font-weight:600">${s.skipped} skipped</span>
      ${s.risky?`<span style="background:#fef3c7;color:#d97706;padding:3px 10px;border-radius:12px;font-size:11px;font-weight:600">${s.risky} risky</span>`:''}
      ${s.errors?`<span style="background:#fee2e2;color:#dc2626;padding:3px 10px;border-radius:12px;font-size:11px;font-weight:600">${s.errors} errors</span>`:''}
    </div>
    <div style="display:flex;gap:6px;justify-content:center;margin-bottom:16px">
      <button onclick="_optimizeMode='safe';runOptimize()" style="padding:5px 14px;border-radius:6px;font-size:11px;cursor:pointer;border:1px solid ${_optimizeMode==='safe'?'#8B6F5E':'#e5e7eb'};background:${_optimizeMode==='safe'?'#F5F0EB':'#fff'};font-weight:${_optimizeMode==='safe'?'700':'400'}">🛡️ Safe</button>
      <button onclick="_optimizeMode='aggressive';runOptimize()" style="padding:5px 14px;border-radius:6px;font-size:11px;cursor:pointer;border:1px solid ${_optimizeMode==='aggressive'?'#d97706':'#e5e7eb'};background:${_optimizeMode==='aggressive'?'#fffbeb':'#fff'};font-weight:${_optimizeMode==='aggressive'?'700':'400'}">⚡ Aggressive</button>
    </div>`;

  for(const r of d.results) {
    const riskColors = {low:'#22c55e',medium:'#d97706',high:'#dc2626',none:'#9ca3af',unknown:'#9ca3af'};
    const riskBg = {low:'#dcfce7',medium:'#fef3c7',high:'#fee2e2',none:'#f3f4f6',unknown:'#f3f4f6'};
    const statusIcons = {ready:'✅',skipped:'⏭️',risky:'⚠️',error:'❌'};
    const checked = r.status==='ready' ? 'checked' : '';
    const disabled = (r.status==='skipped'||r.status==='error') ? 'disabled' : '';
    html += `<div style="font-size:12px;padding:8px 10px;background:#f9fafb;border-radius:8px;margin:4px 0;border:1px solid #e5e7eb">
      <div style="display:flex;justify-content:space-between;align-items:center">
        <label style="display:flex;align-items:center;gap:6px;cursor:pointer">
          <input type="checkbox" class="opt-file-cb" data-file="${r.file}" ${checked} ${disabled} style="cursor:pointer">
          <span style="font-weight:600">${r.file}</span>
        </label>
        <div style="display:flex;gap:8px;align-items:center">
          <span style="background:${riskBg[r.risk]};color:${riskColors[r.risk]};padding:2px 8px;border-radius:8px;font-size:10px;font-weight:600">${r.risk}</span>
          <span style="color:${r.saved>50?'#22c55e':'#9ca3af'};font-weight:600">${r.saved>0?'-'+r.pct+'%':'—'}</span>
        </div>
      </div>
      ${r.reason?`<div style="font-size:11px;color:#6b7280;margin-top:3px;padding-left:22px">${r.reason}</div>`:''}
      ${r.saved>50?`<div style="font-size:11px;color:#6b7280;margin-top:2px;padding-left:22px">${(r.orig/1024).toFixed(1)}KB → ${(r.new/1024).toFixed(1)}KB</div>`:''}
    </div>`;
  }

  html += `<div style="display:flex;gap:8px;justify-content:center;margin-top:16px;padding-top:16px;border-top:1px solid #e5e7eb">
    <button onclick="document.getElementById('proResultsOverlay').classList.add('hidden')" class="btn btn-secondary btn-sm">Cancel</button>
    <button onclick="_applyOptimize()" class="btn btn-sm" style="background:#22c55e;color:#fff;border:none;font-weight:600">🚀 Apply & Backup</button>
  </div>`;

  showProResults('⚡ Optimize Files', html);
}

async function _applyOptimize() {
  const checkboxes = document.querySelectorAll('.opt-file-cb:checked:not(:disabled)');
  const files = [...checkboxes].map(cb => cb.dataset.file);
  if(!files.length){toast('No files selected','err');return}

  document.getElementById('proResBody').innerHTML = '<div style="text-align:center;padding:40px"><div style="font-size:24px;margin-bottom:8px">⏳</div>Backing up & optimizing '+files.length+' files...</div>';

  try {
    const r = await fetch(API+'/api/pro/optimize/apply',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({path:remotePath, files:files, mode:_optimizeMode})});
    const d = await r.json();
    if(d.error){toast(d.error,'err');return}
    _lastBackupDir = d.backup_dir;

    let html = `<div style="text-align:center;margin-bottom:16px">
      <div style="font-size:24px;font-weight:700;color:#22c55e">${(d.total_saved/1024).toFixed(1)} KB saved</div>
      <div style="font-size:12px;color:#9ca3af">${d.backed_up} files backed up to ${d.backup_dir.split('/').pop()}</div>
    </div>`;

    for(const r2 of d.results) {
      if(r2.error){html+=`<div style="font-size:12px;color:#dc2626;padding:4px 0">❌ ${r2.file}: ${r2.error}</div>`;continue}
      const color = r2.applied?'#22c55e':'#9ca3af';
      const icon = r2.applied?'✅':'⏭️';
      html+=`<div style="font-size:12px;padding:6px 8px;background:#f9fafb;border-radius:6px;margin:3px 0;display:flex;justify-content:space-between;border:1px solid #e5e7eb">
        <span>${icon} <strong>${r2.file}</strong></span>
        <span style="color:${color};font-weight:600">${r2.applied?'-'+r2.pct+'%':'skipped'}</span>
      </div>`;
    }

    html+=`<div style="display:flex;gap:8px;justify-content:center;margin-top:16px;padding-top:16px;border-top:1px solid #e5e7eb">
      <button onclick="document.getElementById('proResultsOverlay').classList.add('hidden');loadRemote()" class="btn btn-sm" style="background:#22c55e;color:#fff;border:none">Done</button>
      <button onclick="_rollbackOptimize()" class="btn btn-sm" style="background:#dc2626;color:#fff;border:none">↩ Rollback</button>
    </div>`;

    document.getElementById('proResBody').innerHTML = html;
    proToolStatus('Saved '+(d.total_saved/1024).toFixed(1)+'KB');
  } catch(e){toast(e.message,'err')}
}

async function _rollbackOptimize() {
  if(!_lastBackupDir){toast('No backup to rollback','err');return}
  document.getElementById('proResBody').innerHTML = '<div style="text-align:center;padding:40px"><div style="font-size:24px;margin-bottom:8px">↩</div>Restoring original files...</div>';
  try {
    const r = await fetch(API+'/api/pro/optimize/rollback',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({path:remotePath, backup_dir:_lastBackupDir})});
    const d = await r.json();
    if(d.error){toast(d.error,'err');return}
    document.getElementById('proResBody').innerHTML = `<div style="text-align:center;padding:40px">
      <div style="font-size:48px;margin-bottom:12px">✅</div>
      <div style="font-size:16px;font-weight:700">Restored ${d.restored} files</div>
      <div style="font-size:12px;color:#6b7280;margin-top:4px">All changes have been rolled back</div>
      <button onclick="document.getElementById('proResultsOverlay').classList.add('hidden');loadRemote()" class="btn btn-sm" style="margin-top:16px;background:var(--brand);color:#fff;border:none">Done</button>
    </div>`;
    proToolStatus('Rollback complete');
    _lastBackupDir = null;
  } catch(e){toast(e.message,'err')}
}

function showProResults(title, bodyHtml) {
  var ov = document.getElementById('proResultsOverlay');
  if(!ov) {
    ov = document.createElement('div');
    ov.id = 'proResultsOverlay';
    ov.className = 'preview-overlay';
    ov.onclick = function(e){if(e.target===ov)ov.classList.add('hidden')};
    ov.innerHTML = '<div class="preview-panel" style="max-width:500px"><div class="preview-header" style="background:linear-gradient(135deg,#1a1a2e,#16213e)"><span class="preview-title" style="color:#d4af37;font-family:Playfair Display,serif" id="proResTitle"></span><button class="btn btn-sm" onclick="document.getElementById(\x27proResultsOverlay\x27).classList.add(\x27hidden\x27)" style="background:rgba(212,175,55,.2);color:#d4af37;border:none">\u2715</button></div><div id="proResBody" style="padding:20px;overflow-y:auto;flex:1"></div></div>';
    document.body.appendChild(ov);
  }
  document.getElementById('proResTitle').textContent = title;
  document.getElementById('proResBody').innerHTML = bodyHtml;
  ov.classList.remove('hidden');
}


async function downloadSelected() {
  dwarfWave();
  const items = [...remoteSelected].map(i=>remoteFiles[i]);
  if(!items.length){status('Select remote files first');return}
  showXfer('Preparing download...');
  var pollId = setInterval(pollXferProgress, 400);
  for(const f of items) {
    const rpath = remotePath.replace(/\/+$/,'')+'/'+f.name;
    updateXfer('Downloading ' + f.name + (f.is_dir ? ' (folder)...' : '...'), 0);
    try {
      const r = await fetch(API+'/api/local/download_from_remote',{method:'POST',headers:{'Content-Type':'application/json'},
        body:JSON.stringify({remote_path:rpath, local_dir:localPath, is_dir:f.is_dir})});
      const d = await r.json(); if(!r.ok) throw new Error(d.error);
      if(d.downloaded !== undefined) {
        toast('Downloaded folder: ' + f.name + ' \u2014 ' + d.downloaded + '/' + d.total + ' files','ok');
      } else {
        toast('Downloaded: ' + f.name,'ok');
      }
    } catch(e){toast('Failed: ' + e.message,'err')}
  }
  clearInterval(pollId);
  hideXfer(); loadLocal();
}

// Drag-and-drop upload
const dz=document.getElementById('dropzone'), fi=document.getElementById('fileInput');
dz.addEventListener('click',()=>fi.click());
dz.addEventListener('dragover',e=>{e.preventDefault();dz.classList.add('dragover')});
dz.addEventListener('dragleave',()=>dz.classList.remove('dragover'));
dz.addEventListener('drop',e=>{e.preventDefault();dz.classList.remove('dragover');handleDrop(e.dataTransfer.files)});
fi.addEventListener('change',e=>handleDrop(e.target.files));
async function handleDrop(fl){
  for(const f of fl){
    showXfer(`Uploading ${f.name}...`);
    const form=new FormData();form.append('file',f);form.append('path',remotePath);
    try{const r=await fetch(API+'/api/upload',{method:'POST',body:form});if(!r.ok)throw new Error((await r.json()).error);toast(`Uploaded: ${f.name}`,'ok')}
    catch(e){toast(`Failed: ${e.message}`,'err')}
  }
  hideXfer();loadRemote();
}

// === REMOTE OPERATIONS ===
async function newFolder(){
  const name = await styledPrompt(t('new_folder_title'), t('enter_folder'), '');
  if(!name)return;
  try{const r=await fetch(API+'/api/mkdir',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({path:remotePath.replace(/\/+$/,'')+'/'+name})});if(!r.ok)throw new Error((await r.json()).error);toast(`Created: ${name}`,'ok');loadRemote()}
  catch(e){toast(e.message,'err')}
}
async function deleteOne(path,name){
  const ok = await styledConfirm(t('delete_file'), t('delete_confirm',{name}));
  if(!ok)return;
  try{const r=await fetch(API+'/api/delete',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({path})});if(!r.ok)throw new Error((await r.json()).error);toast(`Deleted: ${name}`,'ok');loadRemote()}
  catch(e){toast(e.message,'err')}
}
async function deleteSelected(){
  const sel=[...remoteSelected].map(i=>remoteFiles[i]);if(!sel.length)return;
  const ok = await styledConfirm(t('delete_file'), t('delete_multi',{count:sel.length}));
  if(!ok)return;
  for(const f of sel){const p=remotePath.replace(/\/+$/,'')+'/'+f.name;try{await fetch(API+'/api/delete',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({path:p})})}catch(e){}}
  toast(`Deleted ${sel.length} item(s)`,'ok');loadRemote();
}
async function renameOne(path,name){
  const n = await styledPrompt(t('rename_title'), t('enter_name'), name);
  if(!n||n===name)return;
  const dir=path.substring(0,path.length-name.length);
  try{const r=await fetch(API+'/api/rename',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({old:path,new:dir+n})});if(!r.ok)throw new Error((await r.json()).error);toast(`Renamed: ${name} → ${n}`,'ok');loadRemote()}
  catch(e){toast(e.message,'err')}
}
function renameSelected(){const sel=[...remoteSelected];if(sel.length!==1){status('Select one file to rename');return}const f=remoteFiles[sel[0]];renameOne(remotePath.replace(/\/+$/,'')+'/'+f.name,f.name)}

// === CHMOD ===
function openChmod(path,name,perms) {
  chmodTarget = path;
  document.getElementById('chmodFile').textContent = name;
  // Parse perms string like rwxr-xr-x to octal
  let mode = 0;
  if(perms && perms.length >= 9) {
    const map = [[256,128,64],[32,16,8],[4,2,1]];
    for(let i=0;i<9;i++) if(perms[i]!=='-') mode |= map[Math.floor(i/3)][i%3];
  } else { mode = 0o755; }
  // Set checkboxes
  document.querySelectorAll('.chmod-cb').forEach(cb => {
    cb.checked = !!(mode & parseInt(cb.dataset.bit));
  });
  updateChmod();
  document.getElementById('chmodModal').classList.remove('hidden');
}
function closeChmod(){document.getElementById('chmodModal').classList.add('hidden')}
function updateChmod(){
  let mode=0;
  document.querySelectorAll('.chmod-cb').forEach(cb=>{if(cb.checked)mode|=parseInt(cb.dataset.bit)});
  const octal = mode.toString(8).padStart(3,'0');
  document.getElementById('chmodPreview').textContent = octal;
  document.getElementById('chmodInput').value = octal;
}
function chmodFromInput(){
  const v = document.getElementById('chmodInput').value;
  const m = parseInt(v,8);
  if(isNaN(m))return;
  document.querySelectorAll('.chmod-cb').forEach(cb=>{cb.checked=!!(m&parseInt(cb.dataset.bit))});
  document.getElementById('chmodPreview').textContent = m.toString(8).padStart(3,'0');
}
async function applyChmod(){
  const mode = document.getElementById('chmodInput').value;
  try {
    const r = await fetch(API+'/api/chmod',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({path:chmodTarget,mode})});
    if(!r.ok) throw new Error((await r.json()).error);
    toast(`Permissions set to ${mode}`,'ok'); closeChmod(); loadRemote();
  } catch(e){toast(e.message,'err')}
}

// === UTILS ===
function fileEmoji(name){
  const ext=name.split('.').pop().toLowerCase();
  if(['jpg','jpeg','png','gif','svg','webp'].includes(ext))return'🖼';
  if(['mp4','avi','mkv','mov'].includes(ext))return'🎬';
  if(['mp3','wav','flac','ogg'].includes(ext))return'🎵';
  if(ext==='pdf')return'📕';
  if(['zip','rar','7z','tar','gz'].includes(ext))return'📦';
  if(['py','js','html','css','php','java','c'].includes(ext))return'💻';
  if(['doc','docx','txt','md'].includes(ext))return'📝';
  return'📄';
}
function fmtSize(b){if(b<=0)return'';if(b<1024)return b+' B';if(b<1048576)return(b/1024).toFixed(1)+' KB';if(b<1073741824)return(b/1048576).toFixed(1)+' MB';return(b/1073741824).toFixed(2)+' GB'}
function esc(s){const d=document.createElement('div');d.textContent=s;return d.innerHTML}
function status(msg){document.getElementById('statusText').textContent=msg}
function showXfer(msg){document.getElementById('xferBar').style.display='flex';document.getElementById('xferText').textContent=msg;var f=document.getElementById('xferFill');if(f)f.style.width='0%'}
function hideXfer(){document.getElementById('xferBar').style.display='none';var f=document.getElementById('xferFill');if(f)f.style.width='0%'}
function toast(msg,type='ok'){const el=document.createElement('div');el.className=`toast ${type}`;el.textContent=msg;document.getElementById('toasts').appendChild(el);setTimeout(()=>{el.style.opacity='0';el.style.transform='translateX(20px)';el.style.transition='all .3s';setTimeout(()=>el.remove(),300)},4000)}

// === CONTEXT MENUS ===
let ctxFile = null;

function hideAllCtx() {
  document.getElementById('localCtx').classList.add('hidden');
  document.getElementById('remoteCtx').classList.add('hidden');
}

function showCtx(menuId, x, y) {
  hideAllCtx();
  const menu = document.getElementById(menuId);
  menu.classList.remove('hidden');
  const mw = menu.offsetWidth || 200, mh = menu.offsetHeight || 300;
  menu.style.left = Math.min(x, window.innerWidth - mw - 8) + 'px';
  menu.style.top = Math.min(y, window.innerHeight - mh - 8) + 'px';
}

// Close menus when clicking anywhere OUTSIDE them
document.addEventListener('click', e => {
  if (!e.target.closest('.ctx-menu') && !e.target.closest('.fa-btn')) {
    hideAllCtx();
  }
});

function handleRightClick(pane, e) {
  e.preventDefault(); e.stopPropagation();
  const files = pane === 'local' ? localFiles : remoteFiles;
  const selected = pane === 'local' ? localSelected : remoteSelected;
  const renderFn = pane === 'local' ? renderLocal : renderRemote;
  const row = e.target.closest('.file-row');
  if (row) {
    const idx = parseInt(row.dataset.idx);
    if (!selected.has(idx)) { selected.clear(); selected.add(idx); renderFn(); }
    const f = files[idx];
    if (pane === 'local') {
      ctxFile = { name: f.name, path: f.full_path, is_dir: f.is_dir, idx, pane };
    } else {
      const fullPath = remotePath.replace(/\/+$/, '') + '/' + f.name;
      ctxFile = { name: f.name, path: fullPath, is_dir: f.is_dir, idx, pane, perms: f.perms || '' };
    }
  } else {
    ctxFile = { name: '', path: pane === 'local' ? localPath : remotePath, is_dir: true, idx: -1, pane };
  }
  showCtx(pane + 'Ctx', e.clientX, e.clientY);
}

['contextmenu', 'mouseup'].forEach(evt => {
  document.getElementById('localBody').addEventListener(evt, e => {
    if (evt === 'mouseup' && e.button !== 2) return;
    handleRightClick('local', e);
  });
  document.getElementById('remoteBody').addEventListener(evt, e => {
    if (evt === 'mouseup' && e.button !== 2) return;
    handleRightClick('remote', e);
  });
});
document.addEventListener('contextmenu', e => e.preventDefault());

// ⋮ button on each remote row
function showRowMenu(event, path, name, isDir, perms) {
  event.preventDefault(); event.stopPropagation();
  let idx = remoteFiles.findIndex(f => f.name === name);
  ctxFile = { name, path, is_dir: isDir, idx, pane: 'remote', perms: perms || '' };
  showCtx('remoteCtx', event.clientX, event.clientY);
}

// === MENU ITEM CLICK HANDLERS ===
function menuAction(action) {
  hideAllCtx();
  const actions = {
    ctxPreview() { if(ctxFile&&ctxFile.name&&!ctxFile.is_dir) openPreview(ctxFile.path,ctxFile.name); },
    ctxUploadSelected() { uploadSelected(); },
    ctxOpenLocal() { if (ctxFile && ctxFile.is_dir) loadLocal(ctxFile.path); },
    async ctxNewLocalFolder() {
      var name = await styledPrompt(t('new_folder_title')||'New Folder', t('enter_folder')||'Folder name:', '');
      if(!name) return;
      try {
        var r = await fetch(API+'/api/local/mkdir',{method:'POST',headers:{'Content-Type':'application/json'},
          body:JSON.stringify({parent:localPath,name:name})});
        var d = await r.json(); if(!r.ok) throw new Error(d.error);
        toast('Created: '+name,'ok'); loadLocal();
      } catch(e){toast(e.message,'err')}
    },
    async ctxRenameLocal() {
      if(!ctxFile||!ctxFile.name) return;
      var n = await styledPrompt(t('rename_title')||'Rename', t('enter_name')||'New name:', ctxFile.name);
      if(!n||n===ctxFile.name) return;
      try {
        var r = await fetch(API+'/api/local/rename',{method:'POST',headers:{'Content-Type':'application/json'},
          body:JSON.stringify({old:ctxFile.path,new_name:n})});
        var d = await r.json(); if(!r.ok) throw new Error(d.error);
        toast('Renamed: '+ctxFile.name+' → '+n,'ok'); loadLocal();
      } catch(e){toast(e.message,'err')}
    },
    async ctxDeleteLocal() {
      if(!ctxFile||!ctxFile.name) return;
      var ok = await styledConfirm(t('delete_file')||'Delete', t('delete_confirm',{name:ctxFile.name})||('Delete '+ctxFile.name+'?'));
      if(!ok) return;
      try {
        var r = await fetch(API+'/api/local/delete',{method:'POST',headers:{'Content-Type':'application/json'},
          body:JSON.stringify({path:ctxFile.path})});
        var d = await r.json(); if(!r.ok) throw new Error(d.error);
        toast('Deleted: '+ctxFile.name,'ok'); loadLocal();
      } catch(e){toast(e.message,'err')}
    },
    ctxCopyPathLocal() { if(ctxFile) navigator.clipboard.writeText(ctxFile.path||localPath).then(()=>toast('Path copied','ok')).catch(()=>{}); },
    ctxDownload() {
      if (!ctxFile || ctxFile.is_dir || !ctxFile.name) return;
      fetch(API+'/api/download?path='+encodeURIComponent(ctxFile.path),{headers:{'X-Session-Token':SESSION_TOKEN}})
        .then(r=>{if(!r.ok)throw new Error('Download failed');return r.blob()})
        .then(blob=>{const u=URL.createObjectURL(blob);const a=document.createElement('a');a.href=u;a.download=ctxFile.name;a.click();URL.revokeObjectURL(u)})
        .catch(e=>toast(e.message,'err'));
    },
    ctxDownloadSelected() {
      if (ctxFile && ctxFile.idx >= 0) { remoteSelected.clear(); remoteSelected.add(ctxFile.idx); renderRemote(); }
      downloadSelected();
    },
    ctxRename() { if(ctxFile&&ctxFile.name) renameOne(ctxFile.path,ctxFile.name); },
    ctxChmod() { if(ctxFile&&ctxFile.name) openChmod(ctxFile.path,ctxFile.name,ctxFile.perms||''); },
    ctxCopyPathRemote() { if(ctxFile) navigator.clipboard.writeText(ctxFile.path||remotePath).then(()=>toast('Path copied','ok')).catch(()=>{}); },
    ctxNewFolder() { newFolder(); },
    async ctxNewFile() {
      var name = await styledPrompt('New File', 'File name:', '.htaccess');
      if(!name) return;
      var filePath = remotePath.replace(/\/$/,'') + '/' + name;
      try {
        var r = await fetch(API+'/api/save',{method:'POST',headers:{'Content-Type':'application/json'},
          body:JSON.stringify({path:filePath, content:'', expected_hash:''})});
        var d = await r.json(); if(!r.ok) throw new Error(d.error);
        toast('Created: '+name,'ok'); loadRemote();
      } catch(e){toast(e.message,'err')}
    },
    ctxZip() { openZipDialog(); },
    ctxUnzip() { if(ctxFile&&ctxFile.name&&ctxFile.name.endsWith('.zip')) doUnzip(ctxFile.path); else toast('Select a .zip file first','err'); },
    ctxRefresh() { loadRemote(); },
    ctxDelete() { if(ctxFile&&ctxFile.name) deleteOne(ctxFile.path,ctxFile.name); else deleteSelected(); },
  };
  if (actions[action]) { actions[action](); return; }
  // Menu bar actions
  switch(action) {
    case 'connect': window.location.reload(); break;
    case 'disconnect': doDisconnect(); break;
    case 'vault': openVault(); break;
    case 'close': closePreview(); break;
    case 'edit': toggleEdit(); break;
    case 'save': saveFile(); break;
    case 'saveas': saveAsCopy(); break;
    case 'checkpoint': createCheckpoint(); break;
    case 'diff': showDiffBeforeSave(); break;
    case 'search': openSearch(); break;
    case 'dashboard': openDashboard(); break;
    case 'backup': runBackup(); break;
    case 'seo': runSeoAudit(); break;
    case 'deadcode': runFindUnused(); break;
    case 'optimize': runOptimize(); break;
    case 'register': openProModal(); break;
    case 'togglesound': toggleZoppySound(); break;
    case 'whozoppy': showZoppyStory(); break;
    case 'zoppymaze': launchZoppyMaze(); break;
    case 'about':
      styledAlert('About Aivelo FTP Vault',
        'Aivelo FTP Vault v' + APP_VER + '\n\n' +
        'Secure FTP / FTPS / SFTP file transfer client\n' +
        'License: ' + (isPro ? '✓ Pro (active)' : 'Free edition') + '\n\n' +
        '© 2026 Aivelo · martijnbenders.nl');
      break;
  }
}
// === INTERNATIONALIZATION (i18n) ===
const APP_VER = '""" + APP_VERSION + r"""';
const ZOPPY_SND = '""" + ZOPPY_SND + r"""';
const SOCK_SPRITE = '""" + SOCK_SPRITE + r"""';
const ZOPPY_GAME = '""" + ZOPPY_GAME + r"""';
const ZOPPY_ATK = '""" + ZOPPY_ATK + r"""';
const ZOPPY_INTRO = '""" + ZOPPY_INTRO + r"""';
const LANG_FLAGS = {en:'🇬🇧',nl:'🇳🇱',es:'🇪🇸',zh:'🇨🇳',hi:'🇮🇳',ar:'🇸🇦',pt:'🇧🇷',fr:'🇫🇷',ja:'🇯🇵',ru:'🇷🇺',de:'🇩🇪'};
let _lang = 'en';
let _t = {};
let _rtl = false;

function t(key, params) {
  let s = _t[key] || key;
  if (params) Object.entries(params).forEach(([k,v]) => { s = s.replace('{'+k+'}', v); });
  return s;
}

async function loadTranslations() {
  try {
    const r = await fetch(API+'/api/translations');
    const d = await r.json();
    _lang = d.lang;
    _t = d.t;
    _rtl = d.rtl;
    applyTranslations();
    if (_rtl) document.documentElement.setAttribute('dir', 'rtl');
    else document.documentElement.removeAttribute('dir');
  } catch(e) {}
}

function applyTranslations() {
  // Apply translations to all elements with data-t attribute
  document.querySelectorAll('[data-t]').forEach(el => {
    const key = el.dataset.t;
    if (_t[key]) {
      if (el.tagName === 'INPUT' && el.placeholder !== undefined && el.dataset.tAttr === 'placeholder') {
        el.placeholder = _t[key];
      } else {
        el.textContent = _t[key];
      }
    }
  });
}

let _selectedLang = 'en';

async function checkLanguage() {
  try {
    const r = await fetch(API+'/api/lang');
    const d = await r.json();
    _selectedLang = d.lang || 'en';
    if (d.needs_select) {
      showLangPicker(true);
    } else {
      await loadTranslations();
    }
  } catch(e) {}
}

function showLangPicker(firstTime) {
  const grid = document.getElementById('langGrid');
  const langs = Object.entries(LANG_FLAGS);
  const langNames = {en:'English',nl:'Nederlands',es:'Español',zh:'中文',hi:'हिन्दी',ar:'العربية',pt:'Português',fr:'Français',ja:'日本語',ru:'Русский',de:'Deutsch'};
  grid.innerHTML = langs.map(([code,flag]) =>
    `<div class="lang-opt ${code===_selectedLang?'active':''}" onclick="selectLang('${code}',this)">
      <span class="lang-flag">${flag}</span>
      <span class="lang-label">${langNames[code]}</span>
    </div>`
  ).join('');
  document.getElementById('langOverlay').classList.remove('hidden');
}

function openLangPicker() { showLangPicker(false); }
function selectLang(code, el) {
  _selectedLang = code;
  document.querySelectorAll('.lang-opt').forEach(o => o.classList.remove('active'));
  el.classList.add('active');
}

async function confirmLang() {
  try {
    await fetch(API+'/api/lang/set', {
      method:'POST', headers:{'Content-Type':'application/json'},
      body: JSON.stringify({lang: _selectedLang})
    });
    document.getElementById('langOverlay').classList.add('hidden');
    await loadTranslations();
    toast('✓ ' + (_t.lang_name || _selectedLang), 'ok');
  } catch(e) {}
}

// Initialize language on load
checkLanguage();

// === ZOPPY RPG ===
function showZoppyStory() {
  var html = '<div style="max-width:500px;padding:8px;font-size:13px;line-height:1.7;color:#333">' +
    '<div style="text-align:center;font-size:40px;margin-bottom:8px">🪓⛏️🔨</div>' +
    '<p style="font-style:italic;color:#8b6914;font-weight:600;margin-bottom:12px">"They said the files were safe. They were wrong."</p>' +
    '<p><b>Zoppy Ironvault</b> was once the master blacksmith of the Dwarven Datacenter deep beneath Mount Serverack. ' +
    'For three hundred years he forged the strongest file locks and the sharpest permission bits in all the realm.</p>' +
    '<p>Then came <b>The Great Corruption</b> — a mass chmod disaster that left every file on the mountain writeable by goblins. ' +
    'Zoppy alone stood against the horde, his hammer ringing through the caverns as he smashed malformed uploads ' +
    'and sealed broken permissions one by one.</p>' +
    '<p>Now retired from the deep mines, Zoppy guards <b>your</b> FTP vault with the same vigilance. ' +
    'Every file you upload, he inspects. Every transfer, he watches. And when danger threatens your server, ' +
    'you will hear his hammer ring once more.</p>' +
    '<p style="margin-top:12px;font-size:11px;color:#999;text-align:center">Zoppy has guarded this vault since v2.0. He likes ale, anvils, and properly minified CSS.</p>' +
    '</div>';
  showProResults('🪓 The Legend of Zoppy Ironvault', html);
}

function launchZoppyMaze() {
  var overlay = document.createElement('div');
  overlay.id = 'zoppyMazeOverlay';
  overlay.style.cssText = 'position:fixed;inset:0;background:rgba(0,0,0,.92);z-index:5000;display:flex;align-items:center;justify-content:center';

  var W = 640, H = 480, T = 32;
  var GRAVITY = 0.5, JUMP_FORCE = -11, MOVE_SPEED = 3.2, CLIMB_SPEED = 2.8, SOCK_SPEED = 1.0;
  var COLS = W/T, ROWS = H/T;

  var sockImg = null;
  if (typeof SOCK_SPRITE !== 'undefined' && SOCK_SPRITE) { sockImg = new window.Image(); sockImg.src = 'data:image/png;base64,' + SOCK_SPRITE; }
  var zoppyImg = null;
  if (typeof ZOPPY_GAME !== 'undefined' && ZOPPY_GAME) { zoppyImg = new window.Image(); zoppyImg.src = 'data:image/png;base64,' + ZOPPY_GAME; }
  var zoppyAtkImg = null;
  if (typeof ZOPPY_ATK !== 'undefined' && ZOPPY_ATK) { zoppyAtkImg = new window.Image(); zoppyAtkImg.src = 'data:image/png;base64,' + ZOPPY_ATK; }

  var levels = [
    { name: 'The Broken Mines', subtitle: 'Learn the basics. Smash through.', map: [
      '11111111111111111111','10000000000000000001','10000000000000000G01','100000000000001111S1',
      '10000000000000L00001','10000000011111L00001','10000000000000L00001','100000R0000000L00001',
      '10001111L00011111001','100000S0L00000000001','10000000L000S0000001','10001111111011111101',
      '10000000L00000000L01','1Z000000L00000000L01','11111111111111111111']},
    { name: 'Shaft of Permissions', subtitle: 'Climb. Time your jumps.', map: [
      '11111111111111111111','1G00000000000S000001','11111100000011111101','10000L00000000000L01',
      '10000L00S00000000L01','10000L001111100S0L01','100001000000L0001111','10000000000SL0000001',
      '10001111L00011110001','10000000L00000000001','1S00000LL000S0000001','11111001100011111001',
      '10000000L000000L0001','1Z000000L00S000L0001','11111111111111111111']},
    { name: 'The Corrupted Forge', subtitle: 'The corruption runs deep.', map: [
      '11111111111111111111','100000000000000RGR01','10000000000000111111','1S0000000000000L0001',
      '100111111RS00S0L0001','1000000L0000111S0001','10000S0L000000L00001','100111111100S0RL0001',
      '1000000L000011110001','100000SL00000S0L0001','100111111100000L0001','1000000L000011111001',
      '1000S00L00000000L001','1Z00L1111111001111S1','11111111111111111111']}
  ];

  var currentLevel=0,tiles,ladderTiles,socks,rocks,goalPos,startPos,z;
  var score=0,lives=3,gameOver=false,gameWon=false,frameCount=0,animId=null,keys={};
  var shakeTimer=0,hurtTimer=0,levelTransition=0,levelTransText='';
  var bossMode=false,boss=null,bossDefeated=false,particles=[];

  function loadLevel(idx) {
    var lv=(idx<levels.length)?levels[idx]:null;
    tiles=[];ladderTiles=[];socks=[];rocks=[];goalPos=null;startPos=null;
    bossMode=false;boss=null;bossDefeated=false;particles=[];
    if(!lv){
      bossMode=true;
      for(var r=0;r<ROWS;r++){tiles[r]=[];ladderTiles[r]=[];for(var c=0;c<COLS;c++){tiles[r][c]=0;ladderTiles[r][c]=false;}}
      for(var c=0;c<COLS;c++){tiles[0][c]=1;tiles[ROWS-1][c]=1;}
      for(var r=0;r<ROWS;r++){tiles[r][0]=1;tiles[r][COLS-1]=1;}
      for(var c=1;c<COLS-1;c++)tiles[ROWS-2][c]=1;
      for(var c=2;c<7;c++)tiles[ROWS-5][c]=1;
      for(var c=13;c<18;c++)tiles[ROWS-5][c]=1;
      for(var c=7;c<13;c++)tiles[ROWS-8][c]=1;
      ladderTiles[ROWS-4][7]=true;ladderTiles[ROWS-3][7]=true;
      ladderTiles[ROWS-4][12]=true;ladderTiles[ROWS-3][12]=true;
      ladderTiles[ROWS-7][9]=true;ladderTiles[ROWS-6][9]=true;
      ladderTiles[ROWS-7][10]=true;ladderTiles[ROWS-6][10]=true;
      for(var r2=0;r2<ROWS;r2++)for(var c2=0;c2<COLS;c2++)if(ladderTiles[r2][c2]&&r2>0)tiles[r2-1][c2]=0;
      startPos={x:10*T,y:(ROWS-2)*T-28};
      boss={x:W/2-48,y:T*2,w:96,h:80,hp:20,maxHp:20,vx:1.5,phase:0,hitFlash:0,mouthOpen:0,eyeGlow:0,tentacles:[],spawnTimer:90,dir:1};
      for(var t=0;t<4;t++)boss.tentacles.push({x:0,y:0,angle:t*Math.PI/2,speed:0.03+t*0.008,len:30});
      initZoppy(startPos.x,startPos.y);
      if(typeof zoppySoundEnabled!=='undefined'&&zoppySoundEnabled){try{var actx=new(window.AudioContext||window.webkitAudioContext)();var o=actx.createOscillator(),g=actx.createGain();o.type='sawtooth';o.frequency.setValueAtTime(80,actx.currentTime);o.frequency.linearRampToValueAtTime(40,actx.currentTime+1);g.gain.setValueAtTime(0.15,actx.currentTime);g.gain.exponentialRampToValueAtTime(0.001,actx.currentTime+1.2);o.connect(g);g.connect(actx.destination);o.start();o.stop(actx.currentTime+1.2);}catch(e){}}
      return;
    }
    var map=lv.map;
    for(var r=0;r<ROWS;r++){tiles[r]=[];ladderTiles[r]=[];for(var c=0;c<COLS;c++){
      var ch=map[r][c];tiles[r][c]=(ch==='1')?1:0;ladderTiles[r][c]=false;
      if(ch==='L')ladderTiles[r][c]=true;
      if(ch==='S')socks.push({x:c*T+4,y:r*T+4,w:T-8,h:T-8,vx:SOCK_SPEED*(Math.random()>.5?1:-1),alive:true,frame:0,animT:0,lastX:c*T+4});
      if(ch==='R')rocks.push({x:c*T,y:r*T,hp:3,maxHp:3});
      if(ch==='G')goalPos={x:c*T,y:r*T};
      if(ch==='Z')startPos={x:c*T,y:r*T};
    }}
    for(var r=0;r<ROWS;r++)for(var c=0;c<COLS;c++)if(ladderTiles[r][c]){tiles[r][c]=0;if(r>0)tiles[r-1][c]=0;}
    if(startPos)initZoppy(startPos.x,startPos.y);
  }

  function initZoppy(sx,sy){z={x:sx,y:sy,w:27,h:32,vx:0,vy:0,onGround:false,isClimbing:false,ladderSnapX:-1,facingR:true,attacking:false,atkTimer:0,state:'idle'};}
  function isSolid(px,py,pw,ph){var x1=Math.floor(px/T),y1=Math.floor(py/T),x2=Math.floor((px+pw-1)/T),y2=Math.floor((py+ph-1)/T);for(var r=y1;r<=y2;r++)for(var c=x1;c<=x2;c++){if(r<0||r>=ROWS||c<0||c>=COLS)return true;if(tiles[r][c]===1)return true;}for(var i=0;i<rocks.length;i++){var rk=rocks[i];if(rk.hp<=0)continue;if(px<rk.x+T&&px+pw>rk.x&&py<rk.y+T&&py+ph>rk.y)return true;}return false;}
  function overlaps(a,b){return a.x<b.x+b.w&&a.x+a.w>b.x&&a.y<b.y+b.h&&a.y+a.h>b.y;}
  function getLadderAt(px,py,pw,ph){var cx=px+pw/2;var col=Math.floor(cx/T);var ry1=Math.floor(py/T),ry2=Math.floor((py+ph-1)/T);for(var r=ry1;r<=ry2;r++){if(r>=0&&r<ROWS&&col>=0&&col<COLS&&ladderTiles[r]&&ladderTiles[r][col])return col*T+T/2;}return-1;}
  function isOnLadderTile(px,py,pw,ph){return getLadderAt(px,py,pw,ph)>=0;}
  function spawnParticles(x,y,color,count){for(var i=0;i<count;i++)particles.push({x:x,y:y,vx:(Math.random()-0.5)*4,vy:-Math.random()*3-1,life:20+Math.random()*15,color:color,size:2+Math.random()*3});}

  function hurtZoppy(){lives--;hurtTimer=60;z.state='hurt';spawnParticles(z.x+z.w/2,z.y+z.h/2,'#ff6666',6);if(lives<=0){gameOver=true;return;}if(startPos){z.x=startPos.x;z.y=startPos.y;}else if(bossMode){z.x=W/2-12;z.y=(ROWS-2)*T-z.h;}z.vy=0;z.isClimbing=false;}

  function update(){
    if(levelTransition>0){levelTransition--;if(levelTransition===0)loadLevel(currentLevel);return;}
    if(gameOver||gameWon)return;
    frameCount++;
    for(var i=particles.length-1;i>=0;i--){var p=particles[i];p.x+=p.vx;p.y+=p.vy;p.vy+=0.15;p.life--;if(p.life<=0)particles.splice(i,1);}
    if(hurtTimer>0)hurtTimer--;
    if(z.attacking){z.atkTimer--;if(z.atkTimer<=0)z.attacking=false;}
    var wL=keys.ArrowLeft||keys.a,wR=keys.ArrowRight||keys.d,wU=keys.ArrowUp||keys.w,wD=keys.ArrowDown||keys.s,wJ=keys[' '],wA=keys.x||keys.Enter;
    if(wA&&!z.attacking&&hurtTimer===0){z.attacking=true;z.atkTimer=14;z.state='attack';
      if(typeof zoppySoundEnabled!=='undefined'&&zoppySoundEnabled){try{var actx=new(window.AudioContext||window.webkitAudioContext)();var o=actx.createOscillator(),g=actx.createGain();o.type='square';o.frequency.setValueAtTime(600,actx.currentTime);o.frequency.exponentialRampToValueAtTime(150,actx.currentTime+0.08);g.gain.setValueAtTime(0.1,actx.currentTime);g.gain.exponentialRampToValueAtTime(0.001,actx.currentTime+0.1);o.connect(g);g.connect(actx.destination);o.start();o.stop(actx.currentTime+0.1);}catch(e){}}}
    var ladderCenter=getLadderAt(z.x,z.y,z.w,z.h);
    if(z.isClimbing){
      z.x=z.ladderSnapX-z.w/2;z.vx=0;z.vy=0;
      if(wU)z.vy=-CLIMB_SPEED;if(wD)z.vy=CLIMB_SPEED;
      z.y+=z.vy;
      if(z.vy<0&&!isOnLadderTile(z.x,z.y,z.w,z.h)){z.isClimbing=false;z.onGround=true;z.vy=0;}
      if(z.vy>0&&!isOnLadderTile(z.x,z.y,z.w,z.h)){z.isClimbing=false;}
      if(isSolid(z.x,z.y,z.w,z.h)){z.y-=z.vy;z.vy=0;}
      if(wJ&&!wU&&!wD){z.isClimbing=false;z.vy=JUMP_FORCE*0.7;}
      if(z.isClimbing)z.state='climb';
    }else{
      if(ladderCenter>=0&&(wU||wD)&&!z.attacking){z.isClimbing=true;z.ladderSnapX=ladderCenter;z.x=ladderCenter-z.w/2;z.vy=0;z.vx=0;}
      else{
        var moveX=0;if(wL){moveX=-MOVE_SPEED;z.facingR=false;}if(wR){moveX=MOVE_SPEED;z.facingR=true;}
        z.x+=moveX;if(isSolid(z.x,z.y,z.w,z.h))z.x-=moveX;
        z.vy+=GRAVITY;if((wU||wJ)&&z.onGround&&!z.isClimbing)z.vy=JUMP_FORCE;
        z.y+=z.vy;z.onGround=false;
        if(isSolid(z.x,z.y,z.w,z.h)){if(z.vy>0){z.y=Math.floor((z.y+z.h)/T)*T-z.h;z.onGround=true;}else{z.y=Math.ceil(z.y/T)*T;}z.vy=0;}
        if(!z.attacking){if(!z.onGround&&z.vy<-1)z.state='jump';else if(!z.onGround&&z.vy>1)z.state='fall';else if(Math.abs(moveX)>0)z.state='run';else z.state='idle';}
      }
    }
    if(z.x<0)z.x=0;if(z.x>W-z.w)z.x=W-z.w;
    if(z.attacking&&z.atkTimer>6){
      var ab={x:z.facingR?z.x+z.w:z.x-22,y:z.y-4,w:22,h:z.h+4};
      for(var i=0;i<socks.length;i++){if(socks[i].alive&&overlaps(ab,socks[i])){socks[i].alive=false;score+=100;spawnParticles(socks[i].x+socks[i].w/2,socks[i].y+socks[i].h/2,'#c03030',8);}}
      for(var i=0;i<rocks.length;i++){var rk=rocks[i];if(rk.hp<=0)continue;if(overlaps(ab,{x:rk.x,y:rk.y,w:T,h:T})){rk.hp--;shakeTimer=4;score+=25;spawnParticles(rk.x+T/2,rk.y+T/2,'#8a7060',5);if(rk.hp<=0)spawnParticles(rk.x+T/2,rk.y+T/2,'#6a5040',12);}}
      if(bossMode&&boss&&boss.hp>0&&overlaps(ab,{x:boss.x,y:boss.y,w:boss.w,h:boss.h})){boss.hp--;boss.hitFlash=10;shakeTimer=8;score+=50;spawnParticles(boss.x+boss.w/2,boss.y+boss.h/2,'#ff4444',10);if(boss.hp<=0){bossDefeated=true;score+=2000;gameWon=true;spawnParticles(boss.x+boss.w/2,boss.y+boss.h/2,'#d4af37',30);if(typeof zoppySoundEnabled!=='undefined'&&zoppySoundEnabled){playHammerSound();setTimeout(zoppySpeak,300);}}}}
    for(var i=0;i<socks.length;i++){var s=socks[i];if(!s.alive)continue;s.animT++;if(s.animT%8===0)s.frame=(s.frame+1)%4;var nx=s.x+s.vx;var hf=isSolid(nx,s.y+s.h+2,s.w,2);var hw=isSolid(nx,s.y,s.w,s.h);if(hw||!hf||nx<T||nx>W-T*2)s.vx=-s.vx;else s.x+=s.vx;if(frameCount%90===0){if(Math.abs(s.x-s.lastX)<5){s.vx=-s.vx;s.x+=s.vx*10;}s.lastX=s.x;}if(hurtTimer===0&&!z.attacking&&overlaps(z,s))hurtZoppy();}
    if(goalPos&&!bossMode&&overlaps(z,{x:goalPos.x,y:goalPos.y,w:T,h:T})){score+=500;spawnParticles(goalPos.x+T/2,goalPos.y+T/2,'#d4af37',15);currentLevel++;levelTransText=currentLevel<levels.length?levels[currentLevel].name:'BOSS: SOCKTHULHU';levelTransition=120;}
    if(bossMode&&boss&&boss.hp>0){
      boss.hitFlash=Math.max(0,boss.hitFlash-1);boss.mouthOpen=Math.sin(frameCount*0.1)*0.5+0.5;boss.eyeGlow=(Math.sin(frameCount*0.05)+1)/2;
      boss.phase=boss.hp<boss.maxHp*0.3?2:boss.hp<boss.maxHp*0.6?1:0;
      var spd=[1.5,2.5,3.5][boss.phase];boss.vx=boss.dir*spd;boss.x+=boss.vx;if(boss.x<T||boss.x>W-T-boss.w)boss.dir=-boss.dir;
      for(var t=0;t<boss.tentacles.length;t++){var tn=boss.tentacles[t];tn.angle+=tn.speed*(boss.phase+1);tn.len=30+boss.phase*12;tn.x=boss.x+boss.w/2+Math.cos(tn.angle)*tn.len;tn.y=boss.y+boss.h+Math.sin(tn.angle)*20+20;}
      boss.spawnTimer--;if(boss.spawnTimer<=0){boss.spawnTimer=[120,80,45][boss.phase];socks.push({x:boss.x+boss.w/2,y:boss.y+boss.h,w:24,h:24,vx:SOCK_SPEED*(Math.random()>.5?1:-1),alive:true,frame:0,animT:0,lastX:boss.x+boss.w/2});}
      if(hurtTimer===0&&overlaps(z,{x:boss.x,y:boss.y,w:boss.w,h:boss.h}))hurtZoppy();
      for(var t=0;t<boss.tentacles.length;t++){var tn=boss.tentacles[t];if(hurtTimer===0&&overlaps(z,{x:tn.x-8,y:tn.y-8,w:16,h:16})){hurtZoppy();break;}}}
    shakeTimer=Math.max(0,shakeTimer-1);
  }

  function render(){
    var c=document.getElementById('zoppyGameCanvas');if(!c)return;var ctx=c.getContext('2d');
    ctx.save();if(shakeTimer>0)ctx.translate(Math.random()*6-3,Math.random()*6-3);
    var bg=bossMode?['#1a0010','#200818']:currentLevel===0?['#0a0a1a','#1a1020']:currentLevel===1?['#0a0f1a','#101828']:['#1a0a0a','#201010'];
    var grd=ctx.createLinearGradient(0,0,0,H);grd.addColorStop(0,bg[0]);grd.addColorStop(1,bg[1]);ctx.fillStyle=grd;ctx.fillRect(0,0,W,H);
    for(var r=0;r<ROWS;r++)for(var co=0;co<COLS;co++){if(tiles[r][co]===1){var tx=co*T,ty=r*T;ctx.fillStyle='#4a3728';ctx.fillRect(tx,ty,T,T);ctx.fillStyle='#5c4633';ctx.fillRect(tx+2,ty+2,T-4,T-4);ctx.fillStyle='#6a5843';ctx.fillRect(tx+4,ty+4,8,6);ctx.fillRect(tx+18,ty+16,10,8);ctx.strokeStyle='#3a2718';ctx.lineWidth=1;ctx.beginPath();ctx.moveTo(tx+12,ty+2);ctx.lineTo(tx+16,ty+14);ctx.stroke();}}
    for(var i=0;i<rocks.length;i++){var rk=rocks[i];if(rk.hp<=0)continue;var rx=rk.x,ry=rk.y,pct=rk.hp/rk.maxHp;ctx.fillStyle=pct>0.6?'#7a6050':pct>0.3?'#6a5040':'#5a4030';ctx.beginPath();ctx.moveTo(rx+3,ry+T);ctx.lineTo(rx,ry+8);ctx.lineTo(rx+4,ry+2);ctx.lineTo(rx+14,ry);ctx.lineTo(rx+T-2,ry+3);ctx.lineTo(rx+T,ry+12);ctx.lineTo(rx+T-3,ry+T);ctx.closePath();ctx.fill();ctx.fillStyle=pct>0.6?'#8a7060':'#7a6050';ctx.beginPath();ctx.moveTo(rx+6,ry+4);ctx.lineTo(rx+14,ry+2);ctx.lineTo(rx+T-4,ry+8);ctx.lineTo(rx+T/2,ry+T/2);ctx.closePath();ctx.fill();ctx.strokeStyle='#2a1a10';ctx.lineWidth=2;if(pct<1){ctx.beginPath();ctx.moveTo(rx+6,ry+6);ctx.lineTo(rx+T/2,ry+T/2+2);ctx.lineTo(rx+T/2+4,ry+T-4);ctx.stroke();}if(pct<0.5){ctx.beginPath();ctx.moveTo(rx+T-6,ry+4);ctx.lineTo(rx+T/2-2,ry+T/2);ctx.stroke();}for(var d=0;d<rk.hp;d++){ctx.fillStyle='#d4af37';ctx.beginPath();ctx.arc(rx+10+d*7,ry+T-4,2,0,Math.PI*2);ctx.fill();}}
    for(var r=0;r<ROWS;r++)for(var co=0;co<COLS;co++){if(ladderTiles[r]&&ladderTiles[r][co]){var lx=co*T,ly=r*T;ctx.strokeStyle='#a0845c';ctx.lineWidth=3;ctx.beginPath();ctx.moveTo(lx+7,ly);ctx.lineTo(lx+7,ly+T);ctx.stroke();ctx.beginPath();ctx.moveTo(lx+T-7,ly);ctx.lineTo(lx+T-7,ly+T);ctx.stroke();ctx.lineWidth=2;for(var rr=0;rr<3;rr++){var ry2=ly+6+rr*10;ctx.beginPath();ctx.moveTo(lx+7,ry2);ctx.lineTo(lx+T-7,ry2);ctx.stroke();}ctx.strokeStyle='#c0a47c';ctx.lineWidth=1;ctx.beginPath();ctx.moveTo(lx+8,ly);ctx.lineTo(lx+8,ly+T);ctx.stroke();}}
    if(goalPos&&!bossMode){var gx=goalPos.x,gy=goalPos.y;var glow=ctx.createRadialGradient(gx+T/2,gy+T/2,4,gx+T/2,gy+T/2,28);glow.addColorStop(0,'rgba(212,175,55,.5)');glow.addColorStop(1,'rgba(212,175,55,0)');ctx.fillStyle=glow;ctx.fillRect(gx-12,gy-12,T+24,T+24);ctx.fillStyle='#d4af37';ctx.fillRect(gx+6,gy+2,20,26);ctx.fillStyle='#f0d060';ctx.fillRect(gx+8,gy+4,16,22);ctx.fillStyle='#d4af37';ctx.font='bold 8px monospace';ctx.textAlign='center';ctx.fillText('FILE',gx+T/2,gy+18);if(frameCount%20<10){ctx.fillStyle='#fff';ctx.fillRect(gx+22,gy+2,3,3);}}
    for(var i=0;i<socks.length;i++){var s=socks[i];if(!s.alive)continue;if(sockImg&&sockImg.complete){var sfW=51,sfH=28,flipX=s.vx<0;ctx.save();if(flipX){ctx.translate(s.x+s.w,s.y);ctx.scale(-1,1);ctx.drawImage(sockImg,s.frame*sfW,0,sfW,sfH,0,0,s.w,s.h);}else ctx.drawImage(sockImg,s.frame*sfW,0,sfW,sfH,s.x,s.y,s.w,s.h);ctx.restore();}else{ctx.fillStyle='#5a6a80';ctx.fillRect(s.x,s.y+4,s.w,s.h-4);ctx.fillStyle='#c03030';ctx.fillRect(s.x,s.y,s.w,6);}}
    if(bossMode&&boss&&boss.hp>0){var b=boss,bf=b.hitFlash>0&&b.hitFlash%2===0;ctx.fillStyle='rgba(0,0,0,.3)';ctx.beginPath();ctx.ellipse(b.x+b.w/2,b.y+b.h+4,b.w/2,8,0,0,Math.PI*2);ctx.fill();for(var t=0;t<b.tentacles.length;t++){var tn=b.tentacles[t];ctx.strokeStyle=bf?'#fff':'#4a5a70';ctx.lineWidth=6;ctx.beginPath();ctx.moveTo(b.x+b.w/2,b.y+b.h);ctx.quadraticCurveTo(b.x+b.w/2+(tn.x-b.x-b.w/2)*0.5,b.y+b.h+(tn.y-b.y-b.h)*0.3,tn.x,tn.y);ctx.stroke();ctx.fillStyle=bf?'#fff':'#c03030';ctx.beginPath();ctx.arc(tn.x,tn.y,6,0,Math.PI*2);ctx.fill();}ctx.fillStyle=bf?'#fff':'#3a4a60';ctx.beginPath();ctx.ellipse(b.x+b.w/2,b.y+b.h/2,b.w/2,b.h/2,0,0,Math.PI*2);ctx.fill();ctx.strokeStyle=bf?'#ddd':'#2a3a50';ctx.lineWidth=2;for(var rr=0;rr<6;rr++){ctx.beginPath();ctx.moveTo(b.x+10,b.y+15+rr*10);ctx.lineTo(b.x+b.w-10,b.y+15+rr*10);ctx.stroke();}ctx.fillStyle=bf?'#faa':'#c03030';ctx.fillRect(b.x+8,b.y+4,b.w-16,10);var mh=12+b.mouthOpen*20;ctx.fillStyle='#200008';ctx.beginPath();ctx.ellipse(b.x+b.w/2,b.y+b.h*0.55,b.w*0.35,mh,0,0,Math.PI*2);ctx.fill();ctx.fillStyle='#fff';for(var tt=0;tt<8;tt++){var ttx=b.x+b.w*0.25+tt*(b.w*0.5/8);ctx.beginPath();ctx.moveTo(ttx,b.y+b.h*0.45);ctx.lineTo(ttx+4,b.y+b.h*0.45+8);ctx.lineTo(ttx+8,b.y+b.h*0.45);ctx.fill();}for(var ei=0;ei<3;ei++){var ex=b.x+b.w*0.2+ei*(b.w*0.3),ey=b.y+20;ctx.fillStyle='rgba(255,'+Math.floor(50+b.eyeGlow*100)+',0,'+(.3+b.eyeGlow*.4)+')';ctx.beginPath();ctx.arc(ex,ey,10,0,Math.PI*2);ctx.fill();ctx.fillStyle=bf?'#faa':'#ff4444';ctx.beginPath();ctx.arc(ex,ey,7,0,Math.PI*2);ctx.fill();var dx2=z.x-ex,dy2=z.y-ey,dist=Math.sqrt(dx2*dx2+dy2*dy2)||1;ctx.fillStyle='#000';ctx.beginPath();ctx.arc(ex+dx2/dist*3,ey+dy2/dist*3,3,0,Math.PI*2);ctx.fill();}ctx.fillStyle='#333';ctx.fillRect(b.x,b.y-14,b.w,8);ctx.fillStyle=b.phase===2?'#ff2222':b.phase===1?'#ff8800':'#44cc44';ctx.fillRect(b.x+1,b.y-13,Math.max(0,(b.w-2)*b.hp/b.maxHp),6);ctx.fillStyle='#fff';ctx.font='bold 9px monospace';ctx.textAlign='center';ctx.fillText('SOCKTHULHU',b.x+b.w/2,b.y-17);}
    for(var i=0;i<particles.length;i++){var p=particles[i];ctx.globalAlpha=p.life/35;ctx.fillStyle=p.color;ctx.fillRect(p.x,p.y,p.size,p.size);}ctx.globalAlpha=1;
    if(z){var zx=Math.round(z.x),zy=Math.round(z.y);var flash=hurtTimer>0&&hurtTimer%4<2;if(!flash){if(z.attacking&&zoppyAtkImg&&zoppyAtkImg.complete){var atkFW=51,atkFH=32,atkFrame=Math.min(5,Math.floor((14-z.atkTimer)/14*6));ctx.save();if(!z.facingR){ctx.translate(zx+atkFW,zy);ctx.scale(-1,1);ctx.drawImage(zoppyAtkImg,atkFrame*atkFW,0,atkFW,atkFH,0,0,atkFW,atkFH);}else{ctx.drawImage(zoppyAtkImg,atkFrame*atkFW,0,atkFW,atkFH,zx-12,zy,atkFW,atkFH);}ctx.restore();if(z.atkTimer>8){ctx.fillStyle='rgba(255,255,200,.4)';var fx=z.facingR?zx+atkFW-16:zx-10;ctx.fillRect(fx,zy,16,16);}}else if(zoppyImg&&zoppyImg.complete){ctx.save();if(!z.facingR){ctx.translate(zx+z.w,zy);ctx.scale(-1,1);ctx.drawImage(zoppyImg,0,0,z.w,z.h);}else{ctx.drawImage(zoppyImg,zx,zy,z.w,z.h);}ctx.restore();}else{ctx.fillStyle='#8B6F5E';ctx.fillRect(zx+4,zy+8,16,14);ctx.fillStyle='#d4a574';ctx.fillRect(zx+6,zy,12,10);ctx.fillStyle='#888';ctx.fillRect(zx+5,zy-2,14,4);}}}
    ctx.fillStyle='rgba(0,0,0,.6)';ctx.fillRect(0,0,W,22);ctx.font='bold 12px monospace';ctx.textAlign='left';ctx.fillStyle='#d4af37';ctx.fillText('SCORE: '+score,8,15);ctx.fillStyle='#e06060';var hearts='';for(var i=0;i<lives;i++)hearts+='\u2764 ';ctx.fillText(hearts,140,15);var lvN=bossMode?'SOCKTHULHU':(currentLevel<levels.length?levels[currentLevel].name:'');ctx.fillStyle='#aaa';ctx.textAlign='center';ctx.fillText(lvN,W/2,15);ctx.fillStyle='#888';ctx.textAlign='right';ctx.font='11px monospace';ctx.fillText('X=SMASH  \u2190\u2191\u2192\u2193  SPACE=JUMP',W-8,15);
    if(levelTransition>0){var alpha=levelTransition>80?(120-levelTransition)/40:levelTransition>40?1:levelTransition/40;ctx.fillStyle='rgba(0,0,0,'+alpha+')';ctx.fillRect(0,0,W,H);if(alpha>0.5){ctx.fillStyle='#d4af37';ctx.font='bold 28px monospace';ctx.textAlign='center';ctx.fillText(levelTransText,W/2,H/2-10);var sub=currentLevel<levels.length?levels[currentLevel].subtitle:'From the laundry of corruption, he rises.';ctx.fillStyle='#aaa';ctx.font='14px monospace';ctx.fillText(sub,W/2,H/2+20);}}
    if(gameOver){ctx.fillStyle='rgba(0,0,0,.8)';ctx.fillRect(0,0,W,H);ctx.fillStyle='#e04040';ctx.font='bold 32px monospace';ctx.textAlign='center';ctx.fillText('GAME OVER',W/2,H/2-20);ctx.fillStyle='#ccc';ctx.font='16px monospace';ctx.fillText('Score: '+score,W/2,H/2+15);ctx.fillText('Press R to retry',W/2,H/2+40);}
    if(gameWon){ctx.fillStyle='rgba(0,0,0,.8)';ctx.fillRect(0,0,W,H);ctx.fillStyle='#d4af37';ctx.font='bold 24px monospace';ctx.textAlign='center';ctx.fillText('\u2692 SOCKTHULHU DEFEATED! \u2692',W/2,H/2-20);ctx.fillStyle='#ccc';ctx.font='16px monospace';ctx.fillText('Final Score: '+score,W/2,H/2+15);ctx.fillText('Press R or Escape',W/2,H/2+40);}
    ctx.restore();
  }

  function gameLoop(){update();render();animId=requestAnimationFrame(gameLoop);}
  function resetGame(){currentLevel=0;score=0;lives=3;gameOver=false;gameWon=false;frameCount=0;shakeTimer=0;hurtTimer=0;levelTransition=0;loadLevel(0);}
  function onKey(e){if(e.key==='Escape'){closeGame();return;}if((e.key==='r'||e.key==='R')&&(gameOver||gameWon)){resetGame();return;}keys[e.key]=true;e.preventDefault();}
  function onKeyUp(e){keys[e.key]=false;}
  function closeGame(){if(animId)cancelAnimationFrame(animId);document.removeEventListener('keydown',onKey);document.removeEventListener('keyup',onKeyUp);var el=document.getElementById('zoppyMazeOverlay');if(el)el.remove();}

  overlay.innerHTML='<div style="position:relative;background:#0a0a0f;border-radius:12px;padding:12px;box-shadow:0 8px 32px rgba(0,0,0,.6)"><div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:8px"><span style="color:#d4af37;font-weight:700;font-size:14px">\u2692 Zoppy vs The Sock Monsters</span><button onclick="document.dispatchEvent(new KeyboardEvent(\'keydown\',{key:\'Escape\'}))" style="background:none;border:none;color:#999;font-size:20px;cursor:pointer">\u2715</button></div><canvas id="zoppyGameCanvas" width="'+W+'" height="'+H+'" style="display:block;border-radius:6px;background:#0a0a1a"></canvas></div>';
  document.body.appendChild(overlay);document.addEventListener('keydown',onKey);document.addEventListener('keyup',onKeyUp);
  loadLevel(0);levelTransText=levels[0].name;levelTransition=120;gameLoop();
}



// === ZOPPY INTRO SOUND ===
setTimeout(function() {
  if (typeof zoppySoundEnabled !== 'undefined' && zoppySoundEnabled && ZOPPY_INTRO) {
    try { var a = new Audio('data:audio/mp3;base64,' + ZOPPY_INTRO); a.volume = 0.7; a.play(); } catch(e) {}
  }
}, 4000);

// === MENU BAR ===
(function initMenuBar() {
  var openMenu = null;
  document.querySelectorAll('.menubar-item').forEach(function(item) {
    item.addEventListener('mousedown', function(e) {
      e.stopPropagation();
      if (item.classList.contains('open')) {
        item.classList.remove('open');
        openMenu = null;
      } else {
        if (openMenu) openMenu.classList.remove('open');
        item.classList.add('open');
        openMenu = item;
      }
    });
    item.addEventListener('mouseenter', function() {
      if (openMenu && openMenu !== item) {
        openMenu.classList.remove('open');
        item.classList.add('open');
        openMenu = item;
      }
    });
  });
  document.addEventListener('mousedown', function() {
    if (openMenu) { openMenu.classList.remove('open'); openMenu = null; }
  });
  document.querySelectorAll('.menu-dropdown').forEach(function(dd) {
    dd.addEventListener('mousedown', function(e) { e.stopPropagation(); });
  });
  document.querySelectorAll('.menu-item').forEach(function(mi) {
    mi.addEventListener('click', function() {
      if (openMenu) { openMenu.classList.remove('open'); openMenu = null; }
    });
  });
})();

function buildLangMenu() {
  var list = document.getElementById('menuLangList');
  if (!list) return;
  var html = '';
  Object.entries(LANG_FLAGS).forEach(function(entry) {
    var code = entry[0], flag = entry[1];
    var names = {en:'English',nl:'Nederlands',es:'Español',zh:'中文',hi:'हिन्दी',ar:'العربية',pt:'Português',fr:'Français',ja:'日本語',ru:'Русский',de:'Deutsch'};
    var check = (code === _lang) ? '✓' : '';
    html += '<div class="menu-item" onclick="menuSetLang(\'' + code + '\')">' +
      '<span class="lang-check">' + check + '</span> ' + flag + ' ' + (names[code]||code) + '</div>';
  });
  list.innerHTML = html;
}

async function menuSetLang(code) {
  try {
    await fetch(API+'/api/lang/set', {
      method:'POST', headers:{'Content-Type':'application/json'},
      body: JSON.stringify({lang: code})
    });
    await loadTranslations();
    buildLangMenu();
    toast('✓ ' + (_t.lang_name || code), 'ok');
  } catch(e) {}
}


// Update pro status in menus
function updateMenuProState() {
  var items = ['menuBackup','menuSeo','menuDead','menuOptimize'];
  items.forEach(function(id) {
    var el = document.getElementById(id);
    if (el) {
      if (isPro) { el.classList.remove('disabled'); var tag = el.querySelector('.pro-tag'); if(tag) tag.remove(); }
      else { el.classList.add('disabled'); }
    }
  });
}

// Build lang menu after translations load
var _origLoadTranslations = loadTranslations;
loadTranslations = async function() {
  await _origLoadTranslations();
  buildLangMenu();
};

// === PRO LICENSE & NAG ===
let isPro = false;

async function checkLaunchInfo() {
  try {
    const r = await fetch(API+'/api/launch_info');
    const d = await r.json();
    isPro = d.is_pro;
    updateProUI();
    if (d.nag) {
      document.getElementById('nagCount').textContent = d.launch_count;
      document.getElementById('proNag').classList.remove('hidden');
    }
  } catch(e) {}
}

function updateProUI() {
  var btn = document.getElementById('topbarPro');
  if (btn && isPro) {
    btn.style.display = 'none';
  }
  var badge = document.getElementById('proBadgeMenu');
  if (badge) {
    if (isPro) {
      badge.setAttribute('style', 'margin-left:auto;color:#d4af37;font-weight:700;display:inline-flex !important');
    } else {
      badge.setAttribute('style', 'margin-left:auto;color:#d4af37;font-weight:700;display:none');
    }
  }
  if (isPro) {
    ['btnProBackup','btnProSeo','btnProDead','btnProMin'].forEach(function(id){
      var el = document.getElementById(id);
      if (el) el.style.display = '';
    });
  }
  updateMenuProState();
}

function closeNag() { document.getElementById('proNag').classList.add('hidden'); }

function openProModal() {
  document.getElementById('proOverlay').classList.remove('hidden');
  document.getElementById('proKeyError').classList.remove('visible');
  var inp = document.getElementById('proKeyInput');
  inp.value = '';
  if (isPro) {
    // Fetch and show the current key
    fetch(API+'/api/pro_key').then(r=>r.json()).then(d=>{
      if(d.key) inp.value = d.key;
    }).catch(()=>{});
  }
}
function closeProModal() { document.getElementById('proOverlay').classList.add('hidden'); }

async function activateKey() {
  const key = document.getElementById('proKeyInput').value.trim();
  const err = document.getElementById('proKeyError');
  err.classList.remove('visible');
  if (!key) { err.textContent = 'Enter your license key'; err.classList.add('visible'); return; }
  try {
    const r = await fetch(API+'/api/activate', {
      method:'POST', headers:{'Content-Type':'application/json'},
      body: JSON.stringify({key})
    });
    const d = await r.json();
    if (!r.ok) throw new Error(d.error);
    isPro = true;
    updateProUI();
    closeProModal();
    toast('🎉 ' + d.message, 'ok');
  } catch(e) {
    err.textContent = e.message;
    err.classList.add('visible');
  }
}

// Check launch info on app load
checkLaunchInfo();

// === STYLED DIALOGS (replaces prompt/confirm) ===
let _dialogResolveFn = null;

function styledPrompt(title, msg, defaultVal) {
  return new Promise(resolve => {
    _dialogResolveFn = resolve;
    document.getElementById('dialogTitle').textContent = title;
    document.getElementById('dialogMsg').textContent = msg;
    const inp = document.getElementById('dialogInput');
    inp.classList.remove('hidden'); inp.value = defaultVal || ''; inp.focus();
    document.getElementById('dialogOk').textContent = 'OK';
    document.getElementById('dialogOverlay').classList.remove('hidden');
    setTimeout(() => inp.focus(), 50);
  });
}

function styledConfirm(title, msg) {
  return new Promise(resolve => {
    _dialogResolveFn = resolve;
    document.getElementById('dialogTitle').textContent = title;
    document.getElementById('dialogMsg').textContent = msg;
    document.getElementById('dialogInput').classList.add('hidden');
    document.getElementById('dialogOk').textContent = 'Confirm';
    document.getElementById('dialogOverlay').classList.remove('hidden');
  });
}

function styledAlert(title, msg) {
  return new Promise(resolve => {
    _dialogResolveFn = resolve;
    document.getElementById('dialogTitle').textContent = title;
    document.getElementById('dialogMsg').textContent = msg;
    document.getElementById('dialogInput').classList.add('hidden');
    document.getElementById('dialogCancel').style.display = 'none';
    document.getElementById('dialogOk').textContent = 'OK';
    document.getElementById('dialogOverlay').classList.remove('hidden');
  }).finally(() => {
    document.getElementById('dialogCancel').style.display = '';
  });
}

function dialogResolve(val) {
  document.getElementById('dialogOverlay').classList.add('hidden');
  if (_dialogResolveFn) {
    const inp = document.getElementById('dialogInput');
    if (val === true && !inp.classList.contains('hidden')) {
      _dialogResolveFn(inp.value);
    } else {
      _dialogResolveFn(val);
    }
    _dialogResolveFn = null;
  }
}

// Enter key in dialog input triggers OK
document.getElementById('dialogInput').addEventListener('keydown', e => {
  if (e.key === 'Enter') dialogResolve(true);
  if (e.key === 'Escape') dialogResolve(null);
});

// === IMAGE GALLERY ===
async function openGallery() {
  document.getElementById('galleryOverlay').classList.remove('hidden');
  document.getElementById('galleryBody').innerHTML = '<div class="gallery-loading">⏳ Loading images from ' + esc(remotePath) + '...</div>';
  document.getElementById('galleryCount').textContent = '';
  try {
    const r = await fetch(API+'/api/gallery?path='+encodeURIComponent(remotePath));
    const d = await r.json();
    if (!r.ok) throw new Error(d.error);
    document.getElementById('galleryCount').textContent = d.count + ' images';
    if (!d.images.length) {
      document.getElementById('galleryBody').innerHTML = '<div class="gallery-loading">No images found in this folder</div>';
      return;
    }
    document.getElementById('galleryBody').innerHTML = '<div class="gallery-grid">' +
      d.images.map(img => `<div class="gallery-item" onclick="openLightbox('${img.mime}','${img.data.substring(0,50)}...','${esc(img.name)}',${img.size})" data-b64="${img.data}" data-mime="${img.mime}">
        <img src="data:${img.mime};base64,${img.data}" alt="${esc(img.name)}" loading="lazy">
        <div class="gallery-info">
          <div class="gallery-name">${esc(img.name)}</div>
          <div class="gallery-size">${fmtSize(img.size)}</div>
        </div>
      </div>`).join('') + '</div>';
    // Fix click handlers to pass full b64
    document.querySelectorAll('.gallery-item').forEach(el => {
      el.onclick = () => {
        const b64 = el.dataset.b64;
        const mime = el.dataset.mime;
        const name = el.querySelector('.gallery-name').textContent;
        const size = el.querySelector('.gallery-size').textContent;
        showLightbox(mime, b64, name, size);
      };
    });
  } catch(e) {
    document.getElementById('galleryBody').innerHTML = '<div class="gallery-loading">❌ ' + esc(e.message) + '</div>';
  }
}
function closeGallery() { document.getElementById('galleryOverlay').classList.add('hidden'); }

function showLightbox(mime, b64, name, size) {
  document.getElementById('lbImg').src = 'data:' + mime + ';base64,' + b64;
  document.getElementById('lbInfo').textContent = name + '  ·  ' + size;
  document.getElementById('lightbox').classList.remove('hidden');
}
function closeLightbox() { document.getElementById('lightbox').classList.add('hidden'); }

// === ENCRYPTED BOOKMARK VAULT ===
let vaultBookmarks = [];
let vaultUnlocked = false;

async function checkVaultStatus() {
  try {
    const r = await fetch(API+'/api/bookmarks/status');
    const d = await r.json();
    const badge = document.getElementById('vaultBadge');
    if (d.unlocked) {
      badge.className = 'vault-badge unlocked';
      badge.innerHTML = '🔓 Vault';
      vaultUnlocked = true;
    } else {
      badge.className = 'vault-badge locked';
      badge.innerHTML = '🔒 Vault';
      vaultUnlocked = false;
    }
  } catch(e) {}
}

function openVault() {
  document.getElementById('vaultOverlay').classList.remove('hidden');
  document.getElementById('vaultError').classList.remove('visible');
  document.getElementById('vaultPass').value = '';
  const desc = document.getElementById('vaultDesc');
  if (vaultUnlocked) {
    desc.textContent = 'Vault is unlocked. Your saved connections:';
    document.getElementById('vaultUnlockBtn').style.display = 'none';
    document.getElementById('vaultPass').parentElement.style.display = 'none';
    renderVaultList();
  } else {
    desc.textContent = 'Enter your master password to unlock saved connections.';
    document.getElementById('vaultUnlockBtn').style.display = '';
    document.getElementById('vaultPass').parentElement.style.display = '';
    document.getElementById('vaultList').innerHTML = '';
    setTimeout(() => document.getElementById('vaultPass').focus(), 50);
  }
}
function closeVault() { document.getElementById('vaultOverlay').classList.add('hidden'); }

async function unlockVault() {
  const pass = document.getElementById('vaultPass').value;
  const err = document.getElementById('vaultError');
  err.classList.remove('visible');
  if (!pass) { err.textContent = 'Enter a password'; err.classList.add('visible'); return; }
  try {
    const r = await fetch(API+'/api/bookmarks/unlock', {
      method:'POST', headers:{'Content-Type':'application/json'},
      body: JSON.stringify({password: pass})
    });
    const d = await r.json();
    if (!r.ok) throw new Error(d.error);
    vaultBookmarks = d.bookmarks || [];
    vaultUnlocked = true;
    checkVaultStatus();
    document.getElementById('vaultUnlockBtn').style.display = 'none';
    document.getElementById('vaultPass').parentElement.style.display = 'none';
    document.getElementById('vaultDesc').textContent = d.existed
      ? 'Vault unlocked! Your saved connections:'
      : 'New vault created! Save your first connection.';
    renderVaultList();
    toast('Vault unlocked', 'ok');
  } catch(e) {
    err.textContent = e.message; err.classList.add('visible');
  }
}

function renderVaultList() {
  const el = document.getElementById('vaultList');
  if (!vaultBookmarks.length) {
    el.innerHTML = '<div style="text-align:center;color:var(--gray-400);padding:12px;font-size:13px">No saved connections yet. Connect to a server and click "Save to Vault".</div>';
    return;
  }
  el.innerHTML = vaultBookmarks.map((b, i) => `<div style="display:flex;align-items:center;gap:8px;padding:8px 0;border-bottom:1px solid var(--gray-100)">
    <span style="font-size:14px">${b.proto === 'SFTP' ? '🔑' : '🌐'}</span>
    <div style="flex:1">
      <div style="font-family:var(--font-mono);font-size:12px;font-weight:600">${esc(b.user)}@${esc(b.host)}:${b.port}</div>
      <div style="font-size:11px;color:var(--gray-400)">${b.proto}</div>
    </div>
    <button class="btn btn-primary btn-sm" onmousedown="vaultConnect(${i})">Connect</button>
    <button class="btn btn-danger btn-sm" onmousedown="vaultDelete(${i})">✕</button>
  </div>`).join('');
}

async function saveToVault() {
  const host = document.getElementById('inHost').value.trim();
  const port = document.getElementById('inPort').value.trim();
  const user = document.getElementById('inUser').value.trim();
  const pass = document.getElementById('inPass').value;
  if (!host || !user) { toast(t('fill_host_user')||'Fill in host and username first', 'err'); return; }
  try {
    const r = await fetch(API+'/api/logins/save', {
      method:'POST', headers:{'Content-Type':'application/json'},
      body: JSON.stringify({host, port, username: user, password: pass, protocol: proto})
    });
    const d = await r.json();
    if (!r.ok) throw new Error(d.error);
    toast(t('connection_saved')||'Connection saved (encrypted)', 'ok');
    // Refresh the dropdown
    refreshSavedLogins();
  } catch(e) { toast('Save failed: ' + e.message, 'err'); }
}

function vaultConnect(idx) {
  const b = vaultBookmarks[idx];
  if (!b) return;
  document.getElementById('inHost').value = b.host;
  document.getElementById('inPort').value = b.port;
  document.getElementById('inUser').value = b.user;
  document.getElementById('inPass').value = b.password || '';
  document.querySelectorAll('.proto-btn').forEach(btn => btn.classList.toggle('active', btn.dataset.proto === b.proto));
  proto = b.proto;
  closeVault();
  doConnect();
}

async function vaultDelete(idx) {
  const ok = await styledConfirm(t('delete'), t('delete_bookmark'));
  if (!ok) return;
  vaultBookmarks.splice(idx, 1);
  try {
    await fetch(API+'/api/bookmarks/save', {
      method:'POST', headers:{'Content-Type':'application/json'},
      body: JSON.stringify({bookmarks: vaultBookmarks})
    });
    toast('Bookmark removed', 'ok');
    renderVaultList();
  } catch(e) { toast(e.message, 'err'); }
}

// === PREVIEW & EDITOR ===
let previewPath = '';
let previewOriginal = '';
let previewModified = false;
let editMode = false;
let snapshotTaken = false;

async function openPreview(path, name) {
  previewPath = path;
  previewModified = false;
  editMode = false;
  snapshotTaken = false;
  document.getElementById('previewTitle').textContent = name;
  document.getElementById('previewIcon').textContent = fileEmoji(name);
  document.getElementById('previewBody').innerHTML = '<div class="binary-info"><div class="binary-icon">⏳</div><div>Loading preview...</div></div>';
  document.getElementById('previewToolbar').style.display = 'none';
  document.getElementById('btnEdit').style.display = 'none';
  document.getElementById('btnSave').style.display = 'none';
  document.getElementById('btnDiff').style.display = 'none';
  document.getElementById('btnCheckpoint').style.display = 'none';
  document.getElementById('btnHistory').style.display = 'none';
  document.getElementById('btnRelated').style.display = 'none';
  document.getElementById('btnSaveAs').style.display = 'none';
  document.getElementById('editIndicator').textContent = '';
  document.getElementById('previewOverlay').classList.remove('hidden');

  try {
    const r = await fetch(API+'/api/preview?path='+encodeURIComponent(path));
    const d = await r.json();
    if (!r.ok) throw new Error(d.error);

    document.getElementById('previewMeta').textContent = fmtSize(d.size);

    if (d.type === 'image') {
      document.getElementById('previewBody').innerHTML = `<img src="data:${d.mime};base64,${d.data}" alt="${esc(d.name)}">`;
    }
    else if (d.type === 'pdf') {
      document.getElementById('previewBody').innerHTML = `<iframe src="data:application/pdf;base64,${d.data}"></iframe>`;
    }
    else if (d.type === 'text') {
      previewOriginal = d.content;
      document.getElementById('previewToolbar').style.display = 'flex';
      document.getElementById('previewLang').textContent = d.language;
      if (d.editable) {
        document.getElementById('btnEdit').style.display = '';
        document.getElementById('btnHistory').style.display = '';
        document.getElementById('btnCheckpoint').style.display = '';
        document.getElementById('btnRelated').style.display = '';
        document.getElementById('btnSaveAs').style.display = '';
      }
      renderCodeView(d.content, d.language);
      if (d.truncated) {
        document.getElementById('editIndicator').textContent = '⚠ Truncated (file too large)';
      }
    }
    else {
      document.getElementById('previewBody').innerHTML = `<div class="binary-info">
        <div class="binary-icon">📦</div>
        <div>Binary file — ${fmtSize(d.size)}</div>
        <div style="font-size:12px;color:var(--gray-400)">Preview not available for this file type</div>
      </div>`;
    }
  } catch(e) {
    document.getElementById('previewBody').innerHTML = `<div class="binary-info">
      <div class="binary-icon">❌</div><div>Error: ${esc(e.message)}</div></div>`;
  }
}

async function closePreview() {
  if (previewModified) {
    const ok = await styledConfirm(t('unsaved_title'), t('unsaved_msg'));
    if (!ok) return;
  }
  // Release edit lock if we had one
  if (snapshotTaken) releaseEditLock();
  document.getElementById('previewOverlay').classList.add('hidden');
  previewPath = '';
  previewModified = false;
  editMode = false;
}

function renderCodeView(text, lang) {
  const body = document.getElementById('previewBody');
  const lines = text.split('\n');
  const lineNums = lines.map((_,i) => i+1).join('\n');
  body.innerHTML = '';
  const wrap = document.createElement('div');
  wrap.style.cssText = 'display:flex;height:100%;overflow:auto';
  const ln = document.createElement('pre');
  ln.style.cssText = 'margin:0;padding:12px 8px 12px 12px;background:#f9fafb;border-right:1px solid #e5e7eb;font-family:Consolas,Menlo,monospace;font-size:13px;line-height:1.6;color:#9ca3af;text-align:right;user-select:none;min-width:40px;flex-shrink:0';
  ln.textContent = lineNums;
  const area = document.createElement('div');
  area.style.cssText = 'flex:1;overflow:auto';
  const code = document.createElement('pre');
  code.id = 'codeContent';
  code.style.cssText = 'margin:0;padding:12px;font-family:Consolas,Menlo,monospace;font-size:13px;line-height:1.6;color:#111827;white-space:pre-wrap;word-wrap:break-word';
  code.textContent = text;
  area.appendChild(code);
  wrap.appendChild(ln);
  wrap.appendChild(area);
  body.appendChild(wrap);
}

async function toggleEdit() {
  if (!editMode) {
    // Entering edit mode — claim lock first
    if (!snapshotTaken) {
      const canEdit = await claimEditLock();
      if (!canEdit) return;
    }
  }
  editMode = !editMode;
  const body = document.getElementById('previewBody');
  if (editMode) {
    // Snapshot the original server version on first edit
    if (!snapshotTaken && previewPath) {
      snapshotTaken = true;
      fetch(API+'/api/snapshot',{method:'POST',headers:{'Content-Type':'application/json'},
        body:JSON.stringify({path:previewPath, label:'auto-edit'})})
        .then(r=>r.json()).then(d=>{
          if(d.snapshot) document.getElementById('editIndicator').textContent = '📸 Snapshot saved';
        }).catch(()=>{});
    }
    const text = previewModified ? document.getElementById('codeTextarea').value : previewOriginal;
    const lines = text.split('\n');
    const lineNums = lines.map((_,i) => i+1).join('\n');
    const wrap = document.createElement('div');
    wrap.className = 'code-wrap';
    const ln = document.createElement('div');
    ln.className = 'line-numbers';
    ln.id = 'editLineNums';
    ln.textContent = lineNums;
    const area = document.createElement('div');
    area.className = 'code-area';
    const ta = document.createElement('textarea');
    ta.className = 'code-editor';
    ta.id = 'codeTextarea';
    ta.spellcheck = false;
    ta.value = text;
    area.appendChild(ta);
    wrap.appendChild(ln);
    wrap.appendChild(area);
    body.innerHTML = '';
    body.appendChild(wrap);
    document.getElementById('btnEdit').textContent = '👁 View';
    document.getElementById('btnSave').style.display = '';
    document.getElementById('btnDiff').style.display = '';
    ta.addEventListener('keydown', e => {
      if (e.key === 'Tab') {
        e.preventDefault();
        const s = ta.selectionStart, end = ta.selectionEnd;
        ta.value = ta.value.substring(0,s) + '  ' + ta.value.substring(end);
        ta.selectionStart = ta.selectionEnd = s + 2;
      }
      if ((e.ctrlKey || e.metaKey) && e.key === 's') { e.preventDefault(); saveFile(); }
      if ((e.ctrlKey || e.metaKey) && e.key === 'd') { e.preventDefault(); showDiffBeforeSave(); }
    });
    ta.addEventListener('input', () => {
      previewModified = true;
      document.getElementById('editIndicator').textContent = '● Modified';
      document.getElementById('editIndicator').className = 'edit-indicator modified';
      const lines = ta.value.split('\n');
      document.getElementById('editLineNums').textContent = lines.map((_,i) => i+1).join('\n');
    });
    ta.addEventListener('scroll', () => {
      document.getElementById('editLineNums').scrollTop = ta.scrollTop;
    });
    ta.focus();
  } else {
    const text = previewModified ? document.getElementById('codeTextarea').value : previewOriginal;
    const lang = document.getElementById('previewLang').textContent;
    renderCodeView(text, lang);
    document.getElementById('btnEdit').textContent = '✏ Edit';
    document.getElementById('btnDiff').style.display = 'none';
    if (!previewModified) document.getElementById('btnSave').style.display = 'none';
  }
}

async function saveFile() {
  const ta = document.getElementById('codeTextarea');
  const content = ta ? ta.value : previewOriginal;

  // Compute hash of the version we loaded (for server-side compare-and-save)
  let origHash = '';
  try {
    const hashBuf = await crypto.subtle.digest('SHA-256', new TextEncoder().encode(previewOriginal));
    origHash = Array.from(new Uint8Array(hashBuf)).map(b=>b.toString(16).padStart(2,'0')).join('');
  } catch(e) { /* hash unavailable — save without CAS */ }

  status('Saving...');
  try {
    const r = await fetch(API+'/api/save', {
      method: 'POST', headers: {'Content-Type':'application/json'},
      body: JSON.stringify({path: previewPath, content, expected_hash: origHash})
    });
    const d = await r.json();
    if (r.status === 409) {
      // Server-side conflict detected
      const ok = await styledConfirm('⚠️ File Changed on Server',
        'This file was modified on the server since you opened it. Overwrite with your version?');
      if(!ok) return;
      // Force save without hash check
      const r2 = await fetch(API+'/api/save', {
        method: 'POST', headers: {'Content-Type':'application/json'},
        body: JSON.stringify({path: previewPath, content, expected_hash: ''})
      });
      const d2 = await r2.json();
      if (!r2.ok) throw new Error(d2.error);
    } else if (!r.ok) {
      throw new Error(d.error);
    }
    previewOriginal = content;
    previewModified = false;
    document.getElementById('editIndicator').textContent = '✓ Saved';
    document.getElementById('editIndicator').className = 'edit-indicator';
    toast('Saved: ' + previewPath.split('/').pop(), 'ok');
    loadRemote();
  } catch(e) { toast('Save failed: ' + e.message, 'err'); }
}

// ═══════════════════════════════════════════════════════════
//  DIFF BEFORE SAVE
// ═══════════════════════════════════════════════════════════

function showDiffBeforeSave() {
  if (!previewModified && !editMode) { toast('No changes to diff','err'); return; }
  const ta = document.getElementById('codeTextarea');
  const newContent = ta ? ta.value : previewOriginal;
  const oldLines = previewOriginal.split('\n');
  const newLines = newContent.split('\n');
  const maxLen = Math.max(oldLines.length, newLines.length);

  let html = `<div style="font-size:11px;color:#6b7280;padding:8px 12px;border-bottom:1px solid #e5e7eb;display:flex;justify-content:space-between">
    <span>🔴 Original (server)</span><span>🟢 Modified (yours)</span></div>
    <div style="overflow:auto;flex:1;font-family:Consolas,Menlo,monospace;font-size:12px;line-height:1.7">`;

  for (let i = 0; i < maxLen; i++) {
    const oldL = i < oldLines.length ? oldLines[i] : '';
    const newL = i < newLines.length ? newLines[i] : '';
    const lineNum = i + 1;
    if (oldL === newL) {
      html += `<div style="display:flex;border-bottom:1px solid #f3f4f6">
        <span style="width:35px;text-align:right;padding-right:6px;color:#9ca3af;flex-shrink:0">${lineNum}</span>
        <span style="flex:1;padding:0 6px;white-space:pre-wrap;word-break:break-all">${escHtml(oldL)}</span></div>`;
    } else {
      if (oldL) html += `<div style="display:flex;background:#fee2e2;border-bottom:1px solid #fca5a5">
        <span style="width:35px;text-align:right;padding-right:6px;color:#dc2626;flex-shrink:0">${lineNum}</span>
        <span style="flex:1;padding:0 6px;white-space:pre-wrap;word-break:break-all;color:#991b1b">- ${escHtml(oldL)}</span></div>`;
      if (newL) html += `<div style="display:flex;background:#dcfce7;border-bottom:1px solid #86efac">
        <span style="width:35px;text-align:right;padding-right:6px;color:#16a34a;flex-shrink:0">${lineNum}</span>
        <span style="flex:1;padding:0 6px;white-space:pre-wrap;word-break:break-all;color:#166534">+ ${escHtml(newL)}</span></div>`;
    }
  }
  html += '</div>';

  const changed = oldLines.filter((l,i) => l !== (newLines[i]||'')).length +
                  Math.max(0, newLines.length - oldLines.length);
  const header = `⇄ Diff — ${changed} line(s) changed`;

  html += `<div style="padding:12px;border-top:1px solid #e5e7eb;display:flex;gap:8px;justify-content:center">
    <button onclick="document.getElementById('proResultsOverlay').classList.add('hidden')" class="btn btn-secondary btn-sm">Close</button>
    <button onclick="document.getElementById('proResultsOverlay').classList.add('hidden');saveFile()" class="btn btn-primary btn-sm">💾 Save</button>
  </div>`;

  showProResults(header, html);
}

// ═══════════════════════════════════════════════════════════
//  FILE HISTORY & ROLLBACK
// ═══════════════════════════════════════════════════════════

async function showFileHistory() {
  if (!previewPath) return;
  try {
    const r = await fetch(API+'/api/snapshot/history',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({path:previewPath})});
    const d = await r.json();

    let html = '';
    if (!d.snapshots || !d.snapshots.length) {
      html = `<div style="text-align:center;padding:40px;color:#9ca3af">
        <div style="font-size:36px;margin-bottom:8px">🕐</div>
        No snapshots yet.<br><span style="font-size:11px">A snapshot is created automatically when you start editing.</span></div>`;
    } else {
      html = `<div style="font-size:12px;color:#6b7280;padding:0 0 12px">
        ${d.snapshots.length} snapshot(s) for <strong>${escHtml(d.file)}</strong></div>`;
      for (const snap of d.snapshots) {
        const ts = snap.timestamp.replace('_',' ').replace(/(\d{4})(\d{2})(\d{2}) (\d{2})(\d{2})(\d{2})/,'$1-$2-$3 $4:$5:$6');
        const labelColors = {'auto-edit':'#3b82f6','checkpoint':'#d97706','pre-rollback':'#8b5cf6','legacy':'#6b7280'};
        const lc = labelColors[snap.label] || '#6b7280';
        html += `<div style="font-size:12px;padding:10px 12px;background:#f9fafb;border-radius:8px;margin:4px 0;border:1px solid #e5e7eb">
          <div style="display:flex;justify-content:space-between;align-items:center">
            <div>
              <span style="color:${lc};font-weight:600;font-size:11px">${snap.label_display}</span><br>
              <span style="color:#6b7280;font-size:11px">${ts} · ${fmtSize(snap.size)}</span>
            </div>
            <div style="display:flex;gap:6px">
              <button onclick="previewSnapshot('${escHtml(snap.path)}')" class="btn btn-secondary btn-sm" style="font-size:11px">👁</button>
              <button onclick="rollbackSnapshot('${escHtml(snap.path)}')" class="btn btn-sm" style="font-size:11px;background:#d97706;color:#fff;border:none">↩</button>
            </div>
          </div>
        </div>`;
      }
    }
    showProResults('🕐 Snapshot History', html);
  } catch(e) { toast('Error loading history: '+e.message,'err'); }
}

async function previewSnapshot(snapPath) {
  try {
    const r = await fetch(API+'/api/preview?path='+encodeURIComponent(snapPath));
    const d = await r.json();
    if (d.type === 'text') {
      let html = `<div style="font-size:11px;color:#6b7280;padding:0 0 8px">Snapshot: ${escHtml(snapPath.split('/').pop())}</div>
        <pre style="margin:0;padding:12px;background:#f9fafb;border:1px solid #e5e7eb;border-radius:8px;font-family:Consolas,Menlo,monospace;font-size:12px;line-height:1.6;overflow:auto;max-height:400px;white-space:pre-wrap">${escHtml(d.content)}</pre>
        <div style="padding:12px 0 0;text-align:center">
          <button onclick="showFileHistory()" class="btn btn-secondary btn-sm">← Back</button>
        </div>`;
      document.getElementById('proResBody').innerHTML = html;
    }
  } catch(e) { toast(e.message,'err'); }
}

async function rollbackSnapshot(snapPath) {
  const ok = await styledConfirm('↩ Restore Snapshot',
    'This will overwrite the current file with this snapshot. A pre-rollback snapshot of the current version will be created first. Continue?');
  if (!ok) return;
  try {
    const r = await fetch(API+'/api/snapshot/rollback',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({path:previewPath, snapshot_path:snapPath})});
    const d = await r.json();
    if (d.error) throw new Error(d.error);
    toast('Restored from snapshot','ok');
    openPreview(previewPath, previewPath.split('/').pop());
    document.getElementById('proResultsOverlay').classList.add('hidden');
    loadRemote();
  } catch(e) { toast('Rollback failed: '+e.message,'err'); }
}

async function createCheckpoint() {
  if (!previewPath) return;
  // If we're in edit mode, save current content first (with conflict check), then snapshot
  if (editMode) {
    const ta = document.getElementById('codeTextarea');
    if (ta && previewModified) {
      try {
        // Compute hash of the version we loaded for server-side CAS
        let origHash = '';
        try {
          const hashBuf = await crypto.subtle.digest('SHA-256', new TextEncoder().encode(previewOriginal));
          origHash = Array.from(new Uint8Array(hashBuf)).map(b=>b.toString(16).padStart(2,'0')).join('');
        } catch(e) {}
        const r = await fetch(API+'/api/save',{method:'POST',headers:{'Content-Type':'application/json'},
          body:JSON.stringify({path:previewPath, content:ta.value, expected_hash:origHash})});
        if (r.status === 409) {
          const ok = await styledConfirm('⚠️ File Changed on Server',
            'This file was modified on the server since you opened it. Overwrite before checkpoint?');
          if (!ok) return;
          const r2 = await fetch(API+'/api/save',{method:'POST',headers:{'Content-Type':'application/json'},
            body:JSON.stringify({path:previewPath, content:ta.value, expected_hash:''})});
          const d2 = await r2.json();
          if (!r2.ok) throw new Error(d2.error || 'Force save failed');
        } else if (!r.ok) {
          const d = await r.json();
          throw new Error(d.error || 'Save failed');
        }
        previewOriginal = ta.value;
        previewModified = false;
      } catch(e) { toast('Save before checkpoint failed: '+e.message,'err'); return; }
    }
  }
  try {
    const r = await fetch(API+'/api/snapshot',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({path:previewPath, label:'checkpoint'})});
    const d = await r.json();
    if (d.snapshot) {
      toast('📌 Checkpoint created','ok');
      document.getElementById('editIndicator').textContent = '📌 Checkpoint saved';
    } else {
      toast(d.reason || 'Could not create checkpoint','err');
    }
  } catch(e) { toast(e.message,'err'); }
}

// ═══════════════════════════════════════════════════════════
//  OPEN RELATED FILE
// ═══════════════════════════════════════════════════════════

async function showRelatedFiles() {
  if (!previewPath) return;
  const content = editMode && document.getElementById('codeTextarea')
    ? document.getElementById('codeTextarea').value : previewOriginal;
  try {
    const r = await fetch(API+'/api/related',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({path:previewPath, content})});
    const d = await r.json();
    if (d.error) { toast(d.error,'err'); return; }
    if (!d.related || !d.related.length) {
      toast('No related files found','err'); return;
    }
    let html = `<div style="font-size:12px;color:#6b7280;padding:0 0 12px">
      ${d.related.length} related file(s) found in <strong>${escHtml(d.source)}</strong></div>`;
    for (const ref of d.related) {
      html += `<div onclick="openPreview('${escHtml(ref.path)}','${escHtml(ref.name)}');document.getElementById('proResultsOverlay').classList.add('hidden')"
        style="font-size:13px;padding:10px 12px;background:#f9fafb;border:1px solid #e5e7eb;border-radius:8px;margin:4px 0;cursor:pointer;display:flex;justify-content:space-between;align-items:center"
        onmouseenter="this.style.background='#F5F0EB'" onmouseleave="this.style.background='#f9fafb'">
        <div><span style="font-weight:600">${escHtml(ref.name)}</span>
          <span style="font-size:11px;color:#9ca3af;margin-left:8px">${escHtml(ref.reference)}</span></div>
        <span style="color:var(--brand);font-size:16px">→</span>
      </div>`;
    }
    showProResults('🔗 Related Files', html);
  } catch(e) { toast(e.message,'err'); }
}

// ═══════════════════════════════════════════════════════════
//  SERVER LOCK / EDIT CLAIM
// ═══════════════════════════════════════════════════════════

async function claimEditLock() {
  if (!previewPath) return true;
  try {
    const r = await fetch(API+'/api/lock',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({path:previewPath, action:'claim'})});
    const d = await r.json();
    if (d.locked) {
      const proceed = await styledConfirm('🔒 File Locked',
        `This file is being edited by <strong>${escHtml(d.locked_by)}</strong> on <strong>${escHtml(d.locked_host)}</strong> since ${d.locked_since}.\n\nEdit anyway?`);
      return proceed;
    }
    return true;
  } catch(e) { return true; /* network issue, don't block */ }
}

async function releaseEditLock() {
  if (!previewPath) return;
  try {
    await fetch(API+'/api/lock',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({path:previewPath, action:'release'})});
  } catch(e) { /* best effort */ }
}

// ═══════════════════════════════════════════════════════════
//  SAVE AS COPY / PUBLISH SWAP
// ═══════════════════════════════════════════════════════════

async function saveAsCopy() {
  if (!previewPath) return;
  const ta = document.getElementById('codeTextarea');
  const content = ta ? ta.value : previewOriginal;
  const name = previewPath.split('/').pop();
  const parent = previewPath.substring(0, previewPath.lastIndexOf('/'));

  const ext = name.includes('.') ? '.' + name.split('.').pop() : '';
  const base = name.includes('.') ? name.substring(0, name.lastIndexOf('.')) : name;

  let html = `<div style="padding:16px 0">
    <div style="font-size:13px;font-weight:600;margin-bottom:12px">Save a copy of <strong>${escHtml(name)}</strong></div>
    <div style="display:flex;flex-direction:column;gap:8px">
      <button onclick="_doSaveAs('${escHtml(parent)}/${escHtml(base)}.copy${escHtml(ext)}')" class="btn btn-secondary btn-sm" style="text-align:left;padding:10px 14px">
        📋 Save as <strong>${escHtml(base)}.copy${escHtml(ext)}</strong>
      </button>
      <button onclick="_doSaveAs('${escHtml(parent)}/${escHtml(base)}.new${escHtml(ext)}')" class="btn btn-secondary btn-sm" style="text-align:left;padding:10px 14px">
        📝 Save as <strong>${escHtml(base)}.new${escHtml(ext)}</strong>
      </button>
      <button onclick="_doSaveAs('${escHtml(parent)}/${escHtml(base)}.bak${escHtml(ext)}')" class="btn btn-secondary btn-sm" style="text-align:left;padding:10px 14px">
        💾 Save as <strong>${escHtml(base)}.bak${escHtml(ext)}</strong>
      </button>
      <div style="margin-top:8px">
        <div style="font-size:11px;color:#6b7280;margin-bottom:4px">Custom path:</div>
        <div style="display:flex;gap:6px">
          <input type="text" id="saveAsCustomPath" value="${escHtml(parent)}/${escHtml(base)}.copy${escHtml(ext)}" style="flex:1;padding:8px 10px;border:1px solid #d1d5db;border-radius:6px;font-family:var(--font-mono);font-size:12px">
          <button onclick="_doSaveAs(document.getElementById('saveAsCustomPath').value)" class="btn btn-primary btn-sm">Save</button>
        </div>
      </div>
    </div>
  </div>`;
  showProResults('📋 Save As Copy', html);
}

async function _doSaveAs(targetPath) {
  const ta = document.getElementById('codeTextarea');
  const content = ta ? ta.value : previewOriginal;
  try {
    const r = await fetch(API+'/api/save_as',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({path:targetPath, content})});
    const d = await r.json();
    if (d.error) throw new Error(d.error);
    toast('Saved copy: ' + targetPath.split('/').pop(),'ok');
    document.getElementById('proResultsOverlay').classList.add('hidden');
    loadRemote();
  } catch(e) { toast('Save failed: '+e.message,'err'); }
}

// ═══════════════════════════════════════════════════════════
//  SEARCH ACROSS FOLDER
// ═══════════════════════════════════════════════════════════

function openSearch() {
  let html = `<div style="padding:4px 0 16px">
    <div style="display:flex;gap:8px;margin-bottom:10px">
      <input type="text" id="searchQuery" placeholder="Search text or /regex/" style="flex:1;padding:10px 12px;border:1px solid #d1d5db;border-radius:8px;font-family:var(--font-mono);font-size:13px" onkeydown="if(event.key==='Enter')runSearch()">
      <button onclick="runSearch()" class="btn btn-primary btn-sm" style="padding:10px 18px">🔎</button>
    </div>
    <div style="display:flex;gap:12px;align-items:center;font-size:11px;color:#6b7280">
      <label><input type="checkbox" id="searchCase"> Case sensitive</label>
      <label><input type="checkbox" id="searchRegex"> Regex</label>
      <label><input type="checkbox" id="searchRecursive" checked> Recursive</label>
    </div>
    <div id="searchStatus" style="font-size:11px;color:#9ca3af;margin-top:8px"></div>
  </div>
  <div id="searchResults" style="overflow-y:auto;max-height:50vh"></div>`;
  showProResults('🔎 Search in Folder: ' + remotePath, html);
  setTimeout(()=>{const q=document.getElementById('searchQuery');if(q)q.focus()},100);
}

async function runSearch() {
  const query = document.getElementById('searchQuery').value;
  if (!query) return;
  const isCase = document.getElementById('searchCase').checked;
  const isRegex = document.getElementById('searchRegex').checked;
  const isRecursive = document.getElementById('searchRecursive').checked;
  document.getElementById('searchStatus').textContent = 'Searching...';
  document.getElementById('searchResults').innerHTML = '';

  try {
    const r = await fetch(API+'/api/search',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({path:remotePath, query, case_sensitive:isCase, regex:isRegex, recursive:isRecursive})});
    const d = await r.json();
    if (d.error){document.getElementById('searchStatus').textContent=d.error;return}

    document.getElementById('searchStatus').textContent =
      `${d.total_matches} match(es) in ${d.files_searched} files` + (d.truncated?' (truncated)':'');

    let html = '';
    let lastFile = '';
    for (const m of d.matches) {
      if (m.file !== lastFile) {
        html += `<div style="font-size:12px;font-weight:700;color:var(--brand-800);padding:10px 0 4px;border-top:${lastFile?'1px solid #e5e7eb':'none'}">${escHtml(m.file)}</div>`;
        lastFile = m.file;
      }
      html += `<div onclick="openPreviewAtLine('${escHtml(m.full_path)}','${escHtml(m.file.split('/').pop())}',${m.line});document.getElementById('proResultsOverlay').classList.add('hidden')"
        style="font-size:12px;padding:6px 8px;margin:2px 0;background:#f9fafb;border:1px solid #e5e7eb;border-radius:6px;cursor:pointer;font-family:Consolas,Menlo,monospace;line-height:1.5"
        onmouseenter="this.style.background='#F5F0EB'" onmouseleave="this.style.background='#f9fafb'">
        <span style="color:#9ca3af;margin-right:6px">${m.line}:</span>${escHtml(m.text)}
      </div>`;
    }
    if (!d.matches.length) {
      html = '<div style="text-align:center;padding:20px;color:#9ca3af">No matches found</div>';
    }
    document.getElementById('searchResults').innerHTML = html;
  } catch(e) { document.getElementById('searchStatus').textContent = 'Error: '+e.message; }
}

function escHtml(s) { return s.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;'); }

let _jumpToLine = 0;

async function openPreviewAtLine(path, name, line) {
  _jumpToLine = line || 0;
  await openPreview(path, name);
  // After preview loads, scroll to line
  if (_jumpToLine > 0) {
    setTimeout(() => {
      const body = document.getElementById('previewBody');
      if (!body) return;
      const lineHeight = 20.8; // ~13px font * 1.6 line-height
      const scrollTarget = (_jumpToLine - 3) * lineHeight;
      const scrollable = body.querySelector('div[style*="overflow"]') || body;
      scrollable.scrollTop = Math.max(0, scrollTarget);
      // Highlight the target line briefly
      const lines = body.querySelectorAll('pre');
      if (lines.length > 0) {
        const code = lines[lines.length - 1];
        const allLines = code.textContent.split('\n');
        if (_jumpToLine <= allLines.length) {
          const lineText = allLines[_jumpToLine - 1];
          const highlighted = code.innerHTML.replace(
            escHtml(lineText),
            `<mark style="background:#fef08a;border-radius:2px">${escHtml(lineText)}</mark>`
          );
          code.innerHTML = highlighted;
          // Remove highlight after 3 seconds
          setTimeout(() => {
            const mark = code.querySelector('mark');
            if (mark) { mark.outerHTML = mark.innerHTML; }
          }, 3000);
        }
      }
      _jumpToLine = 0;
    }, 500);
  }
}

// Simple syntax highlighting
function syntaxHighlight(code, lang) {
  let h = escHtml(code);
  if (lang === 'text' || lang === 'markdown') return h;

  // Comments
  if (['python','ruby','bash','yaml','toml','ini'].includes(lang)) {
    h = h.replace(/(#.*?)(\n|$)/g, '<span class="cmt">$1</span>$2');
  }
  if (['javascript','typescript','jsx','tsx','java','c','cpp','csharp','go','rust','swift','kotlin','scala','php','css','scss','less','sql'].includes(lang)) {
    h = h.replace(/(\/\/.*?)(\n|$)/g, '<span class="cmt">$1</span>$2');
    h = h.replace(/(\/\*[\s\S]*?\*\/)/g, '<span class="cmt">$1</span>');
  }
  if (['html','xml'].includes(lang)) {
    h = h.replace(/(&lt;!--[\s\S]*?--&gt;)/g, '<span class="cmt">$1</span>');
  }

  // Strings
  h = h.replace(/(&quot;.*?&quot;|&#39;.*?&#39;|"[^"]*"|'[^']*'|`[^`]*`)/g, '<span class="str">$1</span>');

  // Numbers
  h = h.replace(/\b(\d+\.?\d*)\b/g, '<span class="num">$1</span>');

  // Keywords per language
  const kwSets = {
    python: 'def class return if elif else for while try except finally import from as with in not and or is None True False lambda yield async await raise pass break continue',
    javascript: 'function const let var return if else for while do switch case break continue try catch finally throw new delete typeof instanceof in of class extends import export default from async await yield this super',
    typescript: 'function const let var return if else for while do switch case break continue try catch finally throw new delete typeof instanceof in of class extends import export default from async await yield this super type interface enum',
    php: 'function class return if else elseif for foreach while do switch case break continue try catch finally throw new echo print public private protected static abstract interface extends implements use namespace require include',
    java: 'class public private protected static final abstract interface extends implements return if else for while do switch case break continue try catch finally throw new import package void int boolean String',
    html: '',
    css: '',
    sql: 'SELECT FROM WHERE AND OR NOT IN JOIN LEFT RIGHT INNER OUTER ON AS ORDER BY GROUP HAVING INSERT INTO VALUES UPDATE SET DELETE CREATE TABLE ALTER DROP INDEX DISTINCT LIMIT OFFSET UNION COUNT SUM AVG MIN MAX',
  };
  const kws = kwSets[lang] || kwSets.javascript || '';
  if (kws) {
    kws.split(' ').forEach(kw => {
      if (kw) h = h.replace(new RegExp('\\b(' + kw + ')\\b', 'g'), '<span class="kw">$1</span>');
    });
  }

  // HTML tags
  if (['html','xml','jsx','tsx','php'].includes(lang)) {
    h = h.replace(/(&lt;\/?)([\w-]+)/g, '$1<span class="tag">$2</span>');
    h = h.replace(/\s([\w-]+)=/g, ' <span class="attr">$1</span>=');
  }

  return h;
}

// Keyboard shortcut: Escape closes modals
document.addEventListener('keydown', e => {
  if (e.key === 'Escape') {
    if (!document.getElementById('proNag').classList.contains('hidden')) { closeNag(); return; }
    if (!document.getElementById('langOverlay').classList.contains('hidden')) { document.getElementById('langOverlay').classList.add('hidden'); return; }
    if (!document.getElementById('proOverlay').classList.contains('hidden')) { closeProModal(); return; }
    if (!document.getElementById('lightbox').classList.contains('hidden')) { closeLightbox(); return; }
    if (!document.getElementById('dialogOverlay').classList.contains('hidden')) { dialogResolve(null); return; }
    if (!document.getElementById('previewOverlay').classList.contains('hidden')) { closePreview(); return; }
    if (!document.getElementById('galleryOverlay').classList.contains('hidden')) { closeGallery(); return; }
    if (!document.getElementById('historyOverlay').classList.contains('hidden')) { closeHistory(); return; }
    if (!document.getElementById('zipOverlay').classList.contains('hidden')) { closeZip(); return; }
    if (!document.getElementById('dashOverlay').classList.contains('hidden')) { closeDash(); return; }
    if (!document.getElementById('syncOverlay').classList.contains('hidden')) { closeSync(); return; }
    if (!document.getElementById('vaultOverlay').classList.contains('hidden')) { closeVault(); return; }
  }
});

// === DASHBOARD ===
async function openDashboard() {
  document.getElementById('dashOverlay').classList.remove('hidden');
  document.getElementById('dashBody').innerHTML = '<div class="dash-loading">⏳ Scanning server... this may take a moment</div>';
  try {
    const r = await fetch(API+'/api/dashboard?path='+encodeURIComponent(remotePath)+'&depth=3');
    const d = await r.json();
    if (!r.ok) throw new Error(d.error);
    renderDashboard(d);
  } catch(e) {
    document.getElementById('dashBody').innerHTML = `<div class="dash-loading">❌ ${esc(e.message)}</div>`;
  }
}
function closeDash() { document.getElementById('dashOverlay').classList.add('hidden'); }

function renderDashboard(d) {
  const body = document.getElementById('dashBody');
  let html = '';

  // Stats cards
  html += `<div class="dash-grid">
    <div class="dash-card"><div class="dash-val">${d.total_files.toLocaleString()}</div><div class="dash-label">Files</div></div>
    <div class="dash-card"><div class="dash-val">${d.total_dirs.toLocaleString()}</div><div class="dash-label">Folders</div></div>
    <div class="dash-card"><div class="dash-val">${fmtSize(d.total_size)}</div><div class="dash-label">Total Size</div></div>
    <div class="dash-card"><div class="dash-val">${d.extensions.length}</div><div class="dash-label">File Types</div></div>
  </div>`;

  // Extension breakdown
  if (d.extensions.length) {
    const maxSize = d.extensions[0]?.size || 1;
    html += `<div class="dash-section"><h3>📁 File Types</h3>`;
    d.extensions.forEach(e => {
      const pct = Math.max(2, (e.size / maxSize) * 100);
      html += `<div class="ext-bar">
        <span class="ext-name">${esc(e.ext)}</span>
        <div class="ext-fill" style="width:${pct}%"></div>
        <span class="ext-info">${e.count} files · ${fmtSize(e.size)}</span>
      </div>`;
    });
    html += `</div>`;
  }

  // Largest files
  if (d.largest.length) {
    html += `<div class="dash-section"><h3>📦 Largest Files</h3>
    <table class="dash-table"><thead><tr><th>File</th><th style="text-align:right">Size</th><th>Path</th></tr></thead><tbody>`;
    d.largest.forEach(f => {
      html += `<tr><td>${esc(f.name)}</td><td style="text-align:right">${fmtSize(f.size)}</td><td style="color:var(--gray-400);max-width:200px;overflow:hidden;text-overflow:ellipsis">${esc(f.path)}</td></tr>`;
    });
    html += `</tbody></table></div>`;
  }

  // Recent files
  if (d.recent.length) {
    html += `<div class="dash-section"><h3>🕐 Recently Modified</h3>
    <table class="dash-table"><thead><tr><th>File</th><th>Modified</th><th style="text-align:right">Size</th></tr></thead><tbody>`;
    d.recent.forEach(f => {
      html += `<tr><td>${esc(f.name)}</td><td>${f.mtime||'—'}</td><td style="text-align:right">${fmtSize(f.size)}</td></tr>`;
    });
    html += `</tbody></table></div>`;
  }

  // Quota info
  if (d.quota) {
    html += `<div class="dash-section"><h3>💾 Server Info</h3><pre style="font-family:var(--font-mono);font-size:12px;background:var(--gray-50);padding:12px;border-radius:6px;overflow-x:auto">${esc(d.quota)}</pre></div>`;
  }

  if (d.errors.length) {
    html += `<div class="dash-section"><h3>⚠ Scan Errors</h3>`;
    d.errors.forEach(e => { html += `<div style="font-size:12px;color:var(--danger)">${esc(e.path)}: ${esc(e.error)}</div>`; });
    html += `</div>`;
  }

  html += `<div style="font-size:11px;color:var(--gray-400);text-align:center;padding:12px">Scanned from ${esc(d.scanned_path)} · depth 3</div>`;
  body.innerHTML = html;
}

// === FOLDER SYNC ===
let syncDiffData = [];

function openSync() {
  document.getElementById('syncOverlay').classList.remove('hidden');
  document.getElementById('syncStats').innerHTML = '';
  document.getElementById('syncBody').innerHTML = '<div class="dash-loading">Click ⟳ Refresh to compare<br><br>📁 Local: <strong>' + esc(localPath) + '</strong><br>🌐 Remote: <strong>' + esc(remotePath) + '</strong></div>';
  document.getElementById('syncSummary').textContent = `Local: ${localPath}  ↔  Remote: ${remotePath}`;
}
function closeSync() { document.getElementById('syncOverlay').classList.add('hidden'); }

async function runSyncDiff() {
  document.getElementById('syncBody').innerHTML = '<div class="dash-loading">⏳ Comparing folders...</div>';
  document.getElementById('syncStats').innerHTML = '';
  try {
    const r = await fetch(API+'/api/sync/diff', {
      method: 'POST', headers: {'Content-Type':'application/json'},
      body: JSON.stringify({local_dir: localPath, remote_dir: remotePath})
    });
    const d = await r.json();
    if (!r.ok) throw new Error(d.error);
    syncDiffData = d.diff;
    renderSyncStats(d.stats);
    renderSyncDiff(d.diff);
  } catch(e) {
    document.getElementById('syncBody').innerHTML = `<div class="dash-loading">❌ ${esc(e.message)}</div>`;
  }
}

function renderSyncStats(s) {
  document.getElementById('syncStats').innerHTML = `
    <span class="sync-stat match">✓ ${s.match} identical</span>
    <span class="sync-stat local">⬆ ${s.local_only} local only</span>
    <span class="sync-stat remote">⬇ ${s.remote_only} remote only</span>
    <span class="sync-stat diff">≠ ${s.different} different</span>
  `;
}

function renderSyncDiff(diff) {
  const body = document.getElementById('syncBody');
  if (!diff.length) { body.innerHTML = '<div class="dash-loading">Folders are empty or identical</div>'; return; }

  // Sort: different first, then local_only, then remote_only, then match
  const order = {different: 0, local_only: 1, remote_only: 2, match: 3};
  diff.sort((a,b) => (order[a.status]||9) - (order[b.status]||9));

  body.innerHTML = diff.map((f, i) => {
    const icon = fileEmoji(f.name);
    const arrow = f.action === 'upload' ? '➡' : f.action === 'download' ? '⬅' : '＝';
    const checked = f.action !== 'none' ? 'checked' : '';
    const localInfo = f.local_size !== undefined ? fmtSize(f.local_size) + ' · ' + (f.local_mtime||'') : '—';
    const remoteInfo = f.remote_size !== undefined ? fmtSize(f.remote_size) + ' · ' + (f.remote_mtime||'') : '—';
    const statusLabel = {match:'Match', local_only:'Local only', remote_only:'Remote only', different:'Different'}[f.status] || f.status;
    return `<div class="sync-row">
      <input type="checkbox" class="sync-check" data-idx="${i}" ${checked} ${f.action==='none'?'disabled':''}>
      <div class="sync-icon">${icon}</div>
      <div class="sync-name">${esc(f.name)}</div>
      <div class="sync-detail">${localInfo}</div>
      <div class="sync-arrow">${arrow}</div>
      <div class="sync-detail">${remoteInfo}</div>
      <div class="sync-status ${f.status}">${statusLabel}</div>
    </div>`;
  }).join('');
}

function syncSelectAll() {
  document.querySelectorAll('.sync-check:not(:disabled)').forEach(cb => cb.checked = true);
}
function syncSelectNone() {
  document.querySelectorAll('.sync-check').forEach(cb => cb.checked = false);
}

async function executeSync() {
  const actions = [];
  document.querySelectorAll('.sync-check:checked').forEach(cb => {
    const idx = parseInt(cb.dataset.idx);
    const f = syncDiffData[idx];
    if (f && f.action && f.action !== 'none') {
      actions.push({name: f.name, action: f.action});
    }
  });
  if (!actions.length) { toast('Nothing selected to sync', 'err'); return; }
  const uploads = actions.filter(a=>a.action==='upload').length;
  const downloads = actions.filter(a=>a.action==='download').length;
  const ok = await styledConfirm(t('sync'), t('sync_confirm',{count:actions.length,up:uploads,down:downloads}));
  if (!ok) return;

  document.getElementById('syncSummary').textContent = '⏳ Syncing...';
  try {
    const r = await fetch(API+'/api/sync/execute', {
      method: 'POST', headers: {'Content-Type':'application/json'},
      body: JSON.stringify({actions, local_dir: localPath, remote_dir: remotePath})
    });
    const d = await r.json();
    if (!r.ok) throw new Error(d.error);
    toast(`Synced: ${d.synced} OK, ${d.failed} failed`, d.failed ? 'err' : 'ok');
    document.getElementById('syncSummary').textContent = `✓ Synced ${d.synced} files`;
    loadLocal(); loadRemote();
    // Re-run diff
    setTimeout(runSyncDiff, 500);
  } catch(e) {
    toast('Sync failed: ' + e.message, 'err');
    document.getElementById('syncSummary').textContent = 'Sync failed';
  }
}

// === TRANSFER HISTORY ===
function openHistory() {
  document.getElementById('historyOverlay').classList.remove('hidden');
  document.getElementById('historySearch').value = '';
  loadHistory();
}
function closeHistory() { document.getElementById('historyOverlay').classList.add('hidden'); }

async function loadHistory() {
  const q = document.getElementById('historySearch').value;
  try {
    const r = await fetch(API+'/api/history?q='+encodeURIComponent(q));
    const d = await r.json();
    renderHistory(d.history);
  } catch(e) {
    document.getElementById('historyBody').innerHTML = '<div style="text-align:center;padding:20px;color:var(--gray-400)">Error loading history</div>';
  }
}

function renderHistory(items) {
  const body = document.getElementById('historyBody');
  if (!items.length) {
    body.innerHTML = '<div style="text-align:center;padding:40px;color:var(--gray-400)">No transfer history yet</div>';
    return;
  }
  body.innerHTML = items.map(h => {
    const icons = {upload:'⬆', download:'⬇', zip:'📦', unzip:'📂', delete:'🗑', rename:'✏', sync:'🔄'};
    const icon = icons[h.action] || '📄';
    return `<div class="history-row">
      <div class="h-status">${h.ok ? '✅' : '❌'}</div>
      <div class="h-icon">${icon}</div>
      <div class="h-action ${h.action}">${h.action}</div>
      <div class="h-path" title="${esc(h.path)}">${esc(h.path)}</div>
      <div class="h-size">${h.size ? fmtSize(h.size) : ''}</div>
      <div class="h-time">${h.time}</div>
    </div>`;
  }).join('');
}

async function clearHistory() {
  const ok = await styledConfirm(t('clear'), t('clear_history_confirm'));
  if (!ok) return;
  await fetch(API+'/api/history/clear', {method:'POST'});
  toast('History cleared', 'ok');
  loadHistory();
}

// === ZIP / UNZIP ===
let zipFiles = [];

function openZipDialog() {
  // Get selected files from remote pane
  zipFiles = [...remoteSelected].map(i => remoteFiles[i]).filter(f => !f.is_dir).map(f => f.name);
  if (!zipFiles.length) { toast('Select files to zip first', 'err'); return; }
  document.getElementById('zipInfo').textContent = `Zip ${zipFiles.length} file(s) on the server (SFTP only)`;
  document.getElementById('zipName').value = 'archive.zip';
  document.getElementById('zipFileList').innerHTML = zipFiles.map(f => `<div style="padding:2px 0">📄 ${esc(f)}</div>`).join('');
  document.getElementById('zipOverlay').classList.remove('hidden');
}
function closeZip() { document.getElementById('zipOverlay').classList.add('hidden'); }

async function doZip() {
  const zipName = document.getElementById('zipName').value.trim();
  if (!zipName) return;
  closeZip();
  status('Zipping files...');
  try {
    const r = await fetch(API+'/api/zip', {
      method:'POST', headers:{'Content-Type':'application/json'},
      body: JSON.stringify({files: zipFiles, zip_name: zipName, directory: remotePath})
    });
    const d = await r.json();
    if (!r.ok) throw new Error(d.error);
    toast(`Created: ${zipName}`, 'ok');
    loadRemote();
  } catch(e) { toast('Zip failed: ' + e.message, 'err'); }
}

async function doUnzip(path) {
  if (!path) return;
  const dest = await styledPrompt('Unzip', 'Extract to directory:', remotePath);
  if (!dest) return;
  status('Unzipping...');
  try {
    const r = await fetch(API+'/api/unzip', {
      method:'POST', headers:{'Content-Type':'application/json'},
      body: JSON.stringify({path, dest})
    });
    const d = await r.json();
    if (!r.ok) throw new Error(d.error);
    toast('Unzipped successfully', 'ok');
    loadRemote();
  } catch(e) { toast('Unzip failed: ' + e.message, 'err'); }
}

// Bookmarks
// Load saved logins dropdown on startup
async function refreshSavedLogins(){
  try{
    const r=await fetch(API+'/api/logins');const d=await r.json();
    const box=document.getElementById('savedLoginsBox');
    const sel=document.getElementById('savedLoginsSelect');
    if(d.logins&&d.logins.length){
      box.classList.remove('hidden');
      sel.innerHTML='<option value="">— '+t('select_saved')+' —</option>';
      d.logins.forEach((l,i)=>{
        const opt=document.createElement('option');
        opt.value=i;
        opt.textContent=`${l.protocol}  ${l.username}@${l.host}:${l.port}`;
        opt.dataset.host=l.host;opt.dataset.port=l.port;opt.dataset.user=l.username;
        opt.dataset.proto=l.protocol;opt.dataset.idx=i;
        sel.appendChild(opt);
      });
    } else {
      box.classList.add('hidden');
    }
  }catch(e){}
}
refreshSavedLogins();
async function selectSavedLogin(){
  const sel=document.getElementById('savedLoginsSelect');
  const opt=sel.options[sel.selectedIndex];
  if(!opt||!opt.dataset.host)return;
  document.getElementById('inHost').value=opt.dataset.host;
  document.getElementById('inPort').value=opt.dataset.port;
  document.getElementById('inUser').value=opt.dataset.user;
  proto=opt.dataset.proto;
  document.querySelectorAll('.proto-btn').forEach(b=>b.classList.toggle('active',b.dataset.proto===proto));
  // Fetch actual password only now
  try{
    const r=await fetch(API+'/api/logins/credentials',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({index:parseInt(opt.dataset.idx)})});
    const d=await r.json();
    document.getElementById('inPass').value=d.password||'';
  }catch(e){document.getElementById('inPass').value='';}
}
function fillBM(h,p,u,pr){document.getElementById('inHost').value=h;document.getElementById('inPort').value=p;document.getElementById('inUser').value=u;document.querySelectorAll('.proto-btn').forEach(b=>{b.classList.toggle('active',b.dataset.proto===pr)});proto=pr}
</script>



<!-- Upload Guard Modal (Pro) -->
<div id="uploadGuardOverlay" class="modal-overlay hidden" onclick="if(event.target===this)dismissUploadGuard()">
  <div class="modal" style="max-width:480px">
    <div style="padding:20px">
      <div id="uploadGuardIcon" style="font-size:48px;text-align:center;margin-bottom:12px">🛡️</div>
      <h3 id="uploadGuardTitle" style="margin:0 0 8px;text-align:center;font-size:18px">Smart Upload Guard</h3>
      <div id="uploadGuardMsg" style="font-size:13px;color:#374151;line-height:1.6;text-align:center"></div>
      <div id="uploadGuardFiles" style="margin-top:12px;font-size:12px;color:#dc2626;display:none"></div>
    </div>
    <div style="padding:12px 20px;border-top:1px solid #e5e7eb;display:flex;gap:8px;justify-content:center">
      <button class="btn btn-secondary btn-sm" onclick="dismissUploadGuard()">Cancel Upload</button>
      <button class="btn btn-sm" id="btnForceUpload" onclick="forceUpload()" style="background:#dc2626;color:#fff;border:none">Upload Anyway</button>
    </div>
  </div>
</div>

<div class="guard-dwarf-wrap idle hidden" id="guardDwarfWrap">
    <div class="guard-speech" id="guardSpeech">Hold on!</div>
    """ + (f'<img class="guard-dwarf-img" src="data:image/gif;base64,{DWARF_IMG}" alt="Guard Dwarf">' if DWARF_IMG else '') + (f'<div class="guard-dwarf-hammer" style="background-image:url(data:image/png;base64,{DWARF_HAMMER})"></div>' if DWARF_HAMMER else '') + r"""
  </div>
  <label class="guard-toggle hidden" id="guardToggle"><input type="checkbox" id="guardEnabled" checked onchange="toggleGuard()"> Guard</label>
</body>
</html>"""


# ═══════════════════════════════════════════════════════════
#  MAIN
# ═══════════════════════════════════════════════════════════

def main():
    import logging
    logging.getLogger("werkzeug").setLevel(logging.ERROR)

    # Start Flask in background thread
    server = threading.Thread(
        target=lambda: app.run(host="127.0.0.1", port=PORT, debug=False, use_reloader=False),
        daemon=True
    )
    server.start()

    # Wait for server to be ready
    import time, urllib.request
    for _ in range(50):
        try:
            req = urllib.request.Request(
                f"http://127.0.0.1:{PORT}/api/bookmarks/status",
                headers={"X-Session-Token": _SESSION_TOKEN}
            )
            urllib.request.urlopen(req, timeout=1)
            break
        except Exception:
            time.sleep(0.1)

    # Try pywebview for native window, fall back to browser
    try:
        import webview

        # Find icon file
        icon_path = None
        for candidate in [
            Path(__file__).parent / "aivelo.ico",
            Path(__file__).parent / "icon.png",
            Path(sys.executable).parent / "aivelo.ico",
        ]:
            if candidate.exists():
                icon_path = str(candidate)
                break

        window = webview.create_window(
            f"Aivelo FTP Vault v{APP_VERSION}",
            f"http://127.0.0.1:{PORT}",
            width=1150,
            height=750,
            min_size=(900, 600),
        )
        webview.start(icon=icon_path) if icon_path else webview.start()
    except ImportError:
        import webbrowser
        print(f"\n  pywebview not found — opening in browser instead.")
        print(f"  Install pywebview for a standalone window: pip install pywebview\n")
        print(f"  Aivelo FTP Vault — http://localhost:{PORT}\n")
        webbrowser.open(f"http://localhost:{PORT}")
        # Keep main thread alive
        try:
            while True:
                time.sleep(1)
        except KeyboardInterrupt:
            pass


if __name__ == "__main__":
    main()
