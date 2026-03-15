#!/usr/bin/env bash
# ═══════════════════════════════════════════════════════════
#  Aivelo FTP Vault — macOS Build Script
#  Produces:  dist/Aivelo FTP Vault.app
# ═══════════════════════════════════════════════════════════
set -euo pipefail

# ─── Configuration ────────────────────────────────────────
APP_NAME="Aivelo FTP Vault"
VERSION="2.1.0"
PYTHON="${PYTHON:-python3}"
VENV_DIR=".venv-build"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color

# ─── Banner ───────────────────────────────────────────────
echo -e "${CYAN}"
echo "╔═══════════════════════════════════════════════════╗"
echo "║    🏰  Aivelo FTP Vault — macOS Builder  🏰     ║"
echo "║                  Version ${VERSION}                  ║"
echo "╚═══════════════════════════════════════════════════╝"
echo -e "${NC}"

# ─── Preflight checks ────────────────────────────────────
echo -e "${BLUE}▸ Checking prerequisites...${NC}"

# Check macOS
if [[ "$(uname)" != "Darwin" ]]; then
    echo -e "${RED}✗ This script must be run on macOS${NC}"
    exit 1
fi
echo -e "${GREEN}  ✓ Running on macOS $(sw_vers -productVersion)${NC}"

# Check Python 3.9+
if ! command -v "$PYTHON" &>/dev/null; then
    echo -e "${RED}✗ Python 3 not found. Install via: brew install python@3.11${NC}"
    exit 1
fi
PY_VERSION=$("$PYTHON" -c "import sys; print(f'{sys.version_info.major}.{sys.version_info.minor}')")
echo -e "${GREEN}  ✓ Python ${PY_VERSION}${NC}"

# Check that aivelo_ftp.py exists
if [[ ! -f "aivelo_ftp.py" ]]; then
    echo -e "${RED}✗ aivelo_ftp.py not found in current directory${NC}"
    echo -e "  Place this script alongside aivelo_ftp.py and run again."
    exit 1
fi
echo -e "${GREEN}  ✓ aivelo_ftp.py found${NC}"

# ─── Create / activate virtual environment ────────────────
echo ""
echo -e "${BLUE}▸ Setting up build environment...${NC}"

if [[ ! -d "$VENV_DIR" ]]; then
    echo -e "  Creating virtual environment in ${VENV_DIR}..."
    "$PYTHON" -m venv "$VENV_DIR"
fi

source "${VENV_DIR}/bin/activate"
echo -e "${GREEN}  ✓ Virtual environment activated${NC}"

# ─── Install dependencies ─────────────────────────────────
echo ""
echo -e "${BLUE}▸ Installing dependencies...${NC}"

pip install --upgrade pip setuptools wheel -q
pip install flask paramiko cryptography pywebview pyinstaller -q

# pywebview on macOS needs pyobjc
pip install pyobjc-core pyobjc-framework-Cocoa pyobjc-framework-WebKit -q

echo -e "${GREEN}  ✓ All dependencies installed${NC}"

# ─── Generate .icns icon (if not present) ─────────────────
echo ""
echo -e "${BLUE}▸ Preparing app icon...${NC}"

if [[ -f "aivelo.icns" ]]; then
    echo -e "${GREEN}  ✓ aivelo.icns already exists${NC}"
elif [[ -f "icon.png" ]]; then
    echo "  Converting icon.png → aivelo.icns..."
    ./generate_icns.sh icon.png
    echo -e "${GREEN}  ✓ aivelo.icns generated from icon.png${NC}"
elif [[ -f "aivelo.ico" ]]; then
    echo "  Converting aivelo.ico → aivelo.icns via sips..."
    # Convert .ico to .png first, then to .icns
    sips -s format png "aivelo.ico" --out "_tmp_icon.png" 2>/dev/null || true
    if [[ -f "_tmp_icon.png" ]]; then
        ./generate_icns.sh _tmp_icon.png
        rm -f _tmp_icon.png
        echo -e "${GREEN}  ✓ aivelo.icns generated from aivelo.ico${NC}"
    else
        echo -e "${YELLOW}  ⚠ Could not convert .ico — building without custom icon${NC}"
    fi
else
    echo -e "${YELLOW}  ⚠ No icon file found (icon.png or aivelo.ico)${NC}"
    echo "    The app will use the default PyInstaller icon."
    echo "    To add a custom icon, place icon.png (1024×1024) in this directory."
fi

# ─── Build with PyInstaller ───────────────────────────────
echo ""
echo -e "${BLUE}▸ Building macOS application...${NC}"
echo ""

# Clean previous builds
rm -rf build dist

pyinstaller AiveloFTP.spec \
    --noconfirm \
    --clean \
    2>&1 | while IFS= read -r line; do
        # Show progress but filter noise
        if [[ "$line" == *"Building"* ]] || [[ "$line" == *"BUNDLE"* ]] || [[ "$line" == *"completed"* ]]; then
            echo -e "  ${CYAN}${line}${NC}"
        fi
    done

echo ""

# ─── Verify the build ────────────────────────────────────
APP_PATH="dist/${APP_NAME}.app"

if [[ -d "$APP_PATH" ]]; then
    APP_SIZE=$(du -sh "$APP_PATH" | awk '{print $1}')
    echo -e "${GREEN}╔═══════════════════════════════════════════════════╗${NC}"
    echo -e "${GREEN}║              ✓ BUILD SUCCESSFUL                  ║${NC}"
    echo -e "${GREEN}╚═══════════════════════════════════════════════════╝${NC}"
    echo ""
    echo -e "  ${CYAN}Application:${NC}  ${APP_PATH}"
    echo -e "  ${CYAN}Size:${NC}         ${APP_SIZE}"
    echo -e "  ${CYAN}Architecture:${NC} $(uname -m)"
    echo ""

    # ─── Optional: Create DMG ─────────────────────────────
    if [[ "${CREATE_DMG:-0}" == "1" ]]; then
        echo -e "${BLUE}▸ Creating DMG installer...${NC}"
        DMG_NAME="AiveloFTP-${VERSION}-$(uname -m).dmg"
        hdiutil create -volname "${APP_NAME}" \
                       -srcfolder "dist" \
                       -ov \
                       -format UDZO \
                       "${DMG_NAME}" 2>/dev/null
        echo -e "${GREEN}  ✓ DMG created: ${DMG_NAME}${NC}"
    fi

    # ─── Optional: Code sign ──────────────────────────────
    if [[ -n "${CODESIGN_IDENTITY:-}" ]]; then
        echo -e "${BLUE}▸ Code signing...${NC}"
        codesign --force --deep --sign "${CODESIGN_IDENTITY}" "${APP_PATH}"
        echo -e "${GREEN}  ✓ Code signed with: ${CODESIGN_IDENTITY}${NC}"
    fi

    # ─── Optional: Notarize ───────────────────────────────
    if [[ -n "${NOTARIZE_PROFILE:-}" ]]; then
        echo -e "${BLUE}▸ Notarizing (this may take a few minutes)...${NC}"
        # First create a zip for notarization
        ditto -c -k --keepParent "${APP_PATH}" "${APP_NAME}.zip"
        xcrun notarytool submit "${APP_NAME}.zip" \
            --keychain-profile "${NOTARIZE_PROFILE}" \
            --wait
        xcrun stapler staple "${APP_PATH}"
        rm -f "${APP_NAME}.zip"
        echo -e "${GREEN}  ✓ Notarization complete${NC}"
    fi

    echo ""
    echo -e "  ${YELLOW}To run:${NC}  open \"${APP_PATH}\""
    echo -e "  ${YELLOW}To distribute:${NC}  CREATE_DMG=1 ./build.sh"
    echo ""
else
    echo -e "${RED}╔═══════════════════════════════════════════════════╗${NC}"
    echo -e "${RED}║              ✗ BUILD FAILED                      ║${NC}"
    echo -e "${RED}╚═══════════════════════════════════════════════════╝${NC}"
    echo ""
    echo "  Check the output above for errors."
    echo "  Common fixes:"
    echo "    • Ensure Xcode Command Line Tools: xcode-select --install"
    echo "    • Try Python 3.11: brew install python@3.11"
    echo "    • Check PyInstaller version: pip install --upgrade pyinstaller"
    exit 1
fi
