# 🏰 Aivelo FTP Vault — macOS Build Kit

Build native macOS `.app` bundles **without owning a Mac** — using GitHub Actions.

## How It Works

You push a version tag → GitHub spins up real macOS machines → builds the `.app` for both Apple Silicon and Intel → packages them as DMGs → attaches them to a GitHub Release. Your Mac users download the DMG and drag to Applications. Done.

## 📦 Repository Structure

```
your-repo/
├── aivelo_ftp.py              ← Your app (the 7700-line Python file)
├── icon.png                    ← App icon, 1024×1024 PNG (optional but recommended)
├── aivelo.icns                 ← Or pre-made macOS icon (optional)
├── requirements-build.txt      ← Python dependencies for the build
├── AiveloFTP.spec              ← PyInstaller config for macOS .app bundle
├── generate_icns.sh            ← PNG → .icns converter (runs on macOS runner)
├── build.sh                    ← Local build script (if you ever get a Mac)
├── README.md
└── .github/
    └── workflows/
        └── build-macos.yml    ← The GitHub Actions pipeline
```

## 🚀 Setup (One-Time)

### 1. Create the repo

Push all these files alongside your `aivelo_ftp.py` to a GitHub repository:

```bash
git init
git add .
git commit -m "Add macOS build pipeline"
git remote add origin https://github.com/YOUR_USER/aivelo-ftp-vault.git
git push -u origin main
```

### 2. Add an app icon (optional but recommended)

Place a `icon.png` (1024×1024, with transparency) in the repo root. The build pipeline automatically converts it to macOS `.icns` format.

### 3. That's it

No secrets or configuration needed for unsigned builds. The workflow runs on GitHub's free macOS runners.

## 📦 Building a Release

### Tag and push:

```bash
git tag v2.1.0
git push origin v2.1.0
```

This automatically:
1. Spins up **two macOS runners** (Apple Silicon + Intel)
2. Installs Python 3.11 + all dependencies
3. Converts your icon to `.icns`
4. Builds `Aivelo FTP Vault.app` via PyInstaller
5. Packages each into a DMG with an Applications shortcut
6. Creates a **GitHub Release** with both DMGs attached

### Or trigger manually:

Go to **Actions** → **Build macOS App** → **Run workflow** → type a version label → **Run**.
This builds without creating a release (useful for testing).

## 📥 What Your Users Get

After a tagged build, your GitHub Releases page shows:

```
Aivelo FTP Vault v2.1.0

  📦 AiveloFTP-2.1.0-arm64.dmg    (Apple Silicon: M1–M4 Macs)
  📦 AiveloFTP-2.1.0-x86_64.dmg   (Intel: pre-2020 Macs)
```

Users download, open the DMG, drag to Applications, done.

> **Note:** Without code signing, users will see a Gatekeeper warning on first launch.
> They bypass it by right-clicking the app → **Open** → **Open** in the dialog.

## 🔐 Optional: Code Signing & Notarization

To eliminate the Gatekeeper warning (professional distribution), you need an **Apple Developer account** (€99/year). Add these secrets to your GitHub repo under **Settings → Secrets → Actions**:

| Secret | What it is |
|--------|-----------|
| `MACOS_CERTIFICATE` | Base64-encoded `.p12` certificate |
| `MACOS_CERTIFICATE_PWD` | Password for the `.p12` |
| `MACOS_KEYCHAIN_PWD` | Any password (for temporary build keychain) |
| `MACOS_SIGNING_IDENTITY` | E.g. `Developer ID Application: Martijn Benders (TEAMID)` |
| `NOTARY_APPLE_ID` | Your Apple ID email |
| `NOTARY_TEAM_ID` | Your Apple Developer Team ID |
| `NOTARY_PASSWORD` | App-specific password from appleid.apple.com |

The workflow detects these automatically — if present, it signs and notarizes; if absent, it builds unsigned. You can add them later whenever you're ready.

### How to get the certificate (on any computer):

1. Enroll at [developer.apple.com](https://developer.apple.com) (€99/year)
2. In **Certificates, Identifiers & Profiles**, create a **Developer ID Application** certificate
3. Export as `.p12` with a password
4. Base64-encode it: `base64 -i certificate.p12 | pbcopy` (or use an online tool)
5. Paste into the `MACOS_CERTIFICATE` secret

## 🔄 Updating the App

When you release a new version of `aivelo_ftp.py`:

```bash
# Make your changes
git add aivelo_ftp.py
git commit -m "v2.2.0 — new feature X"

# Tag and push
git tag v2.2.0
git push origin main --tags
```

New DMGs appear on the Releases page within ~10 minutes.

## 💰 GitHub Actions Pricing

- **Public repos**: Completely free, unlimited macOS minutes
- **Private repos**: 200 free macOS minutes/month (each build uses ~5–8 minutes, so ~12 releases/month for free)

If you need more, the macOS runner costs $0.08/minute beyond the free tier.

## 🐛 Troubleshooting

### Build fails with `ModuleNotFoundError`
Add the missing module to `hiddenimports` in `AiveloFTP.spec`.

### DMG is very large (>200MB)
Add more entries to the `excludes` list in `AiveloFTP.spec`. Common bloat sources: `tkinter`, `unittest`, `email`, `xmlrpc` (already excluded).

### Users report "App is damaged"
This happens when macOS quarantines unsigned apps downloaded from the internet. Tell users:
```bash
xattr -cr "/Applications/Aivelo FTP Vault.app"
```
Or better: set up code signing (see above).

### Want to test locally on a Mac you borrow
```bash
chmod +x build.sh generate_icns.sh
./build.sh
open "dist/Aivelo FTP Vault.app"
```

## ⚙️ Configuration on macOS

The app stores user data in:
```
~/.aiveloftp/
├── config.json        ← Bookmarks, launch count, pro key
├── activation.json    ← RSA-signed license cache
└── aivelo.log         ← Application log
```

---

*Built with 🏰 by Aivelo — [martijnbenders.nl](https://martijnbenders.nl)*
