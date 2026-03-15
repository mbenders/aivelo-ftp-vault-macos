#!/usr/bin/env bash
# ═══════════════════════════════════════════════════════════
#  Generate macOS .icns from a PNG file
#  Usage:  ./generate_icns.sh icon.png [output.icns]
#  Requires: sips, iconutil (both ship with macOS)
# ═══════════════════════════════════════════════════════════
set -euo pipefail

INPUT="${1:-icon.png}"
OUTPUT="${2:-aivelo.icns}"

if [[ ! -f "$INPUT" ]]; then
    echo "Error: Input file '$INPUT' not found"
    echo "Usage: $0 <input.png> [output.icns]"
    exit 1
fi

ICONSET_DIR="AppIcon.iconset"
rm -rf "$ICONSET_DIR"
mkdir -p "$ICONSET_DIR"

echo "Generating icon sizes from ${INPUT}..."

# Required sizes for macOS .icns
sips -z 16   16   "$INPUT" --out "${ICONSET_DIR}/icon_16x16.png"      2>/dev/null
sips -z 32   32   "$INPUT" --out "${ICONSET_DIR}/icon_16x16@2x.png"   2>/dev/null
sips -z 32   32   "$INPUT" --out "${ICONSET_DIR}/icon_32x32.png"      2>/dev/null
sips -z 64   64   "$INPUT" --out "${ICONSET_DIR}/icon_32x32@2x.png"   2>/dev/null
sips -z 128  128  "$INPUT" --out "${ICONSET_DIR}/icon_128x128.png"    2>/dev/null
sips -z 256  256  "$INPUT" --out "${ICONSET_DIR}/icon_128x128@2x.png" 2>/dev/null
sips -z 256  256  "$INPUT" --out "${ICONSET_DIR}/icon_256x256.png"    2>/dev/null
sips -z 512  512  "$INPUT" --out "${ICONSET_DIR}/icon_256x256@2x.png" 2>/dev/null
sips -z 512  512  "$INPUT" --out "${ICONSET_DIR}/icon_512x512.png"    2>/dev/null
sips -z 1024 1024 "$INPUT" --out "${ICONSET_DIR}/icon_512x512@2x.png" 2>/dev/null

echo "Converting iconset → ${OUTPUT}..."
iconutil -c icns "$ICONSET_DIR" -o "$OUTPUT"

rm -rf "$ICONSET_DIR"
echo "✓ ${OUTPUT} created successfully"
