#!/usr/bin/env bash
# Independent validation orchestrator for predecessor direct-queue diagnostics.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="$ROOT/output/direct-queue-validate"
mkdir -p "$OUT"
export PATH="${HOME}/.elan/bin:${PATH}"
cd "$ROOT"

echo "[1/4] classify predecessor scripts"
python3 "$ROOT/scripts/direct-queue-validate-classify.py"

echo "[2/4] static asm/hex anchors"
python3 "$ROOT/scripts/direct-queue-validate-static.py"

echo "[3/4] attempt Ξ inhibition cycle (best-effort)"
set +e
bash "$ROOT/scripts/direct-queue-validate-xi-run.sh"
XI_EC=$?
set -e
echo "xi-run exit=$XI_EC"

echo "[4/4] regenerate French report from JSON artifacts"
python3 "$ROOT/scripts/direct-queue-validate-rapport.py"

echo "DONE → $OUT"
ls -la "$OUT"
