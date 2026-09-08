#!/usr/bin/env bash
# Attempt one finite inhibition cycle under EvmRunner/EVM.Ξ.
# Writes receipts JSON. Exit 0 only if Lean #eval yields true.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="$ROOT/output/direct-queue-validate"
mkdir -p "$OUT"
export PATH="${HOME}/.elan/bin:${PATH}"
cd "$ROOT"

RECEIPT="$OUT/xi-inhibition-receipt.json"
LOG="$OUT/xi-run.log"

if ! command -v lake >/dev/null 2>&1; then
  cat >"$RECEIPT" <<EOF
{"status":"ouvert","is_evm_xi":false,"reason":"lake not installed","plane":"none"}
EOF
  echo "lake missing" | tee "$LOG"
  exit 2
fi

{
  echo "=== lake env lean --version ==="
  lake env lean --version || true
  echo "=== building FFI (needed for native_decide / interpreter) ==="
} >"$LOG" 2>&1

# Build path: need packages + possibly FFI
if ! lake build EvmYul.FFI.ffi:dynlib >>"$LOG" 2>&1; then
  echo "FFI build failed — recording gap" | tee -a "$LOG"
  python3 - <<PY
import json, pathlib
p = pathlib.Path("$RECEIPT")
p.write_text(json.dumps({
  "status": "ouvert",
  "label": "ouvert",
  "is_evm_xi": False,
  "attempted": True,
  "plane": "EvmRunner/EVM.Ξ attempted but build failed",
  "log": "$LOG",
  "gap_fr": (
    "Impossible d'exécuter EvmRunner/EVM.Ξ ici: échec lake build FFI/deps. "
    "Les cycles predecessor restent simulateur Python, non preuves Ξ. "
    "In-tree pcontrol1_bytecode_parent (main@f14791d) affirme déjà inhibit/uninhibit "
    "via native_decide sur depositRuntime — ce n'est PAS une reproduction de cette course."
  ),
}, indent=2, ensure_ascii=False) + "\n")
print("WROTE", p)
PY
  exit 3
fi

# Eval the private lean file
if lake env lean "$ROOT/scripts/direct-queue-validate-xi-attempt.lean" >>"$LOG" 2>&1; then
  # Parse last true/false from log
  RESULT=$(rg -n '^(true|false)$' "$LOG" | tail -1 | awk -F: '{print $2}' || true)
  python3 - <<PY
import json, pathlib
result = """$RESULT""".strip()
ok = result == "true"
p = pathlib.Path("$RECEIPT")
p.write_text(json.dumps({
  "status": "testé" if ok else "ouvert",
  "label": "testé" if ok else "ouvert",
  "is_evm_xi": True if ok else False,
  "eval_result": result,
  "plane": "Eip8282.Audit.EvmRunner → EvmYul.EVM.Ξ",
  "code": "depositRuntime pinned bytes",
  "cycle": [
    "runDepositSystem nonempty oneByte on empty storage → SLOT_EXCESS=INHIBITOR, COUNT=0",
    "runDeposit user on inhibited storage → revert",
    "runDepositSystem empty on inhibited storage → SLOT_EXCESS=0",
  ],
  "finite": True,
  "claims_2_64_wrap": False,
  "log": "$LOG",
  "note_fr": (
    "Réception finie d'un cycle d'inhibition/réactivation sur octets runtime deposit "
    "épinglés via EvmRunner/Ξ. File vide (pas de drain multi-items). "
    "Ne prouve pas ∀ ni wrap 2^64."
  ) if ok else "eval did not return true",
}, indent=2, ensure_ascii=False) + "\n")
print("WROTE", p, "result=", result)
PY
  if [[ "${RESULT:-}" == "true" ]]; then exit 0; else exit 4; fi
else
  python3 - <<PY
import json, pathlib
p = pathlib.Path("$RECEIPT")
p.write_text(json.dumps({
  "status": "ouvert",
  "label": "ouvert",
  "is_evm_xi": False,
  "attempted": True,
  "plane": "EvmRunner/EVM.Ξ lean eval failed",
  "log": "$LOG",
  "gap_fr": (
    "Échec de l'évaluation Lean du cycle d'inhibition. "
    "Écart exact à Ξ: pas de reçu d'exécution EvmRunner sur les octets épinglés "
    "dans cette course de validation. Ne pas sur-revendiquer les traces simulateur."
  ),
}, indent=2, ensure_ascii=False) + "\n")
print("WROTE", p)
PY
  exit 5
fi
