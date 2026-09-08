#!/usr/bin/env bash
# Run nonempty inhibition cycle under EvmRunner/EVM.Ξ; emit receipts JSON.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="$ROOT/output/direct-queue-validate"
mkdir -p "$OUT"
export PATH="${HOME}/.elan/bin:${PATH}"
cd "$ROOT"

LOG="$OUT/xi-run.log"
RECEIPT="$OUT/xi-inhibition-receipt.json"
: >"$LOG"

FFI_DIR=".lake/packages/evmyul/.lake/build/lib"
LEANFFI="$FFI_DIR/libleanffi.so"
MODFFI="$FFI_DIR/lean/evmyul_EvmYul_FFI_ffi.so"
LEAN_FILE="$ROOT/scripts/direct-queue-validate-xi-attempt.lean"

log() { echo "$*" | tee -a "$LOG"; }

write_gap() {
  local reason="$1"
  python3 - "$RECEIPT" "$reason" "$LOG" <<'PY'
import json, sys, pathlib
path, reason, log = sys.argv[1], sys.argv[2], sys.argv[3]
pathlib.Path(path).write_text(json.dumps({
  "status": "ouvert",
  "label": "ouvert",
  "is_evm_xi": False,
  "attempted": True,
  "reason": reason,
  "log": log,
  "plane_required": "Eip8282.Audit.EvmRunner → EvmYul.EVM.Ξ",
}, indent=2, ensure_ascii=False) + "\n")
print("WROTE gap receipt", path)
PY
}

if ! command -v lake >/dev/null; then
  write_gap "lake missing"
  exit 2
fi

log "=== lean/lake versions ==="
lake env lean --version >>"$LOG" 2>&1 || true

log "=== lake exe cache get (best effort) ==="
lake exe cache get >>"$LOG" 2>&1 || log "cache get non-zero (continuing)"

log "=== build FFI dynlib ==="
if ! lake build EvmYul.FFI.ffi:dynlib >>"$LOG" 2>&1; then
  write_gap "FFI dynlib build failed"
  exit 3
fi

log "=== build Eip8282.Audit.EvmRunner + Bytecode ==="
if ! lake build Eip8282.Audit.EvmRunner Eip8282.Audit.Bytecode >>"$LOG" 2>&1; then
  write_gap "EvmRunner/Bytecode build failed"
  exit 4
fi

if [[ ! -f "$LEANFFI" || ! -f "$MODFFI" ]]; then
  write_gap "FFI shared objects missing after build"
  exit 5
fi

log "=== #eval xi-attempt lean ==="
set +e
lake env lean \
  --load-dynlib="$LEANFFI" \
  --load-dynlib="$MODFFI" \
  "$LEAN_FILE" >>"$LOG" 2>&1
EC=$?
set -e
log "lean_ec=$EC"

python3 - "$RECEIPT" "$LOG" "$EC" <<'PY'
import json, re, sys, pathlib, hashlib
from datetime import datetime, timezone
receipt_path, log_path, ec = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2]), int(sys.argv[3])
log = log_path.read_text(errors="replace")
# Collect bare true/false lines from #eval (ignore other noise)
bools = re.findall(r"(?m)^(true|false)$", log)
nums = re.findall(r"(?m)^(\d+)$", log)
labels = [
  "nonemptyInhibitionCycleReceipt",
  "depositCtorOk",
  "exitCtorOk",
  "depositNonemptyInhibitOk",
  "depositInhibitedUserRevertsOk",
  "depositUninhibitOk",
  "depositNonemptyUninhibitOk",
  "exitNonemptyInhibitOk",
  "exitNonemptyUninhibitOk",
  "depositSystemFlagOk",
]
facts = {}
for i, lab in enumerate(labels):
    facts[lab] = bools[i] if i < len(bools) else None
ok = facts.get("nonemptyInhibitionCycleReceipt") == "true" and ec == 0
# numeric samples after bools: finalGas, balance, outSize, slot0_is_inhibitor
samples = {
  "final_gas_after_deposit_nonempty_inhibit": int(nums[0]) if len(nums) > 0 else None,
  "deposit_addr_balance_after_inhibit": int(nums[1]) if len(nums) > 1 else None,
  "success_out_size_deposit_inhibit": int(nums[2]) if len(nums) > 2 else None,
  "slot0_is_inhibitor_flag": int(nums[3]) if len(nums) > 3 else None,
}
# pin hashes
root = pathlib.Path(log_path).parents[2] if False else pathlib.Path(".")
def hx(p):
    t = pathlib.Path(p).read_text().strip()
    return {"nibbles": len(t), "bytes": len(t)//2, "sha256_16": hashlib.sha256(t.encode()).hexdigest()[:16]}
report = {
  "status": "testé" if ok else "ouvert",
  "label": "testé" if ok else "ouvert",
  "is_evm_xi": bool(ok),
  "plane": "Eip8282.Audit.EvmRunner → EvmYul.EVM.Ξ",
  "lean_exit_code": ec,
  "evmyul_pin": "b62586650b4f96cc6da25f36574aaa8f329a6420",
  "code": {
    "depositRuntime": "Eip8282.Audit.Bytecode.depositRuntime",
    "exitRuntime": "Eip8282.Audit.Bytecode.exitRuntime",
    "depositInit": "Eip8282.Audit.Bytecode.depositInit",
    "exitInit": "Eip8282.Audit.Bytecode.exitInit",
  },
  "pinned_hex_files": {
    "builder_deposits/main.hex": hx("pinned/bytecode/builder_deposits/main.hex"),
    "builder_exits/main.hex": hx("pinned/bytecode/builder_exits/main.hex"),
    "builder_deposits/ctor.hex": hx("pinned/bytecode/builder_deposits/ctor.hex") if pathlib.Path("pinned/bytecode/builder_deposits/ctor.hex").exists() else None,
    "builder_exits/ctor.hex": hx("pinned/bytecode/builder_exits/ctor.hex") if pathlib.Path("pinned/bytecode/builder_exits/ctor.hex").exists() else None,
  },
  "facts": facts,
  "receipts": {
    "constructor": {
      "deposit_ctor_returns_runtime_and_zero_storage": facts.get("depositCtorOk"),
      "exit_ctor_returns_runtime_and_inhibitor_slot0": facts.get("exitCtorOk"),
    },
    "nonempty_queue_inhibition_reactivation": {
      "deposit_system_nonempty_calldata_drains_2_and_sets_INHIBITOR": facts.get("depositNonemptyInhibitOk"),
      "deposit_user_reverts_while_inhibited": facts.get("depositInhibitedUserRevertsOk"),
      "deposit_system_empty_clears_inhibitor": facts.get("depositUninhibitOk"),
      "deposit_nonempty_inhibited_queue_drains_and_clears": facts.get("depositNonemptyUninhibitOk"),
      "exit_system_nonempty_drains_2_and_sets_INHIBITOR": facts.get("exitNonemptyInhibitOk"),
      "exit_nonempty_inhibited_queue_drains_and_clears": facts.get("exitNonemptyUninhibitOk"),
    },
    "system_flags": {
      "same_image_user_fee_no_drain_vs_system_drain": facts.get("depositSystemFlagOk"),
      "system_addr": "0xfffffffffffffffffffffffffffffffffffffffe",
      "submitter": "0x1234",
    },
    "payload_storage_gas_balances": samples,
  },
  "cycle_steps_fr": [
    "Ctor deposit/exit sous Ξ (payload = runtime épinglé; storage init).",
    "File deposit non vide (HEAD=0,TAIL=2): system calldata 1 octet → drain 368 octets + EXCESS=INHIBITOR, COUNT=0, HEAD=TAIL=0.",
    "User sur image inhibée → revert (pas de SSTORE).",
    "System calldata vide sur inhibé → EXCESS=0.",
    "File inhibée encore peuplée → drain + clear inhibitor.",
    "Même pour exit (return 136 = 2*68).",
    "Flag SYSTEM: même image, user quote 32 B sans drain; SYSTEM drain + excess fold.",
  ],
  "finite": True,
  "claims_2_64_wrap": False,
  "nowrap_as_premise": False,
  "not_python_simulator": True,
  "timestamp_utc": datetime.now(timezone.utc).isoformat(),
  "log": str(log_path),
  "note_fr": (
    "Reçus finis d'exécution EvmRunner/Ξ sur octets runtime+init épinglés. "
    "Cycle d'inhibition/réactivation avec file non vide. "
    "Pas de wrap 2^64; noWrap n'est pas une prémisse."
    if ok else
    "Évaluation Lean incomplète ou fausse — voir log; ne pas sur-revendiquer."
  ),
}
receipt_path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
print("WROTE", receipt_path, "ok=", ok, "facts=", facts)
raise SystemExit(0 if ok else 6)
PY
