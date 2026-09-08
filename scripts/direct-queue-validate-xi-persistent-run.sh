#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="$ROOT/output/direct-queue-validate"
mkdir -p "$OUT"
export PATH="${HOME}/.elan/bin:${PATH}"
cd "$ROOT"
LOG="$OUT/xi-persistent-run.log"
RECEIPT="$OUT/xi-persistent-inhibition-receipt.json"
: >"$LOG"
FFI_DIR=".lake/packages/evmyul/.lake/build/lib"
LEANFFI="$FFI_DIR/libleanffi.so"
MODFFI="$FFI_DIR/lean/evmyul_EvmYul_FFI_ffi.so"
LEAN_FILE="$ROOT/scripts/direct-queue-validate-xi-persistent.lean"

echo "=== versions ===" | tee -a "$LOG"
lake env lean --version >>"$LOG" 2>&1 || true

# Reuse cache; only rebuild if needed
if [[ ! -f "$LEANFFI" || ! -f "$MODFFI" ]]; then
  echo "=== FFI build ===" | tee -a "$LOG"
  lake build EvmYul.FFI.ffi:dynlib >>"$LOG" 2>&1
fi
if [[ ! -f .lake/build/lib/lean/Eip8282/Audit/EvmRunner.olean ]]; then
  echo "=== EvmRunner build ===" | tee -a "$LOG"
  lake build Eip8282.Audit.EvmRunner Eip8282.Audit.Bytecode >>"$LOG" 2>&1
fi

echo "=== #eval persistent lean ===" | tee -a "$LOG"
set +e
lake env lean --load-dynlib="$LEANFFI" --load-dynlib="$MODFFI" "$LEAN_FILE" >>"$LOG" 2>&1
EC=$?
set -e
echo "lean_ec=$EC" | tee -a "$LOG"

python3 - "$RECEIPT" "$LOG" "$EC" <<'PY'
import json, re, sys, pathlib, hashlib
from datetime import datetime, timezone
receipt_path, log_path, ec = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2]), int(sys.argv[3])
log = log_path.read_text(errors="replace")
vals = re.findall(r"(?m)^(true|false|\d+)$", log)
# First value is persistentInhibitionCycleOk
# Then D1: 8 nums + bool, D2: 3 nums + bool, D3: 8+bool, D4: 8+bool, E1: 8+bool, E2: 3+bool, E3: 8+bool, twoItem: 5 nums + bool

def take(i, n):
    return vals[i:i+n], i+n

i = 0
top, i = take(i, 1)
def parse_step(i, n_fields, name):
    fields, i = take(i, n_fields)
    okb, i = take(i, 1)
    return {
        "name": name,
        "raw": fields,
        "ok": okb[0] if okb else None,
    }, i

# D1: succ,rev,out,s0,count,head,tail,gas + ok
d1, i = parse_step(i, 8, "D1_deposit_system_nonempty_partial_inhibit")
d2, i = parse_step(i, 3, "D2_deposit_user_revert_while_inhibited_nonempty")
d3, i = parse_step(i, 8, "D3_deposit_system_empty_drain_rest_clear")
d4, i = parse_step(i, 8, "D4_deposit_system_empty_idle")
e1, i = parse_step(i, 8, "E1_exit_system_nonempty_partial_inhibit")
e2, i = parse_step(i, 3, "E2_exit_user_revert_while_inhibited_nonempty")
e3, i = parse_step(i, 8, "E3_exit_system_empty_drain_rest_clear")
two, i = parse_step(i, 5, "contrast_two_item_full_reset")

def decode_full(step):
    r = step["raw"]
    if len(r) < 8:
        return step
    return {
        **step,
        "success": r[0] == "1",
        "revert": r[1] == "1",
        "payload_size": int(r[2]),
        "slot0_tag": int(r[3]),  # 1=INHIBITOR, else small excess or 2
        "slot0_meaning": "INHIBITOR" if r[3]=="1" else ("excess="+r[3] if r[3] not in ("2","9") else r[3]),
        "count": int(r[4]),
        "head": int(r[5]),
        "tail": int(r[6]),
        "gas_final": int(r[7]),
        "length_nat": (int(r[6]) - int(r[5])) if r[5].isdigit() and r[6].isdigit() and int(r[6]) >= int(r[5]) else None,
    }

steps = {
    "D1": decode_full(d1),
    "D2": {**d2, "success": d2["raw"][0]=="1" if len(d2["raw"])>0 else None,
           "revert": d2["raw"][1]=="1" if len(d2["raw"])>1 else None,
           "gas_final": int(d2["raw"][2]) if len(d2["raw"])>2 else None},
    "D3": decode_full(d3),
    "D4": decode_full(d4),
    "E1": decode_full(e1),
    "E2": {**e2, "success": e2["raw"][0]=="1" if len(e2["raw"])>0 else None,
           "revert": e2["raw"][1]=="1" if len(e2["raw"])>1 else None,
           "gas_final": int(e2["raw"][2]) if len(e2["raw"])>2 else None},
    "E3": decode_full(e3),
    "two_item_contrast": {
        **two,
        "success": two["raw"][0]=="1" if two["raw"] else None,
        "payload_size": int(two["raw"][1]) if len(two["raw"])>1 else None,
        "slot0_tag": int(two["raw"][2]) if len(two["raw"])>2 else None,
        "head": int(two["raw"][3]) if len(two["raw"])>3 else None,
        "tail": int(two["raw"][4]) if len(two["raw"])>4 else None,
    },
}

top_ok = top[0] == "true" if top else False
# Structural checks for persistent claim
d1s = steps["D1"]
persistent_shape = (
    d1s.get("success") is True
    and d1s.get("head") == 64
    and d1s.get("tail") == 70
    and d1s.get("count") == 0
    and d1s.get("slot0_tag") == 1
    and d1s.get("payload_size") == 64 * 184
)
two_c = steps["two_item_contrast"]
two_is_reset = two_c.get("head") == 0 and two_c.get("tail") == 0

ok = top_ok and persistent_shape and two_is_reset and all(
    steps[k].get('ok') == 'true' for k in ['D1','D2','D3','D4','E1','E2','E3']
) and two_c.get('ok') == 'true'

report = {
    "status": "testé" if ok else "ouvert",
    "label": "testé",
    "label_note_fr": (
        "Traces finies #eval sous EvmRunner/Ξ = testé. "
        "Ce n'est PAS prouvé ∀. Two-item full drain ≠ cycle pointeurs persistants."
    ),
    "is_evm_xi": bool(ok),
    "is_forall_proof": False,
    "plane": "Eip8282.Audit.EvmRunner → EvmYul.EVM.Ξ",
    "lean_exit_code": ec,
    "evmyul_pin": "b62586650b4f96cc6da25f36574aaa8f329a6420",
    "cycle_kind": "nonempty_after_partial_drain_persistent_inhibition",
    "distinction_fr": (
        "Drain à 2 éléments + inhibit remet (HEAD,TAIL)=(0,0) — reset complet, "
        "pas un cycle de pointeurs persistants. "
        "Ici file deposit 70 > cap 64: après system calldata non vide, "
        "HEAD=64 TAIL=70 COUNT=0 EXCESS=INHIBITOR (file encore non vide sous inhibition)."
    ),
    "initial_images": {
        "depositQueue70": {"excess": 100, "count": 5, "head": 0, "tail": 70},
        "exitQueue20": {"excess": 100, "count": 5, "head": 0, "tail": 20},
    },
    "persistentInhibitionCycleOk": top[0] if top else None,
    "steps": steps,
    "assertions_tested": {
        "D1_head_tail_nonempty_under_inhibitor": persistent_shape,
        "D2_user_reverts_while_inhibited_nonempty": steps["D2"].get("ok") == "true",
        "D3_drain_rest_and_clear": steps["D3"].get("ok") == "true",
        "E1_exit_partial_inhibit": steps["E1"].get("ok") == "true",
        "two_item_full_drain_is_not_persistent": two_is_reset and two_c.get("ok") == "true",
    },
    "finite": True,
    "claims_2_64_wrap": False,
    "nowrap_as_premise": False,
    "tail_lt_2_64_convenience": False,
    "not_python_simulator": True,
    "prior_two_item_receipt": "xi-inhibition-receipt.json (full reset only; relabeled testé not prouvé ∀)",
    "timestamp_utc": datetime.now(timezone.utc).isoformat(),
    "log": str(log_path),
    "vals_parsed_count": len(vals),
}
receipt_path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
print("WROTE", receipt_path, "ok=", ok, "top=", top, "D1 head/tail", d1s.get("head"), d1s.get("tail"))
print("persistent_shape", persistent_shape, "two_reset", two_is_reset)
raise SystemExit(0 if ok else 6)
PY
