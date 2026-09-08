#!/usr/bin/env python3
"""Independent integer/word oracle for the pinned EIP-8282 fee loop."""

import argparse
import hashlib
import json
from pathlib import Path

MODULUS = 1 << 256
FRACTION = 17


def fake_exponential(excess: int, word: bool) -> dict:
    accumulator, output, iteration = FRACTION, 0, 1
    rows = []
    while accumulator > 0:
        raw_output = output + accumulator
        raw_product = excess * accumulator
        raw_denominator = iteration * FRACTION
        output = raw_output % MODULUS if word else raw_output
        product = raw_product % MODULUS if word else raw_product
        denominator = raw_denominator % MODULUS if word else raw_denominator
        next_accumulator = product // denominator
        next_iteration = (iteration + 1) % MODULUS if word else iteration + 1
        if raw_output >= MODULUS or raw_product >= MODULUS or raw_denominator >= MODULUS:
            rows.append({
                "iteration": iteration,
                "accumulator": accumulator,
                "raw_output": raw_output,
                "raw_product": raw_product,
                "raw_denominator": raw_denominator,
                "stored_output": output,
                "stored_product": product,
                "stored_denominator": denominator,
            })
        accumulator, iteration = next_accumulator, next_iteration
    return {
        "iterations": iteration - 1,
        "output_before_division": output,
        "fee": output // FRACTION,
        "overflow_events": rows,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    pins = {}
    for kind in ("builder_deposits", "builder_exits"):
        pins[kind] = {}
        for image in ("ctor", "main"):
            p = args.repo / "pinned" / "bytecode" / kind / f"{image}.hex"
            raw = bytes.fromhex(p.read_text().strip().removeprefix("0x"))
            pins[kind][image] = {"path": str(p.relative_to(args.repo)), "bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}
    cases = {}
    for excess in (1608, 1620, 2893):
        cases[str(excess)] = {
            "full_integer": fake_exponential(excess, False),
            "evm_word": fake_exponential(excess, True),
        }
    fee_1620 = cases["1620"]["evm_word"]["fee"]
    print(json.dumps({
        "constants": {"minimum_fee": 1, "fraction": FRACTION, "word_modulus": str(MODULUS)},
        "pins": pins,
        "cases": cases,
        "underpayment_1620": {"required_fee": fee_1620, "callvalue": fee_1620 - 1, "difference_wei": 1},
    }, indent=2))


if __name__ == "__main__":
    main()
