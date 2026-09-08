#!/usr/bin/env python3
"""Fail closed if the saved direct-fee observations differ from expectations."""

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "output" / "direct-fees"


def main() -> None:
    arithmetic = json.loads((OUT / "arithmetic.json").read_text())
    expected_hashes = {
        ("builder_deposits", "ctor"): "166510c29d9ea96c80b854e86743377de1cadccaef62a620c684641fb9267f61",
        ("builder_deposits", "main"): "2c49dcf745b1304f3dac0ea7487eae6d8fd07812ada980d542f79e8e5e53eb8d",
        ("builder_exits", "ctor"): "37d89175964e696bfed69ad5309c0147bdb7af8b11a25ea1ba557d7adb9d50b8",
        ("builder_exits", "main"): "c889ed88730d157d192aae28c2dee61324d0df3bd01ff0078386808b4adb27aa",
    }
    for (kind, image), digest in expected_hashes.items():
        assert arithmetic["pins"][kind][image]["sha256"] == digest

    expected = {
        "1608": (257, 119989470856188333158662703311252429458084),
        "1620": (258, 243056981773394081136356734028591621772929),
    }
    for excess, (iterations, fee) in expected.items():
        for mode in ("full_integer", "evm_word"):
            assert arithmetic["cases"][excess][mode]["iterations"] == iterations
            assert arithmetic["cases"][excess][mode]["fee"] == fee
    full = arithmetic["cases"]["2893"]["full_integer"]
    word = arithmetic["cases"]["2893"]["evm_word"]
    assert (full["iterations"], word["iterations"]) == (462, 457)
    assert full["fee"] == 80668064690921409049190791237320678716946849613533250306370202067869504081
    assert word["fee"] == 32087365885911168062721653499988857431024628719292649881555161070975172167
    assert word["overflow_events"][0]["iteration"] == 167

    lines = [line for line in (OUT / "evm.txt").read_text().splitlines() if line.strip()]
    assert len(lines) == 8
    assert all(fragment in lines[0] for fragment in
               ("kind=deposit-ctor", "status=success", "gas_used=some 136",
                "output_size=628", "output_equals_runtime=true", "slot0=some 0"))
    assert all(fragment in lines[1] for fragment in
               ("kind=exit-ctor", "status=success", "gas_used=some 22211",
                "output_size=458", "output_equals_runtime=true",
                f"slot0=some {(1 << 256) - 1}"))
    assert all(fragment in lines[2] for fragment in
               ("status=success", f"output_word=some {expected['1608'][1]}", "gas_used=some 26781"))
    assert all(fragment in lines[3] for fragment in
               ("status=success", f"output_word=some {expected['1620'][1]}", "gas_used=some 26868"))
    assert all(fragment in lines[4] for fragment in ("status=revert", "gas_used=some 26849"))
    assert all(fragment in lines[5] for fragment in ("status=success", "gas_used=some 96582"))
    for line in lines[6:]:
        assert f"output_word=some {word['fee']}" in line
        assert "gas_used=some 44181" in line
    print("direct-fees verification: PASS")


if __name__ == "__main__":
    main()
