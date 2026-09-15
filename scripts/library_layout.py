#!/usr/bin/env python3
"""Check and generate Lake's explicit correctness, candidate and test partition."""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
START = "-- BEGIN GENERATED LIBRARY PARTITION\n"
END = "-- END GENERATED LIBRARY PARTITION\n"
REGISTERED = "Eip8282.Audit.Integrator.DirectGuarantees"
LEGACY = tuple(
    "Eip8282.Audit." + name
    for name in (
        "XiTransport", "EntryReach", "SymExec", "Model", "Correspondence",
        "EvmRunner", "Step", "UniversalBoundary", "Guarantees", "WellFormed",
        "Reachable", "Represents", "UserXiCorrespondence",
    )
)


def closure(roots: list[str], edges: dict[str, set[str]]) -> set[str]:
    seen: set[str] = set()
    pending = list(roots)
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        if name not in edges:
            if name.startswith("Eip8282."):
                raise SystemExit(f"Missing local module: {name}")
            continue
        seen.add(name)
        pending.extend(edges[name])
    return seen


def layout() -> tuple[dict[str, Path], dict[str, set[str]]]:
    files = {
        ".".join(path.relative_to(ROOT).with_suffix("").parts): path
        for path in (ROOT / "Eip8282").rglob("*.lean")
    }
    edges = {
        name: set(re.findall(r"^import\s+(\S+)", path.read_text(), re.MULTILINE))
        for name, path in files.items()
    }
    for name, dependencies in edges.items():
        missing = {d for d in dependencies if d.startswith("Eip8282.") and d not in files}
        if missing:
            raise SystemExit(f"{name} imports missing local modules: {sorted(missing)}")

    core = closure([REGISTERED], edges)
    forbidden = {
        name for name in core
        if any(name == prefix or name.startswith(prefix + ".") for prefix in LEGACY)
    }
    if forbidden:
        raise SystemExit(f"Superseded layer re-entered correctness core: {sorted(forbidden)}")

    roots = json.loads((ROOT / "audit/delivery-roots.json").read_text())["roots"]
    unused = set(files) - closure(roots, edges)
    if unused:
        raise SystemExit(f"Unneeded modules outside delivery roots: {sorted(unused)}")

    tests = {
        name for name in files
        if name.startswith("Eip8282.Tests.") or name == "Eip8282.Audit.Trust"
    }
    if core & tests:
        raise SystemExit("Correctness core must not import tests")
    candidates = set(files) - core - tests
    for name in candidates:
        if edges[name] & tests:
            raise SystemExit(f"Candidate {name} imports tests")
    return files, {"Eip8282": core, "Eip8282Candidates": candidates, "Eip8282Tests": tests}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    files, groups = layout()
    output = START
    for name, names in groups.items():
        output += "\n@[default_target]\n" if name == "Eip8282" else "\n"
        output += f"lean_lib «{name}» where\n  globs := #[\n"
        output += ",\n".join(f"    .one `{n}" for n in [name] + sorted(names))
        output += "\n  ]\n  moreLeanArgs := ffiDynlibs\n"
    output += "\n" + END

    path = ROOT / "lakefile.lean"
    old = path.read_text()
    new = old[:old.index(START)] + output + old[old.index(END) + len(END):]
    if args.write:
        path.write_text(new)
    elif old != new:
        raise SystemExit("Library partition changed; run python3 scripts/library_layout.py --write")
    for name, names in groups.items():
        lines = sum(len(files[n].read_text().splitlines()) for n in names)
        print(f"{name}: {len(names)} modules, {lines:,} lines")


if __name__ == "__main__":
    main()
