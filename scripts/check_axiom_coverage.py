#!/usr/bin/env python3
r"""Check that every Lean declaration named by the blueprint has an axiom trace.

The blueprint may put several declarations in one ``\lean{...}`` command and
may wrap that command across lines. The axiom-report source uses one
``#print axioms`` command per declaration. Extra report entries are allowed:
the report intentionally tracks some supporting API beyond the blueprint.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BLUEPRINT = ROOT / "blueprint" / "src" / "content.tex"
AXIOM_SOURCE = ROOT / "scripts" / "axiom_report.lean"

LEAN_COMMAND = re.compile(r"\\lean\{([^{}]*)\}", re.DOTALL)
AXIOM_COMMAND = re.compile(
    r"^\s*#print\s+axioms\s+([^\s-]+)\s*(?:--.*)?$", re.MULTILINE
)
TEX_COMMENT = re.compile(r"(?<!\\)%[^\n]*")


def blueprint_declarations(source: str) -> set[str]:
    declarations: set[str] = set()
    source = TEX_COMMENT.sub("", source)
    for match in LEAN_COMMAND.finditer(source):
        for raw_name in match.group(1).split(","):
            name = "".join(raw_name.split())
            if name:
                declarations.add(name)
    return declarations


def axiom_declarations(source: str) -> set[str]:
    return {match.group(1) for match in AXIOM_COMMAND.finditer(source)}


def main() -> int:
    try:
        blueprint_source = BLUEPRINT.read_text(encoding="utf-8")
        axiom_source = AXIOM_SOURCE.read_text(encoding="utf-8")
    except OSError as error:
        print(f"axiom coverage check could not read an input: {error}", file=sys.stderr)
        return 2

    blueprint = blueprint_declarations(blueprint_source)
    tracked = axiom_declarations(axiom_source)

    if not blueprint:
        print(
            f"axiom coverage check found no \\lean declarations in {BLUEPRINT}",
            file=sys.stderr,
        )
        return 2
    if not tracked:
        print(
            f"axiom coverage check found no #print axioms commands in {AXIOM_SOURCE}",
            file=sys.stderr,
        )
        return 2

    missing = sorted(blueprint - tracked)
    if missing:
        print(
            "axiom coverage check failed: blueprint declarations missing from "
            "scripts/axiom_report.lean:",
            file=sys.stderr,
        )
        for name in missing:
            print(f"  - {name}", file=sys.stderr)
        print(
            "Add one '#print axioms <declaration>' command for each missing name "
            "and regenerate audit/axiom-report.txt.",
            file=sys.stderr,
        )
        return 1

    extras = len(tracked - blueprint)
    print(
        f"axiom coverage check passed: {len(blueprint)} blueprint declarations "
        f"are tracked ({extras} additional report declarations)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
