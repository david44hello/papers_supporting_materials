#!/usr/bin/env python3
"""link.py — replace the `sorry` body of Statements theorems by a link to a proved theorem, and add imports.
Usage: scripts/link.py <module.to.import>[,<module2>...] <claim>=<proof> [<claim>=<proof> ...]
       <proof> a bare name  -> body `:= by apply <name> <;> assumption`
       <proof> with spaces  -> body `:=\n  <proof>` (an exact proof term, e.g. "foo_proved a b ha")
       scripts/link.py --test
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
"""
import sys
from pathlib import Path
P = Path(__file__).resolve().parent.parent / "Smale" / "Paper" / "Statements.lean"
ANCHOR = "import Smale.Defs.Conditions\n"
SORRY_BODY = ":= by\n  sorry"


def add_imports(s, modules):
    for module in modules:
        imp = f"import {module}\n"
        if imp in s:
            continue
        if ANCHOR not in s:
            sys.exit(f"LINK FAILED: import anchor {ANCHOR!r} not found")
        s = s.replace(ANCHOR, ANCHOR + imp, 1)
    return s


def link_one(s, claim, proof):
    i = s.find(f"theorem {claim} ")
    if i == -1:
        i = s.find(f"theorem {claim}\n")
    if i == -1:
        sys.exit(f"LINK FAILED: no theorem {claim}")
    j = s.find(SORRY_BODY, i)
    nxt = s.find("\ntheorem ", i + 1)
    if j == -1 or (nxt != -1 and j > nxt):
        sys.exit(f"LINK FAILED: {claim} has no sorry body (already linked?)")
    body = f":=\n  {proof}" if " " in proof else f":= by\n  apply {proof} <;> assumption"
    return s[:j] + body + s[j + len(SORRY_BODY):]


def main_link(modules, pairs):
    s = add_imports(P.read_text(), modules)
    for pair in pairs:
        claim, proof = pair.split("=", 1)
        s = link_one(s, claim, proof)
        print(f"linked {claim} -> {proof}")
    P.write_text(s)


def main_test():
    sample = ANCHOR + "\ntheorem a (x : Nat) : x = x := by\n  sorry\n\ntheorem b : True := by\n  sorry\n"
    out = link_one(link_one(add_imports(sample, ["M.N"]), "a", "rfl_proved x"), "b", "trivial")
    assert "import M.N\n" in out and ":=\n  rfl_proved x" in out and "apply trivial <;> assumption" in out, out
    assert "sorry" not in out
    print("PASS: link.py self-test")


def main():
    if sys.argv[1:] == ["--test"]:
        return main_test()
    main_link(sys.argv[1].split(","), sys.argv[2:])


if __name__ == "__main__":
    main()
