#!/usr/bin/env python3
"""audit.py — the coverage-and-assumptions table for every paper claim, produced by Lean itself.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

For every `theorem` in Smale/Paper/Statements.lean and Smale/Paper/Unconditional.lean this script asks Lean (`#print axioms`) which axioms the proof
depends on, and classifies it:
  PROVED            only Lean's three standard axioms (propext, Classical.choice, Quot.sound)
  PROVED-ASSUMING-(R) proved (as above) from an explicit hypothesis `CondRdata` or `CheckR`: fact (R) in two forms
                    (condR_proved proves the first; a program checks the second) — counted apart, so no reader takes such a
                    row as unconditional
  OPEN              depends on sorryAx (a proof gap somewhere below it; fails loudly)
  VIOLATION         any other axiom (forbidden; fails loudly)
A row whose docstring says RETIRED is proved but is no longer a claim of the paper: it is kept and counted apart.
Usage: scripts/audit.py            (writes AUDIT.md, exits 1 on any VIOLATION or OPEN)
       scripts/audit.py --test     (self-test of the parser)
"""
import os
import re
import subprocess
import sys
from pathlib import Path

PROJECT = Path(__file__).resolve().parent.parent
STATEMENTS = PROJECT / "Smale" / "Paper" / "Statements.lean"
UNCONDITIONAL = PROJECT / "Smale" / "Paper" / "Unconditional.lean"  # the rows above Statements: fact (R), and the main theorems from it
AUDIT_LEAN = PROJECT / "Smale" / "Audit.lean"
AUDIT_MD = PROJECT / "AUDIT.md"
CONDITIONS = PROJECT / "Smale" / "Defs" / "Conditions.lean"  # computer-checked claims (defs) live here
AUDIT_NOTES = PROJECT / "AUDIT_NOTES.md"  # hand-written route/not-formalized notes, appended verbatim
CORE = os.environ.get("SMALE_CORE", "1")
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
NAMESPACE = "Smale"
LABEL = {"CondRdata": "(R)", "CheckR": "(R)"}  # display label of fact (R) (default: its name)
# Rows that name a fact in their signature without assuming it (the implication itself, or the proof of it): plain status.
IMPLICATIONS = {"condR_of_checkR": "the claim is the implication CheckR -> CondRdata itself",
                "condR_proved": "the claim is CondRdata itself, proved"}
ASSUMED_NOTE = ("**Conditional rows.** A row marked PROVED-ASSUMING-(R) takes fact (R) of Theorem 5.1 as an explicit "
                "hypothesis (`CondRdata`, or `CheckR`, the computer-checked statement of (R), for H; the program's F for "
                "L·H is L^34 times it). `CondRdata` is proved, in the row `condR_proved`, so the paper's main results, Theorem 1.1, "
                "Theorem 5.1 and Corollary 5.4, and the first sentence of Remark 5.2, also have rows with no hypothesis: `thm_1_1`, "
                "`thm_5_1`, `cor_5_4`, `rem_5_2_zeros_outside_proved`. `CheckR` is "
                "checked by computer, NOT proved in Lean (table \"Computer-checked\" below).")
RETIRED_MARK = "RETIRED"
RETIRED_NOTE = ("**Retired rows.** A row marked RETIRED is proved but is no longer a claim of the paper (its sentence was removed); it is kept and counted apart.")
TRUST_NOTE = ("**Trust.** The project declares no axiom: every row's `#print axioms` lists only Lean's three standard axioms. "
              "No Lean proof of a theorem of the paper takes a result of another paper as given. The first sentence of each of Jatar and Ng's "
              "Propositions 3.1 and 4.2, and the \"if\" direction of Dieudonne's criterion, which is all the paper uses of them, "
              "are proved in this project (Smale/Proofs/JN31Assembly.lean, Smale/Proofs/JNAssembly.lean, "
              "Smale/Proofs/DieudonneIf.lean), and those proofs quote their sources verbatim. Three rows state the paper's own "
              "deduction from another paper's result, with that result as their hypothesis: intro_smale_K4, "
              "intro_conjecture_false, intro_AC_degree. The Riemann mapping theorem is Smale/Vendor/RiemannMap.lean, ported from "
              "Mathlib's open draft pull request #33505 by Yury Kudryashov (Apache License 2.0), its changes listed at the top "
              "of that file; Lean checks it like every other file.")


def parse_statements(text, assumed_names):
    """Return [(name, doc_first_line, assumed)] for every top-level theorem, in file order; `assumed` labels the
    computer-checked names (`assumed_names`) that occur ANYWHERE in the theorem's signature, "" if none."""
    items = []
    for block in re.finditer(r"(/--((?:(?!-/).)*?)-/\s*)?^theorem\s+(\w+)(.*?):=", text, re.S | re.M):
        doc = " ".join((block.group(2) or "").split())
        used = {n for n in assumed_names if re.search(r"\b" + re.escape(n) + r"\b", block.group(4))}
        assumed = ", ".join(sorted({LABEL.get(n, n) for n in used}))
        items.append((block.group(3), doc.replace("|", "\\|"), assumed))  # a raw | would split the table cell
    return items


def check_no_wrappers(sources, assumed_names):
    """Fail loudly if a def other than the computer-checked defs themselves mentions one of them: a wrapper def
    would hide the hypothesis from the signature scan of parse_statements."""
    for path, text in sources:
        for block in re.finditer(r"^(?:noncomputable\s+)?def\s+(\w+)(.*?)(?=^\S|\Z)", text, re.S | re.M):
            name, body = block.group(1), block.group(2)
            hits = {n for n in assumed_names if n != name and re.search(r"\b" + re.escape(n) + r"\b", body)}
            if hits:
                sys.exit(f"AUDIT FAILED: def {name} in {path} mentions {sorted(hits)}: a wrapper hides (R)")


def write_audit_lean(names):
    lines = ["-- GENERATED by scripts/audit.py — do not edit.", "import Smale.Paper.Unconditional", ""]
    lines += [f"#print axioms {NAMESPACE}.{name}" for name in names]
    content = "\n".join(lines) + "\n"
    # Rewrite only on change: an identical rewrite leaves Lake's (content-hash) build fresh but makes the source
    # newer than its olean, and scripts/kernel_replay.sh then refuses the run as stale.
    if not AUDIT_LEAN.exists() or AUDIT_LEAN.read_text() != content:
        AUDIT_LEAN.write_text(content)


def run_lean():
    env = dict(os.environ, LEAN_NUM_THREADS="1")
    proc = subprocess.run(["nice", "-n", "19", "lake", "build", "Smale.Audit"],
                          cwd=PROJECT, capture_output=True, text=True, env=env)
    if proc.returncode != 0:
        sys.exit("AUDIT FAILED: Lean reported an error:\n" + proc.stdout + proc.stderr)
    return proc.stdout + proc.stderr


def parse_axioms(output, names):
    """Map each theorem name to its set of axioms, from `#print axioms` output."""
    result = {}
    pattern = re.compile(r"'([\w.]+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", re.S)
    for match in pattern.finditer(output):
        full = match.group(1)
        short = full.removeprefix(NAMESPACE + ".")
        axioms = {a.strip() for a in (match.group(2) or "").replace("\n", " ").split(",") if a.strip()}
        result[short] = axioms
    missing = [n for n in names if n not in result]
    if missing:
        sys.exit(f"AUDIT FAILED: no #print axioms output for {missing}")
    return result


def classify(axioms):
    if axioms - STANDARD - {"sorryAx"}:
        return "VIOLATION"
    if "sorryAx" in axioms:
        return "OPEN"
    return "PROVED"


def render(items, axioms_by_name):
    rows = ["| # | Lean name | Paper claim | Status |", "|---|---|---|---|"]
    counts = {}
    for idx, (name, doc, assumed) in enumerate(items, 1):
        axioms = axioms_by_name[name]
        status = classify(axioms)
        cell = status
        if assumed and name not in IMPLICATIONS and status == "PROVED":
            status = f"PROVED-ASSUMING-{assumed}"
            cell = f"PROVED ASSUMING {assumed} — {assumed} is a hypothesis of this row; see the note on conditional rows"
        if RETIRED_MARK in doc:
            cell = f"{status} ({RETIRED_MARK}, not a paper claim)"
            status = f"{status} ({RETIRED_MARK})"
        counts[status] = counts.get(status, 0) + 1
        rows.append(f"| {idx} | `{name}` | {doc} | {cell} |")
    summary = ", ".join(f"{k}: {v}" for k, v in sorted(counts.items()))
    return summary, "\n".join(rows), counts


def parse_computer_checked(text):
    """Return [(name, doc_first_line)] for every `def <name> : Prop` whose docstring starts with **COMPUTER-CHECKED:
    a claim of the paper stated exactly in Lean but checked only by a computer program (never counted as proved)."""
    items = []
    for block in re.finditer(r"/--\s*(\*\*COMPUTER-CHECKED(?:(?!-/).)*?)-/\s*^def\s+(\w+)\s*:\s*Prop", text, re.S | re.M):
        items.append((block.group(2), " ".join(block.group(1).split()).replace("|", "\\|")))
    return items


def render_computer_checked(items):
    if not items:
        return ""
    rows = ["## Computer-checked, NOT proved in Lean", "",
            "Each row is a claim of the paper stated exactly in Lean (a `Prop`, not assumed by any proof); a computer "
            "program checks it. Rows that take it take it as an explicit hypothesis; none needs it, see `condR_proved`.", "",
            "| # | Lean name | Paper claim and where it is checked | Status |", "|---|---|---|---|"]
    rows += [f"| C{idx} | `{name}` | {doc} | checked by computer, NOT proved in Lean |"
             for idx, (name, doc) in enumerate(items, 1)]
    return "\n".join(rows)


def parse_not_stated(text):
    """Return [(label, kind, text)] for the items `(Nx) [kind] ...` of the `/-! ## NOT stated` block of
    Statements.lean; fails loudly on an item without a [kind]."""
    block = re.search(r"/-! ## NOT stated[^\n]*\n(.*?)-/", text, re.S)
    if not block:
        sys.exit("AUDIT FAILED: no `/-! ## NOT stated` block in Statements.lean")
    body = block.group(1)
    items = [(m.group(1), m.group(2), " ".join(m.group(3).split()).replace("|", "\\|"))
             for m in re.finditer(r"^\((N\w+)\)\s*\[([^\]]+)\]\s*(.*?)(?=^\(N\w+\)|\Z)", body, re.S | re.M)]
    if len(items) != len(re.findall(r"^\(N\w+\)", body, re.M)):
        sys.exit("AUDIT FAILED: a NOT-stated item has no [kind] tag")
    return items


def render_not_stated(items):
    rows = ["## Sentences of the paper NOT stated as Lean theorems", "",
            "Every sentence of the paper that has no Lean row is listed here, with its tex lines and the reason "
            "(from the list at the end of Smale/Paper/Statements.lean; each is listed for the author's review). "
            "\"now stated\" items name the rows that cover them now.", "",
            "| # | Kind | tex lines, sentence, and reason |", "|---|---|---|"]
    rows += [f"| {label} | {kind} | {text} |" for label, kind, text in items]
    return "\n".join(rows)


def claim_text():
    """The two files whose theorems are the rows of the table."""
    return STATEMENTS.read_text() + "\n" + UNCONDITIONAL.read_text()


def audit_failure(counts):
    """Why the audit fails, or None. A status may carry a mark, as in "OPEN (RETIRED)": a retired row fails like any other."""
    if any(group.startswith("VIOLATION") for group in counts):
        return "AUDIT FAILED: a forbidden axiom appears (VIOLATION rows)."
    if any(group.startswith("OPEN") for group in counts):
        return "AUDIT FAILED: a proof gap appears (OPEN rows: sorryAx)."
    return None


def main_audit():
    text = STATEMENTS.read_text()
    computer = parse_computer_checked(text) + parse_computer_checked(CONDITIONS.read_text())
    assumed_names = {n for n, _ in computer} | {"CondRdata"}
    check_no_wrappers([(str(f.relative_to(PROJECT)), f.read_text()) for f in sorted((PROJECT / "Smale").rglob("*.lean"))],
                      assumed_names)
    items = parse_statements(claim_text(), assumed_names)
    names = [n for n, _, _ in items]
    write_audit_lean(names)
    axioms_by_name = parse_axioms(run_lean(), names)
    summary, table, counts = render(items, axioms_by_name)
    computer_md = render_computer_checked(computer)
    not_stated_md = render_not_stated(parse_not_stated(text))
    notes = AUDIT_NOTES.read_text() if AUDIT_NOTES.exists() else ""
    AUDIT_MD.write_text(f"# AUDIT — every claim of the paper, as Lean sees it\n\nGenerated by scripts/audit.py from "
                        f"`#print axioms`. Summary: {summary}; COMPUTER-CHECKED: {len(computer)}.\n\n{TRUST_NOTE}\n\n"
                        f"{ASSUMED_NOTE}\n\n{RETIRED_NOTE}\n\n{table}\n\n{computer_md}\n\n{not_stated_md}\n\n{notes}")
    n_retired = sum(count for group, count in counts.items() if RETIRED_MARK in group)
    print(f"AUDIT: {len(items) - n_retired} paper claims (+ {n_retired} retired rows). {summary}. "
          f"COMPUTER-CHECKED: {len(computer)}. Table: {AUDIT_MD}")
    failure = audit_failure(counts)
    if failure:
        sys.exit(failure)


def main_test():
    sample = "/-- **Lemma 9.9**: hello. -/\ntheorem foo : True := trivial\ntheorem bar : True := sorry\n"
    names = {"CondRdata", "CheckR"}
    assert parse_statements(sample, names) == [("foo", "**Lemma 9.9**: hello.", ""), ("bar", "", "")], \
        parse_statements(sample, names)
    cond = "/-- From (R). -/\ntheorem baz (hR : CondRdata) (n : Nat) :\n    True := trivial\ntheorem qux (h : CheckR) : True := trivial\n"
    assert parse_statements(cond, names) == [("baz", "From (R).", "(R)"), ("qux", "", "(R)")], parse_statements(cond, names)
    probes = ("theorem t1 : CondRdata → True := fun _ => trivial\ntheorem t2 (h h2 : CheckR) : True := trivial\n"
              "theorem t3 (h : CheckR ∧ True) : True := trivial\ntheorem t4 {h : CondRdata} : True := trivial\n"
              "theorem t5 (h : CondC Q) : True := trivial\n")
    assert [a for _, _, a in parse_statements(probes, names)] == ["(R)", "(R)", "(R)", "(R)", ""], \
        parse_statements(probes, names)
    check_no_wrappers([("ok.lean", "def CheckR : Prop :=\n  True\ndef CondRdata : Prop := True\n")], names)
    try:
        check_no_wrappers([("bad.lean", "def Hidden : Prop :=\n  CheckR\n")], names)
        raise AssertionError("a wrapper def was not caught")
    except SystemExit:
        pass
    ns = "/-! ## NOT stated (x)\n(N1) [cited] tex l.1: a.\n     more.\n(N2b) [numerical only] tex l.2: b.\n-/\n"
    assert parse_not_stated(ns) == [("N1", "cited", "tex l.1: a. more."), ("N2b", "numerical only", "tex l.2: b.")], \
        parse_not_stated(ns)
    out = ("'Smale.foo' depends on axioms: [propext,\n Classical.choice]\n"
           "'Smale.bar' depends on axioms: [sorryAx]\n'Smale.baz' does not depend on any axioms\n")
    got = parse_axioms(out, ["foo", "bar", "baz"])
    assert classify(got["foo"]) == "PROVED"
    assert classify(got["bar"]) == "OPEN"
    assert classify(got["baz"]) == "PROVED"
    assert classify({"propext", "evil"}) == "VIOLATION"
    assert classify({"sorryAx", "evil"}) == "VIOLATION"
    assert classify({"propext", "Smale.Cited.x"}) == "VIOLATION"  # no axiom of any name is allowed now
    cc = ("/-- **COMPUTER-CHECKED, NOT PROVED IN LEAN.** big check. -/\ndef CheckR : Prop :=\n  True\n"
          "/-- ordinary. -/\ndef CondR : Prop := True\n/-- **COMPUTER-CHECKED** x. -/\ndef notProp (n : Nat) : Nat := n\n")
    assert parse_computer_checked(cc) == [("CheckR", "**COMPUTER-CHECKED, NOT PROVED IN LEAN.** big check.")], \
        parse_computer_checked(cc)
    assert parse_statements(cc, names) == []
    _, table, counts = render([("ret", "C6, RETIRED, not a claim", "")], {"ret": {"propext"}})
    assert counts == {"PROVED (RETIRED)": 1}, counts
    assert "| `ret` | C6, RETIRED, not a claim | PROVED (RETIRED, not a paper claim) |" in table, table
    assert audit_failure(counts) is None
    for axioms, word in (({"sorryAx"}, "gap"), ({"evil"}, "forbidden")):
        for doc, assumed in (("claim", ""), ("C6, RETIRED, not a claim", ""), ("claim", "(R)")):
            failure = audit_failure(render([("row", doc, assumed)], {"row": axioms})[2])
            assert failure and word in failure, (axioms, doc, assumed, failure)
    # condR_proved has CondRdata in its signature and assumes nothing; a row that takes it as a hypothesis still does.
    both = "/-- d. -/\ntheorem condR_proved : CondRdata := x\n/-- e. -/\ntheorem other (h : CondRdata) : True := y\n"
    items = parse_statements(both, {"CondRdata"})
    _, table, counts = render(items, {"condR_proved": {"propext"}, "other": {"propext"}})
    assert counts == {"PROVED": 1, "PROVED-ASSUMING-(R)": 1}, counts
    assert "| `condR_proved` | d. | PROVED |" in table, table
    print("PASS: audit.py self-test")


def main():
    if sys.argv[1:] == ["--test"]:
        main_test()
    elif not sys.argv[1:]:
        main_audit()
    else:
        sys.exit("Usage: scripts/audit.py [--test]")


if __name__ == "__main__":
    main()
