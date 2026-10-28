#!/usr/bin/env python3
"""audit.py — the coverage-and-assumptions table for every paper claim, produced by Lean itself.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

For every `theorem` in NagataHigman/Paper/Statements.lean this script asks Lean (`#print axioms`) which axioms the proof
depends on, and classifies it:
  PROVED            only Lean's three standard axioms (propext, Classical.choice, Quot.sound)
  PROVED-FROM-CITED standard axioms plus NagataHigman.Cited.* axioms (the paper's cited results) — listed by name
  PROVED-FROM-TEMP  uses a NagataHigman.Cited.Temp.* axiom: a fact the paper PROVES that Lean has not proved yet — NOT done
  OPEN              depends on sorryAx (a proof gap somewhere below it)
  VIOLATION         any other axiom (forbidden; fails loudly)
Usage: scripts/audit.py            (writes AUDIT.md, exits 1 on any VIOLATION)
       scripts/audit.py --test     (self-test of the parser)
"""
import re
import subprocess
import sys
from pathlib import Path

PROJECT = Path(__file__).resolve().parent.parent
STATEMENTS = PROJECT / "NagataHigman" / "Paper" / "Statements.lean"
AUDIT_LEAN = PROJECT / "NagataHigman" / "Audit.lean"
AUDIT_MD = PROJECT / "AUDIT.md"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
NAMESPACE = "NagataHigman.Paper"
CITED_WHITELIST = {"NagataHigman.Cited.youngSystem_exists", "NagataHigman.Cited.youngSystemC_exists",
                   "NagataHigman.Cited.procesi_formanek"}
TRUST_NOTE = ("**Trust.** Every PROVED-FROM-CITED result is conditional on the three cited statements in "
              "NagataHigman/Cited/, nothing else (scripts/audit.py rejects any other cited axiom): "
              "(1) `youngSystem_exists` (Cited/Classical.lean) — the classical representation theory of S_N in "
              "characteristic 0 as a Young system: (F2) Wedderburn and Fourier inversion [Ja78 Thm 4.12; CST10 Ch. 1], "
              "(T1) the Young basis with Jucys–Murphy eigenvalues [Ju74, OV96], (F7) S^λ' ≅ S^λ ⊗ sgn [Ja78 Thm 6.7]; "
              "(2) `youngSystemC_exists` (Cited/Classical.lean) — the same over ℂ together with Frobenius' theorem in "
              "source form: Res_{A_N} S^λ = V₊ ⊕ V₋ irreducible, non-isomorphic, χ₊ = χ₋ off h(λ) [JK81 §2.5, "
              "Thm 2.5.13]; (3) `procesi_formanek` (Cited/MatrixInvariants.lean) — the theorem of Procesi and Formanek "
              "as stated in [Dr95, Thms 5.3, 5.6] over an algebraically closed field of characteristic 0, used ONLY by "
              "Corollary 1.1 (`cor_1_1`, `cor_1_1_functions`). "
              "Lean neither assumes nor proves branching (F5), Burnside (F6) or the last sentence of (T1) (the v_T with N "
              "in a corner a span the summand S^{λ−a} of the restriction). Where the paper uses them — (F5) in (F4) "
              "l. 241, Lemma 3.1 l. 371 and §4.3 l. 429; (F6) in Lemma 3.1 l. 372 and Lemma 4.2(e) l. 481; the last "
              "sentence of (T1) in §4.3 l. 429-430 — Lean proves the consequence "
              "that the proof needs by another argument (route items 1, 8, 10). The paper's (T3) paragraph is proved FROM the cited splitting (2): "
              "`Gamma_support`, `Gamma_pm` and `Gamma_trace_even` take it as a hypothesis for their one shape λ (the last "
              "two without the Frobenius clause). Every claim on S_N representations is stated for an ARBITRARY Young "
              "system, so PROVED rows hold for Young's seminormal form in particular; that a Young system exists at all is "
              "the cited statement (1), so these rows speak about the paper's blocks I_λ only together with (1). "
              "A PROVED-FROM-TEMP row would rest on a placeholder for a fact the paper proves (namespace "
              "NagataHigman.Cited.Temp); such rows are NOT counted as proved.")
ROUTE_NOTE = ("## Route differences\n\n"
              "PROVED means that Lean proves the paper's STATEMENT. Where the Lean proof takes a different argument from "
              "the paper's text, the paper's own argument there is not what Lean checks. The dependency facts below are "
              "checked by `scripts/route_check.lean` (run by scripts/check.sh). Line numbers: short v1.04 (draft of 20261027, md5 c867caf6).\n\n"
              "1. **Restriction fact in Lemma 3.1 and Lemma 4.1** (l. 370-372, 439-442): the paper uses branching (F5), "
              "Burnside (F6) and (F2) for S_{N−1}, and for Lemma 4.1 the last sentence of (T1) (§4.3 l. 429-430). Lean derives what is needed, span ρ_λ(S_{N−1}) = the commutant of "
              "ρ_λ(J_N), from the Young basis and tableau combinatorics (Okounkov–Vershik route; Proofs/Restriction.lean, "
              "`restriction_of_young`; claim `lem_4_1_span`).\n"
              "2. **(F1)** (l. 207-209): the paper gets L ∈ T from multihomogeneous components; Lean uses the polarization "
              "identity (Proofs/FreeAlgebraLayer.lean, `polarization`).\n"
              "3. **(F3)** (l. 232-235): the paper uses ⟨a, b⟩ = the coefficient of 1 in a·b^∨; Lean computes ⟨a, b⟩ by "
              "Fourier inversion, block by block (Proofs/BlocksOrth.lean).\n"
              "4. **(T3)** (l. 412-416): the paper rescales to Γ² = id; Lean keeps Γ² = d·id with d ≠ 0 and shows Γ = a on "
              "V₊, −a on V₋ with a² = d (Proofs/TwoCorner/GammaC.lean, `gamma_pm`).\n"
              "5. **(F2)** (l. 224): Lean defines e_λ from the Jucys–Murphy elements (Lagrange polynomials, no Young "
              "system) and proves the paper's formula e_λ = (dim S^λ/N!) Σ χ_λ(σ) σ (`F2_idem_coeff`).\n"
              "6. **Proposition 2.1, step (6), the displayed formula** (l. 325-328): `prop_2_1_step6_formula_arcs` proves "
              "it with the paper's names (a = ξ, v_i = Arc_i, b = ζ, any numbering of the arcs). The proof compares τ "
              "off K with the cycle of its arcs (`Arcs.coeff_fullCycle`, `BlockConfig.coeff_eq`), not by summing over "
              "the bijection θ of steps (5)-(6) (Proofs/Step6Arcs.lean).\n"
              "7. **Proposition 2.1, steps (3)-(6), on the path to Proposition 2.1 and Theorems A, B** (l. 296-328): "
              "`forward_block_lemma` (Proofs/Arcs.lean) cuts the cycle word of an N-cycle at the points of K into the "
              "arcs and compares coefficients directly; its sign fact is that two N-cycles have the same sign "
              "(`Arcs.sign_of_isFullCycle`), not sgn π = sgn τ̄ · sgn(τ̄∘π). The paper's step (4) (τ̄, first return), "
              "step (5) (sign) and step (6) (bijection θ) are proved as separate claims that are not on this path.\n"
              "8. **(F4)** (l. 239-242): Lean shows ρ_λ(E) ≠ 0 ⟺ ℓ(λ) ≥ n+1 from the Young basis "
              "(`rhoAlg_altGen_ne_zero_iff`), not by restriction to S_{n+1} and iterated branching (F5).\n"
              "9. **Proposition 2.1, step (7)** (l. 342-343): Lean shows I^⊥ ⊆ A by a trace argument "
              "(`rhoAlg_eq_zero_of_pairing`), not by counting dimensions.\n"
              "10. **Lemma 4.2(e)** (l. 481): ρ(F[S_N]) = End(S^ν) comes from the cited Wedderburn clause "
              "(`rhoAlg_surjective`), not from Burnside (F6).\n\n"
              "Same route as the paper (checked): the §4.1 field step (l. 384-385) is Proposition 2.1 + (F1), as in the paper: W_{n,m} is spanned by the (F1) elements, whose word coordinates are integers, so its dimension does not depend on the field (Proofs/FieldStep.lean). `lem_4_2` and `lem_4_3` use the chain (a)-(e) of Lemma 4.2 "
              "(`lem_4_2_d_nu`, `lem_4_2_e_proved`); step (d) is the paper's argument c_T(N−1)(c_T(N) − c_T(N−1)) = −2, "
              "D = ½ρ(J_{N−1}); a second proof (ρ(s) = −Y_N Y_{N−1} Y_N, Proofs/TwoCorner/Lemma42.lean) is used by no "
              "claim. Lemma 4.1 passes through Q₊MQ₊ = 0 = Q₋MQ₋ and \"M maps each eigenspace of Y_N into the other\" "
              "(`trace_perp_commutant_iff_blocks`, `blocks_iff_swaps_eigenspaces`, `swaps_eigenspaces_iff_anticomm`). "
              "Lemma 4.3 ends as in the paper: f vanishes off h(ν) (`coeff_nu_eq_zero_off_hooks`), h(ν) is not the type of an "
              "N-cycle, f ∈ C_N vanishes off the N-cycles (`nu_cycle_block_eq_zero`); it does not use ψ ≠ 0 on h(ν). "
              "Theorems A and B reach Proposition 2.1 through `forward_block_lemma` (item 7). Corollary 1.1 uses Theorem B over the "
              "algebraic closure, the cited Procesi–Formanek theorem there, and base change back to F.")


def parse_statements(text):
    """Return [(name, doc_first_line)] for every top-level theorem, in file order."""
    items = []
    doc = ""
    for block in re.finditer(r"(/--(.*?)-/\s*)?^theorem\s+(\w+)", text, re.S | re.M):
        doc = " ".join((block.group(2) or "").split())
        items.append((block.group(3), doc[:140]))
    return items


def write_audit_lean(names):
    lines = ["-- GENERATED by scripts/audit.py — do not edit.", "import NagataHigman.Paper.Statements", ""]
    lines += [f"#print axioms {NAMESPACE}.{name}" for name in names]
    text = "\n".join(lines) + "\n"
    # Rewrite only on change: an identical rewrite bumps the mtime while lake (hash-based) rebuilds nothing,
    # so kernel_replay.sh (mtime-based freshness) would refuse with "olean older than source".
    if not AUDIT_LEAN.exists() or AUDIT_LEAN.read_text() != text:
        AUDIT_LEAN.write_text(text)


def run_lean():
    proc = subprocess.run(["nice", "-n", "19", "lake", "build", "NagataHigman.Audit"],
                          cwd=PROJECT, capture_output=True, text=True, env=None)
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
    forbidden = {name for name in axioms - STANDARD - {"sorryAx"}
                 if name not in CITED_WHITELIST and not name.startswith("NagataHigman.Cited.Temp.")}
    if forbidden:
        return "VIOLATION"
    if "sorryAx" in axioms:
        return "OPEN"
    if any(a.startswith("NagataHigman.Cited.Temp.") for a in axioms):
        return "PROVED-FROM-TEMP"
    extra = axioms - STANDARD
    if not extra:
        return "PROVED"
    if all(a.startswith("NagataHigman.Cited.") for a in extra):
        return "PROVED-FROM-CITED"
    return "VIOLATION"


def render(items, axioms_by_name):
    rows = ["| # | Lean name | Paper claim | Status | Cited axioms used |", "|---|---|---|---|---|"]
    counts = {}
    for idx, (name, doc) in enumerate(items, 1):
        axioms = axioms_by_name[name]
        status = classify(axioms)
        counts[status] = counts.get(status, 0) + 1
        cited = ", ".join(sorted(a.removeprefix("NagataHigman.Cited.") for a in axioms if a.startswith("NagataHigman.Cited.")))
        rows.append(f"| {idx} | `{name}` | {doc.replace('|', chr(92) + '|')} | {status} | {cited or '—'} |")
    summary = ", ".join(f"{k}: {v}" for k, v in sorted(counts.items()))
    return summary, "\n".join(rows), counts


def main_audit():
    items = parse_statements(STATEMENTS.read_text())
    names = [n for n, _ in items]
    write_audit_lean(names)
    axioms_by_name = parse_axioms(run_lean(), names)
    summary, table, counts = render(items, axioms_by_name)
    AUDIT_MD.write_text(f"# AUDIT — every claim of the paper, as Lean sees it\n\nGenerated by scripts/audit.py from "
                        f"`#print axioms`. Summary: {summary}.\n\n{TRUST_NOTE}\n\n{table}\n\n{ROUTE_NOTE}\n")
    print(f"AUDIT: {len(items)} claims. {summary}. Table: {AUDIT_MD}")
    if counts.get("VIOLATION"):
        sys.exit("AUDIT FAILED: a forbidden axiom appears (VIOLATION rows).")


def main_test():
    sample = "/-- **Lemma 9.9**: hello. -/\ntheorem foo : True := trivial\ntheorem bar : True := sorry\n"
    assert parse_statements(sample) == [("foo", "**Lemma 9.9**: hello."), ("bar", "")], parse_statements(sample)
    out = ("'NagataHigman.Paper.foo' depends on axioms: [propext,\n NagataHigman.Cited.procesi_formanek]\n"
           "'NagataHigman.Paper.bar' depends on axioms: [sorryAx]\n'NagataHigman.Paper.baz' does not depend on any axioms\n")
    got = parse_axioms(out, ["foo", "bar", "baz"])
    assert classify(got["foo"]) == "PROVED-FROM-CITED"
    assert classify(got["bar"]) == "OPEN"
    assert classify(got["baz"]) == "PROVED"
    assert classify({"propext", "evil"}) == "VIOLATION"
    assert classify({"sorryAx", "evil"}) == "VIOLATION"
    assert classify({"NagataHigman.Cited.Temp.y", "evil"}) == "VIOLATION"
    assert classify({"sorryAx", "NagataHigman.Cited.Temp.y", "evil"}) == "VIOLATION"
    assert classify({"propext", "NagataHigman.Cited.youngSystem_exists", "NagataHigman.Cited.Temp.y"}) == "PROVED-FROM-TEMP"
    assert classify({"propext", "NagataHigman.Cited.unlisted"}) == "VIOLATION"
    assert classify({"NagataHigman.Cited.kuzmin_lower_bound"}) == "VIOLATION"
    _, table, _ = render([("foo", "for |X| = n + 1")], {"foo": {"propext"}})
    assert "for \\|X\\| = n + 1" in table and table.splitlines()[-1].count(" | ") == 4, table
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
