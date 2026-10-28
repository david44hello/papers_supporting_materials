#!/usr/bin/env python3
"""audit.py — the coverage-and-assumptions table for every paper claim, produced by Lean itself.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
RUN IT INSIDE autonomy_priority_gate.sh.

For every `theorem` in the statement files (STATEMENT_MODULES: Osserman/Paper/Statements.lean, Statements7.lean,
StatementsSix.lean, Statements8.lean) this script asks Lean (`#print axioms`) which axioms the proof depends on, and classifies it:
  PROVED            only Lean's three standard axioms (propext, Classical.choice, Quot.sound)
  PROVED-FROM-CITED standard axioms plus Osserman.Cited.* axioms (the paper's cited results) — listed by name
  PROVED-FROM-TEMP  uses an Osserman.Cited.Temp.* axiom: a fact the paper PROVES that Lean has not proved yet — NOT done
  OPEN              depends on sorryAx (a proof gap somewhere below it)
  VIOLATION         any other axiom (forbidden; fails loudly)
A row whose docstring carries "(Lean-only row" is not a claim of the paper: its status gets the label
(LEAN-ONLY WITNESS) or (LEAN-ONLY HELPER) and it is counted apart from the paper's claims.
Usage: scripts/audit.py            (writes AUDIT.md, exits 1 on any VIOLATION)
       scripts/audit.py --test     (self-test of the parser)
"""
import re
import subprocess
import sys
from pathlib import Path

PROJECT = Path(__file__).resolve().parent.parent
LIB = "Osserman"
STATEMENT_MODULES = ["Statements", "Statements7", "StatementsSix", "Statements8"]  # in Osserman/Paper/, table order
AUDIT_LEAN = PROJECT / LIB / "Audit.lean"
AUDIT_MD = PROJECT / "AUDIT.md"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
NAMESPACE = f"{LIB}.Paper"
CITED = f"{LIB}.Cited."
TEMP = f"{LIB}.Cited.Temp."
CITED_WHITELIST = {f"{CITED}isoparametric_quartic_R32", f"{CITED}symm_clifford9_unique",
                   f"{CITED}nik2006_lemma_3_1", f"{CITED}nik2006_lemma_3_11", f"{CITED}andrejic_thm5",
                   f"{CITED}nik2006_thm_3_1", f"{CITED}nik2006_prop_2_1", f"{CITED}nik2005_prop_1"}
LEAN_ONLY_TAG = "(Lean-only row"  # docstring tag of a row that is NOT a claim of the paper
WITNESS_MARK = "non-vacuity"      # in the title (before the tag): a witness that a hypothesis bundle can hold
LEAN_ONLY_LABEL = {"witness": "LEAN-ONLY WITNESS", "helper": "LEAN-ONLY HELPER"}
LEAN_ONLY_NOTE = ("**Lean-only rows.** A row whose docstring says \"Lean-only row\" is NOT a claim of the paper and is "
                  "counted apart: LEAN-ONLY WITNESS rows show that a hypothesis bundle used by the paper's claims can "
                  "hold (no claim is vacuous); LEAN-ONLY HELPER rows are bridges the Lean statements need (e.g. "
                  "`hasPattern_iff_patternEv` is true by definition). Their status is shown with that label.")
TRUST_NOTE = ("**Trust.** Every PROVED-FROM-CITED result is conditional on the eight cited statements in "
              "Osserman/Cited/ (the column 'Cited axioms used' names them per row), nothing else (scripts/audit.py "
              "rejects any other cited axiom). Sections 7-8 and the six pieces (Cited/Nik2006.lean, "
              "Cited/Andrejic.lean, checked against their sources): `nik2006_lemma_3_1` — "
              "[Nik2006, Lemma 3.1(1),(2)] = [Nikolayevsky, Manuscripta Math. 115 (2004), Lemma 2]: polynomial "
              "eigenvector frames for a simple or double nonzero eigenvalue (n = 16 instance); `nik2006_lemma_3_11` — "
              "[Nik2006, Lemma 3.11]: if |x|² divides a sum of at most eight squares of polynomials on ℝ^16, it divides "
              "each (word for word); `andrejic_thm5` — [AL2023, Thm 3] = [And2022, Thm 5]: a Jacobi-proportional "
              "non-Clifford tensor has multiplicities (8,7) or (7,7,1) (n = 16 instance). Section 8 (checkpoint a3; "
              "all three checked against their sources): `nik2006_thm_3_1` — [Nik2006, Thm 3.1] = [Nagata 1957]: "
              "ℝ[x_1..x_16]/(|x|²) is a UFD (the domain property is a hypothesis, proved in row `s8_q_prime`); "
              "`nik2006_prop_2_1` — [Nik2006, Prop. 2.1]: an Osserman tensor on ℝ^16 with a reduced eigenvalue of "
              "multiplicity 9 has a Cliff(6)-structure (Jacobi form only); `nik2005_prop_1` — [Nik2005, Prop. 1]: m the "
              "maximal multiplicity, ν = 15 − m, 16 ≥ 3ν and 16 > (ν+1)²/4 give a Cliff(ν)-structure (n = 16 instance, "
              "Jacobi form only). Sections 1-6 "
              "(Cited/Isoparametric.lean): "
              "(A) `isoparametric_quartic_R32` — the classification of isoparametric hypersurfaces with four principal "
              "curvatures on S^31 [Münzner 1980, Satz 2-4, Folgerung, §4; Ferus–Karcher–Münzner 1981, Thm 4.1, §§4.3, "
              "5.9, 6.6; Chi 2020] in polynomial form: a homogeneous quartic F on R^32 with |∇F|² = 16s³, ΔF = 8s, "
              "nonconstant on the sphere, is ε·F_P∘U for a symmetric Clifford system P_0..P_m (m ≥ 1), U ∈ O(32), "
              "ε = ±1; (Q) `symm_clifford9_unique` — symmetric Clifford systems of nine matrices on R^16 are unique up "
              "to O(16) and the sign of one generator [FKM 1981, §§3.4-3.5]. Both were checked against their sources. "
              "The paper's own differential-geometric argument that turns the cited "
              "theorems into (A) (Section 3, l. 421-437 and 457-471: g = 4, n = 31, c = 8, the excluded alternative of "
              "Satz 3, connected levels, the multiplicities (7,8), the principal curvatures, the congruence and the "
              "uniqueness of the Cartan polynomial up to sign) is NOT FORMALIZED: Mathlib has no hypersurfaces or "
              "principal curvatures. Absorbing U (`sec3_absorb_U`), ΔF_P = (136 − 16(m+1))s (`sec3_lap_FKM`), the values "
              "of ε and m (`sec3_eps_m`) and (eq:plus)/(eq:minus) (`sec3_plus_or_minus`) are rows; see the table for "
              "their status. The Brown–Gray formula is the DEFINITION of R_Cay (Osserman/Defs/Cayley.lean). "
              "A PROVED-FROM-TEMP row would rest on a placeholder for a fact the paper proves (namespace "
              "Osserman.Cited.Temp); such rows are NOT counted as proved.")
ROUTE_NOTE = ("## Not formalized, and route differences\n\n"
              "PROVED means that Lean proves the paper's STATEMENT. Line numbers: P013_short.tex of the Zenodo posting copy (md5 6e130b95; PDF md5 ea4bb54b).\n\n"
              "1. **Not formalized: Theorem A** (thm:conjA, l. 199-204): its proof needs Sections 9-27 (projective "
              "algebraic geometry, class groups, semialgebraic sets, algebraic topology), outside the agreed scope.\n"
              "2. **Not formalized: Corollary B and its proof** (l. 209-235) and **Remark 1.1** (l. 237-243): "
              "statements about Riemannian manifolds; Mathlib has no curvature tensor of a manifold, so they cannot be "
              "stated. This includes the cited algebraic facts used there (Adams' theorem via [Nik2005]: a "
              "multiplicity of at least 7 is at least 9; [Nik2006, Prop. 2.1]; [Nik2005, Prop. 1]); Theorem C does "
              "not use them.\n"
              "3. **Not formalized: l. 271-280**: Nikolayevsky's announced manifold theorem, and the multiplicities "
              "(1,14) and (3,12) of CP^8, HP^4 and their duals (the paper defines no tensors for them). The "
              "algebraic core of \"a flat space or a space of constant curvature has one Jacobi eigenvalue\" IS a row "
              "(`sec1_const_curv_one_eigenvalue`).\n"
              "4. **Not formalized: R_Cay is the curvature tensor of the Cayley plane** (l. 190-192, 654-659, cited "
              "[BG, Eq. (6.12)]): in Lean the Brown–Gray formula is the DEFINITION of R_Cay; its normalization "
              "(sectional curvatures in [1,4], both attained) is a row (`sec1_Rcay_sectional`).\n"
              "5. **Not formalized: Cl₊(9) ≅ M₁₆(ℝ) ⊕ M₁₆(ℝ)** (l. 672): only its consequence, the cited (Q), is used.\n"
              "6. **Not used: [AL2023, (12)]** (l. 353-355): Lean proves (eq:reconstruct) directly "
              "(`sec2_reconstruct`), so the specialization of [AL2023] is not needed.\n"
              "7. **Not formalized: the Section 3 glue** (l. 421-437, 457-471), see the trust note.\n"
              "8. **Route differences.** (a) **Lemma 4.1, onto and H(a)² = I** (l. 529-533): the paper shows that "
              "the image of h is open and compact in S^m, hence all of S^m, and then gets H(a)² = I from the fibres "
              "over a and -a. Lean goes the other way, algebraically: a ↦ H(a)x is injective (from the rank count), so "
              "every eigenvalue of H(a) is ±1 and H(a)² = I (`lem_4_1_sq`); a +1 eigenvector of H(a) then lies over "
              "a (`lem_4_1_onto`); the paper's sentence \"the image is open and compact\" (`lem_4_1_image_open`) then "
              "follows from onto. route_check.lean checks that these rows use the injectivity step. (b) **m ≥ 1 at "
              "l. 474**: l. 474 uses ΔF_P = (136 − 16(m+1))s for the F_P of l. 447, which is defined for m ≥ 1; "
              "the Lean rows `sec3_lap_FKM` and `sec3_eps_m` carry 1 ≤ m, which the cited (A) provides (0 < m). "
              "(c) **Rotating the index space** (l. 508-526, 559-562, 578-592): Lean states these "
              "steps without choosing the rotation. Each row is stated through the unit vector w (or h(x)): C_w = "
              "Σ w_iC_i, all u ⊥ w, and in 5.2 sums over all nine blocks. For any orthogonal O with first row w, the "
              "rotated generators are C'_0 = C_w and C'_j = C_{u_j}; since OᵀO = I, the sums are unchanged. So each row "
              "gives the paper's sentence for every such rotation. The closing rows `prop_5_1_A_Cl7` and "
              "`prop_5_2_A_Cl8` state the result for every orthonormal basis of w^⊥.\n"
              "9. **Non-vacuity of the hypotheses**: of (Q), by the standard system (`sec6_std_system`); of (A), "
              "`sec3_axiom_nonvacuous` (a condition of accepting the cited statements); of Theorem C, by R_Cay "
              "(`thm_C_hyp_nonvacuous`); of Setting (T), the hypothesis of the Lemma 12.5 rows "
              "(`settingT_nonvacuous`); of the anisotropy step's hypotheses (`thm_G_partner_nonvacuous`).\n"
              "10. **Covered by `thm_C`**: l. 680, J_x = (μ − κ/3)Π(x) + (κ/3)J_x(T^*R_Cay), follows from the tensor "
              "equality in `thm_C`'s third case.\n"
              "11. **Not formalized (six pieces, outside scope):** that Setting (T) holds at a regular anchor "
              "(sec_common_lemmas.tex l. 5-9, 20-21; proved in Section 10 by Lemma 10.2) — Lemma 12.5 takes "
              "Setting (T) as its hypothesis; Theorem G itself (sec_polynomial_gram.tex l. 3-8), Lemma 9.3 (its output "
              "is the hypothesis `IsRationalPartner` of the anisotropy rows) and the closing appeal to Proposition "
              "9.1(2) (l. 267-269). The anisotropy step itself is stated and ends at G(s) = (s² + d)I "
              "(`thm_G_conclude`), polynomial on ℝ^16 (`thm_G_q_pointS`). In these three files nothing else is "
              "formalized: sec_common_lemmas.tex Lemma 12.2, Remark 12.3, Lemmas 12.7-12.9 (l. 50-79, 145-305) and the "
              "Gram matrix G(a) = B(a)B(a)ᵀ (l. 8); sec_polynomial_gram.tex l. 1-233 (Theorem G's statement, "
              "Prop 9.1, Lemma 9.2, Lemma 9.3; l. 11-15 only through `thm_G_shift`); sec_singular_integral_extraction.tex "
              "everything except l. 155-169 (Lemma 24.5). The regular anchor is a point of the set U₀ built in Section "
              "27; so these inputs need Sections 9, 10 and 27. NOT A CLAIM: sec_common_lemmas.tex l. 23 \"L need not "
              "stay an isometry\" (a remark) and l. 23-25 (the |x|² convention).\n"
              "12. **Cited results of Section 7** (cited statements in Osserman/Cited/Nik2006.lean and "
              "Cited/Andrejic.lean; source check DONE: each true and no stronger than its "
              "source): [Nik2006, Lemma 3.1(1),(2)] (Theorem E, Section 8; refereed form: Manuscripta Math. 115 (2004) "
              "Lemma 2), [Nik2006, Lemma 3.11] (Remark 7.2, Section 8, Theorem G; proceedings, refereeing not stated; "
              "true and sharp at 8 by Pfister), [AL2023, Thm 3 p. 8470] = [And2022, Thm 5] (Corollary D; refereed). "
              "The sentence "
              "\"Andrejić's hypothesis places no restriction on the number of eigenvalues\" (l. 838-839) is about the "
              "source and is verified there (AL2023 p. 8469: \"k-root\" for any k; Theorem 3 has no k hypothesis); it "
              "is not a row.\n"
              "13. **Hurwitz–Radon** (l. 825): named without a reference, so it is a row to prove (`rem_7_2_nu_le_8`), "
              "not a cited result.\n"
              "14. **Route: Remark 7.2 for every ν.** The paper cites [Nik2006, Lemma 3.2(1)] at each restoring step. "
              "Remark 7.2 recalls the general proof (it shifts the base constant λ₀), and the paper uses that form when "
              "ν = 8. Lean proves the lemma (`lem_nik_3_2_1`) through the Remark 7.2 rows for every ν ≤ 8, so Lemma "
              "3.2(1) is not a cited input.\n"
              "15. **Section 8 (Statements8.lean, checkpoint a3).** Cited inputs: [Nik2006, Lemmas 3.1, 3.11, Theorem "
              "3.1, Proposition 2.1] and [Nik2005, Proposition 1] only. Results the paper re-proves or uses outside "
              "their stated hypotheses — Lemma 8.2 (= [Nik2006, Lemma 3.5] without its standing hypotheses), the "
              "three-column step, §8.6 (= [Nik2006, Lemma 3.3] with up to eight columns) and every restore "
              "(`lem_nik_3_2_1`) — are rows to prove. Steps inside the paper's proofs by contradiction (Lemma 8.1, "
              "c > 0; Lemma 8.2, r = 2, c ≠ 0, and the lift of the \"Otherwise\" case) are stated in general forms "
              "whose hypotheses can hold (`lem_8_1_rotate`, `lem_8_1_not_const`, `lem_8_1_clifford_t`, "
              "`lem_8_1_trace_const`, `lem_8_2_r2_c_ne`, `lem_8_2_lift` without (8.1)). Non-vacuity: "
              "`thm_F_hyp_nonvacuous`, `s8_threeCol_nonvacuous`, `s8_threeCol_branch_nonvacuous`, "
              "`s8_threeCol_distinct_nonvacuous`, `lem_8_2_lift_nonvacuous`, `lem_8_2_lift_hyp_nonvacuous`, "
              "`s8_3_opposite_nonvacuous`, `s8_4_opposite_nonvacuous`, `s8_5_mixed_nonvacuous`. A row whose proof "
              "needs another row of this file takes that row as a leading argument with its exact type (it is PROVED "
              "once that row is; until then it shows OPEN through the `sorry` it inherits).\n"
              "16. **Lemma 8.1, Ω(0) = ±I (`lem_8_1_Omega_zero`).** Lean proves it by its own route: Ω² = I and Ω "
              "commutes with every S_i; if Ω ≠ −I, a nonzero fixed vector exists, and S_0 and the swap maps "
              "x ↦ (e x̄₂, x̄₁ e), with the left alternative law a(āz) = |a|²z, carry it to every vector, so Ω = I. The "
              "paper's two reasons (\"as nine is odd, Ω(0) commutes with every H_i\"; \"the H_i generate all of "
              "End(ℝ¹⁶)\") are their own rows, `cliffProd_nine_commutes` and `std_sys_generate`.\n")


def row_kind(doc):
    """`claim` (a claim of the paper), or `witness` / `helper` for a row whose docstring carries LEAN_ONLY_TAG
    (a non-vacuity witness if its title, before the tag, says non-vacuity; else a Lean-only helper)."""
    if LEAN_ONLY_TAG not in doc:
        return "claim"
    return "witness" if WITNESS_MARK in doc.split(LEAN_ONLY_TAG)[0] else "helper"


def parse_statements(text):
    """Return [(name, doc_first_line, kind)] for every top-level theorem, in file order."""
    items = []
    for block in re.finditer(r"(/--(.*?)-/\s*)?^theorem\s+(\w+)", text, re.S | re.M):
        doc = " ".join((block.group(2) or "").split())
        items.append((block.group(3), doc[:140], row_kind(doc)))
    return items


def write_audit_lean(names):
    lines = ["-- GENERATED by scripts/audit.py — do not edit."]
    lines += [f"import {LIB}.Paper.{module}" for module in STATEMENT_MODULES] + [""]
    lines += [f"#print axioms {NAMESPACE}.{name}" for name in names]
    text = "\n".join(lines) + "\n"
    # Rewrite only on change: an identical rewrite bumps the mtime while lake (hash-based) rebuilds nothing,
    # so kernel_replay.sh (mtime-based freshness) would refuse with "olean older than source".
    if not AUDIT_LEAN.exists() or AUDIT_LEAN.read_text() != text:
        AUDIT_LEAN.write_text(text)


def run_lean():
    proc = subprocess.run(["nice", "-n", "19", "lake", "build", f"{LIB}.Audit"],
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
                 if name not in CITED_WHITELIST and not name.startswith(TEMP)}
    if forbidden:
        return "VIOLATION"
    if "sorryAx" in axioms:
        return "OPEN"
    if any(a.startswith(TEMP) for a in axioms):
        return "PROVED-FROM-TEMP"
    extra = axioms - STANDARD
    if not extra:
        return "PROVED"
    if all(a.startswith(CITED) for a in extra):
        return "PROVED-FROM-CITED"
    return "VIOLATION"


def count_summary(counts):
    return ", ".join(f"{k}: {v}" for k, v in sorted(counts.items())) or "none"


def render(items, axioms_by_name):
    """Table rows plus separate status counts for the paper's claims and for the Lean-only rows."""
    rows = ["| # | Lean name | Paper claim | Status | Cited axioms used |", "|---|---|---|---|---|"]
    claim_counts, lean_only_counts, kinds = {}, {}, {}
    for idx, (name, doc, kind) in enumerate(items, 1):
        axioms = axioms_by_name[name]
        status = classify(axioms)
        counts = claim_counts if kind == "claim" else lean_only_counts
        counts[status] = counts.get(status, 0) + 1
        kinds[kind] = kinds.get(kind, 0) + 1
        shown = status if kind == "claim" else f"{status} ({LEAN_ONLY_LABEL[kind]})"
        cited = ", ".join(sorted(a.removeprefix(CITED) for a in axioms if a.startswith(CITED)))
        rows.append(f"| {idx} | `{name}` | {doc.replace('|', chr(92) + '|')} | {shown} | {cited or '—'} |")
    n_lean_only = kinds.get("witness", 0) + kinds.get("helper", 0)
    summary = (f"{kinds.get('claim', 0)} paper claims ({count_summary(claim_counts)}); {n_lean_only} Lean-only rows, "
               f"not claims of the paper ({kinds.get('witness', 0)} non-vacuity witnesses, {kinds.get('helper', 0)} "
               f"helpers: {count_summary(lean_only_counts)})")
    violations = claim_counts.get("VIOLATION", 0) + lean_only_counts.get("VIOLATION", 0)
    return summary, "\n".join(rows), violations


def main_audit():
    items = [item for module in STATEMENT_MODULES
             for item in parse_statements((PROJECT / LIB / "Paper" / f"{module}.lean").read_text())]
    names = [n for n, _, _ in items]
    duplicates = sorted({n for n in names if names.count(n) > 1})
    if duplicates:
        sys.exit(f"AUDIT FAILED: theorem names used in two statement files: {duplicates}")
    write_audit_lean(names)
    axioms_by_name = parse_axioms(run_lean(), names)
    summary, table, violations = render(items, axioms_by_name)
    AUDIT_MD.write_text(f"# AUDIT — every claim of the paper, as Lean sees it\n\nGenerated by scripts/audit.py from "
                        f"`#print axioms`. Summary: {summary}.\n\n{LEAN_ONLY_NOTE}\n\n{TRUST_NOTE}\n\n{table}\n\n"
                        f"{ROUTE_NOTE}\n")
    print(f"AUDIT: {len(items)} rows = {summary}. Table: {AUDIT_MD}")
    if violations:
        sys.exit("AUDIT FAILED: a forbidden axiom appears (VIOLATION rows).")


def main_test():
    sample = "/-- **Lemma 9.9**: hello. -/\ntheorem foo : True := trivial\ntheorem bar : True := sorry\n"
    assert parse_statements(sample) == [("foo", "**Lemma 9.9**: hello.", "claim"), ("bar", "", "claim")], \
        parse_statements(sample)
    assert row_kind("**Theorem C, non-vacuity** (Lean-only row; lines 1-2): met.") == "witness"
    assert row_kind("**Named eigenvalues** (Lean-only row, review a3 S1): the same.") == "helper"
    assert row_kind("**Lemma 8.1**: K = 0 (no non-vacuity needed).") == "claim"
    summary, _, violations = render([("w", "x", "witness"), ("c", "y", "claim"), ("h", "z", "helper")],
                                    {"w": {"propext"}, "c": {"sorryAx"}, "h": {"propext"}})
    assert summary.startswith("1 paper claims (OPEN: 1); 2 Lean-only rows") and violations == 0, summary
    out = (f"'{NAMESPACE}.foo' depends on axioms: [propext,\n {CITED}symm_clifford9_unique]\n"
           f"'{NAMESPACE}.bar' depends on axioms: [sorryAx]\n'{NAMESPACE}.baz' does not depend on any axioms\n")
    got = parse_axioms(out, ["foo", "bar", "baz"])
    assert classify(got["foo"]) == "PROVED-FROM-CITED"
    assert classify(got["bar"]) == "OPEN"
    assert classify(got["baz"]) == "PROVED"
    assert classify({"propext", "evil"}) == "VIOLATION"
    assert classify({"sorryAx", "evil"}) == "VIOLATION"
    assert classify({f"{TEMP}y", "evil"}) == "VIOLATION"
    assert classify({"sorryAx", f"{TEMP}y", "evil"}) == "VIOLATION"
    assert classify({"propext", f"{CITED}isoparametric_quartic_R32", f"{TEMP}y"}) == "PROVED-FROM-TEMP"
    assert classify({"propext", f"{CITED}unlisted"}) == "VIOLATION"
    _, table, _ = render([("foo", "for |X| = n + 1", "claim")], {"foo": {"propext"}})
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
