#!/usr/bin/env python3
"""audit.py — the coverage-and-assumptions table for every paper claim, produced by Lean itself.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

For every `theorem` in Matsaev/Paper/Statements.lean this script asks Lean (`#print axioms`) which axioms the proof
depends on, and classifies it:
  PROVED            only Lean's three standard axioms (propext, Classical.choice, Quot.sound)
  PROVED-FROM-CITED standard axioms plus Matsaev.Cited.* axioms (the paper's cited results) — listed by name
  PROVED-FROM-TEMP  uses a Matsaev.Cited.Temp.* axiom: a fact the paper PROVES that Lean has not proved yet — NOT done
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
STATEMENTS = PROJECT / "Matsaev" / "Paper" / "Statements.lean"
AUDIT_LEAN = PROJECT / "Matsaev" / "Audit.lean"
AUDIT_MD = PROJECT / "AUDIT.md"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
NAMESPACE = "Matsaev.Paper"
TRUST_NOTE = ("**Trust.** Project 016 (Matsaev). Trust surface = the definitions the statements use: "
              "Matsaev/Defs/Scalar.lean, Matsaev/Defs/Spaces.lean, Matsaev/Defs/Conjecture.lean, and Matsaev/Angle/Defs.lean "
              "(IsThetaStar, SigmaAng, angDist, Nang, qang; used by lemma_3_5_angle_form, lemma_3_5_i_iii, lemma_3_5_full). "
              "Paper: short version v2.00 (md5 a9b3c6be); the numbers in the table are v2.00's. "
              "Lean names carry the v2.00 numbers (lemma_3_5_angle_form = Lemma 3.5 (i)-(iii) in angle form). "
              "No cited axioms (Matsaev/Cited/ is empty): every PROVED row "
              "rests only on Lean's three standard axioms. A PROVED-FROM-CITED row would rest on a cited result in "
              "Matsaev/Cited/; a PROVED-FROM-TEMP row on a placeholder for a fact the paper proves (NOT counted as proved).")
ROUTE_NOTE = ("## Route differences\n\n"
              "PROVED means the paper's STATEMENT is proved in Lean. In the places below the Lean proof uses a different "
              "argument from the paper's, so the paper's own text there is not machine-checked:\n\n"
              "1. **Proof of Lemma 4.1**: `lemma_4_1` itself is proved with the exact identity `TK.gamma_identity` "
              "(Matsaev/TK/Gain.lean), `TK.bracket_pos` and `TK.key_localization` (Matsaev/TK/Moving.lean). The paper's "
              "own argument is ALSO machine-checked: `lemma_4_1_contraction_deriv`, `lemma_4_1_eps_deriv`, "
              "`lemma_4_1_values`, `lemma_4_1_gamma_zero`, `lemma_4_1_gamma` (Γ(0) = 0, Γ′(0), Γ(a) = aΓ′(0) + o(a)) "
              "and `lemma_4_1_paper_route` (the inequality from the test vector ξ_a = s_a/(s_a)₁ of Lemma 3.5 (iv)); "
              "Matsaev/Assembly/Gamma.lean. One detail differs: Lean shows that the ξ̇ terms of Γ′(0) vanish through "
              "H′(t_*) = 0 for H(s) = ⟨φ(1, s), (J − D_*I)(1, s)⟩ (a maximum), with (ξ_a)₁ = 1; the paper says the "
              "same with the full derivative of ξ ↦ ⟨φ(ξ), (J − D_*I)ξ⟩ at ξ_0, the paper's Ψ ≤ 0 maximal at ξ_0 (also stated: `lemma_4_1_gamma_zero`). "
              "The three-term display of Γ′(0) and the display \"the remaining terms are (p−1)(1+B)^(p−2)BE_* − "
              "½(1+B)^(p−1)(‖ξ_0‖_p^p + D_*⟨φ(ξ_0), Jξ_0⟩)\" (added in v1.80) are not stated; their ingredients are "
              "`lemma_4_1_gamma` (conjunct 1), `lemma_4_1_eps_deriv` (conjuncts 6-7), `lemma_4_1_values` (conjuncts 1-2) and "
              "`lemma_4_1_gamma_zero` (conjuncts 4-6).\n"
              "2. **Lemma 3.5 (iv)** (`lemma_3_5_full`, PROVED) and the \"(i), (iv)\" paragraph of its proof: Lean "
              "factors D_* − Q = h² at θ_* (h analytic, h′(θ_*) > 0) and applies Mathlib's analytic implicit function "
              "theorem to h(θ) + h(θ − γ) = 0, γ = arctan(a/(1+B)), not to ∂_θH = 0 (Matsaev/Assembly/Lem35iv.lean). "
              "The proofs of Theorem 3.6 and of `lemma_4_1` do not use (iv): Lean uses |θ_a − θ_*| ≤ a "
              "(`lemma_3_5_angle_form`) and explicit Lipschitz and Taylor bounds; `lemma_4_1_paper_route` uses (iv), as "
              "the paper does.\n"
              "3. **Proof of Theorem 3.6, Step 3** (all of it: the six bases ≥ κ on 𝒰, their a > 0 refinement ≥ κ/2 once "
              "a ≤ κ/4, the real-analyticity of the terms built from them, and the bound ∂²_ν F_0 ≥ 4q_*; Lean uses instead "
              "κ ≤ |u| and a ≤ (1+B)κ/2 with Taylor bounds, `SJ.est_T4` in Matsaev/SJ/BellmanEst.lean and `SJ.case_near` in "
              "Matsaev/SJ/BellmanCases.lean; the step's own premise, |y|^p is real-analytic for y ≠ 0, is the row "
              "`theorem_3_6_abs_rpow_analytic`) **and the gradient half of Step 5** "
              "(eq. `eq:Ea`, the gradients of k^(1), k^(2) at (1, t_*), and |C_a − (1+B)| ≤ a): Lean uses Lemma 3.3 (`lemma_3_3`) "
              "and direct bounds on Δ_a (`SJ.delta_first_order`, `SJ.delta_second_order`); these displays, and the mean value "
              "bounds of Step 5 (|C_a^p − (1+B)^p| ≤ p(1+B+a)^(p−1)a, ||y+h|^p − |y|^p| ≤ p(|y|+|h|)^(p−1)|h|), are not "
              "stated separately.\n"
              "4. **Remark 5.2, strictness**: Lean (`Rem52.pointwise_lt`) uses the weighted strict convexity of t^q, "
              "so equality forces |ξ₁| = |ξ₂| and sign conditions; the paper uses the strict convexity of ℓ^p_2 and "
              "\"Jξ would be a real multiple of ξ\".\n"
              "5. **Lemma 2.2 at p = ∞**: Lean uses periodic truncation (`JLower.norm_aeval_Jmat_mulVec_le_top`); "
              "the paper uses ‖P(J)‖_∞ ≤ Σ|c_k| = ‖P(S)‖_∞.\n"
              "6. **Theorem B**: Lean bounds the rows of P̃(J) directly, not M = V·P̃(J); at p = ∞ it uses the "
              "triangle inequality, not \"the larger of the two\".\n"
              "7. **Lemma 2.3**: Lean uses finite Toeplitz truncations of P(S) and Hölder's inequality, not convolution on "
              "ℓ^p(ℤ); so ‖P(S)‖_p = ‖𝒞‖_p and \"‖𝒞‖_p = ‖𝒞‖_{p′}\" (v1.90) for the convolution 𝒞 are not stated "
              "(the conclusion for P(S) is `lemma_2_3`).\n"
              "8. **Lemma 3.1**: Lean telescopes the window bound over n < N for every x ∈ ℓ^p(ℕ) and lets N → ∞ (x_N → 0, "
              "G continuous, G(0, 0) = 0; Matsaev/Ops/Bellman.lean); no density argument.\n"
              "9. **Lemma 3.3** and the formulas before it (∂_νF_0 = pB(1+B)^(p−1)φ(ν−u) + pBφ((1+B)u − Bν), which is 0 at "
              "ν = 0, and ∂²_νF_0 = p(p−1)B(1+B)^(p−2)|u|^(p−2) at ν = 0; reused in Step 3 of Theorem 3.6): Lean proves "
              "Lemma 3.3 by a Bregman identity with an explicit constant, not by compactness with these formulas, which "
              "are not stated in Lean.\n"
              "10. **Lemma 3.4**, the step χ < 0: Lean derives it from t^p < t² for t ∈ (0, 1).\n"
              "11. **Lemma 3.5 (i)-(iii)**: Lean's angle route (Matsaev/Angle/: log N, W_γ and |θ_a − θ_*| ≤ a, "
              "`lemma_3_5_angle_form`), not the paper's argument (the choice of ρ and m at its start, C_a^p = (1+B)^p + a c(a)); "
              "∂²_θQ(θ_*) = f″(t_*)sec⁴θ_* is not stated. The limit Σ_a(s)/a → Σ′(s) (uniform, with rate) and \"Σ′(s) is the "
              "right derivative of Σ_a(s) at a = 0\" (v1.90) are stated and proved separately (`lemma_3_5_sigma_right_deriv`), "
              "but Lean's proof of (i)-(iii) does not use them.\n"
              "12. **Theorem 3.6, Step 1**: eq. (`eq:Sigma`), the 4-cycle sum equals Σ_a(s) for every G, is bypassed: Lean "
              "computes the cycle directly (`SJ.fcirc_eq`, Matsaev/SJ/BellmanAlg.lean).\n"
              "13. **Theorem 3.6, Step 6, Case 2**: Lean uses explicit bounds instead of real-analyticity and compactness; "
              "the discriminant and the |ν| ≥ ν_0 bound written out in the paper are not machine-checked; nor is Step 3's "
              "\"the terms k^(1)(u, v) and k^(1)(v, w) are also real-analytic on 𝒰, as u² + v² = 1 and v² + w² ≥ w² ≥ κ² "
              "there\" (v1.90), which only feeds this analyticity argument.\n"
              "14. **Proof of Theorem A, last sentence** ((1) fails on ℓ^p itself): Lean embeds ℓ^p_2 in ℓ^p(ℕ) and proves "
              "‖P(A)‖ ≤ ‖P(A ⊕ 0)‖ by intertwining (Matsaev/Assembly/LpNat.lean); the paper's P_a(T ⊕ 0) = P_a(T) ⊕ I with "
              "norm max(‖P_a(T)‖_p, 1) is not stated.\n"
              "15. **Background, deg P ≤ 1** (`table_deg_one`): Lean proves ‖c_0 + c_1S‖_p ≤ |c_0| + |c_1| by the triangle "
              "inequality and ≥ from Lemma 2.2 at μJ with the eigenvector (1, i) of J (J(1, i) = i(1, i)); the paper's "
              "argument with ω, the isometry U (USU⁻¹ = μS) and the vector of N ones is not machine-checked.\n"
              "16. **Lemma 2.2, p < ∞**: Lean truncates to length L = 4(d+m) and counts only the full periods in [4d, L) "
              "(‖P(S)x‖^p ≥ 2m‖P(J)ξ‖^p, `JLower`), not the paper's O(1) estimate of the at most 2 deg P other indices.\n"
              "17. **Section 3, display (3)** (`eq_Qexp`, PROVED): the first-order term hp⟨φ(ξ), Jξ⟩ = hpQ(ξ)‖ξ‖_p^p is "
              "stated (`sec3_first_order_term`); for the O(a²) term Lean uses a global Taylor bound for |y|^p in each "
              "coordinate (`Qexp.abs_rpow_taylor`, explicit K), not the paper's second derivative in h, "
              "p(p−1)Σ|ξ_i + h(Jξ)_i|^(p−2)(Jξ)_i², which is not stated.")
CITED_NOTE = ("## Cited context (not results of this paper)\n\n"
              "The paper quotes these results of other papers. No proof uses them, and none is assumed in Lean "
              "(Matsaev/Cited/ is empty):\n\n"
              "1. von Neumann's inequality: (1) holds for p = 2 (abstract, table, Background).\n"
              "2. Drury 2011 [Dr11]: (1) fails for p = 4 and p = 4/3 (computer-assisted).\n"
              "3. [Ar13, Prop. 6.1]: real P with coefficients all of one sign or of alternating signs have "
              "‖P(S)‖_p = Σ|c_k| (table, Background).\n"
              "4. Peller [Pe76, Pe78, Pe81]: (1) for contractions with isometric dilations; Lemma 2.2 also follows from "
              "[Pe81] (Background, Section 2).\n"
              "5. Ray [Ra20]: the analogue for several commuting contractions fails for every 1 < p < ∞ (Background).\n"
              "6. [G], the expanded version on Zenodo: explicit counterexamples for every p ∈ [40/39, 40], and near p = 2 "
              "the matrices T = R_θ/‖R_θ‖_p with cos θ = −1/12 (Section 5, bullet list).\n"
              "7. Akcoglu–Sucheston [AS77] with Coifman–Rochberg–Weiss [CRW78]: (1) for positive contractions "
              "(Background).\n"
              "8. [Pe81; Ar13, Sec. 1], [Pe76, Pe78]: contractions with a positive contractive majorant have isometric "
              "dilations; this class contains the isometries, the Lamperti contractions (functions with disjoint supports "
              "go to functions with disjoint supports) and the absolute contractions (Background).\n"
              "9. Fackler [Fa15, Sec. 2.3]: an analytic approach was missing (Background, history).")


def parse_statements(text):
    """Return [(name, doc_first_line)] for every top-level theorem, in file order."""
    items = []
    doc = ""
    for block in re.finditer(r"(/--(.*?)-/\s*)?^theorem\s+(\w+)", text, re.S | re.M):
        doc = " ".join((block.group(2) or "").split())
        items.append((block.group(3), doc[:140]))
    return items


def write_audit_lean(names):
    lines = ["-- GENERATED by scripts/audit.py — do not edit.", "import Matsaev.Paper.Statements", ""]
    lines += [f"#print axioms {NAMESPACE}.{name}" for name in names]
    content = "\n".join(lines) + "\n"
    # Rewrite only on change: an identical rewrite leaves Lake's (content-hash) build fresh but makes the source
    # newer than its olean, and scripts/kernel_replay.sh then refuses the run as stale.
    if not AUDIT_LEAN.exists() or AUDIT_LEAN.read_text() != content:
        AUDIT_LEAN.write_text(content)


def run_lean():
    # No CPU pinning here (it fails on machines with few cores); on a shared machine run this script under taskset.
    proc = subprocess.run(["nice", "-n", "19", "lake", "build", "Matsaev.Audit"],
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
                 if not name.startswith("Matsaev.Cited.")}
    if forbidden:
        return "VIOLATION"
    if "sorryAx" in axioms:
        return "OPEN"
    if any(a.startswith("Matsaev.Cited.Temp.") for a in axioms):
        return "PROVED-FROM-TEMP"
    extra = axioms - STANDARD
    if not extra:
        return "PROVED"
    if all(a.startswith("Matsaev.Cited.") for a in extra):
        return "PROVED-FROM-CITED"
    return "VIOLATION"


def render(items, axioms_by_name):
    rows = ["| # | Lean name | Paper claim | Status | Cited axioms used |", "|---|---|---|---|---|"]
    counts = {}
    for idx, (name, doc) in enumerate(items, 1):
        axioms = axioms_by_name[name]
        status = classify(axioms)
        counts[status] = counts.get(status, 0) + 1
        cited = ", ".join(sorted(a.removeprefix("Matsaev.Cited.") for a in axioms if a.startswith("Matsaev.Cited.")))
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
                        f"`#print axioms`. Summary: {summary}.\n\n{TRUST_NOTE}\n\n{table}\n\n{ROUTE_NOTE}\n\n{CITED_NOTE}\n")
    print(f"AUDIT: {len(items)} claims. {summary}. Table: {AUDIT_MD}")
    if counts.get("VIOLATION"):
        sys.exit("AUDIT FAILED: a forbidden axiom appears (VIOLATION rows).")


def main_test():
    sample = "/-- **Lemma 9.9**: hello. -/\ntheorem foo : True := trivial\ntheorem bar : True := sorry\n"
    assert parse_statements(sample) == [("foo", "**Lemma 9.9**: hello."), ("bar", "")], parse_statements(sample)
    out = ("'Matsaev.Paper.foo' depends on axioms: [propext,\n Matsaev.Cited.x]\n"
           "'Matsaev.Paper.bar' depends on axioms: [sorryAx]\n'Matsaev.Paper.baz' does not depend on any axioms\n")
    got = parse_axioms(out, ["foo", "bar", "baz"])
    assert classify(got["foo"]) == "PROVED-FROM-CITED"
    assert classify(got["bar"]) == "OPEN"
    assert classify(got["baz"]) == "PROVED"
    assert classify({"propext", "evil"}) == "VIOLATION"
    assert classify({"sorryAx", "evil"}) == "VIOLATION"
    assert classify({"Matsaev.Cited.Temp.y", "evil"}) == "VIOLATION"
    assert classify({"sorryAx", "Matsaev.Cited.Temp.y", "evil"}) == "VIOLATION"
    assert classify({"propext", "Matsaev.Cited.x", "Matsaev.Cited.Temp.y"}) == "PROVED-FROM-TEMP"
    summary, table, _ = render([("f", "a |u|^p b")], {"f": {"propext"}})
    assert "a \\|u\\|^p b" in table and table.splitlines()[-1].count(" | ") == 4, table
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
