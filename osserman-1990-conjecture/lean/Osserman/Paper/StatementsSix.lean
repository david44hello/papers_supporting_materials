/-
Osserman/Paper/StatementsSix.lean — one theorem per claim of the six pieces of paper 013 formalized beside Sections 2-8:
Setting (T) and Lemmas 12.1, 12.4, 12.5, 12.6 (sec_common_lemmas.tex, "cl"), the anisotropy step of the proof of
Theorem G (sec_polynomial_gram.tex l. 234-270, "pg") and Lemma 24.5 (sec_singular_integral_extraction.tex l. 155-169,
"sie"), the Zenodo posting copy of the paper. NOT stated here (they need
Sections 9, 10 and 27, outside the formalized scope; the exact list is AUDIT.md route note 11): that Setting (T) holds
at a regular anchor (cl l. 5-9, 20-21: Lemma 10.2; regular anchors are built in Section 27), Theorem G itself,
Lemma 9.3 (its output is the hypothesis `IsRationalPartner`) and the closing appeal to Proposition 9.1(2) (pg l. 267-269).
Bodies link to proofs elsewhere; the audit marks any row without a proof as OPEN.
Rule (review a2-six SHOULD-3): no conjunct of a row may be provable only ex falso from another conjunct.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Paper.Statements7
import Osserman.Defs.SixPieces
import Osserman.Proofs.Six1
import Osserman.Proofs.Six2
import Osserman.Proofs.Six4a
import Osserman.Proofs.Six3
import Osserman.Proofs.Six4b
import Osserman.Proofs.Six4c
import Osserman.Proofs.Six4p
import Osserman.Proofs.Six4d
import Osserman.Proofs.Six4w

namespace Osserman.Paper

open Osserman Osserman.Cited Matrix MvPolynomial

/-! ## Section 12: Setting (T) -/

/-- **Setting (T)** (lines 21-23 of sec_common_lemmas.tex): "A real linear change of the coefficient variable $a$
preserves (T), with $L$ replaced by its composite with the change". -/
theorem setting_T_change (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (Cm : Matrix (Fin 8) (Fin 8) ℝ)
    (hC : IsUnit Cm.det) : SettingT (fun a => B (Cm *ᵥ a)) E (L * Cm) K g0 :=
  Osserman.Proofs.Six3.setting_T_change_proved B E L K g0 h Cm hC

/-- **Setting (T)** (lines 12-16 of sec_common_lemmas.tex; hidden step of line 109): `K` is an isometry onto `E^⊥`, so
`ker Kᵀ = E`. -/
theorem setting_T_ker_Kt (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) :
    LinearMap.ker (Matrix.toLin' Kᵀ) = E :=
  Osserman.Proofs.Six3.setting_T_ker_Kt_proved B E L K g0 h

/-- **Setting (T), non-vacuity** (Lean-only row, review a2-six SHOULD-2): Setting (T) is met, so the rows that assume
it are not vacuous (e.g. `E` = first 8 coordinates, `L = [I;0]`, `K = [0;I]`, `B(a) = [-ℓ_a; 0]` with `ℓ_a` the
octonion left multiplication, `g₀ = 1`). -/
theorem settingT_nonvacuous :
    ∃ (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16)) (L K : Matrix (Fin 16) (Fin 8) ℝ)
      (g0 : Vec 8), SettingT B E L K g0 :=
  Osserman.Proofs.Six3.settingT_nonvacuous_proved

/-! ## Lemma 12.1 (lem:cl-a): positive semidefinite pencils -/

/-- **Lemma 12.1** (lines 29-33 of sec_common_lemmas.tex): for real symmetric `D₀, D₁` and an interval `I` with
nonempty interior with `D(t) = D₁ + tD₀ ⪰ 0` on `I`, "$\ker D(t)=\ker D_0\cap\ker D_1$ for every interior point $t$
of $I$". -/
theorem lem_12_1 {n : ℕ} (D0 D1 : Matrix (Fin n) (Fin n) ℝ) (h0 : D0ᵀ = D0) (h1 : D1ᵀ = D1) (I : Set ℝ)
    (hI : I.OrdConnected) (hint : (interior I).Nonempty) (hpsd : ∀ t ∈ I, (D1 + t • D0).PosSemidef) :
    ∀ t ∈ interior I, LinearMap.ker (Matrix.toLin' (D1 + t • D0)) =
      LinearMap.ker (Matrix.toLin' D0) ⊓ LinearMap.ker (Matrix.toLin' D1) :=
  Osserman.Proofs.Six1.lem_12_1_proved D0 D1 h0 h1 I hI hint hpsd

/-- **Lemma 12.1** (lines 33-34 of sec_common_lemmas.tex): "Hence $D(t)$ has one image
$\mathcal F=\operatorname{Im}D_0+\operatorname{Im}D_1$ for all interior $t$." -/
theorem lem_12_1_image {n : ℕ} (D0 D1 : Matrix (Fin n) (Fin n) ℝ) (h0 : D0ᵀ = D0) (h1 : D1ᵀ = D1) (I : Set ℝ)
    (hI : I.OrdConnected) (hint : (interior I).Nonempty) (hpsd : ∀ t ∈ I, (D1 + t • D0).PosSemidef) :
    ∀ t ∈ interior I, LinearMap.range (Matrix.toLin' (D1 + t • D0)) =
      LinearMap.range (Matrix.toLin' D0) ⊔ LinearMap.range (Matrix.toLin' D1) :=
  Osserman.Proofs.Six1.lem_12_1_image_proved D0 D1 h0 h1 I hI hint hpsd

/-- **Lemma 12.1** (lines 35-36 of sec_common_lemmas.tex): "If $\rank D(t)=\rank D(t')$ for an endpoint $t$ and an
interior point $t'$, then $\ker D(t)=\ker D_0\cap\ker D_1$ as well." STRONGER than the tex: for EVERY real `t` (an
endpoint is a special case; the proof, line 46-47, works for any `t`). -/
theorem lem_12_1_endpoint {n : ℕ} (D0 D1 : Matrix (Fin n) (Fin n) ℝ) (h0 : D0ᵀ = D0) (h1 : D1ᵀ = D1) (I : Set ℝ)
    (hI : I.OrdConnected) (hint : (interior I).Nonempty) (hpsd : ∀ t ∈ I, (D1 + t • D0).PosSemidef) :
    ∀ t t' : ℝ, t' ∈ interior I → (D1 + t • D0).rank = (D1 + t' • D0).rank →
      LinearMap.ker (Matrix.toLin' (D1 + t • D0)) =
        LinearMap.ker (Matrix.toLin' D0) ⊓ LinearMap.ker (Matrix.toLin' D1) :=
  Osserman.Proofs.Six1.lem_12_1_endpoint_proved D0 D1 h0 h1 I hI hint hpsd

/-- **Lemma 12.1, proof** (lines 39-40 of sec_common_lemmas.tex): "The kernel of a sum of two positive semidefinite
matrices is the intersection of their kernels." -/
theorem lem_12_1_psd_sum_ker {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    LinearMap.ker (Matrix.toLin' (P + Q)) = LinearMap.ker (Matrix.toLin' P) ⊓ LinearMap.ker (Matrix.toLin' Q) :=
  Osserman.Proofs.Six1.lem_12_1_psd_sum_ker_proved P Q hP hQ

/-- **Lemma 12.1, proof** (lines 39-40 of sec_common_lemmas.tex, hidden step): for a positive semidefinite `P`,
`vᵀPv = 0` implies `Pv = 0`. -/
theorem lem_12_1_psd_null {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef) (v : Vec n)
    (hv : v ⬝ᵥ (P *ᵥ v) = 0) : P *ᵥ v = 0 :=
  Osserman.Proofs.Six1.lem_12_1_psd_null_proved P hP v hv

/-- **Lemma 12.1, proof** (lines 40-42 of sec_common_lemmas.tex): "An interior point $t$ is a strict convex combination
of two points $t_1<t<t_2$ of $I$, and $D$ is affine in $t$, so $\ker D(t)=\ker D(t_1)\cap\ker D(t_2)$" (for every
such pair). -/
theorem lem_12_1_interior_split {n : ℕ} (D0 D1 : Matrix (Fin n) (Fin n) ℝ) (h0 : D0ᵀ = D0) (h1 : D1ᵀ = D1)
    (I : Set ℝ) (hI : I.OrdConnected) (hint : (interior I).Nonempty) (hpsd : ∀ t ∈ I, (D1 + t • D0).PosSemidef) :
    ∀ t ∈ interior I, (∃ t1 ∈ I, ∃ t2 ∈ I, t1 < t ∧ t < t2) ∧
      ∀ t1 ∈ I, ∀ t2 ∈ I, t1 < t → t < t2 →
        LinearMap.ker (Matrix.toLin' (D1 + t • D0)) =
          LinearMap.ker (Matrix.toLin' (D1 + t1 • D0)) ⊓ LinearMap.ker (Matrix.toLin' (D1 + t2 • D0)) :=
  Osserman.Proofs.Six1.lem_12_1_interior_split_proved D0 D1 h0 h1 I hI hint hpsd

/-- **Lemma 12.1, proof** (lines 42-44 of sec_common_lemmas.tex): "A vector killed by $D(t_1)$ and $D(t_2)$ with
$t_1\ne t_2$ is killed by $D_0$ and $D_1$; the converse inclusion is clear." -/
theorem lem_12_1_two_points {n : ℕ} (D0 D1 : Matrix (Fin n) (Fin n) ℝ) (t1 t2 : ℝ) (h : t1 ≠ t2) :
    LinearMap.ker (Matrix.toLin' (D1 + t1 • D0)) ⊓ LinearMap.ker (Matrix.toLin' (D1 + t2 • D0)) =
      LinearMap.ker (Matrix.toLin' D0) ⊓ LinearMap.ker (Matrix.toLin' D1) :=
  Osserman.Proofs.Six1.lem_12_1_two_points_proved D0 D1 t1 t2 h

/-- **Lemma 12.1, proof** (lines 44-45 of sec_common_lemmas.tex): "For symmetric matrices
$(\ker D_0\cap\ker D_1)^\perp=\operatorname{Im}D_0+\operatorname{Im}D_1$." -/
theorem lem_12_1_orth {n : ℕ} (D0 D1 : Matrix (Fin n) (Fin n) ℝ) (h0 : D0ᵀ = D0) (h1 : D1ᵀ = D1) :
    orthSub (LinearMap.ker (Matrix.toLin' D0) ⊓ LinearMap.ker (Matrix.toLin' D1)) =
      LinearMap.range (Matrix.toLin' D0) ⊔ LinearMap.range (Matrix.toLin' D1) :=
  Osserman.Proofs.Six1.lem_12_1_orth_proved D0 D1 h0 h1

/-- **Lemma 12.1, proof** (lines 46-47 of sec_common_lemmas.tex): "At an endpoint
$\ker D(t)\supseteq\ker D_0\cap\ker D_1$, and equal ranks give equality" (both parts for every real `t`). -/
theorem lem_12_1_rank_eq {n : ℕ} (D0 D1 : Matrix (Fin n) (Fin n) ℝ) :
    (∀ t : ℝ, LinearMap.ker (Matrix.toLin' D0) ⊓ LinearMap.ker (Matrix.toLin' D1) ≤
      LinearMap.ker (Matrix.toLin' (D1 + t • D0))) ∧
    ∀ t t' : ℝ, LinearMap.ker (Matrix.toLin' (D1 + t' • D0)) =
        LinearMap.ker (Matrix.toLin' D0) ⊓ LinearMap.ker (Matrix.toLin' D1) →
      (D1 + t • D0).rank = (D1 + t' • D0).rank →
      LinearMap.ker (Matrix.toLin' (D1 + t • D0)) =
        LinearMap.ker (Matrix.toLin' D0) ⊓ LinearMap.ker (Matrix.toLin' D1) :=
  Osserman.Proofs.Six1.lem_12_1_rank_eq_proved D0 D1

/-! ## Lemma 12.4 (lem:cl-h): the Pfaffian of skew `4 × 4` matrices -/

/-- **Lemma 12.4** (lines 84-86 of sec_common_lemmas.tex): "The Pfaffian $A_{12}A_{34}-A_{13}A_{24}+A_{14}A_{23}$ of real
skew $4\times4$ matrices is a quadratic form of signature $(3,3)$": every skew matrix is `skew4` of its six upper
entries, and in these six variables the Pfaffian becomes `sig33` after an invertible linear change of variables. -/
theorem lem_12_4_signature :
    (∀ A : Matrix (Fin 4) (Fin 4) ℝ, Aᵀ = -A → A = skew4 ![A 0 1, A 0 2, A 0 3, A 1 2, A 1 3, A 2 3]) ∧
      ∃ P : Matrix (Fin 6) (Fin 6) ℝ, IsUnit P.det ∧ ∀ y : Fin 6 → ℝ, pf4 (skew4 (P *ᵥ y)) = sig33 y :=
  Osserman.Proofs.Six1.lem_12_4_signature_proved

/-- **Lemma 12.4** (lines 85-87 of sec_common_lemmas.tex): "Hence no four-dimensional real space of skew $4\times4$
matrices consists, apart from $0$, of invertible matrices" (for dimension at least four). -/
theorem lem_12_4 (W : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ)) (hW : ∀ A ∈ W, Aᵀ = -A)
    (h4 : 4 ≤ Module.finrank ℝ W) : ∃ A ∈ W, A ≠ 0 ∧ A.det = 0 :=
  Osserman.Proofs.Six1.lem_12_4_proved W hW h4

/-- **Lemma 12.4, proof** (lines 90-91 of sec_common_lemmas.tex): "Each of the three products is a hyperbolic plane in
its two variables": `ab = ((a+b)/2)² - ((a-b)/2)²` for the three disjoint pairs of entries. -/
theorem lem_12_4_hyperbolic_planes (A : Matrix (Fin 4) (Fin 4) ℝ) :
    pf4 A = (((A 0 1 + A 2 3) / 2) ^ 2 - ((A 0 1 - A 2 3) / 2) ^ 2) +
      (((A 0 2 - A 1 3) / 2) ^ 2 - ((A 0 2 + A 1 3) / 2) ^ 2) +
      (((A 0 3 + A 1 2) / 2) ^ 2 - ((A 0 3 - A 1 2) / 2) ^ 2) :=
  Osserman.Proofs.Six1.lem_12_4_hyperbolic_planes_proved A

/-- **Lemma 12.4, proof** (lines 91-93 of sec_common_lemmas.tex, hidden step): `det A = Pf(A)²` for a skew `4 × 4`
matrix. -/
theorem lem_12_4_det_pf (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : Aᵀ = -A) : A.det = pf4 A ^ 2 :=
  Osserman.Proofs.Six1.lem_12_4_det_pf_proved A hA

/-- **Lemma 12.4, proof** (lines 91-93 of sec_common_lemmas.tex): "A four-dimensional space whose nonzero members are
invertible carries a nowhere-vanishing restriction of the Pfaffian". -/
theorem lem_12_4_nonvanishing (W : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ)) (hW : ∀ A ∈ W, Aᵀ = -A)
    (h4 : Module.finrank ℝ W = 4) (hinv : ∀ A ∈ W, A ≠ 0 → A.det ≠ 0) : ∀ A ∈ W, A ≠ 0 → pf4 A ≠ 0 :=
  Osserman.Proofs.Six1.lem_12_4_nonvanishing_proved W hW h4 hinv

/-- **Lemma 12.4, proof** (lines 92-93 of sec_common_lemmas.tex): "which would then be definite on a four-dimensional
subspace" (hidden step: the unit sphere of the space is connected, so a nowhere-zero quadratic form has one sign). -/
theorem lem_12_4_definite (W : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ)) (hW : ∀ A ∈ W, Aᵀ = -A)
    (h4 : Module.finrank ℝ W = 4) (hnz : ∀ A ∈ W, A ≠ 0 → pf4 A ≠ 0) :
    (∀ A ∈ W, A ≠ 0 → 0 < pf4 A) ∨ ∀ A ∈ W, A ≠ 0 → pf4 A < 0 :=
  Osserman.Proofs.Six1.lem_12_4_definite_proved W hW h4 hnz

/-- **Lemma 12.4, proof** (line 94 of sec_common_lemmas.tex): "a form of signature $(3,3)$ has none" (no
four-dimensional subspace on which it is positive definite or negative definite). -/
theorem lem_12_4_sylvester (Q : (Fin 6 → ℝ) → ℝ)
    (hQ : ∃ P : Matrix (Fin 6) (Fin 6) ℝ, IsUnit P.det ∧ ∀ y : Fin 6 → ℝ, Q (P *ᵥ y) = sig33 y) :
    ¬ ∃ W : Submodule ℝ (Fin 6 → ℝ), Module.finrank ℝ W = 4 ∧
      ((∀ y ∈ W, y ≠ 0 → 0 < Q y) ∨ ∀ y ∈ W, y ≠ 0 → Q y < 0) :=
  Osserman.Proofs.Six1.lem_12_4_sylvester_proved Q hQ

/-! ## Lemma 12.5 (lem:cl-b)
`𝒲 = KᵀV₁` is `V1.map (Matrix.toLin' Kᵀ)`; "Im" is `LinearMap.range (Matrix.toLin' ·)`. -/

/-- **Lemma 12.5(1)** (lines 98-101 of sec_common_lemmas.tex): for `B` as in Setting (T) and a subspace `U ⊂ ℝ^8`,
"If $\operatorname{Im}B(a)=V_1$ for all $a\in U\setminus\{0\}$, with $V_1$ fixed, and $\dim U\ge4$, then $V_1=E$." -/
theorem lem_12_5_1 (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) = V1)
    (hU : 4 ≤ Module.finrank ℝ U) : V1 = E :=
  Osserman.Proofs.Six3.lem_12_5_1_proved B E L K g0 h U V1 hIm hU

/-- **Lemma 12.5(2)** (lines 102-104 of sec_common_lemmas.tex): "If $\operatorname{Im}B(a)\subset V_1$ for all
$a\in U\setminus\{0\}$, with $V_1$ fixed, $\dim V_1\le9$ and $\dim U\ge7$, then $\operatorname{Im}B(a)=E$ for every
$a\in U\setminus\{0\}$." -/
theorem lem_12_5_2 (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) ≤ V1)
    (hV : Module.finrank ℝ V1 ≤ 9) (hU : 7 ≤ Module.finrank ℝ U) :
    ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) = E :=
  Osserman.Proofs.Six3.lem_12_5_2_proved B E L K g0 h U V1 hIm hV hU

/-- **Lemma 12.5, proof** (lines 108-109 of sec_common_lemmas.tex): "In both parts the radial identity in
(eq:cl-setting) gives $L(U)\subset V_1\cap E$" (under the weaker containment hypothesis of part (2)). -/
theorem lem_12_5_radial (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) ≤ V1) :
    U.map (Matrix.toLin' L) ≤ V1 ⊓ E :=
  Osserman.Proofs.Six3.lem_12_5_radial_proved B E L K g0 h U V1 hIm

/-- **Lemma 12.5, proof** (lines 109-110 of sec_common_lemmas.tex): "Put $\mathcal W=K^TV_1$; then
$\dim\mathcal W=\dim V_1-\dim(V_1\cap E)\le\dim V_1-\dim U$" (written without subtraction). -/
theorem lem_12_5_dim_W (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) ≤ V1) :
    Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) + Module.finrank ℝ ↥(V1 ⊓ E) = Module.finrank ℝ V1 ∧
      Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) + Module.finrank ℝ U ≤ Module.finrank ℝ V1 :=
  Osserman.Proofs.Six3.lem_12_5_dim_W_proved B E L K g0 h U V1 hIm

/-- **Lemma 12.5, proof** (lines 110-111 of sec_common_lemmas.tex): "the skew map $K^TB(a)$ has image in $\mathcal W$
for $a\in U$". -/
theorem lem_12_5_image_W (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) ≤ V1) :
    ∀ a ∈ U, LinearMap.range (Matrix.toLin' (Kᵀ * B a)) ≤ V1.map (Matrix.toLin' Kᵀ) ∧
      (Kᵀ * B a)ᵀ = -(Kᵀ * B a) :=
  Osserman.Proofs.Six3.lem_12_5_image_W_proved B E L K g0 h U V1 hIm

/-- **Lemma 12.5(1), proof** (lines 113-114 of sec_common_lemmas.tex): "Here $\dim\mathcal W\le4$, and $K^TB(a)$ has
image exactly $\mathcal W$ for every nonzero $a\in U$" (hidden step: `dim V₁ = 8`, by rank eight). -/
theorem lem_12_5_1_W (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) = V1)
    (hU : 4 ≤ Module.finrank ℝ U) :
    Module.finrank ℝ V1 = 8 ∧ Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) ≤ 4 ∧
      ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (Kᵀ * B a)) = V1.map (Matrix.toLin' Kᵀ) :=
  Osserman.Proofs.Six3.lem_12_5_1_W_proved B E L K g0 h U V1 hIm hU

/-- **Lemma 12.5(1), proof** (lines 114-116 of sec_common_lemmas.tex), the general fact: "A skew map with image
$\mathcal W$ vanishes on $\mathcal W^\perp$ and is invertible on $\mathcal W$"; its rank is even; and (line 129) "A
skew map with image of dimension at most one is zero". -/
theorem lem_12_5_skew_facts {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : Sᵀ = -S) :
    LinearMap.ker (Matrix.toLin' S) = orthSub (LinearMap.range (Matrix.toLin' S)) ∧
      (∀ v ∈ LinearMap.range (Matrix.toLin' S), S *ᵥ v = 0 → v = 0) ∧
      Even (Module.finrank ℝ (LinearMap.range (Matrix.toLin' S))) ∧
      (Module.finrank ℝ (LinearMap.range (Matrix.toLin' S)) ≤ 1 → S = 0) :=
  Osserman.Proofs.Six3.lem_12_5_skew_facts_proved S hS

/-- **Lemma 12.5(1), proof** (line 116 of sec_common_lemmas.tex): "so $r=\dim\mathcal W\in\{0,2,4\}$". -/
theorem lem_12_5_1_r_even (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) = V1)
    (hU : 4 ≤ Module.finrank ℝ U) :
    Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) = 0 ∨ Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) = 2 ∨
      Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) = 4 :=
  Osserman.Proofs.Six3.lem_12_5_1_r_even_proved B E L K g0 h U V1 hIm hU

/-- **Lemma 12.5, proof** (lines 117-118 and 125-126 of sec_common_lemmas.tex, hidden general fact): the skew maps of
`ℝ^n` with image in a subspace `W` of dimension `r` (the skew maps "supported on `W`") form a space of dimension
`r(r-1)/2` (one for `r = 2`, zero for `r ≤ 1`). -/
theorem lem_12_5_skew_supported {n : ℕ} (W : Submodule ℝ (Vec n)) :
    ∃ S : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ),
      (∀ M, M ∈ S ↔ Mᵀ = -M ∧ LinearMap.range (Matrix.toLin' M) ≤ W) ∧
      Module.finrank ℝ S = Module.finrank ℝ W * (Module.finrank ℝ W - 1) / 2 :=
  Osserman.Proofs.Six3.lem_12_5_skew_supported_proved W

/-- **Lemma 12.5(1), proof** (lines 116-122 of sec_common_lemmas.tex), the content of the steps `r = 2` and `r = 4`
stated for EVERY `r = dim 𝒲` (review a2-six SHOULD-3; written in an orthonormal basis `W_m` of `𝒲`): `dim U + r ≤ 8`
(so `r = 4` forces `dim U = 4`); for `r > 0`, `a ↦ KᵀB(a)` is injective on `U` ("contradicting rank two" / "embeds
`U`"); the restrictions `W_mᵀ(KᵀB(a))W_m` are skew, and invertible for `a ≠ 0` ("invertible skew maps of `𝒲`"). -/
theorem lem_12_5_1_restrict (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) = V1)
    (hU : 4 ≤ Module.finrank ℝ U) {r : ℕ} (Wm : Matrix (Fin 8) (Fin r) ℝ) (hWm : Wmᵀ * Wm = 1)
    (hWr : LinearMap.range (Matrix.toLin' Wm) = V1.map (Matrix.toLin' Kᵀ)) :
    Module.finrank ℝ U + r ≤ 8 ∧ (0 < r → ∀ a ∈ U, Kᵀ * B a = 0 → a = 0) ∧
      (∀ a ∈ U, (Wmᵀ * (Kᵀ * B a) * Wm)ᵀ = -(Wmᵀ * (Kᵀ * B a) * Wm)) ∧
      ∀ a ∈ U, a ≠ 0 → (Wmᵀ * (Kᵀ * B a) * Wm).det ≠ 0 :=
  Osserman.Proofs.Six3.lem_12_5_1_restrict_proved B E L K g0 h U V1 hIm hU Wm hWm hWr

/-- **Lemma 12.5(1), proof** (lines 116-119 of sec_common_lemmas.tex): "If $r=2$, the linear map $a\mapsto K^TB(a)$ sends
$U$ into the one-dimensional space of skew maps supported on $\mathcal W$, so it has a nonzero kernel, contradicting
rank two": `r ≠ 2`. Route: `lem_12_5_1_restrict` (injective on `U` for `r > 0`) with `lem_12_5_skew_supported`
(dimension `1` for `r = 2`, while `dim U ≥ 4 > 1`). -/
theorem lem_12_5_1_r_ne_2 (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) = V1)
    (hU : 4 ≤ Module.finrank ℝ U) :
    Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) ≠ 2 :=
  Osserman.Proofs.Six3.lem_12_5_1_r_ne_2_proved B E L K g0 h U V1 hIm hU

/-- **Lemma 12.5(1), proof** (lines 119-122 of sec_common_lemmas.tex): "If $r=4$, then $\dim U=4$ and
$a\mapsto K^TB(a)|_{\mathcal W}$ embeds $U$ as a four-dimensional space of invertible skew maps of $\mathcal W$, which
Lemma 12.4 excludes": `r ≠ 4`. Route: `lem_12_5_1_restrict` (the restrictions to `𝒲` in an orthonormal basis) with
`lem_12_4`. -/
theorem lem_12_5_1_r_ne_4 (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) = V1)
    (hU : 4 ≤ Module.finrank ℝ U) :
    Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) ≠ 4 :=
  Osserman.Proofs.Six3.lem_12_5_1_r_ne_4_proved B E L K g0 h U V1 hIm hU

/-- **Lemma 12.5(1), proof** (lines 122-123 of sec_common_lemmas.tex): "Hence $r=0$, so $V_1\subset E$, and
$\dim V_1=8$ gives $V_1=E$." -/
theorem lem_12_5_1_r_zero (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) = V1)
    (hU : 4 ≤ Module.finrank ℝ U) :
    Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) = 0 ∧ V1 ≤ E ∧ V1 = E :=
  Osserman.Proofs.Six3.lem_12_5_1_r_zero_proved B E L K g0 h U V1 hIm hU

/-- **Lemma 12.5(2), proof** (lines 125-126 of sec_common_lemmas.tex): "Here $\dim\mathcal W\le2$, so every $K^TB(a)$
with $a\in U$ lies in a space of skew maps of dimension at most one." -/
theorem lem_12_5_2_W (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) ≤ V1)
    (hV : Module.finrank ℝ V1 ≤ 9) (hU : 7 ≤ Module.finrank ℝ U) :
    Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) ≤ 2 ∧
      ∃ S : Submodule ℝ (Matrix (Fin 8) (Fin 8) ℝ), Module.finrank ℝ S ≤ 1 ∧ (∀ M ∈ S, Mᵀ = -M) ∧
        ∀ a ∈ U, Kᵀ * B a ∈ S :=
  Osserman.Proofs.Six3.lem_12_5_2_W_proved B E L K g0 h U V1 hIm hV hU

/-- **Lemma 12.5(2), proof** (lines 126-128 of sec_common_lemmas.tex): "Since $\dim U\ge2$, some $a_0\ne0$ in $U$ has
$K^TB(a_0)=0$; then $\operatorname{Im}B(a_0)=E$ by rank eight, so $E\subset V_1$ and $\dim\mathcal W\le1$." -/
theorem lem_12_5_2_a0 (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) ≤ V1)
    (hV : Module.finrank ℝ V1 ≤ 9) (hU : 7 ≤ Module.finrank ℝ U) :
    ∃ a0 ∈ U, a0 ≠ 0 ∧ Kᵀ * B a0 = 0 ∧ LinearMap.range (Matrix.toLin' (B a0)) = E ∧ E ≤ V1 ∧
      Module.finrank ℝ (V1.map (Matrix.toLin' Kᵀ)) ≤ 1 :=
  Osserman.Proofs.Six3.lem_12_5_2_a0_proved B E L K g0 h U V1 hIm hV hU

/-- **Lemma 12.5(2), proof** (lines 128-130 of sec_common_lemmas.tex): "A skew map with image of dimension at most one is
zero, so $K^TB(a)=0$ on $U$, and rank eight gives the assertion." -/
theorem lem_12_5_2_zero (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16))
    (L K : Matrix (Fin 16) (Fin 8) ℝ) (g0 : Vec 8) (h : SettingT B E L K g0) (U : Submodule ℝ (Vec 8))
    (V1 : Submodule ℝ (Vec 16)) (hIm : ∀ a ∈ U, a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) ≤ V1)
    (hV : Module.finrank ℝ V1 ≤ 9) (hU : 7 ≤ Module.finrank ℝ U) :
    ∀ a ∈ U, Kᵀ * B a = 0 ∧ (a ≠ 0 → LinearMap.range (Matrix.toLin' (B a)) = E) :=
  Osserman.Proofs.Six3.lem_12_5_2_zero_proved B E L K g0 h U V1 hIm hV hU

/-! ## Lemma 12.6 (lem:cl-j): spaces of matrices of rank at most one -/

/-- **Lemma 12.6** (lines 134-135 of sec_common_lemmas.tex): "A linear space of matrices over a field, all of rank at
most one, either has all images in one fixed line or has all rows in one fixed line" (matrices of any size; "in a
line" is written as "in the span of one vector", which is the same when the ambient space is nonzero). -/
theorem lem_12_6 {𝕜 : Type*} [Field 𝕜] {m n : ℕ} (S : Submodule 𝕜 (Matrix (Fin m) (Fin n) 𝕜))
    (hS : ∀ M ∈ S, M.rank ≤ 1) :
    (∃ w : Fin m → 𝕜, ∀ M ∈ S, LinearMap.range (Matrix.toLin' M) ≤ Submodule.span 𝕜 {w}) ∨
      ∃ e : Fin n → 𝕜, ∀ M ∈ S, ∀ i, M i ∈ Submodule.span 𝕜 {e} :=
  Osserman.Proofs.Six1.lem_12_6_proved S hS

/-- **Lemma 12.6, proof** (line 138 of sec_common_lemmas.tex, hidden step): "Write two nonzero members as $w_1e_1^*$
and $w_2e_2^*$": a matrix of rank at most one is `w eᵀ`. -/
theorem lem_12_6_rank_one {𝕜 : Type*} [Field 𝕜] {m n : ℕ} (M : Matrix (Fin m) (Fin n) 𝕜) (hM : M.rank ≤ 1) :
    ∃ (w : Fin m → 𝕜) (e : Fin n → 𝕜), M = vecMulVec w e :=
  Osserman.Proofs.Six1.lem_12_6_rank_one_proved M hM

/-- **Lemma 12.6, proof** (lines 138-142 of sec_common_lemmas.tex): "If $w_1,w_2$ are independent, rank at most one of
the sum forces $e_1,e_2$ to be proportional; a third member $w_3e_3^*$ has $w_3$ independent of $w_1$ or of $w_2$, so
the same argument makes $e_3$ proportional to $e_1$ or to $e_2$, hence to both." -/
theorem lem_12_6_pair {𝕜 : Type*} [Field 𝕜] {m n : ℕ} (S : Submodule 𝕜 (Matrix (Fin m) (Fin n) 𝕜))
    (hS : ∀ M ∈ S, M.rank ≤ 1) :
    ∀ (w1 w2 : Fin m → 𝕜) (e1 e2 : Fin n → 𝕜), vecMulVec w1 e1 ∈ S → vecMulVec w2 e2 ∈ S →
      LinearIndependent 𝕜 ![w1, w2] → e1 ≠ 0 → e2 ≠ 0 →
      e2 ∈ Submodule.span 𝕜 {e1} ∧ ∀ M ∈ S, ∀ i, M i ∈ Submodule.span 𝕜 {e1} :=
  Osserman.Proofs.Six1.lem_12_6_pair_proved S hS

/-- **Lemma 12.6, proof** (line 142 of sec_common_lemmas.tex): "If no such pair exists, the image line is common" (no
two members have images spanning a plane). -/
theorem lem_12_6_common_image {𝕜 : Type*} [Field 𝕜] {m n : ℕ} (S : Submodule 𝕜 (Matrix (Fin m) (Fin n) 𝕜))
    (hS : ∀ M ∈ S, M.rank ≤ 1)
    (hno : ∀ M1 ∈ S, ∀ M2 ∈ S,
      Module.finrank 𝕜 ↥(LinearMap.range (Matrix.toLin' M1) ⊔ LinearMap.range (Matrix.toLin' M2)) ≤ 1) :
    ∃ w : Fin m → 𝕜, ∀ M ∈ S, LinearMap.range (Matrix.toLin' M) ≤ Submodule.span 𝕜 {w} :=
  Osserman.Proofs.Six1.lem_12_6_common_image_proved S hS hno

/-! ## Theorem G (thm:extreme) and the anisotropy step of its proof (§9.4)
The field `𝔼 = 𝔽(α)` is ANY field extension of `𝔽` generated by an `α` with `α² = -d`. -/

/-- **Theorem G, proof** (lines 237-238 of sec_polynomial_gram.tex, with lines 11-15): "Shift the extreme eigenvalue of
multiplicity seven or eight to zero; then $\nu=7$ or $8$ and $\Lambda$ is definite": `J'_x = J_x - μ₀Π(x)` has rank
`ν = 15 - m` at unit `x`, is semidefinite of one sign (positive if `μ₀` is the smallest, negative if the largest),
and so is definite the matrix `Λ` of any orthonormal frame `M_X` of `Im J'_X` with `J'_X = M_XΛM_Xᵀ`. -/
theorem thm_G_shift (R : CurvTensor 16) (hO : R.IsOsserman) (μ0 : ℝ) (m : ℕ) (hm : m = 7 ∨ m = 8)
    (hmult : ∀ x : Vec 16, x ⬝ᵥ x = 1 → R.redMult x μ0 = m) :
    (∀ x : Vec 16, x ⬝ᵥ x = 1 → (R.jacobi x - μ0 • Pi x).rank = 15 - m) ∧
      (IsSmallestRed R μ0 → ∀ x : Vec 16, (R.jacobi x - μ0 • Pi x).PosSemidef) ∧
      (IsLargestRed R μ0 → ∀ x : Vec 16, (-(R.jacobi x - μ0 • Pi x)).PosSemidef) ∧
      ∀ Xa : Vec 16, Xa ⬝ᵥ Xa = 1 → ∀ (ν : ℕ) (MX : Matrix (Fin 16) (Fin ν) ℝ) (Λ : Matrix (Fin ν) (Fin ν) ℝ),
        MXᵀ * MX = 1 → LinearMap.range (Matrix.toLin' MX) = LinearMap.range (Matrix.toLin' (R.jacobi Xa - μ0 • Pi Xa)) →
        R.jacobi Xa - μ0 • Pi Xa = MX * Λ * MXᵀ →
        ν = 15 - m ∧ (IsSmallestRed R μ0 → Λ.PosDef) ∧ (IsLargestRed R μ0 → (-Λ).PosDef) :=
  Osserman.Proofs.Six4.thm_G_shift_proved R hO μ0 m hm hmult

/-- **Theorem G, proof, bridge** (Lean-only row; lines 11-15 and 238-250 of sec_polynomial_gram.tex): the polynomial
extension `jacAlg` of the shifted Jacobi family, at a real vector, is the shifted Jacobi matrix `J_x - μ₀Π(x)`. -/
theorem jacAlg_real (R : CurvTensor 16) (μ0 : ℝ) (x : Vec 16) :
    jacAlg R μ0 (RingHom.id ℝ) x = R.jacobi x - μ0 • Pi x :=
  Osserman.Proofs.Six4.jacAlg_real_proved R μ0 x

/-- **Theorem G, proof** (lines 241-244 of sec_polynomial_gram.tex): "$G(s)=s^2I+s\Phi_1+\Phi_0$, where
$\Phi_1=M_X^TM_Y+M_Y^TM_X$ and $\Phi_0=M_Y^TM_Y$ have entries in $\mathbb F$; thus $G(s)=\Phi(sX+Y)$ is the full Gram":
`(sM_X+M_Y)ᵀ(sM_X+M_Y) = G(s)` (hidden: `M_XᵀM_X = I`), and `Φ₀, Φ₁` are symmetric (hidden). -/
theorem thm_G_gram_pencil {ν : ℕ} (MX : Matrix (Fin 16) (Fin ν) ℝ) (MY : Matrix (Fin 16) (Fin ν) RatF15)
    (hMX : MXᵀ * MX = 1) :
    (factorS MX MY)ᵀ * factorS MX MY = GramS (Phi1 MX MY) (Phi0 MY) ∧ (Phi1 MX MY)ᵀ = Phi1 MX MY ∧
      (Phi0 MY)ᵀ = Phi0 MY :=
  Osserman.Proofs.Six4.thm_G_gram_pencil_proved MX MY hMX

/-- **Theorem G, proof** (lines 244-250 of sec_polynomial_gram.tex), (eq:spectralpencil): "Equality of the nonzero Jacobi
spectra gives $\det(tI-\Lambda G(s))=\prod_{i=1}^{\nu}(t-(s^2+d)\mu_i)$ in $\mathbb F[s,t]$", for `Λ = diag(μ)` the
nonzero eigenvalues and the data of Lemma 9.3 (any shift `μ₀`; the proof needs only that `R` is Osserman). -/
theorem thm_G_spectral_pencil (R : CurvTensor 16) (hO : R.IsOsserman) (μ0 : ℝ) {ν : ℕ} (μ : Fin ν → ℝ)
    (hμ : ∀ i, μ i ≠ 0) (Xa : Vec 16) (f : Fin 15 → Vec 16) (MX : Matrix (Fin 16) (Fin ν) ℝ)
    (MY : Matrix (Fin 16) (Fin ν) RatF15) (hP : IsRationalPartner R μ0 (diagonal μ) Xa f MX MY) :
    SpectralPencil μ (Phi1 MX MY) (Phi0 MY) :=
  Osserman.Proofs.Six4.thm_G_spectral_pencil_proved R hO μ0 μ hμ Xa f MX MY hP

/-- **Theorem G, proof** (lines 252-253 of sec_polynomial_gram.tex): "Let $\mathbb E=\mathbb F(\alpha)$ with
$\alpha^2=-d$; as $\mathbb F$ is formally real, $[\mathbb E:\mathbb F]=2$" (hidden: `-d` is not a square in `𝔽`). -/
theorem thm_G_degree_two (𝔼 : Type*) [Field 𝔼] [Algebra RatF15 𝔼] (α : 𝔼)
    (hα : α ^ 2 = -algebraMap RatF15 𝔼 dF) (hgen : IntermediateField.adjoin RatF15 {α} = ⊤) :
    IsFormallyReal RatF15 ∧ (∀ c : RatF15, c ^ 2 ≠ -dF) ∧ Module.finrank RatF15 𝔼 = 2 :=
  Osserman.Proofs.Six4.thm_G_degree_two_proved 𝔼 α hα hgen

/-- **Theorem G, proof** (lines 253-254 of sec_polynomial_gram.tex): "$\mathbb E$ is the fraction field of
$\R[s,y_1,\ldots,y_{15}]/(s^2+y_1^2+\cdots+y_{15}^2)$": the map `s ↦ α`, `y_i ↦ y_i` (variable `0` is `s`, variable
`i+1` is `y_i`; the relation is `sqP 16`) makes `𝔼` a fraction field of this quotient. -/
theorem thm_G_fraction_field (𝔼 : Type*) [Field 𝔼] [Algebra RatF15 𝔼] (α : 𝔼)
    (hα : α ^ 2 = -algebraMap RatF15 𝔼 dF) (hgen : IntermediateField.adjoin RatF15 {α} = ⊤) :
    ∃ φ : (MvPolynomial (Fin 16) ℝ ⧸ Ideal.span {sqP 16}) →+* 𝔼,
      (∀ p, φ (Ideal.Quotient.mk _ p) =
        MvPolynomial.eval₂ ((algebraMap RatF15 𝔼).comp ofRealF)
          (Fin.cons α (fun i : Fin 15 => algebraMap RatF15 𝔼 (yF i)) : Fin 16 → 𝔼) p) ∧
      (letI : Algebra (MvPolynomial (Fin 16) ℝ ⧸ Ideal.span {sqP 16}) 𝔼 := φ.toAlgebra
       IsFractionRing (MvPolynomial (Fin 16) ℝ ⧸ Ideal.span {sqP 16}) 𝔼) :=
  Osserman.Proofs.Six4.thm_G_fraction_field_proved 𝔼 α hα hgen

/-- **Theorem G, proof** (lines 254-257 of sec_polynomial_gram.tex), ADAPTED-CITED ([Nik2006, Lemma 3.11 and its
proof, p. 398]; the field form is derived here, from the cited STATEMENT `Osserman.Cited.nik2006_lemma_3_11` and
`thm_G_fraction_field` by clearing denominators — no stronger cited input, review a2-s7 N-3): "a sum of
at most eight squares in $\mathbb E$ vanishes only when every term vanishes". -/
theorem thm_G_eight_squares (𝔼 : Type*) [Field 𝔼] [Algebra RatF15 𝔼] (α : 𝔼)
    (hα : α ^ 2 = -algebraMap RatF15 𝔼 dF) (hgen : IntermediateField.adjoin RatF15 {α} = ⊤) :
    ∀ k : ℕ, k ≤ 8 → ∀ v : Fin k → 𝔼, ∑ i, v i ^ 2 = 0 → ∀ i, v i = 0 :=
  Osserman.Proofs.Six4.thm_G_eight_squares_proved 𝔼 α hα hgen

/-- **Theorem G, proof** (lines 256-258 of sec_polynomial_gram.tex): "so every constant definite real quadratic form of
dimension at most eight is anisotropic over $\mathbb E$" (positive or negative definite). -/
theorem thm_G_anisotropic (𝔼 : Type*) [Field 𝔼] [Algebra RatF15 𝔼] (α : 𝔼)
    (hα : α ^ 2 = -algebraMap RatF15 𝔼 dF) (hgen : IntermediateField.adjoin RatF15 {α} = ⊤) :
    ∀ k : ℕ, k ≤ 8 → ∀ H : Matrix (Fin k) (Fin k) ℝ, (H.PosDef ∨ (-H).PosDef) →
      ∀ v : Fin k → 𝔼, v ⬝ᵥ (H.map ((algebraMap RatF15 𝔼).comp ofRealF) *ᵥ v) = 0 → v = 0 :=
  Osserman.Proofs.Six4.thm_G_anisotropic_proved 𝔼 α hα hgen

/-- **Theorem G, proof** (lines 258-259 of sec_polynomial_gram.tex): "At $s=\alpha$, (eq:spectralpencil) shows that
$N=\Lambda G(\alpha)$ is nilpotent" (hidden: `α² + d = 0`, so its characteristic polynomial is `t^ν`;
Cayley–Hamilton). -/
theorem thm_G_nilpotent {ν : ℕ} (μ : Fin ν → ℝ) (Φ1 Φ0 : Matrix (Fin ν) (Fin ν) RatF15)
    (hspec : SpectralPencil μ Φ1 Φ0) (𝔼 : Type*) [Field 𝔼] [Algebra RatF15 𝔼] (α : 𝔼)
    (hα : α ^ 2 = -algebraMap RatF15 𝔼 dF) :
    ((diagonal μ).map ((algebraMap RatF15 𝔼).comp ofRealF) * GramAt α Φ1 Φ0).charpoly = Polynomial.X ^ ν ∧
      IsNilpotent ((diagonal μ).map ((algebraMap RatF15 𝔼).comp ofRealF) * GramAt α Φ1 Φ0) :=
  Osserman.Proofs.Six4.thm_G_nilpotent_proved μ Φ1 Φ0 hspec 𝔼 α hα

/-- **Theorem G, proof** (lines 259-261 of sec_polynomial_gram.tex): "it is self-adjoint for the anisotropic form
$\langle v,w\rangle_{\Lambda^{-1}}=v^T\Lambda^{-1}w$, since $\Lambda^{-1}N=G(\alpha)$ is symmetric". -/
theorem thm_G_self_adjoint {ν : ℕ} (μ : Fin ν → ℝ) (hμ : ∀ i, μ i ≠ 0) (Φ1 Φ0 : Matrix (Fin ν) (Fin ν) RatF15)
    (h1 : Φ1ᵀ = Φ1) (h0 : Φ0ᵀ = Φ0) (𝔼 : Type*) [Field 𝔼] [Algebra RatF15 𝔼] (α : 𝔼) :
    let Λe := (diagonal μ).map ((algebraMap RatF15 𝔼).comp ofRealF)
    let N := Λe * GramAt α Φ1 Φ0
    Λe⁻¹ * N = GramAt α Φ1 Φ0 ∧ (GramAt α Φ1 Φ0)ᵀ = GramAt α Φ1 Φ0 ∧
      ∀ v w : Fin ν → 𝔼, (N *ᵥ v) ⬝ᵥ (Λe⁻¹ *ᵥ w) = v ⬝ᵥ (Λe⁻¹ *ᵥ (N *ᵥ w)) :=
  Osserman.Proofs.Six4.thm_G_self_adjoint_proved μ hμ Φ1 Φ0 h1 h0 𝔼 α

/-- **Theorem G, proof** (lines 261-264 of sec_polynomial_gram.tex): "Such an $N$ is zero: if its nilpotency index were
$e\ge2$, then $w=N^{e-1}v\ne0$ for some $v$ and $\langle w,w\rangle_{\Lambda^{-1}}=\langle v,N^{2e-2}v\rangle_{\Lambda^{-1}}=0$,
contradicting anisotropy" (over any field, for any anisotropic form `vᵀHv`). -/
theorem thm_G_nilpotent_self_adjoint_zero {K : Type*} [Field K] {n : ℕ} (H N : Matrix (Fin n) (Fin n) K)
    (hanis : ∀ v : Fin n → K, v ⬝ᵥ (H *ᵥ v) = 0 → v = 0)
    (hadj : ∀ v w : Fin n → K, (N *ᵥ v) ⬝ᵥ (H *ᵥ w) = v ⬝ᵥ (H *ᵥ (N *ᵥ w))) (hnil : IsNilpotent N) : N = 0 :=
  Osserman.Proofs.Six4.thm_G_nilpotent_self_adjoint_zero_proved H N hanis hadj hnil

/-- **Theorem G, proof** (lines 264-265 of sec_polynomial_gram.tex): `N = ΛG(α) = 0`, and "As $\Lambda$ is invertible,
$\Phi_0-dI+\alpha\Phi_1=0$" (for `Λ = diag(μ)` definite of size `ν ≤ 8`). -/
theorem thm_G_G_alpha_zero {ν : ℕ} (hν : ν ≤ 8) (μ : Fin ν → ℝ) (hdef : (∀ i, 0 < μ i) ∨ ∀ i, μ i < 0)
    (Φ1 Φ0 : Matrix (Fin ν) (Fin ν) RatF15) (h1 : Φ1ᵀ = Φ1) (h0 : Φ0ᵀ = Φ0) (hspec : SpectralPencil μ Φ1 Φ0)
    (𝔼 : Type*) [Field 𝔼] [Algebra RatF15 𝔼] (α : 𝔼) (hα : α ^ 2 = -algebraMap RatF15 𝔼 dF)
    (hgen : IntermediateField.adjoin RatF15 {α} = ⊤) :
    (diagonal μ).map ((algebraMap RatF15 𝔼).comp ofRealF) * GramAt α Φ1 Φ0 = 0 ∧
      Φ0.map (algebraMap RatF15 𝔼) - algebraMap RatF15 𝔼 dF • (1 : Matrix (Fin ν) (Fin ν) 𝔼) +
        α • Φ1.map (algebraMap RatF15 𝔼) = 0 :=
  Osserman.Proofs.Six4.thm_G_G_alpha_zero_proved hν μ hdef Φ1 Φ0 h1 h0 hspec 𝔼 α hα hgen

/-- **Theorem G, proof** (lines 265-266 of sec_polynomial_gram.tex): "the independence of $1,\alpha$ over $\mathbb F$
gives $\Phi_1=0$ and $\Phi_0=dI$". -/
theorem thm_G_Phi_scalar {ν : ℕ} (Φ1 Φ0 : Matrix (Fin ν) (Fin ν) RatF15) (𝔼 : Type*) [Field 𝔼] [Algebra RatF15 𝔼]
    (α : 𝔼) (hα : α ^ 2 = -algebraMap RatF15 𝔼 dF) (hgen : IntermediateField.adjoin RatF15 {α} = ⊤)
    (h : Φ0.map (algebraMap RatF15 𝔼) - algebraMap RatF15 𝔼 dF • (1 : Matrix (Fin ν) (Fin ν) 𝔼) +
      α • Φ1.map (algebraMap RatF15 𝔼) = 0) :
    LinearIndependent RatF15 ![(1 : 𝔼), α] ∧ Φ1 = 0 ∧ Φ0 = dF • (1 : Matrix (Fin ν) (Fin ν) RatF15) :=
  Osserman.Proofs.Six4.thm_G_Phi_scalar_proved Φ1 Φ0 𝔼 α hα hgen h

/-- **Theorem G, proof** (lines 265-267 of sec_polynomial_gram.tex): for the data of Lemma 9.3 of the tensor shifted by
the extreme eigenvalue `μ₀`, `Φ₁ = 0`, `Φ₀ = dI`, "So the full Gram is $G(s)=(s^2+d)I$" (the end of the anisotropy step).
"Polynomial on $\R^{16}$" is the next row, `thm_G_q_pointS`; "Proposition 9.1(2) makes $R$ Clifford" needs
Proposition 9.1(2) (Section 9, outside the formalized scope; AUDIT.md route note 11). The hypothesis of three reduced
eigenvalues (pg l. 5) is used only by Prop. 9.1(2) and is not needed here. -/
theorem thm_G_conclude (R : CurvTensor 16) (hO : R.IsOsserman) (μ0 : ℝ)
    (hext : IsExtremeSevenEight R μ0) {ν : ℕ} (μ : Fin ν → ℝ) (hμ : ∀ i, μ i ≠ 0) (Xa : Vec 16)
    (f : Fin 15 → Vec 16) (MX : Matrix (Fin 16) (Fin ν) ℝ) (MY : Matrix (Fin 16) (Fin ν) RatF15)
    (hP : IsRationalPartner R μ0 (diagonal μ) Xa f MX MY) :
    Phi1 MX MY = 0 ∧ Phi0 MY = dF • (1 : Matrix (Fin ν) (Fin ν) RatF15) ∧
      GramS (Phi1 MX MY) (Phi0 MY) =
        (Polynomial.X ^ 2 + Polynomial.C dF) • (1 : Matrix (Fin ν) (Fin ν) (Polynomial RatF15)) :=
  Osserman.Proofs.Six4d.thm_G_conclude_proved thm_G_spectral_pencil R hO μ0 hext μ hμ Xa f MX MY hP

/-- **Theorem G, proof** (lines 241 and 266-267 of sec_polynomial_gram.tex): "polynomial on $\R^{16}$": in the
coordinates of Lemma 9.3, `s² + d = |z|² = ∑_a z_a²` at `z = sX + Y`, so `G(s) = (s² + d)I` is `|z|²I`
(review a2-six SHOULD-1). -/
theorem thm_G_q_pointS (Xa : Vec 16) (f : Fin 15 → Vec 16) (hX : Xa ⬝ᵥ Xa = 1) (hXf : ∀ i, Xa ⬝ᵥ f i = 0)
    (hf : ∀ i j, f i ⬝ᵥ f j = if i = j then 1 else 0) :
    ∑ a, pointS Xa f a ^ 2 = Polynomial.X ^ 2 + Polynomial.C dF :=
  Osserman.Proofs.Six4.thm_G_q_pointS_proved Xa f hX hXf hf

/-- **Theorem G, non-vacuity** (Lean-only row, review a2-six SHOULD-2): the hypotheses of `thm_G_conclude` are met
(e.g. a Clifford tensor `J_x = ∑ η_i (J_i x)(J_i x)ᵀ` with a `Cl(8)`-structure, `η_i > 0`, `μ₀ = 0`, `M_X = [J_i X]`,
`M_Y = [J_i Y]`). -/
theorem thm_G_partner_nonvacuous :
    ∃ (R : CurvTensor 16) (μ0 : ℝ) (ν : ℕ) (μ : Fin ν → ℝ) (Xa : Vec 16) (f : Fin 15 → Vec 16)
      (MX : Matrix (Fin 16) (Fin ν) ℝ) (MY : Matrix (Fin 16) (Fin ν) RatF15),
      R.IsOsserman ∧ IsExtremeSevenEight R μ0 ∧ (∀ i, μ i ≠ 0) ∧
        IsRationalPartner R μ0 (diagonal μ) Xa f MX MY :=
  Osserman.Proofs.Six4w.thm_G_partner_nonvacuous_proved

/-! ## Lemma 24.5 (lem:sie-local-splitting)
A symmetric bilinear form on the free module `T²` is given by its symmetric Gram matrix `Bm`; "unimodular" is
`IsUnit Bm.det`; `FractionRing T` is `Frac(T)`. -/

/-- **Lemma 24.5 (Local splitting)** (lines 156-159 of sec_singular_integral_extraction.tex): "Let $T$ be a normal local
domain in which $2$ is invertible. A unimodular symmetric bilinear form on a free $T$-module of rank two which is
hyperbolic over $\operatorname{Frac}(T)$ splits over $T$ into two free isotropic lines": a `T`-basis `(Pe₀, Pe₁)`
of two isotropic vectors. -/
theorem lem_24_5 {T : Type*} [CommRing T] [IsDomain T] [IsLocalRing T] [IsIntegrallyClosed T] (h2 : IsUnit (2 : T))
    (Bm : Matrix (Fin 2) (Fin 2) T) (hsym : Bmᵀ = Bm) (hunimod : IsUnit Bm.det)
    (hhyp : IsHyperbolic2 (Bm.map (algebraMap T (FractionRing T)))) :
    ∃ P : Matrix (Fin 2) (Fin 2) T, IsUnit P.det ∧ (Pᵀ * Bm * P) 0 0 = 0 ∧ (Pᵀ * Bm * P) 1 1 = 0 :=
  Osserman.Proofs.Six2.lem_24_5_proved h2 Bm hsym hunimod hhyp

/-- **Lemma 24.5, proof** (lines 162-164 of sec_singular_integral_extraction.tex): "There is a vector whose norm is a
unit of $T$". -/
theorem lem_24_5_unit_norm {T : Type*} [CommRing T] [IsLocalRing T] (h2 : IsUnit (2 : T))
    (Bm : Matrix (Fin 2) (Fin 2) T) (hsym : Bmᵀ = Bm) (hunimod : IsUnit Bm.det) :
    ∃ v : Fin 2 → T, IsUnit (v ⬝ᵥ (Bm *ᵥ v)) :=
  Osserman.Proofs.Six2.lem_24_5_unit_norm_proved h2 Bm hsym hunimod

/-- **Lemma 24.5, proof** (lines 162-164 of sec_singular_integral_extraction.tex): "otherwise all diagonal entries and,
by evaluation on sums of basis vectors, all matrix entries would lie in the maximal ideal" (hidden: then so does the
determinant, against unimodularity). -/
theorem lem_24_5_entries_max {T : Type*} [CommRing T] [IsLocalRing T] (h2 : IsUnit (2 : T))
    (Bm : Matrix (Fin 2) (Fin 2) T) (hsym : Bmᵀ = Bm)
    (hall : ∀ v : Fin 2 → T, v ⬝ᵥ (Bm *ᵥ v) ∈ IsLocalRing.maximalIdeal T) :
    (∀ i j, Bm i j ∈ IsLocalRing.maximalIdeal T) ∧ Bm.det ∈ IsLocalRing.maximalIdeal T :=
  Osserman.Proofs.Six2.lem_24_5_entries_max_proved h2 Bm hsym hall

/-- **Lemma 24.5, proof** (lines 164-165 of sec_singular_integral_extraction.tex): "Splitting it off gives
$\operatorname{diag}(a,b)$ with units $a,b$" (hidden: the orthogonal complement of a vector `v` of unit norm is the free
line `Tw`, `(v, w)` is a basis, and `b` is a unit by unimodularity; true over any commutative ring). -/
theorem lem_24_5_split_off {T : Type*} [CommRing T] (Bm : Matrix (Fin 2) (Fin 2) T) (hsym : Bmᵀ = Bm)
    (hunimod : IsUnit Bm.det) :
    ∀ v : Fin 2 → T, IsUnit (v ⬝ᵥ (Bm *ᵥ v)) → ∃ w : Fin 2 → T, v ⬝ᵥ (Bm *ᵥ w) = 0 ∧
      IsUnit (Matrix.of ![v, w]).det ∧ IsUnit (w ⬝ᵥ (Bm *ᵥ w)) ∧
      (∀ u : Fin 2 → T, v ⬝ᵥ (Bm *ᵥ u) = 0 ↔ ∃ c : T, u = c • w) ∧
      Matrix.of ![v, w] * Bm * (Matrix.of ![v, w])ᵀ = diagonal ![v ⬝ᵥ (Bm *ᵥ v), w ⬝ᵥ (Bm *ᵥ w)] :=
  Osserman.Proofs.Six2.lem_24_5_split_off_proved Bm hsym hunimod

/-- **Lemma 24.5, proof** (lines 165-166 of sec_singular_integral_extraction.tex): "Generic hyperbolicity gives
$r^2=-b/a$ in the fraction field". -/
theorem lem_24_5_root {T : Type*} [CommRing T] [IsDomain T] (a b : T) (ha : IsUnit a) (hb : IsUnit b)
    (hhyp : IsHyperbolic2 ((diagonal ![a, b]).map (algebraMap T (FractionRing T)))) :
    ∃ r : FractionRing T, r ^ 2 = -(algebraMap T (FractionRing T) b / algebraMap T (FractionRing T) a) :=
  Osserman.Proofs.Six2.lem_24_5_root_proved a b ha hb hhyp

/-- **Lemma 24.5, proof** (lines 166-167 of sec_singular_integral_extraction.tex): "$r$ is integral over $T$, hence in
$T$ by normality, and a unit". -/
theorem lem_24_5_integral {T : Type*} [CommRing T] [IsDomain T] [IsIntegrallyClosed T] (a b : T) (ha : IsUnit a)
    (hb : IsUnit b) (r : FractionRing T)
    (hr : r ^ 2 = -(algebraMap T (FractionRing T) b / algebraMap T (FractionRing T) a)) :
    IsIntegral T r ∧ ∃ r' : T, algebraMap T (FractionRing T) r' = r ∧ IsUnit r' ∧ a * r' ^ 2 + b = 0 :=
  Osserman.Proofs.Six2.lem_24_5_integral_proved a b ha hb r hr

/-- **Lemma 24.5, proof** (lines 167-168 of sec_singular_integral_extraction.tex): "The isotropic vectors $(r,1),(-r,1)$
form a basis, since $2r$ is a unit" (for `diag(a,b)` with `ar² + b = 0`). -/
theorem lem_24_5_basis {T : Type*} [CommRing T] (h2 : IsUnit (2 : T)) (a b r : T) (hr : IsUnit r)
    (hab : a * r ^ 2 + b = 0) :
    ![r, 1] ⬝ᵥ (diagonal ![a, b] *ᵥ ![r, 1]) = 0 ∧ ![-r, 1] ⬝ᵥ (diagonal ![a, b] *ᵥ ![-r, 1]) = 0 ∧
      IsUnit (Matrix.of ![![r, 1], ![-r, 1]]).det :=
  Osserman.Proofs.Six2.lem_24_5_basis_proved h2 a b r hr hab

/-- **Lemma 24.5, bridge to Prop. 24.6** (hidden, used at lines 198-199 of sec_singular_integral_extraction.tex,
"Lemma 24.5 makes each line closure free at $\eta$"): for every isotropic line `Frac(T)·v` of the generic form, its
saturation `{u ∈ T² | u ∈ Frac(T)·v}` is the free line `Te`, where `(e, f)` is a `T`-basis of isotropic vectors. -/
theorem lem_24_5_saturation {T : Type*} [CommRing T] [IsDomain T] [IsLocalRing T] [IsIntegrallyClosed T]
    (h2 : IsUnit (2 : T)) (Bm : Matrix (Fin 2) (Fin 2) T) (hsym : Bmᵀ = Bm) (hunimod : IsUnit Bm.det)
    (hhyp : IsHyperbolic2 (Bm.map (algebraMap T (FractionRing T)))) :
    ∀ v : Fin 2 → FractionRing T, v ≠ 0 → v ⬝ᵥ (Bm.map (algebraMap T (FractionRing T)) *ᵥ v) = 0 →
      ∃ e f : Fin 2 → T, IsUnit (Matrix.of ![e, f]).det ∧ e ⬝ᵥ (Bm *ᵥ e) = 0 ∧ f ⬝ᵥ (Bm *ᵥ f) = 0 ∧
        ∀ u : Fin 2 → T, (∃ c : FractionRing T, (fun i => algebraMap T (FractionRing T) (u i)) = c • v) ↔
          ∃ t : T, u = t • e :=
  Osserman.Proofs.Six2.lem_24_5_saturation_proved h2 Bm hsym hunimod hhyp

end Osserman.Paper
