/-
Osserman/Proofs/S8Gen.lean — the two general steps of §8.3-8.5 of paper 013: moving a linear eigenfield and the spectral
projector identity (rows s8_move_eigenfield, s8_spectral_identity; statements copied verbatim from
Osserman/Paper/Statements8.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Moving. At a unit `x` put `u = Jx` (unit, `⊥ x`, `J_x u = λ₁u`) and `J'_x = J_x - (λ₁ - λ₂)uuᵀ`, so `J'_x u = λ₂u`.
Whenever `S = R + d uuᵀ` at `x` moves `u` from the eigenvalue `s` to `t ≠ s`: `E_S(t) = E_R(t) ⊕ ℝu`, and for `t'` other
than both eigenvalues of `u`, `E_S(t') = E_R(t')` (an eigenvector of `t'` is `⊥ u`). So `λ₁` loses one, `λ₂` gains one.
Spectral identity. Both sides are homogeneous of degree 6, so take `x` unit; `p_j = P_j(x)` are orthonormal reduced
eigenvectors. `D = ∑ μ_j(μ_j - λ)p_jp_jᵀ - A(A - λ)` kills every `p_j` and `W = E_0 ⊕ E_λ ⊕ ℝx` (there `A(A - λ) = 0`
and `W ⊥ p_j`). The fields fill the other eigenspaces, so `r + m_0 + m_λ = 15`, `span p ⊕ W = ℝ^16` and `D = 0`.
-/
import Osserman.Proofs.S83Endpoint
import Osserman.Proofs.CorD
import Osserman.Proofs.Rem72a
import Osserman.Proofs.CayleyIdentify

namespace Osserman.Proofs.S8Gen

open Osserman Matrix

lemma mem_Esp' {R : CurvTensor 16} {x v : Vec 16} {t : ℝ} :
    v ∈ Spectral.Esp R x t ↔ R.jacobi x *ᵥ v = t • v ∧ x ⬝ᵥ v = 0 := by
  rw [Submodule.mem_inf, S8Tools.mem_eig_iff, Spectral.mem_perp]

/-! ### Reduced eigenspaces under a rank-one change at `x` -/

section RankOne

variable {R S : CurvTensor 16} {x u : Vec 16} {s t d : ℝ}

/-- If `S = R + d uuᵀ` at `x` and `u` is an eigenvector of `R` of `s ≠ t`, then `E_R(t) ≤ E_S(t)`. -/
lemma esp_le (hts : t ≠ s) (hjS : ∀ v, S.jacobi x *ᵥ v = R.jacobi x *ᵥ v + d • ((u ⬝ᵥ v) • u))
    (hRu : R.jacobi x *ᵥ u = s • u) : Spectral.Esp R x t ≤ Spectral.Esp S x t := by
  intro v hv
  have hvu : v ⬝ᵥ u = 0 := S83.esp_dot_eig hts hv hRu
  obtain ⟨hRv, hxv⟩ := mem_Esp'.mp hv
  refine mem_Esp'.mpr ⟨?_, hxv⟩
  rw [hjS, hRv, dotProduct_comm, hvu, zero_smul, smul_zero, add_zero]

/-- Moving the unit line `ℝu` from `s` (under `R`) to `t` (under `S = R + d uuᵀ`) adds one to the multiplicity of
`t`. -/
lemma redMult_add_line (hst : s ≠ t) (hu : u ⬝ᵥ u = 1) (hxu : x ⬝ᵥ u = 0)
    (hjS : ∀ v, S.jacobi x *ᵥ v = R.jacobi x *ᵥ v + d • ((u ⬝ᵥ v) • u)) (hRu : R.jacobi x *ᵥ u = s • u)
    (hSu : S.jacobi x *ᵥ u = t • u) : S.redMult x t = R.redMult x t + 1 := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have heq : Spectral.Esp S x t = Spectral.Esp R x t ⊔ Submodule.span ℝ {u} := by
    refine le_antisymm (fun v hv => ?_) (sup_le (esp_le hst.symm hjS hRu) ?_)
    · obtain ⟨hSv, hxv⟩ := mem_Esp'.mp hv
      have huw : u ⬝ᵥ (v - (u ⬝ᵥ v) • u) = 0 := by
        rw [dotProduct_sub, dotProduct_smul, hu, smul_eq_mul, mul_one, sub_self]
      have hw : v - (u ⬝ᵥ v) • u ∈ Spectral.Esp R x t := by
        refine mem_Esp'.mpr ⟨?_, ?_⟩
        · have h := hjS (v - (u ⬝ᵥ v) • u)
          rw [huw, zero_smul, smul_zero, add_zero] at h
          rw [← h, Matrix.mulVec_sub, Matrix.mulVec_smul, hSv, hSu]
          module
        · rw [dotProduct_sub, dotProduct_smul, hxv, hxu, smul_zero, sub_zero]
      rw [← sub_add_cancel v ((u ⬝ᵥ v) • u)]
      exact Submodule.add_mem_sup hw (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u))
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact mem_Esp'.mpr ⟨hSu, hxu⟩
  show Module.finrank ℝ (Spectral.Esp S x t) = Module.finrank ℝ (Spectral.Esp R x t) + 1
  rw [heq]
  exact S83.dim_add_one hu0 fun y hy => S83.esp_dot_eig hst.symm hy hRu

/-- For `t` different from both eigenvalues of `u`, the multiplicities of `t` agree. -/
lemma redMult_eq_off {s' : ℝ} (hts : t ≠ s) (hts' : t ≠ s')
    (hjS : ∀ v, S.jacobi x *ᵥ v = R.jacobi x *ᵥ v + d • ((u ⬝ᵥ v) • u)) (hRu : R.jacobi x *ᵥ u = s • u)
    (hSu : S.jacobi x *ᵥ u = s' • u) : S.redMult x t = R.redMult x t := by
  have hjR : ∀ v, R.jacobi x *ᵥ v = S.jacobi x *ᵥ v + (-d) • ((u ⬝ᵥ v) • u) := fun v => by
    rw [hjS]; module
  have heq : Spectral.Esp S x t = Spectral.Esp R x t :=
    le_antisymm (esp_le hts' hjR hSu) (esp_le hts hjS hRu)
  show Module.finrank ℝ (Spectral.Esp S x t) = Module.finrank ℝ (Spectral.Esp R x t)
  rw [heq]

end RankOne

/-- The multiplicities after `J'_x = J_x - (λ₁ - λ₂)uuᵀ`, `u` a unit eigenvector of `λ₁` orthogonal to `x`. -/
lemma move_at {R R' : CurvTensor 16} {x u : Vec 16} {l1 l2 : ℝ} (hne : l1 ≠ l2) (hu : u ⬝ᵥ u = 1)
    (hxu : x ⬝ᵥ u = 0) (hRu : R.jacobi x *ᵥ u = l1 • u)
    (hj' : ∀ v, R'.jacobi x *ᵥ v = R.jacobi x *ᵥ v + (-(l1 - l2)) • ((u ⬝ᵥ v) • u)) :
    R'.redMult x l1 + 1 = R.redMult x l1 ∧ R'.redMult x l2 = R.redMult x l2 + 1 ∧
      ∀ t, t ≠ l1 → t ≠ l2 → R'.redMult x t = R.redMult x t := by
  have hj : ∀ v, R.jacobi x *ᵥ v = R'.jacobi x *ᵥ v + (l1 - l2) • ((u ⬝ᵥ v) • u) := fun v => by
    rw [hj']; module
  have hR'u : R'.jacobi x *ᵥ u = l2 • u := by rw [hj', hRu, hu, one_smul]; module
  exact ⟨(redMult_add_line hne.symm hu hxu hj hR'u hRu).symm, redMult_add_line hne hu hxu hj' hRu hR'u,
    fun t h1 h2 => redMult_eq_off h1 h2 hj' hRu hR'u⟩

/-- A linear eigenfield of `l` gives, at a unit `x`, the eigenvector `Jx` of `l`. -/
lemma eig_at {R : CurvTensor 16} {l : ℝ} {J : Matrix (Fin 16) (Fin 16) ℝ} (hJ : IsEigenfield R l (linP J))
    {x : Vec 16} (hx : x ⬝ᵥ x = 1) : R.jacobi x *ᵥ (J *ᵥ x) = l • (J *ᵥ x) := by
  have h := mem_Esp'.mp (hJ x)
  rw [S8Tools.evalField_linP, hx, mul_one] at h
  exact h.1

/-- Row `s8_move_eigenfield`. -/
theorem s8_move_eigenfield_proved {k : ℕ} (R : CurvTensor 16) (m : Fin k → ℕ) (ev : Fin k → ℝ)
    (hR : PatternEv R m ev) (hsum : ∑ i, m i = 15) (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J)
    (hJo : Jᵀ * J = 1) (i1 i2 : Fin k) (h12 : i1 ≠ i2) (hJ : IsEigenfield R (ev i1) (linP J)) :
    ∃ R' : CurvTensor 16, (∀ u v z, R'.op u v z = R.op u v z - (ev i1 - ev i2) • RJfun J u v z) ∧
      (∀ x, R'.jacobi x = R.jacobi x - (ev i1 - ev i2) • jfam J x) ∧ R'.IsOsserman ∧
      ∀ x : Vec 16, x ⬝ᵥ x = 1 → R'.redMult x (ev i1) = m i1 - 1 ∧ R'.redMult x (ev i2) = m i2 + 1 ∧
        ∀ i, i ≠ i1 → i ≠ i2 → R'.redMult x (ev i) = m i := by
  obtain ⟨-, RJ, hRJop, -⟩ := Rem72a.RJ_curv_proved J hJs
  obtain ⟨R', hR'0⟩ := Rem72a.exists_sub R RJ (ev i1 - ev i2)
  have hR' : ∀ u v z, R'.op u v z = R.op u v z - (ev i1 - ev i2) • RJfun J u v z := fun u v z => by
    rw [hR'0, hRJop]
  have hjac : ∀ x, R'.jacobi x = R.jacobi x - (ev i1 - ev i2) • jfam J x := fun x =>
    eq_sub_of_add_eq (Rem72a.rem_7_2_jac_split_proved R R' J hJs _ hR' x).1.symm
  have hne : ev i1 ≠ ev i2 := fun e => h12 (hR.1 e)
  have hO : R.IsOsserman := (CorD.hasPattern_osserman_proved R m (by omega) ⟨ev, hR⟩).1
  have facts (x : Vec 16) (hx : x ⬝ᵥ x = 1) := move_at (R := R) (R' := R') (u := J *ᵥ x) hne
    (by rw [CayleyIdentify.orthogonal_dot J hJo, hx]) (Rem72a.skew_dot_self hJs x) (eig_at hJ hx) fun v => by
      rw [hjac, Matrix.sub_mulVec, Matrix.smul_mulVec, Rem72a.jfam_mulVec]; module
  refine ⟨R', hR', hjac, fun x y hx hy μ => ?_, fun x hx => ?_⟩
  · obtain ⟨ax, bx, cx⟩ := facts x hx
    obtain ⟨ay, b_y, cy⟩ := facts y hy
    have m1 := (hR.2 x hx i1).trans (hR.2 y hy i1).symm
    have m2 := (hR.2 x hx i2).trans (hR.2 y hy i2).symm
    by_cases h1 : μ = ev i1
    · subst h1; omega
    · by_cases h2 : μ = ev i2
      · subst h2; omega
      · rw [cx μ h1 h2, cy μ h1 h2]; exact hO x y hx hy μ
  · obtain ⟨a, b, c⟩ := facts x hx
    have m1 := hR.2 x hx i1
    refine ⟨by omega, by rw [b, hR.2 x hx i2], fun i hi1 hi2 => ?_⟩
    rw [c _ (fun e => hi1 (hR.1 e)) (fun e => hi2 (hR.1 e)), hR.2 x hx i]

/-! ### The spectral projector identity -/

/-- The fields fill the eigenspaces other than those of `i0, i1`: `r + m i0 + m i1 = ∑ m`. -/
lemma count_fields {k r : ℕ} (m : Fin k → ℕ) (ev : Fin k → ℝ) (hinj : Function.Injective ev) (i0 i1 : Fin k)
    (h01 : i0 ≠ i1) (μ : Fin r → ℝ) (hμ : ∀ j, ∃ i, i ≠ i0 ∧ i ≠ i1 ∧ μ j = ev i)
    (hcount : ∀ i, i ≠ i0 → i ≠ i1 → (Finset.univ.filter fun j => μ j = ev i).card = m i) :
    r + m i0 + m i1 = ∑ i, m i := by
  choose f hf using hμ
  have hmem : ∀ i, i ∈ (Finset.univ.erase i0).erase i1 ↔ i ≠ i0 ∧ i ≠ i1 := fun i => by
    rw [Finset.mem_erase, Finset.mem_erase]
    simp only [Finset.mem_univ, and_true]
    exact and_comm
  have hfib : r = ∑ i ∈ (Finset.univ.erase i0).erase i1, m i := by
    have h := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ)
      (t := (Finset.univ.erase i0).erase i1) fun j _ => (hmem _).mpr ⟨(hf j).1, (hf j).2.1⟩
    rw [Finset.card_univ, Fintype.card_fin] at h
    rw [h]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← hcount i ((hmem i).mp hi).1 ((hmem i).mp hi).2]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun e => by rw [(hf j).2.2, e], fun e => hinj ((hf j).2.2.symm.trans e)⟩
  have hsplit : ∑ i, m i = m i0 + (m i1 + ∑ i ∈ (Finset.univ.erase i0).erase i1, m i) := by
    rw [← Finset.add_sum_erase Finset.univ m (Finset.mem_univ i0),
      ← Finset.add_sum_erase (Finset.univ.erase i0) m (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ i1⟩)]
  omega

section Unit

variable {r : ℕ} {R : CurvTensor 16} {x : Vec 16} {p : Fin r → Vec 16} {μ : Fin r → ℝ}

/-- Orthonormal vectors are linearly independent. -/
lemma orthonormal_li (hp : ∀ j l, p j ⬝ᵥ p l = if j = l then 1 else 0) : LinearIndependent ℝ p := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hd := congrArg (fun v => v ⬝ᵥ p j) hg
  simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct, hp] at hd
  simpa using hd

/-- A reduced eigenfield of `μ`, at a unit `x`. -/
lemma unit_eig {μ₀ : ℝ} {P : Fin 16 → MvPolynomial (Fin 16) ℝ} (hP : IsEigenfield R μ₀ P) (hx : x ⬝ᵥ x = 1) :
    R.jacobi x *ᵥ evalField P x = μ₀ • evalField P x ∧ x ⬝ᵥ evalField P x = 0 := by
  have h := mem_Esp'.mp (hP x)
  rw [hx, mul_one] at h
  exact h

/-- At a unit `x`, orthonormal reduced eigenvectors `p_j` of `μ_j` filling the eigenspaces other than those of `0` and
`λ`: `∑ μ_j(μ_j - λ)p_jp_jᵀ = A(A - λ)`. -/
lemma unit_identity {k : ℕ} (m : Fin k → ℕ) (ev : Fin k → ℝ) (hR : PatternEv R m ev) (hsum : ∑ i, m i = 15)
    (i0 i1 : Fin k) (h01 : i0 ≠ i1) (h0 : ev i0 = 0) (hx : x ⬝ᵥ x = 1)
    (hpe : ∀ j, R.jacobi x *ᵥ p j = μ j • p j ∧ x ⬝ᵥ p j = 0)
    (hpo : ∀ j l, p j ⬝ᵥ p l = if j = l then 1 else 0) (hμ : ∀ j, ∃ i, i ≠ i0 ∧ i ≠ i1 ∧ μ j = ev i)
    (hcount : ∀ i, i ≠ i0 → i ≠ i1 → (Finset.univ.filter fun j => μ j = ev i).card = m i) :
    ∑ j, (μ j * (μ j - ev i1)) • vecMulVec (p j) (p j) = R.jacobi x * (R.jacobi x - ev i1 • 1) := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hμ0 : ∀ j i, (i = i0 ∨ i = i1) → ev i ≠ μ j := by
    rintro j i hi e
    obtain ⟨i', h0', h1', e'⟩ := hμ j
    have hii := hR.1 (e.trans e')
    rcases hi with rfl | rfl
    · exact h0' hii.symm
    · exact h1' hii.symm
  have hpx : ∀ j, p j ⬝ᵥ x = 0 := fun j => by rw [dotProduct_comm]; exact (hpe j).2
  have hpE : ∀ i, (i = i0 ∨ i = i1) → ∀ y ∈ Spectral.Esp R x (ev i), ∀ j, p j ⬝ᵥ y = 0 := fun i hi y hy j => by
    rw [dotProduct_comm]; exact S83.esp_dot_eig (hμ0 j i hi) hy (hpe j).1
  obtain ⟨D, hDdef⟩ : ∃ D, D = ∑ j, (μ j * (μ j - ev i1)) • vecMulVec (p j) (p j) -
      R.jacobi x * (R.jacobi x - ev i1 • 1) := ⟨_, rfl⟩
  have hDv : ∀ v, D *ᵥ v = ∑ j, (μ j * (μ j - ev i1) * (p j ⬝ᵥ v)) • p j -
      (R.jacobi x *ᵥ (R.jacobi x *ᵥ v) - ev i1 • (R.jacobi x *ᵥ v)) := fun v => by
    rw [hDdef, Matrix.sub_mulVec, Matrix.sum_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul]
    simp only [Matrix.smul_mulVec, Spectral.vecMulVec_self_mulVec, smul_smul]
  have kill : ∀ w t, R.jacobi x *ᵥ w = t • w → (∀ j, p j ⬝ᵥ w = 0) → t * (t - ev i1) = 0 → D *ᵥ w = 0 := by
    intro w t hw hp ht
    rw [hDv, hw, Matrix.mulVec_smul, hw]
    simp only [hp, mul_zero, zero_smul, Finset.sum_const_zero, zero_sub, neg_eq_zero]
    rw [show t • t • w - ev i1 • t • w = (t * (t - ev i1)) • w by module, ht, zero_smul]
  -- `D` kills the fields
  have hspan : Submodule.span ℝ (Set.range p) ≤ LinearMap.ker (Matrix.toLin' D) := by
    rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    have hQ : ∑ j, (μ j * (μ j - ev i1) * (p j ⬝ᵥ p l)) • p j = (μ l * (μ l - ev i1)) • p l := by
      rw [Finset.sum_eq_single l]
      · rw [hpo, ite_eq_left rfl, mul_one]
      · intro j _ hj
        rw [hpo, ite_eq_right hj, mul_zero, zero_smul]
      · intro h
        exact absurd (Finset.mem_univ l) h
    rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.toLin'_apply, hDv, hQ, (hpe l).1, Matrix.mulVec_smul, (hpe l).1]
    module
  -- `D` kills `W = E_0 ⊕ E_λ ⊕ ℝx`
  have hW : Spectral.Esp R x (ev i0) ⊔ Spectral.Esp R x (ev i1) ⊔ Submodule.span ℝ {x} ≤
      LinearMap.ker (Matrix.toLin' D) := by
    refine sup_le (sup_le (fun y hy => ?_) (fun y hy => ?_)) ?_
    · rw [LinearMap.mem_ker, Matrix.toLin'_apply]
      exact kill y (ev i0) (mem_Esp'.mp hy).1 (hpE i0 (Or.inl rfl) y hy) (by rw [h0, zero_mul])
    · rw [LinearMap.mem_ker, Matrix.toLin'_apply]
      exact kill y (ev i1) (mem_Esp'.mp hy).1 (hpE i1 (Or.inr rfl) y hy) (by rw [sub_self, mul_zero])
    · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker, Matrix.toLin'_apply]
      exact kill x 0 (by rw [Spectral.jacobi_self, zero_smul]) hpx (by ring)
  -- `W ⊥ p_j`
  have perpW : ∀ v ∈ Spectral.Esp R x (ev i0) ⊔ Spectral.Esp R x (ev i1) ⊔ Submodule.span ℝ {x}, ∀ j,
      p j ⬝ᵥ v = 0 := by
    have hle : Spectral.Esp R x (ev i0) ⊔ Spectral.Esp R x (ev i1) ⊔ Submodule.span ℝ {x} ≤
        ⨅ j, LinearMap.ker (Spectral.dotL (p j)) := by
      refine sup_le (sup_le (fun y hy => ?_) (fun y hy => ?_)) ?_
      · exact (Submodule.mem_iInf _).mpr fun j => LinearMap.mem_ker.mpr (hpE i0 (Or.inl rfl) y hy j)
      · exact (Submodule.mem_iInf _).mpr fun j => LinearMap.mem_ker.mpr (hpE i1 (Or.inr rfl) y hy j)
      · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
        exact (Submodule.mem_iInf _).mpr fun j => LinearMap.mem_ker.mpr (hpx j)
    intro v hv j
    exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp (hle hv) j)
  -- dimensions: `span p ⊕ W = ℝ^16`
  have hfr_p : Module.finrank ℝ (Submodule.span ℝ (Set.range p)) = r := by
    rw [finrank_span_eq_card (orthonormal_li hpo), Fintype.card_fin]
  have hfr_E : Module.finrank ℝ ↥(Spectral.Esp R x (ev i0) ⊔ Spectral.Esp R x (ev i1)) = m i0 + m i1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Spectral.Esp R x (ev i0)) (Spectral.Esp R x (ev i1))
    rw [Spectral.Esp_inf R x (fun e => h01 (hR.1 e)), finrank_bot, add_zero] at h
    rw [h]
    exact congrArg₂ (· + ·) (hR.2 x hx i0) (hR.2 x hx i1)
  have horth : ∀ y ∈ Spectral.Esp R x (ev i0) ⊔ Spectral.Esp R x (ev i1), y ⬝ᵥ x = 0 := fun y hy => by
    rw [dotProduct_comm]
    exact (sup_le inf_le_right inf_le_right : Spectral.Esp R x (ev i0) ⊔ Spectral.Esp R x (ev i1) ≤ perp x) hy
  have hfr_W : Module.finrank ℝ ↥(Spectral.Esp R x (ev i0) ⊔ Spectral.Esp R x (ev i1) ⊔ Submodule.span ℝ {x}) =
      m i0 + m i1 + 1 := by
    rw [S83.dim_add_one hx0 horth, hfr_E]
  have hinf : Submodule.span ℝ (Set.range p) ⊓
      (Spectral.Esp R x (ev i0) ⊔ Spectral.Esp R x (ev i1) ⊔ Submodule.span ℝ {x}) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvp, hvW⟩ := Submodule.mem_inf.mp hv
    have hperp := perpW v hvW
    have hle : Submodule.span ℝ (Set.range p) ≤ LinearMap.ker (Spectral.dotL v) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      show v ⬝ᵥ p j = 0
      rw [dotProduct_comm]
      exact hperp j
    have hself : v ⬝ᵥ v = 0 := LinearMap.mem_ker.mp (hle hvp)
    rw [Submodule.mem_bot]
    exact dotProduct_self_eq_zero.mp hself
  have htop : Submodule.span ℝ (Set.range p) ⊔
      (Spectral.Esp R x (ev i0) ⊔ Spectral.Esp R x (ev i1) ⊔ Submodule.span ℝ {x}) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span ℝ (Set.range p))
      (Spectral.Esp R x (ev i0) ⊔ Spectral.Esp R x (ev i1) ⊔ Submodule.span ℝ {x})
    rw [hinf, finrank_bot, add_zero, hfr_p, hfr_W] at h
    rw [h, Module.finrank_fin_fun]
    have hc := count_fields m ev hR.1 i0 i1 h01 μ hμ hcount
    omega
  have hker : (⊤ : Submodule ℝ (Vec 16)) ≤ LinearMap.ker (Matrix.toLin' D) := by
    rw [← htop]
    exact sup_le hspan hW
  have hall : ∀ v, D *ᵥ v = 0 := fun v => by
    have h := hker (Submodule.mem_top (x := v))
    rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at h
  rw [← sub_eq_zero, ← hDdef]
  exact Matrix.ext_iff_mulVec.mpr fun v => by rw [hall v, Matrix.zero_mulVec]

end Unit

/-- Row `s8_spectral_identity`. -/
theorem s8_spectral_identity_proved {k r : ℕ} (R : CurvTensor 16) (m : Fin k → ℕ) (ev : Fin k → ℝ)
    (hR : PatternEv R m ev) (hsum : ∑ i, m i = 15) (i0 i1 : Fin k) (h01 : i0 ≠ i1) (h0 : ev i0 = 0)
    (P : Fin r → Fin 16 → MvPolynomial (Fin 16) ℝ) (μ : Fin r → ℝ) (hP3 : ∀ j a, (P j a).IsHomogeneous 3)
    (hPe : ∀ j, IsEigenfield R (μ j) (P j))
    (hPo : ∀ (x : Vec 16) j l, evalField (P j) x ⬝ᵥ evalField (P l) x = if j = l then (x ⬝ᵥ x) ^ 3 else 0)
    (hμ : ∀ j, ∃ i, i ≠ i0 ∧ i ≠ i1 ∧ μ j = ev i)
    (hcount : ∀ i, i ≠ i0 → i ≠ i1 → (Finset.univ.filter fun j => μ j = ev i).card = m i) :
    ∀ x : Vec 16, ∑ j, (μ j * (μ j - ev i1)) • vecMulVec (evalField (P j) x) (evalField (P j) x) =
      (x ⬝ᵥ x) • (R.jacobi x * (R.jacobi x - (ev i1 * (x ⬝ᵥ x)) • (1 : Matrix (Fin 16) (Fin 16) ℝ))) := by
  intro x
  obtain ⟨s, u, hu, rfl⟩ := Spectral.exists_unit_scale x
  have hunit := unit_identity (p := fun j => evalField (P j) u) (μ := μ) m ev hR hsum i0 i1 h01 h0 hu
    (fun j => unit_eig (hPe j) hu) (fun j l => by simp only [hPo, hu, one_pow]) hμ hcount
  have hev : ∀ j, evalField (P j) (s • u) = s ^ 3 • evalField (P j) u := fun j =>
    S8Tools.evalField_smul (hP3 j) s u
  have hq : (s • u) ⬝ᵥ (s • u) = s * s := by
    rw [smul_dotProduct, dotProduct_smul, hu, smul_eq_mul, smul_eq_mul, mul_one]
  have hrhs : (s * s) • ((s * s) • R.jacobi u * ((s * s) • R.jacobi u -
      (ev i1 * (s * s)) • (1 : Matrix (Fin 16) (Fin 16) ℝ))) =
      (s ^ 3 * s ^ 3) • (R.jacobi u * (R.jacobi u - ev i1 • 1)) := by
    rw [show (s * s) • R.jacobi u - (ev i1 * (s * s)) • (1 : Matrix (Fin 16) (Fin 16) ℝ) =
      (s * s) • (R.jacobi u - ev i1 • 1) by module, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
    congr 1
    ring
  simp only [hev, smul_vecMulVec, vecMulVec_smul, smul_smul]
  rw [hq, Spectral.jacobi_smul, hrhs, ← hunit, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]
  congr 1
  ring

end Osserman.Proofs.S8Gen
