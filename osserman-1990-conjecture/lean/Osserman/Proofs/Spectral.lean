/-
Osserman/Proofs/Spectral.lean — proofs of five statements of paper 013 (§1 l. 278-279, §2 l. 335-374, the spectral normalization of
the Jacobi family): sec2_names, sec2_A_properties, thm_C_hyp_osserman, sec1_const_curv_one_eigenvalue,
sec2_Q_properties.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.Curv
import Osserman.Defs.TwoRoot

namespace Osserman.Proofs.Spectral

open Osserman Matrix

variable {n : ℕ}

/-! ### Curvature identities: pair symmetry, `J_x` symmetric, `J_x x = 0`, `J_{tx} = t²J_x` -/

section Curvature

variable (R : CurvTensor n)

lemma op_dot_anti1 (u v w z : Vec n) : R.op u v w ⬝ᵥ z = -(R.op v u w ⬝ᵥ z) := by
  rw [R.antisymm u v w, neg_dotProduct]

lemma op_dot_anti2 (u v w z : Vec n) : R.op u v w ⬝ᵥ z = -(R.op u v z ⬝ᵥ w) := R.skew u v w z

lemma op_dot_bianchi (u v w z : Vec n) :
    R.op u v w ⬝ᵥ z + R.op v w u ⬝ᵥ z + R.op w u v ⬝ᵥ z = 0 := by
  rw [← add_dotProduct, ← add_dotProduct, R.bianchi, zero_dotProduct]

/-- Pair symmetry `⟨R(u,v)w,z⟩ = ⟨R(w,z)u,v⟩` (four Bianchi identities). -/
lemma op_dot_pair (u v w z : Vec n) : R.op u v w ⬝ᵥ z = R.op w z u ⬝ᵥ v := by
  have b1 := op_dot_bianchi R w u v z
  have b2 := op_dot_bianchi R u v z w
  have b3 := op_dot_bianchi R v z w u
  have b4 := op_dot_bianchi R z w u v
  have a1 := op_dot_anti2 R u v z w
  have a2 := op_dot_anti2 R v z u w
  have a3 := op_dot_anti1 R w v z u
  have a4 := op_dot_anti2 R v w z u
  have a5 := op_dot_anti2 R z w u v
  have a6 := op_dot_anti2 R w u z v
  have a7 := op_dot_anti1 R u z w v
  have a8 := op_dot_anti2 R z u w v
  have a9 := op_dot_anti1 R w z u v
  linarith

lemma jacobiMap_apply (x y : Vec n) : R.jacobiMap x y = R.op y x x := rfl

/-- `⟨J_x y, z⟩ = ⟨J_x z, y⟩`. -/
lemma jacobi_dot (x y z : Vec n) : R.op y x x ⬝ᵥ z = R.op z x x ⬝ᵥ y := by
  have h1 := op_dot_pair R y x x z
  have h2 := op_dot_anti2 R x z y x
  have h3 := op_dot_anti1 R x z x y
  linarith

/-- A matrix that moves across the dot product is symmetric. -/
lemma transpose_of_dot {M : Matrix (Fin n) (Fin n) ℝ} (h : ∀ y z, (M *ᵥ y) ⬝ᵥ z = (M *ᵥ z) ⬝ᵥ y) : Mᵀ = M := by
  ext i j
  have hij := h (Pi.single i 1) (Pi.single j 1)
  rw [mulVec_single_one, mulVec_single_one, dotProduct_single_one, dotProduct_single_one] at hij
  simpa [col_apply] using hij

lemma jacobi_transpose (x : Vec n) : (R.jacobi x)ᵀ = R.jacobi x :=
  transpose_of_dot fun y z => by simp only [Curv.jacobi_mulVec]; exact jacobi_dot R x y z

lemma op_self (x : Vec n) : R.op x x x = 0 := by
  ext i
  have h := congrFun (R.antisymm x x x) i
  simp only [Pi.neg_apply, Pi.zero_apply] at h ⊢
  linarith

lemma jacobi_self (x : Vec n) : R.jacobi x *ᵥ x = 0 := by
  rw [Curv.jacobi_mulVec, op_self]

lemma jacobi_smul (t : ℝ) (x : Vec n) : R.jacobi (t • x) = (t * t) • R.jacobi x := by
  rw [ext_iff_mulVec]
  intro y
  simp only [smul_mulVec, Curv.jacobi_mulVec, map_smul, LinearMap.smul_apply, smul_smul]

/-- The Jacobi family of any curvature tensor is quadratic. -/
lemma quad_jacobi : IsQuadFamily R.jacobi := by
  refine ⟨fun a b => LinearMap.toMatrix' ((R.op.flip (Pi.single b 1)).flip (Pi.single a 1)), fun x => ?_⟩
  rw [ext_iff_mulVec]
  intro y
  rw [Curv.jacobi_mulVec]
  conv_lhs => rw [pi_eq_sum_univ' x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
    smul_smul, Matrix.sum_mulVec, smul_mulVec, LinearMap.toMatrix'_mulVec, LinearMap.flip_apply]

end Curvature

/-! ### `Π(x)` -/

lemma Pi_mulVec (x y : Vec n) : Pi x *ᵥ y = (x ⬝ᵥ x) • y - (y ⬝ᵥ x) • x :=
  (Curv.sec1_jacobi_R1_proved n x y).symm

lemma Pi_transpose (x : Vec n) : (Pi x)ᵀ = Pi x := by
  simp only [Osserman.Pi, transpose_sub, transpose_smul, transpose_one, transpose_vecMulVec]

lemma Pi_self (x : Vec n) : Pi x *ᵥ x = 0 := by
  rw [Pi_mulVec, sub_self]

lemma Pi_smul (t : ℝ) (x : Vec n) : Pi (t • x) = (t * t) • Pi x := by
  rw [ext_iff_mulVec]
  intro y
  rw [smul_mulVec, Pi_mulVec, Pi_mulVec]
  simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul]
  module

lemma quad_Pi : IsQuadFamily (Osserman.Pi : Vec n → Matrix (Fin n) (Fin n) ℝ) := by
  obtain ⟨R1, hR1⟩ := Curv.sec1_R1_curv_proved n
  obtain ⟨M, hM⟩ := quad_jacobi R1
  refine ⟨M, fun x => ?_⟩
  rw [← hM x, ext_iff_mulVec]
  intro y
  rw [Curv.jacobi_mulVec, hR1, Curv.sec1_jacobi_R1_proved]

/-! ### Orthogonal complements -/

lemma mem_perp {x y : Vec n} : y ∈ perp x ↔ x ⬝ᵥ y = 0 := Iff.rfl

/-- The functional `y ↦ ⟨x, y⟩`. -/
def dotL (x : Vec n) : Vec n →ₗ[ℝ] ℝ where
  toFun y := x ⬝ᵥ y
  map_add' := dotProduct_add x
  map_smul' c y := by simp [dotProduct_smul]

lemma perp_eq_ker (x : Vec n) : perp x = LinearMap.ker (dotL x) := by
  ext y
  rw [mem_perp, LinearMap.mem_ker]
  rfl

lemma finrank_perp {x : Vec n} (hx : x ⬝ᵥ x = 1) : Module.finrank ℝ (perp x) + 1 = n := by
  have h := LinearMap.finrank_range_add_finrank_ker (dotL x)
  have hr : LinearMap.range (dotL x) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro r
    exact ⟨r • x, by simp [dotL, hx]⟩
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun, ← perp_eq_ker] at h
  omega

/-! ### Reduced eigenspaces and the decomposition `ℝ^16 = ℝx ⊕ E_μ ⊕ E_{μ+κ}` -/

/-- The reduced eigenspace `E_μ(x) = ker(J_x - μ) ∩ x^⊥`; `redMult R x μ` is its dimension. -/
abbrev Esp (R : CurvTensor n) (x : Vec n) (μ : ℝ) : Submodule ℝ (Vec n) :=
  Module.End.eigenspace (R.jacobiMap x) μ ⊓ perp x

lemma mem_Esp {R : CurvTensor n} {x v : Vec n} {μ : ℝ} : v ∈ Esp R x μ ↔ R.op v x x = μ • v ∧ x ⬝ᵥ v = 0 := by
  rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff, mem_perp, jacobiMap_apply]

lemma Esp_inf (R : CurvTensor n) (x : Vec n) {μ₁ μ₂ : ℝ} (hne : μ₁ ≠ μ₂) : Esp R x μ₁ ⊓ Esp R x μ₂ = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf, mem_Esp, mem_Esp] at hv
  rw [Submodule.mem_bot]
  have h : (μ₁ - μ₂) • v = 0 := by rw [sub_smul, ← hv.1.1, ← hv.2.1, sub_self]
  exact (smul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)

/-- At a unit `x` with reduced multiplicities 8 and 7 for `μ₁ ≠ μ₂`: `y = ⟨x,y⟩x + e₁ + e₂`, `eᵢ ∈ E_{μᵢ}(x)`. -/
lemma decomp (R : CurvTensor 16) {μ₁ μ₂ : ℝ} (hne : μ₁ ≠ μ₂) {x : Vec 16} (hx : x ⬝ᵥ x = 1)
    (h1 : R.redMult x μ₁ = 8) (h2 : R.redMult x μ₂ = 7) (y : Vec 16) :
    ∃ e1 ∈ Esp R x μ₁, ∃ e2 ∈ Esp R x μ₂, y = (x ⬝ᵥ y) • x + e1 + e2 := by
  have hsup : Esp R x μ₁ ⊔ Esp R x μ₂ = perp x := by
    apply Submodule.eq_of_le_of_finrank_eq (sup_le inf_le_right inf_le_right)
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Esp R x μ₁) (Esp R x μ₂)
    rw [Esp_inf R x hne, finrank_bot] at h
    have hp := finrank_perp hx
    have h1' : Module.finrank ℝ (Esp R x μ₁) = 8 := h1
    have h2' : Module.finrank ℝ (Esp R x μ₂) = 7 := h2
    omega
  have hmem : y - (x ⬝ᵥ y) • x ∈ perp x := by
    rw [mem_perp, dotProduct_sub, dotProduct_smul, hx, smul_eq_mul, mul_one, sub_self]
  rw [← hsup, Submodule.mem_sup] at hmem
  obtain ⟨e1, he1, e2, he2, he⟩ := hmem
  exact ⟨e1, he1, e2, he2, by rw [add_assoc, he]; abel⟩

/-! ### `A(x) = κ⁻¹(J_x - μΠ(x))` -/

section Amat

variable (R : CurvTensor 16) (μ κ : ℝ)

lemma Amat_mulVec (x y : Vec 16) :
    Amat R μ κ x *ᵥ y = κ⁻¹ • (R.op y x x - μ • ((x ⬝ᵥ x) • y - (y ⬝ᵥ x) • x)) := by
  simp only [Amat, smul_mulVec, sub_mulVec, Curv.jacobi_mulVec, Pi_mulVec]

lemma Amat_self (x : Vec 16) : Amat R μ κ x *ᵥ x = 0 := by
  simp only [Amat, smul_mulVec, sub_mulVec, jacobi_self, Pi_self, smul_zero, sub_zero]

lemma Amat_transpose (x : Vec 16) : (Amat R μ κ x)ᵀ = Amat R μ κ x := by
  simp only [Amat, transpose_smul, transpose_sub, jacobi_transpose, Pi_transpose]

lemma Amat_smul (t : ℝ) (x : Vec 16) : Amat R μ κ (t • x) = (t * t) • Amat R μ κ x := by
  simp only [Amat, jacobi_smul, Pi_smul]
  module

lemma quad_Amat : IsQuadFamily (Amat R μ κ) := by
  obtain ⟨M, hM⟩ := quad_jacobi R
  obtain ⟨N, hN⟩ := (quad_Pi (n := 16))
  refine ⟨fun a b => κ⁻¹ • (M a b - μ • N a b), fun x => ?_⟩
  rw [Amat, hM x, hN x]
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  module

/-- `A(x)` on a reduced eigenvector `e ∈ E_ν(x)` of a unit `x`: `A(x)e = κ⁻¹(ν - μ)e`. -/
lemma Amat_eig {x e : Vec 16} {ν : ℝ} (hx : x ⬝ᵥ x = 1) (he : e ∈ Esp R x ν) :
    Amat R μ κ x *ᵥ e = (κ⁻¹ * (ν - μ)) • e := by
  rw [mem_Esp] at he
  rw [Amat_mulVec, he.1, hx, dotProduct_comm, he.2]
  module

/-- Under the two-root hypothesis, at a unit `x`: `A(x)` maps into `E_{μ+κ}(x)` and fixes it. -/
lemma Amat_unit (h : TwoRootHyp R μ κ) {x : Vec 16} (hx : x ⬝ᵥ x = 1) :
    (∀ y, Amat R μ κ x *ᵥ y ∈ Esp R x (μ + κ)) ∧ ∀ e ∈ Esp R x (μ + κ), Amat R μ κ x *ᵥ e = e := by
  have hfix : ∀ e ∈ Esp R x (μ + κ), Amat R μ κ x *ᵥ e = e := fun e he => by
    have hk : μ + κ - μ = κ := by ring
    rw [Amat_eig R μ κ hx he, hk, inv_mul_cancel₀ h.1, one_smul]
  refine ⟨fun y => ?_, hfix⟩
  have hne : μ ≠ μ + κ := fun e => h.1 (by linarith)
  obtain ⟨e1, he1, e2, he2, hy⟩ := decomp R hne hx (h.2 x hx).1 (h.2 x hx).2 y
  rw [hy, mulVec_add, mulVec_add, mulVec_smul, Amat_self, Amat_eig R μ κ hx he1, hfix e2 he2, sub_self, mul_zero,
    zero_smul, smul_zero, zero_add, zero_add]
  exact he2

lemma Amat_unit_sq (h : TwoRootHyp R μ κ) {x : Vec 16} (hx : x ⬝ᵥ x = 1) :
    Amat R μ κ x * Amat R μ κ x = Amat R μ κ x := by
  rw [ext_iff_mulVec]
  intro y
  rw [← mulVec_mulVec]
  exact (Amat_unit R μ κ h hx).2 _ ((Amat_unit R μ κ h hx).1 y)

lemma Amat_unit_trace (h : TwoRootHyp R μ κ) {x : Vec 16} (hx : x ⬝ᵥ x = 1) : (Amat R μ κ x).trace = 7 := by
  have hP : LinearMap.IsProj (Esp R x (μ + κ)) (Matrix.toLin' (Amat R μ κ x)) :=
    ⟨fun y => by rw [Matrix.toLin'_apply]; exact (Amat_unit R μ κ h hx).1 y,
      fun e he => by rw [Matrix.toLin'_apply]; exact (Amat_unit R μ κ h hx).2 e he⟩
  have htr := hP.trace
  rw [Matrix.trace_toLin'_eq] at htr
  rw [htr]
  have h7 : Module.finrank ℝ (Esp R x (μ + κ)) = 7 := (h.2 x hx).2
  rw [h7]
  norm_num

end Amat

/-- Every vector is `s • u` with `u` a unit vector. -/
lemma exists_unit_scale (x : Vec 16) : ∃ (s : ℝ) (u : Vec 16), u ⬝ᵥ u = 1 ∧ x = s • u := by
  by_cases hx0 : x = 0
  · exact ⟨0, Pi.single 0 1, by simp, by simp [hx0]⟩
  have hnn : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  have hpos : 0 < x ⬝ᵥ x := lt_of_le_of_ne hnn (Ne.symm (mt dotProduct_self_eq_zero.mp hx0))
  have hs : Real.sqrt (x ⬝ᵥ x) * Real.sqrt (x ⬝ᵥ x) = x ⬝ᵥ x := Real.mul_self_sqrt hnn
  have hs0 : Real.sqrt (x ⬝ᵥ x) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  refine ⟨Real.sqrt (x ⬝ᵥ x), (Real.sqrt (x ⬝ᵥ x))⁻¹ • x, ?_, ?_⟩
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_inv, hs,
      inv_mul_cancel₀ hpos.ne']
  · rw [smul_smul, mul_inv_cancel₀ hs0, one_smul]

/-! ### The five statements -/

theorem sec2_names_proved (R : CurvTensor 16)
    (h2 : ∃ μ₁ μ₂ : ℝ, μ₁ ≠ μ₂ ∧ ∀ x : Vec 16, x ⬝ᵥ x = 1 → R.redMult x μ₁ = 8 ∧ R.redMult x μ₂ = 7) :
    ∃ μ κ : ℝ, TwoRootHyp R μ κ := by
  obtain ⟨μ₁, μ₂, hne, h⟩ := h2
  have hsum : μ₁ + (μ₂ - μ₁) = μ₂ := by ring
  exact ⟨μ₁, μ₂ - μ₁, sub_ne_zero.mpr (Ne.symm hne), fun x hx => by rw [hsum]; exact h x hx⟩

theorem sec2_A_properties_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) :
    IsQuadFamily (Amat R μ κ) ∧ (∀ x, (Amat R μ κ x)ᵀ = Amat R μ κ x) ∧
      ∀ x, Amat R μ κ x *ᵥ x = 0 ∧ Amat R μ κ x * Amat R μ κ x = (x ⬝ᵥ x) • Amat R μ κ x ∧
        (Amat R μ κ x).trace = 7 * (x ⬝ᵥ x) := by
  refine ⟨quad_Amat R μ κ, Amat_transpose R μ κ, fun x => ⟨Amat_self R μ κ x, ?_⟩⟩
  obtain ⟨s, u, hu, rfl⟩ := exists_unit_scale x
  have hxx : (s • u) ⬝ᵥ (s • u) = s * s := by
    rw [smul_dotProduct, dotProduct_smul, hu, smul_eq_mul, smul_eq_mul, mul_one]
  rw [Amat_smul, hxx]
  refine ⟨?_, ?_⟩
  · rw [smul_mul_assoc, mul_smul_comm, Amat_unit_sq R μ κ h hu]
  · rw [trace_smul, Amat_unit_trace R μ κ h hu, smul_eq_mul]
    ring

theorem thm_C_hyp_osserman_proved (R : CurvTensor 16) (μ₁ μ₂ : ℝ) (hne : μ₁ ≠ μ₂)
    (h : ∀ x : Vec 16, x ⬝ᵥ x = 1 → R.redMult x μ₁ = 8 ∧ R.redMult x μ₂ = 7) :
    R.IsOsserman ∧ ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ μ, μ ≠ μ₁ → μ ≠ μ₂ → R.redMult x μ = 0 := by
  have hzero : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ μ, μ ≠ μ₁ → μ ≠ μ₂ → R.redMult x μ = 0 := by
    intro x hx μ hμ1 hμ2
    rw [CurvTensor.redMult, Submodule.finrank_eq_zero, eq_bot_iff]
    intro v hv0
    have hv := mem_Esp.1 hv0
    obtain ⟨e1, he1, e2, he2, hdec⟩ := decomp R hne hx (h x hx).1 (h x hx).2 v
    rw [hv.2, zero_smul, zero_add] at hdec
    have hJ : R.op v x x = R.op e1 x x + R.op e2 x x := by
      rw [hdec, map_add, LinearMap.add_apply, LinearMap.add_apply]
    rw [hv.1, (mem_Esp.1 he1).1, (mem_Esp.1 he2).1, hdec] at hJ
    have key : (μ - μ₁) • e1 = (μ₂ - μ) • e2 := by
      calc (μ - μ₁) • e1 = (μ - μ₁) • e1 - (μ • (e1 + e2) - (μ₁ • e1 + μ₂ • e2)) := by rw [hJ, sub_self, sub_zero]
        _ = (μ₂ - μ) • e2 := by module
    have hm : (μ - μ₁) • e1 ∈ Esp R x μ₁ ⊓ Esp R x μ₂ :=
      Submodule.mem_inf.2 ⟨Submodule.smul_mem _ _ he1, key ▸ Submodule.smul_mem _ _ he2⟩
    rw [Esp_inf R x hne, Submodule.mem_bot, key] at hm
    have hz1 : e1 = 0 := by
      have hm' : (μ - μ₁) • e1 = 0 := by rw [key, hm]
      exact (smul_eq_zero.mp hm').resolve_left (sub_ne_zero.mpr hμ1)
    have hz2 : e2 = 0 := (smul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr (Ne.symm hμ2))
    rw [Submodule.mem_bot, hdec, hz1, hz2, add_zero]
  refine ⟨fun x y hx hy μ => ?_, hzero⟩
  by_cases hμ1 : μ = μ₁
  · rw [hμ1, (h x hx).1, (h y hy).1]
  by_cases hμ2 : μ = μ₂
  · rw [hμ2, (h x hx).2, (h y hy).2]
  rw [hzero x hx μ hμ1 hμ2, hzero y hy μ hμ1 hμ2]

theorem sec1_const_curv_one_eigenvalue_proved (c : ℝ) (R : CurvTensor 16)
    (hR : ∀ u v w, R.op u v w = c • R1fun u v w) :
    ∀ x : Vec 16, x ⬝ᵥ x = 1 → R.redMult x c = 15 := by
  intro x hx
  have hE : Esp R x c = perp x := by
    refine le_antisymm inf_le_right fun y hy => mem_Esp.2 ⟨?_, hy⟩
    rw [hR, R1fun, hx, dotProduct_comm, mem_perp.1 hy, one_smul, zero_smul, sub_zero]
  have hp := finrank_perp hx
  show Module.finrank ℝ (Esp R x c) = 15
  rw [hE]
  omega

/-! ### `Q(x) = A(x) + xxᵀ` -/

section Qmat

variable (R : CurvTensor 16) (μ κ : ℝ)

lemma vecMulVec_self_mulVec (x y : Vec 16) : vecMulVec x x *ᵥ y = (x ⬝ᵥ y) • x := by
  rw [vecMulVec_mulVec, op_smul_eq_smul]

lemma Qmat_mulVec (x y : Vec 16) : Qmat R μ κ x *ᵥ y = Amat R μ κ x *ᵥ y + (x ⬝ᵥ y) • x := by
  rw [Qmat, add_mulVec, vecMulVec_self_mulVec]

lemma dot_Amat (x y : Vec 16) : x ⬝ᵥ (Amat R μ κ x *ᵥ y) = 0 := by
  rw [dotProduct_comm, Curv.symm_dot (Amat_transpose R μ κ x), Amat_self, zero_dotProduct]

lemma Qmat_props (h : TwoRootHyp R μ κ) (x : Vec 16) :
    Qmat R μ κ x * Qmat R μ κ x = (x ⬝ᵥ x) • Qmat R μ κ x ∧ Qmat R μ κ x *ᵥ x = (x ⬝ᵥ x) • x ∧
      (Qmat R μ κ x).trace = 8 * (x ⬝ᵥ x) := by
  obtain ⟨-, -, hA⟩ := sec2_A_properties_proved R μ κ h
  obtain ⟨hk, hsq, htr⟩ := hA x
  refine ⟨?_, ?_, ?_⟩
  · rw [ext_iff_mulVec]
    intro y
    have hAA : Amat R μ κ x *ᵥ (Amat R μ κ x *ᵥ y) = (x ⬝ᵥ x) • (Amat R μ κ x *ᵥ y) := by
      rw [mulVec_mulVec, hsq, smul_mulVec]
    rw [← mulVec_mulVec, smul_mulVec, Qmat_mulVec, Qmat_mulVec, mulVec_add, hAA, mulVec_smul, hk, dotProduct_add,
      dot_Amat, dotProduct_smul, smul_eq_mul]
    module
  · rw [Qmat_mulVec, hk, zero_add]
  · rw [Qmat, trace_add, htr, trace_vecMulVec]
    ring

end Qmat

theorem sec2_Q_properties_proved (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) :
    (∀ x, Qmat R μ κ x * Qmat R μ κ x = (x ⬝ᵥ x) • Qmat R μ κ x ∧ Qmat R μ κ x *ᵥ x = (x ⬝ᵥ x) • x ∧
        (Qmat R μ κ x).trace = 8 * (x ⬝ᵥ x)) ∧
      ∀ x, x ≠ 0 → Module.finrank ℝ ↥(Lsub R μ κ x) = 8 ∧
        ∃ Pr : Matrix (Fin 16) (Fin 16) ℝ, Prᵀ = Pr ∧ Pr * Pr = Pr ∧
          LinearMap.range (Matrix.toLin' Pr) = Lsub R μ κ x ∧ Qmat R μ κ x = (x ⬝ᵥ x) • Pr := by
  refine ⟨Qmat_props R μ κ h, fun x hx0 => ?_⟩
  obtain ⟨hQQ, hQx, hQtr⟩ := Qmat_props R μ κ h x
  obtain ⟨-, -, hA⟩ := sec2_A_properties_proved R μ κ h
  obtain ⟨hk, hsq, -⟩ := hA x
  have hxx : x ⬝ᵥ x ≠ 0 := mt dotProduct_self_eq_zero.mp hx0
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (x ⬝ᵥ x)⁻¹ := ⟨_, rfl⟩
  have hcx : c * (x ⬝ᵥ x) = 1 := by rw [hc, inv_mul_cancel₀ hxx]
  have hxc : (x ⬝ᵥ x) * c = 1 := by rw [mul_comm, hcx]
  obtain ⟨Pr, hPr⟩ : ∃ P : Matrix (Fin 16) (Fin 16) ℝ, P = c • Qmat R μ κ x := ⟨_, rfl⟩
  have hPP : Pr * Pr = Pr := by
    rw [hPr, smul_mul_assoc, mul_smul_comm, hQQ, smul_smul, smul_smul, mul_assoc, hcx, mul_one]
  have hPrx : Pr *ᵥ x = x := by
    rw [hPr, smul_mulVec, hQx, smul_smul, hcx, one_smul]
  have hPrA : ∀ y, Pr *ᵥ (Amat R μ κ x *ᵥ y) = Amat R μ κ x *ᵥ y := fun y => by
    rw [hPr, smul_mulVec, Qmat_mulVec, mulVec_mulVec, hsq, smul_mulVec, dot_Amat, zero_smul, add_zero, smul_smul,
      hcx, one_smul]
  have hrange : LinearMap.range (Matrix.toLin' Pr) = Lsub R μ κ x := by
    unfold Lsub
    apply le_antisymm
    · intro v hv
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hv
      have hy : Matrix.toLin' Pr y = Matrix.toLin' (Amat R μ κ x) (c • y) + (c * (x ⬝ᵥ y)) • x := by
        rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hPr, smul_mulVec, Qmat_mulVec, mulVec_smul]
        module
      rw [hy]
      exact add_mem (Submodule.mem_sup_right (LinearMap.mem_range_self _ _))
        (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)))
    · apply sup_le
      · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
        exact LinearMap.mem_range.2 ⟨x, by rw [Matrix.toLin'_apply, hPrx]⟩
      · intro v hv
        obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hv
        exact LinearMap.mem_range.2 ⟨Amat R μ κ x *ᵥ y, by rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hPrA]⟩
  have hP : LinearMap.IsProj (LinearMap.range (Matrix.toLin' Pr)) (Matrix.toLin' Pr) :=
    ⟨fun y => LinearMap.mem_range_self _ y, fun v hv => by
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hv
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, mulVec_mulVec, hPP]⟩
  have htr := hP.trace
  rw [Matrix.trace_toLin'_eq, hrange, hPr, trace_smul, hQtr, smul_eq_mul, mul_left_comm, hcx, mul_one] at htr
  refine ⟨by exact_mod_cast htr.symm, Pr, ?_, hPP, hrange, ?_⟩
  · rw [hPr, transpose_smul, Qmat, transpose_add, Amat_transpose, transpose_vecMulVec]
  · rw [hPr, smul_smul, hxc, one_smul]

end Osserman.Proofs.Spectral
