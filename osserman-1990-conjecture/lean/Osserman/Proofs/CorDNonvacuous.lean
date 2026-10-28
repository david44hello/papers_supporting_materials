/-
Osserman/Proofs/CorDNonvacuous.lean — the two Lean-only non-vacuity rows of Corollary D / Theorem E (paper 013):
`cor_D_hyp_nonvacuous` (R_Cay is Osserman and Jacobi-proportional) and `thm_E_hyp_nonvacuous` (the pattern (7,7,1)).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.CayleyJacobi
import Osserman.Proofs.CayleyCurvature
import Osserman.Proofs.Spectral
import Osserman.Defs.ThreeRoot

namespace Osserman.Proofs.CorDNonvacuous

open Osserman Matrix Osserman.Proofs.Threshold Osserman.Proofs.StdSystem Osserman.Proofs.CayleyEigenspaces
  Osserman.Proofs.CayleyJacobi Osserman.Proofs.CayleyCurvature

lemma dot_pos {x : Vec 16} (hx : x ≠ 0) : 0 < x ⬝ᵥ x :=
  lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (x i))
    (fun e => hx (dotProduct_self_eq_zero.mp e.symm))

lemma sym_dot {S : Matrix (Fin 16) (Fin 16) ℝ} (hST : Sᵀ = S) (a b : Vec 16) : a ⬝ᵥ (S *ᵥ b) = (S *ᵥ a) ⬝ᵥ b := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hST]

/-- For `x ≠ 0`: `A(x) = (|x|²/2)(1 + S_w) - xxᵀ` with `S_w` a symmetric involution fixing `x` (`sec6_Sw`). -/
lemma acay_split (x : Vec 16) (hx : x ≠ 0) : ∃ S : Matrix (Fin 16) (Fin 16) ℝ, S *ᵥ x = x ∧ S * S = 1 ∧ Sᵀ = S ∧
    Acay stdSys x = ((x ⬝ᵥ x) / 2) • (1 + S) - vecMulVec x x := by
  obtain ⟨hA, hSx, hSS, hST, -, -, -, -, -, -, hQ⟩ := sec6_Sw_proved stdSys sec6_std_system_proved.2 x hx
  exact ⟨_, hSx, hSS, hST, by rw [hA, hQ]⟩

/-- `J_x v = (5q/2) v + (3q/2) S_w v - 4⟨x,v⟩x` for `R_Cay`, `q = |x|²`. -/
lemma jac_formula {R : CurvTensor 16} (hR : ∀ u v w, R.op u v w = RCayFun u v w) (x : Vec 16)
    (S : Matrix (Fin 16) (Fin 16) ℝ) (hA : Acay stdSys x = ((x ⬝ᵥ x) / 2) • (1 + S) - vecMulVec x x) (v : Vec 16) :
    R.jacobiMap x v = (5 * (x ⬝ᵥ x) / 2) • v + (3 * (x ⬝ᵥ x) / 2) • (S *ᵥ v) - (4 * (x ⬝ᵥ v)) • x := by
  change R.op v x x = _
  rw [hR, RCay_jacobi, hA]
  simp only [Osserman.Pi, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, outer_mulVec_real]
  module

/-- The reduced `μ|x|²`-eigenvectors of `J_x` are the `v ⊥ x` with `S_w v = ((2μ - 5)/3) v`. -/
lemma mem_iff {J : Vec 16 →ₗ[ℝ] Vec 16} {x : Vec 16} (hq : 0 < x ⬝ᵥ x) {S : Matrix (Fin 16) (Fin 16) ℝ}
    (hJ : ∀ v, J v = (5 * (x ⬝ᵥ x) / 2) • v + (3 * (x ⬝ᵥ x) / 2) • (S *ᵥ v) - (4 * (x ⬝ᵥ v)) • x)
    (μ : ℝ) (v : Vec 16) :
    v ∈ Module.End.eigenspace J (μ * (x ⬝ᵥ x)) ⊓ perp x ↔ x ⬝ᵥ v = 0 ∧ S *ᵥ v = ((2 * μ - 5) / 3) • v := by
  rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff]
  change J v = _ ∧ x ⬝ᵥ v = 0 ↔ _
  rw [hJ]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    rw [h2, mul_zero, zero_smul, sub_zero] at h1
    ext i
    have hi := congrFun h1 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    have key : (3 * (x ⬝ᵥ x) / 2) * ((S *ᵥ v) i - (2 * μ - 5) / 3 * v i) = 0 := by linear_combination hi
    rcases mul_eq_zero.1 key with h | h
    · linarith
    · linarith
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    rw [h1, mul_zero, zero_smul, sub_zero, h2, smul_smul, ← add_smul]
    congr 1
    ring

lemma c_cases {S : Matrix (Fin 16) (Fin 16) ℝ} (hSS : S * S = 1) {c : ℝ} {v : Vec 16} (hc : S *ᵥ v = c • v) :
    v = 0 ∨ c = 1 ∨ c = -1 := by
  have h : (c * c - 1) • v = 0 := by
    have e : S *ᵥ (S *ᵥ v) = v := by rw [mulVec_mulVec, hSS, one_mulVec]
    rw [hc, mulVec_smul, hc, smul_smul] at e
    rw [sub_smul, e, one_smul, sub_self]
  rcases smul_eq_zero.1 h with h | h
  · right
    exact mul_self_eq_one_iff.1 (by linarith)
  · left
    exact h

/-- A symmetric idempotent `px` with range `V` agrees with any symmetric `P` that maps into `V` and fixes `V`. -/
lemma proj_agree {V : Submodule ℝ (Vec 16)} (px : Vec 16 →ₗ[ℝ] Vec 16)
    (hpx : LinearMap.range px = V ∧ ∀ z w, px z ⬝ᵥ w = z ⬝ᵥ px w ∧ px (px z) = px z)
    (P : Vec 16 → Vec 16) (hP1 : ∀ z, P z ∈ V) (hP2 : ∀ v ∈ V, P v = v) (hPs : ∀ z w, P z ⬝ᵥ w = z ⬝ᵥ P w)
    (z w : Vec 16) : px z ⬝ᵥ w = P z ⬝ᵥ w := by
  obtain ⟨hr, hs⟩ := hpx
  have h1 : P (px z) = px z := hP2 _ (by rw [← hr]; exact LinearMap.mem_range_self px z)
  obtain ⟨u, hu⟩ : P w ∈ LinearMap.range px := by rw [hr]; exact hP1 w
  have h2 : px (P w) = P w := by rw [← hu, (hs u 0).2]
  calc px z ⬝ᵥ w = P (px z) ⬝ᵥ w := by rw [h1]
    _ = px z ⬝ᵥ P w := hPs _ _
    _ = z ⬝ᵥ px (P w) := (hs z (P w)).1
    _ = z ⬝ᵥ P w := by rw [h2]
    _ = P z ⬝ᵥ w := (hPs z w).symm

/-- The projector onto `{v ⊥ x : S v = v}`. -/
noncomputable def Pp (x : Vec 16) (S : Matrix (Fin 16) (Fin 16) ℝ) (z : Vec 16) : Vec 16 :=
  (1 / 2 : ℝ) • (z + S *ᵥ z) - ((x ⬝ᵥ z) / (x ⬝ᵥ x)) • x

/-- The projector onto `{v : S v = -v}` (these are `⊥ x` when `S x = x`). -/
noncomputable def Pm (S : Matrix (Fin 16) (Fin 16) ℝ) (z : Vec 16) : Vec 16 := (1 / 2 : ℝ) • (z - S *ᵥ z)

section projectors

variable {x : Vec 16} {S : Matrix (Fin 16) (Fin 16) ℝ}

lemma Pp_perp (hq : 0 < x ⬝ᵥ x) (hSx : S *ᵥ x = x) (hST : Sᵀ = S) (z : Vec 16) : x ⬝ᵥ Pp x S z = 0 := by
  have hq' := hq.ne'
  simp only [Pp, dotProduct_sub, dotProduct_smul, dotProduct_add, smul_eq_mul]
  rw [sym_dot hST x z, hSx]
  field_simp
  ring

lemma Pp_fix (hSx : S *ᵥ x = x) (hSS : S * S = 1) (z : Vec 16) : S *ᵥ Pp x S z = Pp x S z := by
  simp only [Pp, mulVec_sub, mulVec_smul, mulVec_add, mulVec_mulVec, hSS, one_mulVec, hSx]
  module

lemma Pp_id {v : Vec 16} (h0 : x ⬝ᵥ v = 0) (hv : S *ᵥ v = v) : Pp x S v = v := by
  simp only [Pp, h0, hv, zero_div, zero_smul, sub_zero]
  module

lemma Pp_symm (hST : Sᵀ = S) (z w : Vec 16) : Pp x S z ⬝ᵥ w = z ⬝ᵥ Pp x S w := by
  simp only [Pp, sub_dotProduct, smul_dotProduct, add_dotProduct, dotProduct_sub, dotProduct_smul, dotProduct_add,
    smul_eq_mul]
  rw [dotProduct_comm z x, sym_dot hST z w]
  ring

lemma Pm_perp (hSx : S *ᵥ x = x) (hST : Sᵀ = S) (z : Vec 16) : x ⬝ᵥ Pm S z = 0 := by
  simp only [Pm, dotProduct_smul, dotProduct_sub, smul_eq_mul]
  rw [sym_dot hST x z, hSx]
  ring

lemma Pm_fix (hSS : S * S = 1) (z : Vec 16) : S *ᵥ Pm S z = (-1 : ℝ) • Pm S z := by
  simp only [Pm, mulVec_smul, mulVec_sub, mulVec_mulVec, hSS, one_mulVec]
  module

lemma Pm_id {v : Vec 16} (hv : S *ᵥ v = (-1 : ℝ) • v) : Pm S v = v := by
  simp only [Pm, hv]
  module

lemma Pm_symm (hST : Sᵀ = S) (z w : Vec 16) : Pm S z ⬝ᵥ w = z ⬝ᵥ Pm S w := by
  have h := sym_dot hST z w
  simp only [Pm, smul_dotProduct, sub_dotProduct, dotProduct_smul, dotProduct_sub, smul_eq_mul]
  linarith

lemma Pp_link (hq : 0 < x ⬝ᵥ x) (hA : Acay stdSys x = ((x ⬝ᵥ x) / 2) • (1 + S) - vecMulVec x x) (y : Vec 16) :
    (x ⬝ᵥ x) * (Pp x S y ⬝ᵥ y) = y ⬝ᵥ (Acay stdSys x *ᵥ y) := by
  have hq' := hq.ne'
  rw [hA]
  simp only [Pp, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, outer_mulVec_real,
    sub_dotProduct, smul_dotProduct, add_dotProduct, dotProduct_sub, dotProduct_smul, dotProduct_add, smul_eq_mul]
  rw [dotProduct_comm y (S *ᵥ y), dotProduct_comm y x]
  field_simp

lemma Pm_link (hA : Acay stdSys x = ((x ⬝ᵥ x) / 2) • (1 + S) - vecMulVec x x) (y : Vec 16) :
    (x ⬝ᵥ x) * (Pm S y ⬝ᵥ y) = y ⬝ᵥ (Osserman.Pi x *ᵥ y) - y ⬝ᵥ (Acay stdSys x *ᵥ y) := by
  rw [hA]
  simp only [Pm, Osserman.Pi, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    outer_mulVec_real, sub_dotProduct, smul_dotProduct, dotProduct_sub, dotProduct_smul, dotProduct_add, smul_eq_mul]
  rw [dotProduct_comm y (S *ᵥ y)]
  ring

end projectors

lemma acay_quad (a b : Vec 16) : b ⬝ᵥ (Acay stdSys a *ᵥ b) =
    (1 / 2) * ((a ⬝ᵥ a) * (b ⬝ᵥ b) + hvec stdSys a ⬝ᵥ hvec stdSys b) - (a ⬝ᵥ b) * (a ⬝ᵥ b) := by
  have hc : (∑ i, (a ⬝ᵥ (stdSys i *ᵥ a)) • stdSys i) = Hcomb stdSys (hvec stdSys a) := rfl
  simp only [Acay, hc, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    outer_mulVec_real, dotProduct_sub, dotProduct_smul, dotProduct_add, quadratic_combination, smul_eq_mul]
  rw [dotProduct_comm b a]

lemma acay_swap (x y : Vec 16) : y ⬝ᵥ (Acay stdSys x *ᵥ y) = x ⬝ᵥ (Acay stdSys y *ᵥ x) := by
  rw [acay_quad, acay_quad, dotProduct_comm (hvec stdSys y), dotProduct_comm y x]
  ring

lemma pi_swap (x y : Vec 16) : y ⬝ᵥ (Osserman.Pi x *ᵥ y) = x ⬝ᵥ (Osserman.Pi y *ᵥ x) := by
  simp only [Osserman.Pi, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, outer_mulVec_real, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm y x]
  ring

/-- `|x|² ⟨p_x y, y⟩` for the reduced `μ|x|²`-projector `p_x` of `J_x(R_Cay)`: `⟨A(x)y,y⟩` for `μ = 4`,
`⟨(Π(x) - A(x))y,y⟩` for `μ = 1`, and `0` otherwise. -/
lemma side {R : CurvTensor 16} (hR : ∀ u v w, R.op u v w = RCayFun u v w) (μ : ℝ) (x : Vec 16) (hx : x ≠ 0)
    (px : Vec 16 →ₗ[ℝ] Vec 16)
    (hpx : LinearMap.range px = Module.End.eigenspace (R.jacobiMap x) (μ * (x ⬝ᵥ x)) ⊓ perp x ∧
        ∀ z w, px z ⬝ᵥ w = z ⬝ᵥ px w ∧ px (px z) = px z) (y : Vec 16) :
    (x ⬝ᵥ x) * (px y ⬝ᵥ y) = if μ = 4 then y ⬝ᵥ (Acay stdSys x *ᵥ y)
      else if μ = 1 then y ⬝ᵥ (Osserman.Pi x *ᵥ y) - y ⬝ᵥ (Acay stdSys x *ᵥ y) else 0 := by
  obtain ⟨S, hSx, hSS, hST, hA⟩ := acay_split x hx
  have hq := dot_pos hx
  have mem := mem_iff hq (jac_formula hR x S hA) μ
  split_ifs with h4 h1
  · have c4 : (2 * μ - 5) / 3 = 1 := by rw [h4]; norm_num
    have hP1 : ∀ z, Pp x S z ∈ Module.End.eigenspace (R.jacobiMap x) (μ * (x ⬝ᵥ x)) ⊓ perp x := fun z =>
      (mem _).2 ⟨Pp_perp hq hSx hST z, by rw [c4, one_smul]; exact Pp_fix hSx hSS z⟩
    have hP2 : ∀ v ∈ Module.End.eigenspace (R.jacobiMap x) (μ * (x ⬝ᵥ x)) ⊓ perp x, Pp x S v = v := fun v hv => by
      obtain ⟨h0, hc⟩ := (mem v).1 hv
      rw [c4, one_smul] at hc
      exact Pp_id h0 hc
    rw [proj_agree px hpx (Pp x S) hP1 hP2 (Pp_symm hST) y y]
    exact Pp_link hq hA y
  · have c1 : (2 * μ - 5) / 3 = -1 := by rw [h1]; norm_num
    have hP1 : ∀ z, Pm S z ∈ Module.End.eigenspace (R.jacobiMap x) (μ * (x ⬝ᵥ x)) ⊓ perp x := fun z =>
      (mem _).2 ⟨Pm_perp hSx hST z, by rw [c1]; exact Pm_fix hSS z⟩
    have hP2 : ∀ v ∈ Module.End.eigenspace (R.jacobiMap x) (μ * (x ⬝ᵥ x)) ⊓ perp x, Pm S v = v := fun v hv => by
      obtain ⟨-, hc⟩ := (mem v).1 hv
      rw [c1] at hc
      exact Pm_id hc
    rw [proj_agree px hpx (Pm S) hP1 hP2 (Pm_symm hST) y y]
    exact Pm_link hA y
  · have hP2 : ∀ v ∈ Module.End.eigenspace (R.jacobiMap x) (μ * (x ⬝ᵥ x)) ⊓ perp x, (fun _ => (0 : Vec 16)) v = v :=
      fun v hv => by
        obtain ⟨-, hc⟩ := (mem v).1 hv
        rcases c_cases hSS hc with h | h | h
        · exact h.symm
        · exact absurd (by linarith) h4
        · exact absurd (by linarith) h1
    rw [proj_agree px hpx (fun _ => 0) (fun _ => Submodule.zero_mem _) hP2 (fun _ _ => by simp) y y]
    simp

/-- The reduced multiplicities of `J_x(R_Cay)` at a unit `x`: `8` at `1`, `7` at `4`, `0` elsewhere. -/
lemma redMult_val {R : CurvTensor 16} (hR : ∀ u v w, R.op u v w = RCayFun u v w) (x : Vec 16) (hx : x ⬝ᵥ x = 1)
    (μ : ℝ) : R.redMult x μ = if μ = 1 then 8 else if μ = 4 then 7 else 0 := by
  have maps : R.jacobiMap x = Matrix.toLin' (Osserman.Pi x + (3 : ℝ) • Acay stdSys x) := by
    apply LinearMap.ext
    intro y
    change R.op y x x = (Osserman.Pi x + (3 : ℝ) • Acay stdSys x) *ᵥ y
    rw [hR, RCay_jacobi]
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  unfold CurvTensor.redMult
  split_ifs with h1 h4
  · subst h1
    rw [maps]
    exact (reduced_dimensions x hx).1
  · subst h4
    rw [maps]
    exact (reduced_dimensions x hx).2
  · obtain ⟨S, hSx, hSS, hST, hA⟩ := acay_split x hx0
    have hbot : Module.End.eigenspace (R.jacobiMap x) μ ⊓ perp x = ⊥ := by
      refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
      rw [show μ = μ * (x ⬝ᵥ x) by rw [hx, mul_one]] at hv
      obtain ⟨-, hc⟩ := (mem_iff (dot_pos hx0) (jac_formula hR x S hA) μ v).1 hv
      rcases c_cases hSS hc with h | h | h
      · exact h
      · exact absurd (by linarith) h4
      · exact absurd (by linarith) h1
    rw [hbot, finrank_bot]

/-- **Corollary D, non-vacuity** (Statements7 `cor_D_hyp_nonvacuous`): `R_Cay` is Osserman and Jacobi-proportional. -/
theorem cor_D_hyp_nonvacuous_proved :
    ∃ R : CurvTensor 16, R.IsOsserman ∧ IsJacobiProportional R ∧ (∀ u v w, R.op u v w = RCayFun u v w) := by
  obtain ⟨R, hR⟩ := sec1_Rcay_curv_proved
  refine ⟨R, fun x y hx hy μ => by rw [redMult_val hR x hx, redMult_val hR y hy], ?_, hR⟩
  intro μ x y hx hy px py hpx hpy
  rw [side hR μ x hx px hpx y, side hR μ y hy py hpy x]
  split_ifs
  · exact acay_swap x y
  · rw [pi_swap x y, acay_swap x y]
  · rfl

/-! ### Theorem E non-vacuity: the pattern `(7,7,1)` -/

/-- `R_J(u,v)w = ⟨Ju,w⟩Jv - ⟨Jv,w⟩Ju + 2⟨Ju,v⟩Jw`, the curvature tensor of one skew `J`. -/
def rjFun (M : Matrix (Fin 16) (Fin 16) ℝ) (u v w : Vec 16) : Vec 16 :=
  ((M *ᵥ u) ⬝ᵥ w) • (M *ᵥ v) - ((M *ᵥ v) ⬝ᵥ w) • (M *ᵥ u) + (2 * ((M *ᵥ u) ⬝ᵥ v)) • (M *ᵥ w)

section skew

variable {M : Matrix (Fin 16) (Fin 16) ℝ}

lemma skew_dot (hM : Mᵀ = -M) (a b : Vec 16) : (M *ᵥ a) ⬝ᵥ b = -((M *ᵥ b) ⬝ᵥ a) := by
  rw [dotProduct_comm (M *ᵥ b) a, dotProduct_mulVec, ← mulVec_transpose, hM, neg_mulVec, neg_dotProduct, neg_neg]

lemma skew_self (hM : Mᵀ = -M) (a : Vec 16) : (M *ᵥ a) ⬝ᵥ a = 0 := by
  have h := skew_dot hM a a
  linarith

lemma rj_add1 (u u' v w : Vec 16) : rjFun M (u + u') v w = rjFun M u v w + rjFun M u' v w := by
  simp only [rjFun, Matrix.mulVec_add, add_dotProduct]
  module

lemma rj_smul1 (c : ℝ) (u v w : Vec 16) : rjFun M (c • u) v w = c • rjFun M u v w := by
  simp only [rjFun, Matrix.mulVec_smul, smul_dotProduct, smul_eq_mul]
  module

lemma rj_add2 (u v v' w : Vec 16) : rjFun M u (v + v') w = rjFun M u v w + rjFun M u v' w := by
  simp only [rjFun, Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  module

lemma rj_smul2 (c : ℝ) (u v w : Vec 16) : rjFun M u (c • v) w = c • rjFun M u v w := by
  simp only [rjFun, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  module

lemma rj_add3 (u v w w' : Vec 16) : rjFun M u v (w + w') = rjFun M u v w + rjFun M u v w' := by
  simp only [rjFun, Matrix.mulVec_add, dotProduct_add]
  module

lemma rj_smul3 (c : ℝ) (u v w : Vec 16) : rjFun M u v (c • w) = c • rjFun M u v w := by
  simp only [rjFun, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  module

lemma rj_anti (hM : Mᵀ = -M) (u v w : Vec 16) : rjFun M u v w = -rjFun M v u w := by
  simp only [rjFun]
  rw [skew_dot hM u v]
  module

lemma rj_skew (hM : Mᵀ = -M) (u v w z : Vec 16) : rjFun M u v w ⬝ᵥ z = -(rjFun M u v z ⬝ᵥ w) := by
  simp only [rjFun, add_dotProduct, sub_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [skew_dot hM w z]
  ring

lemma rj_bianchi (hM : Mᵀ = -M) (u v w : Vec 16) : rjFun M u v w + rjFun M v w u + rjFun M w u v = 0 := by
  simp only [rjFun]
  rw [skew_dot hM w u, skew_dot hM u v, skew_dot hM v w]
  module

/-- `R_J(y,x)x = -3⟨Jx,y⟩Jx`. -/
lemma rj_jac (hM : Mᵀ = -M) (x y : Vec 16) : rjFun M y x x = (-3 * ((M *ᵥ x) ⬝ᵥ y)) • (M *ᵥ x) := by
  simp only [rjFun]
  rw [skew_self hM x, skew_dot hM y x]
  module

end skew

/-- The `Cl(8)`-structure `J_α = S_0 S_α` (`α = 1, …, 8`) of the standard system. -/
noncomputable def Jcl (a : Fin 8) : Matrix (Fin 16) (Fin 16) ℝ := stdSys 0 * stdSys a.succ

lemma Jcl_skew (a : Fin 8) : (Jcl a)ᵀ = -Jcl a := by
  have hC := sec6_std_system_proved.2.2 0 a.succ
  rw [ite_eq_right (Fin.succ_ne_zero a).symm] at hC
  rw [Jcl, transpose_mul, std_symmetric, std_symmetric]
  exact (neg_eq_of_add_eq_zero_right hC).symm

lemma Jcl_apply (a : Fin 8) (x : Vec 16) : Jcl a *ᵥ x = stdSysFun 0 (stdSysFun a.succ x) := by
  rw [Jcl, ← mulVec_mulVec, std_mulVec, std_mulVec]

lemma std_sq (i : Fin 9) (v : Vec 16) : stdSysFun i (stdSysFun i v) = v := by
  have h := std_clifford_fun i i v
  rw [ite_eq_left rfl, ← two_smul ℝ (stdSysFun i (stdSysFun i v))] at h
  exact smul_right_injective (Vec 16) two_ne_zero h

/-- `⟨J_α x, J_β x⟩ = δ_αβ |x|²`. -/
lemma frame_dot (a b : Fin 8) (x : Vec 16) :
    (Jcl a *ᵥ x) ⬝ᵥ (Jcl b *ᵥ x) = if a = b then x ⬝ᵥ x else 0 := by
  rw [Jcl_apply, Jcl_apply, std_adjoint, std_sq]
  have h1 := std_adjoint a.succ x (stdSysFun b.succ x)
  have h2 := std_adjoint b.succ x (stdSysFun a.succ x)
  have key : 2 * (stdSysFun a.succ x ⬝ᵥ stdSysFun b.succ x) =
      x ⬝ᵥ (stdSysFun a.succ (stdSysFun b.succ x) + stdSysFun b.succ (stdSysFun a.succ x)) := by
    rw [dotProduct_add, ← h1, ← h2, dotProduct_comm (stdSysFun b.succ x)]
    ring
  rw [std_clifford_fun] at key
  by_cases hab : a = b
  · subst hab
    rw [ite_eq_left rfl] at key ⊢
    rw [dotProduct_smul, smul_eq_mul] at key
    linarith
  · rw [ite_eq_right (fun h => hab (Fin.succ_injective _ h)), dotProduct_zero] at key
    rw [ite_eq_right hab]
    linarith

/-- The weights: `1` for `α ≤ 7`, `2` for `α = 8`. -/
noncomputable def cw (a : Fin 8) : ℝ := if a = Fin.last 7 then 2 else 1

/-- `Σ_{α ≤ 7} R_{J_α} + 2 R_{J_8}`. -/
noncomputable def fE (u v w : Vec 16) : Vec 16 := ∑ a, cw a • rjFun (Jcl a) u v w

lemma fE_curv : ∃ R : CurvTensor 16, ∀ u v w, R.op u v w = fE u v w := by
  refine Curv.exists_curv fE ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro u u' v w
    simp only [fE, rj_add1, smul_add, Finset.sum_add_distrib]
  · intro c u v w
    simp only [fE, rj_smul1, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => smul_comm _ _ _
  · intro u v v' w
    simp only [fE, rj_add2, smul_add, Finset.sum_add_distrib]
  · intro c u v w
    simp only [fE, rj_smul2, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => smul_comm _ _ _
  · intro u v w w'
    simp only [fE, rj_add3, smul_add, Finset.sum_add_distrib]
  · intro c u v w
    simp only [fE, rj_smul3, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => smul_comm _ _ _
  · intro u v w
    simp only [fE]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [rj_anti (Jcl_skew a), smul_neg]
  · intro u v w z
    simp only [fE, sum_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [rj_skew (Jcl_skew a)]; ring
  · intro u v w
    simp only [fE]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun a _ => by rw [← smul_add, ← smul_add, rj_bianchi (Jcl_skew a), smul_zero]

/-- `J_x = -3 Σ_α cw_α (J_α x)(J_α x)ᵀ`. -/
lemma jacE {R : CurvTensor 16} (hR : ∀ u v w, R.op u v w = fE u v w) (x y : Vec 16) :
    R.jacobiMap x y = ∑ a, (-3 * cw a * ((Jcl a *ᵥ x) ⬝ᵥ y)) • (Jcl a *ᵥ x) := by
  change R.op y x x = _
  rw [hR]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rj_jac (Jcl_skew a), smul_smul]
  congr 1
  ring

/-- Three reduced eigenspaces for distinct values are independent. -/
lemma three_inf (R : CurvTensor 16) (x : Vec 16) {μ1 μ2 μ3 : ℝ} (h12 : μ1 ≠ μ2) (h13 : μ1 ≠ μ3) (h23 : μ2 ≠ μ3) :
    (Spectral.Esp R x μ1 ⊔ Spectral.Esp R x μ2) ⊓ Spectral.Esp R x μ3 = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv.1
  have ha' := (Spectral.mem_Esp.1 ha).1
  have hb' := (Spectral.mem_Esp.1 hb).1
  have e3 := (Spectral.mem_Esp.1 hv.2).1
  simp only [map_add, LinearMap.add_apply, ha', hb'] at e3
  have e4 : R.op (μ1 • a + μ2 • b) x x = R.op (μ3 • (a + b)) x x := by rw [e3]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, ha', hb', smul_add] at e4
  ext i
  have c3 := congrFun e3 i
  have c4 := congrFun e4 i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at c3 c4
  have ka : (μ1 - μ2) * (μ1 - μ3) * a i = 0 := by linear_combination c4 - μ2 * c3
  have hai : a i = 0 := by
    rcases mul_eq_zero.1 ka with h | h
    · rcases mul_eq_zero.1 h with h' | h'
      · exact absurd (sub_eq_zero.1 h') h12
      · exact absurd (sub_eq_zero.1 h') h13
    · exact h
  have kb : (μ2 - μ3) * b i = 0 := by linear_combination c3 - (μ1 - μ3) * hai
  have hbi : b i = 0 := by
    rcases mul_eq_zero.1 kb with h | h
    · exact absurd (sub_eq_zero.1 h) h23
    · exact h
  simp only [Pi.add_apply, Pi.zero_apply, hai, hbi, add_zero]

/-- At a unit `x`, the reduced eigenspaces of `J_x` at `0, -3, -6` have dimensions `7, 7, 1`. -/
lemma dimsE {R : CurvTensor 16} (hR : ∀ u v w, R.op u v w = fE u v w) (x : Vec 16) (hx : x ⬝ᵥ x = 1) :
    Module.finrank ℝ (Spectral.Esp R x 0) = 7 ∧ Module.finrank ℝ (Spectral.Esp R x (-3)) = 7 ∧
      Module.finrank ℝ (Spectral.Esp R x (-6)) = 1 := by
  set e : Fin 8 → Vec 16 := fun a => Jcl a *ᵥ x with he
  have orth : ∀ a b, e a ⬝ᵥ e b = if a = b then 1 else 0 := fun a b => by
    simp only [he, frame_dot, hx]
  have ex : ∀ a, x ⬝ᵥ e a = 0 := fun a => by
    rw [dotProduct_comm]
    exact skew_self (Jcl_skew a) x
  have jac_e : ∀ b, R.op (e b) x x = (-3 * cw b) • e b := fun b => by
    change R.jacobiMap x (e b) = _
    rw [jacE hR, Finset.sum_eq_single b]
    · show (-3 * cw b * (e b ⬝ᵥ e b)) • e b = _
      rw [orth, ite_eq_left rfl, mul_one]
    · intro a _ hab
      show (-3 * cw a * (e a ⬝ᵥ e b)) • e a = 0
      rw [orth, ite_eq_right hab, mul_zero, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ b) h
  -- lower bound at `-3`: the seven vectors `J_α x`, `α ≤ 7`
  have li : LinearIndependent ℝ (fun j : Fin 7 => e j.castSucc) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have hd := congrArg (fun v => v ⬝ᵥ e j.castSucc) hg
    simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct] at hd
    rw [Finset.sum_eq_single j] at hd
    · rwa [orth, ite_eq_left rfl, mul_one] at hd
    · intro i _ hij
      rw [orth, ite_eq_right (fun h => hij (Fin.castSucc_injective _ h)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have le3 : Submodule.span ℝ (Set.range fun j : Fin 7 => e j.castSucc) ≤ Spectral.Esp R x (-3) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine Spectral.mem_Esp.2 ⟨?_, ex _⟩
    rw [jac_e, cw, ite_eq_right (Fin.castSucc_lt_last j).ne, mul_one]
  have d3 : 7 ≤ Module.finrank ℝ (Spectral.Esp R x (-3)) := by
    have h := Submodule.finrank_mono le3
    rwa [finrank_span_eq_card li, Fintype.card_fin] at h
  -- lower bound at `-6`: `J_8 x`
  have e7 : e (Fin.last 7) ≠ 0 := by
    intro h
    have h1 := orth (Fin.last 7) (Fin.last 7)
    rw [h, zero_dotProduct, ite_eq_left rfl] at h1
    exact zero_ne_one h1
  have le6 : ℝ ∙ e (Fin.last 7) ≤ Spectral.Esp R x (-6) := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    refine Spectral.mem_Esp.2 ⟨?_, ex _⟩
    rw [jac_e, cw, ite_eq_left rfl]
    norm_num
  have d6 : 1 ≤ Module.finrank ℝ (Spectral.Esp R x (-6)) := by
    have h := Submodule.finrank_mono le6
    rwa [finrank_span_singleton e7] at h
  -- lower bound at `0`: the vectors orthogonal to `x, J_1 x, …, J_8 x`
  let F : Vec 16 →ₗ[ℝ] (Fin 9 → ℝ) := LinearMap.pi fun i => Spectral.dotL ((Fin.cons x e : Fin 9 → Vec 16) i)
  have le0 : LinearMap.ker F ≤ Spectral.Esp R x 0 := by
    intro y hy
    have hi : ∀ i, (Fin.cons x e : Fin 9 → Vec 16) i ⬝ᵥ y = 0 := fun i => congrFun (LinearMap.mem_ker.1 hy) i
    have hxy : x ⬝ᵥ y = 0 := hi 0
    have hey : ∀ a, e a ⬝ᵥ y = 0 := fun a => hi a.succ
    refine Spectral.mem_Esp.2 ⟨?_, hxy⟩
    change R.jacobiMap x y = _
    rw [jacE hR, zero_smul]
    exact Finset.sum_eq_zero fun a _ => by
      show (-3 * cw a * (e a ⬝ᵥ y)) • e a = 0
      rw [hey, mul_zero, zero_smul]
  have d0 : 7 ≤ Module.finrank ℝ (Spectral.Esp R x 0) := by
    have h := LinearMap.finrank_range_add_finrank_ker F
    have hr := Submodule.finrank_le (LinearMap.range F)
    have hk := Submodule.finrank_mono le0
    rw [Module.finrank_fin_fun] at h hr
    omega
  -- upper bound: the three spaces are independent inside `x^⊥`
  have i1 : Spectral.Esp R x 0 ⊓ Spectral.Esp R x (-3) = ⊥ := Spectral.Esp_inf R x (by norm_num)
  have i2 := three_inf R x (μ1 := 0) (μ2 := -3) (μ3 := -6) (by norm_num) (by norm_num) (by norm_num)
  have s1 := Submodule.finrank_sup_add_finrank_inf_eq (Spectral.Esp R x 0) (Spectral.Esp R x (-3))
  have s2 := Submodule.finrank_sup_add_finrank_inf_eq (Spectral.Esp R x 0 ⊔ Spectral.Esp R x (-3))
    (Spectral.Esp R x (-6))
  rw [i1, finrank_bot] at s1
  rw [i2, finrank_bot] at s2
  have hle : Spectral.Esp R x 0 ⊔ Spectral.Esp R x (-3) ⊔ Spectral.Esp R x (-6) ≤ perp x :=
    sup_le (sup_le inf_le_right inf_le_right) inf_le_right
  have hp := Spectral.finrank_perp hx
  have hm := Submodule.finrank_mono hle
  omega

/-- **Theorem E, non-vacuity** (Statements7 `thm_E_hyp_nonvacuous`): the pattern `(7,7,1)` occurs, for
`J_x = -3(Σ_{α ≤ 7} (J_αx)(J_αx)ᵀ + 2(J_8x)(J_8x)ᵀ)` (`-3` times the paper's witness), `J_α = S_0S_α` (reduced
eigenvalues `0, -3, -6`). -/
theorem thm_E_hyp_nonvacuous_proved : ∃ R : CurvTensor 16, HasPattern R ![7, 7, 1] := by
  obtain ⟨R, hR⟩ := fE_curv
  refine ⟨R, ![0, -3, -6], ?_, fun x hx i => ?_⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | norm_num at h
  · obtain ⟨h0, h3, h6⟩ := dimsE hR x hx
    fin_cases i
    · exact h0
    · exact h3
    · exact h6

end Osserman.Proofs.CorDNonvacuous
