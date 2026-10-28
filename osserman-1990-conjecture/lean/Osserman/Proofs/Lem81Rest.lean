/-
Lem81Rest.lean — Lemma 8.1 of paper 013 (sec_small_roots.tex of the posting copy, lines 17-52): the rows other than the
five of Lem81Stable.lean, on the Statements8 v0.31 types (review a3 applied: MUST-2 rows, NIT-5).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Route. For `x ≠ 0` Section 6 gives the symmetric involution `S_w = ∑ (h_i/q) S_i` with `S_w x = x`,
`∑ (S_ix)(S_ix)ᵀ = xxᵀ + qI - (q/2)(I + S_w)`, and Section 7 gives `L(x)`, `N(x)` as its `±1` eigenspaces. So
`π_N y = (y - S_w y)/2` and `Z_x y = ⟨x,y⟩x + q π_N y`, the paper's `Z_x = xxᵀ + q π_N`.
-/
import Osserman.Defs.SmallRoots
import Osserman.Proofs.Lem81Stable
import Osserman.Proofs.Threshold
import Osserman.Proofs.Hopf
import Osserman.Proofs.CayleyEigenspaces
import Osserman.Proofs.Lemma71Blocks
import Osserman.Proofs.Six1
import Osserman.Proofs.CayleyProducts

namespace Osserman.Proofs.Lem81

open Osserman Matrix Osserman.Proofs.StdSystem

/-! ## Orthogonal projections -/

lemma mem_orthSub_iff {n : ℕ} (W : Submodule ℝ (Vec n)) (v : Vec n) :
    v ∈ orthSub W ↔ ∀ w ∈ W, w ⬝ᵥ v = 0 := Iff.rfl

/-- The orthogonal projection is unique. -/
lemma orthProj_unique {n : ℕ} {W : Submodule ℝ (Vec n)} {v w w' : Vec n} (h : IsOrthProj W v w)
    (h' : IsOrthProj W v w') : w = w' := by
  have diff : w - w' ∈ W := W.sub_mem h.1 h'.1
  have orth : (v - w') - (v - w) ∈ orthSub W := (orthSub W).sub_mem h'.2 h.2
  have zero := (mem_orthSub_iff W _).mp orth _ diff
  rw [show (v - w') - (v - w) = w - w' by abel] at zero
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp zero)

lemma vmv_mulVec {n : ℕ} (u v w : Vec n) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  rw [vecMulVec_mulVec, op_smul_eq_smul]

lemma dot_mulVec_T {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (a y : Vec n) : a ⬝ᵥ (M *ᵥ y) = (Mᵀ *ᵥ a) ⬝ᵥ y := by
  rw [dotProduct_mulVec, mulVec_transpose]

lemma skew_dot_self {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ} (hK : Kᵀ = -K) (x : Vec n) : x ⬝ᵥ (K *ᵥ x) = 0 := by
  have h := dot_mulVec_T K x x
  rw [hK, neg_mulVec, neg_dotProduct, dotProduct_comm] at h
  rw [dotProduct_comm]
  linarith

/-! ## The involution `S_w` of a point, `π_N` and `Z_x` -/

section Projection

variable (x : Vec 16)

/-- `S_w = ∑ (h_i/q) S_i` (Section 6). -/
noncomputable def swOf : Matrix (Fin 16) (Fin 16) ℝ := ∑ i, ((x ⬝ᵥ (stdSys i *ᵥ x)) / (x ⬝ᵥ x)) • stdSys i

/-- `π_N y = (y - S_w y)/2`. -/
noncomputable def projN (y : Vec 16) : Vec 16 := (1 / 2 : ℝ) • (y - swOf x *ᵥ y)

variable {x}

lemma sw_facts (hx : x ≠ 0) :
    swOf x * swOf x = 1 ∧ swOf x *ᵥ x = x ∧
      ∑ i, vecMulVec (stdSys i *ᵥ x) (stdSys i *ᵥ x) =
        vecMulVec x x + (x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ) - ((x ⬝ᵥ x) / 2) • (1 + swOf x) ∧
      ∑ i, (x ⬝ᵥ (stdSys i *ᵥ x)) • stdSys i = (x ⬝ᵥ x) • swOf x := by
  obtain ⟨-, hSwx, hsq, -, -, -, -, hZ, -, hsum, hQ⟩ :=
    Osserman.Proofs.CayleyEigenspaces.sec6_Sw_proved stdSys sec6_std_system_proved.2 x hx
  exact ⟨hsq, hSwx, by rw [hZ, hQ]; rfl, hsum⟩

lemma mem_N_iff (hx : x ≠ 0) (v : Vec 16) : v ∈ Nstd x ↔ swOf x *ᵥ v = -v := by
  have h := Osserman.Proofs.Lemma71Geometry.negative_space x hx
  simp only at h
  rw [h, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, neg_one_smul]
  exact Iff.rfl

lemma mem_L_iff (hx : x ≠ 0) (v : Vec 16) : v ∈ Lstd x ↔ swOf x *ᵥ v = v := by
  have h := (Osserman.Proofs.Lemma71Geometry.sec7_L_eigenspace_proved x hx).2.1
  simp only at h
  rw [h, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, one_smul]
  exact Iff.rfl

lemma orthSub_N : orthSub (Nstd x) = Lstd x := Osserman.Proofs.Six1.orthSub_orthSub (Lstd x)

lemma dot_L_N {l v : Vec 16} (hl : l ∈ Lstd x) (hv : v ∈ Nstd x) : l ⬝ᵥ v = 0 := hv l hl

lemma projN_mem (hx : x ≠ 0) (y : Vec 16) : projN x y ∈ Nstd x := by
  rw [mem_N_iff hx, projN, mulVec_smul, mulVec_sub, mulVec_mulVec, (sw_facts hx).1, one_mulVec]
  module

lemma projN_rest (hx : x ≠ 0) (y : Vec 16) : y - projN x y ∈ Lstd x := by
  rw [mem_L_iff hx, projN, mulVec_sub, mulVec_smul, mulVec_sub, mulVec_mulVec, (sw_facts hx).1, one_mulVec]
  module

lemma projN_isOrthProj (hx : x ≠ 0) (y : Vec 16) : IsOrthProj (Nstd x) y (projN x y) :=
  ⟨projN_mem hx y, by rw [orthSub_N]; exact projN_rest hx y⟩

lemma isOrthProj_N_iff (hx : x ≠ 0) (y w : Vec 16) : IsOrthProj (Nstd x) y w ↔ w = projN x y :=
  ⟨fun h => orthProj_unique h (projN_isOrthProj hx y), fun h => h ▸ projN_isOrthProj hx y⟩

lemma Z_mulVec (hx : x ≠ 0) (y : Vec 16) :
    (∑ i, vecMulVec (stdSys i *ᵥ x) (stdSys i *ᵥ x)) *ᵥ y = (x ⬝ᵥ y) • x + (x ⬝ᵥ x) • projN x y := by
  rw [(sw_facts hx).2.2.1, sub_mulVec, add_mulVec, vmv_mulVec, smul_mulVec, one_mulVec, smul_mulVec,
    add_mulVec, one_mulVec, projN]
  module

lemma Z_mulVec_sum (v : Vec 16) :
    (∑ i, vecMulVec (stdSys i *ᵥ x) (stdSys i *ᵥ x)) *ᵥ v = ∑ i, ((stdSys i *ᵥ x) ⬝ᵥ v) • (stdSys i *ᵥ x) := by
  rw [sum_mulVec]
  simp only [vmv_mulVec]

end Projection

/-! ## The rows -/

/-- **Lemma 8.1** (lines 23-24), (hidden): `|π_E v|² + |π_N v|² = |v|²` for `v ⊥ x`. -/
theorem lem_8_1_pythagoras_proved (x : Vec 16) (_hx : x ≠ 0) (v : Vec 16) (hv : x ⬝ᵥ v = 0) (wE wN : Vec 16)
    (hE : IsOrthProj (Estd x) v wE) (hN : IsOrthProj (Nstd x) v wN) : wE ⬝ᵥ wE + wN ⬝ᵥ wN = v ⬝ᵥ v := by
  have hwN : wN ∈ Nstd x := hN.1
  have hrest : v - wN ∈ Lstd x := by rw [← orthSub_N]; exact hN.2
  have xwN : x ⬝ᵥ wN = 0 := dot_L_N (Osserman.Proofs.Lemma71Geometry.self_mem_L x) hwN
  have hE' : IsOrthProj (Estd x) v (v - wN) := by
    refine ⟨⟨hrest, ?_⟩, ?_⟩
    · show x ⬝ᵥ (v - wN) = 0
      rw [dotProduct_sub, hv, xwN, sub_zero]
    · rw [sub_sub_cancel]
      intro e he
      exact dot_L_N he.1 hwN
  rw [orthProj_unique hE hE']
  have cross : (v - wN) ⬝ᵥ wN = 0 := dot_L_N hrest hwN
  rw [sub_dotProduct] at cross
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm wN v]
  linarith

/-- **Lemma 8.1, proof** (lines 30-33): `∑(H_ix)(H_ix)ᵀ = xxᵀ + qπ_N = qπ_{ℝx+N}`. -/
theorem lem_8_1_Z_proj_proved (x : Vec 16) (hx : x ≠ 0) :
    let Z := ∑ i, vecMulVec (stdSys i *ᵥ x) (stdSys i *ᵥ x)
    ∀ y : Vec 16, (∀ w, IsOrthProj (Nstd x) y w → Z *ᵥ y = (x ⬝ᵥ y) • x + (x ⬝ᵥ x) • w) ∧
      IsOrthProj (Submodule.span ℝ {x} ⊔ Nstd x) y ((x ⬝ᵥ x)⁻¹ • (Z *ᵥ y)) := by
  dsimp only
  intro y
  have qne : x ⬝ᵥ x ≠ 0 := fun h => hx (dotProduct_self_eq_zero.mp h)
  refine ⟨fun w hw => by rw [Z_mulVec hx, (isOrthProj_N_iff hx y w).mp hw], ?_⟩
  have split : (x ⬝ᵥ x)⁻¹ • ((∑ i, vecMulVec (stdSys i *ᵥ x) (stdSys i *ᵥ x)) *ᵥ y) =
      ((x ⬝ᵥ x)⁻¹ * (x ⬝ᵥ y)) • x + projN x y := by
    rw [Z_mulVec hx, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ qne, one_smul]
  rw [split]
  refine ⟨Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)) (projN_mem hx y), ?_⟩
  have xL := Osserman.Proofs.Lemma71Geometry.self_mem_L x
  have zL : y - (((x ⬝ᵥ x)⁻¹ * (x ⬝ᵥ y)) • x + projN x y) ∈ Lstd x := by
    rw [show y - (((x ⬝ᵥ x)⁻¹ * (x ⬝ᵥ y)) • x + projN x y) =
      (y - projN x y) - ((x ⬝ᵥ x)⁻¹ * (x ⬝ᵥ y)) • x by abel]
    exact (Lstd x).sub_mem (projN_rest hx y) ((Lstd x).smul_mem _ xL)
  intro v hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp ha
  have xp : x ⬝ᵥ projN x y = 0 := dot_L_N xL (projN_mem hx y)
  have key : (x ⬝ᵥ x)⁻¹ * (x ⬝ᵥ y) * (x ⬝ᵥ x) = x ⬝ᵥ y := by field_simp
  have xz : x ⬝ᵥ (y - (((x ⬝ᵥ x)⁻¹ * (x ⬝ᵥ y)) • x + projN x y)) = 0 := by
    rw [dotProduct_sub, dotProduct_add, dotProduct_smul, xp, smul_eq_mul, add_zero, key, sub_self]
  rw [add_dotProduct, smul_dotProduct, xz, smul_zero, zero_add, dotProduct_comm]
  exact dot_L_N zL hb

/-- **Lemma 8.1, proof** (lines 34-35): "the nine orthogonal vectors `H_ix` ... span `ℝx+N(x)`". -/
theorem lem_8_1_span_proved (x : Vec 16) (hx : x ≠ 0) :
    Submodule.span ℝ (Set.range fun i => stdSys i *ᵥ x) = Submodule.span ℝ {x} ⊔ Nstd x := by
  have qne : x ⬝ᵥ x ≠ 0 := fun h => hx (dotProduct_self_eq_zero.mp h)
  have Zspan : ∀ v, (∑ i, vecMulVec (stdSys i *ᵥ x) (stdSys i *ᵥ x)) *ᵥ v ∈
      Submodule.span ℝ (Set.range fun i => stdSys i *ᵥ x) := by
    intro v
    rw [Z_mulVec_sum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have back : ∀ v, (∑ i, vecMulVec (stdSys i *ᵥ x) (stdSys i *ᵥ x)) *ᵥ v = (x ⬝ᵥ x) • v →
      v ∈ Submodule.span ℝ (Set.range fun i => stdSys i *ᵥ x) := by
    intro v hv
    have h := Submodule.smul_mem _ (x ⬝ᵥ x)⁻¹ (Zspan v)
    rwa [hv, smul_smul, inv_mul_cancel₀ qne, one_smul] at h
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hZi : (∑ j, vecMulVec (stdSys j *ᵥ x) (stdSys j *ᵥ x)) *ᵥ (stdSys i *ᵥ x) = (x ⬝ᵥ x) • (stdSys i *ᵥ x) := by
      rw [Z_mulVec_sum]
      simp only [lem_8_1_orthonormal_proved, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hsplit := Z_mulVec hx (stdSys i *ᵥ x)
    rw [hZi] at hsplit
    have hcoef : stdSys i *ᵥ x = ((x ⬝ᵥ x)⁻¹ * (x ⬝ᵥ (stdSys i *ᵥ x))) • x + projN x (stdSys i *ᵥ x) := by
      have h2 := congrArg (fun v => (x ⬝ᵥ x)⁻¹ • v) hsplit
      simp only [smul_add, smul_smul, inv_mul_cancel₀ qne, one_smul] at h2
      exact h2
    have hmem := Submodule.add_mem_sup (Submodule.smul_mem _ ((x ⬝ᵥ x)⁻¹ * (x ⬝ᵥ (stdSys i *ᵥ x)))
      (Submodule.mem_span_singleton_self x)) (projN_mem hx (stdSys i *ᵥ x))
    rw [← hcoef] at hmem
    exact hmem
  · apply sup_le
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      refine back x ?_
      rw [Z_mulVec hx, projN, (sw_facts hx).2.1, sub_self, smul_zero, smul_zero, add_zero]
    · intro v hv
      refine back v ?_
      have hxv : x ⬝ᵥ v = 0 := dot_L_N (Osserman.Proofs.Lemma71Geometry.self_mem_L x) hv
      rw [Z_mulVec hx, hxv, zero_smul, zero_add, projN, (mem_N_iff hx v).mp hv, sub_neg_eq_add]
      congr 1
      module

/-- **Lemma 8.1, proof** (lines 35-36): "$K$ being skew, $\sum_i a_i^2=cq^2$". -/
theorem lem_8_1_sum_a_proved (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : Kᵀ = -K) (c : ℝ)
    (hc : ∀ x : Vec 16, x ≠ 0 → ∃ w, IsOrthProj (Nstd x) (K *ᵥ x) w ∧ w ⬝ᵥ w = c * (x ⬝ᵥ x)) :
    ∀ x : Vec 16, ∑ i, ((stdSys i *ᵥ x) ⬝ᵥ (K *ᵥ x)) ^ 2 = c * (x ⬝ᵥ x) ^ 2 := by
  intro x
  by_cases hx : x = 0
  · subst hx
    simp
  obtain ⟨w, hw, hww⟩ := hc x hx
  have quad : (K *ᵥ x) ⬝ᵥ ((∑ i, vecMulVec (stdSys i *ᵥ x) (stdSys i *ᵥ x)) *ᵥ (K *ᵥ x)) =
      ∑ i, ((stdSys i *ᵥ x) ⬝ᵥ (K *ᵥ x)) ^ 2 := by
    rw [Z_mulVec_sum, dotProduct_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dotProduct_smul, smul_eq_mul, dotProduct_comm (K *ᵥ x), sq]
  have hwK : (K *ᵥ x) ⬝ᵥ w = w ⬝ᵥ w := by
    have h := (mem_orthSub_iff _ _).mp hw.2 w hw.1
    rw [dotProduct_sub, sub_eq_zero, dotProduct_comm] at h
    exact h
  rw [← quad, Z_mulVec hx, ← (isOrthProj_N_iff hx _ w).mp hw, dotProduct_add, dotProduct_smul, dotProduct_smul,
    dotProduct_comm (K *ᵥ x) x, skew_dot_self hK x, zero_smul, zero_add, hwK, hww, smul_eq_mul]
  ring

/-- **Lemma 8.1, proof** (lines 36-37): "differentiating the latter along $Kx$ gives $\sum_i h_ia_i=0$". Lean's
route: `∑ h_i S_i x = q S_w x = q x` (Section 6), then `⟨qx, Kx⟩ = 0`. -/
theorem lem_8_1_sum_ha_proved (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : Kᵀ = -K) (x : Vec 16) :
    ∑ i, (x ⬝ᵥ (stdSys i *ᵥ x)) * ((stdSys i *ᵥ x) ⬝ᵥ (K *ᵥ x)) = 0 := by
  by_cases hx : x = 0
  · subst hx
    simp
  have vec : ∑ i, (x ⬝ᵥ (stdSys i *ᵥ x)) • (stdSys i *ᵥ x) = (x ⬝ᵥ x) • x := by
    have h := congrArg (fun M => M *ᵥ x) (sw_facts hx).2.2.2
    rw [sum_mulVec, smul_mulVec, (sw_facts hx).2.1] at h
    simpa only [smul_mulVec] using h
  calc ∑ i, (x ⬝ᵥ (stdSys i *ᵥ x)) * ((stdSys i *ᵥ x) ⬝ᵥ (K *ᵥ x))
      = (∑ i, (x ⬝ᵥ (stdSys i *ᵥ x)) • (stdSys i *ᵥ x)) ⬝ᵥ (K *ᵥ x) := by
        rw [sum_dotProduct]
        simp only [smul_dotProduct, smul_eq_mul]
    _ = 0 := by rw [vec, smul_dotProduct, skew_dot_self hK, smul_zero]

/-- **Lemma 8.1, proof** (lines 37-38): "The matrix of $a_i$ is the symmetric trace-free $A_i=(H_iK-KH_i)/2$". -/
theorem lem_8_1_A_matrix_proved (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : Kᵀ = -K) (i : Fin 9) :
    let Ai := (1 / 2 : ℝ) • (stdSys i * K - K * stdSys i)
    Aiᵀ = Ai ∧ Ai.trace = 0 ∧ ∀ x : Vec 16, x ⬝ᵥ (Ai *ᵥ x) = (stdSys i *ᵥ x) ⬝ᵥ (K *ᵥ x) := by
  dsimp only
  have hS := std_symmetric i
  refine ⟨?_, ?_, fun x => ?_⟩
  · rw [transpose_smul, transpose_sub, transpose_mul, transpose_mul, hS, hK, neg_mul, mul_neg, sub_neg_eq_add,
      neg_add_eq_sub]
  · rw [trace_smul, trace_sub, trace_mul_comm, sub_self, smul_zero]
  · rw [smul_mulVec, dotProduct_smul, sub_mulVec, dotProduct_sub, ← mulVec_mulVec, ← mulVec_mulVec,
      dot_mulVec_T (stdSys i) x (K *ᵥ x), hS, dot_mulVec_T K x (stdSys i *ᵥ x), hK, neg_mulVec, neg_dotProduct,
      dotProduct_comm (K *ᵥ x), sub_neg_eq_add, smul_eq_mul]
    ring

lemma hvec_fam (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : Kᵀ = -K) (c t : ℝ) (x : Vec 16) (i : Fin 9) :
    hvec (lem81Fam K c t) x i = Real.cos t * (x ⬝ᵥ (stdSys i *ᵥ x)) +
      ((Real.sqrt c)⁻¹ * Real.sin t) * ((stdSys i *ᵥ x) ⬝ᵥ (K *ᵥ x)) := by
  have hA := lem_8_1_A_matrix_proved K hK i
  simp only at hA
  show x ⬝ᵥ (lem81Fam K c t i *ᵥ x) = _
  unfold lem81Fam
  rw [add_mulVec, smul_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, dotProduct_smul, hA.2.2 x,
    smul_eq_mul, smul_eq_mul]

/-- **Lemma 8.1, proof** (lines 40-41): the expansion of `∑⟨H_i(t)x,x⟩²` (general form of review a2-six SHOULD-3). -/
theorem lem_8_1_rotate_proved (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : Kᵀ = -K) (c : ℝ) (hc0 : 0 < c) (t : ℝ)
    (x : Vec 16) :
    ∑ i, hvec (lem81Fam K c t) x i ^ 2 =
      Real.cos t ^ 2 * ∑ i, (x ⬝ᵥ (stdSys i *ᵥ x)) ^ 2 +
        2 * Real.cos t * Real.sin t * (Real.sqrt c)⁻¹ *
          ∑ i, (x ⬝ᵥ (stdSys i *ᵥ x)) * ((stdSys i *ᵥ x) ⬝ᵥ (K *ᵥ x)) +
        Real.sin t ^ 2 * c⁻¹ * ∑ i, ((stdSys i *ᵥ x) ⬝ᵥ (K *ᵥ x)) ^ 2 := by
  have hs : ((Real.sqrt c)⁻¹) ^ 2 = c⁻¹ := by rw [inv_pow, Real.sq_sqrt hc0.le]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hvec_fam K hK c t x i, ← hs]
  ring

/-- **Lemma 8.1, proof** (lines 41-43): the `H_i(t)` are symmetric and trace-free, and nine symmetric trace-free
matrices with `∑⟨H_ix,x⟩² = 1` on the unit sphere do not give a constant map. -/
theorem lem_8_1_not_const_proved (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : Kᵀ = -K) (c t : ℝ) :
    (∀ i, (lem81Fam K c t i).IsSymm ∧ (lem81Fam K c t i).trace = 0) ∧
      ∀ H : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ, (∀ i, (H i).IsSymm ∧ (H i).trace = 0) →
        (∀ x : Vec 16, x ⬝ᵥ x = 1 → ∑ i, hvec H x i ^ 2 = 1) →
        ∃ x y : Vec 16, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧ hvec H x ≠ hvec H y := by
  refine ⟨fun i => ?_, fun H hH hsum => ?_⟩
  · have hA := lem_8_1_A_matrix_proved K hK i
    simp only at hA
    refine ⟨?_, ?_⟩
    · show (lem81Fam K c t i)ᵀ = lem81Fam K c t i
      unfold lem81Fam
      rw [transpose_add, transpose_smul, transpose_smul, std_symmetric, hA.1]
    · unfold lem81Fam
      rw [trace_add, trace_smul, trace_smul, std_sys_trace_zero_proved, hA.2.1, smul_zero, smul_zero, add_zero]
  · have unit (j : Fin 16) : (Pi.single j 1 : Vec 16) ⬝ᵥ Pi.single j 1 = 1 := by simp
    have diag (i : Fin 9) (j : Fin 16) : hvec H (Pi.single j 1) i = H i j j := by
      simp [hvec, mulVec, dotProduct, Pi.single_apply]
    by_contra hall
    have const (j : Fin 16) : hvec H (Pi.single j 1) = hvec H (Pi.single 0 1) := by
      by_contra hne
      exact hall ⟨_, _, unit j, unit 0, hne⟩
    have zero (i : Fin 9) : H i 0 0 = 0 := by
      have hjj (j : Fin 16) : H i j j = H i 0 0 := by rw [← diag i j, ← diag i 0, const j]
      have htr : (H i).trace = 16 * H i 0 0 := by
        simp only [Matrix.trace, Matrix.diag_apply, hjj, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        norm_num
      linarith [(hH i).2]
    have one := hsum _ (unit 0)
    simp [diag, zero] at one

/-- **Lemma 8.1, proof** (lines 43-45): "By Lemma 4.1(c) the $H_i(t)$ form a symmetric Clifford system". -/
theorem lem_8_1_clifford_t_proved (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : Kᵀ = -K) (c t : ℝ)
    (hsum : ∀ x : Vec 16, ∑ i, hvec (lem81Fam K c t) x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (hnc : ∃ x y : Vec 16, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧ hvec (lem81Fam K c t) x ≠ hvec (lem81Fam K c t) y) :
    IsSymmCliffordSystem (lem81Fam K c t) := by
  have hsym (i : Fin 9) : (lem81Fam K c t i).IsSymm := ((lem_8_1_not_const_proved K hK c t).1 i).1
  exact ⟨hsym, Osserman.Proofs.Threshold.lem_4_1_c_proved (lem81Fam K c t) hsym hsum (by norm_num) (by norm_num) hnc⟩

/-- The trace of an involution is an integer: `Ω = 2P - I` with `P = (I + Ω)/2` idempotent, `tr P = rank P`. -/
lemma trace_int_of_inv {n : ℕ} (Ω : Matrix (Fin n) (Fin n) ℝ) (h : Ω * Ω = 1) : ∃ z : ℤ, Ω.trace = z := by
  set P : Matrix (Fin n) (Fin n) ℝ := (1 / 2 : ℝ) • (1 + Ω) with hPdef
  have hP : P * P = P := by
    rw [hPdef, smul_mul_smul_comm, add_mul, mul_add, mul_add, h, one_mul, mul_one, one_mul]
    module
  have hidem : IsIdempotentElem (Matrix.toLin' P) := by
    show Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP]
  have htr := (LinearMap.IsIdempotentElem.isProj_range _ hidem).trace
  rw [Matrix.trace_toLin'_eq] at htr
  refine ⟨2 * (Module.finrank ℝ (LinearMap.range (Matrix.toLin' P)) : ℤ) - n, ?_⟩
  have hΩ : Ω = (2 : ℝ) • P - 1 := by
    rw [hPdef, smul_smul]
    module
  rw [hΩ, trace_sub, trace_smul, htr, trace_one, Fintype.card_fin, smul_eq_mul]
  push_cast
  ring

/-- **Lemma 8.1, proof** (line 46): "$\tr\Omega(t)$ is continuous and integer-valued, hence constant". -/
theorem lem_8_1_trace_const_proved (H : ℝ → Fin 9 → Matrix (Fin 16) (Fin 16) ℝ)
    (hcont : ∀ i, Continuous fun t => H t i) (hH : ∀ t, IsSymmCliffordSystem (H t)) :
    Continuous (fun t : ℝ => (cliffProd (H t)).trace) ∧ (∀ t : ℝ, ∃ z : ℤ, (cliffProd (H t)).trace = z) ∧
      ∀ t : ℝ, (cliffProd (H t)).trace = (cliffProd (H 0)).trace := by
  have cont : Continuous (fun t : ℝ => (cliffProd (H t)).trace) := by
    apply Continuous.matrix_trace
    have hform : (fun t => cliffProd (H t)) = fun t => ((List.finRange 9).map fun i => H t i).prod := by
      funext t
      rw [cliffProd, List.ofFn_eq_map]
    rw [hform]
    exact continuous_list_prod _ fun i _ => hcont i
  have hint (t : ℝ) : ∃ z : ℤ, (cliffProd (H t)).trace = z :=
    trace_int_of_inv _ (cliffProd_nine_symm_inv_proved (H t) (hH t)).2
  refine ⟨cont, hint, fun t => ?_⟩
  choose g hg using hint
  have gcont : Continuous g := by
    rw [Int.isClosedEmbedding_coe_real.isEmbedding.continuous_iff]
    have hfun : ((↑) ∘ g : ℝ → ℝ) = fun t => (cliffProd (H t)).trace := by
      funext s
      exact (hg s).symm
    rw [hfun]
    exact cont
  rw [hg t, hg 0, PreconnectedSpace.constant inferInstance gcont]

/-- **Lemma 8.1, proof** (lines 40, 50), (hidden): `c ≥ 0`. -/
theorem lem_8_1_c_nonneg_proved (K : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ)
    (hc : ∀ x : Vec 16, x ≠ 0 → ∃ w, IsOrthProj (Nstd x) (K *ᵥ x) w ∧ w ⬝ᵥ w = c * (x ⬝ᵥ x)) : 0 ≤ c := by
  have e0 : (Pi.single 0 1 : Vec 16) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  obtain ⟨w, -, hww⟩ := hc _ e0
  have unit : (Pi.single 0 1 : Vec 16) ⬝ᵥ Pi.single 0 1 = 1 := by simp
  rw [unit, mul_one] at hww
  rw [← hww]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (w i)

/-- **Lemma 8.1, proof** (lines 50-51): "If $c=0$, then $Kx\in L(x)$, and skewness gives $Kx\in E(x)$, so $K=0$ by
Lemma~\ref{lem:nofield}" (`lem_7_1_a`). -/
theorem lem_8_1_c_zero_proved (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : Kᵀ = -K) (c : ℝ) (hc0 : c = 0)
    (hc : ∀ x : Vec 16, x ≠ 0 → ∃ w, IsOrthProj (Nstd x) (K *ᵥ x) w ∧ w ⬝ᵥ w = c * (x ⬝ᵥ x)) :
    (∀ x : Vec 16, x ≠ 0 → K *ᵥ x ∈ Lstd x ∧ K *ᵥ x ∈ Estd x) ∧ K = 0 := by
  have inE (x : Vec 16) (hx : x ≠ 0) : K *ᵥ x ∈ Lstd x ∧ K *ᵥ x ∈ Estd x := by
    obtain ⟨w, hw, hww⟩ := hc x hx
    rw [hc0, zero_mul] at hww
    have w0 : w = 0 := dotProduct_self_eq_zero.mp hww
    have hL : K *ᵥ x ∈ Lstd x := by
      have h := hw.2
      rw [w0, sub_zero, orthSub_N] at h
      exact h
    exact ⟨hL, Submodule.mem_inf.mpr ⟨hL, skew_dot_self hK x⟩⟩
  exact ⟨inE, Osserman.Proofs.Lemma71Blocks.lem_7_1_a_proved K fun x hx => (inE x hx).2⟩

/-- **Lemma 8.1, proof** (lines 40-50): the case `c > 0` is impossible. -/
theorem lem_8_1_c_pos_proved (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : Kᵀ = -K) (c : ℝ)
    (hc : ∀ x : Vec 16, x ≠ 0 → ∃ w, IsOrthProj (Nstd x) (K *ᵥ x) w ∧ w ⬝ᵥ w = c * (x ⬝ᵥ x)) : ¬ 0 < c := by
  intro hpos
  have hcne : c ≠ 0 := hpos.ne'
  have hsum (t : ℝ) (x : Vec 16) : ∑ i, hvec (lem81Fam K c t) x i ^ 2 = (x ⬝ᵥ x) ^ 2 := by
    rw [lem_8_1_rotate_proved K hK c hpos t x,
      (Osserman.Proofs.Hopf.sec6_hopf_proved stdSys sec6_std_system_proved.2 x).2, lem_8_1_sum_ha_proved K hK x,
      lem_8_1_sum_a_proved K hK c hc x, mul_zero, add_zero, mul_assoc (Real.sin t ^ 2), ← mul_assoc c⁻¹,
      inv_mul_cancel₀ hcne, one_mul]
    linear_combination (x ⬝ᵥ x) ^ 2 * Real.cos_sq_add_sin_sq t
  have hnc (t : ℝ) := (lem_8_1_not_const_proved K hK c t).2 _ (lem_8_1_not_const_proved K hK c t).1
    (fun x hx => by rw [hsum t x, hx, one_pow])
  have hcl (t : ℝ) : IsSymmCliffordSystem (lem81Fam K c t) := lem_8_1_clifford_t_proved K hK c t (hsum t) (hnc t)
  have hcont (i : Fin 9) : Continuous fun t => lem81Fam K c t i := by
    unfold lem81Fam
    fun_prop
  have hconst := (lem_8_1_trace_const_proved (lem81Fam K c) hcont hcl).2.2 Real.pi
  obtain ⟨h0, hpm⟩ := lem_8_1_Omega_zero_proved K c
  rw [(lem_8_1_Omega_pi_proved K c).2, h0, trace_neg] at hconst
  have hzero : (cliffProd stdSys).trace = 0 := by linarith
  rcases hpm with h | h <;> rw [h] at hzero <;> simp at hzero

/-- **Lemma 8.1** (lines 19-23): a skew `K` with `|π_{N(x)}Kx|² = c|x|²` is zero. -/
theorem lem_8_1_proved (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : Kᵀ = -K) (c : ℝ)
    (hc : ∀ x : Vec 16, x ≠ 0 → ∃ w, IsOrthProj (Nstd x) (K *ᵥ x) w ∧ w ⬝ᵥ w = c * (x ⬝ᵥ x)) : K = 0 := by
  have hzero : c = 0 := by
    rcases (lem_8_1_c_nonneg_proved K c hc).lt_or_eq with h | h
    · exact absurd h (lem_8_1_c_pos_proved K hK c hc)
    · exact h.symm
  exact (lem_8_1_c_zero_proved K hK c hzero hc).2

/-- **Lemma 8.1** (lines 23-24): an orthogonal skew map has no constant normalized projection lengths. -/
theorem lem_8_1_orthogonal_proved (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : Kᵀ = -K) (hKo : Kᵀ * K = 1) (cE cN : ℝ) :
    ¬ ∀ x : Vec 16, x ≠ 0 → (∃ w, IsOrthProj (Estd x) (K *ᵥ x) w ∧ w ⬝ᵥ w = cE * (x ⬝ᵥ x)) ∧
      ∃ w, IsOrthProj (Nstd x) (K *ᵥ x) w ∧ w ⬝ᵥ w = cN * (x ⬝ᵥ x) := by
  intro h
  have hK0 := lem_8_1_proved K hK cN fun x hx => (h x hx).2
  rw [hK0, mul_zero] at hKo
  exact zero_ne_one hKo

/-! ## The two reasons for `Ω(0) = ±I` (review a3 MUST-2) -/

/-- **Lemma 8.1, proof** (lines 46-47): "as nine is odd, `Ω(0)` commutes with every `H_i`" (any symmetric Clifford
system of nine matrices). -/
theorem cliffProd_nine_commutes_proved {n : ℕ} (H : Fin 9 → Matrix (Fin n) (Fin n) ℝ) (hH : IsSymmCliffordSystem H)
    (i : Fin 9) : cliffProd H * H i = H i * cliffProd H :=
  (cliff_comm_prod hH (by decide) i).symm

lemma std_word_mem (s : Finset (Fin 9)) :
    ((s.sort (· ≤ ·)).map stdSys).prod ∈ Algebra.adjoin ℝ (Set.range stdSys) :=
  Subalgebra.list_prod_mem _ fun a ha => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
    exact Algebra.subset_adjoin ⟨i, rfl⟩

lemma mem_of_span_symm {T : Set (Matrix (Fin 16) (Fin 16) ℝ)} {A : Subalgebra ℝ (Matrix (Fin 16) (Fin 16) ℝ)}
    (hT : T ⊆ A) (hspan : (Submodule.span ℝ T : Set (Matrix (Fin 16) (Fin 16) ℝ)) = {M | Mᵀ = M})
    {M : Matrix (Fin 16) (Fin 16) ℝ} (hM : Mᵀ = M) : M ∈ A := by
  have hmem : M ∈ (Submodule.span ℝ T : Set (Matrix (Fin 16) (Fin 16) ℝ)) := by
    rw [hspan]
    exact hM
  exact (Submodule.span_le (p := Subalgebra.toSubmodule A)).mpr hT hmem

/-- Every symmetric matrix is in the algebra generated by the `S_i` (Section 6: the 136 words of length 0, 1, 4 span
the symmetric matrices). -/
lemma symm_mem_adjoin {M : Matrix (Fin 16) (Fin 16) ℝ} (hM : Mᵀ = M) : M ∈ Algebra.adjoin ℝ (Set.range stdSys) := by
  have facts := Osserman.Proofs.CayleyProducts.sec6_basis_136_proved stdSys sec6_std_system_proved.2
  simp only at facts
  obtain ⟨-, -, -, -, hspan, -⟩ := facts
  refine mem_of_span_symm ?_ hspan hM
  rintro _ ⟨s, -, rfl⟩
  exact std_word_mem s

/-- Every matrix unit is in it: `E_ij = E_ii (E_ij + E_ji)` for `i ≠ j`, a product of two symmetric matrices. -/
lemma single_mem_adjoin (i j : Fin 16) : single i j (1 : ℝ) ∈ Algebra.adjoin ℝ (Set.range stdSys) := by
  by_cases hij : i = j
  · subst hij
    exact symm_mem_adjoin (transpose_single i i 1)
  · have hprod : single i i (1 : ℝ) * (single i j 1 + single j i 1) = single i j 1 := by
      rw [mul_add, single_mul_single_same, single_mul_single_of_ne (h := hij), mul_one, add_zero]
    rw [← hprod]
    exact Subalgebra.mul_mem _ (symm_mem_adjoin (transpose_single i i 1))
      (symm_mem_adjoin (by rw [transpose_add, transpose_single, transpose_single, add_comm]))

/-- **Lemma 8.1, proof** (lines 47-49): "the `H_i` generate all of `End(ℝ^16)`", and the consequence used: a matrix
commuting with every `S_i` is scalar. -/
theorem std_sys_generate_proved :
    Algebra.adjoin ℝ (Set.range stdSys) = ⊤ ∧
      ∀ M : Matrix (Fin 16) (Fin 16) ℝ, (∀ i, M * stdSys i = stdSys i * M) → ∃ r : ℝ, M = r • 1 := by
  have top : Algebra.adjoin ℝ (Set.range stdSys) = ⊤ := by
    refine Algebra.eq_top_iff.mpr fun M => ?_
    rw [matrix_eq_sum_single M]
    refine Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => ?_
    have hunit : single i j (M i j) = M i j • single i j (1 : ℝ) := by rw [smul_single, smul_eq_mul, mul_one]
    rw [hunit]
    exact Subalgebra.smul_mem _ (single_mem_adjoin i j) _
  refine ⟨top, fun M hM => ?_⟩
  have hle : Algebra.adjoin ℝ (Set.range stdSys) ≤ Subalgebra.centralizer ℝ {M} := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact hM i
  have hcomm (i j : Fin 16) : Commute (single i j (1 : ℝ)) M :=
    ((Subalgebra.mem_centralizer_iff ℝ).mp (hle (single_mem_adjoin i j)) M rfl).symm
  obtain ⟨r, hr⟩ := mem_range_scalar_iff_commute_single'.mpr hcomm
  exact ⟨r, by rw [← hr, scalar_apply, smul_one_eq_diagonal]⟩

end Osserman.Proofs.Lem81
