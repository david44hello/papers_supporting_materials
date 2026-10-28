/-
Osserman/Proofs/Curv.lean — proofs of six statements of paper 013 (§1 l. 175-178, §2 l. 345-363) about algebraic
curvature tensors: the Jacobi family of `R_1`, `R_1` is a curvature tensor, polarization of a quadratic family,
Jacobi-family reconstruction, and "the Jacobi family determines the tensor".
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.TwoRoot

namespace Osserman.Proofs.Curv

open Osserman Matrix

variable {n : ℕ}

/-! ### Generic helpers -/

/-- `J_x y = R(y,x)x`, read through the matrix `jacobi R x`. -/
@[simp] lemma jacobi_mulVec (R : CurvTensor n) (x y : Vec n) : R.jacobi x *ᵥ y = R.op y x x := by
  rw [CurvTensor.jacobi, LinearMap.toMatrix'_mulVec]
  rfl

/-- A symmetric matrix moves across the dot product. -/
lemma symm_dot {S : Matrix (Fin n) (Fin n) ℝ} (hS : Sᵀ = S) (x y : Vec n) :
    (S *ᵥ x) ⬝ᵥ y = (S *ᵥ y) ⬝ᵥ x := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hS]

/-- A trilinear function with the three curvature identities is (the operator of) a `CurvTensor`. -/
lemma exists_curv (f : Vec n → Vec n → Vec n → Vec n)
    (h1 : ∀ u u' v w, f (u + u') v w = f u v w + f u' v w) (h1s : ∀ (c : ℝ) u v w, f (c • u) v w = c • f u v w)
    (h2 : ∀ u v v' w, f u (v + v') w = f u v w + f u v' w) (h2s : ∀ (c : ℝ) u v w, f u (c • v) w = c • f u v w)
    (h3 : ∀ u v w w', f u v (w + w') = f u v w + f u v w') (h3s : ∀ (c : ℝ) u v w, f u v (c • w) = c • f u v w)
    (ha : ∀ u v w, f u v w = -f v u w) (hsk : ∀ u v w z, f u v w ⬝ᵥ z = -(f u v z ⬝ᵥ w))
    (hb : ∀ u v w, f u v w + f v w u + f w u v = 0) :
    ∃ R : CurvTensor n, ∀ u v w, R.op u v w = f u v w :=
  ⟨⟨mkTri f h1 h1s h2 h2s h3 h3s, ha, hsk, hb⟩, fun _ _ _ => rfl⟩

/-! ### (1), (2): `R_1` -/

theorem sec1_jacobi_R1_proved (n : ℕ) (x y : Vec n) : R1fun y x x = Pi x *ᵥ y := by
  ext i
  simp only [R1fun, Osserman.Pi, sub_mulVec, smul_mulVec, one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  simp only [mulVec, vecMulVec, dotProduct, of_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem sec1_R1_curv_proved (n : ℕ) : ∃ R : CurvTensor n, ∀ u v w, R.op u v w = R1fun u v w := by
  refine exists_curv R1fun ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals intros
  all_goals simp only [R1fun, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, sub_dotProduct,
    smul_eq_mul]
  · module
  · module
  · module
  · module
  · module
  · module
  · module
  · ring
  · rename_i u v w
    rw [dotProduct_comm w u, dotProduct_comm v u, dotProduct_comm w v]
    module

/-! ### The symmetric bilinear map `𝓑` of a quadratic family -/

/-- The bilinear map `(u, v) ↦ ∑_{a,b} u_a v_b M_{ab}`. -/
noncomputable def bil (M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Vec n →ₗ[ℝ] Vec n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.mk₂ ℝ (fun u v => ∑ a, ∑ b, (u a * v b) • M a b)
    (fun u u' v => by simp only [Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib])
    (fun c u v => by simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, mul_assoc])
    (fun u v v' => by simp only [Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib])
    (fun c u v => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by congr 1; ring)

lemma bil_apply (M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ) (u v : Vec n) :
    bil M u v = ∑ a, ∑ b, (u a * v b) • M a b := rfl

/-- A quadratic family `A` has a symmetric bilinear `𝓑` with `Bpol A = 𝓑` and `A x = 𝓑(x,x)`. -/
lemma exists_symm_bilin {A : Vec n → Matrix (Fin n) (Fin n) ℝ} (hq : IsQuadFamily A) :
    ∃ Bl : Vec n →ₗ[ℝ] Vec n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ,
      (∀ u v, Bpol A u v = Bl u v) ∧ (∀ u v, Bl u v = Bl v u) ∧ ∀ x, A x = Bl x x := by
  obtain ⟨M, hM⟩ := hq
  have hA : ∀ x, A x = bil M x x := fun x => (hM x).trans (bil_apply M x x).symm
  refine ⟨(1 / 2 : ℝ) • (bil M + (bil M).flip), fun u v => ?_, fun u v => ?_, fun x => ?_⟩
  · simp only [Bpol, hA, map_add, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply]
    module
  · simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply]
    rw [add_comm]
  · simp only [hA, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply]
    module

section Bilin

variable {Bl : Vec n →ₗ[ℝ] Vec n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ}

/-- From `𝓑(x,x)x = 0`: `𝓑(x,y)x = -𝓑(x,x)y/2` (compare `x ± y`). -/
lemma bl_key (hBs : ∀ u v, Bl u v = Bl v u) (hk : ∀ x, Bl x x *ᵥ x = 0) (x y : Vec n) :
    Bl x y *ᵥ x = -(1 / 2 : ℝ) • (Bl x x *ᵥ y) := by
  have h1 := hk (x + y)
  have h2 := hk (x + (-1 : ℝ) • y)
  have h3 := hk x
  have h4 := hk y
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, add_mulVec, mulVec_add, smul_mulVec,
    mulVec_smul, hBs y x] at h1 h2
  ext i
  have e1 := congrFun h1 i
  have e2 := congrFun h2 i
  have e3 := congrFun h3 i
  have e4 := congrFun h4 i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at e1 e2 e3 e4 ⊢
  linarith

/-- `⟨𝓑(x,x)y, y⟩ = ⟨𝓑(y,y)x, x⟩`. -/
lemma bl_dot (hBs : ∀ u v, Bl u v = Bl v u) (hT : ∀ u v, (Bl u v)ᵀ = Bl u v) (hk : ∀ x, Bl x x *ᵥ x = 0)
    (x y : Vec n) : (Bl x x *ᵥ y) ⬝ᵥ y = (Bl y y *ᵥ x) ⬝ᵥ x := by
  have s := symm_dot (hT x y) x y
  rw [bl_key hBs hk x y, hBs x y, bl_key hBs hk y x] at s
  simp only [smul_dotProduct, smul_eq_mul] at s
  linarith

/-- Pair symmetry `⟨𝓑(a,b)c, d⟩ = ⟨𝓑(c,d)a, b⟩` (polarize `bl_dot` twice). -/
lemma bl_pair (hBs : ∀ u v, Bl u v = Bl v u) (hT : ∀ u v, (Bl u v)ᵀ = Bl u v) (hk : ∀ x, Bl x x *ᵥ x = 0)
    (a b c d : Vec n) : (Bl a b *ᵥ c) ⬝ᵥ d = (Bl c d *ᵥ a) ⬝ᵥ b := by
  have hsym : ∀ p q r s, (Bl p q *ᵥ r) ⬝ᵥ s = (Bl p q *ᵥ s) ⬝ᵥ r := fun p q r s => symm_dot (hT p q) r s
  have step1 : ∀ a b y, (Bl a b *ᵥ y) ⬝ᵥ y = (Bl y y *ᵥ a) ⬝ᵥ b := by
    intro a b y
    have h := bl_dot hBs hT hk (a + b) y
    simp only [map_add, LinearMap.add_apply, add_mulVec, mulVec_add, add_dotProduct, dotProduct_add,
      hBs b a] at h
    have := bl_dot hBs hT hk a y
    have := bl_dot hBs hT hk b y
    have := hsym y y b a
    linarith
  have h := step1 a b (c + d)
  simp only [map_add, LinearMap.add_apply, add_mulVec, mulVec_add, add_dotProduct, dotProduct_add, hBs d c] at h
  have := step1 a b c
  have := step1 a b d
  have := hsym a b d c
  linarith

end Bilin

/-! ### (3), (4): polarization and reconstruction -/

theorem sec2_polarization_proved {n : ℕ} (A : Vec n → Matrix (Fin n) (Fin n) ℝ) (hq : IsQuadFamily A)
    (hs : ∀ x, (A x)ᵀ = A x) (hk : ∀ x, A x *ᵥ x = 0) :
    (∀ x y, Bpol A x y *ᵥ x = -(1 / 2 : ℝ) • (A x *ᵥ y)) ∧ ∀ x y, (A x *ᵥ y) ⬝ᵥ y = (A y *ᵥ x) ⬝ᵥ x := by
  obtain ⟨Bl, hB, hBs, hA⟩ := exists_symm_bilin hq
  have hk' : ∀ x, Bl x x *ᵥ x = 0 := fun x => by rw [← hA x]; exact hk x
  have hT : ∀ u v, (Bl u v)ᵀ = Bl u v := fun u v => by
    rw [← hB]
    simp only [Bpol, transpose_smul, transpose_sub, hs]
  refine ⟨fun x y => ?_, fun x y => ?_⟩
  · rw [hB, hA x]
    exact bl_key hBs hk' x y
  · rw [hA x, hA y]
    exact bl_dot hBs hT hk' x y

theorem sec2_reconstruct_proved {n : ℕ} (A : Vec n → Matrix (Fin n) (Fin n) ℝ) (hq : IsQuadFamily A)
    (hs : ∀ x, (A x)ᵀ = A x) (hk : ∀ x, A x *ᵥ x = 0) :
    ∃ R : CurvTensor n, (∀ u v w, R.op u v w = RAfun A u v w) ∧ ∀ x, R.jacobi x = A x := by
  obtain ⟨Bl, hB, hBs, hA⟩ := exists_symm_bilin hq
  have hk' : ∀ x, Bl x x *ᵥ x = 0 := fun x => by rw [← hA x]; exact hk x
  have hT : ∀ u v, (Bl u v)ᵀ = Bl u v := fun u v => by
    rw [← hB]
    simp only [Bpol, transpose_smul, transpose_sub, hs]
  have hRA : ∀ u v w, RAfun A u v w = (2 / 3 : ℝ) • (Bl v w *ᵥ u - Bl u w *ᵥ v) := fun u v w => by
    simp only [RAfun, hB]
  obtain ⟨R, hR⟩ := exists_curv (RAfun A)
    (fun u u' v w => by simp only [hRA, map_add, LinearMap.add_apply, add_mulVec, mulVec_add]; module)
    (fun c u v w => by simp only [hRA, map_smul, LinearMap.smul_apply, smul_mulVec, mulVec_smul]; module)
    (fun u v v' w => by simp only [hRA, map_add, LinearMap.add_apply, add_mulVec, mulVec_add]; module)
    (fun c u v w => by simp only [hRA, map_smul, LinearMap.smul_apply, smul_mulVec, mulVec_smul]; module)
    (fun u v w w' => by simp only [hRA, map_add, add_mulVec]; module)
    (fun c u v w => by simp only [hRA, map_smul, smul_mulVec]; module)
    (fun u v w => by simp only [hRA]; module)
    (fun u v w z => by
      simp only [hRA, smul_dotProduct, sub_dotProduct, smul_eq_mul]
      linarith [bl_pair hBs hT hk' v w u z, bl_pair hBs hT hk' v z u w])
    (fun u v w => by simp only [hRA, hBs w u, hBs v u, hBs w v]; module)
  refine ⟨R, hR, fun x => Matrix.ext_iff_mulVec.2 fun y => ?_⟩
  rw [jacobi_mulVec, hR, hRA, hBs y x, bl_key hBs hk' x y, hA x]
  module

/-! ### (5), (6): the Jacobi family determines the tensor -/

theorem sec2_determines_proved {n : ℕ} (R : CurvTensor n) :
    (∀ u v w, Bpol R.jacobi v w *ᵥ u = (1 / 2 : ℝ) • (R.op u v w + R.op u w v)) ∧
      ∀ u v w, R.op u v w = RAfun R.jacobi u v w := by
  have hB : ∀ u v w, Bpol R.jacobi v w *ᵥ u = (1 / 2 : ℝ) • (R.op u v w + R.op u w v) := by
    intro u v w
    simp only [Bpol, smul_mulVec, sub_mulVec, jacobi_mulVec, map_add, LinearMap.add_apply]
    module
  refine ⟨hB, fun u v w => ?_⟩
  rw [RAfun, hB, hB]
  ext i
  have e1 := congrFun (R.antisymm v u w) i
  have e2 := congrFun (R.antisymm w u v) i
  have e3 := congrFun (R.bianchi u v w) i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul] at e1 e2 e3 ⊢
  linarith

theorem sec2_jacobi_determines_proved {n : ℕ} (R R' : CurvTensor n) (h : ∀ x, R.jacobi x = R'.jacobi x) :
    ∀ u v w, R.op u v w = R'.op u v w := by
  intro u v w
  have hJ : R.jacobi = R'.jacobi := funext h
  rw [(sec2_determines_proved R).2 u v w, (sec2_determines_proved R').2 u v w, hJ]

end Osserman.Proofs.Curv
