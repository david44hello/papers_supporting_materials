/-
Osserman/Proofs/Lemma71Blocks.lean — block-matrix steps of Lemma 7.1, paper 013, lines 716–722.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.Lemma71Coordinates
import Osserman.Proofs.Lemma71Algebra
import Osserman.Proofs.Lemma71Geometry

namespace Osserman.Proofs.Lemma71Blocks

open Osserman Matrix Osserman.Proofs.OctonionLinear Osserman.Proofs.OctonionFacts
open Osserman.Proofs.Lemma71Coordinates Osserman.Proofs.StdSystem
open Osserman.Proofs.Lemma71Geometry Osserman.Proofs.Lemma71Algebra

def leftIn : Vec 8 →ₗ[ℝ] Vec 16 where
  toFun := fun u => octPair u 0
  map_add' := by intro u v; rw [pair_add]; simp only [add_zero]
  map_smul' := by intro c u; rw [pair_smul]; simp only [smul_zero, RingHom.id_apply]

def rightIn : Vec 8 →ₗ[ℝ] Vec 16 where
  toFun := fun u => octPair 0 u
  map_add' := by intro u v; rw [pair_add]; simp only [add_zero]
  map_smul' := by intro c u; rw [pair_smul]; simp only [smul_zero, RingHom.id_apply]

def firstLinear : Vec 16 →ₗ[ℝ] Vec 8 where
  toFun := oct1
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

def secondLinear : Vec 16 →ₗ[ℝ] Vec 8 where
  toFun := oct2
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

theorem lem_7_1_a_diag_proved (K' : Matrix (Fin 16) (Fin 16) ℝ)
    (h0 : ∀ y ∈ cayLine 0, K' *ᵥ y ∈ cayLine 0)
    (hinf : ∀ y ∈ cayLineInf, K' *ᵥ y ∈ cayLineInf)
    (h1 : ∀ y ∈ cayLine oone, K' *ᵥ y ∈ cayLine oone) :
    ∃ D : Matrix (Fin 8) (Fin 8) ℝ, ∀ y : Vec 16,
      K' *ᵥ y = octPair (D *ᵥ oct1 y) (D *ᵥ oct2 y) := by
  let d := firstLinear.comp ((Matrix.toLin' K').comp leftIn)
  let D := LinearMap.toMatrix' d
  have d_action (u : Vec 8) : D *ᵥ u = oct1 (K' *ᵥ octPair u 0) := by
    exact LinearMap.toMatrix'_mulVec d u
  have left_zero (u : Vec 8) : oct2 (K' *ᵥ octPair u 0) = 0 := by
    have member : octPair u 0 ∈ cayLine 0 := by simp [cayLine, zero_omul]
    have image := h0 (octPair u 0) member
    simpa only [cayLine, Set.mem_ofPred_eq, zero_omul] using image
  have right_zero (u : Vec 8) : oct1 (K' *ᵥ octPair 0 u) = 0 :=
    hinf (octPair 0 u) (by simp [cayLineInf])
  have right_action (u : Vec 8) : oct2 (K' *ᵥ octPair 0 u) = D *ᵥ u := by
    have member : octPair u u ∈ cayLine oone := by simp [cayLine, one_omul]
    have image := h1 (octPair u u) member
    change oct2 (K' *ᵥ octPair u u) = omul oone (oct1 (K' *ᵥ octPair u u)) at image
    have split : octPair u u = octPair u 0 + octPair 0 u := by rw [pair_add]; simp only [add_zero, zero_add]
    rw [split, Matrix.mulVec_add, first_add, second_add, left_zero, right_zero,
      zero_add, add_zero, one_omul, ← d_action] at image
    exact image
  refine ⟨D, ?_⟩
  intro y
  have split : y = octPair (oct1 y) 0 + octPair 0 (oct2 y) := by
    rw [pair_add, add_zero, zero_add, pair_parts]
  have first : oct1 (K' *ᵥ y) = D *ᵥ oct1 y := by
    conv_lhs => rw [split]
    rw [Matrix.mulVec_add, first_add, right_zero, add_zero, d_action]
  have second : oct2 (K' *ᵥ y) = D *ᵥ oct2 y := by
    conv_lhs => rw [split]
    rw [Matrix.mulVec_add, second_add, left_zero, zero_add, right_action]
  rw [← pair_parts (K' *ᵥ y), first, second]

theorem lem_7_1_a_scalar_proved (K : Matrix (Fin 16) (Fin 16) ℝ)
    (D : Matrix (Fin 8) (Fin 8) ℝ) (r : ℝ)
    (hdiag : ∀ y : Vec 16, (conjChange * K * conjChange) *ᵥ y = octPair (D *ᵥ oct1 y) (D *ᵥ oct2 y))
    (hD : ∀ u : Vec 8, D *ᵥ u = omul u (r • oone)) (hskew : Kᵀ = -K) :
    K = r • (1 : Matrix (Fin 16) (Fin 16) ℝ) ∧ r = 0 := by
  have scalar_new : conjChange * K * conjChange = r • (1 : Matrix (Fin 16) (Fin 16) ℝ) := by
    rw [Matrix.ext_iff_mulVec]
    intro y
    rw [hdiag, hD, hD, omul_smul_right, omul_smul_right, omul_one, omul_one,
      ← pair_smul, pair_parts, Matrix.smul_mulVec, Matrix.one_mulVec]
  have restore : conjChange * (conjChange * K * conjChange) * conjChange = K := by
    calc
      _ = (conjChange * conjChange) * K * (conjChange * conjChange) := by noncomm_ring
      _ = K := by rw [conj_square]; simp
  have scalar : K = r • (1 : Matrix (Fin 16) (Fin 16) ℝ) := by
    rw [scalar_new, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, conj_square] at restore
    exact restore.symm
  refine ⟨scalar, ?_⟩
  have entry := congrArg (fun M : Matrix (Fin 16) (Fin 16) ℝ => M 0 0) hskew
  simp [scalar] at entry
  linarith

lemma transformed_N (K : Matrix (Fin 16) (Fin 16) ℝ)
    (hK : ∀ x : Vec 16, x ≠ 0 → K *ᵥ x ∈ Nstd x) (y : Vec 16) (hy : y ≠ 0) :
    conjChange *ᵥ ((conjChange * K * conjChange) *ᵥ y) ∈ Nstd (conjChange *ᵥ y) := by
  have nonzero : conjChange *ᵥ y ≠ 0 := by
    intro equal
    apply hy
    apply Osserman.Proofs.Lemma71Coordinates.conj_injective
    simpa only [Matrix.mulVec_zero] using equal
  simp only [← Matrix.mulVec_mulVec, conj_invol]
  exact hK _ nonzero

lemma pair_nonzero_left (u v : Vec 8) (hu : u ≠ 0) : octPair u v ≠ 0 := by
  intro equal
  apply hu
  exact (first_pair u v).symm.trans ((congrArg oct1 equal).trans (show oct1 (0 : Vec 16) = 0 by rfl))

lemma pair_zero : octPair (0 : Vec 8) 0 = 0 := by
  exact Osserman.Proofs.OctonionNucleus.zero_of_parts _ (first_pair _ _) (second_pair _ _)

theorem lem_7_1_b_offdiag_proved (K : Matrix (Fin 16) (Fin 16) ℝ)
    (hK : ∀ x : Vec 16, x ≠ 0 → K *ᵥ x ∈ Nstd x) :
    ∃ B C : Matrix (Fin 8) (Fin 8) ℝ,
      ∀ y : Vec 16, (conjChange * K * conjChange) *ᵥ y = octPair (B *ᵥ oct2 y) (C *ᵥ oct1 y) := by
  let K' := conjChange * K * conjChange
  let bmap := firstLinear.comp ((Matrix.toLin' K').comp rightIn)
  let cmap := secondLinear.comp ((Matrix.toLin' K').comp leftIn)
  let B := LinearMap.toMatrix' bmap
  let C := LinearMap.toMatrix' cmap
  have b_action (u : Vec 8) : B *ᵥ u = oct1 (K' *ᵥ octPair 0 u) :=
    LinearMap.toMatrix'_mulVec bmap u
  have c_action (u : Vec 8) : C *ᵥ u = oct2 (K' *ᵥ octPair u 0) :=
    LinearMap.toMatrix'_mulVec cmap u
  have left_zero (u : Vec 8) : oct1 (K' *ᵥ octPair u 0) = 0 := by
    by_cases hu : u = 0
    · subst u; rw [pair_zero, Matrix.mulVec_zero]; rfl
    · have line := lem_7_1_N_line_proved.1 0 (octPair u 0) (pair_nonzero_left u 0 hu)
        (by simp [cayLine, zero_omul])
      have image := (Set.ext_iff.mp line (K' *ᵥ octPair u 0)).mp
        (transformed_N K hK _ (pair_nonzero_left u 0 hu))
      change oct1 (K' *ᵥ octPair u 0) = -omul (oconj 0) (oct2 (K' *ᵥ octPair u 0)) at image
      have conj_zero : oconj (0 : Vec 8) = 0 := by
        simpa only [zero_smul] using oconj_smul (0 : Vec 8) (0 : ℝ)
      simpa only [conj_zero, zero_omul, neg_zero] using image
  have right_zero (u : Vec 8) : oct2 (K' *ᵥ octPair 0 u) = 0 := by
    by_cases hu : u = 0
    · subst u; rw [pair_zero, Matrix.mulVec_zero]; rfl
    · have nonzero : octPair 0 u ≠ 0 := by
        intro equal
        apply hu
        exact (second_pair (0 : Vec 8) u).symm.trans
          ((congrArg oct2 equal).trans (show oct2 (0 : Vec 16) = 0 by rfl))
      have line := lem_7_1_N_line_proved.2 (octPair 0 u) nonzero (by simp [cayLineInf])
      have image := (Set.ext_iff.mp line (K' *ᵥ octPair 0 u)).mp (transformed_N K hK _ nonzero)
      simpa only [cayLine, Set.mem_ofPred_eq, zero_omul] using image
  refine ⟨B, C, ?_⟩
  intro y
  have split : y = octPair (oct1 y) 0 + octPair 0 (oct2 y) := by
    rw [pair_add, add_zero, zero_add, pair_parts]
  have first : oct1 (K' *ᵥ y) = B *ᵥ oct2 y := by
    conv_lhs => rw [split]
    rw [Matrix.mulVec_add, first_add, left_zero, zero_add, b_action]
  have second : oct2 (K' *ᵥ y) = C *ᵥ oct1 y := by
    conv_lhs => rw [split]
    rw [Matrix.mulVec_add, second_add, right_zero, add_zero, c_action]
  change K' *ᵥ y = _
  rw [← pair_parts (K' *ᵥ y), first, second]

theorem lem_7_1_b_graph_proved (K : Matrix (Fin 16) (Fin 16) ℝ)
    (hK : ∀ x : Vec 16, x ≠ 0 → K *ᵥ x ∈ Nstd x) (B C : Matrix (Fin 8) (Fin 8) ℝ)
    (hBC : ∀ y : Vec 16, (conjChange * K * conjChange) *ᵥ y = octPair (B *ᵥ oct2 y) (C *ᵥ oct1 y)) :
    ∀ ω u : Vec 8, B *ᵥ omul ω u = -omul (oconj ω) (C *ᵥ u) := by
  intro ω u
  by_cases hu : u = 0
  · subst u; simp only [omul_zero, Matrix.mulVec_zero, neg_zero]
  · let y := octPair u (omul ω u)
    have nonzero : y ≠ 0 := pair_nonzero_left u _ hu
    have member : y ∈ cayLine ω := by simp [y, cayLine]
    have line := lem_7_1_N_line_proved.1 ω y nonzero member
    have image := (Set.ext_iff.mp line ((conjChange * K * conjChange) *ᵥ y)).mp
      (transformed_N K hK y nonzero)
    change oct1 ((conjChange * K * conjChange) *ᵥ y) =
      -omul (oconj ω) (oct2 ((conjChange * K * conjChange) *ᵥ y)) at image
    simpa only [hBC, y, first_pair, second_pair] using image

theorem lem_7_1_a_proved (K : Matrix (Fin 16) (Fin 16) ℝ)
    (hK : ∀ x : Vec 16, x ≠ 0 → K *ᵥ x ∈ Estd x) : K = 0 := by
  have lines := lem_7_1_a_lines_proved K hK
  obtain ⟨D, diagonal⟩ := lem_7_1_a_diag_proved (conjChange * K * conjChange)
    (lines.1 0) lines.2 (lines.1 oone)
  have left_linear : ∀ ω u : Vec 8, D *ᵥ omul ω u = omul ω (D *ᵥ u) :=
    lem_7_1_a_left_linear_proved D (fun ω y hy => by rw [← diagonal]; exact lines.1 ω y hy)
  have right_mult := lem_7_1_a_right_mult_proved D left_linear
  obtain ⟨r, real_scalar⟩ := (Osserman.Proofs.OctonionNucleus.oct_right_nucleus_proved (D *ᵥ oone)).mp right_mult.2
  have scalar := lem_7_1_a_scalar_proved K D r diagonal
    (fun u => by rw [right_mult.1, real_scalar]) (lem_7_1_a_skew_proved K hK).2
  simpa only [scalar.2, zero_smul] using scalar.1

theorem lem_7_1_b_proved (K : Matrix (Fin 16) (Fin 16) ℝ)
    (hK : ∀ x : Vec 16, x ≠ 0 → K *ᵥ x ∈ Nstd x) : K = 0 := by
  obtain ⟨B, C, offdiag⟩ := lem_7_1_b_offdiag_proved K hK
  have graph := lem_7_1_b_graph_proved K hK B C offdiag
  have gamma := lem_7_1_b_gamma_proved B C graph
  have c_linear (ω u : Vec 8) : C *ᵥ omul ω u = omul (oconj ω) (C *ᵥ u) := by
    have equal := graph ω u
    rw [gamma.1, Matrix.neg_mulVec] at equal
    exact neg_injective equal
  have relation := lem_7_1_b_rel_proved C (C *ᵥ oone) c_linear gamma.2
  have zero_gamma := lem_7_1_b_gamma_zero_proved (C *ᵥ oone) relation
  have zero_C : C = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro u
    rw [gamma.2, zero_gamma, omul_zero, Matrix.zero_mulVec]
  have zero_B : B = 0 := by rw [gamma.1, zero_C, neg_zero]
  have zero_new : conjChange * K * conjChange = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro y
    rw [offdiag, zero_B, zero_C, Matrix.zero_mulVec, Matrix.zero_mulVec,
      pair_zero, Matrix.zero_mulVec]
  calc
    K = (conjChange * conjChange) * K * (conjChange * conjChange) := by rw [conj_square]; simp
    _ = conjChange * (conjChange * K * conjChange) * conjChange := by noncomm_ring
    _ = 0 := by rw [zero_new]; simp

end Osserman.Proofs.Lemma71Blocks
