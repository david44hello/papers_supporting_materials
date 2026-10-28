/-
Osserman/Proofs/Lemma71Geometry.lean — Cayley distributions of Section 7, paper 013, lines 691–694.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.CayleySectional
import Osserman.Proofs.Spectral
import Osserman.Defs.ThreeRoot
import Osserman.Proofs.Lemma71Coordinates
import Osserman.Proofs.OctonionNucleus

namespace Osserman.Proofs.Lemma71Geometry

open Osserman Matrix Osserman.Proofs.Curv Osserman.Proofs.Threshold
open Osserman.Proofs.StdSystem Osserman.Proofs.CayleyEigenspaces
open Osserman.Proofs.Lemma71Coordinates Osserman.Proofs.OctonionLinear
open Osserman.Proofs.OctonionFacts

lemma cayley_normalized : ∃ R : CurvTensor 16, TwoRootHyp R 1 3 ∧ Amat R 1 3 = Acay stdSys := by
  obtain ⟨R, hR, roots⟩ := Osserman.Proofs.CayleySectional.thm_C_hyp_nonvacuous_proved
  refine ⟨R, roots, ?_⟩
  funext x
  have jacobi : R.jacobi x = Pi x + (3 : ℝ) • Acay stdSys x := by
    rw [Matrix.ext_iff_mulVec]
    intro y
    rw [jacobi_mulVec, hR, Osserman.Proofs.CayleyJacobi.RCay_jacobi]
  rw [Amat, jacobi]
  module

theorem sec7_cayley_A_props_proved :
    IsQuadFamily (Acay stdSys) ∧ (∀ x, (Acay stdSys x)ᵀ = Acay stdSys x) ∧
      ∀ x, Acay stdSys x *ᵥ x = 0 ∧ Acay stdSys x * Acay stdSys x = (x ⬝ᵥ x) • Acay stdSys x ∧
        (Acay stdSys x).trace = 7 * (x ⬝ᵥ x) := by
  obtain ⟨R, roots, equal⟩ := cayley_normalized
  have properties := Osserman.Proofs.Spectral.sec2_A_properties_proved R 1 3 roots
  rwa [equal] at properties

lemma self_mem_L (x : Vec 16) : x ∈ Lstd x :=
  Submodule.mem_sup_left (Submodule.mem_span_singleton_self x)

theorem sec7_L_eigenspace_proved (x : Vec 16) (hx : x ≠ 0) :
    let w : Fin 9 → ℝ := fun i => (x ⬝ᵥ (stdSys i *ᵥ x)) / (x ⬝ᵥ x)
    Lstd x = LinearMap.range (Matrix.toLin' (Acay stdSys x + vecMulVec x x)) ∧
      Lstd x = Module.End.eigenspace (Matrix.toLin' (∑ i, w i • stdSys i)) 1 ∧
      Module.finrank ℝ ↥(Lstd x) = 8 ∧ x ∈ Lstd x := by
  let q := x ⬝ᵥ x
  let w : Fin 9 → ℝ := fun i => (x ⬝ᵥ (stdSys i *ᵥ x)) / q
  let Sw := ∑ i, w i • stdSys i
  let Q := Acay stdSys x + vecMulVec x x
  have qne : q ≠ 0 := mt dotProduct_self_eq_zero.mp hx
  obtain ⟨R, roots, am⟩ := cayley_normalized
  have amx : Amat R 1 3 x = Acay stdSys x := congrFun am x
  obtain ⟨dimension, Pr, symmetric, square, image, scale⟩ :=
    (Osserman.Proofs.Spectral.sec2_Q_properties_proved R 1 3 roots).2 x hx
  have image' : LinearMap.range (Matrix.toLin' Pr) = Lstd x := by
    simpa only [Lsub, Lstd, am] using image
  have scale' : Q = q • Pr := by simpa only [Qmat, am] using scale
  have dimension' : Module.finrank ℝ ↥(Lstd x) = 8 := by
    have subeq : Lsub R 1 3 x = Lstd x := by unfold Lsub Lstd; rw [amx]
    rw [subeq] at dimension
    exact dimension
  have rangeQ : LinearMap.range (Matrix.toLin' Q) = Lstd x := by
    rw [← image']
    ext y
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨q • z, ?_⟩
      change Pr *ᵥ (q • z) = y
      change Q *ᵥ z = y at hz
      simpa only [scale', Matrix.smul_mulVec, Matrix.mulVec_smul] using hz
    · rintro ⟨z, hz⟩
      refine ⟨q⁻¹ • z, ?_⟩
      change Q *ᵥ (q⁻¹ • z) = y
      change Pr *ᵥ z = y at hz
      rw [scale', Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ qne, one_smul, hz]
  have fixes_iff (y : Vec 16) : y ∈ Lstd x ↔ Q *ᵥ y = q • y := by
    rw [← image']
    constructor
    · rintro ⟨z, rfl⟩
      change Q *ᵥ (Pr *ᵥ z) = q • (Pr *ᵥ z)
      rw [scale', Matrix.smul_mulVec, Matrix.mulVec_mulVec, square]
    · intro h
      refine ⟨y, ?_⟩
      change Pr *ᵥ y = y
      rw [scale', Matrix.smul_mulVec] at h
      exact (smul_right_injective _ qne) h
  have swfacts := sec6_Sw_proved stdSys sec6_std_system_proved.2 x hx
  have qformula : Q = (q / 2) • (1 + Sw) := by
    calc
      Q = (1 / 2 : ℝ) • (q • (1 : Matrix (Fin 16) (Fin 16) ℝ) +
        ∑ i, (x ⬝ᵥ (stdSys i *ᵥ x)) • stdSys i) := by unfold Q; rw [Acay]; module
      _ = _ := swfacts.2.2.2.2.2.2.2.2.2.2
  have eigenspace : Lstd x = Module.End.eigenspace (Matrix.toLin' Sw) 1 := by
    ext y
    rw [fixes_iff, Module.End.mem_eigenspace_iff]
    change Q *ᵥ y = q • y ↔ Sw *ᵥ y = (1 : ℝ) • y
    rw [qformula, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, one_smul]
    constructor
    · intro equal
      ext i
      have entry := congrFun equal i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at entry
      have product : q * ((Sw *ᵥ y) i - y i) = 0 := by nlinarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_left qne)
    · intro equal
      rw [equal]
      module
  exact ⟨rangeQ.symm, eigenspace, dimension', self_mem_L x⟩

lemma negative_space (x : Vec 16) (hx : x ≠ 0) :
    let w : Fin 9 → ℝ := fun i => (x ⬝ᵥ (stdSys i *ᵥ x)) / (x ⬝ᵥ x)
    Nstd x = Module.End.eigenspace (Matrix.toLin' (∑ i, w i • stdSys i)) (-1) := by
  let w : Fin 9 → ℝ := fun i => (x ⬝ᵥ (stdSys i *ᵥ x)) / (x ⬝ᵥ x)
  let Sw := ∑ i, w i • stdSys i
  have leigen := (sec7_L_eigenspace_proved x hx).2.1
  change Lstd x = Module.End.eigenspace (Matrix.toLin' Sw) 1 at leigen
  have facts := sec6_Sw_proved stdSys sec6_std_system_proved.2 x hx
  have square : Sw * Sw = 1 := facts.2.2.1
  have symmetric : Sw.IsSymm := facts.2.2.2.1
  change Nstd x = Module.End.eigenspace (Matrix.toLin' Sw) (-1)
  ext y
  constructor
  · intro hy
    change ∀ z ∈ Lstd x, z ⬝ᵥ y = 0 at hy
    let p := y + Sw *ᵥ y
    have fixes : Sw *ᵥ p = p := by
      dsimp only [p]
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, square, Matrix.one_mulVec]
      module
    have member : p ∈ Lstd x := by
      rw [leigen]
      apply Module.End.mem_eigenspace_iff.mpr
      change Sw *ᵥ p = (1 : ℝ) • p
      rw [fixes, one_smul]
    have orthogonal := hy p member
    have moved := symmetric.dotProduct_mulVec_comm (x := p) (y := y)
    rw [fixes, dotProduct_comm y p, orthogonal] at moved
    have pzero : p = 0 := dotProduct_self_eq_zero.mp (by
      calc
        p ⬝ᵥ p = p ⬝ᵥ y + p ⬝ᵥ (Sw *ᵥ y) := dotProduct_add _ _ _
        _ = 0 := by rw [orthogonal, moved, add_zero])
    apply Module.End.mem_eigenspace_iff.mpr
    change Sw *ᵥ y = (-1 : ℝ) • y
    rw [neg_one_smul]
    exact eq_neg_of_add_eq_zero_right pzero
  · intro hy
    have eigen : Sw *ᵥ y = -y := by
      simpa only [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, neg_one_smul] using hy
    change ∀ z ∈ Lstd x, z ⬝ᵥ y = 0
    intro z hz
    rw [leigen] at hz
    have fixes : Sw *ᵥ z = z := by
      simpa only [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, one_smul] using hz
    have moved := symmetric.dotProduct_mulVec_comm (x := z) (y := y)
    rw [fixes, eigen, dotProduct_neg, dotProduct_comm y z] at moved
    linarith

theorem sec7_EN_dims_proved (x : Vec 16) (hx : x ≠ 0) :
    Module.finrank ℝ ↥(Estd x) = 7 ∧ Module.finrank ℝ ↥(Nstd x) = 8 := by
  have dimensions := sec7_L_eigenspace_proved x hx
  let f : Lstd x →ₗ[ℝ] ℝ := (dotProductBilin ℝ ℝ x).comp (Lstd x).subtype
  have nonzero : f ≠ 0 := by
    intro equal
    have evaluated := congrArg (fun g : Lstd x →ₗ[ℝ] ℝ => g ⟨x, self_mem_L x⟩) equal
    change x ⬝ᵥ x = 0 at evaluated
    exact hx (dotProduct_self_eq_zero.mp evaluated)
  have rank := Module.Dual.finrank_ker_add_one_of_ne_zero nonzero
  let equivalence : LinearMap.ker f ≃ₗ[ℝ] ↥(Estd x) :=
    { toFun := fun y => ⟨y.1.1, ⟨y.1.2, y.2⟩⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have same := equivalence.finrank_eq
  have ldim : Module.finrank ℝ ↥(Lstd x) = 8 := dimensions.2.2.1
  refine ⟨by omega, ?_⟩
  rw [negative_space x hx]
  exact (sec6_Sw_proved stdSys sec6_std_system_proved.2 x hx).2.2.2.2.2.1

lemma L_is_line (y : Vec 16) (hy : y ≠ 0) :
    (∃ ω : Vec 8, {z : Vec 16 | conjChange *ᵥ z ∈ Lstd (conjChange *ᵥ y)} = cayLine ω) ∨
      {z : Vec 16 | conjChange *ᵥ z ∈ Lstd (conjChange *ᵥ y)} = cayLineInf := by
  let x := conjChange *ᵥ y
  have hx : x ≠ 0 := by
    intro equal
    apply hy
    apply Osserman.Proofs.Lemma71Coordinates.conj_injective
    simpa only [Matrix.mulVec_zero] using equal
  let q := x ⬝ᵥ x
  let w : Fin 9 → ℝ := fun i => (x ⬝ᵥ (stdSys i *ᵥ x)) / q
  let a : Vec 8 := fun k => w k.succ
  have qne : q ≠ 0 := mt dotProduct_self_eq_zero.mp hx
  have squares : ∑ i : Fin 9, w i ^ 2 = 1 := by
    dsimp only [w]
    simp only [div_pow, ← Finset.sum_div]
    change (∑ i, hvec stdSys x i ^ 2) / q ^ 2 = 1
    rw [system_norm_identity stdSys sec6_std_system_proved.2]
    exact div_self (pow_ne_zero 2 qne)
  have norm : w 0 ^ 2 + a ⬝ᵥ a = 1 := by
    rw [Fin.sum_univ_succ] at squares
    simpa only [dotProduct, pow_two, a] using squares
  have comb : (∑ i : Fin 9, w i • stdSys i) = stdComb (w 0) a := by
    rw [Fin.sum_univ_succ]
    rfl
  have leigen := (sec7_L_eigenspace_proved x hx).2.1
  have expressed : {z : Vec 16 | conjChange *ᵥ z ∈ Lstd x} =
      {z : Vec 16 | stdComb (w 0) a *ᵥ (conjChange *ᵥ z) = conjChange *ᵥ z} := by
    ext z
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, leigen, Module.End.mem_eigenspace_iff]
    change (∑ i, w i • stdSys i) *ᵥ (conjChange *ᵥ z) = (1 : ℝ) • (conjChange *ᵥ z) ↔ _
    rw [comb, one_smul]
  by_cases pole : w 0 = -1
  · exact Or.inr (expressed.trans ((lem_7_1_eigenspace_line_proved (w 0) a norm).2 pole))
  · exact Or.inl ⟨(1 + w 0)⁻¹ • oconj a,
      expressed.trans ((lem_7_1_eigenspace_line_proved (w 0) a norm).1 pole)⟩

theorem lem_7_1_L_line_proved :
    (∀ x : Vec 16, x ∈ Lstd x) ∧
      (∀ (ω : Vec 8) (y : Vec 16), y ≠ 0 → y ∈ cayLine ω →
        {z : Vec 16 | conjChange *ᵥ z ∈ Lstd (conjChange *ᵥ y)} = cayLine ω) ∧
      ∀ y : Vec 16, y ≠ 0 → y ∈ cayLineInf →
        {z : Vec 16 | conjChange *ᵥ z ∈ Lstd (conjChange *ᵥ y)} = cayLineInf := by
  refine ⟨self_mem_L, ?_, ?_⟩
  · intro ω y hy member
    have inL : conjChange *ᵥ y ∈ Lstd (conjChange *ᵥ y) := self_mem_L _
    rcases L_is_line y hy with ⟨ω', equal⟩ | equal
    · by_cases same : ω = ω'
      · simpa only [same] using equal
      · have intersection : y ∈ cayLine ω ∩ cayLine ω' := ⟨member, by rw [← equal]; exact inL⟩
        rw [(Osserman.Proofs.OctonionNucleus.cayley_lines_meet_zero_proved).1 ω ω' same] at intersection
        exact (hy (Set.mem_singleton_iff.mp intersection)).elim
    · have intersection : y ∈ cayLine ω ∩ cayLineInf := ⟨member, by rw [← equal]; exact inL⟩
      rw [(Osserman.Proofs.OctonionNucleus.cayley_lines_meet_zero_proved).2 ω] at intersection
      exact (hy (Set.mem_singleton_iff.mp intersection)).elim
  · intro y hy member
    have inL : conjChange *ᵥ y ∈ Lstd (conjChange *ᵥ y) := self_mem_L _
    rcases L_is_line y hy with ⟨ω, equal⟩ | equal
    · have intersection : y ∈ cayLine ω ∩ cayLineInf := ⟨by rw [← equal]; exact inL, member⟩
      rw [(Osserman.Proofs.OctonionNucleus.cayley_lines_meet_zero_proved).2 ω] at intersection
      exact (hy (Set.mem_singleton_iff.mp intersection)).elim
    · exact equal

lemma N_new_iff (y z : Vec 16) :
    conjChange *ᵥ z ∈ Nstd (conjChange *ᵥ y) ↔
      ∀ v : Vec 16, conjChange *ᵥ v ∈ Lstd (conjChange *ᵥ y) → v ⬝ᵥ z = 0 := by
  constructor
  · intro h v hv
    have pair := h (conjChange *ᵥ v) hv
    simpa only [conj_dot] using pair
  · intro h
    change ∀ u ∈ Lstd (conjChange *ᵥ y), u ⬝ᵥ (conjChange *ᵥ z) = 0
    intro u hu
    calc
      u ⬝ᵥ (conjChange *ᵥ z) =
          (conjChange *ᵥ (conjChange *ᵥ u)) ⬝ᵥ (conjChange *ᵥ z) := by rw [conj_invol]
      _ = (conjChange *ᵥ u) ⬝ᵥ z := conj_dot _ _
      _ = 0 := h _ (by simpa only [conj_invol] using hu)

lemma finite_orth (ω : Vec 8) (z : Vec 16) :
    (∀ v ∈ cayLine ω, v ⬝ᵥ z = 0) ↔ oct1 z = -omul (oconj ω) (oct2 z) := by
  have pairing (u : Vec 8) : octPair u (omul ω u) ⬝ᵥ z =
      u ⬝ᵥ (oct1 z + omul (oconj ω) (oct2 z)) := by
    conv_lhs => arg 2; rw [← pair_parts z]
    rw [pair_dot, oct_adjoint_proved, dotProduct_add]
  constructor
  · intro h
    let p := oct1 z + omul (oconj ω) (oct2 z)
    have member : octPair p (omul ω p) ∈ cayLine ω := by simp [cayLine]
    have zero := h _ member
    rw [pairing] at zero
    have pzero : p = 0 := dotProduct_self_eq_zero.mp zero
    exact eq_neg_of_add_eq_zero_left pzero
  · intro h v hv
    have parts : v = octPair (oct1 v) (omul ω (oct1 v)) := by
      rw [← hv]; exact (pair_parts v).symm
    rw [parts, pairing, h, neg_add_cancel, dotProduct_zero]

lemma infinite_orth (z : Vec 16) : (∀ v ∈ cayLineInf, v ⬝ᵥ z = 0) ↔ oct2 z = 0 := by
  have pairing (u : Vec 8) : octPair 0 u ⬝ᵥ z = u ⬝ᵥ oct2 z := by
    conv_lhs => arg 2; rw [← pair_parts z]
    rw [pair_dot, zero_dotProduct, zero_add]
  constructor
  · intro h
    have zero := h (octPair 0 (oct2 z)) (by simp [cayLineInf])
    rw [pairing] at zero
    exact dotProduct_self_eq_zero.mp zero
  · intro h v hv
    have parts : v = octPair 0 (oct2 v) := by rw [← hv]; exact (pair_parts v).symm
    rw [parts, pairing, h, dotProduct_zero]

theorem lem_7_1_N_line_proved :
    (∀ (ω : Vec 8) (y : Vec 16), y ≠ 0 → y ∈ cayLine ω →
        {z : Vec 16 | conjChange *ᵥ z ∈ Nstd (conjChange *ᵥ y)} =
          {z | oct1 z = -omul (oconj ω) (oct2 z)}) ∧
      ∀ y : Vec 16, y ≠ 0 → y ∈ cayLineInf →
        {z : Vec 16 | conjChange *ᵥ z ∈ Nstd (conjChange *ᵥ y)} = cayLine 0 := by
  constructor
  · intro ω y hy member
    have line := lem_7_1_L_line_proved.2.1 ω y hy member
    ext z
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, N_new_iff]
    have line_mem (v : Vec 16) : conjChange *ᵥ v ∈ Lstd (conjChange *ᵥ y) ↔ v ∈ cayLine ω :=
      Set.ext_iff.mp line v
    simp_rw [line_mem]
    exact finite_orth ω z
  · intro y hy member
    have line := lem_7_1_L_line_proved.2.2 y hy member
    ext z
    rw [Set.mem_ofPred_eq, N_new_iff]
    have line_mem (v : Vec 16) : conjChange *ᵥ v ∈ Lstd (conjChange *ᵥ y) ↔ v ∈ cayLineInf :=
      Set.ext_iff.mp line v
    simp_rw [line_mem]
    simpa only [cayLine, Set.mem_ofPred_eq, zero_omul] using infinite_orth z

theorem lem_7_1_a_lines_proved (K : Matrix (Fin 16) (Fin 16) ℝ)
    (hK : ∀ x : Vec 16, x ≠ 0 → K *ᵥ x ∈ Estd x) :
    (∀ ω : Vec 8, ∀ y ∈ cayLine ω, (conjChange * K * conjChange) *ᵥ y ∈ cayLine ω) ∧
      ∀ y ∈ cayLineInf, (conjChange * K * conjChange) *ᵥ y ∈ cayLineInf := by
  have image (y : Vec 16) (hy : y ≠ 0) :
      conjChange *ᵥ ((conjChange * K * conjChange) *ᵥ y) ∈ Lstd (conjChange *ᵥ y) := by
    have nonzero : conjChange *ᵥ y ≠ 0 := by
      intro equal
      apply hy
      apply Osserman.Proofs.Lemma71Coordinates.conj_injective
      simpa only [Matrix.mulVec_zero] using equal
    simp only [← Matrix.mulVec_mulVec, conj_invol]
    exact (hK _ nonzero).1
  constructor
  · intro ω y member
    by_cases zero : y = 0
    · subst y
      rw [Matrix.mulVec_zero]
      change (0 : Vec 8) = omul ω 0
      rw [omul_zero]
    · rw [← lem_7_1_L_line_proved.2.1 ω y zero member]
      exact image y zero
  · intro y member
    by_cases zero : y = 0
    · subst y
      rw [Matrix.mulVec_zero]
      change (0 : Vec 8) = 0
      rfl
    · rw [← lem_7_1_L_line_proved.2.2 y zero member]
      exact image y zero

end Osserman.Proofs.Lemma71Geometry
