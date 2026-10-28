/-
NagataHigman/Proofs/MatInvDensity.lean — Corollary 1.1: conjugation invariance over F (char 0) survives base change F → K.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import NagataHigman.Defs.MatrixInvariants

/-!
Proof. Over `F`, invariance under `g` is equivalent to `p(g X) = p(X g)` for all `X` (put `X := X' g`). Take a
generic matrix `Y` and a generic tuple `X` and let `E := p(Y X) - p(X Y)`. Then `det(Y) · E` vanishes at every point
of `F`, so it is `0` (`F` is infinite); `det(Y) ≠ 0`, so `E = 0`. Mapped to `K` and evaluated at `Y ↦ g`,
`X ↦ X g⁻¹`, this gives `p(g X g⁻¹) = p(X)` over `K`.
-/

noncomputable section

namespace NagataHigman.Proofs.MatInvDensity

open MvPolynomial

variable {F : Type*} [Field F] {n k : ℕ}

/-- The variables of the generic problem: the entries of a matrix `Y` (left) and of a `k`-tuple `X` (right). -/
abbrev GVar (n k : ℕ) : Type := (Fin n × Fin n) ⊕ (Fin k × Fin n × Fin n)

/-- The coordinates of a `k`-tuple of matrices over any type (`tupleCoords` without the field assumption). -/
def coords {R : Type*} (M : Fin k → Matrix (Fin n) (Fin n) R) : Fin k × Fin n × Fin n → R :=
  fun v => M v.1 v.2.1 v.2.2

/-- The matrix `Y` read off a point `y`. -/
def ptY {R : Type*} (y : GVar n k → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun a b => y (Sum.inl (a, b))

/-- The `i`-th matrix `X_i` read off a point `y`. -/
def ptX {R : Type*} (y : GVar n k → R) (i : Fin k) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun a b => y (Sum.inr (i, a, b))

/-- The generic difference `E = p(Y X) - p(X Y)`, with `Y`, `X` the generic matrices (`y := MvPolynomial.X`). -/
def E (p : MatPoly F n k) : MvPolynomial (GVar n k) F :=
  aeval (coords fun i => ptY X * ptX X i) p - aeval (coords fun i => ptX X i * ptY X) p

lemma map_ptY {R S : Type*} (y : GVar n k → R) (f : R → S) : (ptY y).map f = ptY (f ∘ y) := rfl

lemma map_ptX {R S : Type*} (y : GVar n k → R) (f : R → S) (i : Fin k) : (ptX y i).map f = ptX (f ∘ y) i := rfl

/-- A ring hom applied to a substitution of matrix entries is the substitution of the mapped entries. -/
lemma hom_aeval_coords {R : Type*} [CommRing R] (ψ : MvPolynomial (GVar n k) F →+* R)
    (M : Fin k → Matrix (Fin n) (Fin n) (MvPolynomial (GVar n k) F)) (p : MatPoly F n k) :
    ψ (aeval (coords M) p) = eval₂ (ψ.comp C) (coords fun i => (M i).map ψ) p := by
  rw [aeval_def, eval₂_comp_left, algebraMap_eq]
  rfl

/-- `E` evaluated at a point `y` of any commutative `F`-ring: `p(Y X) - p(X Y)` at `Y = ptY y`, `X = ptX y`. -/
lemma eval₂Hom_E {R : Type*} [CommRing R] (φ : F →+* R) (y : GVar n k → R) (p : MatPoly F n k) :
    eval₂Hom φ y (E p) =
      eval₂ φ (coords fun i => ptY y * ptX y i) p - eval₂ φ (coords fun i => ptX y i * ptY y) p := by
  have hY : (ptY X).map (eval₂Hom φ y) = ptY y := by
    rw [map_ptY]; congr 1; funext v; exact eval₂Hom_X' φ y v
  have hX : ∀ i, (ptX X i).map (eval₂Hom φ y) = ptX y i := by
    intro i; rw [map_ptX]; congr 1; funext v; exact eval₂Hom_X' φ y v
  simp only [E, map_sub, hom_aeval_coords, eval₂Hom_comp_C, Matrix.map_mul, hY, hX]

/-- Step (1): over `F`, invariance gives `p(g X) = p(X g)` for every invertible `g`, hence `E` vanishes at every
point whose `Y` is invertible. -/
lemma eval_E_of_isUnit {p : MatPoly F n k} (hp : IsConjInvariant p) (x : GVar n k → F) (hx : IsUnit (ptY x)) :
    eval x (E p) = 0 := by
  obtain ⟨g, hg⟩ := hx
  have h := hp g (fun i => ptX x i * (g : Matrix (Fin n) (Fin n) F))
  simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at h
  have hE := eval₂Hom_E (RingHom.id F) x p
  rw [← hg] at hE
  change eval x (E p) = eval (coords fun i => (g : Matrix (Fin n) (Fin n) F) * ptX x i) p -
    eval (coords fun i => ptX x i * (g : Matrix (Fin n) (Fin n) F)) p at hE
  rw [hE, sub_eq_zero]
  exact h

/-- The determinant of the generic matrix `Y`, evaluated at a point. -/
lemma eval_det_ptY (x : GVar n k → F) : eval x (ptY (X : GVar n k → MvPolynomial (GVar n k) F)).det =
    (ptY x).det := by
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [ptY]

/-- Step (3a): `det(Y) · E` vanishes at every point of `F`. -/
lemma eval_det_mul_E {p : MatPoly F n k} (hp : IsConjInvariant p) (x : GVar n k → F) :
    eval x ((ptY (X : GVar n k → MvPolynomial (GVar n k) F)).det * E p) = 0 := by
  rw [map_mul, eval_det_ptY]
  by_cases hdet : (ptY x).det = 0
  · rw [hdet, zero_mul]
  · rw [eval_E_of_isUnit hp x ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)), mul_zero]

/-- The generic determinant is a nonzero polynomial (it is `1` at `Y = 1`). -/
lemma det_ptY_ne_zero : (ptY (X : GVar n k → MvPolynomial (GVar n k) F)).det ≠ 0 := by
  intro h
  have h1 := congrArg (eval (Sum.elim (fun ab : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) F) ab.1 ab.2)
    (fun _ => 0) : GVar n k → F)) h
  rw [eval_det_ptY, map_zero] at h1
  have hone : ptY (Sum.elim (fun ab : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) F) ab.1 ab.2)
      (fun _ => 0) : GVar n k → F) = 1 := by
    ext a b; simp [ptY]
  rw [hone, Matrix.det_one] at h1
  exact one_ne_zero h1

/-- Step (3b): over a field of characteristic `0`, `E = 0`. -/
lemma E_eq_zero [CharZero F] {p : MatPoly F n k} (hp : IsConjInvariant p) : E p = 0 := by
  have hprod : (ptY (X : GVar n k → MvPolynomial (GVar n k) F)).det * E p = 0 :=
    MvPolynomial.funext fun x => by rw [eval_det_mul_E hp x, map_zero]
  exact (mul_eq_zero.1 hprod).resolve_left det_ptY_ne_zero

/-- Corollary 1.1, base change: conjugation invariance over `F` (characteristic `0`) persists over any field
extension `K`. -/
theorem isConjInvariant_map {F K : Type*} [Field F] [CharZero F] [Field K] [Algebra F K] {n k : ℕ}
    {p : MatPoly F n k} (hp : IsConjInvariant p) :
    IsConjInvariant (MvPolynomial.map (algebraMap F K) p) := by
  intro g Xs
  set y : GVar n k → K := Sum.elim (fun ab => (g : Matrix (Fin n) (Fin n) K) ab.1 ab.2)
    (fun v => (Xs v.1 * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) v.2.1 v.2.2) with hy
  have hY : ptY y = (g : Matrix (Fin n) (Fin n) K) := by ext a b; simp [ptY, hy]
  have hX : ∀ i, ptX y i = Xs i * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    intro i; ext a b; simp [ptX, hy]
  have h := eval₂Hom_E (algebraMap F K) y p
  rw [E_eq_zero hp, map_zero, eq_comm, sub_eq_zero, hY] at h
  have hcancel : ∀ i, Xs i * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) =
      Xs i := fun i => by rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  simp only [hX, hcancel, ← Matrix.mul_assoc] at h
  rw [eval_map, eval_map]
  exact h

end NagataHigman.Proofs.MatInvDensity

end
