/-
S8TCFactor.lean — primitive columns and the third-column factor, paper 013, Section8.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.S8TCAlgebra
import Mathlib.RingTheory.Localization.NumDen

namespace Osserman.Proofs.S8TC

open Osserman Matrix MvPolynomial

lemma scalar_in_ring_of_primitive {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    (v w : Fin 16 → A) (hv : ∀ d : A, (∀ a, d ∣ v a) → IsUnit d)
    (z : FractionRing A) (hz : ∀ a, z * algebraMap A (FractionRing A) (v a) =
      algebraMap A (FractionRing A) (w a)) :
    ∃ u : A, algebraMap A (FractionRing A) u = z := by
  let f := algebraMap A (FractionRing A)
  let d := IsFractionRing.den A z
  let n := IsFractionRing.num A z
  have numerator : z * f d = f n := by
    exact (IsFractionRing.num_mul_den_eq_num_iff_eq (A := A) (x := z) (y := z)).mpr rfl
  have divides (a : Fin 16) : (d : A) ∣ v a := by
    have product : (d : A) * w a = n * v a := by
      apply IsFractionRing.injective A (FractionRing A)
      simp only [map_mul]
      calc
        f d * f (w a) = f d * (z * f (v a)) := by rw [hz]
        _ = (z * f d) * f (v a) := by ring
        _ = f n * f (v a) := by rw [numerator]
    exact (IsFractionRing.num_den_reduced A z).symm.dvd_of_dvd_mul_left
      ⟨w a, product.symm⟩
  exact IsFractionRing.isInteger_of_isUnit_den (hv d divides)

lemma primitive_pair {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    (p q : Fin 16 → A) (hp : p ≠ 0)
    (hminor : ∀ a b, p a * q b - q a * p b = 0) :
    ∃ (u0 u1 : A) (v : Fin 16 → A), (∀ d : A, (∀ a, d ∣ v a) → IsUnit d) ∧
      p = u0 • v ∧ q = u1 • v := by
  classical
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α := A)
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid A
  obtain ⟨v, hpv, hv⟩ := Finset.extract_gcd (s := Finset.univ) p (by simp : (Finset.univ : Finset (Fin 16)).Nonempty)
  let g : A := Finset.univ.gcd p
  have primitive : ∀ d : A, (∀ a, d ∣ v a) → IsUnit d := by
    intro d hd
    have common : d ∣ Finset.univ.gcd v := Finset.dvd_gcd fun a _ => hd a
    rw [hv] at common
    exact isUnit_of_dvd_one common
  obtain ⟨a0, ha0⟩ : ∃ a, p a ≠ 0 := by
    by_contra absent
    apply hp
    funext a
    by_contra different
    exact absent ⟨a, different⟩
  have decomp (a : Fin 16) : p a = g * v a := hpv a (Finset.mem_univ a)
  have hg : g ≠ 0 := fun zero => ha0 (by rw [decomp, zero, zero_mul])
  have hva : v a0 ≠ 0 := fun zero => ha0 (by rw [decomp, zero, mul_zero])
  have minor (b : Fin 16) : v a0 * q b = q a0 * v b := by
    have relation := hminor a0 b
    rw [decomp a0, decomp b] at relation
    apply mul_left_cancel₀ hg
    linear_combination relation
  let f := algebraMap A (FractionRing A)
  have hmap : f (v a0) ≠ 0 := by
    intro zero
    apply hva
    apply IsFractionRing.injective A (FractionRing A)
    simpa only [map_zero] using zero
  let z := f (q a0) / f (v a0)
  have action (b : Fin 16) : z * f (v b) = f (q b) := by
    have relation := congrArg f (minor b)
    simp only [map_mul] at relation
    dsimp only [z]
    field_simp
    linear_combination -relation
  obtain ⟨u1, hu1⟩ := scalar_in_ring_of_primitive v q primitive z action
  refine ⟨g, u1, v, primitive, ?_, ?_⟩
  · funext a
    exact decomp a
  · funext a
    apply IsFractionRing.injective A (FractionRing A)
    change f (q a) = f (u1 * v a)
    rw [map_mul, hu1, action]

theorem s8_tc_primitive_of_s8_q_prime
    (hQ : Irreducible (sqP 16) ∧ Prime (sqP 16) ∧ IsDomain Ocal)
    (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (wt : Fin 3 → ℝ) (h : ThreeColHyp R μ P wt) (hne : ∀ i, tcImg wt P i ≠ 0) :
    ∃ (u0 u1 : Ocal) (v : Fin 16 → Ocal), (∀ d : Ocal, (∀ a, d ∣ v a) → IsUnit d) ∧
      tcImg wt P 0 = u0 • v ∧ tcImg wt P 1 = u1 • v := by
  let := hQ.2.2
  let := Osserman.Cited.nik2006_thm_3_1
  have rankone := (s8_tc_rankone_proved R μ P wt h).2
  have minors := s8_tc_minors_of_s8_q_prime hQ (tcImg wt P) rankone
  exact primitive_pair (tcImg wt P 0) (tcImg wt P 1) (hne 0) (fun a b => (minors a b).2.2)

theorem s8_tc_third_of_s8_q_prime
    (hQ : Irreducible (sqP 16) ∧ Prime (sqP 16) ∧ IsDomain Ocal)
    (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (wt : Fin 3 → ℝ) (h : ThreeColHyp R μ P wt) (u0 u1 : Ocal) (v : Fin 16 → Ocal)
    (hv : ∀ d : Ocal, (∀ a, d ∣ v a) → IsUnit d) (h0 : tcImg wt P 0 = u0 • v) (h1 : tcImg wt P 1 = u1 • v) :
    ∃ u3 : Ocal, tcImg wt P 2 = u3 • v ∧ u0 ^ 2 + u1 ^ 2 = u3 ^ 2 := by
  let := hQ.2.2
  have nonzero : v ≠ 0 := by
    intro zero
    have impossible := hv 0 (fun a => by simp [zero])
    exact not_isUnit_zero impossible
  obtain ⟨a0, ha0⟩ : ∃ a, v a ≠ 0 := by
    by_contra absent
    apply nonzero
    funext a
    by_contra different
    exact absent ⟨a, different⟩
  have relation (a b : Fin 16) : (u0 ^ 2 + u1 ^ 2) * (v a * v b) = tcImg wt P 2 a * tcImg wt P 2 b := by
    have equation := (s8_tc_rankone_proved R μ P wt h).2 a b
    rw [h0, h1] at equation
    simp only [Pi.smul_apply, smul_eq_mul] at equation
    linear_combination equation
  obtain ⟨z, hz, _⟩ := s8_tc_sqrt_frac_of_s8_q_prime hQ u0 u1 v (tcImg wt P 2) relation a0 ha0
  obtain ⟨u3, hu3⟩ := s8_tc_integral_of_s8_q_prime hQ z (u0 ^ 2 + u1 ^ 2) hz
  have square : u0 ^ 2 + u1 ^ 2 = u3 ^ 2 := by
    apply IsFractionRing.injective Ocal (FractionRing Ocal)
    rw [← hz, hu3, map_pow]
  have outer (a b : Fin 16) : (u3 * v a) * (u3 * v b) = tcImg wt P 2 a * tcImg wt P 2 b := by
    rw [← relation a b, square]
    ring
  rcases s8_tc_sign_of_s8_q_prime hQ u3 v (tcImg wt P 2) outer with first | second
  · exact ⟨u3, first, square⟩
  · refine ⟨-u3, second, ?_⟩
    calc
      u0 ^ 2 + u1 ^ 2 = u3 ^ 2 := square
      _ = (-u3) ^ 2 := by ring

end Osserman.Proofs.S8TC
