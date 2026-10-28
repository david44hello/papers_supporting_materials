/-
NagataHigman/Proofs/FreeAlgebraLayer.lean — free-algebra layer: lift, multilinearity, polarization, (F0), (F1), [Ro22 1.8].
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Mathlib
import NagataHigman.Defs.FreeAlgebra
import NagataHigman.Defs.Spanning

universe u

noncomputable section

namespace NagataHigman.Proofs

open NagataHigman Equiv Finset

/-! ### Basic facts on `tupleProd` -/

section TupleProd

variable {R S : Type*}

theorem tupleProd_zero [Mul R] [Zero R] (x : Fin 0 → R) : tupleProd 0 x = 0 := rfl

theorem tupleProd_one [Mul R] [Zero R] (x : Fin 1 → R) : tupleProd 1 x = x 0 := rfl

theorem tupleProd_succ_succ [Mul R] [Zero R] (m : ℕ) (x : Fin (m + 2) → R) :
    tupleProd (m + 2) x = tupleProd (m + 1) (fun i => x i.castSucc) * x (Fin.last (m + 1)) := rfl

/-- The recursion step of `tupleProd` for every length `m ≥ 1`. -/
theorem tupleProd_succ [Mul R] [Zero R] (m : ℕ) (hm : 1 ≤ m) (x : Fin (m + 1) → R) :
    tupleProd (m + 1) x = tupleProd m (fun i => x i.castSucc) * x (Fin.last m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rfl

/-- A multiplicative map commutes with `tupleProd` of positive length. -/
theorem tupleProd_map_succ [Mul R] [Zero R] [Mul S] [Zero S] (f : R → S)
    (hmul : ∀ a b, f (a * b) = f a * f b) :
    ∀ (m : ℕ) (x : Fin (m + 1) → R), f (tupleProd (m + 1) x) = tupleProd (m + 1) (fun i => f (x i))
  | 0, _ => rfl
  | (m + 1), x => by
      rw [tupleProd_succ_succ, hmul, tupleProd_map_succ f hmul m]
      rfl

/-- A multiplicative map that sends `0` to `0` commutes with `tupleProd`. -/
theorem tupleProd_map [Mul R] [Zero R] [Mul S] [Zero S] (f : R → S)
    (hmul : ∀ a b, f (a * b) = f a * f b) (hzero : f 0 = 0) :
    ∀ (m : ℕ) (x : Fin m → R), f (tupleProd m x) = tupleProd m (fun i => f (x i))
  | 0, _ => hzero
  | (m + 1), x => tupleProd_map_succ f hmul m x

/-- **A2** A multiplicative, zero-preserving hom commutes with `tupleProd`. -/
theorem map_tupleProd [MulZeroClass R] [MulZeroClass S] {G : Type*} [FunLike G R S] [MulHomClass G R S]
    [ZeroHomClass G R S] (f : G) (m : ℕ) (x : Fin m → R) :
    f (tupleProd m x) = tupleProd m (fun i => f (x i)) :=
  tupleProd_map f (map_mul f) (map_zero f) m x

/-- **A2** A multiplicative, zero-preserving hom commutes with `nuPow`. -/
theorem map_nuPow [MulZeroClass R] [MulZeroClass S] {G : Type*} [FunLike G R S] [MulHomClass G R S]
    [ZeroHomClass G R S] (f : G) (a : R) (n : ℕ) : f (nuPow a n) = nuPow (f a) n :=
  map_tupleProd f n _

/-- **A2** A `MulHom` commutes with `tupleProd` of length `m ≥ 1`. -/
theorem mulHom_map_tupleProd [Mul R] [Zero R] [Mul S] [Zero S] (f : R →ₙ* S) (m : ℕ) (hm : 1 ≤ m)
    (x : Fin m → R) : f (tupleProd m x) = tupleProd m (fun i => f (x i)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  exact tupleProd_map_succ f (map_mul f) k x

/-- **A2** A `MulHom` commutes with `nuPow` of exponent `n ≥ 1`. -/
theorem mulHom_map_nuPow [Mul R] [Zero R] [Mul S] [Zero S] (f : R →ₙ* S) (a : R) (n : ℕ) (hn : 1 ≤ n) :
    f (nuPow a n) = nuPow (f a) n :=
  mulHom_map_tupleProd f n hn _

/-- A tuple with a zero entry has product `0`. -/
theorem tupleProd_eq_zero_of [MulZeroClass R] :
    ∀ (m : ℕ) (x : Fin m → R) (k : Fin m), x k = 0 → tupleProd m x = 0
  | 0, _, k, _ => k.elim0
  | 1, x, k, hk => by rw [tupleProd_one, ← hk, Subsingleton.elim k 0]
  | (m + 2), x, k, hk => by
      rw [tupleProd_succ_succ]
      induction k using Fin.lastCases with
      | last => rw [hk, mul_zero]
      | cast j => rw [tupleProd_eq_zero_of (m + 1) _ j hk, zero_mul]

/-- **A4** Multilinearity of `tupleProd`, general form: one finite sum per factor. -/
theorem tupleProd_sum_pi [NonUnitalNonAssocSemiring R] {ι : Type*} [Fintype ι] :
    ∀ (m : ℕ) (y : Fin m → ι → R),
      tupleProd m (fun k => ∑ i, y k i) = ∑ f : Fin m → ι, tupleProd m (fun k => y k (f k))
  | 0, _ => by simp [tupleProd_zero]
  | 1, y => by
      rw [tupleProd_one]
      exact (Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι) _ _ (fun f => rfl)).symm
  | (m + 2), y => by
      rw [tupleProd_succ_succ, tupleProd_sum_pi (m + 1), Finset.sum_mul_sum]
      conv_rhs => rw [← (Fin.snocEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun i _ => ?_
      simp [tupleProd_succ_succ, Fin.snocEquiv]

/-- **A4** Multilinearity of `tupleProd` for a sum over a finset, the same in every factor. -/
theorem tupleProd_finset_sum [NonUnitalNonAssocSemiring R] {ι : Type*} (s : Finset ι) (m : ℕ) (y : ι → R) :
    tupleProd m (fun _ => ∑ i ∈ s, y i) = ∑ f : Fin m → s, tupleProd m (fun k => y (f k)) := by
  rw [← tupleProd_sum_pi m (fun _ (i : s) => y i)]
  simp only [Finset.sum_coe_sort s y]

end TupleProd

/-! ### A1: the universal property of `F⟨X⟩` -/

section Lift

variable (F : Type*) [Field F] {R : Type*} [NonUnitalRing R] [Module F R] [IsScalarTower F R R]
  [SMulCommClass F R R]

/-- **A1** The non-unital algebra hom `F⟨X⟩ → R` that sends the letter `x_i` to `r i`. -/
def freeLift (r : ℕ → R) : FreeNUAlg F →ₙₐ[F] R :=
  MonoidAlgebra.liftMagma F (FreeSemigroup.lift r)

/-- **A1** `freeLift r` sends `x_i` to `r i`. -/
@[simp] theorem freeLift_letter (r : ℕ → R) (i : ℕ) : freeLift F r (letter F i) = r i := by
  simp [freeLift, letter]

omit [IsScalarTower F R R] [SMulCommClass F R R] in
/-- **A1** Uniqueness: two non-unital algebra homs out of `F⟨X⟩` that agree on every letter are equal. -/
theorem freeNUAlg_hom_ext {φ ψ : FreeNUAlg F →ₙₐ[F] R} (h : ∀ i, φ (letter F i) = ψ (letter F i)) :
    φ = ψ := by
  refine MonoidAlgebra.nonUnitalAlgHom_ext F fun w => ?_
  induction w using FreeSemigroup.recOnMul with
  | ih1 i => exact h i
  | ih2 i w _ hw =>
      rw [← one_mul (1 : F), ← MonoidAlgebra.single_mul_single, map_mul, map_mul, hw]
      exact congrArg (· * ψ (MonoidAlgebra.single w 1)) (h i)

/-- **A1** Every non-unital algebra hom out of `F⟨X⟩` is the lift of its values on the letters. -/
theorem freeLift_unique (φ : FreeNUAlg F →ₙₐ[F] R) : φ = freeLift F (fun i => φ (letter F i)) :=
  freeNUAlg_hom_ext F fun i => (freeLift_letter F (fun i => φ (letter F i)) i).symm

end Lift

/-! ### A3: `T` is the smallest T-ideal containing `x^n` -/

section TIdealBasics

variable (F : Type*) [Field F]

/-- The infimum of all T-ideals with a property `P` is a T-ideal. -/
theorem isTIdeal_sInf (P : Submodule F (FreeNUAlg F) → Prop) :
    IsTIdeal F (sInf {S | IsTIdeal F S ∧ P S}) where
  mul_left r a ha := Submodule.mem_sInf.2 fun S hS => hS.1.mul_left r a (Submodule.mem_sInf.1 ha S hS)
  mul_right r a ha := Submodule.mem_sInf.2 fun S hS => hS.1.mul_right r a (Submodule.mem_sInf.1 ha S hS)
  endo φ a ha := Submodule.mem_sInf.2 fun S hS => hS.1.endo φ a (Submodule.mem_sInf.1 ha S hS)

/-- **A3** `T = (x^n)^T` is a T-ideal. -/
theorem isTIdeal_TIdeal (n : ℕ) : IsTIdeal F (TIdeal F n) :=
  isTIdeal_sInf F _

/-- **A3** `x^n ∈ T`. -/
theorem nuPow_letter_mem_TIdeal (n : ℕ) : nuPow (letter F 0) n ∈ TIdeal F n :=
  Submodule.mem_sInf.2 fun _ hS => hS.2

/-- **A3** `T` lies in every T-ideal that contains `x^n`. -/
theorem TIdeal_le {n : ℕ} {S : Submodule F (FreeNUAlg F)} (hS : IsTIdeal F S)
    (h : nuPow (letter F 0) n ∈ S) : TIdeal F n ≤ S :=
  sInf_le ⟨hS, h⟩

/-- `p^n ∈ T` for every `p ∈ F⟨X⟩` (substitute `x_0 ↦ p`). -/
theorem nuPow_mem_TIdeal (n : ℕ) (p : FreeNUAlg F) : nuPow p n ∈ TIdeal F n := by
  have h := (isTIdeal_TIdeal F n).endo (freeLift F (fun _ => p)) _ (nuPow_letter_mem_TIdeal F n)
  rwa [map_nuPow, freeLift_letter] at h

end TIdealBasics

/-! ### A5: polarization -/

section Polarization

variable {R : Type*} [NonUnitalRing R]

/-- `(∑_{i ∈ S} y_i)^n`, expanded over all maps `f : Fin n → Fin n`, keeping those with values in `S`. -/
theorem nuPow_finset_sum_eq (n : ℕ) (y : Fin n → R) (S : Finset (Fin n)) :
    nuPow (∑ i ∈ S, y i) n =
      ∑ f : Fin n → Fin n, if (∀ k, f k ∈ S) then tupleProd n (fun k => y (f k)) else 0 := by
  rw [nuPow, ← Fintype.sum_ite_mem S y]
  refine (tupleProd_sum_pi n (fun _ i => if i ∈ S then y i else 0)).trans
    (Finset.sum_congr rfl fun f _ => ?_)
  by_cases h : ∀ k, f k ∈ S
  · rw [ite_eq_left h]
    exact congrArg (tupleProd n) (funext fun k => ite_eq_left (h k))
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨k, hk⟩ := h
    exact tupleProd_eq_zero_of n _ k (ite_eq_right hk)

/-- Over the subsets `S` of `Fin n`, `∑_{S ⊇ A} (-1)^{n-|S|}` is `1` if `A` is everything and `0` otherwise. -/
theorem sum_superset_neg_one_pow (n : ℕ) (A : Finset (Fin n)) :
    (∑ S : Finset (Fin n), if A ⊆ S then (-1 : ℤ) ^ (n - S.card) else 0) = if A = univ then 1 else 0 := by
  have hT : ∀ T : Finset (Fin n), (if A ⊆ Tᶜ then (-1 : ℤ) ^ (n - Tᶜ.card) else 0) =
      if T ∈ Aᶜ.powerset then (-1 : ℤ) ^ T.card else 0 := by
    intro T
    have hc : n - Tᶜ.card = T.card := by
      rw [Finset.card_compl, Fintype.card_fin, Nat.sub_sub_self (by simpa using card_le_univ T)]
    rw [hc]
    exact if_congr (Finset.subset_compl_comm.trans Finset.mem_powerset.symm) rfl rfl
  rw [← Fintype.sum_equiv (Function.Involutive.toPerm _ compl_involutive)
    (fun T => if A ⊆ Tᶜ then (-1 : ℤ) ^ (n - Tᶜ.card) else 0) _ (fun T => rfl)]
  refine (Finset.sum_congr rfl fun T _ => hT T).trans ?_
  rw [Fintype.sum_ite_mem, Finset.sum_powerset_neg_one_pow_card]
  exact if_congr (Finset.compl_eq_empty_iff A) rfl rfl

/-- The coefficient of the word of `f : Fin n → Fin n` in the polarization sum. -/
theorem polarization_coeff (n : ℕ) (f : Fin n → Fin n) (P : R) :
    (∑ S : Finset (Fin n), ((-1 : ℤ) ^ (n - S.card)) • (if (∀ k, f k ∈ S) then P else 0)) =
      if Function.Surjective f then P else 0 := by
  have h1 : ∀ S : Finset (Fin n), ((-1 : ℤ) ^ (n - S.card)) • (if (∀ k, f k ∈ S) then P else 0) =
      (if univ.image f ⊆ S then (-1 : ℤ) ^ (n - S.card) else 0) • P := by
    intro S
    have hiff : (∀ k, f k ∈ S) ↔ univ.image f ⊆ S := by simp [Finset.image_subset_iff]
    by_cases h : ∀ k, f k ∈ S
    · rw [ite_eq_left h, ite_eq_left (hiff.1 h)]
    · rw [ite_eq_right h, ite_eq_right (mt hiff.2 h), smul_zero, zero_smul]
  have hsurj : univ.image f = univ ↔ Function.Surjective f := by
    simp [Finset.eq_univ_iff_forall, Function.Surjective]
  simp only [h1]
  rw [← Finset.sum_smul, sum_superset_neg_one_pow]
  by_cases hf : Function.Surjective f
  · rw [ite_eq_left (hsurj.2 hf), ite_eq_left hf, one_smul]
  · rw [ite_eq_right (mt hsurj.1 hf), ite_eq_right hf, zero_smul]

/-- A sum over the surjective self-maps of `Fin n` is a sum over the permutations. -/
theorem sum_surjective_eq_sum_perm {M : Type*} [AddCommMonoid M] (n : ℕ) (g : (Fin n → Fin n) → M)
    [DecidablePred (fun f : Fin n → Fin n => Function.Surjective f)] :
    (∑ f : Fin n → Fin n, if Function.Surjective f then g f else 0) = ∑ π : Perm (Fin n), g π := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun π _ => ⇑π) (fun π _ => by simpa using π.surjective)
    (fun π _ σ _ h => Equiv.ext (congrFun h)) (fun f hf => ?_) (fun π _ => rfl)
  have hs : Function.Surjective f := (Finset.mem_filter.1 hf).2
  exact ⟨Equiv.ofBijective f ⟨Finite.injective_iff_surjective.2 hs, hs⟩, Finset.mem_univ _, rfl⟩

/-- **A5** Polarization (paper line 245), in any non-unital ring:
`∑_{S ⊆ [n]} (-1)^{n-|S|} (∑_{i ∈ S} y_i)^n = L(y_1, …, y_n)`. -/
theorem polarization (n : ℕ) (y : Fin n → R) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, ((-1 : ℤ) ^ (n - S.card)) • nuPow (∑ i ∈ S, y i) n =
      symSum n y := by
  classical
  rw [Finset.powerset_univ]
  simp only [nuPow_finset_sum_eq, Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [polarization_coeff]
  exact sum_surjective_eq_sum_perm n (fun f => tupleProd n (fun k => y (f k)))

end Polarization

/-! ### A6, A9, A10: the polynomial `L` and `T = (L)^T` -/

section SymSum

/-- A multiplicative additive hom commutes with `L`. -/
theorem map_symSum {R S G : Type*} [NonUnitalRing R] [NonUnitalRing S] [FunLike G R S] [MulHomClass G R S]
    [AddMonoidHomClass G R S] (φ : G) (n : ℕ) (y : Fin n → R) :
    φ (symSum n y) = symSum n (fun i => φ (y i)) := by
  rw [symSum, map_sum]
  exact Finset.sum_congr rfl fun π _ => map_tupleProd φ n _

/-- **A6** (F1), paper line 245: `L(y_1, …, y_n) ∈ T` for all `y_i ∈ F⟨X⟩` (no characteristic assumption). -/
theorem F1_symSum_mem_proved (F : Type*) [Field F] (n : ℕ) (_hn : 1 ≤ n) (y : Fin n → FreeNUAlg F) :
    symSum n y ∈ TIdeal F n := by
  rw [← polarization n y]
  exact Submodule.sum_mem _ fun S _ => zsmul_mem (nuPow_mem_TIdeal F n _) _

variable (F : Type*) [Field F]

/-- **A6** `a · L(y) · b ∈ T`. -/
theorem mul_symSum_mul_mem (n : ℕ) (hn : 1 ≤ n) (y : Fin n → FreeNUAlg F) (a b : FreeNUAlg F) :
    a * symSum n y * b ∈ TIdeal F n :=
  (isTIdeal_TIdeal F n).mul_right b _ ((isTIdeal_TIdeal F n).mul_left a _ (F1_symSum_mem_proved F n hn y))

/-- **A6** `a · L(y) ∈ T`. -/
theorem mul_symSum_mem (n : ℕ) (hn : 1 ≤ n) (y : Fin n → FreeNUAlg F) (a : FreeNUAlg F) :
    a * symSum n y ∈ TIdeal F n :=
  (isTIdeal_TIdeal F n).mul_left a _ (F1_symSum_mem_proved F n hn y)

/-- **A6** `L(y) · b ∈ T`. -/
theorem symSum_mul_mem (n : ℕ) (hn : 1 ≤ n) (y : Fin n → FreeNUAlg F) (b : FreeNUAlg F) :
    symSum n y * b ∈ TIdeal F n :=
  (isTIdeal_TIdeal F n).mul_right b _ (F1_symSum_mem_proved F n hn y)

/-- **A9** (F1), paper line 247: `L(x, …, x) = n! x^n`. -/
theorem F1_symSum_diag_proved (F : Type*) [Field F] (n : ℕ) (x : FreeNUAlg F) :
    symSum n (fun _ => x) = (n.factorial : F) • nuPow x n := by
  simp only [symSum, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul F]
  rfl

/-- `x^n` lies in every T-ideal that contains `L(x_0, …, x_{n-1})` (characteristic `0`). -/
theorem nuPow_letter_mem_of_symSum_mem [CharZero F] (n : ℕ) {S : Submodule F (FreeNUAlg F)}
    (hS : IsTIdeal F S) (hL : symSum n (fun i => letter F i) ∈ S) : nuPow (letter F 0) n ∈ S := by
  have h := hS.endo (freeLift F (fun _ => letter F 0)) _ hL
  rw [map_symSum] at h
  simp only [freeLift_letter] at h
  rw [F1_symSum_diag_proved] at h
  have hne : (n.factorial : F) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  simpa [smul_smul, inv_mul_cancel₀ hne] using S.smul_mem (n.factorial : F)⁻¹ h

/-- **A10** (F1), paper line 245: in characteristic `0`, `T = (L)^T`. -/
theorem F1_TIdeal_eq_proved (F : Type*) [Field F] [CharZero F] (n : ℕ) (hn : 1 ≤ n) :
    TIdeal F n = sInf {S | IsTIdeal F S ∧ symSum n (fun i => letter F i) ∈ S} := by
  apply le_antisymm
  · refine TIdeal_le F (isTIdeal_sInf F _) (Submodule.mem_sInf.2 ?_)
    rintro S ⟨hS, hL⟩
    exact nuPow_letter_mem_of_symSum_mem F n hS hL
  · exact sInf_le ⟨isTIdeal_TIdeal F n, F1_symSum_mem_proved F n hn _⟩

end SymSum

/-! ### A7: transfer to algebras with `x^n = 0` (the easy half of [Ro22, Prop. 1.8]) -/

section Transfer

variable (F : Type*) [Field F] (R : Type*) [NonUnitalRing R] [Module F R]

/-- The common kernel of all non-unital algebra homs `F⟨X⟩ → R`. -/
def homKernels : Submodule F (FreeNUAlg F) where
  carrier := {p | ∀ φ : FreeNUAlg F →ₙₐ[F] R, φ p = 0}
  add_mem' {a b} ha hb φ := by rw [map_add, ha φ, hb φ, add_zero]
  zero_mem' φ := map_zero φ
  smul_mem' c p hp φ := by rw [map_smul, hp φ, smul_zero]

theorem mem_homKernels {p : FreeNUAlg F} : p ∈ homKernels F R ↔ ∀ φ : FreeNUAlg F →ₙₐ[F] R, φ p = 0 :=
  Iff.rfl

/-- The common kernel of all homs `F⟨X⟩ → R` is a T-ideal. -/
theorem isTIdeal_homKernels : IsTIdeal F (homKernels F R) where
  mul_left r a ha := (mem_homKernels F R).2 fun φ => by rw [map_mul, (mem_homKernels F R).1 ha φ, mul_zero]
  mul_right r a ha := (mem_homKernels F R).2 fun φ => by rw [map_mul, (mem_homKernels F R).1 ha φ, zero_mul]
  endo ψ a ha := (mem_homKernels F R).2 fun φ => (mem_homKernels F R).1 ha (φ.comp ψ)

variable {F R}

/-- **A7** Transfer: if `x^n = 0` in `R`, every element of `T` is sent to `0` by every hom `F⟨X⟩ → R`. -/
theorem transfer {n : ℕ} (hnil : ∀ x : R, nuPow x n = 0) {p : FreeNUAlg F} (hp : p ∈ TIdeal F n)
    (φ : FreeNUAlg F →ₙₐ[F] R) : φ p = 0 := by
  have hle : TIdeal F n ≤ homKernels F R :=
    TIdeal_le F (isTIdeal_homKernels F R) ((mem_homKernels F R).2 fun ψ => by rw [map_nuPow]; exact hnil _)
  exact (mem_homKernels F R).1 (hle hp) φ

/-- **A7** Corollary: if `x_1 ⋯ x_m ∈ T` and `x^n = 0` in `R`, then `R` satisfies `x_1 ⋯ x_m = 0`. -/
theorem tupleProd_eq_zero_of_mem [IsScalarTower F R R] [SMulCommClass F R R] {n m : ℕ} (_hm : 1 ≤ m)
    (h : firstLettersProd F m ∈ TIdeal F n)
    (hnil : ∀ x : R, nuPow x n = 0) (xs : Fin m → R) : tupleProd m xs = 0 := by
  have key := transfer hnil h (freeLift F (fun i => if hi : i < m then xs ⟨i, hi⟩ else 0))
  rw [firstLettersProd, map_tupleProd] at key
  simpa [freeLift_letter] using key

end Transfer

/-! ### A8: (F0) -/

section F0

variable (F : Type*) [Field F]

/-- Renaming the letters: if `x_0 ⋯ x_{m-1} ∈ T` then every multilinear word of degree `m` lies in `T`. -/
theorem multilinWord_mem_TIdeal {n m : ℕ} (h : firstLettersProd F m ∈ TIdeal F n) (w : Perm (Fin m)) :
    multilinWord F w ∈ TIdeal F n := by
  have key := (isTIdeal_TIdeal F n).endo
    (freeLift F (fun i => if hi : i < m then letter F (w ⟨i, hi⟩) else 0)) _ h
  rw [firstLettersProd, map_tupleProd] at key
  simpa [freeLift_letter, multilinWord] using key

/-- **A8** (F0), paper v1.02 line 169: `x_1 ⋯ x_m ∈ T` iff `W_{n,m} = V_m`. -/
theorem F0_mem_iff_proved (F : Type*) [Field F] (n m : ℕ) (_hm : 1 ≤ m) :
    firstLettersProd F m ∈ TIdeal F n ↔ multilinIdentities F n m = multilinSpace F m := by
  constructor
  · intro h
    refine inf_eq_left.2 (Submodule.span_le.2 ?_)
    rintro _ ⟨w, rfl⟩
    exact multilinWord_mem_TIdeal F h w
  · intro h
    have h1 : firstLettersProd F m ∈ multilinSpace F m := Submodule.subset_span ⟨1, rfl⟩
    rw [← h] at h1
    exact (Submodule.mem_inf.1 h1).2

/-- **A8** Monotonicity: `x_1 ⋯ x_m ∈ T` implies `x_1 ⋯ x_{m+1} ∈ T`. -/
theorem firstLettersProd_succ_mem {n m : ℕ} (hm : 1 ≤ m) (h : firstLettersProd F m ∈ TIdeal F n) :
    firstLettersProd F (m + 1) ∈ TIdeal F n := by
  rw [firstLettersProd, tupleProd_succ m hm]
  exact (isTIdeal_TIdeal F n).mul_right _ _ h

/-- Monotonicity, iterated: `x_1 ⋯ x_m ∈ T` and `m ≤ k` imply `x_1 ⋯ x_k ∈ T`. -/
theorem firstLettersProd_mem_of_le {n m k : ℕ} (hm : 1 ≤ m) (h : firstLettersProd F m ∈ TIdeal F n)
    (hmk : m ≤ k) : firstLettersProd F k ∈ TIdeal F n := by
  induction k, hmk using Nat.le_induction with
  | base => exact h
  | succ k hmk ih => exact firstLettersProd_succ_mem F (hm.trans hmk) ih

/-- **A8** `x_1 ⋯ x_m ∈ T` (with `m ≥ 1`) implies `d(n) ≤ m`. -/
theorem nhIndex_le {n m : ℕ} (hm : 1 ≤ m) (h : firstLettersProd F m ∈ TIdeal F n) : nhIndex F n ≤ m :=
  Nat.sInf_le ⟨hm, h⟩

/-- (F0) `d(n) ≤ m ↔ x_1 ⋯ x_m ∈ T` for `m ≥ 1`, once SOME `x_1 ⋯ x_{m₀}` (`m₀ ≥ 1`) is known to lie in `T`. -/
theorem nhIndex_le_iff_of_mem {n m₀ : ℕ} (hm₀ : 1 ≤ m₀) (h₀ : firstLettersProd F m₀ ∈ TIdeal F n)
    (m : ℕ) (hm : 1 ≤ m) : nhIndex F n ≤ m ↔ firstLettersProd F m ∈ TIdeal F n := by
  refine ⟨fun hle => ?_, nhIndex_le F hm⟩
  obtain ⟨h1, h2⟩ := Nat.sInf_mem (s := {k | 1 ≤ k ∧ firstLettersProd F k ∈ TIdeal F n}) ⟨m₀, hm₀, h₀⟩
  exact firstLettersProd_mem_of_le F h1 h2 hle

end F0

/-! ### A11: the converse half of [Ro22, Prop. 1.8], via the quotient algebra `F⟨X⟩ / T` -/

section Quotient

variable (F : Type u) [Field F] (n : ℕ)

/-- The ring congruence `a ~ b ↔ a - b ∈ T` on `F⟨X⟩`. -/
def tCon : RingCon (FreeNUAlg F) where
  r a b := a - b ∈ TIdeal F n
  iseqv := ⟨fun a => by simp, fun {a b} h => by rw [← neg_sub]; exact neg_mem h,
    fun {a b c} h1 h2 => by rw [← sub_add_sub_cancel a b c]; exact add_mem h1 h2⟩
  add' {a b c d} h1 h2 := by rw [add_sub_add_comm]; exact add_mem h1 h2
  mul' {a b c d} h1 h2 := by
    rw [show a * c - b * d = (a - b) * c + b * (c - d) by noncomm_ring]
    exact add_mem ((isTIdeal_TIdeal F n).mul_right _ _ h1) ((isTIdeal_TIdeal F n).mul_left _ _ h2)

/-- The quotient algebra `F⟨X⟩ / T`. -/
abbrev TQuot : Type u := (tCon F n).Quotient

instance : SMul F (TQuot F n) where
  smul r := Quotient.map' (r • ·) fun a b (h : a - b ∈ TIdeal F n) => by
    show r • a - r • b ∈ TIdeal F n
    rw [← smul_sub]
    exact Submodule.smul_mem _ r h

/-- The quotient map `F⟨X⟩ → F⟨X⟩ / T`, as an additive hom. -/
def tMk : FreeNUAlg F →+ TQuot F n where
  toFun := ((↑) : FreeNUAlg F → TQuot F n)
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module F (TQuot F n) :=
  Function.Surjective.module F (tMk F n) (fun q => Quotient.inductionOn' q fun a => ⟨a, rfl⟩)
    (fun _ _ => rfl)

instance : IsScalarTower F (TQuot F n) (TQuot F n) where
  smul_assoc r x y := Quotient.inductionOn₂' x y fun a b =>
    congrArg ((↑) : FreeNUAlg F → TQuot F n) (smul_mul_assoc r a b)

instance : SMulCommClass F (TQuot F n) (TQuot F n) where
  smul_comm r x y := Quotient.inductionOn₂' x y fun a b =>
    congrArg ((↑) : FreeNUAlg F → TQuot F n) (mul_smul_comm r a b).symm

theorem tQuot_coe_eq_zero (p : FreeNUAlg F) : (p : TQuot F n) = 0 ↔ p ∈ TIdeal F n := by
  show (p : TQuot F n) = ((0 : FreeNUAlg F) : TQuot F n) ↔ _
  rw [RingCon.eq]
  show p - 0 ∈ TIdeal F n ↔ _
  rw [sub_zero]

theorem tQuot_coe_tupleProd (k : ℕ) (x : Fin k → FreeNUAlg F) :
    ((tupleProd k x : FreeNUAlg F) : TQuot F n) = tupleProd k (fun i => (x i : TQuot F n)) :=
  tupleProd_map _ (fun _ _ => rfl) rfl k x

/-- In `F⟨X⟩ / T` every element satisfies `x^n = 0` (because `T` is closed under endomorphisms). -/
theorem tQuot_nuPow_eq_zero (x : TQuot F n) : nuPow x n = 0 :=
  Quotient.inductionOn' x fun p =>
    (tQuot_coe_tupleProd F n n (fun _ => p)).symm.trans ((tQuot_coe_eq_zero F n _).2 (nuPow_mem_TIdeal F n p))

/-- **A11** The converse half of [Ro22, Prop. 1.8]: if every non-unital `F`-algebra (in the universe of `F`)
with `x^n = 0` satisfies `x_1 ⋯ x_m = 0`, then `x_1 ⋯ x_m ∈ T`. -/
theorem mem_TIdeal_of_forall_nil (m : ℕ) (_hm : 1 ≤ m)
    (h : ∀ (R : Type u) [NonUnitalRing R] [Module F R] [IsScalarTower F R R] [SMulCommClass F R R],
      (∀ x : R, nuPow x n = 0) → ∀ xs : Fin m → R, tupleProd m xs = 0) :
    firstLettersProd F m ∈ TIdeal F n := by
  have key := h (TQuot F n) (tQuot_nuPow_eq_zero F n) (fun i => (letter F i : TQuot F n))
  rw [← tQuot_coe_tupleProd] at key
  exact (tQuot_coe_eq_zero F n _).1 key

/-- [Ro22, Prop. 1.8]: `x_1 ⋯ x_m ∈ T` iff every non-unital `F`-algebra with `x^n = 0` satisfies
`x_1 ⋯ x_m = 0`. -/
theorem mem_TIdeal_iff_forall_nil (m : ℕ) (hm : 1 ≤ m) :
    firstLettersProd F m ∈ TIdeal F n ↔
      ∀ (R : Type u) [NonUnitalRing R] [Module F R] [IsScalarTower F R R] [SMulCommClass F R R],
        (∀ x : R, nuPow x n = 0) → ∀ xs : Fin m → R, tupleProd m xs = 0 :=
  ⟨fun h _ _ _ _ _ hnil xs => tupleProd_eq_zero_of_mem hm h hnil xs, mem_TIdeal_of_forall_nil F n m hm⟩

end Quotient

end NagataHigman.Proofs

end
