/-
NagataHigman/Proofs/BaseChange.lean — field transfer of T-ideal membership ℂ → ℚ → F (char 0).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Route. (a) For a field hom `f : K → K'`, the coefficient map `coeffMap f : K⟨X⟩ → K'⟨X⟩` sends `T_K` into `T_{K'}`
(its preimage of `T_{K'}` is a T-ideal over `K` containing `x^n`). (b) For a char-0 field `K`, let
`ι = coeffMap (ℚ → K)` and `S = K-span of ι(T_ℚ)`. `S` is a T-ideal over `K` (for endomorphism closure: the
`g ∈ ℚ⟨X⟩` with `φ(ι g) ∈ S` for all `K`-endomorphisms `φ` form a `ℚ`-T-ideal containing `L(x_0, …, x_{n-1})`,
by multilinearity of `L`; then (F1) over ℚ). So `T_K ⊆ S`. (c) A `ℚ`-linear `λ : K → ℚ` with `λ 1 = 1`, applied to
coefficients, maps `c • ι g` to `λ(c) • g`, hence maps `S` into `T_ℚ` and `x_0 ⋯ x_{m-1}` to itself.
-/
import Mathlib
import NagataHigman.Defs.Spanning
import NagataHigman.Proofs.FreeAlgebraLayer

noncomputable section

namespace NagataHigman.Proofs

open NagataHigman Equiv Finset MonoidAlgebra

/-! ### Multilinearity of `L` -/

section Multilinear

variable {K : Type*} [Field K] {R : Type*} [NonUnitalRing R] [Module K R] [IsScalarTower K R R]
  [SMulCommClass K R R]

/-- Scalars pull out of `tupleProd`. -/
theorem tupleProd_smul : ∀ (m : ℕ) (c : Fin m → K) (z : Fin m → R),
    tupleProd m (fun k => c k • z k) = (∏ k, c k) • tupleProd m z
  | 0, _, _ => by simp [tupleProd_zero]
  | 1, c, z => by simp [tupleProd_one]
  | (m + 2), c, z => by
      rw [tupleProd_succ_succ, tupleProd_succ_succ,
        tupleProd_smul (m + 1) (fun i => c i.castSucc) (fun i => z i.castSucc), Fin.prod_univ_castSucc c,
        smul_mul_smul_comm]

/-- Multilinearity of `L`: expand every argument in one finite family `e`. -/
theorem symSum_sum_smul {J : Type*} [Fintype J] (n : ℕ) (c : Fin n → J → K) (e : J → R) :
    symSum n (fun i => ∑ j, c i j • e j) =
      ∑ g : Fin n → J, (∏ i, c i (g i)) • symSum n (fun i => e (g i)) := by
  simp only [symSum, Finset.smul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [tupleProd_sum_pi n (fun k j => c (π k) j • e j)]
  simp only [tupleProd_smul]
  refine Fintype.sum_equiv (Equiv.arrowCongr π (Equiv.refl J)) _ _ fun f => ?_
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq, Equiv.symm_apply_apply]
  rw [← Equiv.prod_comp π (fun i => c i (f (π.symm i)))]
  simp only [Equiv.symm_apply_apply]

end Multilinear

/-! ### `L` of arbitrary arguments lies in any subspace containing `L` of words -/

section Words

variable {K : Type*} [Field K]

/-- Every `a ∈ K⟨X⟩` is the sum of its terms over any finset of words containing its support. -/
theorem eq_sum_smul_single (a : FreeNUAlg K) (s : Finset (FreeSemigroup ℕ)) (hs : a.coeff.support ⊆ s) :
    a = ∑ w : s, a.coeff w • single (w : FreeSemigroup ℕ) (1 : K) := by
  conv_lhs => rw [← sum_coeff_single a]
  rw [Finsupp.sum_of_support_subset _ hs _ (fun w _ => single_zero w), ← Finset.sum_coe_sort s]
  simp only [smul_single', mul_one]

/-- If `M` contains `L(w_1, …, w_n)` for all words `w_i`, it contains `L(y_1, …, y_n)` for all `y_i`. -/
theorem symSum_mem_of_words {n : ℕ} (M : Submodule K (FreeNUAlg K))
    (hM : ∀ w : Fin n → FreeSemigroup ℕ, symSum n (fun i => single (w i) (1 : K)) ∈ M)
    (y : Fin n → FreeNUAlg K) : symSum n y ∈ M := by
  classical
  let s := Finset.univ.biUnion (fun i => (y i).coeff.support)
  have hy : symSum n y = symSum n (fun i => ∑ w : s, (y i).coeff w • single (w : FreeSemigroup ℕ) (1 : K)) :=
    congrArg (symSum n) (funext fun i =>
      eq_sum_smul_single (y i) s
        (Finset.subset_biUnion_of_mem (fun i => (y i).coeff.support) (Finset.mem_univ i)))
  rw [hy, symSum_sum_smul]
  exact Submodule.sum_mem _ fun g _ => M.smul_mem _ (hM _)

end Words

/-! ### (a) Coefficient maps along field homs preserve the T-ideal -/

section CoeffMap

variable {K K' : Type*} [Field K] [Field K']

/-- The coefficient map `K⟨X⟩ → K'⟨X⟩` along a field hom `f`. -/
def coeffMap (f : K →+* K') : FreeNUAlg K →ₙ+* FreeNUAlg K' where
  toFun := MonoidAlgebra.map (f : K →+ K')
  map_mul' := MonoidAlgebra.map_mul f
  map_zero' := MonoidAlgebra.map_zero _
  map_add' := MonoidAlgebra.map_add _

theorem coeff_coeffMap (f : K →+* K') (a : FreeNUAlg K) (w : FreeSemigroup ℕ) :
    (coeffMap f a).coeff w = f (a.coeff w) := rfl

theorem coeffMap_single (f : K →+* K') (w : FreeSemigroup ℕ) (c : K) :
    coeffMap f (single w c) = single w (f c) :=
  MonoidAlgebra.map_single _ _ _

theorem coeffMap_letter (f : K →+* K') (i : ℕ) : coeffMap f (letter K i) = letter K' i := by
  rw [letter, letter, coeffMap_single, map_one]

theorem coeffMap_smul (f : K →+* K') (c : K) (a : FreeNUAlg K) : coeffMap f (c • a) = f c • coeffMap f a := by
  ext w
  simp only [coeff_coeffMap, coeff_smul_apply, smul_eq_mul, map_mul]

theorem coeffMap_firstLettersProd (f : K →+* K') (m : ℕ) :
    coeffMap f (firstLettersProd K m) = firstLettersProd K' m := by
  rw [firstLettersProd, map_tupleProd]
  simp only [coeffMap_letter, firstLettersProd]

theorem coeffMap_nuPow_letter (f : K →+* K') (n : ℕ) :
    coeffMap f (nuPow (letter K 0) n) = nuPow (letter K' 0) n := by
  rw [map_nuPow, coeffMap_letter]

/-- The `K'`-endomorphism of `K'⟨X⟩` whose values on letters are those of `φ`, coefficients mapped by `f`. -/
def extendEndo (f : K →+* K') (φ : FreeNUAlg K →ₙₐ[K] FreeNUAlg K) : FreeNUAlg K' →ₙₐ[K'] FreeNUAlg K' :=
  freeLift K' (fun i => coeffMap f (φ (letter K i)))

theorem coeffMap_endo_single_one (f : K →+* K') (φ : FreeNUAlg K →ₙₐ[K] FreeNUAlg K) (w : FreeSemigroup ℕ) :
    coeffMap f (φ (single w 1)) = extendEndo f φ (coeffMap f (single w 1)) := by
  have hl : ∀ i, coeffMap f (φ (letter K i)) = extendEndo f φ (coeffMap f (letter K i)) := fun i => by
    rw [coeffMap_letter, extendEndo, freeLift_letter]
  induction w using FreeSemigroup.recOnMul with
  | ih1 i => exact hl i
  | ih2 i w _ hw =>
      rw [← one_mul (1 : K), ← single_mul_single, map_mul, map_mul, map_mul, map_mul, hw]
      exact congrArg (· * extendEndo f φ (coeffMap f (single w 1))) (hl i)

/-- `ι ∘ φ = φ_{K'} ∘ ι`: the coefficient map intertwines `φ` with its extension. -/
theorem coeffMap_endo (f : K →+* K') (φ : FreeNUAlg K →ₙₐ[K] FreeNUAlg K) (a : FreeNUAlg K) :
    coeffMap f (φ a) = extendEndo f φ (coeffMap f a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single w c =>
      rw [show single w c = c • single w (1 : K) by rw [smul_single', mul_one], map_smul, coeffMap_smul,
        coeffMap_smul, map_smul, coeffMap_endo_single_one]

/-- The `K`-subspace of the `a` with `coeffMap f a ∈ T_{K'}`. -/
def pullTIdeal (f : K →+* K') (n : ℕ) : Submodule K (FreeNUAlg K) where
  carrier := {a | coeffMap f a ∈ TIdeal K' n}
  add_mem' {a b} ha hb := by
    show coeffMap f (a + b) ∈ TIdeal K' n
    rw [map_add]
    exact add_mem ha hb
  zero_mem' := by
    show coeffMap f 0 ∈ TIdeal K' n
    rw [map_zero]
    exact zero_mem _
  smul_mem' c a ha := by
    show coeffMap f (c • a) ∈ TIdeal K' n
    rw [coeffMap_smul]
    exact Submodule.smul_mem _ _ ha

theorem mem_pullTIdeal {f : K →+* K'} {n : ℕ} {a : FreeNUAlg K} :
    a ∈ pullTIdeal f n ↔ coeffMap f a ∈ TIdeal K' n := Iff.rfl

theorem isTIdeal_pullTIdeal (f : K →+* K') (n : ℕ) : IsTIdeal K (pullTIdeal f n) where
  mul_left r a ha := by
    rw [mem_pullTIdeal, map_mul]
    exact (isTIdeal_TIdeal K' n).mul_left _ _ ha
  mul_right r a ha := by
    rw [mem_pullTIdeal, map_mul]
    exact (isTIdeal_TIdeal K' n).mul_right _ _ ha
  endo φ a ha := by
    rw [mem_pullTIdeal, coeffMap_endo]
    exact (isTIdeal_TIdeal K' n).endo _ _ ha

/-- **(a)** The coefficient map along any field hom sends `T_K` into `T_{K'}`. -/
theorem coeffMap_mem_TIdeal (f : K →+* K') (n : ℕ) {a : FreeNUAlg K} (ha : a ∈ TIdeal K n) :
    coeffMap f a ∈ TIdeal K' n :=
  TIdeal_le K (isTIdeal_pullTIdeal f n)
    (by rw [mem_pullTIdeal, coeffMap_nuPow_letter]; exact nuPow_letter_mem_TIdeal K' n) ha

end CoeffMap

/-! ### (b) In char 0, `T_K` lies in the `K`-span of `ι(T_ℚ)` -/

section Span

variable (K : Type*) [Field K] [CharZero K]

/-- `S = K`-span of `ι(T_ℚ)`, `ι = coeffMap (ℚ → K)`. -/
def ratSpan (n : ℕ) : Submodule K (FreeNUAlg K) :=
  Submodule.span K (coeffMap (algebraMap ℚ K) '' (TIdeal ℚ n : Set (FreeNUAlg ℚ)))

variable {K}

theorem coeffMap_mem_ratSpan {n : ℕ} {g : FreeNUAlg ℚ} (hg : g ∈ TIdeal ℚ n) :
    coeffMap (algebraMap ℚ K) g ∈ ratSpan K n :=
  Submodule.subset_span ⟨g, hg, rfl⟩

theorem single_mul_mem_ratSpan {n : ℕ} (w : FreeSemigroup ℕ) (c : K) {g : FreeNUAlg ℚ} (hg : g ∈ TIdeal ℚ n) :
    single w c * coeffMap (algebraMap ℚ K) g ∈ ratSpan K n := by
  have h : single w c * coeffMap (algebraMap ℚ K) g = c • coeffMap (algebraMap ℚ K) (single w 1 * g) := by
    rw [map_mul, coeffMap_single, map_one, ← smul_mul_assoc, smul_single', mul_one]
  rw [h]
  exact Submodule.smul_mem _ _ (coeffMap_mem_ratSpan ((isTIdeal_TIdeal ℚ n).mul_left _ _ hg))

theorem mul_single_mem_ratSpan {n : ℕ} (w : FreeSemigroup ℕ) (c : K) {g : FreeNUAlg ℚ} (hg : g ∈ TIdeal ℚ n) :
    coeffMap (algebraMap ℚ K) g * single w c ∈ ratSpan K n := by
  have h : coeffMap (algebraMap ℚ K) g * single w c = c • coeffMap (algebraMap ℚ K) (g * single w 1) := by
    rw [map_mul, coeffMap_single, map_one, ← mul_smul_comm, smul_single', mul_one]
  rw [h]
  exact Submodule.smul_mem _ _ (coeffMap_mem_ratSpan ((isTIdeal_TIdeal ℚ n).mul_right _ _ hg))

theorem ratSpan_mul_left {n : ℕ} (r : FreeNUAlg K) {x : FreeNUAlg K} (hx : x ∈ ratSpan K n) :
    r * x ∈ ratSpan K n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      induction r using MonoidAlgebra.induction_linear with
      | zero => rw [zero_mul]; exact zero_mem _
      | add p q hp hq => rw [add_mul]; exact add_mem hp hq
      | single w c => exact single_mul_mem_ratSpan w c hg
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

theorem ratSpan_mul_right {n : ℕ} (r : FreeNUAlg K) {x : FreeNUAlg K} (hx : x ∈ ratSpan K n) :
    x * r ∈ ratSpan K n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      induction r using MonoidAlgebra.induction_linear with
      | zero => rw [mul_zero]; exact zero_mem _
      | add p q hp hq => rw [mul_add]; exact add_mem hp hq
      | single w c => exact mul_single_mem_ratSpan w c hg
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

/-- `L(y_1, …, y_n) ∈ S` for all `y_i ∈ K⟨X⟩` (multilinearity of `L` and (F1) over ℚ). -/
theorem symSum_mem_ratSpan {n : ℕ} (hn : 1 ≤ n) (y : Fin n → FreeNUAlg K) : symSum n y ∈ ratSpan K n := by
  refine symSum_mem_of_words _ (fun w => ?_) y
  have h : symSum n (fun i => single (w i) (1 : K)) =
      coeffMap (algebraMap ℚ K) (symSum n (fun i => single (w i) (1 : ℚ))) := by
    rw [map_symSum]
    simp only [coeffMap_single, map_one]
  rw [h]
  exact coeffMap_mem_ratSpan (F1_symSum_mem_proved ℚ n hn _)

variable (K) in
/-- `{g ∈ ℚ⟨X⟩ : φ(ι g) ∈ S for every K-endomorphism φ of K⟨X⟩}`. -/
def endoPull (n : ℕ) : Submodule ℚ (FreeNUAlg ℚ) where
  carrier := {g | ∀ φ : FreeNUAlg K →ₙₐ[K] FreeNUAlg K, φ (coeffMap (algebraMap ℚ K) g) ∈ ratSpan K n}
  add_mem' {a b} ha hb := by
    intro φ
    rw [map_add, map_add]
    exact add_mem (ha φ) (hb φ)
  zero_mem' := by
    intro φ
    rw [map_zero, map_zero]
    exact zero_mem _
  smul_mem' q g hg := by
    intro φ
    rw [coeffMap_smul, map_smul]
    exact Submodule.smul_mem _ _ (hg φ)

theorem mem_endoPull {n : ℕ} {g : FreeNUAlg ℚ} :
    g ∈ endoPull K n ↔ ∀ φ : FreeNUAlg K →ₙₐ[K] FreeNUAlg K, φ (coeffMap (algebraMap ℚ K) g) ∈ ratSpan K n :=
  Iff.rfl

theorem isTIdeal_endoPull (n : ℕ) : IsTIdeal ℚ (endoPull K n) where
  mul_left r g hg := mem_endoPull.2 fun φ => by
    rw [map_mul, map_mul]
    exact ratSpan_mul_left _ (mem_endoPull.1 hg φ)
  mul_right r g hg := mem_endoPull.2 fun φ => by
    rw [map_mul, map_mul]
    exact ratSpan_mul_right _ (mem_endoPull.1 hg φ)
  endo ψ g hg := mem_endoPull.2 fun φ => by
    rw [coeffMap_endo]
    exact mem_endoPull.1 hg (φ.comp (extendEndo (algebraMap ℚ K) ψ))

theorem symSum_letter_mem_endoPull {n : ℕ} (hn : 1 ≤ n) :
    symSum n (fun i => letter ℚ i) ∈ endoPull K n := mem_endoPull.2 fun φ => by
  rw [map_symSum, map_symSum]
  exact symSum_mem_ratSpan hn _

/-- `φ(ι g) ∈ S` for every `g ∈ T_ℚ` and every `K`-endomorphism `φ` ((F1) over ℚ). -/
theorem TIdeal_rat_le_endoPull {n : ℕ} (hn : 1 ≤ n) : TIdeal ℚ n ≤ endoPull K n := by
  rw [F1_TIdeal_eq_proved ℚ n hn]
  exact sInf_le ⟨isTIdeal_endoPull n, symSum_letter_mem_endoPull hn⟩

theorem isTIdeal_ratSpan {n : ℕ} (hn : 1 ≤ n) : IsTIdeal K (ratSpan K n) where
  mul_left r _ hx := ratSpan_mul_left r hx
  mul_right r _ hx := ratSpan_mul_right r hx
  endo φ x hx := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨g, hg, rfl⟩ := hx
        exact mem_endoPull.1 (TIdeal_rat_le_endoPull hn hg) φ
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/-- **(b)** In characteristic `0`, `T_K ⊆ K`-span of `ι(T_ℚ)`. -/
theorem TIdeal_le_ratSpan {n : ℕ} (hn : 1 ≤ n) : TIdeal K n ≤ ratSpan K n :=
  TIdeal_le K (isTIdeal_ratSpan hn)
    (by rw [← coeffMap_nuPow_letter (algebraMap ℚ K)]; exact coeffMap_mem_ratSpan (nuPow_letter_mem_TIdeal ℚ n))

end Span

/-! ### (c) Descent `K → ℚ` by a `ℚ`-linear functional -/

section Descent

variable {K : Type*} [Field K] [CharZero K]

/-- A `ℚ`-linear functional `λ : K → ℚ`, applied to every coefficient. -/
def coeffProj (lam : K →ₗ[ℚ] ℚ) : FreeNUAlg K →+ FreeNUAlg ℚ where
  toFun := MonoidAlgebra.map lam.toAddMonoidHom
  map_zero' := MonoidAlgebra.map_zero _
  map_add' := MonoidAlgebra.map_add _

theorem coeffProj_smul_coeffMap (lam : K →ₗ[ℚ] ℚ) (c : K) (g : FreeNUAlg ℚ) :
    coeffProj lam (c • coeffMap (algebraMap ℚ K) g) = lam c • g := by
  ext w
  show lam (c * algebraMap ℚ K (g.coeff w)) = lam c * g.coeff w
  rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

/-- The `K`-subspace of the `x` all of whose `K`-multiples project into `T_ℚ`. -/
def projPull (lam : K →ₗ[ℚ] ℚ) (n : ℕ) : Submodule K (FreeNUAlg K) where
  carrier := {x | ∀ c : K, coeffProj lam (c • x) ∈ TIdeal ℚ n}
  add_mem' {a b} ha hb := by
    intro c
    rw [smul_add, map_add]
    exact add_mem (ha c) (hb c)
  zero_mem' := by
    intro c
    rw [smul_zero, map_zero]
    exact zero_mem _
  smul_mem' d x hx := by
    intro c
    rw [smul_smul]
    exact hx (c * d)

theorem ratSpan_le_projPull (lam : K →ₗ[ℚ] ℚ) (n : ℕ) : ratSpan K n ≤ projPull lam n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, hg, rfl⟩ c
  rw [coeffProj_smul_coeffMap]
  exact Submodule.smul_mem _ _ hg

variable (K) in
/-- A `ℚ`-linear functional `λ : K → ℚ` with `λ 1 = 1` (a left inverse of `ℚ → K`). -/
theorem exists_rat_functional : ∃ lam : K →ₗ[ℚ] ℚ, lam 1 = 1 := by
  obtain ⟨g, hg⟩ := (Algebra.linearMap ℚ K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (algebraMap ℚ K).injective)
  exact ⟨g, by simpa using LinearMap.congr_fun hg 1⟩

/-- **(c)** Descent: in characteristic `0`, `x_0 ⋯ x_{m-1} ∈ T_K` implies `x_0 ⋯ x_{m-1} ∈ T_ℚ`. -/
theorem mem_TIdeal_rat_of_mem (n m : ℕ) (hn : 1 ≤ n) (K : Type*) [Field K] [CharZero K]
    (h : firstLettersProd K m ∈ TIdeal K n) : firstLettersProd ℚ m ∈ TIdeal ℚ n := by
  obtain ⟨lam, hlam⟩ := exists_rat_functional K
  have h1 := ratSpan_le_projPull lam n (TIdeal_le_ratSpan hn h) 1
  rwa [← coeffMap_firstLettersProd (algebraMap ℚ K) m, coeffProj_smul_coeffMap, hlam, one_smul] at h1

end Descent

/-! ### The transfer -/

/-- Transfer between any two fields of characteristic `0`. -/
theorem mem_TIdeal_transfer (n m : ℕ) (hn : 1 ≤ n) (K F : Type*) [Field K] [CharZero K] [Field F] [CharZero F]
    (h : firstLettersProd K m ∈ TIdeal K n) : firstLettersProd F m ∈ TIdeal F n := by
  have h1 := coeffMap_mem_TIdeal (algebraMap ℚ F) n (mem_TIdeal_rat_of_mem n m hn K h)
  rwa [coeffMap_firstLettersProd] at h1

/-- **Section 4.1, field step**: `x_0 ⋯ x_{m-1} ∈ T` over ℂ implies the same over every field of
characteristic `0`. -/
theorem mem_TIdeal_of_complex (n m : ℕ) (hn : 1 ≤ n) (F : Type*) [Field F] [CharZero F]
    (h : firstLettersProd ℂ m ∈ TIdeal ℂ n) : firstLettersProd F m ∈ TIdeal F n :=
  mem_TIdeal_transfer n m hn ℂ F h

end NagataHigman.Proofs

end
