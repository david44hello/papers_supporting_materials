/-
EulerFlow/Reduction/Split.lean — the algebra of splitting off (Lemma 3.2 of paper 002, tex l.234-269), for maps
into any additive group: the map `L = splitLift` keeps the flow condition at every vertex, makes the ends of
`e, e'` at `v` a balanced pair, is inverted by `splitRes` on the balanced maps, and is additive.
-/
import EulerFlow.Defs.Constructions

namespace EulerFlow

open Finset

namespace MGraph

variable {V E : Type} (G : MGraph V E) [DecidableEq V]

/-! ### Boundary as a sum over edges -/

/-- The contribution of the edge `e` to the boundary at `z` (entering minus leaving). -/
def bdryTerm {M : Type} [AddCommGroup M] (x : E → M) (z : V) (e : E) : M :=
  (if G.tgt e = z then x e else 0) - (if G.src e = z then x e else 0)

/-- The number of ends of `e` at `z`. -/
def endCount (z : V) (e : E) : ℕ := (if G.src e = z then 1 else 0) + (if G.tgt e = z then 1 else 0)

variable [Fintype E]

theorem boundary_eq_sum_bdryTerm {M : Type} [AddCommGroup M] (x : E → M) (z : V) :
    G.boundary x z = ∑ e, G.bdryTerm x z e := by
  simp only [boundary, bdryTerm, Finset.sum_sub_distrib, Finset.sum_filter]

theorem isFlow_iff_boundary {M : Type} [AddCommGroup M] (x : E → M) :
    G.IsFlow x ↔ ∀ z, G.boundary x z = 0 := by
  simp only [IsFlow, boundary, sub_eq_zero]
  exact forall_congr' fun _ => eq_comm

theorem degree_eq_sum_endCount (z : V) : G.degree z = ∑ e, G.endCount z e := by
  rw [degree, Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Fintype.sum_bool, endVertex, endCount, ite_true, Bool.false_eq_true, ite_false, add_comm]

end MGraph

/-! ### Splitting a sum over the edges -/

section SumSplit

variable {E : Type} [DecidableEq E] [Fintype E] {M : Type} [AddCommMonoid M] {e e' : E}

/-- A sum over `E` is the two terms at `e ≠ e'` plus the sum over the other edges. -/
theorem sum_split (hne : e ≠ e') (F : E → M) :
    ∑ x, F x = F e + F e' + ∑ s : {x : E // x ≠ e ∧ x ≠ e'}, F s.1 := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun x => x ≠ e ∧ x ≠ e'), add_comm]
  have hpair : univ.filter (fun x => ¬(x ≠ e ∧ x ≠ e')) = {e, e'} := by
    ext x; simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]; tauto
  rw [hpair, Finset.sum_pair hne, Finset.sum_subtype (p := fun x => x ≠ e ∧ x ≠ e') _ (fun x => by simp)]

end SumSplit

namespace MGraph

variable {V E : Type} {G : MGraph V E} [DecidableEq V] [DecidableEq E] {v : V} {e e' : E}

/-! ### The map `L` on the two split edges -/

section Lift

variable {M : Type} [AddCommGroup M]

theorem splitLift_some (f' : Option {x : E // x ≠ e ∧ x ≠ e'} → M) (s : {x : E // x ≠ e ∧ x ≠ e'}) :
    G.splitLift v e e' f' s.1 = f' (some s) := by
  simp [splitLift, s.2.1, s.2.2]

theorem splitLift_fst (f' : Option {x : E // x ≠ e ∧ x ≠ e'} → M) :
    G.splitLift v e e' f' e = if G.tgt e = v then f' none else -f' none := by
  simp [splitLift]

theorem splitLift_snd (hne : e ≠ e') (f' : Option {x : E // x ≠ e ∧ x ≠ e'} → M) :
    G.splitLift v e e' f' e' = if G.src e' = v then f' none else -f' none := by
  simp [splitLift, Ne.symm hne]

omit [DecidableEq E] in
/-- For a non-loop edge `e` at `v`: its end at `v` is at `v`. -/
theorem endVertex_endAt (he : G.IsAt e v) : G.endVertex (G.endAt e v) = v := by
  unfold endAt endVertex IsAt at *
  split_ifs with h <;> simp_all

/-- In `L f'` the end of `e` at `v` carries the outward value `-x`, `x = f'(g)` (tex l.252). -/
theorem dirVal_splitLift_fst (he : G.IsAt e v) (hl : ¬G.IsLoop e) (f' : Option {x : E // x ≠ e ∧ x ≠ e'} → M) :
    dirVal (G.splitLift v e e' f') (G.endAt e v) = -f' none := by
  unfold IsAt IsLoop at *
  rw [endAt]
  split_ifs with h
  · simp only [dirVal, Bool.false_eq_true, ite_false, splitLift_fst]
    rw [ite_eq_right (fun ht => hl (h.trans ht.symm))]
  · simp only [dirVal, ite_true, splitLift_fst]
    rw [ite_eq_left (he.resolve_left h)]

/-- In `L f'` the end of `e'` at `v` carries the outward value `x` (tex l.252). -/
theorem dirVal_splitLift_snd (hne : e ≠ e') (f' : Option {x : E // x ≠ e ∧ x ≠ e'} → M) :
    dirVal (G.splitLift v e e' f') (G.endAt e' v) = f' none := by
  rw [endAt]
  split_ifs with h
  · simp only [dirVal, Bool.false_eq_true, ite_false, splitLift_snd hne, ite_eq_left h]
  · simp only [dirVal, ite_true, splitLift_snd hne, ite_eq_right h, neg_neg]

/-- `L f'` has the balanced pair formed by the ends of `e` and `e'` at `v` (tex l.252). -/
theorem splitLift_balanced (hne : e ≠ e') (he : G.IsAt e v) (hl : ¬G.IsLoop e) (_he' : G.IsAt e' v)
    (_hl' : ¬G.IsLoop e') (f' : Option {x : E // x ≠ e ∧ x ≠ e'} → M) :
    dirVal (G.splitLift v e e' f') (G.endAt e v) + dirVal (G.splitLift v e e' f') (G.endAt e' v) = 0 := by
  rw [dirVal_splitLift_fst he hl, dirVal_splitLift_snd hne, neg_add_cancel]

/-- The edges `e, e'` of `G` contribute at `z` what the new edge `g` contributes in `G'`. -/
theorem bdryTerm_fst_add_snd (hne : e ≠ e') (he : G.IsAt e v) (hl : ¬G.IsLoop e) (he' : G.IsAt e' v)
    (hl' : ¬G.IsLoop e') (f' : Option {x : E // x ≠ e ∧ x ≠ e'} → M) (z : V) :
    G.bdryTerm (G.splitLift v e e' f') z e + G.bdryTerm (G.splitLift v e e' f') z e' =
      (G.splitOff v e e').bdryTerm f' z none := by
  simp only [bdryTerm, splitLift_fst, splitLift_snd hne, splitOff, otherEnd]
  unfold IsAt IsLoop at *
  rcases he with h1 | h1 <;> rcases he' with h2 | h2 <;>
    · subst h1
      have h3 : G.tgt e ≠ G.src e := fun h => hl h.symm
      have h4 : G.tgt e' ≠ G.src e' := fun h => hl' h.symm
      split_ifs <;> simp_all

/-- Hypotheses of Lemma 3.2: `e ≠ e'` are two edges at `v`, neither a loop. -/
structure SplitData (G : MGraph V E) (v : V) (e e' : E) : Prop where
  ne : e ≠ e'
  at₁ : G.IsAt e v
  at₂ : G.IsAt e' v
  nl₁ : ¬G.IsLoop e
  nl₂ : ¬G.IsLoop e'

variable [Fintype E]

/-- Lemma 3.2 (a), the flow condition (tex l.252-254): the boundary of `L f'` in `G` at `z` is the boundary of
`f'` in `G'` at `z`. -/
theorem boundary_splitLift (hd : SplitData G v e e') (f' : Option {x : E // x ≠ e ∧ x ≠ e'} → M) (z : V) :
    G.boundary (G.splitLift v e e' f') z = (G.splitOff v e e').boundary f' z := by
  rw [boundary_eq_sum_bdryTerm, boundary_eq_sum_bdryTerm, Fintype.sum_option, sum_split hd.ne,
    bdryTerm_fst_add_snd hd.ne hd.at₁ hd.nl₁ hd.at₂ hd.nl₂]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [bdryTerm, splitLift_some, splitOff]
  rfl

theorem isFlow_splitLift_iff (hd : SplitData G v e e') (f' : Option {x : E // x ≠ e ∧ x ≠ e'} → M) :
    G.IsFlow (G.splitLift v e e' f') ↔ (G.splitOff v e e').IsFlow f' := by
  simp only [isFlow_iff_boundary, boundary_splitLift hd]

end Lift

/-! ### The inverse of `L` on balanced maps, linearity, values -/

section Inverse

variable {M : Type} [AddCommGroup M]

/-- The inverse of `L` (tex l.254-256): keep the common values; give `g`, from `u` to `w`, the value of `e` from
`u` to `v`, which is minus the outward value of the end of `e` at `v`. -/
def splitRes (G : MGraph V E) (v : V) (e e' : E) (f : E → M) : Option {x : E // x ≠ e ∧ x ≠ e'} → M :=
  fun o => match o with
  | none => -dirVal f (G.endAt e v)
  | some x => f x.1

theorem splitRes_splitLift (he : G.IsAt e v) (hl : ¬G.IsLoop e) (f' : Option {x : E // x ≠ e ∧ x ≠ e'} → M) :
    G.splitRes v e e' (G.splitLift v e e' f') = f' := by
  funext o
  cases o with
  | none => simp only [splitRes, dirVal_splitLift_fst he hl, neg_neg]
  | some s => simp only [splitRes, splitLift_some]

theorem splitLift_splitRes (hd : SplitData G v e e') (f : E → M)
    (hbal : dirVal f (G.endAt e v) + dirVal f (G.endAt e' v) = 0) :
    G.splitLift v e e' (G.splitRes v e e' f) = f := by
  have hl := hd.nl₁; have hl' := hd.nl₂; have he := hd.at₁; have he' := hd.at₂
  unfold IsAt IsLoop at *
  funext x
  by_cases h : x ≠ e ∧ x ≠ e'
  · simp only [splitLift, dite_eq_left h, splitRes]
  · by_cases hx : x = e
    · subst hx
      rw [splitLift_fst]
      simp only [splitRes, endAt, dirVal]
      rcases he with h1 | h1
      · have : G.tgt x ≠ v := fun ht => hl (h1.trans ht.symm)
        simp [h1, this]
      · have : G.src x ≠ v := fun hs => hl (hs.trans h1.symm)
        simp [h1, this]
    · have hxe' : x = e' := by tauto
      subst hxe'
      rw [splitLift_snd hd.ne]
      have hj : -dirVal f (G.endAt e v) = dirVal f (G.endAt x v) := neg_eq_of_add_eq_zero_right hbal
      simp only [splitRes]
      rw [hj]
      rcases he' with h2 | h2
      · simp [h2, endAt, dirVal]
      · have : G.src x ≠ v := fun hs => hl' (hs.trans h2.symm)
        simp [this, endAt, dirVal]

theorem splitLift_injective (he : G.IsAt e v) (hl : ¬G.IsLoop e) :
    Function.Injective (G.splitLift (A := M) v e e') := fun f' g' h => by
  rw [← splitRes_splitLift he hl f', h, splitRes_splitLift he hl]

theorem splitLift_add (f' g' : Option {x : E // x ≠ e ∧ x ≠ e'} → M) :
    G.splitLift v e e' (f' + g') = G.splitLift v e e' f' + G.splitLift v e e' g' := by
  funext x
  simp only [splitLift, Pi.add_apply]
  split_ifs <;> abel

theorem splitLift_zero : G.splitLift v e e' (0 : Option {x : E // x ≠ e ∧ x ≠ e'} → M) = 0 := by
  funext x
  simp only [splitLift, Pi.zero_apply, neg_zero, dite_eq_ite, ite_self]

/-- `L(t·h') = t·L(h')` for an integer map `h'` (the identity behind tex l.265). -/
theorem splitLift_zsmul (h' : Option {x : E // x ≠ e ∧ x ≠ e'} → ℤ) (t : M) :
    G.splitLift v e e' (fun o => h' o • t) = fun x => G.splitLift v e e' h' x • t := by
  funext x
  simp only [splitLift]
  split_ifs <;> simp [neg_smul]

/-- Every value of `L f'` is a value of `f'` or its negative. -/
theorem splitLift_mem {I : Set M} (hI : ∀ y, y ∈ I → -y ∈ I) (f' : Option {x : E // x ≠ e ∧ x ≠ e'} → M)
    (hf' : ∀ o, f' o ∈ I) (x : E) : G.splitLift v e e' f' x ∈ I := by
  simp only [splitLift]
  split_ifs <;> first | exact hf' _ | exact hI _ (hf' _)

/-- Every value of `f'` is a value of `L f'` or its negative. -/
theorem mem_of_splitLift_mem {I : Set M} (hI : ∀ y, y ∈ I → -y ∈ I)
    (f' : Option {x : E // x ≠ e ∧ x ≠ e'} → M) (hf : ∀ x, G.splitLift v e e' f' x ∈ I) (o) : f' o ∈ I := by
  cases o with
  | some s => have h := hf s.1; rwa [splitLift_some] at h
  | none =>
    have h := hf e
    rw [splitLift_fst] at h
    split_ifs at h
    · exact h
    · simpa using hI _ h

/-- Lemma 3.2 (a) for `I`-flows: `L f'` is an `I`-flow of `G` iff `f'` is an `I`-flow of `G'`. -/
theorem isIFlow_splitLift_iff [Fintype E] {I : Set M} (hI : ∀ y, y ∈ I → -y ∈ I) (hd : SplitData G v e e')
    (f' : Option {x : E // x ≠ e ∧ x ≠ e'} → M) :
    G.IsIFlow I (G.splitLift v e e' f') ↔ (G.splitOff v e e').IsIFlow I f' := by
  rw [IsIFlow, IsIFlow, isFlow_splitLift_iff hd]
  exact and_congr Iff.rfl ⟨mem_of_splitLift_mem hI f', splitLift_mem hI f'⟩

end Inverse

/-! ### Degrees after splitting off (tex l.408-410) -/

omit [DecidableEq E] in
/-- The edges `e, e'` have, together, the ends of `g` and two more ends at `v`. -/
theorem endCount_fst_add_snd (hd : SplitData G v e e') (z : V) :
    G.endCount z e + G.endCount z e' = (G.splitOff v e e').endCount z none + (if v = z then 2 else 0) := by
  have hl := hd.nl₁; have hl' := hd.nl₂; have he := hd.at₁; have he' := hd.at₂
  simp only [endCount, splitOff, otherEnd]
  unfold IsAt IsLoop at *
  rcases he with h1 | h1 <;> rcases he' with h2 | h2 <;> subst h1 <;>
    split_ifs <;> simp_all

/-- Splitting off lowers the degree of `v` by `2` and keeps the other degrees. -/
theorem degree_splitOff [Fintype E] (hd : SplitData G v e e') (z : V) :
    (G.splitOff v e e').degree z + (if v = z then 2 else 0) = G.degree z := by
  rw [degree_eq_sum_endCount, degree_eq_sum_endCount, Fintype.sum_option, sum_split hd.ne,
    endCount_fst_add_snd hd]
  have : ∑ s : {x : E // x ≠ e ∧ x ≠ e'}, (G.splitOff v e e').endCount z (some s) =
      ∑ s : {x : E // x ≠ e ∧ x ≠ e'}, G.endCount z s.1 := by
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [endCount, splitOff]
    rfl
  rw [this]; ring

end MGraph

end EulerFlow
