/-
NagataHigman/Proofs/Arcs.lean — package B: the "arcs" combinatorics of Proposition 2.1, steps (1)-(6).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Paper v1.10, lines 318-382.
-/
import Mathlib
import NagataHigman.Defs.FreeAlgebra
import NagataHigman.Defs.Spanning
import NagataHigman.Defs.GroupAlgebra
import NagataHigman.Defs.WordCycle

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace NagataHigman.Proofs.Arcs

open Equiv List

/-! ## 1. General lists and permutations -/

section General

variable {α : Type*} [DecidableEq α]

/-- `σ` follows the list `l`: it maps every entry of `l` (but the last) to the next entry. -/
def Follows (σ : Perm α) (l : List α) : Prop := List.IsChain (fun x y => σ x = y) l

theorem follows_formPerm {D : List α} (hD : D.Nodup) : Follows (formPerm D) D := by
  unfold Follows
  rw [isChain_iff_getElem]
  intro i hi
  exact formPerm_apply_lt_getElem D hD i hi

theorem Follows.infix {σ : Perm α} {l l₁ : List α} (h : Follows σ l) (h' : l₁ <:+: l) :
    Follows σ l₁ :=
  List.IsChain.infix h h'

theorem Follows.apply {σ : Perm α} {P S : List α} {x y : α} (h : Follows σ (P ++ x :: y :: S)) :
    σ x = y := by
  have h2 : Follows σ [x, y] := h.infix ⟨P, S, by simp⟩
  exact (isChain_pair (R := fun a b => σ a = b)).mp h2

/-- Two permutations that agree off one point are equal. -/
theorem perm_eq_of_eq_off_point {σ τ : Perm α} (z : α) (h : ∀ x, x ≠ z → σ x = τ x) : σ = τ := by
  ext x
  by_cases hx : x = z
  · subst hx
    by_contra hne
    have hσy : σ (σ.symm (τ x)) = τ x := by simp
    have hyx : σ.symm (τ x) ≠ x := by
      intro h'
      rw [h'] at hσy
      exact hne hσy
    exact hyx (τ.injective ((h _ hyx).symm.trans hσy))
  · exact h x hx

theorem exists_split_of_mem_dropLast {l : List α} {x : α} (hx : x ∈ l.dropLast) :
    ∃ P S y, l = P ++ x :: y :: S := by
  have hl : l ≠ [] := by rintro rfl; simp at hx
  obtain ⟨P, T, hPT⟩ := List.append_of_mem hx
  have e := dropLast_append_getLast hl
  rw [hPT] at e
  rcases T with _ | ⟨t, T'⟩
  · exact ⟨P, [], l.getLast hl, e.symm.trans (by simp)⟩
  · exact ⟨P, T' ++ [l.getLast hl], t, e.symm.trans (by simp)⟩

theorem mem_tail_of_ne_head {l : List α} {y : α} (hy : y ∈ l) (hh : l.head? ≠ some y) : y ∈ l.tail := by
  rcases l with _ | ⟨a, t⟩
  · simp at hy
  · simp only [head?_cons, ne_eq, Option.some.injEq] at hh
    simp only [tail_cons]
    rcases List.mem_cons.mp hy with rfl | h
    · exact absurd rfl hh
    · exact h

theorem exists_split_of_mem_tail {l : List α} {y : α} (hy : y ∈ l.tail) :
    ∃ P S x, l = P ++ x :: y :: S := by
  rcases l with _ | ⟨x, T⟩
  · simp at hy
  · obtain ⟨P, S, hPS⟩ := List.append_of_mem hy
    simp only [tail_cons] at hPS
    subst hPS
    rcases List.eq_nil_or_concat P with rfl | ⟨P', p, rfl⟩
    · exact ⟨[], S, x, by simp⟩
    · exact ⟨x :: P', S, p, by simp⟩

/-- In a nodup list, an entry that is followed by another entry is not the last entry. -/
theorem getLast_ne_of_split {l P S : List α} {x y : α} (hnd : l.Nodup) (hl : l = P ++ x :: y :: S)
    (hne : l ≠ []) : l.getLast hne ≠ x := by
  subst hl
  have hmem : (P ++ x :: y :: S).getLast hne ∈ y :: S := by
    rw [List.getLast_append_of_ne_nil _ (by simp), List.getLast_cons (by simp)]
    exact List.getLast_mem _
  have hx : x ∉ y :: S := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
  intro h
  exact hx (h ▸ hmem)

theorem follows_of_agree {σ τ : Perm α} {X : Finset α} (h : ∀ x, x ∉ X → σ x = τ x) :
    ∀ {B : List α}, Follows τ B → (∀ x ∈ B.dropLast, x ∉ X) → Follows σ B
  | [], _, _ => List.IsChain.nil
  | [a], _, _ => List.IsChain.singleton a
  | a :: b :: l, hB, hin => by
    unfold Follows at hB ⊢
    rw [isChain_cons_cons] at hB ⊢
    refine ⟨?_, follows_of_agree h hB.2 ?_⟩
    · rw [h a (hin a (by simp))]
      exact hB.1
    · intro x hx
      exact hin x (by simp [hx])

theorem block_infix {B0 B : List α} {Bs : List (List α)} (hB : B = B0 ∨ B ∈ Bs) :
    B <:+: B0 ++ Bs.flatten := by
  rcases hB with rfl | hB
  · exact (List.prefix_append _ _).isInfix
  · obtain ⟨L1, L2, rfl⟩ := List.append_of_mem hB
    exact ⟨B0 ++ L1.flatten, L2.flatten, by simp⟩

theorem orbit_subset {σ : Perm α} {S : List α} (hS : ∀ x ∈ S, σ x ∈ S) {x : α} (hx : x ∈ S) (i : ℕ) :
    (σ ^ i) x ∈ S := by
  induction i with
  | zero => simpa using hx
  | succ i ih =>
    rw [pow_succ', Perm.mul_apply]
    exact hS _ ih

/-- `formPerm` is injective on nodup lists of equal length with equal heads. -/
theorem formPerm_inj {l₁ l₂ : List α} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (hlen : l₁.length = l₂.length)
    (hhead : l₁.head? = l₂.head?) (h : formPerm l₁ = formPerm l₂) : l₁ = l₂ := by
  rcases l₁ with _ | ⟨x₁, r₁⟩ <;> rcases l₂ with _ | ⟨x₂, r₂⟩
  · rfl
  · simp at hlen
  · simp at hlen
  simp only [head?_cons, Option.some.injEq] at hhead
  subst hhead
  apply List.ext_getElem hlen
  intro i hi₁ hi₂
  have e₁ := formPerm_pow_apply_getElem (x₁ :: r₁) h₁ i 0 (by simp)
  have e₂ := formPerm_pow_apply_getElem (x₁ :: r₂) h₂ i 0 (by simp)
  simp only [List.getElem_cons_zero, zero_add, Nat.mod_eq_of_lt hi₁] at e₁
  simp only [List.getElem_cons_zero, zero_add, Nat.mod_eq_of_lt hi₂] at e₂
  rw [← e₁, ← e₂, h]

/-- A list that is a permutation of `ofFn f`, `f` injective, is `ofFn (f ∘ π)` for a permutation `π`. -/
theorem exists_perm_of_perm_ofFn {β : Type*} {n : ℕ} {f : Fin n → β} (hf : Function.Injective f)
    {l : List β} (h : l.Perm (List.ofFn f)) : ∃ π : Perm (Fin n), l = List.ofFn (f ∘ π) := by
  have hlen : l.length = n := by simpa using h.length_eq
  have hmem : ∀ i : Fin n, ∃ j, f j = l[i.1]'(by omega) := fun i => by
    have : l[i.1]'(by omega) ∈ List.ofFn f := h.mem_iff.mp (List.getElem_mem _)
    simpa [List.mem_ofFn] using this
  choose g hg using hmem
  have hnd : l.Nodup := h.nodup_iff.mpr (List.nodup_ofFn.mpr hf)
  have hinj : Function.Injective g := by
    intro i i' hii'
    have e : l[i.1]'(by omega) = l[i'.1]'(by omega) := by rw [← hg, ← hg, hii']
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp e)
  refine ⟨Equiv.ofBijective g hinj.bijective_of_finite, ?_⟩
  apply List.ext_getElem (by simp [hlen])
  intro i h1 h2
  simp [hg]

/-- Lists of nonempty blocks with a nodup concatenation: equal concatenations of two orderings of the same
blocks force the orderings to be equal. -/
theorem eq_of_perm_of_flatten_eq :
    ∀ {Ls₁ Ls₂ : List (List α)}, Ls₁.Perm Ls₂ → (∀ B ∈ Ls₁, B ≠ []) → Ls₁.flatten.Nodup →
      Ls₁.flatten = Ls₂.flatten → Ls₁ = Ls₂
  | [], Ls₂, hp, _, _, _ => (List.Perm.nil_eq hp)
  | B :: R₁, [], hp, _, _, _ => absurd hp.length_eq (by simp)
  | B :: R₁, C :: R₂, hp, hne, hnd, hfl => by
    have hC : C ∈ B :: R₁ := hp.mem_iff.mpr (List.mem_cons_self)
    have hCne : C ≠ [] := hne C hC
    have hBne : B ≠ [] := hne B List.mem_cons_self
    simp only [flatten_cons] at hfl hnd
    have hheads : B.head? = C.head? := by
      rcases B with _ | ⟨b, B'⟩
      · exact absurd rfl hBne
      rcases C with _ | ⟨c, C'⟩
      · exact absurd rfl hCne
      simp only [cons_append, cons.injEq] at hfl
      simp [hfl.1]
    have hCB : C = B := by
      rcases List.mem_cons.mp hC with h | h
      · exact h
      · exfalso
        obtain ⟨c, hc⟩ : ∃ c, C.head? = some c := Option.isSome_iff_exists.mp (by simpa using hCne)
        have hcC : c ∈ C := List.mem_of_mem_head? hc
        have hcB : c ∈ B := List.mem_of_mem_head? (hheads.trans hc)
        exact (List.nodup_append.mp hnd).2.2 c hcB c (List.mem_flatten.mpr ⟨C, h, hcC⟩) rfl
    subst hCB
    have hR : R₁.Perm R₂ := hp.cons_inv
    have := eq_of_perm_of_flatten_eq hR (fun B' hB' => hne B' (List.mem_cons_of_mem _ hB'))
      (List.nodup_append.mp hnd).2.1 (List.append_cancel_left hfl)
    rw [this]

end General

/-! ## 2. The core: blocks, arcs and one-orbit permutations

Blocks `B0 :: Bs` (nonempty, concatenation `D = B0 ++ Bs.flatten` nodup and covering `α`), `X` contains every block
end and no inner block entry. For `σ` with one orbit: `σ = formPerm D` off `X` iff `σ = formPerm (B0 ++ Bs'.flatten)`
for a reordering `Bs'` of `Bs` (paper, steps (4)-(6)). -/

section Core

variable {α : Type*} [DecidableEq α]

/-- `σ (last of B0)` is the head of a block of `Bs`, when `σ` follows every block and has one orbit. -/
theorem exists_next_block [Finite α] {σ : Perm α} (hσ : ∀ x y, σ.SameCycle x y) {B0 : List α}
    {Bs : List (List α)} (hB0 : B0 ≠ []) (hBs : ∀ B ∈ Bs, B ≠ []) (hBs0 : Bs ≠ [])
    (hnd : (B0 ++ Bs.flatten).Nodup) (hcov : ∀ x, x ∈ B0 ++ Bs.flatten) (hf0 : Follows σ B0)
    (hfs : ∀ B ∈ Bs, Follows σ B) : ∃ C ∈ Bs, C.head? = some (σ (B0.getLast hB0)) := by
  have hnd0 : B0.Nodup := (List.nodup_append.mp hnd).1
  have hdisj : ∀ a ∈ B0, ∀ b ∈ Bs.flatten, a ≠ b := (List.nodup_append.mp hnd).2.2
  -- `σ (last B0)` is not an inner (non-head) entry of any block
  have not_inner : ∀ (B P S : List α) (x : α), (B = B0 ∨ B ∈ Bs) →
      B = P ++ x :: σ (B0.getLast hB0) :: S → False := by
    intro B P S x hB hsplit
    have hfB : Follows σ B := by
      rcases hB with rfl | hB
      · exact hf0
      · exact hfs B hB
    rw [hsplit] at hfB
    have hxz : x = B0.getLast hB0 := σ.injective hfB.apply
    rcases hB with rfl | hB
    · exact getLast_ne_of_split hnd0 hsplit hB0 hxz.symm
    · exact hdisj _ (List.getLast_mem hB0) x
        (List.mem_flatten.mpr ⟨B, hB, by rw [hsplit]; simp⟩) hxz.symm
  rcases List.mem_append.mp (hcov (σ (B0.getLast hB0))) with hy0 | hy1
  · exfalso
    by_cases hh : B0.head? = some (σ (B0.getLast hB0))
    · -- then `B0` is `σ`-invariant, against the single orbit
      have hinv : ∀ x ∈ B0, σ x ∈ B0 := by
        intro x hx
        by_cases hxl : x = B0.getLast hB0
        · rw [hxl]
          exact List.mem_of_mem_head? hh
        · obtain ⟨P, S, y, hsplit⟩ :=
            exists_split_of_mem_dropLast (List.mem_dropLast_of_mem_of_ne_getLast hx hxl)
          have hf := hf0
          rw [hsplit] at hf ⊢
          rw [hf.apply]
          simp
      obtain ⟨C, hC⟩ := List.exists_mem_of_ne_nil Bs hBs0
      obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil C (hBs C hC)
      obtain ⟨i, hi⟩ := (hσ (B0.getLast hB0) c).exists_nat_pow_eq
      have hcB0 := orbit_subset hinv (List.getLast_mem hB0) i
      rw [hi] at hcB0
      exact hdisj c hcB0 c (List.mem_flatten.mpr ⟨C, hC, hc⟩) rfl
    · obtain ⟨P, S, x, hsplit⟩ := exists_split_of_mem_tail (mem_tail_of_ne_head hy0 hh)
      exact not_inner B0 P S x (Or.inl rfl) hsplit
  · obtain ⟨C, hC, hyC⟩ := List.mem_flatten.mp hy1
    by_cases hh : C.head? = some (σ (B0.getLast hB0))
    · exact ⟨C, hC, hh⟩
    · exfalso
      obtain ⟨P, S, x, hsplit⟩ := exists_split_of_mem_tail (mem_tail_of_ne_head hyC hh)
      exact not_inner C P S x (Or.inr hC) hsplit

/-- The merge induction: a one-orbit `σ` that follows every block is `formPerm` of a reordering of the blocks
(the first block stays first). -/
theorem core_forward [Finite α] (σ : Perm α) (hσ : ∀ x y, σ.SameCycle x y) (k : ℕ) :
    ∀ (B0 : List α) (Bs : List (List α)), Bs.length = k → B0 ≠ [] → (∀ B ∈ Bs, B ≠ []) →
      (B0 ++ Bs.flatten).Nodup → (∀ x, x ∈ B0 ++ Bs.flatten) → Follows σ B0 →
      (∀ B ∈ Bs, Follows σ B) → ∃ Bs' : List (List α), Bs'.Perm Bs ∧ σ = formPerm (B0 ++ Bs'.flatten) := by
  induction k with
  | zero =>
    intro B0 Bs hk hB0 _ hnd hcov hf0 _
    rw [List.length_eq_zero_iff] at hk
    subst hk
    refine ⟨[], List.Perm.nil, ?_⟩
    simp only [flatten_nil, append_nil] at hnd hcov ⊢
    apply perm_eq_of_eq_off_point (B0.getLast hB0)
    intro x hx
    obtain ⟨P, S, y, hsplit⟩ :=
      exists_split_of_mem_dropLast (List.mem_dropLast_of_mem_of_ne_getLast (hcov x) hx)
    have h1 := hf0
    have h2 := follows_formPerm hnd
    rw [hsplit] at h1 h2 ⊢
    rw [h1.apply, h2.apply]
  | succ k ih =>
    intro B0 Bs hk hB0 hBs hnd hcov hf0 hfs
    have hBs0 : Bs ≠ [] := by rintro rfl; simp at hk
    obtain ⟨C, hC, hhead⟩ := exists_next_block hσ hB0 hBs hBs0 hnd hcov hf0 hfs
    have hperm : Bs.Perm (C :: Bs.erase C) := List.perm_cons_erase hC
    have hP : (B0 ++ Bs.flatten).Perm ((B0 ++ C) ++ (Bs.erase C).flatten) := by
      simpa [List.append_assoc] using hperm.flatten.append_left B0
    have hf' : Follows σ (B0 ++ C) := by
      unfold Follows
      rw [isChain_append]
      refine ⟨hf0, hfs C hC, ?_⟩
      intro x hx y hy
      rw [List.getLast?_eq_some_getLast hB0, Option.mem_some_iff] at hx
      rw [hhead, Option.mem_some_iff] at hy
      rw [← hx]
      exact hy
    obtain ⟨Bs3, hp3, heq⟩ := ih (B0 ++ C) (Bs.erase C)
      (by rw [List.length_erase_of_mem hC]; omega) (by simp [hB0])
      (fun B hB => hBs B (List.mem_of_mem_erase hB)) (hP.nodup_iff.mp hnd)
      (fun x => hP.mem_iff.mp (hcov x)) hf' (fun B hB => hfs B (List.mem_of_mem_erase hB))
    refine ⟨C :: Bs3, (hp3.cons C).trans hperm.symm, ?_⟩
    simpa [List.append_assoc] using heq

theorem core_backward {B0 : List α} {Bs Bs' : List (List α)} (hp : Bs'.Perm Bs)
    (hnd : (B0 ++ Bs.flatten).Nodup) {X : Finset α}
    (hout : ∀ x, x ∉ X → ∃ B, (B = B0 ∨ B ∈ Bs) ∧ x ∈ B.dropLast) :
    ∀ x, x ∉ X → formPerm (B0 ++ Bs'.flatten) x = formPerm (B0 ++ Bs.flatten) x := by
  intro x hx
  obtain ⟨B, hB, hxB⟩ := hout x hx
  obtain ⟨P, S, y, hsplit⟩ := exists_split_of_mem_dropLast hxB
  have hP : (B0 ++ Bs'.flatten).Perm (B0 ++ Bs.flatten) := hp.flatten.append_left B0
  have hB' : B = B0 ∨ B ∈ Bs' := hB.imp_right hp.mem_iff.mpr
  have h1 := (follows_formPerm hnd).infix (block_infix hB)
  have h2 := (follows_formPerm (hP.nodup_iff.mpr hnd)).infix (block_infix hB')
  rw [hsplit] at h1 h2
  rw [h1.apply, h2.apply]

/-- **The core equivalence** (paper, steps (4)-(6), for one block configuration). -/
theorem core_iff [Finite α] {B0 : List α} {Bs : List (List α)} {X : Finset α} (hB0 : B0 ≠ [])
    (hBs : ∀ B ∈ Bs, B ≠ []) (hnd : (B0 ++ Bs.flatten).Nodup) (hcov : ∀ x, x ∈ B0 ++ Bs.flatten)
    (hin : ∀ B, (B = B0 ∨ B ∈ Bs) → ∀ x ∈ B.dropLast, x ∉ X)
    (hend : ∀ B, (B = B0 ∨ B ∈ Bs) → ∀ x ∈ B.getLast?, x ∈ X)
    (σ : Perm α) (hσ : ∀ x y, σ.SameCycle x y) :
    (∀ x, x ∉ X → σ x = formPerm (B0 ++ Bs.flatten) x) ↔
      ∃ Bs' : List (List α), Bs'.Perm Bs ∧ σ = formPerm (B0 ++ Bs'.flatten) := by
  constructor
  · intro hag
    have hfol : ∀ B, (B = B0 ∨ B ∈ Bs) → Follows σ B := fun B hB =>
      follows_of_agree hag ((follows_formPerm hnd).infix (block_infix hB)) (hin B hB)
    exact core_forward σ hσ Bs.length B0 Bs rfl hB0 hBs hnd hcov (hfol B0 (Or.inl rfl))
      (fun B hB => hfol B (Or.inr hB))
  · rintro ⟨Bs', hp, rfl⟩
    refine core_backward hp hnd ?_
    intro x hx
    obtain ⟨B, hB, hxB⟩ : ∃ B, (B = B0 ∨ B ∈ Bs) ∧ x ∈ B := by
      rcases List.mem_append.mp (hcov x) with h | h
      · exact ⟨B0, Or.inl rfl, h⟩
      · obtain ⟨B, hB, hxB⟩ := List.mem_flatten.mp h
        exact ⟨B, Or.inr hB, hxB⟩
    refine ⟨B, hB, List.mem_dropLast_of_mem_of_ne_getLast hxB ?_⟩
    intro hxl
    apply hx
    apply hend B hB
    rw [List.getLast?_eq_some_getLast (List.ne_nil_of_mem hxB)]
    exact Option.mem_some_iff.mpr hxl.symm

end Core

end NagataHigman.Proofs.Arcs

/-! ## 3. Words and `N`-cycles (paper step (1)); monomials -/

namespace NagataHigman.Proofs

open Equiv List Arcs

-- `cycList w = [N, w 0, …, w (m-1)]` and `wordCycle w = formPerm (cycList w)` (step (1), `Φ` on words) are defined in
-- NagataHigman/Defs/WordCycle.lean (namespace `NagataHigman`).

/-- The letters `[w 0, …, w (m-1)]` of the word of `w`, as naturals (letter `k` is `x_{k+1}` in the paper). -/
def wordList {m : ℕ} (w : Perm (Fin m)) : List ℕ := List.ofFn (fun i => ((w i : Fin m) : ℕ))

/-- The monomial of a nonempty list of letters (the empty list gets the junk value `x_0`; never used). -/
def monoOf : List ℕ → FreeSemigroup ℕ
  | [] => FreeSemigroup.of 0
  | x :: l => ⟨x, l⟩

/-- The multilinear monomial `x_{w 0} ⋯ x_{w (m-1)}`. -/
def wordMono {m : ℕ} (w : Perm (Fin m)) : FreeSemigroup ℕ := monoOf (wordList w)

namespace Arcs

theorem cycList_nodup {m : ℕ} (w : Perm (Fin m)) : (cycList w).Nodup := by
  unfold cycList
  refine List.nodup_cons.mpr ⟨?_, List.nodup_ofFn.mpr ?_⟩
  · simp [List.mem_ofFn, Fin.castSucc_ne_last]
  · intro i j h
    exact w.injective (Fin.castSucc_injective _ h)

theorem cycList_length {m : ℕ} (w : Perm (Fin m)) : (cycList w).length = m + 1 := by
  simp [cycList]

theorem mem_cycList {m : ℕ} (w : Perm (Fin m)) (x : Fin (m + 1)) : x ∈ cycList w := by
  unfold cycList
  rcases Fin.eq_castSucc_or_eq_last x with ⟨j, rfl⟩ | rfl
  · refine List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨w.symm j, by simp⟩)
  · exact List.mem_cons_self

theorem cycList_head {m : ℕ} (w : Perm (Fin m)) : (cycList w).head? = some (Fin.last m) := rfl

/-- `formPerm` of a nodup list of length `≥ 2` covering `Fin N` is an `N`-cycle. -/
theorem isFullCycle_formPerm {N : ℕ} {l : List (Fin N)} (hnd : l.Nodup) (hlen : 2 ≤ l.length)
    (hcov : ∀ x, x ∈ l) : IsFullCycle (formPerm l) := by
  refine ⟨List.isCycle_formPerm hnd hlen, ?_⟩
  rw [List.support_formPerm_of_nodup l hnd (fun x hx => by rw [hx] at hlen; simp at hlen)]
  ext x
  simp [hcov x]

theorem sameCycle_of_isFullCycle {N : ℕ} {σ : Perm (Fin N)} (h : IsFullCycle σ) (x y : Fin N) :
    σ.SameCycle x y :=
  h.1.sameCycle (Perm.mem_support.mp (h.2 ▸ Finset.mem_univ x))
    (Perm.mem_support.mp (h.2 ▸ Finset.mem_univ y))

theorem sign_of_isFullCycle {N : ℕ} {σ : Perm (Fin N)} (h : IsFullCycle σ) :
    Perm.sign σ = -(-1) ^ N := by
  rw [h.1.sign, h.2, Finset.card_univ, Fintype.card_fin]

/-- A nodup list of length `m+1` headed by `N` is the cycle list of a word. -/
theorem exists_cycList_eq {m : ℕ} {t : List (Fin (m + 1))} (hnd : t.Nodup) (hlen : t.length = m + 1)
    (hhead : t.head? = some (Fin.last m)) : ∃ w : Perm (Fin m), cycList w = t := by
  rcases t with _ | ⟨x, T⟩
  · simp at hlen
  simp only [head?_cons, Option.some.injEq] at hhead
  subst hhead
  have hT : T.length = m := by simpa using hlen
  have hlast : Fin.last m ∉ T := (List.nodup_cons.mp hnd).1
  have hTnd : T.Nodup := (List.nodup_cons.mp hnd).2
  have hne : ∀ i : Fin m, T[i.1]'(by omega) ≠ Fin.last m := fun i h =>
    hlast (h ▸ List.getElem_mem _)
  let g : Fin m → Fin m := fun i => (T[i.1]'(by omega)).castPred (hne i)
  have hg : Function.Injective g := by
    intro i j hij
    have := congrArg Fin.castSucc hij
    simp only [g, Fin.castSucc_castPred] at this
    exact Fin.ext ((List.Nodup.getElem_inj_iff hTnd).mp this)
  refine ⟨Equiv.ofBijective g hg.bijective_of_finite, ?_⟩
  simp only [cycList, cons.injEq, true_and]
  apply List.ext_getElem (by simp [hT])
  intro i h1 h2
  simp [g]

/-- A permutation of `range m` is the letter list of a word. -/
theorem exists_wordList_eq {m : ℕ} {L : List ℕ} (h : L.Perm (List.range m)) :
    ∃ w : Perm (Fin m), wordList w = L := by
  have hlen : L.length = m := by simpa using h.length_eq
  have hlt : ∀ i : Fin m, L[i.1]'(by omega) < m := fun i =>
    List.mem_range.mp (h.mem_iff.mp (List.getElem_mem _))
  have hnd : L.Nodup := h.nodup_iff.mpr List.nodup_range
  let g : Fin m → Fin m := fun i => ⟨L[i.1]'(by omega), hlt i⟩
  have hg : Function.Injective g := by
    intro i j hij
    have := congrArg Fin.val hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp this)
  refine ⟨Equiv.ofBijective g hg.bijective_of_finite, ?_⟩
  apply List.ext_getElem (by simp [wordList, hlen])
  intro i h1 h2
  simp [wordList, g]

theorem map_val_cycList_tail {m : ℕ} (w : Perm (Fin m)) :
    (List.ofFn (fun i => (w i).castSucc)).map Fin.val = wordList w := by
  simp [wordList, List.map_ofFn, Function.comp_def]

theorem monoOf_append {l₁ l₂ : List ℕ} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    monoOf (l₁ ++ l₂) = monoOf l₁ * monoOf l₂ := by
  rcases l₁ with _ | ⟨x, r⟩
  · exact absurd rfl h₁
  rcases l₂ with _ | ⟨y, s⟩
  · exact absurd rfl h₂
  rfl

theorem monoOf_inj {l₁ l₂ : List ℕ} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) (h : monoOf l₁ = monoOf l₂) : l₁ = l₂ := by
  rcases l₁ with _ | ⟨x, r⟩
  · exact absurd rfl h₁
  rcases l₂ with _ | ⟨y, s⟩
  · exact absurd rfl h₂
  simp only [monoOf, FreeSemigroup.mk.injEq] at h
  rw [h.1, h.2]

variable (F : Type*) [Field F]

/-- A product of monomials of nonempty lists is the monomial of the concatenation. -/
theorem tupleProd_monos : ∀ (k : ℕ) (L : Fin (k + 1) → List ℕ), (∀ i, L i ≠ []) →
    tupleProd (k + 1) (fun i => (MonoidAlgebra.single (monoOf (L i)) (1 : F) : FreeNUAlg F)) =
      MonoidAlgebra.single (monoOf (List.ofFn L).flatten) 1
  | 0, L, _ => by simp [tupleProd]
  | k + 1, L, hL => by
    have hne : (List.ofFn fun i => L i.castSucc).flatten ≠ [] := by
      intro hnil
      rw [List.flatten_eq_nil_iff] at hnil
      exact hL _ (hnil _ (List.mem_ofFn.mpr ⟨0, rfl⟩))
    rw [tupleProd, tupleProd_monos k (fun i => L i.castSucc) (fun i => hL _), MonoidAlgebra.single_mul_single,
      mul_one, List.ofFn_succ' (f := L), List.concat_eq_append, List.flatten_append, List.flatten_singleton,
      monoOf_append hne (hL _)]

theorem tupleProd_monos' {n : ℕ} (hn : 1 ≤ n) (L : Fin n → List ℕ) (hL : ∀ i, L i ≠ []) :
    tupleProd n (fun i => (MonoidAlgebra.single (monoOf (L i)) (1 : F) : FreeNUAlg F)) =
      MonoidAlgebra.single (monoOf (List.ofFn L).flatten) 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact tupleProd_monos F k L hL

theorem letter_eq (x : ℕ) : letter F x = MonoidAlgebra.single (monoOf [x]) 1 := rfl

theorem tupleProd_letters {n : ℕ} (hn : 1 ≤ n) (f : Fin n → ℕ) :
    tupleProd n (fun i => letter F (f i)) = MonoidAlgebra.single (monoOf (List.ofFn f)) 1 := by
  simp only [letter_eq]
  rw [tupleProd_monos' F hn (fun i => [f i]) (fun i => by simp)]
  have e : List.ofFn (fun i => [f i]) = (List.ofFn f).map (fun x => [x]) := by
    simp [List.map_ofFn, Function.comp_def]
  rw [e, ← List.flatMap_def, List.flatMap_singleton']

theorem wordOf_eq {l : List ℕ} (hl : l ≠ []) : wordOf F l = MonoidAlgebra.single (monoOf l) 1 := by
  unfold wordOf
  rw [tupleProd_letters F (List.length_pos_of_ne_nil hl) (fun i => l.get i), List.ofFn_get]

end Arcs

variable (F : Type*) [Field F]

/-- `x_{w 0} ⋯ x_{w (m-1)}` is the basis element of the monomial `wordMono w` (brief, def of `wordMono`). -/
theorem multilinWord_eq_single {m : ℕ} (hm : 1 ≤ m) (w : Perm (Fin m)) :
    multilinWord F w = MonoidAlgebra.single (wordMono w) 1 := by
  unfold multilinWord wordMono wordList
  exact Arcs.tupleProd_letters F hm _

/-- **B1 (a)**: `Φ(w)` is an `N`-cycle. -/
theorem wordCycle_isFullCycle {m : ℕ} (hm : 1 ≤ m) (w : Perm (Fin m)) : IsFullCycle (wordCycle w) :=
  Arcs.isFullCycle_formPerm (Arcs.cycList_nodup w) (by rw [Arcs.cycList_length]; omega)
    (Arcs.mem_cycList w)

/-- **B1 (b)**: `Φ` is injective on words. -/
theorem wordCycle_injective {m : ℕ} : Function.Injective (wordCycle (m := m)) := by
  intro w₁ w₂ h
  have hl := Arcs.formPerm_inj (Arcs.cycList_nodup w₁) (Arcs.cycList_nodup w₂)
    (by rw [Arcs.cycList_length, Arcs.cycList_length]) rfl h
  simp only [cycList, cons.injEq, true_and] at hl
  ext i
  have := congrFun (List.ofFn_injective hl) i
  simpa using congrArg Fin.val this

/-- **B1 (c)**: every `N`-cycle is `Φ(w)` for a word `w`. -/
theorem exists_wordCycle_eq {m : ℕ} {σ : Perm (Fin (m + 1))} (hσ : IsFullCycle σ) :
    ∃ w : Perm (Fin m), wordCycle w = σ := by
  have hlast : Fin.last m ∈ σ.support := hσ.2 ▸ Finset.mem_univ _
  have hcyc : σ.cycleOf (Fin.last m) = σ := hσ.1.cycleOf_eq (Perm.mem_support.mp hlast)
  have hlen : (σ.toList (Fin.last m)).length = m + 1 := by
    rw [Perm.length_toList, hcyc, hσ.2, Finset.card_univ, Fintype.card_fin]
  have hhead : (σ.toList (Fin.last m)).head? = some (Fin.last m) := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega), Perm.toList_getElem_zero _ _ hlast]
  obtain ⟨w, hw⟩ := Arcs.exists_cycList_eq (Perm.nodup_toList σ _) hlen hhead
  refine ⟨w, ?_⟩
  rw [wordCycle, hw, Perm.formPerm_toList, hcyc]

/-! ## 4. Coefficients: the two sides of the block lemma -/

namespace Arcs

/-- The coefficient of `σ` in `τ · E_X` is `sgn(τ⁻¹σ)` if `τ⁻¹σ ∈ Sym(X)`, else `0`. -/
theorem coeff_perm_mul_altSum {N : ℕ} (τ σ : Perm (Fin N)) (X : Finset (Fin N)) :
    (perm F τ * altSum F X).coeff σ =
      if (τ⁻¹ * σ).support ⊆ X then ((Perm.sign (τ⁻¹ * σ) : ℤ) : F) else 0 := by
  classical
  simp only [altSum, perm, Finset.mul_sum, mul_smul_comm, MonoidAlgebra.single_mul_single, mul_one,
    MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_zero]
  simp_rw [← eq_inv_mul_iff_mul_eq]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_filter]

theorem sign_inv_mul_of_isFullCycle {N : ℕ} {τ σ : Perm (Fin N)} (hτ : IsFullCycle τ)
    (hσ : IsFullCycle σ) : Perm.sign (τ⁻¹ * σ) = 1 := by
  rw [Perm.sign_mul, Perm.sign_inv, sign_of_isFullCycle hτ, sign_of_isFullCycle hσ, Int.units_mul_self]

theorem support_inv_mul_subset_iff {N : ℕ} (τ σ : Perm (Fin N)) (X : Finset (Fin N)) :
    (τ⁻¹ * σ).support ⊆ X ↔ ∀ x, x ∉ X → σ x = τ x := by
  constructor
  · intro h x hx
    have hns : x ∉ (τ⁻¹ * σ).support := fun hs => hx (h hs)
    rw [Perm.notMem_support, Perm.mul_apply, Perm.inv_eq_iff_eq] at hns
    exact hns
  · intro h x hx
    by_contra hxX
    rw [Perm.mem_support, Perm.mul_apply, h x hxX] at hx
    simp at hx

/-- **Step (5), constant sign**: between two `N`-cycles the coefficient is `1` or `0`, never `-1`. -/
theorem coeff_fullCycle {N : ℕ} {τ σ : Perm (Fin N)} (hτ : IsFullCycle τ) (hσ : IsFullCycle σ)
    (X : Finset (Fin N)) :
    (perm F τ * altSum F X).coeff σ = if (∀ x, x ∉ X → σ x = τ x) then 1 else 0 := by
  rw [coeff_perm_mul_altSum, sign_inv_mul_of_isFullCycle hτ hσ]
  by_cases h : ∀ x, x ∉ X → σ x = τ x
  · rw [ite_eq_left ((support_inv_mul_subset_iff τ σ X).mpr h), ite_eq_left h]
    simp
  · rw [ite_eq_right (mt (support_inv_mul_subset_iff τ σ X).mp h), ite_eq_right h]

/-- `a · L(v_1, …, v_n) · b` is the sum of the words `a v_{π 1} ⋯ v_{π n} b`, `π ∈ S_n`. -/
theorem sandwichElem_eq_sum {n : ℕ} (hn : 1 ≤ n) (a b : List ℕ) (v : Fin n → List ℕ) (hv : ∀ i, v i ≠ []) :
    sandwichElem F a v b =
      ∑ π : Perm (Fin n), MonoidAlgebra.single (monoOf (a ++ (List.ofFn (v ∘ π)).flatten ++ b)) (1 : F) := by
  have hG : ∀ π : Perm (Fin n), (List.ofFn (v ∘ π)).flatten ≠ [] := by
    intro π hnil
    rw [List.flatten_eq_nil_iff] at hnil
    exact hv (π ⟨0, hn⟩) (hnil _ (List.mem_ofFn.mpr ⟨⟨0, hn⟩, rfl⟩))
  have hsym : symSum n (fun i => wordOf F (v i)) =
      ∑ π : Perm (Fin n), MonoidAlgebra.single (monoOf (List.ofFn (v ∘ π)).flatten) (1 : F) := by
    unfold symSum
    refine Finset.sum_congr rfl (fun π _ => ?_)
    simp only [wordOf_eq F (hv _)]
    exact tupleProd_monos' F hn (v ∘ π) (fun i => hv _)
  simp only [sandwichElem, sandwich]
  rw [hsym]
  by_cases ha : a = [] <;> by_cases hb : b = []
  · simp [ha, hb]
  · rw [ite_eq_left ha, ite_eq_right hb, wordOf_eq F hb, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun π _ => ?_)
    rw [MonoidAlgebra.single_mul_single, mul_one, ← monoOf_append (hG π) hb, ha, List.nil_append]
  · rw [ite_eq_right ha, ite_eq_left hb, wordOf_eq F ha, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun π _ => ?_)
    rw [MonoidAlgebra.single_mul_single, mul_one, ← monoOf_append ha (hG π), hb, List.append_nil]
  · rw [ite_eq_right ha, ite_eq_right hb, wordOf_eq F ha, wordOf_eq F hb, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun π _ => ?_)
    rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, mul_one, mul_one,
      ← monoOf_append ha (hG π), ← monoOf_append (by simp [ha]) hb]

/-- The coefficient of a multilinear word in `a · L(v) · b`: the number of `π` with `a v_π b = w`. -/
theorem coeff_sandwichElem {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (a b : List ℕ) (v : Fin n → List ℕ)
    (hv : ∀ i, v i ≠ []) (w : Perm (Fin m)) :
    (sandwichElem F a v b).coeff (wordMono w) =
      ∑ π : Perm (Fin n), if a ++ (List.ofFn (v ∘ π)).flatten ++ b = wordList w then (1 : F) else 0 := by
  rw [sandwichElem_eq_sum F hn a b v hv, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl (fun π _ => ?_)
  rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  have hne1 : a ++ (List.ofFn (v ∘ π)).flatten ++ b ≠ [] := by
    intro hnil
    simp only [List.append_eq_nil_iff, List.flatten_eq_nil_iff] at hnil
    exact hv (π ⟨0, hn⟩) (hnil.1.2 _ (List.mem_ofFn.mpr ⟨⟨0, hn⟩, rfl⟩))
  have hne2 : wordList w ≠ [] := by
    intro hnil
    have := congrArg List.length hnil
    simp [wordList] at this
    omega
  unfold wordMono
  by_cases h : a ++ (List.ofFn (v ∘ π)).flatten ++ b = wordList w
  · rw [ite_eq_left h, ite_eq_left (by rw [h])]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (monoOf_inj hne1 hne2 h'))]

/-- Distinct nonempty blocks with a nodup concatenation: the block map is injective. -/
theorem injective_of_nodup_flatten {β : Type*} {n : ℕ} {v : Fin n → List β} (hv : ∀ i, v i ≠ [])
    (hnd : (List.ofFn v).flatten.Nodup) : Function.Injective v := by
  intro i j hij
  by_contra hne
  rw [List.nodup_flatten, List.pairwise_ofFn] at hnd
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hv i)
    exact hnd.2 h hx (hij ▸ hx)
  · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hv j)
    exact hnd.2 h hx (hij.symm ▸ hx)

end Arcs

/-! ## 5. Block configurations: the block lemma -/

namespace Arcs

/-- A block configuration on `Fin (m+1)`: the cycle `N → a → v_1 → ⋯ → v_n → b → N` with nonempty `v_i`
(paper, step (6): `τ = Φ(a v_1 ⋯ v_n b)`). -/
structure BlockConfig (m n : ℕ) where
  a : List (Fin (m + 1))
  b : List (Fin (m + 1))
  v : Fin n → List (Fin (m + 1))
  v_ne : ∀ i, v i ≠ []
  nodup : (Fin.last m :: (a ++ (List.ofFn v).flatten ++ b)).Nodup
  cover : ∀ x, x ∈ Fin.last m :: (a ++ (List.ofFn v).flatten ++ b)

namespace BlockConfig

variable {m n : ℕ} (K : BlockConfig m n)

/-- The cycle list with the blocks reordered by `π`. -/
def cyc (π : Perm (Fin n)) : List (Fin (m + 1)) :=
  Fin.last m :: (K.a ++ (List.ofFn (K.v ∘ π)).flatten ++ K.b)

/-- The cycle list itself. -/
def list : List (Fin (m + 1)) := Fin.last m :: (K.a ++ (List.ofFn K.v).flatten ++ K.b)

/-- `τ = Φ(a v_1 ⋯ v_n b)`. -/
def tau : Perm (Fin (m + 1)) := formPerm K.list

/-- The arc that contains `N`: `b, N, a` (paper: `Arc_0 = (ζ, N, ξ)`). -/
def B0 : List (Fin (m + 1)) := K.b ++ Fin.last m :: K.a

/-- `X` is the set of arc ends: no inner arc entry lies in `X`, and every arc end does. -/
def Splits (X : Finset (Fin (m + 1))) : Prop :=
  (∀ B, (B = K.B0 ∨ B ∈ List.ofFn K.v) → ∀ x ∈ B.dropLast, x ∉ X) ∧
    (∀ B, (B = K.B0 ∨ B ∈ List.ofFn K.v) → ∀ x ∈ B.getLast?, x ∈ X)

theorem rotated (Bs : List (List (Fin (m + 1)))) :
    K.B0 ++ Bs.flatten ~r Fin.last m :: (K.a ++ Bs.flatten ++ K.b) := by
  have e1 : K.B0 ++ Bs.flatten = K.b ++ (Fin.last m :: (K.a ++ Bs.flatten)) := by simp [B0]
  have e2 : Fin.last m :: (K.a ++ Bs.flatten ++ K.b) = (Fin.last m :: (K.a ++ Bs.flatten)) ++ K.b := by simp
  rw [e1, e2]
  exact List.isRotated_append

theorem v_injective : Function.Injective K.v := by
  have h := (List.nodup_cons.mp K.nodup).2
  exact injective_of_nodup_flatten K.v_ne ((List.nodup_append.mp (List.nodup_append.mp h).1).2.1)

theorem cyc_perm (π : Perm (Fin n)) : (K.cyc π).Perm K.list := by
  unfold cyc list
  exact (((π.ofFn_comp_perm K.v).flatten.append_left K.a).append_right K.b).cons _

theorem cyc_nodup (π : Perm (Fin n)) : (K.cyc π).Nodup := (K.cyc_perm π).nodup_iff.mpr K.nodup

theorem list_length : K.list.length = m + 1 := by
  unfold list
  rw [← List.toFinset_card_of_nodup K.nodup]
  have : (Fin.last m :: (K.a ++ (List.ofFn K.v).flatten ++ K.b)).toFinset = Finset.univ :=
    Finset.eq_univ_of_forall (fun x => List.mem_toFinset.mpr (K.cover x))
  rw [this, Finset.card_univ, Fintype.card_fin]

theorem tau_isFullCycle (hn : 1 ≤ n) : IsFullCycle K.tau := by
  refine isFullCycle_formPerm K.nodup ?_ K.cover
  have hG : 1 ≤ (List.ofFn K.v).flatten.length := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (K.v_ne ⟨0, hn⟩)
    exact List.length_pos_of_mem (List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨⟨0, hn⟩, rfl⟩, hx⟩)
  simp only [list, List.length_cons, List.length_append]
  omega

/-- The words of the reordered cycles are the words `a v_π b` (letters as naturals). -/
theorem wordList_eq_iff (π : Perm (Fin n)) (w : Perm (Fin m)) :
    (K.a.map Fin.val ++ (List.ofFn ((fun i => (K.v i).map Fin.val) ∘ π)).flatten ++ K.b.map Fin.val =
        wordList w) ↔ cycList w = K.cyc π := by
  rw [← map_val_cycList_tail]
  have e : K.a.map Fin.val ++ (List.ofFn ((fun i => (K.v i).map Fin.val) ∘ π)).flatten ++ K.b.map Fin.val =
      (K.a ++ (List.ofFn (K.v ∘ π)).flatten ++ K.b).map Fin.val := by
    simp [List.map_flatten, List.map_ofFn, Function.comp_def]
  rw [e, (List.map_injective_iff.mpr Fin.val_injective).eq_iff]
  simp only [cycList, cyc, List.cons.injEq, true_and]
  exact eq_comm

/-- At most one ordering of the blocks gives a given cycle list. -/
theorem cyc_unique {π₁ π₂ : Perm (Fin n)} (h : K.cyc π₁ = K.cyc π₂) : π₁ = π₂ := by
  simp only [cyc, List.cons.injEq, true_and, List.append_cancel_right_eq, List.append_cancel_left_eq] at h
  have hp : (List.ofFn (K.v ∘ π₁)).Perm (List.ofFn (K.v ∘ π₂)) :=
    (π₁.ofFn_comp_perm K.v).trans (π₂.ofFn_comp_perm K.v).symm
  have hnd : (List.ofFn (K.v ∘ π₁)).flatten.Nodup := by
    have h1 := (List.nodup_cons.mp (K.cyc_nodup π₁)).2
    exact (List.nodup_append.mp (List.nodup_append.mp h1).1).2.1
  have hne : ∀ B ∈ List.ofFn (K.v ∘ π₁), B ≠ [] := by
    intro B hB
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hB
    exact K.v_ne _
  have hfn := List.ofFn_injective (eq_of_perm_of_flatten_eq hp hne hnd h)
  ext i
  exact congrArg Fin.val (K.v_injective (congrFun hfn i))

/-- Reordered configurations, in the two shapes: as reorderings of the arc list, and as words. -/
theorem exists_cyc_iff (w : Perm (Fin m)) :
    (∃ π : Perm (Fin n), cycList w = K.cyc π) ↔
      ∃ Bs' : List (List (Fin (m + 1))), Bs'.Perm (List.ofFn K.v) ∧ wordCycle w = formPerm (K.B0 ++ Bs'.flatten) := by
  constructor
  · rintro ⟨π, hπ⟩
    refine ⟨List.ofFn (K.v ∘ π), π.ofFn_comp_perm K.v, ?_⟩
    have hrot := K.rotated (List.ofFn (K.v ∘ π))
    have hnd : (K.B0 ++ (List.ofFn (K.v ∘ π)).flatten).Nodup := hrot.nodup_iff.mpr (K.cyc_nodup π)
    rw [wordCycle, hπ, formPerm_eq_of_isRotated hnd hrot]
    rfl
  · rintro ⟨Bs', hp, he⟩
    obtain ⟨π, rfl⟩ := exists_perm_of_perm_ofFn K.v_injective hp
    refine ⟨π, ?_⟩
    have hrot := K.rotated (List.ofFn (K.v ∘ π))
    have hnd : (K.B0 ++ (List.ofFn (K.v ∘ π)).flatten).Nodup := hrot.nodup_iff.mpr (K.cyc_nodup π)
    rw [formPerm_eq_of_isRotated hnd hrot] at he
    exact formPerm_inj (cycList_nodup w) (K.cyc_nodup π)
      (by rw [cycList_length, (K.cyc_perm π).length_eq, K.list_length]) rfl he

/-- **The block lemma** (paper, steps (5)-(6), for `τ = Φ(a v_1 ⋯ v_n b)` and `X` = the arc ends):
`P(τ E_X) = Φ(a · L(v_1, …, v_n) · b)`, coefficientwise on the `N`-cycles. -/
theorem coeff_eq (hn : 1 ≤ n) (hm : 1 ≤ m) {X : Finset (Fin (m + 1))} (hX : K.Splits X)
    (w : Perm (Fin m)) :
    (perm F K.tau * altSum F X).coeff (wordCycle w) =
      (sandwichElem F (K.a.map Fin.val) (fun i => (K.v i).map Fin.val) (K.b.map Fin.val)).coeff (wordMono w) := by
  have hvℕ : ∀ i, (K.v i).map Fin.val ≠ [] := fun i => by simpa using K.v_ne i
  rw [coeff_fullCycle F (K.tau_isFullCycle hn) (wordCycle_isFullCycle hm w),
    coeff_sandwichElem F hn hm _ _ _ hvℕ w]
  simp_rw [K.wordList_eq_iff]
  -- the core equivalence for the arcs `B0 :: v`
  have hrot := K.rotated (List.ofFn K.v)
  have hD : (K.B0 ++ (List.ofFn K.v).flatten).Nodup := hrot.nodup_iff.mpr K.nodup
  have hcov : ∀ x, x ∈ K.B0 ++ (List.ofFn K.v).flatten := fun x => hrot.mem_iff.mpr (K.cover x)
  have hτ : K.tau = formPerm (K.B0 ++ (List.ofFn K.v).flatten) := (formPerm_eq_of_isRotated hD hrot).symm
  have hcore := core_iff (B0 := K.B0) (Bs := List.ofFn K.v) (X := X) (by simp [B0])
    (fun B hB => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hB; exact K.v_ne i) hD hcov hX.1 hX.2
    (wordCycle w) (sameCycle_of_isFullCycle (wordCycle_isFullCycle hm w))
  rw [← hτ, ← K.exists_cyc_iff w] at hcore
  by_cases hex : ∃ π : Perm (Fin n), cycList w = K.cyc π
  · obtain ⟨π₀, hπ₀⟩ := hex
    rw [ite_eq_left (hcore.mpr ⟨π₀, hπ₀⟩)]
    rw [Finset.sum_eq_single π₀ (fun π _ hπ => ite_eq_right (fun h => hπ (K.cyc_unique (h.symm.trans hπ₀))))
      (by simp)]
    rw [ite_eq_left hπ₀]
  · rw [ite_eq_right (fun h => hex (hcore.mp h))]
    exact (Finset.sum_eq_zero (fun π _ => ite_eq_right (fun h => hex ⟨π, h⟩))).symm

end BlockConfig

end Arcs

/-! ## 6. Splitting a cycle at the points of `X`; arc ends -/

namespace Arcs

section Split

variable {α : Type*} [DecidableEq α]

/-- Split a list after each point of `X`: chunks that end in `X` with no other point of `X`, and a tail
without points of `X` (paper, step (4): the arcs). -/
theorem split_exists (X : Finset α) : ∀ l : List α, ∃ (Cs : List (List α)) (t : List α),
    l = Cs.flatten ++ t ∧ (∀ C ∈ Cs, C ≠ [] ∧ (∀ x ∈ C.getLast?, x ∈ X) ∧ ∀ x ∈ C.dropLast, x ∉ X) ∧
      ∀ x ∈ t, x ∉ X
  | [] => ⟨[], [], by simp, by simp, by simp⟩
  | x :: l => by
    obtain ⟨Cs, t, hl, hCs, ht⟩ := split_exists X l
    by_cases hx : x ∈ X
    · refine ⟨[x] :: Cs, t, by simp [hl], ?_, ht⟩
      intro C hC
      rcases List.mem_cons.mp hC with rfl | hC
      · simp [hx]
      · exact hCs C hC
    · rcases Cs with _ | ⟨C, Cs'⟩
      · refine ⟨[], x :: t, by simp [hl], by simp, ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact ht y hy
      · obtain ⟨hCne, hCend, hCin⟩ := hCs C List.mem_cons_self
        refine ⟨(x :: C) :: Cs', t, by simp [hl], ?_, ht⟩
        intro D hD
        rcases List.mem_cons.mp hD with rfl | hD
        · rcases C with _ | ⟨c, C'⟩
          · exact absurd rfl hCne
          refine ⟨by simp, ?_, ?_⟩
          · intro y hy
            rw [List.getLast?_cons_cons] at hy
            exact hCend y hy
          · intro y hy
            rw [List.dropLast_cons_cons] at hy
            rcases List.mem_cons.mp hy with rfl | hy
            · exact hx
            · exact hCin y hy
        · exact hCs D (List.mem_cons_of_mem _ hD)

/-- In a nodup concatenation of blocks, every entry lies in exactly one block. -/
theorem eq_of_mem_flatten_of_nodup : ∀ {L : List (List α)}, L.flatten.Nodup →
    ∀ {B B' : List α} {x : α}, B ∈ L → B' ∈ L → x ∈ B → x ∈ B' → B = B'
  | [], _, _, _, _, hB, _, _, _ => absurd hB List.not_mem_nil
  | C :: R, hnd, B, B', x, hB, hB', hx, hx' => by
    rw [List.flatten_cons, List.nodup_append] at hnd
    rcases List.mem_cons.mp hB with e1 | h1 <;> rcases List.mem_cons.mp hB' with e2 | h2
    · rw [e1, e2]
    · exact absurd rfl (hnd.2.2 x (e1 ▸ hx) x (List.mem_flatten.mpr ⟨B', h2, hx'⟩))
    · exact absurd rfl (hnd.2.2 x (e2 ▸ hx') x (List.mem_flatten.mpr ⟨B, h1, hx⟩))
    · exact eq_of_mem_flatten_of_nodup hnd.2.1 h1 h2 hx hx'

/-- The list of block ends `[last B | B ∈ Ls]`. -/
def endsOf (Ls : List (List α)) : List α := Ls.filterMap List.getLast?

theorem mem_endsOf {Ls : List (List α)} {x : α} : x ∈ endsOf Ls ↔ ∃ B ∈ Ls, B.getLast? = some x :=
  List.mem_filterMap

theorem endsOf_sublist : ∀ {Ls : List (List α)}, (∀ B ∈ Ls, B ≠ []) → endsOf Ls <+ Ls.flatten
  | [], _ => by simp [endsOf]
  | C :: R, h => by
    have hC := h C List.mem_cons_self
    have ih := endsOf_sublist (Ls := R) (fun B hB => h B (List.mem_cons_of_mem _ hB))
    simp only [endsOf, List.filterMap_cons, List.getLast?_eq_some_getLast hC, List.flatten_cons] at ih ⊢
    exact (List.singleton_sublist.mpr (List.getLast_mem hC)).append ih

theorem endsOf_length : ∀ {Ls : List (List α)}, (∀ B ∈ Ls, B ≠ []) → (endsOf Ls).length = Ls.length
  | [], _ => rfl
  | C :: R, h => by
    have hC := h C List.mem_cons_self
    have ih := endsOf_length (Ls := R) (fun B hB => h B (List.mem_cons_of_mem _ hB))
    simp only [endsOf, List.filterMap_cons, List.getLast?_eq_some_getLast hC, List.length_cons] at ih ⊢
    rw [ih]

theorem getLast?_ne_of_mem_dropLast {B : List α} {x : α} (hnd : B.Nodup) (hx : x ∈ B.dropLast) :
    B.getLast? ≠ some x := by
  obtain ⟨P, S, y, hsplit⟩ := exists_split_of_mem_dropLast hx
  have hne : B ≠ [] := by rw [hsplit]; simp
  intro h
  rw [List.getLast?_eq_some_getLast hne] at h
  exact getLast_ne_of_split hnd hsplit hne (Option.some.inj h)

end Split

end Arcs

/-! ## 7. The forward block lemma (B2) and its converse (B3) -/

namespace Arcs

/-- The arc ends of a block configuration. -/
def BlockConfig.ends {m n : ℕ} (K : BlockConfig m n) : Finset (Fin (m + 1)) :=
  (endsOf (K.B0 :: List.ofFn K.v)).toFinset

theorem BlockConfig.blocks_ne {m n : ℕ} (K : BlockConfig m n) : ∀ B ∈ K.B0 :: List.ofFn K.v, B ≠ [] := by
  intro B hB
  rcases List.mem_cons.mp hB with rfl | hB
  · simp [BlockConfig.B0]
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hB
    exact K.v_ne i

theorem BlockConfig.blocks_nodup {m n : ℕ} (K : BlockConfig m n) :
    (K.B0 :: List.ofFn K.v).flatten.Nodup := by
  rw [List.flatten_cons]
  exact (K.rotated (List.ofFn K.v)).nodup_iff.mpr K.nodup

theorem BlockConfig.splits_ends {m n : ℕ} (K : BlockConfig m n) : K.Splits K.ends := by
  constructor
  · intro B hB x hx hxe
    have hB' : B ∈ K.B0 :: List.ofFn K.v := by
      rcases hB with rfl | hB
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ hB
    obtain ⟨B', hB'mem, hB'last⟩ := mem_endsOf.mp (List.mem_toFinset.mp hxe)
    have hxB' : x ∈ B' := List.mem_of_getLast? hB'last
    have hxB : x ∈ B := List.dropLast_subset _ hx
    have heq := eq_of_mem_flatten_of_nodup K.blocks_nodup hB' hB'mem hxB hxB'
    subst heq
    have hBnd : B.Nodup := (List.nodup_flatten.mp K.blocks_nodup).1 B hB'
    exact getLast?_ne_of_mem_dropLast hBnd hx hB'last
  · intro B hB x hx
    have hB' : B ∈ K.B0 :: List.ofFn K.v := by
      rcases hB with rfl | hB
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ hB
    exact List.mem_toFinset.mpr (mem_endsOf.mpr ⟨B, hB', hx⟩)

theorem BlockConfig.card_ends {m n : ℕ} (K : BlockConfig m n) : K.ends.card = n + 1 := by
  unfold BlockConfig.ends
  rw [List.toFinset_card_of_nodup ((endsOf_sublist K.blocks_ne).nodup K.blocks_nodup),
    endsOf_length K.blocks_ne]
  simp

/-- Coefficient comparison when `τ π₀ = τ₀` for some `π₀ ∈ Sym(X)`: the coefficients of `τ E_X` are
`sgn(π₀)` times those of `τ₀ E_X` (paper, step (3)). -/
theorem coeff_mul_sym {N : ℕ} (τ π₀ σ : Perm (Fin N)) (X : Finset (Fin N)) (hπ₀ : π₀.support ⊆ X) :
    (perm F τ * altSum F X).coeff σ =
      ((Perm.sign π₀ : ℤ) : F) * (perm F (τ * π₀) * altSum F X).coeff σ := by
  have e : (τ * π₀)⁻¹ * σ = π₀⁻¹ * (τ⁻¹ * σ) := by group
  rw [coeff_perm_mul_altSum, coeff_perm_mul_altSum, e]
  have hsupp : (π₀⁻¹ * (τ⁻¹ * σ)).support ⊆ X ↔ (τ⁻¹ * σ).support ⊆ X := by
    constructor
    · intro h
      have e : τ⁻¹ * σ = π₀ * (π₀⁻¹ * (τ⁻¹ * σ)) := by group
      rw [e]
      intro x hx
      rcases Finset.mem_union.mp (Perm.support_mul_le _ _ hx) with h1 | h1
      · exact hπ₀ h1
      · exact h h1
    · intro h x hx
      rcases Finset.mem_union.mp (Perm.support_mul_le _ _ hx) with h1 | h1
      · rw [Perm.support_inv] at h1
        exact hπ₀ h1
      · exact h h1
  by_cases h : (τ⁻¹ * σ).support ⊆ X
  · rw [ite_eq_left h, ite_eq_left (hsupp.mpr h)]
    have hs : Perm.sign (π₀⁻¹ * (τ⁻¹ * σ)) = Perm.sign π₀ * Perm.sign (τ⁻¹ * σ) := by
      rw [Perm.sign_mul, Perm.sign_inv]
    rw [hs, Units.val_mul, Int.cast_mul, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self,
      Units.val_one, Int.cast_one, one_mul]
  · rw [ite_eq_right h, ite_eq_right (mt hsupp.mp h), mul_zero]

theorem wordList_perm_range {m : ℕ} (w : Perm (Fin m)) : (wordList w).Perm (List.range m) := by
  have hnd : (wordList w).Nodup := by
    unfold wordList
    refine List.nodup_ofFn.mpr ?_
    intro i j h
    exact w.injective (Fin.ext h)
  refine (List.perm_ext_iff_of_nodup hnd List.nodup_range).mpr ?_
  intro k
  simp only [wordList, List.mem_ofFn, List.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact (w i).isLt
  · intro hk
    exact ⟨w.symm ⟨k, hk⟩, by simp⟩

end Arcs

open Arcs in
/-- **B2, the forward block lemma** (paper, steps (3)-(6)): for `|X| = n + 1`, the `N`-cycle part of `τ E_X` is
`0` or `± Φ(a · L(v_1, …, v_n) · b)` for a multilinear triple `(a, v, b)`. -/
theorem forward_block_lemma {m n : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) (τ : Perm (Fin (m + 1)))
    (X : Finset (Fin (m + 1))) (hX : X.card = n + 1) :
    ∃ p : FreeNUAlg F,
      (p = 0 ∨ ∃ (a : List ℕ) (v : Fin n → List ℕ) (b : List ℕ) (s : F),
          IsMultilinTriple m a v b ∧ (s = 1 ∨ s = -1) ∧ p = s • sandwichElem F a v b) ∧
        ∀ w : Perm (Fin m), (perm F τ * altSum F X).coeff (wordCycle w) = p.coeff (wordMono w) := by
  have hm : 1 ≤ m := le_trans hn hnm
  by_cases hex : ∃ π₀ : Perm (Fin (m + 1)), π₀.support ⊆ X ∧ IsFullCycle (τ * π₀)
  · obtain ⟨π₀, hπ₀X, hfull⟩ := hex
    obtain ⟨w₀, hw₀⟩ := exists_wordCycle_eq hfull
    -- split the cycle list of `τ₀ = τ π₀` after each point of `X`
    obtain ⟨Cs, t, hc, hCs, ht⟩ := split_exists X (cycList w₀)
    have hCne : ∀ C ∈ Cs, C ≠ [] := fun C hC => (hCs C hC).1
    have hcnd : (Cs.flatten ++ t).Nodup := hc ▸ cycList_nodup w₀
    have hendsX : (endsOf Cs).toFinset = X := by
      ext x
      rw [List.mem_toFinset, mem_endsOf]
      constructor
      · rintro ⟨C, hC, hx⟩
        exact (hCs C hC).2.1 x hx
      · intro hx
        have hxc : x ∈ Cs.flatten ++ t := hc ▸ mem_cycList w₀ x
        rcases List.mem_append.mp hxc with h | h
        · obtain ⟨C, hC, hxC⟩ := List.mem_flatten.mp h
          refine ⟨C, hC, ?_⟩
          by_contra hne
          have hxl : x ≠ C.getLast (hCne C hC) := by
            intro e
            exact hne (by rw [e, List.getLast?_eq_some_getLast])
          exact (hCs C hC).2.2 x (List.mem_dropLast_of_mem_of_ne_getLast hxC hxl) hx
        · exact absurd hx (ht x h)
    have hlenCs : Cs.length = n + 1 := by
      rw [← endsOf_length hCne, ← hX, ← hendsX,
        List.toFinset_card_of_nodup ((endsOf_sublist hCne).nodup (List.nodup_append.mp hcnd).1)]
    obtain ⟨C₀, Rest, rfl⟩ : ∃ C₀ Rest, Cs = C₀ :: Rest := by
      rcases Cs with _ | ⟨C₀, Rest⟩
      · simp at hlenCs
      · exact ⟨C₀, Rest, rfl⟩
    have hRest : Rest.length = n := by simpa using hlenCs
    -- `C₀ = N :: a`
    obtain ⟨a', hC₀⟩ : ∃ a', C₀ = Fin.last m :: a' := by
      have hC₀ne := hCne C₀ List.mem_cons_self
      rcases C₀ with _ | ⟨c, a'⟩
      · exact absurd rfl hC₀ne
      · refine ⟨a', ?_⟩
        have := congrArg List.head? hc
        simp [cycList] at this
        rw [this]
    subst hC₀
    let v' : Fin n → List (Fin (m + 1)) := fun i => Rest[i.1]'(by omega)
    have hv'Rest : List.ofFn v' = Rest := by
      apply List.ext_getElem (by simp [hRest])
      intro i h1 h2
      simp [v']
    have hlist : Fin.last m :: (a' ++ (List.ofFn v').flatten ++ t) = cycList w₀ := by
      rw [hv'Rest, hc]
      simp
    let K : BlockConfig m n :=
      { a := a', b := t, v := v'
        v_ne := fun i => hCne _ (List.mem_cons_of_mem _ (List.getElem_mem _))
        nodup := hlist ▸ cycList_nodup w₀
        cover := fun x => hlist ▸ mem_cycList w₀ x }
    have hKtau : K.tau = τ * π₀ := by
      show formPerm (Fin.last m :: (a' ++ (List.ofFn v').flatten ++ t)) = τ * π₀
      rw [hlist, ← hw₀]
      rfl
    have hsplits : K.Splits X := by
      have hblocks : ∀ B, (B = K.B0 ∨ B ∈ List.ofFn K.v) →
          (B = t ++ Fin.last m :: a' ∨ B ∈ Rest) := by
        intro B hB
        rcases hB with rfl | hB
        · exact Or.inl rfl
        · exact Or.inr (hv'Rest ▸ hB)
      constructor
      · intro B hB x hx
        rcases hblocks B hB with rfl | hB
        · rw [List.dropLast_append_of_ne_nil (by simp)] at hx
          rcases List.mem_append.mp hx with h | h
          · exact ht x h
          · exact (hCs _ List.mem_cons_self).2.2 x h
        · exact (hCs B (List.mem_cons_of_mem _ hB)).2.2 x hx
      · intro B hB x hx
        rcases hblocks B hB with rfl | hB
        · rw [List.getLast?_append_of_ne_nil _ (by simp)] at hx
          exact (hCs _ List.mem_cons_self).2.1 x hx
        · exact (hCs B (List.mem_cons_of_mem _ hB)).2.1 x hx
    refine ⟨((Perm.sign π₀ : ℤ) : F) • sandwichElem F (a'.map Fin.val) (fun i => (v' i).map Fin.val)
      (t.map Fin.val), Or.inr ⟨_, _, _, _, ?_, ?_, rfl⟩, ?_⟩
    · -- the triple is multilinear
      refine ⟨fun i => by simpa using K.v_ne i, ?_⟩
      have e : a'.map Fin.val ++ (List.ofFn fun i => (v' i).map Fin.val).flatten ++ t.map Fin.val =
          wordList w₀ := by
        rw [← map_val_cycList_tail]
        have := congrArg List.tail hlist
        simp only [List.tail_cons] at this
        rw [show List.ofFn (fun i => (w₀ i).castSucc) = (cycList w₀).tail from rfl, ← this]
        simp [List.map_flatten, List.map_ofFn, Function.comp_def]
      rw [e]
      exact wordList_perm_range w₀
    · rcases Int.units_eq_one_or (Perm.sign π₀) with h | h <;> simp [h]
    · intro w
      rw [coeff_mul_sym F τ π₀ _ X hπ₀X, ← hKtau, K.coeff_eq F hn hm hsplits w, MonoidAlgebra.coeff_smul,
        Finsupp.smul_apply, smul_eq_mul]
  · refine ⟨0, Or.inl rfl, fun w => ?_⟩
    rw [coeff_perm_mul_altSum, ite_eq_right]
    · rfl
    · intro hsub
      apply hex
      refine ⟨τ⁻¹ * wordCycle w, hsub, ?_⟩
      rw [mul_inv_cancel_left]
      exact wordCycle_isFullCycle hm w

open Arcs in
/-- **B3, the converse** (end of paper step (6)): every multilinear `a · L(v_1, …, v_n) · b` is the `N`-cycle part
of some `τ E_X` with `|X| = n + 1`. -/
theorem converse_block_lemma {m n : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) (a : List ℕ) (v : Fin n → List ℕ)
    (b : List ℕ) (h : IsMultilinTriple m a v b) :
    ∃ (τ : Perm (Fin (m + 1))) (X : Finset (Fin (m + 1))), X.card = n + 1 ∧
      ∀ w : Perm (Fin m), (perm F τ * altSum F X).coeff (wordCycle w) =
        (sandwichElem F a v b).coeff (wordMono w) := by
  have hm : 1 ≤ m := le_trans hn hnm
  obtain ⟨hvne, hperm⟩ := h
  let toPt : ℕ → Fin (m + 1) := fun k => Fin.ofNat (m + 1) k
  have hlt : ∀ k ∈ a ++ (List.ofFn v).flatten ++ b, k < m := fun k hk =>
    List.mem_range.mp (hperm.mem_iff.mp hk)
  have hval : ∀ k, k < m → (toPt k : ℕ) = k := fun k hk => by
    simp only [toPt, Fin.val_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hmapval : ∀ L : List ℕ, (∀ k ∈ L, k < m) → (L.map toPt).map Fin.val = L := by
    intro L hL
    rw [List.map_map]
    conv_rhs => rw [← List.map_id L]
    exact List.map_congr_left (fun k hk => hval k (hL k hk))
  have hall : (Fin.last m :: (a.map toPt ++ (List.ofFn fun i => (v i).map toPt).flatten ++ b.map toPt)) =
      Fin.last m :: (a ++ (List.ofFn v).flatten ++ b).map toPt := by
    simp [List.map_flatten, List.map_ofFn, Function.comp_def]
  have hnd0 : (a ++ (List.ofFn v).flatten ++ b).Nodup := hperm.nodup_iff.mpr List.nodup_range
  let K : BlockConfig m n :=
    { a := a.map toPt, b := b.map toPt, v := fun i => (v i).map toPt
      v_ne := fun i => by simpa using hvne i
      nodup := by
        rw [hall]
        refine List.nodup_cons.mpr ⟨?_, hnd0.map_on ?_⟩
        · intro hmem
          obtain ⟨k, hk, hkl⟩ := List.mem_map.mp hmem
          have := congrArg Fin.val hkl
          rw [hval k (hlt k hk), Fin.val_last] at this
          exact absurd (hlt k hk) (by omega)
        · intro x hx y hy hxy
          rw [← hval x (hlt x hx), ← hval y (hlt y hy), hxy]
      cover := by
        intro x
        rw [hall]
        rcases Fin.eq_castSucc_or_eq_last x with ⟨j, rfl⟩ | rfl
        · refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j, hperm.mem_iff.mpr (List.mem_range.mpr j.isLt), ?_⟩)
          ext
          simp [hval j j.isLt]
        · exact List.mem_cons_self }
  refine ⟨K.tau, K.ends, K.card_ends, fun w => ?_⟩
  rw [K.coeff_eq F hn hm K.splits_ends w]
  have ha : K.a.map Fin.val = a := hmapval a (fun k hk => hlt k (by simp [hk]))
  have hb : K.b.map Fin.val = b := hmapval b (fun k hk => hlt k (by simp [hk]))
  have hv : (fun i => (K.v i).map Fin.val) = v := by
    funext i
    exact hmapval (v i) (fun k hk => hlt k
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatten.mpr ⟨v i, List.mem_ofFn.mpr ⟨i, rfl⟩, hk⟩))))
  rw [ha, hb, hv]

/-! ## 8. Step (2): `I = span {τ E_X : |X| = n + 1}` (B4), and (F1) elements are multilinear (B5) -/

namespace Arcs

/-- `E_X σ = σ E_{σ⁻¹ X}`. -/
theorem altSum_mul_perm {N : ℕ} (X : Finset (Fin N)) (σ : Perm (Fin N)) :
    altSum F X * perm F σ = perm F σ * altSum F (X.map σ⁻¹.toEmbedding) := by
  unfold altSum
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_equiv (MulAut.conj σ⁻¹).toEquiv ?_ ?_
  · intro π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
      MulAut.conj_apply]
    rw [Perm.support_conj, Finset.map_subset_map]
  · intro π _
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, smul_mul_assoc,
      mul_smul_comm, perm, MonoidAlgebra.single_mul_single, mul_one]
    have hs : Perm.sign (σ⁻¹ * π * σ⁻¹⁻¹) = Perm.sign π := by
      rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, inv_inv, mul_comm, ← mul_assoc, Int.units_mul_self,
        one_mul]
    rw [hs]
    congr 2
    group

/-- `σ₁ E_X σ₂ = (σ₁ σ₂) E_{σ₂⁻¹ X}` (paper, step (2): `gEh = (gh) E_{h⁻¹[n+1]}`). -/
theorem perm_mul_altSum_mul_perm {N : ℕ} (σ₁ σ₂ : Perm (Fin N)) (X : Finset (Fin N)) :
    perm F σ₁ * altSum F X * perm F σ₂ = perm F (σ₁ * σ₂) * altSum F (X.map σ₂⁻¹.toEmbedding) := by
  rw [mul_assoc, altSum_mul_perm, ← mul_assoc]
  simp only [perm, MonoidAlgebra.single_mul_single, mul_one]

theorem card_filter_val_le {N n : ℕ} (hn : n + 1 ≤ N) :
    (Finset.univ.filter (fun i : Fin N => (i : ℕ) ≤ n)).card = n + 1 := by
  have e : Finset.univ.filter (fun i : Fin N => (i : ℕ) ≤ n) = Finset.Iic ⟨n, by omega⟩ := by
    ext i
    simp [Fin.le_def]
  rw [e, Fin.card_Iic]

/-- Any two `(n+1)`-subsets are moved onto each other by a permutation. -/
theorem exists_perm_map_eq {N : ℕ} {X Y : Finset (Fin N)} (h : X.card = Y.card) :
    ∃ g : Perm (Fin N), X.map g.toEmbedding = Y := by
  have e1 : {x // x ∈ X} ≃ {x // x ∈ Y} := Fintype.equivOfCardEq (by simp [h])
  have e2 : {x // ¬ x ∈ X} ≃ {x // ¬ x ∈ Y} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]; simp [h])
  refine ⟨Equiv.subtypeCongr e1 e2, ?_⟩
  refine Finset.eq_of_subset_of_card_le ?_ (by simp [h])
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
  have : (Equiv.subtypeCongr e1 e2) x = e1 ⟨x, hx⟩ := by
    simp [Equiv.subtypeCongr, Equiv.sumCompl, hx]
  rw [Equiv.toEmbedding_apply, this]
  exact (e1 ⟨x, hx⟩).2

end Arcs

open Arcs in
/-- **B4, step (2), first half**: `g E h ∈ span {τ E_X : |X| = n + 1}` for all `g, h ∈ F[S_N]`. -/
theorem mul_altGen_mul_mem_span {N n : ℕ} (hn : n + 1 ≤ N) (g h : GrpAlg F N) :
    g * altGen F N n * h ∈ Submodule.span F
      {x | ∃ (τ : Perm (Fin N)) (X : Finset (Fin N)), X.card = n + 1 ∧ x = perm F τ * altSum F X} := by
  have hof : ∀ σ : Perm (Fin N), MonoidAlgebra.of F (Perm (Fin N)) σ = perm F σ := fun σ => rfl
  induction g using MonoidAlgebra.induction_on with
  | of σ₁ =>
    induction h using MonoidAlgebra.induction_on with
    | of σ₂ =>
      rw [hof, hof]
      refine Submodule.subset_span ⟨σ₁ * σ₂, _, ?_, perm_mul_altSum_mul_perm F σ₁ σ₂ _⟩
      rw [Finset.card_map]
      exact card_filter_val_le hn
    | add x y hx hy =>
      rw [mul_add]
      exact Submodule.add_mem _ hx hy
    | smul r x hx =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ r hx
  | add x y hx hy =>
    rw [add_mul, add_mul]
    exact Submodule.add_mem _ hx hy
  | smul r x hx =>
    rw [smul_mul_assoc, smul_mul_assoc]
    exact Submodule.smul_mem _ r hx

open Arcs in
/-- **Step (2)** in full (paper, v1.02 line 252): `I = span {τ E_X : τ ∈ S_N, |X| = n + 1}`. -/
theorem altIdeal_eq_span {N n : ℕ} (hn : n + 1 ≤ N) :
    altIdeal F N n = Submodule.span F
      {x | ∃ (τ : Perm (Fin N)) (X : Finset (Fin N)), X.card = n + 1 ∧ x = perm F τ * altSum F X} := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨g, h, rfl⟩
    exact mul_altGen_mul_mem_span F hn g h
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨τ, X, hX, rfl⟩
    -- move `X` onto `{0, …, n}` and conjugate
    obtain ⟨g, hg⟩ := exists_perm_map_eq (X := Finset.univ.filter (fun i : Fin N => (i : ℕ) ≤ n)) (Y := X)
      (by rw [card_filter_val_le hn, hX])
    have key : perm F τ * altSum F X =
        perm F (τ * g) * altGen F N n * perm F g⁻¹ := by
      unfold altGen
      rw [perm_mul_altSum_mul_perm, inv_inv, mul_inv_cancel_right, hg]
    rw [key]
    exact Submodule.subset_span ⟨_, _, rfl⟩

open Arcs in
/-- **B5**: every spanning element `a · L(v_1, …, v_n) · b` of (F1) (multilinear) lies in `V_m`. -/
theorem sandwichElem_mem_multilinSpace {m n : ℕ} (hm : 1 ≤ m) (a : List ℕ) (v : Fin n → List ℕ)
    (b : List ℕ) (h : IsMultilinTriple m a v b) : sandwichElem F a v b ∈ multilinSpace F m := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : symSum 0 (fun i => wordOf F (v i)) = 0 := by simp [symSum, tupleProd]
    simp only [sandwichElem, sandwich, h0, mul_zero]
    split_ifs <;> exact Submodule.zero_mem _
  · rw [sandwichElem_eq_sum F hn a b v h.1]
    refine Submodule.sum_mem _ (fun π _ => ?_)
    have hp : (a ++ (List.ofFn (v ∘ π)).flatten ++ b).Perm (List.range m) :=
      ((((π.ofFn_comp_perm v).flatten).append_left a).append_right b).trans h.2
    obtain ⟨w, hw⟩ := exists_wordList_eq hp
    rw [← hw, show monoOf (wordList w) = wordMono w from rfl, ← multilinWord_eq_single F hm w]
    exact Submodule.subset_span ⟨w, rfl⟩

end NagataHigman.Proofs

end
