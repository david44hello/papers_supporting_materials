/-
EulerFlow/Sec4/Decomp.lean — Section 4 opening (tex l.321-332): every finite abelian group has a cyclic
decomposition, the properties of the small set `S`, and helper lemmas on parts and colours.
-/
import EulerFlow.Defs.Constructions

namespace EulerFlow

open Finset

namespace CyclicDecomp

variable {A : Type} [AddCommGroup A] (D : CyclicDecomp A)

/-- Two decompositions into parts with the same sum are equal (uniqueness of the parts). -/
theorem parts_ext {c c' : Fin D.r → A} (hc : ∀ k, c k ∈ AddSubgroup.zmultiples (D.s k))
    (hc' : ∀ k, c' k ∈ AddSubgroup.zmultiples (D.s k)) (h : ∑ k, c k = ∑ k, c' k) : c = c' :=
  (D.parts_unique (∑ k, c' k)).unique ⟨hc, h⟩ ⟨hc', rfl⟩

/-- A one-part decomposition: `x ∈ ⟨s_k⟩` placed at the index `k`. -/
theorem single_mem {k : Fin D.r} {x : A} (hx : x ∈ AddSubgroup.zmultiples (D.s k)) (l : Fin D.r) :
    (Pi.single k x : Fin D.r → A) l ∈ AddSubgroup.zmultiples (D.s l) := by
  by_cases h : l = k
  · subst h; simpa using hx
  · simp [h]

/-- `±s_k ∈ ⟨s_k⟩`. -/
theorem pm_mem {k : Fin D.r} {x : A} (hx : x = D.s k ∨ x = -D.s k) :
    x ∈ AddSubgroup.zmultiples (D.s k) := by
  rcases hx with rfl | rfl
  · exact AddSubgroup.mem_zmultiples _
  · exact (AddSubgroup.zmultiples _).neg_mem (AddSubgroup.mem_zmultiples _)

/-- `±s_k ≠ 0`. -/
theorem pm_ne_zero {k : Fin D.r} {x : A} (hx : x = D.s k ∨ x = -D.s k) : x ≠ 0 := by
  rcases hx with rfl | rfl
  · exact D.s_ne k
  · exact neg_ne_zero.mpr (D.s_ne k)

/-- The groups `⟨s_k⟩` and `⟨s_j⟩`, `k ≠ j`, meet only in `0`. -/
theorem eq_zero_of_mem_mem {k j : Fin D.r} (hkj : k ≠ j) {x : A}
    (hk : x ∈ AddSubgroup.zmultiples (D.s k)) (hj : x ∈ AddSubgroup.zmultiples (D.s j)) : x = 0 := by
  have h := D.parts_ext (D.single_mem hk) (D.single_mem hj) (by simp)
  have := congrFun h k
  simpa [Pi.single_apply, hkj] using this

theorem colour_unique (D : CyclicDecomp A) {x : A} {k j : Fin D.r} (hk : x = D.s k ∨ x = -D.s k)
    (hj : x = D.s j ∨ x = -D.s j) : k = j := by
  by_contra hkj
  exact D.pm_ne_zero hk (D.eq_zero_of_mem_mem hkj (D.pm_mem hk) (D.pm_mem hj))

theorem small_sum_eq (D : CyclicDecomp A) {t₃ t₄ a b : A} (h₃ : t₃ ∈ D.S) (h₄ : t₄ ∈ D.S) {i j : Fin D.r}
    (ha : a = D.s i ∨ a = -D.s i) (hb : b = D.s j ∨ b = -D.s j) (hij : i ≠ j) (h : t₃ + t₄ = a - b) :
    t₃ = a ∨ t₄ = a := by
  classical
  obtain ⟨k₃, hk₃⟩ := h₃
  obtain ⟨k₄, hk₄⟩ := h₄
  have hb' : -b ∈ AddSubgroup.zmultiples (D.s j) := (AddSubgroup.zmultiples _).neg_mem (D.pm_mem hb)
  have hpart := D.parts_ext
    (c := fun l => (Pi.single k₃ t₃ : Fin D.r → A) l + (Pi.single k₄ t₄ : Fin D.r → A) l)
    (c' := fun l => (Pi.single i a : Fin D.r → A) l + (Pi.single j (-b) : Fin D.r → A) l)
    (fun l => add_mem (D.single_mem (D.pm_mem hk₃) l) (D.single_mem (D.pm_mem hk₄) l))
    (fun l => add_mem (D.single_mem (D.pm_mem ha) l) (D.single_mem hb' l))
    (by simp [Finset.sum_add_distrib, h, sub_eq_add_neg])
  have hi := congrFun hpart i
  have hj := congrFun hpart j
  have hji : j ≠ i := Ne.symm hij
  have ha0 := D.pm_ne_zero ha
  have hb0 := D.pm_ne_zero hb
  by_cases h3 : i = k₃ <;> by_cases h4 : i = k₄
  · subst h3; subst h4
    simp [hji] at hj
    exact absurd hj hb0
  · subst h3
    left; simpa [hji, h4] using hi
  · subst h4
    right; simpa [hji, h3] using hi
  · simp [hji, h3, h4] at hi
    exact absurd hi.symm ha0

theorem closure_S_eq_closure_submonoid (D : CyclicDecomp A) : ((AddSubgroup.closure D.S : Set A)) =
    (AddSubmonoid.closure D.S : Set A) := by
  have hneg : -D.S = D.S := by
    ext x
    simp only [Set.mem_neg, S, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨k, hk | hk⟩
      · exact ⟨k, Or.inr (neg_eq_iff_eq_neg.mp hk)⟩
      · exact ⟨k, Or.inl (neg_eq_iff_eq_neg.mp hk |>.trans (neg_neg _))⟩
    · rintro ⟨k, hk | hk⟩
      · exact ⟨k, Or.inr (by rw [hk])⟩
      · exact ⟨k, Or.inl (by rw [hk, neg_neg])⟩
  have := AddSubgroup.closure_toAddSubmonoid D.S
  rw [hneg, Set.union_self] at this
  rw [← this]
  rfl

end CyclicDecomp

/-- Section 4 (tex l.329): `S = -S`, `0 ∉ S`, and `S` generates `A`. -/
theorem sec4_S_props_proved {A : Type} [AddCommGroup A] (D : CyclicDecomp A) :
    (∀ x ∈ D.S, -x ∈ D.S) ∧ (0 : A) ∉ D.S ∧ AddSubgroup.closure D.S = ⊤ := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨k, hk | hk⟩
    · exact ⟨k, Or.inr (by rw [hk])⟩
    · exact ⟨k, Or.inl (by rw [hk, neg_neg])⟩
  · rintro ⟨k, hk⟩
    exact D.pm_ne_zero hk rfl
  · rw [eq_top_iff]
    intro a _
    obtain ⟨c, ⟨hc, hsum⟩, -⟩ := D.parts_unique a
    rw [← hsum]
    refine AddSubgroup.sum_mem _ fun k _ => ?_
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp (hc k)
    rw [← hz]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (show D.s k ∈ D.S from ⟨k, Or.inl rfl⟩)) z

/-! ### Existence of a cyclic decomposition -/

namespace CyclicDecomp

section Exists

variable {A : Type} [AddCommGroup A] {ι : Type} [DecidableEq ι] {n : ι → ℕ}

/-- In `Π i, ZMod (n i)`, every element of the `i`-th summand is an integer multiple of `Pi.single i 1`. -/
theorem piZMod_single_mem (i : ι) (x : ZMod (n i)) :
    (Pi.single i x : (i : ι) → ZMod (n i)) ∈ AddSubgroup.zmultiples (Pi.single i 1) := by
  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨(ZMod.cast x : ℤ), ?_⟩
  rw [← Pi.single_smul, zsmul_one, ZMod.intCast_zmod_cast]

/-- An integer multiple of `Pi.single i 1` vanishes off the index `i`. -/
theorem piZMod_apply_eq_zero {i i' : ι} (hii' : i' ≠ i) {y : (i : ι) → ZMod (n i)}
    (hy : y ∈ AddSubgroup.zmultiples (Pi.single i 1)) : y i' = 0 := by
  obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
  simp [hii']

/-- The cyclic decomposition transported from `Π i, ZMod (n i)` along `φ`, indices enumerated by `σ`. -/
noncomputable def ofPiZMod [Fintype ι] (hn : ∀ i, 1 < n i) (φ : A ≃+ ((i : ι) → ZMod (n i))) {r : ℕ}
    (σ : ι ≃ Fin r) : CyclicDecomp A where
  r := r
  s k := φ.symm (Pi.single (σ.symm k) 1)
  s_ne k := by
    have : Fact (1 < n (σ.symm k)) := ⟨hn _⟩
    simp
  parts_unique a := by
    have hmem : ∀ {k : Fin r} {y : (i : ι) → ZMod (n i)},
        y ∈ AddSubgroup.zmultiples (Pi.single (σ.symm k) 1) →
        φ.symm y ∈ AddSubgroup.zmultiples (φ.symm (Pi.single (σ.symm k) 1)) := by
      intro k y hy
      obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨z, (map_zsmul φ.symm z _).symm⟩
    refine ⟨fun k => φ.symm (Pi.single (σ.symm k) (φ a (σ.symm k))),
      ⟨fun k => hmem (piZMod_single_mem _ _), ?_⟩, ?_⟩
    · rw [← map_sum, Equiv.sum_comp σ.symm (fun i => Pi.single i (φ a i)), Finset.univ_sum_single,
        AddEquiv.symm_apply_apply]
    · rintro c' ⟨hc', hsum⟩
      funext k
      have key : ∀ l, φ (c' l) ∈ AddSubgroup.zmultiples (Pi.single (σ.symm l) 1) := by
        intro l
        obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp (hc' l)
        exact AddSubgroup.mem_zmultiples_iff.mpr
          ⟨z, by rw [← hz, map_zsmul, AddEquiv.apply_symm_apply]⟩
      rw [AddEquiv.eq_symm_apply]
      funext i
      by_cases hi : i = σ.symm k
      · subst hi
        rw [Pi.single_eq_same, ← hsum, map_sum, Finset.sum_apply, Finset.sum_eq_single k]
        · intro l _ hl
          exact piZMod_apply_eq_zero (σ.symm.injective.ne (Ne.symm hl)) (key l)
        · intro hk; exact absurd (Finset.mem_univ k) hk
      · rw [Pi.single_eq_of_ne hi]
        exact piZMod_apply_eq_zero hi (key k)

end Exists

end CyclicDecomp

/-- Section 4 (tex l.323-327): every finite abelian group is a direct sum of cyclic groups `⟨s_k⟩`, `s_k ≠ 0`. -/
theorem sec4_decomp_exists_proved (A : Type) [AddCommGroup A] [Fintype A] : Nonempty (CyclicDecomp A) := by
  classical
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' A
  exact ⟨CyclicDecomp.ofPiZMod hn (e.trans (DirectSum.addEquivProd _)) (Fintype.equivFin ι)⟩

end EulerFlow
