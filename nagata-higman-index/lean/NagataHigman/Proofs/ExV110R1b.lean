/-
NagataHigman/Proofs/ExV110R1b.lean — project 011 v1.10 FINAL, coverage review r1: MUST-4 ((F6) extension of scalars),
SHOULD-8 (`IsMultilinWordIn`: a nonempty word whose letters are a permutation of 0, …, n-1 — a definition used in the
statement of `F1_L_multilinear_coeff`; checked faithful by the coordinator). The rows are in Paper/Statements.lean.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. Paper v1.10.
-/
import NagataHigman.Proofs.ExV110

universe u

noncomputable section

open NagataHigman Equiv Finset Matrix Module Submodule Set

namespace NagataHigman.Proofs.ExV110R1b

/-- Extending scalars does not change the dimension of the span of a finite family of `d × d` matrices: a linearly
independent subfamily stays independent over `K` (`linearIndependent_algebraMap_comp_iff`), and it still spans. -/
theorem finrank_span_map_algebraMap {F K : Type*} [Field F] [Field K] [Algebra F K] {ι : Type*} [Finite ι] {d : ℕ}
    (v : ι → Matrix (Fin d) (Fin d) F) :
    finrank F (span F (range v)) = finrank K (span K (range fun i => (v i).map (algebraMap F K))) := by
  classical
  obtain ⟨s, hsv, hspan, hli⟩ := exists_linearIndependent F (range v)
  have : Fintype s := ((Set.finite_range v).subset hsv).fintype
  have hF : finrank F (span F (range v)) = Fintype.card s := by
    have h := finrank_span_eq_card hli
    rwa [Subtype.range_coe, hspan] at h
  -- the scalar extension, as an `F`-linear map
  let φ : Matrix (Fin d) (Fin d) F →ₗ[F] Matrix (Fin d) (Fin d) K :=
    { toFun := fun A => A.map (algebraMap F K)
      map_add' := fun A B => by ext i j; simp
      map_smul' := fun c A => by
        ext i j
        simp only [Matrix.map_apply, Matrix.smul_apply, RingHom.id_apply, smul_eq_mul, map_mul]
        rw [Algebra.smul_def] }
  -- flatten to vectors indexed by `Fin d × Fin d`, extend scalars there, and fold back
  let flatF : Matrix (Fin d) (Fin d) F →ₗ[F] (Fin d × Fin d → F) :=
    { toFun := fun A p => A p.1 p.2, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let foldK : (Fin d × Fin d → K) →ₗ[K] Matrix (Fin d) (Fin d) K :=
    { toFun := fun w => Matrix.of fun i j => w (i, j), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hflat : LinearMap.ker flatF = ⊥ := by
    refine LinearMap.ker_eq_bot_of_injective fun A B h => ?_
    ext i j
    exact congrFun h (i, j)
  have hfold : LinearMap.ker foldK = ⊥ := by
    refine LinearMap.ker_eq_bot_of_injective fun w w' h => ?_
    funext p
    exact congrFun (congrFun h p.1) p.2
  have h1 : LinearIndependent F (fun x : s => flatF x) := hli.map' flatF hflat
  have h2 : LinearIndependent K (fun x : s => algebraMap F K ∘ flatF x) :=
    linearIndependent_algebraMap_comp_iff.mpr h1
  have hliK : LinearIndependent K (fun x : s => φ x) := by
    have h3 := h2.map' foldK hfold
    convert h3 using 1
    funext x
    ext i j
    rfl
  have hspanK : span K (range fun i => (v i).map (algebraMap F K)) = span K (range fun x : s => φ x) := by
    apply le_antisymm
    · rw [span_le]
      rintro _ ⟨i, rfl⟩
      have hvi : v i ∈ span F s := hspan ▸ subset_span ⟨i, rfl⟩
      have hmap : φ (v i) ∈ span F (φ '' s) := by
        rw [← Submodule.map_span]
        exact ⟨v i, hvi, rfl⟩
      have himg : φ '' s = range fun x : s => φ x := by
        ext y
        simp
      rw [himg] at hmap
      exact span_le_restrictScalars F K _ hmap
    · rw [span_le]
      rintro _ ⟨x, rfl⟩
      obtain ⟨i, hi⟩ := hsv x.2
      exact subset_span ⟨i, by simp only [hi]; rfl⟩
  rw [hF, hspanK, finrank_span_eq_card hliK]

/-- A word of the free semigroup is MULTILINEAR in `x_0, …, x_{n-1}`: it has length `n` and each of the letters
`0, …, n-1` occurs exactly once (its letter list is a permutation of `[0, …, n-1]`). -/
def IsMultilinWordIn (n : ℕ) (w : FreeSemigroup ℕ) : Prop := (w.head :: w.tail).Perm (List.range n)

instance (n : ℕ) : DecidablePred (IsMultilinWordIn n) := fun w =>
  inferInstanceAs (Decidable ((w.head :: w.tail).Perm (List.range n)))

/-- A nonempty letter list whose monomial is `w` is the letter list of `w`. -/
theorem ofFn_eq_of_monoOf_eq {n : ℕ} (hn : 1 ≤ n) (f : Fin n → ℕ) (w : FreeSemigroup ℕ)
    (h : NagataHigman.Proofs.monoOf (List.ofFn f) = w) : List.ofFn f = w.head :: w.tail := by
  obtain ⟨hd, tl⟩ := w
  rcases hl : List.ofFn f with _ | ⟨x, l⟩
  · simp only [List.ofFn_eq_nil_iff] at hl
    omega
  · rw [hl] at h
    simp only [NagataHigman.Proofs.monoOf, FreeSemigroup.mk.injEq] at h
    rw [h.1, h.2]

end NagataHigman.Proofs.ExV110R1b

end
