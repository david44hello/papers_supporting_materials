/-
EulerFlow/Concrete/K5Tri.lean — paper 002, Remark 2.6 (tex l.205-207): `K₅` is triangularly connected in the sense of
[CLSWX] (`IsTriConnectedOn Set.univ`).
Route: `arc u v` is the dart from `u` to `v` (`u ≠ v`), `tri p q r` the triangle `p → q → r → p`. For edges `ab` and
`cd`, pick a vertex `x` off `a, b, c, d` (K₅ has five). If `a = c`: the triangles `abx`, `adx` share the edge `ax`.
Otherwise: `abx`, `acx`, `cdx`, consecutive ones sharing `ax` and `cx`.
-/
import EulerFlow.Defs.Constructions

namespace EulerFlow

namespace K5Tri

open MGraph

/-- The edges of `K₅`. -/
abbrev Ed := {pr : Fin 5 × Fin 5 // pr.1 < pr.2}

/-- The dart of `K₅` from `u` to `v` (for `u ≠ v`; the last branch is never used). -/
def arc (u v : Fin 5) : Ed × Bool :=
  if h : u < v then (⟨(u, v), h⟩, false)
  else if h' : v < u then (⟨(v, u), h'⟩, true) else (⟨(0, 1), by decide⟩, false)

lemma tail_arc {u v : Fin 5} (h : u ≠ v) : K5.dartTail (arc u v) = u := by
  unfold arc
  split_ifs with h1 h2
  · rfl
  · rfl
  · exact absurd (le_antisymm (not_lt.1 h2) (not_lt.1 h1)) h

lemma head_arc {u v : Fin 5} (h : u ≠ v) : K5.dartHead (arc u v) = v := by
  unfold arc
  split_ifs with h1 h2
  · rfl
  · rfl
  · exact absurd (le_antisymm (not_lt.1 h2) (not_lt.1 h1)) h

lemma arc_fst_of_lt {u v : Fin 5} (h : u < v) : (arc u v).1 = ⟨(u, v), h⟩ := by
  simp [arc, h]

lemma arc_fst_comm {u v : Fin 5} (h : u ≠ v) : (arc u v).1 = (arc v u).1 := by
  rcases lt_or_gt_of_ne h with h1 | h1
  · simp [arc, h1, not_lt.2 h1.le]
  · simp [arc, h1, not_lt.2 h1.le]

/-- Two darts lie on one edge only if they join the same two vertices. -/
lemma arc_fst_eq {u v x y : Fin 5} (huv : u ≠ v) (hxy : x ≠ y) (h : (arc u v).1 = (arc x y).1) :
    (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
  have key : ∀ {u v : Fin 5}, u ≠ v → ((arc u v).1.1.1 = u ∧ (arc u v).1.1.2 = v) ∨
      ((arc u v).1.1.1 = v ∧ (arc u v).1.1.2 = u) := by
    intro u v huv
    unfold arc
    split_ifs with h1 h2
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd (le_antisymm (not_lt.1 h2) (not_lt.1 h1)) huv
  have h1 : (arc u v).1.1.1 = (arc x y).1.1.1 := by rw [h]
  have h2 : (arc u v).1.1.2 = (arc x y).1.1.2 := by rw [h]
  rcases key huv with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases key hxy with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
    rw [a1, b1] at h1 <;> rw [a2, b2] at h2 <;> simp [h1, h2]

/-- The triangle `p → q → r → p` of `K₅`. -/
def tri (p q r : Fin 5) (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p) : K5.DirCycle where
  darts := [arc p q, arc q r, arc r p]
  ne_nil := by simp
  chain := by simp [head_arc hpq, tail_arc hqr, head_arc hqr, tail_arc hrp]
  closes := by simp [head_arc hrp, tail_arc hpq]
  edges_nodup := by
    have h1 : (arc p q).1 ≠ (arc q r).1 := fun h => by
      rcases arc_fst_eq hpq hqr h with ⟨e1, -⟩ | ⟨e1, -⟩
      · exact hpq e1
      · exact hrp e1.symm
    have h2 : (arc p q).1 ≠ (arc r p).1 := fun h => by
      rcases arc_fst_eq hpq hrp h with ⟨e1, -⟩ | ⟨-, e2⟩
      · exact hrp e1.symm
      · exact hqr e2
    have h3 : (arc q r).1 ≠ (arc r p).1 := fun h => by
      rcases arc_fst_eq hqr hrp h with ⟨e1, -⟩ | ⟨e1, -⟩
      · exact hqr e1
      · exact hpq e1.symm
    simp [h1, h2, h3]
  tails_nodup := by
    simp [tail_arc hpq, tail_arc hqr, tail_arc hrp, hpq, hqr, Ne.symm hrp]

/-- `K₅` has five vertices: four of them leave a fifth one. -/
lemma exists_fifth : ∀ a b c d : Fin 5, ∃ x : Fin 5, x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d := by
  decide

/-- `K₅` is triangularly connected (Remark 2.6, tex l.205-207). -/
theorem triConnected : K5.IsTriConnectedOn Set.univ := by
  rintro ⟨⟨a, b⟩, hab⟩ - ⟨⟨c, d⟩, hcd⟩ -
  obtain ⟨x, hxa, hxb, hxc, hxd⟩ := exists_fifth a b c d
  have hab' : a ≠ b := ne_of_lt hab
  have hcd' : c ≠ d := ne_of_lt hcd
  by_cases hac : a = c
  · subst hac
    refine ⟨[tri a b x hab' hxb.symm hxa, tri a d x hcd' hxd.symm hxa], by simp, ?_, ?_, ?_, ?_⟩
    · intro T hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
      rcases hT with rfl | rfl <;> exact ⟨rfl, fun _ _ => Set.mem_univ _⟩
    · exact ⟨arc a b, by simp [tri], arc_fst_of_lt hab⟩
    · exact ⟨arc a d, by simp [tri], arc_fst_of_lt hcd⟩
    · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
      exact ⟨arc x a, by simp [tri], arc x a, by simp [tri], rfl⟩
  · refine ⟨[tri a b x hab' hxb.symm hxa, tri a c x hac hxc.symm hxa, tri c d x hcd' hxd.symm hxc], by simp, ?_, ?_,
      ?_, ?_⟩
    · intro T hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
      rcases hT with rfl | rfl | rfl <;> exact ⟨rfl, fun _ _ => Set.mem_univ _⟩
    · exact ⟨arc a b, by simp [tri], arc_fst_of_lt hab⟩
    · exact ⟨arc c d, by simp [tri], arc_fst_of_lt hcd⟩
    · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
      exact ⟨⟨arc x a, by simp [tri], arc x a, by simp [tri], rfl⟩,
        ⟨arc c x, by simp [tri], arc x c, by simp [tri], arc_fst_comm hxc.symm⟩⟩

end K5Tri

end EulerFlow
