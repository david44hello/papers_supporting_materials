/-
EulerFlow/Graph/Chi.lean — paper 002 foundation: the dart algebra of a directed cycle `Q`:
the heads of `Q` are a permutation of its tails, `χ_Q` is the sign of the dart on the edges of `Q` and `0`
elsewhere, and `χ_Q` satisfies the flow condition (`DirCycle.chi_isFlow`).
-/
import EulerFlow.Graph.CycleFind

namespace EulerFlow

namespace MGraph

open Finset

variable {V E : Type} (G : MGraph V E)

/-- The sign of a dart: `1` along the reference direction, `-1` against it. -/
def dartSign (b : Bool) : ℤ := if b then -1 else 1

lemma dartSign_ne_zero (b : Bool) : dartSign b ≠ 0 := by cases b <;> simp [dartSign]

/-- Along a chain of darts, the list of heads is the list of tails shifted by one. -/
lemma map_dartHead_of_isChain (d : E × Bool) (rest : List (E × Bool))
    (hc : (d :: rest).IsChain (fun d d' => G.dartHead d = G.dartTail d')) :
    (d :: rest).map G.dartHead = rest.map G.dartTail ++ [G.dartHead ((d :: rest).getLast (by simp))] := by
  induction rest generalizing d with
  | nil => simp
  | cons d1 rest ih =>
    rw [List.isChain_cons_cons] at hc
    rw [List.map_cons, ih d1 hc.2, List.map_cons, hc.1]
    simp

/-- The heads of a directed cycle are a permutation of its tails. -/
lemma DirCycle.heads_perm_tails {G : MGraph V E} (Q : G.DirCycle) :
    (Q.darts.map G.dartHead).Perm (Q.darts.map G.dartTail) := by
  obtain ⟨ds, hne, hc, hcl, _, _⟩ := Q
  simp only
  match ds, hne, hc, hcl with
  | d :: rest, _, hc, hcl =>
    rw [map_dartHead_of_isChain G d rest hc, hcl]
    simp

/-- Two darts of a directed cycle on the same edge are equal. -/
lemma DirCycle.eq_of_fst_eq {G : MGraph V E} (Q : G.DirCycle) {d d' : E × Bool} (hd : d ∈ Q.darts)
    (hd' : d' ∈ Q.darts) (h : d.1 = d'.1) : d = d' :=
  List.inj_on_of_nodup_map Q.edges_nodup hd hd' h

variable [DecidableEq E]

/-- On a dart of `Q`, `χ_Q` is the sign of that dart. -/
lemma DirCycle.chi_of_mem {G : MGraph V E} (Q : G.DirCycle) {d : E × Bool} (hd : d ∈ Q.darts) :
    Q.chi d.1 = dartSign d.2 := by
  rcases d with ⟨e, _ | _⟩
  · simp [DirCycle.chi, hd, dartSign]
  · have hf : (e, false) ∉ Q.darts := fun hf => by
      have := Q.eq_of_fst_eq hf hd rfl
      simp at this
    simp [DirCycle.chi, hd, hf, dartSign]

/-- Off the edges of `Q`, `χ_Q` is `0`. -/
lemma DirCycle.chi_of_not_mem {G : MGraph V E} (Q : G.DirCycle) {e : E}
    (he : e ∉ Q.darts.map Prod.fst) : Q.chi e = 0 := by
  have hf : (e, false) ∉ Q.darts := fun h => he (List.mem_map.2 ⟨_, h, rfl⟩)
  have ht : (e, true) ∉ Q.darts := fun h => he (List.mem_map.2 ⟨_, h, rfl⟩)
  simp [DirCycle.chi, hf, ht]

lemma DirCycle.chi_ne_zero_iff {G : MGraph V E} (Q : G.DirCycle) (e : E) :
    Q.chi e ≠ 0 ↔ e ∈ Q.darts.map Prod.fst := by
  constructor
  · intro h
    by_contra he
    exact h (Q.chi_of_not_mem he)
  · intro he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 he
    rw [Q.chi_of_mem hd]
    exact dartSign_ne_zero _

/-- `χ_Q` takes only the values `-1, 0, 1`. -/
lemma DirCycle.chi_mem {G : MGraph V E} (Q : G.DirCycle) (e : E) :
    Q.chi e = -1 ∨ Q.chi e = 0 ∨ Q.chi e = 1 := by
  by_cases he : e ∈ Q.darts.map Prod.fst
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 he
    rw [Q.chi_of_mem hd]
    cases d.2 <;> simp [dartSign]
  · exact Or.inr (Or.inl (Q.chi_of_not_mem he))

/-- `χ_Q` as a sum over the darts of `Q`. -/
lemma DirCycle.chi_eq_sum {G : MGraph V E} (Q : G.DirCycle) (e : E) :
    Q.chi e = (Q.darts.map (fun d => if d.1 = e then dartSign d.2 else 0)).sum := by
  by_cases he : e ∈ Q.darts.map Prod.fst
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 he
    rw [Q.chi_of_mem hd]
    -- only the dart `d` has the edge `d.1`
    have key : ∀ l : List (E × Bool), (l.map Prod.fst).Nodup → d ∈ l →
        (l.map (fun d' => if d'.1 = d.1 then dartSign d'.2 else 0)).sum = dartSign d.2 := by
      intro l hl hdl
      induction l with
      | nil => simp at hdl
      | cons x l ih =>
        rw [List.map_cons, List.nodup_cons] at hl
        rcases List.mem_cons.1 hdl with rfl | hdl'
        · have : (l.map (fun d' => if d'.1 = d.1 then dartSign d'.2 else 0)).sum = 0 := by
            apply List.sum_eq_zero
            intro y hy
            obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
            have : z.1 ≠ d.1 := fun h => hl.1 (h ▸ List.mem_map_of_mem hz)
            simp [this]
          simp [this]
        · have hx : x.1 ≠ d.1 := fun h => hl.1 (h ▸ List.mem_map_of_mem hdl')
          simp [hx, ih hl.2 hdl']
    exact (key Q.darts Q.edges_nodup hd).symm
  · rw [Q.chi_of_not_mem he]
    symm
    apply List.sum_eq_zero
    intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have : z.1 ≠ e := fun h => he (h ▸ List.mem_map_of_mem hz)
    simp [this]

/-- Exchange a finset sum with a list sum. -/
private lemma finset_sum_list_sum {α β : Type} (s : Finset α) (l : List β) (F : α → β → ℤ) :
    ∑ a ∈ s, (l.map (F a)).sum = (l.map (fun b => ∑ a ∈ s, F a b)).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [Finset.sum_add_distrib, ih]

/-- A list sum of differences. -/
private lemma list_sum_map_sub {β : Type} (l : List β) (F H : β → ℤ) :
    (l.map (fun b => F b - H b)).sum = (l.map F).sum - (l.map H).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]; ring

variable [Fintype E] [DecidableEq V]

omit [DecidableEq V] in
/-- The sum of `χ_Q` over the edges with a property `p`, as a sum over the darts of `Q`. -/
private lemma sum_chi_filter {G : MGraph V E} (Q : G.DirCycle) (p : E → Prop) [DecidablePred p] :
    ∑ e ∈ univ.filter p, Q.chi e = (Q.darts.map (fun d => if p d.1 then dartSign d.2 else 0)).sum := by
  simp_rw [Q.chi_eq_sum]
  rw [finset_sum_list_sum]
  congr 1
  apply List.map_congr_left
  intro d _
  rw [Finset.sum_ite_eq]
  simp

omit [DecidableEq E] [Fintype E] in
/-- Per dart: the contribution to `[enters v] - [leaves v]`. -/
private lemma dart_contrib (v : V) (d : E × Bool) :
    (if G.tgt d.1 = v then dartSign d.2 else 0) - (if G.src d.1 = v then dartSign d.2 else 0) =
      (if G.dartHead d = v then 1 else 0) - (if G.dartTail d = v then 1 else 0) := by
  rcases d with ⟨e, _ | _⟩
  · simp [dartSign]
  · simp only [dartSign, dartHead_mk_true, dartTail_mk_true, ↓reduceIte]
    split_ifs <;> norm_num

/-- **`χ_Q` is a circulation** (`G.IsFlow Q.chi`): at every vertex the sum over the edges that leave it equals
the sum over the edges that enter it. -/
theorem DirCycle.isFlow_chi {G : MGraph V E} (Q : G.DirCycle) : G.IsFlow Q.chi := by
  intro v
  rw [sum_chi_filter, sum_chi_filter]
  have hperm : (Q.darts.map (fun d => (if G.dartHead d = v then (1 : ℤ) else 0))).sum =
      (Q.darts.map (fun d => (if G.dartTail d = v then (1 : ℤ) else 0))).sum := by
    have := (Q.heads_perm_tails.map (fun x => (if x = v then (1 : ℤ) else 0))).sum_eq
    simpa [List.map_map, Function.comp_def] using this
  have key : (Q.darts.map (fun d => if G.tgt d.1 = v then dartSign d.2 else 0)).sum -
      (Q.darts.map (fun d => if G.src d.1 = v then dartSign d.2 else 0)).sum = 0 := by
    rw [← list_sum_map_sub]
    simp_rw [dart_contrib G v]
    rw [list_sum_map_sub, hperm, sub_self]
  linarith

end MGraph

end EulerFlow
