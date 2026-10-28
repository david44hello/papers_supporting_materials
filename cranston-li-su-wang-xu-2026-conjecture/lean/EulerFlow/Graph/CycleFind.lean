/-
EulerFlow/Graph/CycleFind.lean — paper 002 foundation: a directed cycle from a non-backtracking successor
function on darts. Every "contains a cycle" argument of the paper (Lemma 3.3, Prop 4.4, Prop 6.3, Lemma 8.2,
Prop 9.6, and the decomposition of circulations) goes through `exists_dirCycle_of_succ`.
-/
import EulerFlow.Defs.Graph

namespace EulerFlow

namespace MGraph

variable {V E : Type} (G : MGraph V E)

/-- The reverse of a dart: the same edge, passed in the other direction. -/
def dartRev (d : E × Bool) : E × Bool := (d.1, !d.2)

@[simp] lemma dartTail_mk_false (e : E) : G.dartTail (e, false) = G.src e := by
  simp [dartTail, endVertex]
@[simp] lemma dartTail_mk_true (e : E) : G.dartTail (e, true) = G.tgt e := by
  simp [dartTail, endVertex]
@[simp] lemma dartHead_mk_false (e : E) : G.dartHead (e, false) = G.tgt e := by
  simp [dartHead, endVertex]
@[simp] lemma dartHead_mk_true (e : E) : G.dartHead (e, true) = G.src e := by
  simp [dartHead, endVertex]

@[simp] lemma dartTail_dartRev (d : E × Bool) : G.dartTail (dartRev d) = G.dartHead d := by
  rcases d with ⟨e, _ | _⟩ <;> simp [dartRev]

@[simp] lemma dartHead_dartRev (d : E × Bool) : G.dartHead (dartRev d) = G.dartTail d := by
  rcases d with ⟨e, _ | _⟩ <;> simp [dartRev]

/-- Two different darts on the same edge are reverses of each other. -/
lemma eq_dartRev_of_fst_eq {d d' : E × Bool} (h1 : d.1 = d'.1) (hne : d ≠ d') : d' = dartRev d := by
  rcases d with ⟨e, b⟩
  rcases d' with ⟨e', b'⟩
  simp only at h1
  subst h1
  cases b <;> cases b' <;> simp_all [dartRev]

/-- A list `[g 0, g 1, ..., g (n-1)]` is a chain for `R` when consecutive values are related. -/
lemma isChain_range_map {α : Type*} (R : α → α → Prop) (g : ℕ → α) (hg : ∀ k, R (g k) (g (k + 1)))
    (n : ℕ) : ((List.range n).map g).IsChain R := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine List.IsChain.append ih (by simp) ?_
    intro x hx y hy
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    rcases n with _ | n
    · simp at hx
    · rw [List.range_succ, List.map_append, List.map_singleton, List.getLast?_append] at hx
      simp at hx
      subst hx
      exact hg n

variable [Finite E]

/-- **Cycle finder.** Iterate a successor function `s` on darts satisfying `P`; if `s d` always leaves the head
of `d` and never goes straight back along the edge of `d`, the iteration closes a directed cycle all of whose
darts satisfy `P`. -/
theorem exists_dirCycle_of_succ (P : E × Bool → Prop) (s : E × Bool → E × Bool)
    (hP : ∀ d, P d → P (s d)) (hhead : ∀ d, P d → G.dartHead d = G.dartTail (s d))
    (hrev : ∀ d, P d → s d ≠ dartRev d) (d0 : E × Bool) (h0 : P d0) :
    ∃ Q : G.DirCycle, ∀ d ∈ Q.darts, P d := by
  classical
  set seq : ℕ → E × Bool := fun n => s^[n] d0 with hseq
  have seq_succ : ∀ n, seq (n + 1) = s (seq n) := fun n => Function.iterate_succ_apply' s n d0
  have seqP : ∀ n, P (seq n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => rw [seq_succ]; exact hP _ ih
  set vt : ℕ → V := fun n => G.dartTail (seq n) with hvt
  have head_seq : ∀ n, G.dartHead (seq n) = vt (n + 1) := by
    intro n; simp only [hvt, seq_succ]; exact hhead _ (seqP n)
  -- a repeated tail vertex exists
  have hex : ∃ j, ∃ i < j, vt i = vt j := by
    obtain ⟨x, y, hxy, hs⟩ := Finite.exists_ne_map_eq_of_infinite seq
    have hv : vt x = vt y := by simp only [hvt, hs]
    rcases lt_or_gt_of_ne hxy with h | h
    · exact ⟨y, x, h, hv⟩
    · exact ⟨x, y, h, hv.symm⟩
  set J := Nat.find hex with hJ
  obtain ⟨i, hiJ, hvi⟩ := Nat.find_spec hex
  have hmin : ∀ j < J, ∀ i' < j, vt i' ≠ vt j := by
    intro j hj i' hi' heq
    exact Nat.find_min hex hj ⟨i', hi', heq⟩
  -- tails are injective below J
  have vt_inj : ∀ a b, a < J → b < J → vt a = vt b → a = b := by
    intro a b ha hb hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (hmin b hb a h)
    · exact h
    · exact absurd hab.symm (hmin a ha b h)
  set L := J - i with hL
  have hLpos : 0 < L := by omega
  set g : ℕ → E × Bool := fun k => seq (i + k) with hg
  set ds : List (E × Bool) := (List.range L).map g with hds
  have hds_ne : ds ≠ [] := by
    simp only [hds, ne_eq, List.map_eq_nil_iff, List.range_eq_nil]; omega
  refine ⟨⟨ds, hds_ne, ?chain, ?closes, ?edges, ?tails⟩, ?_⟩
  case chain =>
    refine isChain_range_map _ g (fun k => ?_) L
    simp only [hg, head_seq, hvt, ← add_assoc]
  case closes =>
    have hlast : ds.getLast hds_ne = seq (J - 1) := by
      simp only [hds, List.getLast_map, List.getLast_range, hg]
      congr 1; omega
    have hhd : ds.head hds_ne = seq i := by
      simp only [hds, List.head_map, List.head_range, hg, add_zero]
    rw [hlast, hhd, head_seq]
    have : J - 1 + 1 = J := by omega
    rw [this]; exact hvi.symm
  case tails =>
    rw [hds, List.map_map]
    refine List.Nodup.map_on (fun a ha b hb hab => ?_) List.nodup_range
    simp only [List.mem_range] at ha hb
    have := vt_inj (i + a) (i + b) (by omega) (by omega) hab
    omega
  case edges =>
    rw [hds, List.map_map]
    refine List.Nodup.map_on (fun a ha b hb hab => ?_) List.nodup_range
    simp only [List.mem_range, Function.comp_apply] at ha hb hab
    by_contra hne
    -- WLOG a < b
    have key : ∀ a b, a < b → b < L → (g a).1 = (g b).1 → False := by
      intro a b hab' hbL hfst
      have hgne : g a ≠ g b := by
        intro heq
        have := vt_inj (i + a) (i + b) (by omega) (by omega) (by simp only [hvt, hg] at heq ⊢; rw [heq])
        omega
      have hrevd : g b = dartRev (g a) := eq_dartRev_of_fst_eq hfst hgne
      have htail : vt (i + b) = vt (i + a + 1) := by
        simp only [hvt]
        rw [show seq (i + b) = g b from rfl, hrevd, dartTail_dartRev]
        exact head_seq (i + a)
      have hb1 : b = a + 1 := by
        have := vt_inj (i + b) (i + a + 1) (by omega) (by omega) htail
        omega
      subst hb1
      have hs : g (a + 1) = s (g a) := by simp only [hg, ← add_assoc, seq_succ]
      exact hrev _ (seqP (i + a)) (hs ▸ hrevd)
    rcases lt_or_gt_of_ne hne with h | h
    · exact key a b h hb hab
    · exact key b a h ha hab.symm
  · intro d hd
    simp only [hds, List.mem_map, List.mem_range] at hd
    obtain ⟨k, _, rfl⟩ := hd
    exact seqP _

end MGraph

end EulerFlow
