/-
LeeDiam/Sec6/SigmaMixed.lean — the σ step of the paper's proof of Proposition 6.6 (sec_reverse.tex v1.50 l. 166):
σ maps mixed pairs to mixed pairs, commutes with `u ↦ u^-` and `u ↦ u^+` on targets, carries `Iso(I, J)` and
`J \ I` to the corresponding sets of `(σI, σJ)`, and preserves `d_O`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Sec2.Projections
import LeeDiam.Sec6.SigmaGraph

namespace LeeDiam

open PnSets

/-- A graph isomorphism preserves distances. -/
theorem iso_edist {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (u v : V) :
    H.edist (e u) (e v) = G.edist u v := by
  apply le_antisymm
  · exact graph_edge_map_edist_le e
      (fun a b hab => le_of_eq (SimpleGraph.edist_eq_one_iff_adj.2 (e.map_adj_iff.2 hab))) u v
  · have h := graph_edge_map_edist_le e.symm
      (fun a b hab => le_of_eq (SimpleGraph.edist_eq_one_iff_adj.2 (e.symm.map_adj_iff.2 hab))) (e u) (e v)
    simpa using h

namespace S6

variable {n : ℕ}

theorem orderAut_oVtx (I : Set (Pn n)) (hI : IsIdeal I) (hI' : IsIdeal (sigma n '' I)) :
    orderAut (oVtx I hI) = oVtx (sigma n '' I) hI' := by
  apply Subtype.ext
  rw [orderAut_val, sigmaPerm_apply]
  exact setVector_sigma I

theorem sigma_mem_tgts {x : Pn n} : sigma n x ∈ tgts n ↔ x ∈ tgts n := by
  cases x <;> simp [tgts, tgtA, tgtB, sigma]

theorem sigma_lo (u : Pn n) : sigma n (lo n u) = lo n (sigma n u) := by
  cases u <;> rfl

theorem sigma_up (u : Pn n) : sigma n (up n u) = up n (sigma n u) := by
  cases u <;> rfl

end S6

theorem prop_6_6_sigma_proved (n : ℕ) :
    (∀ I J : Set (Pn n), IsMixed n I J → IsMixed n (sigma n '' I) (sigma n '' J)) ∧
    (∀ u ∈ tgts n, sigma n (lo n u) = lo n (sigma n u) ∧ sigma n (up n u) = up n (sigma n u)) ∧
    (∀ I J : Set (Pn n), isoSet n (sigma n '' I) (sigma n '' J) = sigma n '' isoSet n I J ∧
      sigma n '' J \ sigma n '' I = sigma n '' (J \ I)) ∧
    (∀ (I J : Set (Pn n)) (hI : IsIdeal I) (hJ : IsIdeal J) (hI' : IsIdeal (sigma n '' I))
      (hJ' : IsIdeal (sigma n '' J)), dO (sigma n '' I) (sigma n '' J) hI' hJ' = dO I J hI hJ) := by
  refine ⟨fun I J hIJ => ?_, fun u _ => ⟨S6.sigma_lo u, S6.sigma_up u⟩, fun I J => ⟨?_, ?_⟩,
    fun I J hI hJ hI' hJ' => ?_⟩
  · obtain ⟨hI, hJ, hhI, hhJ⟩ := hIJ
    refine ⟨S6.isIdeal_sigma hI, S6.isIdeal_sigma hJ, ⟨PnElem.h, hhI, rfl⟩, fun hh => hhJ ?_⟩
    exact S6.mem_sigma_image.1 hh
  · ext x
    rw [S6.mem_sigma_image]
    simp only [isoSet, Set.mem_ofPred_eq, S6.mem_sigma_image, S6.sigma_mem_tgts, S6.sigma_lo, S6.sigma_up]
  · exact (Set.image_sdiff S6.sigma_injective J I).symm
  · unfold dO
    rw [← S6.orderAut_oVtx I hI hI', ← S6.orderAut_oVtx J hJ hJ']
    exact iso_edist S6.orderAut _ _

end LeeDiam
