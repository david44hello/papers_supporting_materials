/-
Smale/Proofs/JN31Domain.lean — the component of the lemniscate domain `{|q| < R}` that contains `0`: it is open, connected
and bounded, its sublevel sets are compact, and they have connected complement by the maximum modulus principle.
-/
import Smale.Defs.Basic
import Smale.Proofs.JNUnivalent

namespace Smale

open Polynomial Complex Metric Filter Topology Set

/-- The component of the lemniscate domain `{|q| < R}` that contains `0`. -/
def lemComp (q : ℂ[X]) (R : ℝ) : Set ℂ := connectedComponentIn {z | ‖q.eval z‖ < R} 0

theorem lemDomain_isOpen (q : ℂ[X]) (R : ℝ) : IsOpen {z | ‖q.eval z‖ < R} :=
  isOpen_lt q.continuous.norm continuous_const

theorem lemComp_isOpen (q : ℂ[X]) (R : ℝ) : IsOpen (lemComp q R) :=
  (lemDomain_isOpen q R).connectedComponentIn

theorem lemComp_isPreconnected (q : ℂ[X]) (R : ℝ) : IsPreconnected (lemComp q R) :=
  isPreconnected_connectedComponentIn

theorem mem_lemComp_zero {q : ℂ[X]} {R : ℝ} (h0 : ‖q.eval 0‖ < R) : (0 : ℂ) ∈ lemComp q R :=
  mem_connectedComponentIn h0

theorem lemComp_lt {q : ℂ[X]} {R : ℝ} {z : ℂ} (hz : z ∈ lemComp q R) : ‖q.eval z‖ < R :=
  (connectedComponentIn_subset {z | ‖q.eval z‖ < R} 0 hz : z ∈ {z | ‖q.eval z‖ < R})

theorem lemComp_isBounded {q : ℂ[X]} (hq : 0 < q.natDegree) (R : ℝ) : Bornology.IsBounded (lemComp q R) := by
  have hdeg : 0 < q.degree := natDegree_pos_iff_degree_pos.1 hq
  have hlim : Tendsto (fun z => ‖q.eval z‖) (cocompact ℂ) atTop := q.tendsto_norm_atTop hdeg tendsto_norm_cocompact_atTop
  obtain ⟨K, hK, hKsub⟩ := mem_cocompact.1 ((tendsto_atTop.1 hlim) R)
  refine hK.isBounded.subset fun z hz => ?_
  by_contra hzK
  have h1 : R ≤ ‖q.eval z‖ := hKsub hzK
  exact absurd (lemComp_lt hz) (not_lt.2 h1)

/-- A point of the closure of the component where `|q| < R` lies in the component. -/
theorem mem_lemComp_of_mem_closure {q : ℂ[X]} {R : ℝ} {z : ℂ} (hz : z ∈ closure (lemComp q R)) (hlt : ‖q.eval z‖ < R) :
    z ∈ lemComp q R := by
  have hzV : z ∈ {z | ‖q.eval z‖ < R} := hlt
  obtain ⟨c, hcz, hc0⟩ := mem_closure_iff.1 hz _ (lemDomain_isOpen q R).connectedComponentIn (mem_connectedComponentIn hzV)
  have h1 := connectedComponentIn_eq hcz
  have h2 : lemComp q R = connectedComponentIn {z | ‖q.eval z‖ < R} c := connectedComponentIn_eq hc0
  rw [h2, ← h1]
  exact mem_connectedComponentIn hzV

/-- **Sublevel sets of the component are compact.** -/
theorem lemComp_sublevel_isCompact {q : ℂ[X]} (hq : 0 < q.natDegree) {R t : ℝ} (ht : t < R) :
    IsCompact (lemComp q R ∩ {z | ‖q.eval z‖ ≤ t}) := by
  have hcl : IsCompact (closure (lemComp q R)) := (lemComp_isBounded hq R).isCompact_closure
  have hclosed : IsClosed {z | ‖q.eval z‖ ≤ t} := isClosed_le q.continuous.norm continuous_const
  have heq : lemComp q R ∩ {z | ‖q.eval z‖ ≤ t} = closure (lemComp q R) ∩ {z | ‖q.eval z‖ ≤ t} := by
    ext z
    constructor
    · exact fun h => ⟨subset_closure h.1, h.2⟩
    · exact fun h => ⟨mem_lemComp_of_mem_closure h.1 (lt_of_le_of_lt h.2 ht), h.2⟩
  rw [heq]
  exact hcl.inter_right hclosed

/-- The outside of a disk is connected. -/
theorem outer_isPreconnected {M : ℝ} (h0 : 0 ≤ M) : IsPreconnected {z : ℂ | M < ‖z‖} := by
  have hmap : {z : ℂ | M < ‖z‖} = (fun p : ℝ × ℝ => ((p.1 : ℂ) * Complex.exp (p.2 * I))) '' (Ioi M ×ˢ univ) := by
    ext z
    constructor
    · intro h1
      exact ⟨(‖z‖, arg z), ⟨h1, mem_univ _⟩, norm_mul_exp_arg_mul_I z⟩
    · rintro ⟨⟨t, u⟩, ⟨h1, -⟩, rfl⟩
      have ht : 0 < t := lt_of_le_of_lt h0 h1
      show M < ‖((t : ℂ) * Complex.exp (u * I))‖
      rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_of_nonneg ht.le]
      exact h1
  rw [hmap]
  refine ((isPreconnected_Ioi).prod isPreconnected_univ).image _ ?_
  fun_prop

/-- **Sublevel sets of the component have connected complement** (maximum modulus). -/
theorem lemComp_sublevel_compl_isPreconnected {q : ℂ[X]} (hq : 0 < q.natDegree) {R t : ℝ} (ht : t < R) :
    IsPreconnected (lemComp q R ∩ {z | ‖q.eval z‖ ≤ t})ᶜ := by
  set E : Set ℂ := lemComp q R ∩ {z | ‖q.eval z‖ ≤ t} with hEdef
  have hE : IsCompact E := lemComp_sublevel_isCompact hq ht
  obtain ⟨M₀, hM₀⟩ := hE.isBounded.subset_closedBall (0 : ℂ)
  set M : ℝ := max M₀ 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hEM : ∀ z ∈ E, ‖z‖ ≤ M := fun z hz => by
    have h1 := hM₀ hz
    rw [mem_closedBall_zero_iff] at h1
    exact h1.trans (le_max_left _ _)
  set A : Set ℂ := {z : ℂ | M < ‖z‖} with hAdef
  have hApre : IsPreconnected A := outer_isPreconnected hM0
  have hAsub : A ⊆ Eᶜ := fun z hz hzE => absurd (hEM z hzE) (not_le.2 hz)
  have hU : IsOpen Eᶜ := hE.isClosed.isOpen_compl
  -- every component reaches the outside
  have hmeet : ∀ y ∈ Eᶜ, (connectedComponentIn Eᶜ y ∩ A).Nonempty := by
    intro y hy
    by_contra hempty
    set C : Set ℂ := connectedComponentIn Eᶜ y with hCdef
    have hCopen : IsOpen C := hU.connectedComponentIn
    have hCsub : C ⊆ Eᶜ := connectedComponentIn_subset _ _
    have hyC : y ∈ C := mem_connectedComponentIn hy
    have hCball : C ⊆ closedBall (0 : ℂ) M := fun z hz => by
      rw [mem_closedBall_zero_iff]
      by_contra hlt
      exact hempty ⟨z, hz, not_le.1 hlt⟩
    have hCb : Bornology.IsBounded C := isBounded_closedBall.subset hCball
    -- its frontier lies in `E`
    have hfront : ∀ p ∈ frontier C, p ∈ E := by
      intro p hp
      have hpcl : p ∈ closure C := frontier_subset_closure hp
      have hpC : p ∉ C := by
        rw [frontier, hCopen.interior_eq] at hp
        exact hp.2
      by_contra hpE
      have hCp : IsOpen (connectedComponentIn Eᶜ p) := hU.connectedComponentIn
      obtain ⟨c, hcp, hcC⟩ := mem_closure_iff.1 hpcl _ hCp (mem_connectedComponentIn hpE)
      have h1 := connectedComponentIn_eq hcp
      have h2 : C = connectedComponentIn Eᶜ c := connectedComponentIn_eq hcC
      exact hpC (h2 ▸ h1 ▸ mem_connectedComponentIn hpE)
    have hCne : C ≠ univ := fun h => by
      have h1 : ((M + 1 : ℝ) : ℂ) ∈ closedBall (0 : ℂ) M := hCball (h ▸ mem_univ _)
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_of_nonneg (by linarith)] at h1
      linarith
    obtain ⟨p, hp⟩ := nonempty_frontier_iff.2 ⟨⟨y, hyC⟩, hCne⟩
    -- maximum modulus on `C`
    have hmax : ∀ z ∈ closure C, ‖q.eval z‖ ≤ t := fun z hz =>
      Complex.norm_le_of_forall_mem_frontier_norm_le hCb q.differentiable.diffContOnCl
        (fun w hw => (hfront w hw).2) hz
    -- so `closure C` lies in the component
    have hpcl : p ∈ closure C := frontier_subset_closure hp
    have hsub : closure C ⊆ connectedComponentIn {z | ‖q.eval z‖ < R} p :=
      isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn hpcl fun z hz =>
        lt_of_le_of_lt (hmax z hz) ht
    have heq : connectedComponentIn {z | ‖q.eval z‖ < R} p = lemComp q R :=
      (connectedComponentIn_eq (hfront p hp).1).symm
    have hyΩ : y ∈ lemComp q R := heq ▸ hsub (subset_closure hyC)
    exact hy ⟨hyΩ, hmax y (subset_closure hyC)⟩
  have hx₀ : ((M + 1 : ℝ) : ℂ) ∈ A := by
    show M < ‖((M + 1 : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    linarith
  refine isPreconnected_of_forall ((M + 1 : ℝ) : ℂ) fun y hy => ?_
  exact ⟨connectedComponentIn Eᶜ y ∪ A, union_subset (connectedComponentIn_subset _ _) hAsub, Or.inr hx₀,
    Or.inl (mem_connectedComponentIn hy),
    IsPreconnected.union' (hmeet y hy) isPreconnected_connectedComponentIn hApre⟩

end Smale
