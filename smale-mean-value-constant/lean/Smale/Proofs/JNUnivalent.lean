/-
Smale/Proofs/JNUnivalent.lean — univalent maps on the unit disk: the image of an open set is open, the derivative
never vanishes, and the complement of the image of a closed subdisk is connected.
-/
import Smale.Defs.Basic

namespace Smale

open Complex Metric Filter Topology Set

/-- A univalent map on the disk is analytic there. -/
theorem univalent_analyticOnNhd {W : ℂ → ℂ} (hW : IsUnivalentOn W disk) : AnalyticOnNhd ℂ W disk :=
  hW.1.analyticOnNhd isOpen_ball

/-- A univalent map on the disk is not constant there. -/
theorem univalent_not_constant {W : ℂ → ℂ} (hW : IsUnivalentOn W disk) : ¬∃ w, ∀ z ∈ disk, W z = w := by
  rintro ⟨w, hw⟩
  have h0 : (0 : ℂ) ∈ disk := mem_ball_self one_pos
  have h1 : ((1 / 2 : ℝ) : ℂ) ∈ disk := by
    rw [mem_ball_zero_iff, Complex.norm_real]
    norm_num
  have h2 := hW.2 h0 h1 ((hw 0 h0).trans (hw _ h1).symm)
  have h3 : (0 : ℝ) = 1 / 2 := by exact_mod_cast h2
  norm_num at h3

/-- Open mapping for a univalent map on the disk. -/
theorem univalent_isOpen_image {W : ℂ → ℂ} (hW : IsUnivalentOn W disk) {s : Set ℂ} (hs : s ⊆ disk) (ho : IsOpen s) :
    IsOpen (W '' s) :=
  ((univalent_analyticOnNhd hW).is_constant_or_isOpen (convex_ball _ _).isPreconnected).resolve_left
    (univalent_not_constant hW) s hs ho

/-- The left inverse of `W` on `W(s)` is continuous at every point of `W(s)`, `s` open in the disk. -/
theorem univalent_invFunOn_continuousAt {W : ℂ → ℂ} (hW : IsUnivalentOn W disk) {s : Set ℂ} (hs : s ⊆ disk)
    (ho : IsOpen s) {z : ℂ} (hz : z ∈ s) : ContinuousAt (Function.invFunOn W s) (W z) := by
  have hinj : InjOn W s := hW.2.mono hs
  have hinv : ∀ x ∈ s, Function.invFunOn W s (W x) = x := fun x hx => hinj.leftInvOn_invFunOn hx
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hsub : s ∩ ball z ε ⊆ disk := inter_subset_left.trans hs
  have hopen := univalent_isOpen_image hW hsub (ho.inter isOpen_ball)
  have hmem : W z ∈ W '' (s ∩ ball z ε) := ⟨z, ⟨hz, mem_ball_self hε⟩, rfl⟩
  filter_upwards [hopen.mem_nhds hmem]
  rintro _ ⟨x, ⟨hxs, hxb⟩, rfl⟩
  rw [hinv x hxs, hinv z hz]
  exact hxb

/-- A nonconstant analytic function has a punctured neighbourhood free of zeros of its derivative. -/
theorem univalent_deriv_ne_zero_punctured {W : ℂ → ℂ} (hW : IsUnivalentOn W disk) {z₀ : ℂ} (hz₀ : z₀ ∈ disk) :
    ∀ᶠ z in 𝓝[≠] z₀, deriv W z ≠ 0 := by
  have hA := univalent_analyticOnNhd hW z₀ hz₀
  rcases hA.deriv.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h.and (isOpen_ball.mem_nhds hz₀))
    have hconst : ∀ x ∈ ball z₀ δ, W x = W z₀ := by
      have hdiff : DifferentiableOn ℂ W (ball z₀ δ) := hW.1.mono fun x hx => (hball x hx).2
      intro x hx
      exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z₀ δ).isPreconnected hdiff
        (fun y hy => (hball y hy).1) hx (mem_ball_self hδ)
    obtain ⟨x, hx, hxne⟩ : ∃ x ∈ ball z₀ δ, x ≠ z₀ := by
      refine ⟨z₀ + (δ / 2 : ℝ), ?_, ?_⟩
      · rw [mem_ball_iff_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        linarith
      · intro h1
        have h2 : ((δ / 2 : ℝ) : ℂ) = 0 := by simpa using h1
        have h3 : δ / 2 = 0 := by exact_mod_cast h2
        linarith
    exact hxne (hW.2 (hball x hx).2 hz₀ (hconst x hx))
  · exact h

/-- **A univalent map has no critical point.** The left inverse is continuous, and differentiable off one point;
the removable singularity theorem then makes it differentiable at that point too, and the chain rule ends the proof. -/
theorem univalent_deriv_ne_zero {W : ℂ → ℂ} (hW : IsUnivalentOn W disk) {z₀ : ℂ} (hz₀ : z₀ ∈ disk) :
    deriv W z₀ ≠ 0 := by
  intro hzero
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1
    (eventually_nhdsWithin_iff.1 (univalent_deriv_ne_zero_punctured hW hz₀) |>.and (isOpen_ball.mem_nhds hz₀))
  set s : Set ℂ := ball z₀ δ with hsdef
  have hsd : s ⊆ disk := fun x hx => (hball x hx).2
  have hinj : InjOn W s := hW.2.mono hsd
  set V : ℂ → ℂ := Function.invFunOn W s with hVdef
  have hVW : ∀ x ∈ s, V (W x) = x := fun x hx => hinj.leftInvOn_invFunOn hx
  have hopen : IsOpen (W '' s) := univalent_isOpen_image hW hsd isOpen_ball
  have hz₀s : z₀ ∈ s := mem_ball_self hδ
  have hmem : W z₀ ∈ W '' s := ⟨z₀, hz₀s, rfl⟩
  have hdiffV : DifferentiableOn ℂ V (W '' s \ {W z₀}) := by
    rintro _ ⟨⟨x, hxs, rfl⟩, hne⟩
    have hxne : x ≠ z₀ := fun h => hne (by rw [h]; rfl)
    have hd : deriv W x ≠ 0 := (hball x hxs).1 hxne
    have hcont : ContinuousAt V (W x) := univalent_invFunOn_continuousAt hW hsd isOpen_ball hxs
    have hder : HasDerivAt W (deriv W x) (V (W x)) := by
      rw [hVW x hxs]
      exact (hW.1.differentiableAt (isOpen_ball.mem_nhds (hsd hxs))).hasDerivAt
    have hev : ∀ᶠ y in 𝓝 (W x), W (V y) = y := by
      filter_upwards [hopen.mem_nhds ⟨x, hxs, rfl⟩]
      rintro _ ⟨u, hu, rfl⟩
      rw [hVW u hu]
    exact (hder.of_local_left_inverse hcont hd hev).differentiableAt.differentiableWithinAt
  have hcontV : ContinuousAt V (W z₀) := univalent_invFunOn_continuousAt hW hsd isOpen_ball hz₀s
  have hVdiff : DifferentiableOn ℂ V (W '' s) :=
    (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (hopen.mem_nhds hmem)).1 ⟨hdiffV, hcontV⟩
  have hVat : DifferentiableAt ℂ V (W z₀) := hVdiff.differentiableAt (hopen.mem_nhds hmem)
  have hWat : HasDerivAt W (deriv W z₀) z₀ :=
    (hW.1.differentiableAt (isOpen_ball.mem_nhds hz₀)).hasDerivAt
  have hcomp : HasDerivAt (V ∘ W) (deriv V (W z₀) * deriv W z₀) z₀ := hVat.hasDerivAt.comp z₀ hWat
  have hid : V ∘ W =ᶠ[𝓝 z₀] id := by
    filter_upwards [isOpen_ball.mem_nhds hz₀s] with x hx
    exact hVW x hx
  have h1 : HasDerivAt (V ∘ W) (1 : ℂ) z₀ := (hasDerivAt_id z₀).congr_of_eventuallyEq hid
  have h2 := hcomp.unique h1
  rw [hzero, mul_zero] at h2
  exact zero_ne_one h2

/-- The open annulus `r < |z| < r'` is connected. -/
theorem annulus_isPreconnected {r r' : ℝ} (h0 : 0 ≤ r) :
    IsPreconnected {z : ℂ | r < ‖z‖ ∧ ‖z‖ < r'} := by
  have hmap : {z : ℂ | r < ‖z‖ ∧ ‖z‖ < r'} =
      (fun p : ℝ × ℝ => ((p.1 : ℂ) * Complex.exp (p.2 * I))) '' (Ioo r r' ×ˢ univ) := by
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(‖z‖, arg z), ⟨⟨h1, h2⟩, mem_univ _⟩, norm_mul_exp_arg_mul_I z⟩
    · rintro ⟨⟨t, u⟩, ⟨⟨h1, h2⟩, -⟩, rfl⟩
      have ht : 0 < t := lt_of_le_of_lt h0 h1
      have hn : ‖((t : ℂ) * Complex.exp (u * I))‖ = t := by
        rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_of_nonneg ht.le]
      exact ⟨hn.symm ▸ h1, hn.symm ▸ h2⟩
  rw [hmap]
  refine ((isPreconnected_Ioo).prod isPreconnected_univ).image _ ?_
  fun_prop

/-- The compact image of a closed subdisk. -/
theorem univalent_isCompact_image {W : ℂ → ℂ} (hW : IsUnivalentOn W disk) {r : ℝ} (hr : r < 1) :
    IsCompact (W '' closedBall (0 : ℂ) r) :=
  (isCompact_closedBall _ _).image_of_continuousOn (hW.1.continuousOn.mono (closedBall_subset_ball hr))

/-- A connected component of the complement of `K = W(closed disk r)` meets the image of a thin annulus. -/
theorem component_meets_image_annulus {W : ℂ → ℂ} (hW : IsUnivalentOn W disk) {r r' : ℝ} (h0 : 0 ≤ r) (hr' : r' < 1)
    (hrr' : r < r') {y : ℂ} (hy : y ∈ (W '' closedBall (0 : ℂ) r)ᶜ) :
    (connectedComponentIn (W '' closedBall (0 : ℂ) r)ᶜ y ∩ (W '' {z : ℂ | r < ‖z‖ ∧ ‖z‖ < r'})).Nonempty := by
  set K : Set ℂ := W '' closedBall (0 : ℂ) r with hKdef
  have hK : IsCompact K := univalent_isCompact_image hW (hrr'.trans hr')
  have hU : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  set C : Set ℂ := connectedComponentIn Kᶜ y with hCdef
  have hCopen : IsOpen C := hU.connectedComponentIn
  have hCsub : C ⊆ Kᶜ := connectedComponentIn_subset _ _
  have hCne : C ≠ univ := fun h => by
    have h1 : W 0 ∈ K := ⟨0, mem_closedBall_self h0, rfl⟩
    exact hCsub (h ▸ mem_univ (W 0)) h1
  obtain ⟨p, hp⟩ := nonempty_frontier_iff.2 ⟨⟨y, mem_connectedComponentIn hy⟩, hCne⟩
  have hpcl : p ∈ closure C := frontier_subset_closure hp
  have hpC : p ∉ C := by
    rw [frontier, hCopen.interior_eq] at hp
    exact hp.2
  have hpK : p ∈ K := by
    by_contra hpK
    have hCp : IsOpen (connectedComponentIn Kᶜ p) := hU.connectedComponentIn
    obtain ⟨c, hcp, hcC⟩ := mem_closure_iff.1 hpcl _ hCp (mem_connectedComponentIn hpK)
    have h1 := connectedComponentIn_eq hcp
    have h2 : C = connectedComponentIn Kᶜ c := connectedComponentIn_eq hcC
    exact hpC (h2 ▸ h1 ▸ mem_connectedComponentIn hpK)
  have hsub : ball (0 : ℂ) r' ⊆ disk := ball_subset_ball hr'.le
  have hopen : IsOpen (W '' ball (0 : ℂ) r') := univalent_isOpen_image hW hsub isOpen_ball
  have hpV : p ∈ W '' ball (0 : ℂ) r' := by
    obtain ⟨z, hz, rfl⟩ := hpK
    exact ⟨z, closedBall_subset_ball hrr' hz, rfl⟩
  obtain ⟨c, ⟨z, hz, rfl⟩, hcC⟩ := mem_closure_iff.1 hpcl _ hopen hpV
  refine ⟨W z, hcC, z, ⟨?_, by simpa using hz⟩, rfl⟩
  by_contra hle
  exact hCsub hcC ⟨z, by simpa using not_lt.1 hle, rfl⟩

/-- **The complement of `W(closed disk r)` is connected** (`W` univalent on the disk, `0 ≤ r < 1`). -/
theorem compl_image_closedBall_isPreconnected {W : ℂ → ℂ} (hW : IsUnivalentOn W disk) {r : ℝ} (h0 : 0 ≤ r)
    (hr : r < 1) : IsPreconnected (W '' closedBall (0 : ℂ) r)ᶜ := by
  obtain ⟨r', hrr', hr'⟩ := exists_between hr
  set A : Set ℂ := W '' {z : ℂ | r < ‖z‖ ∧ ‖z‖ < r'} with hAdef
  have hsubd : {z : ℂ | r < ‖z‖ ∧ ‖z‖ < r'} ⊆ disk := fun z hz => by
    simpa using hz.2.trans hr'
  have hApre : IsPreconnected A := (annulus_isPreconnected h0).image _ (hW.1.continuousOn.mono hsubd)
  have hAsub : A ⊆ (W '' closedBall (0 : ℂ) r)ᶜ := by
    rintro _ ⟨z, hz, rfl⟩ ⟨z', hz', hzz'⟩
    have h1 : z' = z := hW.2 (closedBall_subset_ball hr hz') (hsubd hz) hzz'
    have h2 : ‖z‖ ≤ r := by simpa [h1] using hz'
    exact absurd hz.1 (not_lt.2 h2)
  obtain ⟨x₀, hx₀⟩ : A.Nonempty := by
    refine ⟨W ((r + r') / 2 : ℝ), ((r + r') / 2 : ℝ), ?_, rfl⟩
    have hpos : 0 ≤ (r + r') / 2 := by linarith
    show r < ‖(((r + r') / 2 : ℝ) : ℂ)‖ ∧ ‖(((r + r') / 2 : ℝ) : ℂ)‖ < r'
    rw [Complex.norm_real, Real.norm_of_nonneg hpos]
    constructor <;> linarith
  refine isPreconnected_of_forall x₀ fun y hy => ?_
  refine ⟨connectedComponentIn _ y ∪ A, union_subset (connectedComponentIn_subset _ _) hAsub,
    Or.inr hx₀, Or.inl (mem_connectedComponentIn hy), ?_⟩
  exact IsPreconnected.union' (component_meets_image_annulus hW h0 hr' hrr' hy)
    isPreconnected_connectedComponentIn hApre

end Smale
