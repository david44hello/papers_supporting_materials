/-
Smale/Proofs/JN31Root.lean — from polynomial approximation to square roots: a locally uniform limit of polynomials on a
connected open set has a primitive, and if every holomorphic function has a primitive then every nonvanishing one has a
holomorphic square root. With a bounded domain, that is all the Riemann mapping theorem needs.
-/
import Smale.Defs.Basic
import Smale.Proofs.DataSec5
import Smale.Vendor.RiemannMap

namespace Smale

open Polynomial Complex Metric Filter Topology Set

/-- Every nonvanishing holomorphic function on `U` has a holomorphic square root. This is what the Riemann mapping theorem
uses of simple connectivity. -/
def IsRootDomain (U : Set ℂ) : Prop :=
  ∀ g : ℂ → ℂ, DifferentiableOn ℂ g U → (∀ z ∈ U, g z ≠ 0) →
    ∃ s : ℂ → ℂ, DifferentiableOn ℂ s U ∧ ∀ z ∈ U, s z ^ 2 = g z

/-- **A locally uniform limit of polynomials on a connected open set has a primitive.** -/
theorem exists_primitive_of_poly_approx {U : Set ℂ} (hUo : IsOpen U) (hUp : IsPreconnected U) {x₀ : ℂ} (hx₀ : x₀ ∈ U)
    {G : ℂ → ℂ} {P : ℕ → ℂ[X]} (hP : TendstoLocallyUniformlyOn (fun n z => (P n).eval z) G atTop U) :
    ∃ L : ℂ → ℂ, ∀ z ∈ U, HasDerivAt L (G z) z := by
  set F : ℕ → ℂ → ℂ := fun n z => (antideriv (P n)).eval z - (antideriv (P n)).eval x₀ with hFdef
  have hder : ∀ n y, HasDerivAt (F n) ((P n).eval y) y := fun n y => by
    have h := (antideriv (P n)).hasDerivAt y
    rw [Exact.derivative_antideriv] at h
    exact h.sub_const _
  -- around each point, uniformly Cauchy derivatives
  have hlocal : ∀ z ∈ U, ∃ r > 0, ball z r ⊆ U ∧
      UniformCauchySeqOn (fun n w => (P n).eval w) atTop (ball z r) := by
    intro z hz
    obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (hUo.mem_nhds hz)
    refine ⟨r, hr, ball_subset_closedBall.trans hrU, ?_⟩
    have h := (tendstoLocallyUniformlyOn_iff_forall_isCompact hUo).1 hP (closedBall z r) hrU (isCompact_closedBall z r)
    exact (h.mono ball_subset_closedBall).uniformCauchySeqOn
  have hprop : ∀ {c : ℂ} {s : ℝ}, UniformCauchySeqOn (fun n w => (P n).eval w) atTop (ball c s) →
      CauchySeq (fun n => F n c) → ∀ w ∈ ball c s, CauchySeq (fun n => F n w) := by
    intro c s hu hc w hw
    have h := uniformCauchySeqOn_ball_of_deriv (f := F) (f' := fun n w => (P n).eval w) hu
      (fun n y _ => hder n y) hc
    exact h.cauchySeq hw
  -- the clopen argument
  set A : Set ℂ := {z | z ∈ U ∧ CauchySeq fun n => F n z} with hAdef
  have hAo : IsOpen A := by
    refine Metric.isOpen_iff.2 fun z hz => ?_
    obtain ⟨r, hr, hrU, hu⟩ := hlocal z hz.1
    exact ⟨r, hr, fun w hw => ⟨hrU hw, hprop hu hz.2 w hw⟩⟩
  have hx₀A : x₀ ∈ U ∩ A := by
    refine ⟨hx₀, hx₀, ?_⟩
    have hzero : (fun n => F n x₀) = fun _ => 0 := funext fun n => sub_self _
    rw [hzero]
    exact cauchySeq_const _
  have hcl : closure A ∩ U ⊆ A := by
    rintro z ⟨hzc, hzU⟩
    obtain ⟨r, hr, hrU, hu⟩ := hlocal z hzU
    obtain ⟨y, hyA, hyz⟩ := Metric.mem_closure_iff.1 hzc (r / 2) (by positivity)
    have hsub : ball y (r / 2) ⊆ ball z r := by
      refine ball_subset_ball' ?_
      rw [dist_comm]
      linarith
    refine ⟨hzU, hprop (hu.mono hsub) hyA.2 z ?_⟩
    rw [mem_ball]
    exact hyz
  have hUA : U ⊆ A := hUp.subset_of_closure_inter_subset hAo ⟨x₀, hx₀A⟩ hcl
  have hlim : ∀ x ∈ U, ∃ l, Tendsto (fun n => F n x) atTop (𝓝 l) := fun x hx =>
    cauchySeq_tendsto_of_complete (hUA hx).2
  choose! L hL using hlim
  exact ⟨L, fun z hz => hasDerivAt_of_tendstoLocallyUniformlyOn hUo hP (Eventually.of_forall fun n x _ => hder n x) hL hz⟩

/-- **Primitives give square roots.** -/
theorem isRootDomain_of_primitive {U : Set ℂ} (hUo : IsOpen U) (hUp : IsPreconnected U)
    (h : ∀ G : ℂ → ℂ, DifferentiableOn ℂ G U → ∃ L : ℂ → ℂ, ∀ z ∈ U, HasDerivAt L (G z) z) : IsRootDomain U := by
  intro g hg hg0
  obtain ⟨L, hL⟩ := h (fun z => deriv g z / g z) ((hg.deriv hUo).div hg hg0)
  rcases U.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨fun _ => 0, differentiableOn_empty, fun z hz => absurd hz (notMem_empty z)⟩
  set w : ℂ → ℂ := fun z => g z * Complex.exp (-L z) with hwdef
  have hw : ∀ z ∈ U, HasDerivAt w 0 z := by
    intro z hz
    have hgz : HasDerivAt g (deriv g z) z := (hg.differentiableAt (hUo.mem_nhds hz)).hasDerivAt
    have h1 := hgz.mul (hL z hz).neg.cexp
    have h0 := hg0 z hz
    convert h1 using 1
    field_simp
    ring
  have hwd : DifferentiableOn ℂ w U := fun z hz => (hw z hz).differentiableAt.differentiableWithinAt
  have hconst : ∀ z ∈ U, w z = w x₀ := fun z hz =>
    hUo.is_const_of_deriv_eq_zero hUp hwd (fun y hy => (hw y hy).deriv) hz hx₀
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c ^ 2 = w x₀ := IsAlgClosed.exists_pow_nat_eq _ (by norm_num)
  refine ⟨fun z => c * Complex.exp (L z / 2), fun z hz => ?_, fun z hz => ?_⟩
  · have h1 : HasDerivAt L (deriv g z / g z) z := hL z hz
    exact (((h1.div_const 2).cexp.const_mul c).differentiableAt).differentiableWithinAt
  · have h1 : Complex.exp (L z / 2) ^ 2 = Complex.exp (L z) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [mul_pow, hc, h1, ← hconst z hz, hwdef]
    simp only [mul_assoc]
    rw [← Complex.exp_add]
    simp

/-- A bounded connected open set with square roots has what the proof of the Riemann mapping theorem uses. -/
theorem riemannData_of_isRootDomain {U : Set ℂ} (hUo : IsOpen U) (hUp : IsPreconnected U)
    (hUb : Bornology.IsBounded U) (hUr : IsRootDomain U) {x : ℂ} (hx : x ∈ U) : Complex.RiemannData U x := by
  classical
  obtain ⟨M, hM⟩ := hUb.subset_ball x
  have hM0 : 0 < M := pos_of_mem_ball (hM hx)
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
  have hnorm : ∀ z ∈ U, ‖(z - x) / (M : ℂ)‖ < 1 := fun z hz => by
    have h1 := hM hz
    rw [mem_ball_iff_norm] at h1
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hM0.le, div_lt_one hM0]
    exact h1
  refine ⟨hUp, ?_, ?_⟩
  · refine ⟨fun z => if hz : z ∈ U then .mk ((z - x) / (M : ℂ)) (hnorm z hz) else 0, ?_, ?_, ?_⟩
    · apply Complex.UnitDisc.coe_injective
      simp [hx]
    · intro a ha b hb hab
      simp only [ha, hb, ↓reduceDIte, Complex.UnitDisc.mk_inj] at hab
      exact sub_left_inj.1 ((div_left_inj' hMC).1 hab)
    · intro z hz
      have heq : (Complex.UnitDisc.coe ∘ fun z => if hz : z ∈ U then Complex.UnitDisc.mk ((z - x) / (M : ℂ)) (hnorm z hz)
          else 0) =ᶠ[𝓝 z] fun w => (w - x) / (M : ℂ) := by
        filter_upwards [hUo.mem_nhds hz] with w hw
        simp [hw]
      have hd : HasDerivAt (fun w : ℂ => (w - x) / (M : ℂ)) (1 / (M : ℂ)) z :=
        ((hasDerivAt_id' z).sub_const x).div_const _
      rw [heq.deriv_eq, hd.deriv]
      exact div_ne_zero one_ne_zero hMC
  · intro g hg h0
    have hg0 : ∀ z ∈ U, (Complex.UnitDisc.coe ∘ g) z ≠ 0 := fun z hz h => by
      apply h0
      refine ⟨z, hz, ?_⟩
      apply Complex.UnitDisc.coe_injective
      simpa using h
    obtain ⟨s, hsd, hs⟩ := hUr (Complex.UnitDisc.coe ∘ g) hg hg0
    set f₀ : ℂ → ℂ := U.piecewise s fun z => (g z : ℂ) ^ (((2 : ℕ) : ℂ)⁻¹) with hf₀def
    have hf₀2 : ∀ z, f₀ z ^ 2 = g z := fun z => by
      by_cases hz : z ∈ U
      · rw [hf₀def, Set.piecewise_eq_of_mem _ _ _ hz]
        exact hs z hz
      · rw [hf₀def, Set.piecewise_eq_of_notMem _ _ _ hz]
        exact Complex.cpow_nat_inv_pow _ two_ne_zero
    have hf₀1 : ∀ z, ‖f₀ z‖ < 1 := fun z => by
      rw [← pow_lt_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, ← norm_pow, hf₀2]
      exact (g z).norm_lt_one
    have hf₀c : ContinuousOn f₀ U :=
      hsd.continuousOn.congr fun z hz => Set.piecewise_eq_of_mem _ _ _ hz
    refine ⟨fun z => .mk (f₀ z) (hf₀1 z), Complex.UnitDisc.isEmbedding_coe.continuousOn_iff.mpr hf₀c, fun z => ?_⟩
    apply Complex.UnitDisc.coe_injective
    simpa [Complex.UnitDisc.coe_pow] using hf₀2 z

/-- **The Riemann mapping theorem, with simple connectivity replaced by square roots.** -/
theorem exists_bijOn_unitBall_of_isRootDomain {U : Set ℂ} (hUo : IsOpen U) (hUp : IsPreconnected U)
    (hUb : Bornology.IsBounded U) (hUr : IsRootDomain U) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ BijOn f U (ball 0 1) ∧ f x₀ = 0 :=
  Complex.exists_bijOn_unitBall_map_eq_zero_of_riemannData hUo
    (riemannData_of_isRootDomain hUo hUp hUb hUr hx₀) hx₀

end Smale
