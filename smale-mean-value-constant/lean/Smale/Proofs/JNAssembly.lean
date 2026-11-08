/-
Smale/Proofs/JNAssembly.lean — [JN, Prop. 4.2], the first sentence, proved: for an admissible pair `(W, B)` and
`0 < A < 1/B(0)` there is a polynomial of `𝓟` with `m(p) > A`. The route avoids the Riemann map, Runge's theorem in
general, Hilbert's lemniscate theorem and the Jordan curve theorem; see the modules imported here.
-/
import Smale.Proofs.JNBase
import Smale.Proofs.JNCrit
import Smale.Proofs.JNFekete

namespace Smale

open Polynomial Complex Metric Filter Topology

/-! ### Assembly -/

/-- The numbers of the proof: radii and levels below `1/B(0)`. -/
theorem jn_levels {A b₀ : ℝ} (hb₀ : 0 < b₀) (hA : A < 1 / b₀) :
    ∃ A' t : ℝ, A < A' ∧ A' * b₀ < t ∧ t < 1 := by
  have h1 : A * b₀ < 1 := by rwa [lt_div_iff₀ hb₀] at hA
  refine ⟨(A + 1 / b₀) / 2, ((A + 1 / b₀) / 2 * b₀ + 1) / 2, by linarith, ?_, ?_⟩
  · have h2 : (A + 1 / b₀) / 2 * b₀ < 1 := by
      have h3 : (A + 1 / b₀) / 2 * b₀ = (A * b₀ + 1) / 2 := by field_simp
      rw [h3]; linarith
    linarith
  · have h3 : (A + 1 / b₀) / 2 * b₀ = (A * b₀ + 1) / 2 := by field_simp
    rw [h3]; linarith

/-- `W` is continuous on the disk, and on closed subdisks. -/
theorem univalent_continuousOn_closedBall {W : ℂ → ℂ} (hW : IsUnivalentOn W disk) {r : ℝ} (hr : r < 1) :
    ContinuousOn W (closedBall (0 : ℂ) r) :=
  hW.1.continuousOn.mono (closedBall_subset_ball hr)

/-- `|W|` is bounded below on a closed band away from `0`. -/
theorem univalent_norm_lower {W : ℂ → ℂ} (hW : IsUnivalentOn W disk) (hW0 : W 0 = 0) {r₁ r₃ : ℝ} (hr₁ : 0 < r₁)
    (hr₃ : r₃ < 1) : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₃ → c₀ ≤ ‖W z‖ := by
  have hcomp : IsCompact (closedBall (0 : ℂ) r₃ \ ball (0 : ℂ) r₁) := (isCompact_closedBall _ _).diff isOpen_ball
  have hcont : ContinuousOn (fun z => ‖W z‖) (closedBall (0 : ℂ) r₃ \ ball (0 : ℂ) r₁) :=
    ((univalent_continuousOn_closedBall hW hr₃).mono Set.sdiff_subset).norm
  have hpos : ∀ z ∈ closedBall (0 : ℂ) r₃ \ ball (0 : ℂ) r₁, (0 : ℝ) < ‖W z‖ := by
    intro z hz
    have hz3 : ‖z‖ ≤ r₃ := by simpa using hz.1
    have hz1 : r₁ ≤ ‖z‖ := by simpa using hz.2
    have hzd : z ∈ disk := by simpa using hz3.trans_lt hr₃
    refine norm_pos_iff.2 fun h0 => ?_
    have hz0 : z = 0 := hW.2 hzd (mem_ball_self one_pos) (h0.trans hW0.symm)
    rw [hz0, norm_zero] at hz1
    linarith
  obtain ⟨c₀, hc₀, hlow⟩ := hcomp.exists_forall_le' hcont hpos
  refine ⟨c₀, hc₀, fun z h1 h3 => hlow z ⟨by simpa using h3, by simpa using h1⟩⟩

/-- `G = W B / b₀` has the properties the base polynomial asks for. -/
theorem jn_G_props {W B : ℂ → ℂ} {b₀ : ℝ} (hW : InClassS W) (hBd : DifferentiableOn ℂ B disk)
    (hb₀ : 0 < b₀) (hB0 : B 0 = b₀) (hWB : ∀ w ∈ disk, deriv (fun z => W z * B z) w ≠ 0) :
    DifferentiableOn ℂ (fun z => W z * B z / b₀) disk ∧ (fun z => W z * B z / b₀) 0 = 0 ∧
      deriv (fun z => W z * B z / b₀) 0 = 1 ∧ ∀ z ∈ disk, deriv (fun z => W z * B z / b₀) z ≠ 0 := by
  have hb₀c : (b₀ : ℂ) ≠ 0 := by exact_mod_cast hb₀.ne'
  have hd : ∀ z, deriv (fun z => W z * B z / b₀) z = deriv (fun z => W z * B z) z / b₀ := fun z => deriv_div_const _
  have h0mem : (0 : ℂ) ∈ disk := mem_ball_self one_pos
  have hWat : DifferentiableAt ℂ W 0 := hW.1.1.differentiableAt (isOpen_ball.mem_nhds h0mem)
  have hBat : DifferentiableAt ℂ B 0 := hBd.differentiableAt (isOpen_ball.mem_nhds h0mem)
  refine ⟨(hW.1.1.mul hBd).div_const _, by simp [hW.2.1], ?_, fun z hz => ?_⟩
  · rw [hd]
    have h1 : deriv (fun z => W z * B z) 0 = deriv W 0 * B 0 + W 0 * deriv B 0 := deriv_fun_mul hWat hBat
    rw [h1, hW.2.1, hW.2.2, hB0]
    field_simp
    simp
  · rw [hd]
    exact div_ne_zero (hWB z hz) hb₀c

/-- On the band `r₁ ≤ |z| ≤ r₃`, `|P(Wz)/Wz| > A'`, from closeness to `G`. -/
theorem jn_ratio_of_close {W B : ℂ → ℂ} {P : ℂ[X]} {z : ℂ} {b₀ t A' c₀ : ℝ} (hb₀ : 0 < b₀)
    (hc₀ : 0 < c₀) (hWz : c₀ ≤ ‖W z‖) (hBz : t < ‖B z‖)
    (hclose : ‖P.eval (W z) - W z * B z / b₀‖ < (t / b₀ - A') * c₀) (hgap : A' < t / b₀) :
    A' < ‖P.eval (W z)‖ / ‖W z‖ := by
  have hWpos : 0 < ‖W z‖ := lt_of_lt_of_le hc₀ hWz
  rw [lt_div_iff₀ hWpos]
  have hG : ‖W z * B z / b₀‖ = ‖W z‖ * (‖B z‖ / b₀) := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb₀.le, mul_div_assoc]
  have htri : ‖W z * B z / b₀‖ - ‖P.eval (W z) - W z * B z / b₀‖ ≤ ‖P.eval (W z)‖ := by
    have h := norm_sub_norm_le (W z * B z / b₀) (W z * B z / b₀ - P.eval (W z))
    rw [sub_sub_cancel, norm_sub_rev] at h
    exact h
  have hBb : t / b₀ < ‖B z‖ / b₀ := div_lt_div_of_pos_right hBz hb₀
  have hgap' : 0 < t / b₀ - A' := by linarith
  have h1 : (t / b₀ - A') * c₀ ≤ (t / b₀ - A') * ‖W z‖ := mul_le_mul_of_nonneg_left hWz hgap'.le
  have h2 : ‖W z‖ * (t / b₀) < ‖W z‖ * (‖B z‖ / b₀) := mul_lt_mul_of_pos_left hBb hWpos
  nlinarith

/-- **[JN, Prop. 4.2]** (A. Jatar and T. W. Ng, arXiv:2610.21472v2, an unrefereed preprint; the paper's Theorem 2.2, tex
l.183-185), verbatim:
"For every admissible pair $(W,B)$ and every positive real number $A < \frac{1}{B(0)}$, there is a polynomial
$P \in \mathcal{P}$ such that $S(P) > A$. Consequently $$\Bee \leq \M, \ \Bee_{d} \leq \M \quad (d \geq 0) $$"
Lean form: the first sentence only (the "Consequently" is derived: `thm_2_2_hence`); `P ∈ 𝒫` is `∃ d ≥ 2, IsPd d p`.
The route is not the one in [JN]; see the headers of the modules imported here. -/
theorem jatarNg_prop_4_2_proved (W B : ℂ → ℂ) (k : ℕ) (hWB : IsAdmissible W B k) (A : ℝ) (hA0 : 0 < A)
    (hA : A < 1 / (B 0).re) :
    ∃ d : ℕ, 2 ≤ d ∧ ∃ p : ℂ[X], IsPd d p ∧ A < mval p := by
  obtain ⟨hW, hBl, ⟨hBim, hBre⟩, hWB'⟩ := hWB
  set b₀ : ℝ := (B 0).re with hb₀def
  have hB0 : B 0 = (b₀ : ℂ) := Complex.ext (by simp [hb₀def]) (by simp [hBim])
  have hBd := blaschke_differentiableOn hBl
  obtain ⟨A', t, hAA', hA't, ht1⟩ := jn_levels hBre hA
  have hgap : A' < t / b₀ := by rwa [lt_div_iff₀ hBre]
  -- radii
  obtain ⟨r₀, -, hr₀1, hcollar₀⟩ := blaschke_collar hBl ht1
  set r₁ : ℝ := max r₀ (1 / 2) with hr₁def
  have hr₁pos : 0 < r₁ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have h0r₁ : 0 ≤ r₁ := hr₁pos.le
  have hr₁1 : r₁ < 1 := max_lt hr₀1 (by norm_num)
  have hcollar : ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ < 1 → t < ‖B z‖ :=
    fun z h1 h2 => hcollar₀ z ((le_max_left _ _).trans h1) h2
  obtain ⟨r₂, hr₁₂, hr₂1⟩ := exists_between hr₁1
  obtain ⟨r₃, hr₂₃, hr₃1⟩ := exists_between hr₂1
  have h0r₂ : 0 ≤ r₂ := h0r₁.trans hr₁₂.le
  have h0r₃ : 0 ≤ r₃ := h0r₂.trans hr₂₃.le
  have hUniv := hW.1
  -- the band away from `0`: a lower bound for `|W|`
  obtain ⟨c₀, hc₀, hWlow⟩ := univalent_norm_lower hUniv hW.2.1 hr₁pos hr₃1
  have hεpos : 0 < (t / b₀ - A') * c₀ := mul_pos (by linarith) hc₀
  obtain ⟨hGd, hG0, hG1, hG'⟩ := jn_G_props hW hBd hBre hB0 hWB'
  obtain ⟨P, hP0, hP1, ⟨μ, hμ, hPμ⟩, hPclose⟩ :=
    base_polynomial hW hGd hG0 hG1 hG' h0r₃ hr₃1 hεpos
  -- the separating polynomial
  set E : Set ℂ := W '' closedBall (0 : ℂ) r₂ with hEdef
  set F : Set ℂ := (W '' ball (0 : ℂ) r₃)ᶜ with hFdef
  have hball3 : ball (0 : ℂ) r₃ ⊆ disk := ball_subset_ball hr₃1.le
  have hEcomp : IsCompact E := (isCompact_closedBall _ _).image_of_continuousOn
    (univalent_continuousOn_closedBall hUniv hr₂1)
  have hEinf : E.Infinite :=
    (infinite_of_mem_nhds (0 : ℂ) (closedBall_mem_nhds _ (hr₁pos.trans hr₁₂))).image
      (hUniv.2.mono (closedBall_subset_ball hr₂1))
  have hEconn : IsPreconnected Eᶜ := compl_image_closedBall_isPreconnected hUniv h0r₂ hr₂1
  have hFclosed : IsClosed F := (univalent_isOpen_image hUniv hball3 isOpen_ball).isClosed_compl
  have hEF : Disjoint E F := by
    refine Set.disjoint_left.2 fun w hwE hwF => hwF ?_
    obtain ⟨z, hz, rfl⟩ := hwE
    exact ⟨z, closedBall_subset_ball hr₂₃ hz, rfl⟩
  obtain ⟨Q, a, c, hQdeg, ha, hac, hQE, hQF⟩ := fekete_separation hEcomp hEinf hEconn hFclosed hEF
  obtain ⟨s, r, hr, has, hsc, hcrit⟩ := level_choice hQdeg ha hac
  have hs : 0 < s := by linarith
  have hrs : r < s := by linarith
  have hsne : (s : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hs.ne')
  set q : ℂ[X] := C (s : ℂ)⁻¹ * Q with hqdef
  have hqeval : ∀ b, ‖q.eval b‖ = ‖Q.eval b‖ / s := by
    intro b
    rw [hqdef, eval_mul, eval_C, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs.le]
    field_simp
  have hqdegree : 1 ≤ q.natDegree := by rwa [hqdef, natDegree_C_mul hsne]
  have hρ0 : 0 < r / s := div_pos hr hs
  have hρ1 : r / s < 1 := (div_lt_one hs).2 hrs
  have hlow : ∀ b, ‖q.eval b‖ < 1 - r / s ↔ ‖Q.eval b‖ < s - r := by
    intro b
    rw [hqeval, div_lt_iff₀ hs]
    have : (1 - r / s) * s = s - r := by field_simp
    rw [this]
  have hhigh : ∀ b, ‖q.eval b‖ ≤ 1 + r / s ↔ ‖Q.eval b‖ ≤ s + r := by
    intro b
    rw [hqeval, div_le_iff₀ hs]
    have : (1 + r / s) * s = s + r := by field_simp
    rw [this]
  have h0E : (0 : ℂ) ∈ E := ⟨0, mem_closedBall_self h0r₂, hW.2.1⟩
  have hq0 : ‖q.eval 0‖ < 1 - r / s := (hlow 0).2 (lt_of_le_of_lt (hQE 0 h0E) has)
  -- `|q| ≤ 1 + ρ` keeps a point inside `W(D_{r₃})`
  have hinside : ∀ b, ‖q.eval b‖ ≤ 1 + r / s → b ∈ W '' ball (0 : ℂ) r₃ := by
    intro b hb
    by_contra hbF
    have h1 := hQF b hbF
    have h2 := (hhigh b).1 hb
    linarith
  refine perturb_crit (P := P) (q := q) (K := W '' closedBall (0 : ℂ) r₃) (A' := A') (ρ := r / s) (μ := μ) hP0 hP1
    hqdegree hA0 hAA' hρ0 hρ1 hq0 ((isCompact_closedBall _ _).image_of_continuousOn
      (univalent_continuousOn_closedBall hUniv hr₃1))
    hμ (fun b hb => ?_) ?_ ?_
  · obtain ⟨z, hz, rfl⟩ := hinside b hb
    exact ⟨z, ball_subset_closedBall hz, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hPμ z hz
  · intro b hb1 hb2
    have hband1 : s - r ≤ ‖Q.eval b‖ := not_lt.1 fun h => absurd ((hlow b).2 h) (not_lt.2 hb1)
    have hband2 : ‖Q.eval b‖ ≤ s + r := (hhigh b).1 hb2
    have hQ' : Q.derivative.eval b ≠ 0 := fun h => hcrit b h ⟨hband1, hband2⟩
    have hnotE : b ∉ E := fun hbE => by
      have := hQE b hbE
      linarith
    obtain ⟨z, hz, rfl⟩ := hinside b hb2
    have hzr₃ : ‖z‖ < r₃ := by simpa using hz
    have hzr₂ : r₂ < ‖z‖ := by
      by_contra hle
      exact hnotE ⟨z, by simpa using not_lt.1 hle, rfl⟩
    have hzr₁ : r₁ < ‖z‖ := hr₁₂.trans hzr₂
    have hz1 : ‖z‖ < 1 := hzr₃.trans hr₃1
    refine ⟨?_, ?_, ?_⟩
    · rw [hqdef, derivative_C_mul, eval_mul, eval_C]
      exact mul_ne_zero hsne hQ'
    · exact fun h => hnotE (h ▸ h0E)
    · exact jn_ratio_of_close hBre hc₀ (hWlow z hzr₁.le hzr₃.le) (hcollar z hzr₁.le hz1)
        (hPclose z (by simpa using hzr₃.le)) hgap

end Smale
