/-
Smale/Proofs/JN31Blaschke.lean — finite Blaschke products from a factorization: if `B = H ∏ B_a` on the disk with `H`
holomorphic and nonvanishing, `|B| < 1` and `|B| → 1` at the circle, then `H` is a unimodular constant. And `q ∘ φ` factors
this way when `φ` is univalent and `q` is a polynomial.
-/
import Smale.Proofs.JNBase

namespace Smale

open Polynomial Complex Metric Filter Topology Set
open scoped ComplexConjugate

/-- A holomorphic function on the disk, bounded by `1/t` near the circle for every `t < 1`, is bounded by `1`. -/
theorem norm_le_one_of_collar {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g disk)
    (h : ∀ t : ℝ, 0 < t → t < 1 → ∃ r, r < 1 ∧ ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ < 1 → ‖g z‖ ≤ 1 / t) {z : ℂ} (hz : z ∈ disk) :
    ‖g z‖ ≤ 1 := by
  by_contra hgt
  have hgt' : 1 < ‖g z‖ := not_le.1 hgt
  have hpos : 0 < ‖g z‖ := by linarith
  have hinv : ‖g z‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hgt'
  obtain ⟨t, htl, htu⟩ := exists_between hinv
  have ht0 : 0 < t := lt_trans (inv_pos.2 hpos) htl
  obtain ⟨r, hr1, hr⟩ := h t ht0 htu
  have hz1 : ‖z‖ < 1 := by simpa using hz
  set s : ℝ := (max r ‖z‖ + 1) / 2 with hsdef
  have hmax : max r ‖z‖ < 1 := max_lt hr1 hz1
  have hs1 : s < 1 := by rw [hsdef]; linarith
  have hsr : r ≤ s := by have := le_max_left r ‖z‖; rw [hsdef]; linarith
  have hsz : ‖z‖ < s := by have := le_max_right r ‖z‖; rw [hsdef]; linarith
  have hs0 : 0 < s := lt_of_le_of_lt (norm_nonneg z) hsz
  have hd : DiffContOnCl ℂ g (ball (0 : ℂ) s) := hg.diffContOnCl_ball (closedBall_subset_ball hs1)
  have hbound := Complex.norm_le_of_forall_mem_frontier_norm_le (C := 1 / t) (isBounded_ball (x := (0 : ℂ)) (r := s)) hd
    (fun w hw => by
      rw [frontier_ball _ hs0.ne', mem_sphere_zero_iff_norm] at hw
      exact hr w (hw ▸ hsr) (hw ▸ hs1))
    (subset_closure (by simpa using hsz) : z ∈ closure (ball (0 : ℂ) s))
  have hlt : 1 / t < ‖g z‖ := by
    rw [one_div]
    exact (inv_lt_comm₀ ht0 hpos).2 htl
  linarith

/-- A Blaschke factor has norm at most `1` on the disk. -/
theorem blaschkeFactor_norm_le_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : ‖blaschkeFactor a z‖ ≤ 1 := by
  have hden : (1 : ℂ) - conj a * z ≠ 0 :=
    one_sub_mul_ne_zero (by simpa using ha) (by simpa using hz.le)
  have hdenpos : 0 < ‖(1 : ℂ) - conj a * z‖ := norm_pos_iff.2 hden
  rw [blaschkeFactor, norm_div, div_le_one hdenpos]
  have hsq : ‖z - a‖ ^ 2 ≤ ‖(1 : ℂ) - conj a * z‖ ^ 2 := by
    have h := normSq_one_sub_conj_mul a z
    have hp := mul_nonneg (sub_nonneg.2 (pow_le_one₀ (norm_nonneg a) ha.le : ‖a‖ ^ 2 ≤ 1))
      (sub_nonneg.2 (pow_le_one₀ (norm_nonneg z) hz.le : ‖z‖ ^ 2 ≤ 1))
    rw [norm_sub_rev z a]
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- The norm of a Blaschke product on the disk is at most `1`. -/
theorem blaschke_list_norm_le_one (as : List ℂ) (has : ∀ a ∈ as, a ∈ disk) {z : ℂ} (hz : z ∈ disk) :
    ‖(as.map fun a => blaschkeFactor a z).prod‖ ≤ 1 := by
  induction as with
  | nil => simp
  | cons a as ih =>
    have ha : a ∈ disk := has a List.mem_cons_self
    have h1 := ih fun b hb => has b (List.mem_cons_of_mem a hb)
    rw [List.map_cons, List.prod_cons, norm_mul]
    have h2 : ‖blaschkeFactor a z‖ ≤ 1 := blaschkeFactor_norm_le_one (by simpa using ha) (by simpa using hz)
    calc ‖blaschkeFactor a z‖ * ‖(as.map fun a => blaschkeFactor a z).prod‖ ≤ 1 * 1 :=
          mul_le_mul h2 h1 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- **A nonvanishing factor squeezed to modulus one is a unimodular constant.** -/
theorem isFiniteBlaschke_of_factor {B H : ℂ → ℂ} {as : List ℂ} (has : ∀ a ∈ as, a ∈ disk)
    (hH : DifferentiableOn ℂ H disk) (hH0 : ∀ z ∈ disk, H z ≠ 0)
    (hEq : ∀ z ∈ disk, B z = H z * (as.map fun a => blaschkeFactor a z).prod) (hlt : ∀ z ∈ disk, ‖B z‖ < 1)
    (hcollar : ∀ t < (1 : ℝ), ∃ r, 0 ≤ r ∧ r < 1 ∧ ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ < 1 → t < ‖B z‖) :
    IsFiniteBlaschke B as.length := by
  have hup : ∀ z ∈ disk, ‖H z‖ ≤ 1 := fun z hz => by
    refine norm_le_one_of_collar hH (fun t ht0 ht1 => ?_) hz
    obtain ⟨r, -, hr1, hr⟩ := blaschke_list_collar as has ht1
    refine ⟨r, hr1, fun w hwr hw1 => ?_⟩
    have hwd : w ∈ disk := by simpa using hw1
    have h1 := hr w hwr hw1
    have h2 := hlt w hwd
    rw [hEq w hwd, norm_mul] at h2
    rw [le_div_iff₀ ht0]
    nlinarith [norm_nonneg (H w)]
  have hlow : ∀ z ∈ disk, ‖(H z)⁻¹‖ ≤ 1 := fun z hz => by
    refine norm_le_one_of_collar (g := fun w => (H w)⁻¹) (hH.inv hH0) (fun t ht0 ht1 => ?_) hz
    obtain ⟨r, -, hr1, hr⟩ := hcollar t ht1
    refine ⟨r, hr1, fun w hwr hw1 => ?_⟩
    have hwd : w ∈ disk := by simpa using hw1
    have h1 := hr w hwr hw1
    rw [hEq w hwd, norm_mul] at h1
    have h2 := blaschke_list_norm_le_one as has hwd
    have h3 : t < ‖H w‖ := by nlinarith [norm_nonneg (H w)]
    rw [norm_inv, one_div]
    exact inv_anti₀ ht0 h3.le
  have hone : ∀ z ∈ disk, ‖H z‖ = 1 := fun z hz => by
    refine le_antisymm (hup z hz) ?_
    have h1 := hlow z hz
    have hpos : 0 < ‖H z‖ := norm_pos_iff.2 (hH0 z hz)
    rw [norm_inv, inv_le_one₀ hpos] at h1
    exact h1
  have h0d : (0 : ℂ) ∈ disk := by simp
  have hmax : IsMaxOn (norm ∘ H) disk 0 := isMaxOn_iff.2 fun z hz => by
    simp only [Function.comp_apply, hone z hz, hone 0 h0d, le_refl]
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball (0 : ℂ) 1).isPreconnected isOpen_ball hH
    h0d hmax
  refine ⟨H 0, as, hone 0 h0d, rfl, has, fun z hz => ?_⟩
  rw [hEq z hz, blaschkeProd, hconst hz]
  rfl

/-- Divide out the zeros: a product of `φ - ρ` over a multiset of `ρ` factors through Blaschke factors. -/
theorem exists_factor_multiset {φ : ℂ → ℂ} (hφ : IsUnivalentOn φ disk) (m : Multiset ℂ) :
    ∃ (as : List ℂ) (H : ℂ → ℂ), as.length ≤ Multiset.card m ∧ (∀ a ∈ as, a ∈ disk) ∧ DifferentiableOn ℂ H disk ∧
      (∀ z ∈ disk, H z ≠ 0) ∧
      ∀ z ∈ disk, (m.map fun ρ => φ z - ρ).prod = H z * (as.map fun a => blaschkeFactor a z).prod := by
  induction m using Multiset.induction_on with
  | empty =>
    exact ⟨[], fun _ => 1, by simp, by simp, differentiableOn_const _, by simp, by simp⟩
  | cons ρ m ih =>
    obtain ⟨as, H, hlen, has, hd, h0, heq⟩ := ih
    by_cases hρ : ∃ a ∈ disk, φ a = ρ
    · obtain ⟨a, ha, rfl⟩ := hρ
      have ha1 : ‖a‖ < 1 := by simpa using ha
      have hden : ∀ z ∈ disk, (1 : ℂ) - conj a * z ≠ 0 := fun z hz =>
        one_sub_mul_ne_zero (by simpa using ha1) (by simpa using (le_of_lt (by simpa using hz) : ‖z‖ ≤ 1))
      have hds : DifferentiableOn ℂ (dslope φ a) disk :=
        (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds ha)).2 hφ.1
      refine ⟨a :: as, fun z => H z * (((1 : ℂ) - conj a * z) * dslope φ a z), ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_cons, Multiset.card_cons]
        omega
      · intro b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · exact ha
        · exact has b hb
      · exact hd.mul (((differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id)).mul hds)
      · intro z hz
        exact mul_ne_zero (h0 z hz) (mul_ne_zero (hden z hz) (univalent_dslope_ne_zero hφ ha hz))
      · intro z hz
        have hsl : φ z - φ a = (z - a) * dslope φ a z := by
          have h := sub_smul_dslope φ a z
          rw [smul_eq_mul] at h
          exact h.symm
        have hfac : z - a = (z - a) / ((1 : ℂ) - conj a * z) * ((1 : ℂ) - conj a * z) :=
          (div_mul_cancel₀ _ (hden z hz)).symm
        show ((φ a ::ₘ m).map fun ρ => φ z - ρ).prod =
          H z * (((1 : ℂ) - conj a * z) * dslope φ a z) * ((a :: as).map fun a => blaschkeFactor a z).prod
        rw [Multiset.map_cons, Multiset.prod_cons, heq z hz, List.map_cons, List.prod_cons, hsl, blaschkeFactor]
        generalize (z - a) / ((1 : ℂ) - conj a * z) = b at hfac ⊢
        rw [hfac]
        ring
    · have hne : ∀ z ∈ disk, φ z - ρ ≠ 0 := fun z hz h => hρ ⟨z, hz, sub_eq_zero.1 h⟩
      refine ⟨as, fun z => H z * (φ z - ρ), ?_, has, ?_, ?_, ?_⟩
      · simp only [Multiset.card_cons]
        omega
      · exact hd.mul (hφ.1.sub (differentiableOn_const _))
      · exact fun z hz => mul_ne_zero (h0 z hz) (hne z hz)
      · intro z hz
        rw [Multiset.map_cons, Multiset.prod_cons, heq z hz]
        ring

/-- **Divide out the zeros of `q ∘ φ`.** -/
theorem exists_factor_of_univalent {φ : ℂ → ℂ} (hφ : IsUnivalentOn φ disk) {q : ℂ[X]} (hq : q ≠ 0) :
    ∃ (as : List ℂ) (H : ℂ → ℂ), as.length ≤ q.natDegree ∧ (∀ a ∈ as, a ∈ disk) ∧ DifferentiableOn ℂ H disk ∧
      (∀ z ∈ disk, H z ≠ 0) ∧ ∀ z ∈ disk, q.eval (φ z) = H z * (as.map fun a => blaschkeFactor a z).prod := by
  obtain ⟨as, H, hlen, has, hd, h0, heq⟩ := exists_factor_multiset hφ q.roots
  have hlead : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hq
  refine ⟨as, fun z => q.leadingCoeff * H z, hlen.trans q.card_roots', has, hd.const_mul _,
    fun z hz => mul_ne_zero hlead (h0 z hz), fun z hz => ?_⟩
  rw [(IsAlgClosed.splits q).eval_eq_prod_roots, heq z hz]
  ring

end Smale
