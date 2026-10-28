/-
HibiLi/Proofs/Steps46.lean — the intermediate claims of the proof of Lemma 4.6 (v2.10 l. 797-837).
Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Proofs.Lemma46

namespace HibiLi.Proofs.Steps46

open Finset Filter Topology Metric Lemma46

section Concrete

open Classical

variable {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P)

/-- A form `Σ_{p∈K∖{c}} u_p` (`c ∈ {a, b}`, `c ∈ K`, `K` a chain of `L`) is a linear form of `ζ`. -/
lemma form_of_zeta {K : Finset x.toSwitch.P'} (hK : K ∈ x.toSwitch.lowBranches) {pc : x.toSwitch.P'}
    (hpc : pc = x.pa ∨ pc = x.pb) (hcK : pc ∈ K) :
    ∃ μ : ({p // p ∉ x.special} → ℝ) →ₗ[ℝ] ℝ, ∀ u, μ (x.zeta u) = x.toSwitch.chainSum (K.erase pc) u := by
  refine ⟨∑ p ∈ (K.erase pc).attach,
    LinearMap.proj (R := ℝ) (φ := fun _ : {p // p ∉ x.special} => ℝ) ⟨p.1, form_not_special x hK hpc hcK p.2⟩,
    fun u => ?_⟩
  rw [LinearMap.sum_apply]
  unfold Switch.chainSum
  rw [← Finset.sum_attach (K.erase pc) (fun p => u p)]
  exact Finset.sum_congr rfl fun p _ => rfl

/-- The point of `Lemma46.exists_local`, re-run with one more output: near `w`, within `E`, `λ_a` and `λ_b` are the
single forms of `K_a` and `K_b` (the proof is that of `Lemma46.exists_local`, which keeps these facts internal). -/
lemma exists_local_forms {E : Set (x.toSwitch.P' → ℝ)} (hE : IsFace x.toSwitch.B E) (hE0 : x.E0 ⊆ E) :
    ∃ (w : x.toSwitch.P' → ℝ) (ρ r : ℝ) (Ka Kb : Finset x.toSwitch.P'), w ∈ affineSpan ℝ E ∧ 0 < ρ ∧
      (∀ y ∈ affineSpan ℝ E, dist y w < ρ → y ∈ E) ∧ 0 < r ∧
      Ka ∈ x.toSwitch.lowBranches ∧ x.pa ∈ Ka ∧ Kb ∈ x.toSwitch.lowBranches ∧ x.pb ∈ Kb ∧
      (∀ u ∈ E ∩ ball w r, x.lamA u = x.toSwitch.chainSum (Ka.erase x.pa) u ∧
        x.lamB u = x.toSwitch.chainSum (Kb.erase x.pb) u) ∧
      x.toSwitch.chainSum Ka w = x.toSwitch.chainSum Kb w ∧ w x.pg = w x.ph := by
  have hEc : Convex ℝ E := hE.2.convex (B_convex x)
  have hu0E : x.u0 ∈ E := hE0 (Lemma45.mem_E0 x (fun p => by simp) (fun _ _ => rfl))
  obtain ⟨hea, heb, heg, heh⟩ := singles_mem x hE0
  have hε := Lemma45.eps_pos x
  obtain ⟨δ₁, hδ₁, hcont⟩ :=
    Metric.continuousAt_iff.mp ((shift_continuous x).continuousAt (x := x.u0)) (Lemma45.eps x / 2) (half_pos hε)
  simp only [shift_u0, add_zero] at hcont
  obtain ⟨δ, hδ, hδ₁', hδε⟩ : ∃ δ, 0 < δ ∧ δ ≤ δ₁ ∧ δ ≤ Lemma45.eps x / 2 :=
    ⟨min δ₁ (Lemma45.eps x / 2), lt_min hδ₁ (half_pos hε), min_le_left _ _, min_le_right _ _⟩
  obtain ⟨z₀, hz₀, hz₀d⟩ := exists_relint_near hEc hu0E hδ
  obtain ⟨z, ⟨hzI, hzd⟩, hgen⟩ :=
    exists_generic x {z | z ∈ intrinsicInterior ℝ E ∧ dist z x.u0 < δ} ⟨z₀, hz₀, hz₀d⟩
  obtain ⟨hzA, εz, hεz, hrelz⟩ := mem_intrinsicInterior_iff.mp hzI
  obtain ⟨rz, hrz, hgen'⟩ := Metric.eventually_nhds_iff.mp hgen
  obtain ⟨Ka, hKa, haK, hfa⟩ := (familyA x).attain z
  obtain ⟨Kb, hKb, hbK, hfb⟩ := (familyB x).attain z
  obtain ⟨r₁, hr₁, hr₁z, hr₁ε, hr₁δ⟩ : ∃ r₁, 0 < r₁ ∧ r₁ ≤ rz ∧ r₁ ≤ εz / 2 ∧ r₁ ≤ δ - dist z x.u0 :=
    ⟨min rz (min (εz / 2) (δ - dist z x.u0)), lt_min hrz (lt_min (half_pos hεz) (by linarith)),
      min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hloc : ∀ u ∈ E, dist u z < r₁ → x.lamA u = x.toSwitch.chainSum (Ka.erase x.pa) u ∧
      x.lamB u = x.toSwitch.chainSum (Kb.erase x.pb) u := by
    intro u huE hu
    have huI : u ∈ intrinsicInterior ℝ E := by
      refine mem_intrinsicInterior_iff.mpr
        ⟨subset_affineSpan ℝ E huE, εz / 2, half_pos hεz, fun y hy hyd => hrelz y hy ?_⟩
      linarith [dist_triangle y u z]
    have huδ : dist u x.u0 < δ := by linarith [dist_triangle u z x.u0]
    obtain ⟨hA, hB⟩ := hgen' (lt_of_lt_of_le hu hr₁z) ⟨huI, huδ⟩
    have hKaM : Ka ∈ maxSet x x.lamA x.pa u := by rw [hA]; exact (mem_maxSet x).mpr ⟨hKa, haK, hfa⟩
    have hKbM : Kb ∈ maxSet x x.lamB x.pb u := by rw [hB]; exact (mem_maxSet x).mpr ⟨hKb, hbK, hfb⟩
    exact ⟨((mem_maxSet x).mp hKaM).2.2.symm, ((mem_maxSet x).mp hKbM).2.2.symm⟩
  obtain ⟨d, hd⟩ : ∃ d, d = shift x z := ⟨_, rfl⟩
  have hdS : ∀ p, p ∉ x.special → d p = 0 := fun p hp => by rw [hd]; exact shift_special x z hp
  have hdV : d ∈ vectorSpan ℝ E := by rw [hd]; exact shift_mem x hea heb heg heh z
  have hwd : dist (z + d) x.u0 < Lemma45.eps x / 2 := by rw [hd]; exact hcont (lt_of_lt_of_le hzd hδ₁')
  have hdist : ∀ y, dist (y - d) z = dist y (z + d) := fun y => by
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    abel
  have hzeta : ∀ y, x.zeta (y - d) = x.zeta y := fun y => funext fun q => by
    simp [XSwitch.zeta, hdS q.1 q.2]
  have hclose : ∀ y, dist y (z + d) < Lemma45.eps x / 2 → Lemma45.Close x y ∧ Lemma45.Close x (y - d) :=
    fun y hy => ⟨close_of_dist x (by linarith [dist_triangle y (z + d) x.u0]),
      close_of_dist x (by linarith [dist_triangle (y - d) z x.u0, hdist y])⟩
  have hsub : ∀ y ∈ affineSpan ℝ E, y - d ∈ affineSpan ℝ E := fun y hy => by
    rw [sub_eq_add_neg, add_comm]
    exact AffineSubspace.vadd_mem_of_mem_direction (by rw [direction_affineSpan]; exact neg_mem hdV) hy
  refine ⟨z + d, min εz (Lemma45.eps x / 2), min r₁ (Lemma45.eps x / 2), Ka, Kb, ?_, lt_min hεz (half_pos hε),
    ?_, lt_min hr₁ (half_pos hε), hKa, haK, hKb, hbK, ?_, ?_⟩
  · rw [add_comm]
    exact AffineSubspace.vadd_mem_of_mem_direction (by rwa [direction_affineSpan]) hzA
  · intro y hy hyd
    have hc := hclose y (lt_of_lt_of_le hyd (min_le_right _ _))
    exact Lemma45.face_transfer x hE hE0 hc.2 hc.1 (hzeta y)
      (hrelz _ (hsub y hy) (by rw [hdist]; exact lt_of_lt_of_le hyd (min_le_left _ _)))
  · intro u hu
    obtain ⟨hcu, hcud⟩ := hclose u (lt_of_lt_of_le (mem_ball.mp hu.2) (min_le_right _ _))
    have hudE : u - d ∈ E := Lemma45.face_transfer x hE hE0 hcu hcud (hzeta u).symm hu.1
    obtain ⟨hla, hlb⟩ := hloc (u - d) hudE
      (by rw [hdist]; exact lt_of_lt_of_le (mem_ball.mp hu.2) (min_le_left _ _))
    constructor
    · have h1 := (familyA x).add (u - d) d hdS
      have h2 := form_add x hKa (Or.inl rfl) haK (u := u - d) hdS
      rw [sub_add_cancel] at h1 h2
      rw [h1, hla, h2]
    · have h1 := (familyB x).add (u - d) d hdS
      have h2 := form_add x hKb (Or.inr rfl) hbK (u := u - d) hdS
      rw [sub_add_cancel] at h1 h2
      rw [h1, hlb, h2]
  · rw [hd]
    exact tie x hKa haK hfa hKb hbK hfb

end Concrete

end HibiLi.Proofs.Steps46

namespace HibiLi.Proofs

open Finset Filter Topology Metric Steps46 Lemma46

open Classical in
/-- **Proof of Lemma 4.6, the intermediate claims** (v2.10 l. 797-837): for every face `E ⊇ E₀` of `B` there is a point
`w ∈ relint E` where the two terms of the max are equal and so are the two terms of the min (l. 807-809), `E` contains
a segment through `w` in the `α`- and in the `γ`-direction (l. 815-816, 834-835), and near `w` within `E`, `λ_a` and
`λ_b` are linear forms `μ_a, μ_b` of `ζ` (l. 803-806). -/
theorem lemma_4_6_point_proved {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P)
    (E : Set (x.toSwitch.P' → ℝ)) (hE : IsFace x.toSwitch.B E) (hE0 : x.E0 ⊆ E) :
    ∃ w ∈ intrinsicInterior ℝ E,
      w x.pa + x.lamA w = w x.pb + x.lamB w ∧ w x.pg = w x.ph ∧
      (∃ ε > 0, ∀ t : ℝ, |t| < ε → w + t • Pi.single x.pa 1 ∈ E ∧ w + t • Pi.single x.pg 1 ∈ E) ∧
      ∃ μa μb : ({p // p ∉ x.special} → ℝ) →ₗ[ℝ] ℝ,
        ∀ᶠ u in 𝓝[E] w, x.lamA u = μa (x.zeta u) ∧ x.lamB u = μb (x.zeta u) := by
  obtain ⟨w, ρ, r, Ka, Kb, hwA, hρ, hrel, hr, hKa, haK, hKb, hbK, hforms, htL, htU⟩ :=
    exists_local_forms x hE hE0
  have hwE : w ∈ E := hrel w hwA (by rw [dist_self]; exact hρ)
  have hwI : w ∈ intrinsicInterior ℝ E := mem_intrinsicInterior_iff.mpr ⟨hwA, ρ, hρ, hrel⟩
  obtain ⟨hla, hlb⟩ := hforms w ⟨hwE, mem_ball_self hr⟩
  obtain ⟨hea, -, heg, -⟩ := singles_mem x hE0
  have hseg : ∀ {v}, v ∈ vectorSpan ℝ E → ‖v‖ = 1 → ∀ t : ℝ, |t| < ρ → w + t • v ∈ E := by
    intro v hv hv1 t ht
    refine hrel _ ?_ ?_
    · rw [add_comm]
      exact AffineSubspace.vadd_mem_of_mem_direction
        (by rw [direction_affineSpan]; exact Submodule.smul_mem _ t hv) hwA
    · rw [dist_self_add_left, norm_smul, hv1, mul_one, Real.norm_eq_abs]
      exact ht
  have hnorm1 : ∀ {p : x.toSwitch.P'}, ‖(Pi.single p (1 : ℝ) : x.toSwitch.P' → ℝ)‖ = 1 := fun {p} => by
    rw [Pi.norm_single, norm_one]
  obtain ⟨μa, hμa⟩ := form_of_zeta x hKa (Or.inl rfl) haK
  obtain ⟨μb, hμb⟩ := form_of_zeta x hKb (Or.inr rfl) hbK
  refine ⟨w, hwI, ?_, htU, ⟨ρ, hρ, fun t ht => ⟨hseg hea hnorm1 t ht, hseg heg hnorm1 t ht⟩⟩,
    μa, μb, Filter.eventually_of_mem (inter_mem_nhdsWithin E (ball_mem_nhds w hr)) fun u hu => ?_⟩
  · rw [hla, hlb]
    unfold Switch.chainSum at htL ⊢
    rw [← Finset.add_sum_erase Ka (fun p => w p) haK, ← Finset.add_sum_erase Kb (fun p => w p) hbK] at htL
    exact htL
  · rw [(hforms u hu).1, (hforms u hu).2, hμa, hμb]
    exact ⟨rfl, rfl⟩

end HibiLi.Proofs
