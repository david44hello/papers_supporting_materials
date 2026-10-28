/-
HibiLi/Proofs/QEPaper.lean — Lemma 4.5(a) with the paper's own `Q_E` (paper v2.10 lines 752–759): the polyhedron of
the points of the `ζ`-space that satisfy the defining inequalities of `B` tight at `u₀`, those tight on all of `E`
imposed as equations.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.QEPaper
import HibiLi.Proofs.Lemma45Full

namespace HibiLi.Proofs

open Filter Topology Set

namespace QEPaper

/-! ### The inequality system of `B` (any switch) -/

section Ineqs

variable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)

/-- `B` is exactly the set where every inequality of `ineqs` holds: `ineqs` lists the five families of `B`. -/
lemma mem_B_iff_ineqs {u : s.P' → ℝ} : u ∈ s.B ↔ ∀ g ∈ s.ineqs, 0 ≤ g u := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩ g hg
    rcases hg with ⟨p, hp, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, r', hr, hr', hle, rfl⟩ |
      ⟨r, K, hr, hKI, hK, hlt, rfl⟩ | ⟨K, hKI, hK, rfl⟩
    · exact h1 p hp
    · exact (h2 r hr).1
    · exact sub_nonneg.mpr (h2 r hr).2
    · exact sub_nonneg.mpr (h3 r r' hr hr' hle)
    · exact sub_nonneg.mpr (h4 r hr K hKI hK hlt)
    · exact sub_nonneg.mpr (h5 K hKI hK)
  · intro h
    refine ⟨fun p hp => h _ (Or.inl ⟨p, hp, rfl⟩), fun r hr => ⟨h _ (Or.inr (Or.inl ⟨r, hr, rfl⟩)),
      sub_nonneg.mp (h _ (Or.inr (Or.inr (Or.inl ⟨r, hr, rfl⟩))))⟩,
      fun r r' hr hr' hle => sub_nonneg.mp (h _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, r', hr, hr', hle, rfl⟩))))),
      fun r hr K hKI hK hlt => sub_nonneg.mp
        (h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, K, hr, hKI, hK, hlt, rfl⟩)))))),
      fun K hKI hK => sub_nonneg.mp (h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨K, hKI, hK, rfl⟩))))))⟩

/-- Every slack is affine: it respects affine combinations. -/
lemma ineqs_combo {g : (s.P' → ℝ) → ℝ} (hg : g ∈ s.ineqs) (u v : s.P' → ℝ) {a b : ℝ} (hab : a + b = 1) :
    g (a • u + b • v) = a * g u + b * g v := by
  rcases hg with ⟨p, hp, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, r', hr, hr', hle, rfl⟩ |
      ⟨r, K, hr, hKI, hK, hlt, rfl⟩ | ⟨K, hKI, hK, rfl⟩ <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum] <;>
    first | ring1 | linear_combination -hab

lemma ineqs_lineMap {g : (s.P' → ℝ) → ℝ} (hg : g ∈ s.ineqs) (u v : s.P' → ℝ) (t : ℝ) :
    g (AffineMap.lineMap u v t) = (1 - t) * g u + t * g v := by
  rw [AffineMap.lineMap_apply_module]
  exact ineqs_combo s hg u v (by ring)

/-- `B` has finitely many defining inequalities. -/
lemma ineqs_finite : s.ineqs.Finite := by
  classical
  refine (((((Set.finite_range fun p : s.P' => fun u : s.P' → ℝ => u p).union
    (Set.finite_range fun r : s.P' => fun u : s.P' → ℝ => 1 - u r)).union
    (Set.finite_range fun rr : s.P' × s.P' => fun u : s.P' → ℝ => u rr.2 - u rr.1)).union
    (Set.finite_range fun rK : s.P' × Finset s.P' => fun u : s.P' → ℝ => u rK.1 - ∑ p ∈ rK.2, u p)).union
    (Set.finite_range fun K : Finset s.P' => fun u : s.P' → ℝ => 1 - ∑ p ∈ K, u p)).subset ?_
  rintro g (⟨p, -, rfl⟩ | ⟨r, -, rfl⟩ | ⟨r, -, rfl⟩ | ⟨r, r', -, -, -, rfl⟩ | ⟨r, K, -, -, -, -, rfl⟩ |
    ⟨K, -, -, rfl⟩)
  · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨p, rfl⟩)))
  · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨r, rfl⟩)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨r, rfl⟩)))
  · exact Or.inl (Or.inl (Or.inr ⟨(r, r'), rfl⟩))
  · exact Or.inl (Or.inr ⟨(r, K), rfl⟩)
  · exact Or.inr ⟨K, rfl⟩

/-- An inequality of `B` that is not tight on the convex set `E ⊆ B` is strict on `relint E`. -/
lemma ineq_pos_of_intrinsicInterior {E : Set (s.P' → ℝ)} (hEB : E ⊆ s.B) {w e : s.P' → ℝ}
    (hw : w ∈ intrinsicInterior ℝ E) (he : e ∈ E) {g : (s.P' → ℝ) → ℝ} (hg : g ∈ s.ineqs) (hge : g e ≠ 0) :
    0 < g w := by
  have hw0 : 0 ≤ g w := (mem_B_iff_ineqs s).mp (hEB (intrinsicInterior_subset hw)) g hg
  have he0 : 0 < g e := lt_of_le_of_ne ((mem_B_iff_ineqs s).mp (hEB he) g hg) (Ne.symm hge)
  refine lt_of_le_of_ne hw0 fun hw' => ?_
  obtain ⟨t, htE, ht⟩ := ((eventually_lineMap_mem_of_intrinsicInterior hw he).filter_mono nhdsWithin_le_nhds
    |>.and (self_mem_nhdsWithin : ∀ᶠ t in 𝓝[<] (0 : ℝ), t ∈ Iio 0)).exists
  have h := (mem_B_iff_ineqs s).mp (hEB htE) g hg
  rw [ineqs_lineMap s hg, ← hw'] at h
  have ht' : t < 0 := ht
  nlinarith

/-- **A face of `B` is `B` with the inequalities tight on it made equalities**: a point of `B` at which every
inequality tight on the face `E` is an equality lies in `E`. -/
lemma mem_face_of_tight {E : Set (s.P' → ℝ)} (hE : IsFace s.B E) {u : s.P' → ℝ} (hu : u ∈ s.B)
    (htight : ∀ g ∈ s.ineqs, (∀ e ∈ E, g e = 0) → g u = 0) : u ∈ E := by
  have hEB : E ⊆ s.B := hE.subset
  have hEc : Convex ℝ E := hE.2.convex (B_convex_closed s).1
  obtain ⟨w, hw⟩ := Set.Nonempty.intrinsicInterior hEc hE.1
  have hwE : w ∈ E := intrinsicInterior_subset hw
  have hev : ∀ g ∈ s.ineqs, ∀ᶠ t in 𝓝 (0 : ℝ), 0 ≤ g (AffineMap.lineMap w u t) := by
    intro g hg
    by_cases ht : ∀ e ∈ E, g e = 0
    · refine Filter.Eventually.of_forall fun t => ?_
      rw [ineqs_lineMap s hg, ht w hwE, htight g hg ht]
      simp
    · push Not at ht
      obtain ⟨e, he, hge⟩ := ht
      have hpos := ineq_pos_of_intrinsicInterior s hEB hw he hg hge
      have hcont : Continuous fun t : ℝ => (1 - t) * g w + t * g u := by fun_prop
      have hlim := hcont.tendsto 0
      simp only [sub_zero, one_mul, zero_mul, add_zero] at hlim
      filter_upwards [hlim.eventually (lt_mem_nhds hpos)] with t ht
      rw [ineqs_lineMap s hg]
      exact ht.le
  obtain ⟨t, hz, ht⟩ := (((ineqs_finite s).eventually_all.mpr hev).filter_mono nhdsWithin_le_nhds
    |>.and (self_mem_nhdsWithin : ∀ᶠ t in 𝓝[<] (0 : ℝ), t ∈ Iio 0)).exists
  have ht' : t < 0 := ht
  have hzB : AffineMap.lineMap w u t ∈ s.B := (mem_B_iff_ineqs s).mpr hz
  have h1t : (1 - t) ≠ 0 := by linarith
  have hseg : w ∈ openSegment ℝ u (AffineMap.lineMap w u t) := by
    refine ⟨-t / (1 - t), 1 / (1 - t), div_pos (by linarith) (by linarith), div_pos one_pos (by linarith),
      by field_simp; ring, ?_⟩
    have ha : -t / (1 - t) + 1 / (1 - t) * t = 0 := by field_simp; ring
    have hb : 1 / (1 - t) * (1 - t) = 1 := by field_simp
    rw [AffineMap.lineMap_apply_module]
    calc (-t / (1 - t)) • u + (1 / (1 - t)) • ((1 - t) • w + t • u)
        = (-t / (1 - t) + 1 / (1 - t) * t) • u + (1 / (1 - t) * (1 - t)) • w := by module
      _ = w := by rw [ha, hb, zero_smul, one_smul, zero_add]
  exact hE.2.isExtreme.left_mem_of_mem_openSegment hu hzB hwE hseg

end Ineqs

/-! ### The section `ζ ↦ (α, β, γ, η of u₀; ζ)` -/

section XS

open Lemma45 Lemma45Full

variable {P : Type*} [Fintype P] [PartialOrder P] (x : HibiLi.XSwitch P)

lemma zeta_withZeta (ζ : {p // p ∉ x.special} → ℝ) : x.zeta (x.withZeta ζ) = ζ := by
  ext ⟨p, hp⟩
  simp [XSwitch.zeta, XSwitch.withZeta, hp]

lemma alphaPart_withZeta (ζ : {p // p ∉ x.special} → ℝ) : x.alphaPart (x.withZeta ζ) = x.alphaPart x.u0 := by
  ext i
  fin_cases i <;> simp [XSwitch.alphaPart, XSwitch.withZeta, XSwitch.special]

lemma withZeta_zeta {v : x.toSwitch.P' → ℝ} (hva : x.alphaPart v = x.alphaPart x.u0) :
    x.withZeta (x.zeta v) = v := by
  ext p
  by_cases hp : p ∈ x.special
  · simp [XSwitch.withZeta, hp, eq_of_alphaPart x hva hp]
  · simp [XSwitch.withZeta, hp, XSwitch.zeta]

lemma withZeta_combo (ζ₁ ζ₂ : {p // p ∉ x.special} → ℝ) {a b : ℝ} (hab : a + b = 1) :
    x.withZeta (a • ζ₁ + b • ζ₂) = a • x.withZeta ζ₁ + b • x.withZeta ζ₂ := by
  ext p
  by_cases hp : p ∈ x.special
  · simp only [XSwitch.withZeta, hp, dite_true, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← add_mul, hab, one_mul]
  · simp [XSwitch.withZeta, hp]

lemma close_u0 : Close x x.u0 := fun p => by simp [eps_pos x]

lemma close_withZeta {ζ : {p // p ∉ x.special} → ℝ} (hζ : ζ ∈ box (x.zeta x.u0) (eps x)) :
    Close x (x.withZeta ζ) := by
  intro p
  by_cases hp : p ∈ x.special
  · simp [XSwitch.withZeta, hp, eps_pos x]
  · have h := hζ ⟨p, hp⟩ (Set.mem_univ _)
    rw [Metric.mem_ball, Real.dist_eq] at h
    simpa [XSwitch.withZeta, hp, XSwitch.zeta] using h

/-- **The inequalities of `B` tight at `u₀` involve only `ζ`** (paper proof of Lemma 4.5(a), lines 766–773): every
inequality involving `α, β, γ` or `η` is strict at `u₀`. -/
theorem tight_ineq_zeta {g : (x.toSwitch.P' → ℝ) → ℝ} (hg : g ∈ x.toSwitch.ineqs) (h0 : g x.u0 = 0)
    {u v : x.toSwitch.P' → ℝ} (huv : x.zeta u = x.zeta v) : g u = g v := by
  have hc := close_u0 x
  rcases hg with ⟨p, hp, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, r', hr, hr', hle, rfl⟩ |
      ⟨r, K, hr, hKI, hK, hlt, rfl⟩ | ⟨K, hKI, hK, rfl⟩
  · have hs : p ∉ x.special := fun hs => by
      have := (special_bounds hc hs).1
      linarith
    exact (eq_of_zeta x huv hs).symm
  · linarith [J_bound hc hr]
  · have hs : r ∉ x.special := fun hs => by
      have := (special_bounds hc hs).2
      linarith
    simp only [eq_of_zeta x huv hs]
  · by_cases hs' : r' ∈ x.special
    · simp only [eq_of_le_special x hr (special_J x hs' hr') hle, sub_self]
    · have hs : r ∉ x.special := fun hs => by
        have := (special_bounds hc hs).2
        have := J_nonspecial hc hr' hs'
        linarith
      simp only [eq_of_zeta x huv hs, eq_of_zeta x huv hs']
  · linarith [J_bound hc hr, chain_bound hc hKI hK]
  · linarith [chain_bound hc hKI hK]

lemma u0_mem_face {E : Set (x.toSwitch.P' → ℝ)} (hE0 : x.E0 ⊆ E) : x.u0 ∈ E :=
  hE0 (mem_E0 x (fun p => by simp) (fun _ _ => rfl))

lemma zeta_u0_mem_QEpaper (E : Set (x.toSwitch.P' → ℝ)) : x.zeta x.u0 ∈ x.QEpaper E := by
  intro g _ h0
  rw [withZeta_zeta x rfl, h0]
  exact ⟨le_rfl, fun _ => rfl⟩

lemma QEpaper_convex (E : Set (x.toSwitch.P' → ℝ)) : Convex ℝ (x.QEpaper E) := by
  intro ζ₁ h₁ ζ₂ h₂ a b ha hb hab g hg h0
  rw [withZeta_combo x ζ₁ ζ₂ hab, ineqs_combo x.toSwitch hg _ _ hab]
  obtain ⟨n₁, e₁⟩ := h₁ g hg h0
  obtain ⟨n₂, e₂⟩ := h₂ g hg h0
  refine ⟨by positivity, fun ht => ?_⟩
  rw [e₁ ht, e₂ ht, mul_zero, mul_zero, add_zero]

/-- The section `Q_E` of `E` lies in the paper's polyhedron `Q_E` (everywhere, not only near `ζ₀`). -/
theorem QE_subset_QEpaper {E : Set (x.toSwitch.P' → ℝ)} (hEB : E ⊆ x.toSwitch.B) : x.QE E ⊆ x.QEpaper E := by
  rintro _ ⟨v, hvE, hva, rfl⟩ g hg _
  rw [withZeta_zeta x hva]
  exact ⟨(mem_B_iff_ineqs x.toSwitch).mp (hEB hvE) g hg, fun h => h v hvE⟩

/-- Near `ζ₀`, the paper's polyhedron `Q_E` lies in the section of `E`: the inequalities strict at `u₀` stay strict
on the box (as in the proof of Lemma 4.5), so the point lies in `B`, and the equalities put it in the face `E`. -/
theorem QEpaper_subset_QE_near {E : Set (x.toSwitch.P' → ℝ)} (hE : IsFace x.toSwitch.B E) (hE0 : x.E0 ⊆ E)
    {ζ : {p // p ∉ x.special} → ℝ} (hζb : ζ ∈ box (x.zeta x.u0) (eps x)) (hζ : ζ ∈ x.QEpaper E) :
    ζ ∈ x.QE E := by
  set v := x.withZeta ζ with hvdef
  have hv : Close x v := close_withZeta x hζb
  have hQ : ∀ g ∈ x.toSwitch.ineqs, g x.u0 = 0 → 0 ≤ g v := fun g hg h0 => (hζ g hg h0).1
  have hvB : v ∈ x.toSwitch.B := by
    refine ⟨fun p hp => ?_, fun r hr => ⟨?_, ?_⟩, fun r r' hr hr' hle => ?_, fun r hr K hKI hK _ => ?_,
      fun K hKI hK => ?_⟩
    · by_cases hs : p ∈ x.special
      · linarith [(special_bounds hv hs).1]
      · exact hQ _ (Or.inl ⟨p, hp, rfl⟩) (u0_I x hs hp)
    · linarith [J_bound hv hr]
    · by_cases hs : r ∈ x.special
      · linarith [(special_bounds hv hs).2]
      · have h := hQ _ (Or.inr (Or.inr (Or.inl ⟨r, hr, rfl⟩))) (by simp [u0_J x hs hr])
        linarith
    · by_cases hs' : r' ∈ x.special
      · rw [eq_of_le_special x hr (special_J x hs' hr') hle]
      · by_cases hs : r ∈ x.special
        · linarith [(special_bounds hv hs).2, J_nonspecial hv hr' hs']
        · have h := hQ _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, r', hr, hr', hle, rfl⟩))))
            (by simp [u0_J x hs hr, u0_J x hs' hr'])
          linarith
    · linarith [chain_bound hv hKI hK, J_bound hv hr]
    · linarith [chain_bound hv hKI hK]
  have hvE : v ∈ E := mem_face_of_tight x.toSwitch hE hvB fun g hg htE =>
    (hζ g hg (htE _ (u0_mem_face x hE0))).2 htE
  exact ⟨v, hvE, alphaPart_withZeta x ζ, zeta_withZeta x ζ⟩

/-- **The paper's `Q_E` agrees with the section of `E` near `ζ₀`** (inside the box `V_ζ` of Lemma 4.5). -/
theorem QE_iff_QEpaper {E : Set (x.toSwitch.P' → ℝ)} (hE : IsFace x.toSwitch.B E) (hE0 : x.E0 ⊆ E)
    {ζ : {p // p ∉ x.special} → ℝ} (hζb : ζ ∈ box (x.zeta x.u0) (eps x)) : ζ ∈ x.QE E ↔ ζ ∈ x.QEpaper E :=
  ⟨fun h => QE_subset_QEpaper x hE.subset h, QEpaper_subset_QE_near x hE hE0 hζb⟩

/-- Relative interiors agree near `ζ₀` as well. -/
theorem intrinsicInterior_QE_iff_QEpaper {E : Set (x.toSwitch.P' → ℝ)} (hE : IsFace x.toSwitch.B E)
    (hE0 : x.E0 ⊆ E) {ζ : {p // p ∉ x.special} → ℝ} (hζb : ζ ∈ box (x.zeta x.u0) (eps x)) :
    ζ ∈ intrinsicInterior ℝ (x.QE E) ↔ ζ ∈ intrinsicInterior ℝ (x.QEpaper E) := by
  classical
  have hEc : Convex ℝ E := hE.2.convex (B_convex_closed x.toSwitch).1
  exact (intrinsicInterior_transfer (QEpaper_convex x E) (QE_convex x hEc) id (fun _ _ _ => rfl)
    (fun ζ hζ => ⟨ζ, QE_subset_QEpaper x hE.subset hζ, rfl⟩) (isOpen_box _ _)
    (fun ζ hζ => (QE_iff_QEpaper x hE hE0 hζ).symm) hζb).symm

end XS

end QEPaper

/-- **Lemma 4.5, with the paper's own `Q_E`** (paper lines 752–759): `lemma_4_5_full_proved` with `Q_E` the polyhedron
in the `ζ`-space cut out by the defining inequalities of `B` tight at `u₀`, those tight on all of `E` imposed as
equations (`XSwitch.QEpaper`).  For every face `E ⊇ E₀` of `B`: `ζ₀ ∈ Q_E`, `E ∩ N₀ = V₄ × (Q_E ∩ V_ζ)` and
`relint E ∩ N₀ = V₄ × (relint Q_E ∩ V_ζ)`; part (b) as before. -/
theorem lemma_4_5_paper {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) :
    ∃ (V4 : Set (Fin 4 → ℝ)) (Vz : Set ({p // p ∉ x.special} → ℝ)), IsOpen V4 ∧ IsOpen Vz ∧
      x.alphaPart x.u0 ∈ V4 ∧ x.zeta x.u0 ∈ Vz ∧
      (∀ E, IsFace x.toSwitch.B E → x.E0 ⊆ E → x.zeta x.u0 ∈ x.QEpaper E ∧ ∀ u ∈ x.N0 V4 Vz,
        (u ∈ E ↔ x.zeta u ∈ x.QEpaper E) ∧
        (u ∈ intrinsicInterior ℝ E ↔ x.zeta u ∈ intrinsicInterior ℝ (x.QEpaper E))) ∧
      (∀ u ∈ x.toSwitch.B, u ∈ x.N0 V4 Vz →
        x.toSwitch.L u = max (u x.pa + x.lamA u) (u x.pb + x.lamB u) ∧ x.toSwitch.U u = min (u x.pg) (u x.ph)) := by
  open Lemma45 QEPaper in
  obtain ⟨V4, Vz, hV4, hVz, h4, hz, hA, hB⟩ := lemma_4_5_full_proved x
  refine ⟨V4, Vz ∩ box (x.zeta x.u0) (eps x), hV4, hVz.inter (isOpen_box _ _), h4,
    ⟨hz, center_mem_box _ (eps_pos x)⟩, fun E hE hE0 => ⟨zeta_u0_mem_QEpaper x E, fun u hu => ?_⟩,
    fun u huB hu => hB u huB ⟨hu.1, hu.2.1⟩⟩
  obtain ⟨hmem, hint⟩ := (hA E hE hE0).2 u ⟨hu.1, hu.2.1⟩
  exact ⟨hmem.trans (QE_iff_QEpaper x hE hE0 hu.2.2),
    hint.trans (intrinsicInterior_QE_iff_QEpaper x hE hE0 hu.2.2)⟩

end HibiLi.Proofs
