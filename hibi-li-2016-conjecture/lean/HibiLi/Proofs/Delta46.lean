/- The point, segments, linear forms, and explicit valid branches
share the same witness. E=E0 is allowed; E0 supplies all four independent
coordinate directions, so a point face cannot satisfy the hypotheses. -/
import HibiLi.Proofs.Steps46

namespace HibiLi.Proofs

open Finset Filter Topology Metric Steps46 Lemma46

open Classical in
/-- l.797-837: near w the two lower families attain valid branch forms; the
two affine forms are distinct on aff(E), witnessed by an alpha displacement. -/
theorem lemma_4_6_point_full {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P)
    (E : Set (x.toSwitch.P' → ℝ)) (hE : IsFace x.toSwitch.B E) (hE0 : x.E0 ⊆ E) :
    ∃ w ∈ intrinsicInterior ℝ E,
      w x.pa + x.lamA w = w x.pb + x.lamB w ∧ w x.pg = w x.ph ∧
      (∃ ε > 0, ∀ t : ℝ, |t| < ε → w + t • Pi.single x.pa 1 ∈ E ∧ w + t • Pi.single x.pg 1 ∈ E) ∧
      (∃ μa μb : ({p // p ∉ x.special} → ℝ) →ₗ[ℝ] ℝ,
        ∀ᶠ u in 𝓝[E] w, x.lamA u = μa (x.zeta u) ∧ x.lamB u = μb (x.zeta u)) ∧
      ∃ Ka ∈ x.toSwitch.lowBranches, x.pa ∈ Ka ∧
        ∃ Kb ∈ x.toSwitch.lowBranches, x.pb ∈ Kb ∧
          (∀ᶠ u in 𝓝[E] w, x.lamA u = x.toSwitch.chainSum (Ka.erase x.pa) u ∧
            x.lamB u = x.toSwitch.chainSum (Kb.erase x.pb) u) ∧
          (∃ u ∈ affineSpan ℝ E,
            u x.pa + x.toSwitch.chainSum (Ka.erase x.pa) u ≠
              u x.pb + x.toSwitch.chainSum (Kb.erase x.pb) u) := by
  obtain ⟨w, ρ, r, Ka, Kb, hwA, hρ, hrel, hr, hKa, haK, hKb, hbK, hforms, htL, htU⟩ :=
    exists_local_forms x hE hE0
  have hwE : w ∈ E := hrel w hwA (by rw [dist_self]; exact hρ)
  have hwI : w ∈ intrinsicInterior ℝ E := mem_intrinsicInterior_iff.mpr ⟨hwA, ρ, hρ, hrel⟩
  obtain ⟨hla, hlb⟩ := hforms w ⟨hwE, mem_ball_self hr⟩
  have htie : w x.pa + x.toSwitch.chainSum (Ka.erase x.pa) w =
      w x.pb + x.toSwitch.chainSum (Kb.erase x.pb) w := by
    unfold Switch.chainSum at htL ⊢
    rw [← Finset.add_sum_erase Ka (fun p => w p) haK,
      ← Finset.add_sum_erase Kb (fun p => w p) hbK] at htL
    exact htL
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
  have hevent : ∀ᶠ u in 𝓝[E] w, x.lamA u = x.toSwitch.chainSum (Ka.erase x.pa) u ∧
      x.lamB u = x.toSwitch.chainSum (Kb.erase x.pb) u :=
    Filter.eventually_of_mem (inter_mem_nhdsWithin E (ball_mem_nhds w hr)) fun u hu => hforms u hu
  refine ⟨w, hwI, by simpa only [hla, hlb] using htie, htU,
    ⟨ρ, hρ, fun t ht => ⟨hseg hea hnorm1 t ht, hseg heg hnorm1 t ht⟩⟩,
    ⟨μa, μb, hevent.mono fun u hu => by rw [hu.1, hu.2, hμa, hμb]; exact ⟨rfl, rfl⟩⟩,
    Ka, hKa, haK, Kb, hKb, hbK, hevent, ?_⟩
  refine ⟨w + Pi.single x.pa 1, ?_, ?_⟩
  · rw [add_comm]
    exact AffineSubspace.vadd_mem_of_mem_direction (by rwa [direction_affineSpan]) hwA
  · have hd : ∀ p, p ∉ x.special → (Pi.single x.pa (1 : ℝ) : x.toSwitch.P' → ℝ) p = 0 := by
      intro p hp
      have hne : p ≠ x.pa := fun h => hp (by simp [h, XSwitch.special])
      exact Pi.single_eq_of_ne hne _
    rw [form_add x hKa (Or.inl rfl) haK hd, form_add x hKb (Or.inr rfl) hbK hd]
    have hab : x.pb ≠ x.pa := (Lemma45.distinct x).1.symm
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab, add_zero]
    linarith

end HibiLi.Proofs

#print axioms HibiLi.Proofs.lemma_4_6_point_full
