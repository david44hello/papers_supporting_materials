/-
HibiLi/Proofs/Steps42.lean — the intermediate claims of the proof of Lemma 4.2 (v2.10 l. 595-629).
Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Proofs.Lemma42
import HibiLi.Proofs.V060Claims
import HibiLi.Proofs.StepRows
import HibiLi.Polytope.RelintPartition

namespace HibiLi.Proofs.Steps42

open Set Filter L42
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- If `w ∈ X ∩ aff(E)` and `dir(X) = dir(E) ∩ ker φ`, then `aff(X)` is the hyperplane `{φ = φ w}` of `aff(E)`. -/
theorem affineSpan_eq_hyperplane {X E : Set V} {w : V} (φ : V →ₗ[ℝ] ℝ) (hwX : w ∈ X)
    (hwE : w ∈ affineSpan ℝ E) (hspan : vectorSpan ℝ X = vectorSpan ℝ E ⊓ LinearMap.ker φ) :
    (affineSpan ℝ X : Set V) = {u | u ∈ affineSpan ℝ E ∧ φ u = φ w} := by
  ext u
  have hwX' : w ∈ affineSpan ℝ X := subset_affineSpan ℝ X hwX
  simp only [SetLike.mem_coe, Set.mem_ofPred_eq]
  rw [← AffineSubspace.vsub_right_mem_direction_iff_mem hwX' u, direction_affineSpan, hspan,
    ← AffineSubspace.vsub_right_mem_direction_iff_mem hwE u, direction_affineSpan, Submodule.mem_inf,
    LinearMap.mem_ker, vsub_eq_sub, map_sub, sub_eq_zero]

end HibiLi.Proofs.Steps42

namespace HibiLi.Proofs

open Set Filter L42 Steps42
open scoped Topology

/-- **Proof of Lemma 4.2, the intermediate claims** (v2.10 l. 595-629), under the v2.10 hypothesis of Lemma 4.2 for the
given `N, S₁, S₂, T₁, T₂, φ, ψ` (the body of `lemma_4_2_v190`'s hypothesis, unbundled): `S_w = S₁ ∩ S₂` is an
`(e−1)`-cell of `S` with `w` in its relative interior, carrier `E` and affine span `H_S` (l. 595-602), and the same for
`T_w = T₁ ∩ T₂` with `H_T`; `R_w = S_w ∩ T_w` is an `(e−2)`-cell of `R` with `w` in its relative interior, in no `R(Y)`
(l. 604-611; by uniqueness of the cell whose relative interior contains `w`, as in the paper);
`|R(S_w)| ≥ 2`, `|R(T_w)| ≥ 2` (l. 614-620); the four `S_i ∩ T_j` are `e`-cells of `R|_E` (l. 625-629). -/
theorem lemma_4_2_steps_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ))
    (hE : IsFace s.B E) (w : s.P' → ℝ) (hw : w ∈ intrinsicInterior ℝ E) (N S₁ S₂ T₁ T₂ : Set (s.P' → ℝ))
    (φ ψ : (s.P' → ℝ) →ₗ[ℝ] ℝ)
    (H : Convex ℝ N ∧ N ⊆ E ∧
      (∃ O : Set (s.P' → ℝ), IsOpen O ∧ N = O ∩ (affineSpan ℝ E : Set (s.P' → ℝ))) ∧ w ∈ N ∧
        S₁ ∈ s.topCells s.cellsS E ∧ S₂ ∈ s.topCells s.cellsS E ∧
        T₁ ∈ s.topCells s.cellsT E ∧ T₂ ∈ s.topCells s.cellsT E ∧
        (∀ A ∈ s.topCells s.cellsS E, (A ∩ N).Nonempty → A = S₁ ∨ A = S₂) ∧
        (∀ D ∈ s.topCells s.cellsT E, (D ∩ N).Nonempty → D = T₁ ∨ D = T₂) ∧
        S₁ ∩ N = {u ∈ N | φ w ≤ φ u} ∧ S₂ ∩ N = {u ∈ N | φ u ≤ φ w} ∧
        T₁ ∩ N = {u ∈ N | ψ w ≤ ψ u} ∧ T₂ ∩ N = {u ∈ N | ψ u ≤ ψ w} ∧
        φ.domRestrict (vectorSpan ℝ E) ≠ 0 ∧ ψ.domRestrict (vectorSpan ℝ E) ≠ 0 ∧
        {u | u ∈ affineSpan ℝ E ∧ φ u = φ w} ≠ {u | u ∈ affineSpan ℝ E ∧ ψ u = ψ w}) :
    S₁ ∩ S₂ ∈ s.cellsS ∧ adim (S₁ ∩ S₂) + 1 = adim E ∧ w ∈ intrinsicInterior ℝ (S₁ ∩ S₂) ∧
      IsCarrier s.B E (S₁ ∩ S₂) ∧
      (affineSpan ℝ (S₁ ∩ S₂) : Set _) = {u | u ∈ affineSpan ℝ E ∧ φ u = φ w} ∧
    T₁ ∩ T₂ ∈ s.cellsT ∧ adim (T₁ ∩ T₂) + 1 = adim E ∧ w ∈ intrinsicInterior ℝ (T₁ ∩ T₂) ∧
      IsCarrier s.B E (T₁ ∩ T₂) ∧
      (affineSpan ℝ (T₁ ∩ T₂) : Set _) = {u | u ∈ affineSpan ℝ E ∧ ψ u = ψ w} ∧
    (S₁ ∩ S₂) ∩ (T₁ ∩ T₂) ∈ s.cellsR ∧ adim ((S₁ ∩ S₂) ∩ (T₁ ∩ T₂)) + 2 = adim E ∧
      w ∈ intrinsicInterior ℝ ((S₁ ∩ S₂) ∩ (T₁ ∩ T₂)) ∧
      (∀ Y, (Y ∈ s.cellsS ∨ Y ∈ s.cellsT) → IsCarrier s.B E Y → adim Y + 2 = adim E →
        (S₁ ∩ S₂) ∩ (T₁ ∩ T₂) ∉ s.RR Y) ∧
    2 ≤ (s.RR (S₁ ∩ S₂)).ncard ∧ 2 ≤ (s.RR (T₁ ∩ T₂)).ncard ∧
    S₁ ∩ T₁ ∈ s.topCells s.cellsR E ∧ S₁ ∩ T₂ ∈ s.topCells s.cellsR E ∧
    S₂ ∩ T₁ ∈ s.topCells s.cellsR E ∧ S₂ ∩ T₂ ∈ s.topCells s.cellsR E := by
  obtain ⟨-, -, ⟨O, hO, hNO⟩, hwN, hS₁, hS₂, hT₁, hT₂, -, -, hS₁N, hS₂N, hT₁N, hT₂N, hφ0, hψ0, hne⟩ := H
  have hwA : w ∈ affineSpan ℝ E := subset_affineSpan ℝ E (intrinsicInterior_subset hw)
  have hind := (linearIndependent_pair_iff_hyperplanes_ne E hwA φ ψ).2 ⟨hφ0, hψ0, hne⟩
  have hwO : w ∈ O := by
    rw [hNO] at hwN
    exact hwN.1
  have hNw : N ∈ 𝓝[E] w := by
    refine mem_nhdsWithin.2 ⟨O, hO, hwO, fun u hu => ?_⟩
    rw [hNO]
    exact ⟨hu.1, subset_affineSpan ℝ E hu.2⟩
  obtain ⟨ε, hε, hball⟩ := exists_ball hw hNw
  have hL : Local E N w ε := ⟨hε, hball⟩
  -- dual vectors and the dimensions of the model subspaces (as in `L42.crossing_counts`)
  obtain ⟨v₁, hv₁, h1⟩ := surj_of_linearIndependent _ φ ψ hind (1, 0)
  obtain ⟨v₂, hv₂, h2⟩ := surj_of_linearIndependent _ φ ψ hind (0, 1)
  have h11 : φ v₁ = 1 := congrArg Prod.fst h1
  have h12 : ψ v₁ = 0 := congrArg Prod.snd h1
  have h21 : φ v₂ = 0 := congrArg Prod.fst h2
  have h22 : ψ v₂ = 1 := congrArg Prod.snd h2
  have hadim : adim E = Module.finrank ℝ (vectorSpan ℝ E) := rfl
  have hdimφ : Module.finrank ℝ ↥(vectorSpan ℝ E ⊓ LinearMap.ker φ) + 1 = adim E := by
    have := finrank_inf_ker_add (vectorSpan ℝ E) φ
      (fun y => ⟨y • v₁, Submodule.smul_mem _ _ hv₁, by simp [h11]⟩)
    rw [Module.finrank_self] at this
    rw [hadim]; exact this
  have hdimψ : Module.finrank ℝ ↥(vectorSpan ℝ E ⊓ LinearMap.ker ψ) + 1 = adim E := by
    have := finrank_inf_ker_add (vectorSpan ℝ E) ψ
      (fun y => ⟨y • v₂, Submodule.smul_mem _ _ hv₂, by simp [h22]⟩)
    rw [Module.finrank_self] at this
    rw [hadim]; exact this
  have hdim2 : Module.finrank ℝ ↥(vectorSpan ℝ E ⊓ LinearMap.ker φ ⊓ LinearMap.ker ψ) + 2 = adim E := by
    have := finrank_inf_ker_add (vectorSpan ℝ E) (φ.prod ψ) (surj_of_linearIndependent _ φ ψ hind)
    rw [LinearMap.ker_prod, ← inf_assoc, Module.finrank_prod, Module.finrank_self] at this
    rw [hadim]; omega
  -- the walls `S_w`, `T_w` and the crossing `R_w` (l. 595-611)
  have hS₁c : S₁ ∈ s.cellsS := s.restrict_cellsS_subset hE hS₁.1
  have hS₂c : S₂ ∈ s.cellsS := s.restrict_cellsS_subset hE hS₂.1
  have hT₁c : T₁ ∈ s.cellsT := s.restrict_cellsT_subset hE hT₁.1
  have hT₂c : T₂ ∈ s.cellsT := s.restrict_cellsT_subset hE hT₂.1
  have hwS₁ : w ∈ S₁ := hL.w_mem hS₁N
  have hwS₂ : w ∈ S₂ := hL.w_mem (Local.half_neg hS₂N)
  have hwT₁ : w ∈ T₁ := hL.w_mem hT₁N
  have hwT₂ : w ∈ T₂ := hL.w_mem (Local.half_neg hT₂N)
  have hSw : S₁ ∩ S₂ ∈ s.cellsS :=
    top_inter_mem (maxFamily_L s) (s.restrict_cellsS_subset hE) hS₁ hS₂ ⟨w, hwS₁, hwS₂⟩
  have hTw : T₁ ∩ T₂ ∈ s.cellsT :=
    top_inter_mem (maxFamily_U s) (s.restrict_cellsT_subset hE) hT₁ hT₂ ⟨w, hwT₁, hwT₂⟩
  have hSwE : S₁ ∩ S₂ ⊆ E := inter_subset_left.trans (top_subset hS₁)
  have hTwE : T₁ ∩ T₂ ⊆ E := inter_subset_left.trans (top_subset hT₁)
  have hSwspan := hL.wall_span hS₁N hS₂N ((maxFamily_L s).convex_of_mem hSw) hSwE
  have hTwspan := hL.wall_span hT₁N hT₂N ((maxFamily_U s).convex_of_mem hTw) hTwE
  have hSwdim : adim (S₁ ∩ S₂) = Module.finrank ℝ ↥(vectorSpan ℝ E ⊓ LinearMap.ker φ) := by
    unfold adim; rw [hSwspan]
  have hTwdim : adim (T₁ ∩ T₂) = Module.finrank ℝ ↥(vectorSpan ℝ E ⊓ LinearMap.ker ψ) := by
    unfold adim; rw [hTwspan]
  have hSwcar : IsCarrier s.B E (S₁ ∩ S₂) := isCarrier_of_relint hE hSwE ⟨hwS₁, hwS₂⟩ hw
  have hTwcar : IsCarrier s.B E (T₁ ∩ T₂) := isCarrier_of_relint hE hTwE ⟨hwT₁, hwT₂⟩ hw
  have hwR : w ∈ S₁ ∩ S₂ ∩ (T₁ ∩ T₂) := ⟨⟨hwS₁, hwS₂⟩, ⟨hwT₁, hwT₂⟩⟩
  have hRw : S₁ ∩ S₂ ∩ (T₁ ∩ T₂) ∈ s.cellsR := ⟨⟨w, hwR⟩, _, hSw, _, hTw, rfl⟩
  have hRwspan := hL.cross_span hS₁N hS₂N hT₁N hT₂N ((maxFamily_L s).convex_of_mem hSw) hSwE
    ((maxFamily_U s).convex_of_mem hTw) hTwE
  have hRwdim : adim (S₁ ∩ S₂ ∩ (T₁ ∩ T₂)) =
      Module.finrank ℝ ↥(vectorSpan ℝ E ⊓ LinearMap.ker φ ⊓ LinearMap.ker ψ) := by
    unfold adim; rw [hRwspan]
  have hSwrel : w ∈ intrinsicInterior ℝ (S₁ ∩ S₂) :=
    mem_intrinsicInterior_of_ball hε ⟨hwS₁, hwS₂⟩ hSwspan.le (hL.wall_ball hS₁N hS₂N)
  have hTwrel : w ∈ intrinsicInterior ℝ (T₁ ∩ T₂) :=
    mem_intrinsicInterior_of_ball hε ⟨hwT₁, hwT₂⟩ hTwspan.le (hL.wall_ball hT₁N hT₂N)
  have hRwrel : w ∈ intrinsicInterior ℝ (S₁ ∩ S₂ ∩ (T₁ ∩ T₂)) :=
    mem_intrinsicInterior_of_ball hε hwR hRwspan.le (hL.cross_ball hS₁N hS₂N hT₁N hT₂N)
  have hres : ∀ {K : Set (Set (s.P' → ℝ))} {Y : Set (s.P' → ℝ)}, Y ∈ K → Y ⊆ E → w ∈ Y → Y ∈ s.restrict K E :=
    fun hY hYE hwY => ⟨⟨w, hwY⟩, _, hY, (inter_eq_left.mpr hYE).symm⟩
  -- `R_w` lies in no `R(Y)` (l. 607-611): `w ∈ relint R_w ⊆ relint Y`, so `Y = S_w` or `Y = T_w` (the cell of `S`, resp.
  -- `T`, whose relative interior contains `w` is unique), and these have dimension `e − 1`, not `e − 2`
  have hwB : w ∈ s.B := hE.2.subset (intrinsicInterior_subset hw)
  obtain ⟨cS, cT, -, hcSeq, hcTeq, -, hsubS, hsubT, -⟩ := sec3_subdivisions_proved s
  have hnot : ∀ Y, (Y ∈ s.cellsS ∨ Y ∈ s.cellsT) → IsCarrier s.B E Y → adim Y + 2 = adim E →
      S₁ ∩ S₂ ∩ (T₁ ∩ T₂) ∉ s.RR Y := by
    intro Y hY _ hYk hRY
    have hwY : w ∈ intrinsicInterior ℝ Y := lemma_3_5_i_relint s hY hRY hRwrel
    rcases hY with hY | hY
    · obtain ⟨C, -, huniq⟩ := subdivision_relint_partition s.B cS hsubS w hwB
      have hYS : Y = S₁ ∩ S₂ := (huniq Y ⟨by simpa [← hcSeq] using hY, hwY⟩).trans
        (huniq _ ⟨by simpa [← hcSeq] using hSw, hSwrel⟩).symm
      subst hYS
      omega
    · obtain ⟨C, -, huniq⟩ := subdivision_relint_partition s.B cT hsubT w hwB
      have hYT : Y = T₁ ∩ T₂ := (huniq Y ⟨by simpa [← hcTeq] using hY, hwY⟩).trans
        (huniq _ ⟨by simpa [← hcTeq] using hTw, hTwrel⟩).symm
      subst hYT
      omega
  -- each wall is cut in two by the other hyperplane (l. 614-620)
  have hRR : ∀ {Y Z : Set (s.P' → ℝ)}, Z ∈ s.cellsR → Z ⊆ Y → vectorSpan ℝ Y ≤ vectorSpan ℝ Z →
      Z ∈ s.RR Y :=
    fun hZ hZY hspan => ⟨hZ, hZY, le_antisymm (Submodule.finrank_mono (vectorSpan_mono ℝ hZY))
      (Submodule.finrank_mono hspan)⟩
  have hfin : ∀ Y : Set (s.P' → ℝ), (s.RR Y).Finite := fun Y => s.cellsR_finite.subset fun _ h => h.1
  have hcS : 2 ≤ (s.RR (S₁ ∩ S₂)).ncard := by
    refine (Set.one_lt_ncard_iff (hfin _)).2 ⟨S₁ ∩ S₂ ∩ T₁, S₁ ∩ S₂ ∩ T₂, ?_, ?_,
      hL.halfwall_ne hS₁N hS₂N hT₁N hT₂N hv₂ h21 h22⟩
    · exact hRR ⟨⟨w, ⟨hwS₁, hwS₂⟩, hwT₁⟩, _, hSw, _, hT₁c, rfl⟩ inter_subset_left
        (hSwspan ▸ hL.halfwall_span hS₁N hS₂N hT₁N hv₂ h21 h22)
    · exact hRR ⟨⟨w, ⟨hwS₁, hwS₂⟩, hwT₂⟩, _, hSw, _, hT₂c, rfl⟩ inter_subset_left
        (hSwspan ▸ hL.halfwall_span hS₁N hS₂N (Local.half_neg hT₂N) (Submodule.neg_mem _ hv₂)
          (by simp [h21]) (by simp [h22]))
  have hcT : 2 ≤ (s.RR (T₁ ∩ T₂)).ncard := by
    refine (Set.one_lt_ncard_iff (hfin _)).2 ⟨T₁ ∩ T₂ ∩ S₁, T₁ ∩ T₂ ∩ S₂, ?_, ?_,
      hL.halfwall_ne hT₁N hT₂N hS₁N hS₂N hv₁ h12 h11⟩
    · exact hRR ⟨⟨w, ⟨hwT₁, hwT₂⟩, hwS₁⟩, _, hS₁c, _, hTw, inter_comm _ _⟩ inter_subset_left
        (hTwspan ▸ hL.halfwall_span hT₁N hT₂N hS₁N hv₁ h12 h11)
    · exact hRR ⟨⟨w, ⟨hwT₁, hwT₂⟩, hwS₂⟩, _, hS₂c, _, hTw, inter_comm _ _⟩ inter_subset_left
        (hTwspan ▸ hL.halfwall_span hT₁N hT₂N (Local.half_neg hS₂N) (Submodule.neg_mem _ hv₁)
          (by simp [h12]) (by simp [h11]))
  -- the four quadrants are `e`-cells of `R|_E` (l. 625-629)
  have htopR : ∀ {A D : Set (s.P' → ℝ)}, A ∈ s.topCells s.cellsS E → D ∈ s.topCells s.cellsT E →
      w ∈ A → w ∈ D → vectorSpan ℝ E ≤ vectorSpan ℝ (A ∩ D) → A ∩ D ∈ s.topCells s.cellsR E := by
    intro A D hA hD hwA hwD hspan
    have hADE : A ∩ D ⊆ E := inter_subset_left.trans (top_subset hA)
    exact ⟨hres ⟨⟨w, hwA, hwD⟩, A, s.restrict_cellsS_subset hE hA.1, D, s.restrict_cellsT_subset hE hD.1, rfl⟩
        hADE ⟨hwA, hwD⟩,
      le_antisymm (Submodule.finrank_mono (vectorSpan_mono ℝ hADE)) (Submodule.finrank_mono hspan)⟩
  refine ⟨hSw, by omega, hSwrel, hSwcar, affineSpan_eq_hyperplane φ ⟨hwS₁, hwS₂⟩ hwA hSwspan,
    hTw, by omega, hTwrel, hTwcar, affineSpan_eq_hyperplane ψ ⟨hwT₁, hwT₂⟩ hwA hTwspan,
    hRw, by omega, hRwrel, hnot, hcS, hcT, ?_, ?_, ?_, ?_⟩
  · exact htopR hS₁ hT₁ hwS₁ hwT₁ (hL.quadrant_span hS₁N hT₁N hv₁ hv₂ h11 h12 h21 h22)
  · exact htopR hS₁ hT₂ hwS₁ hwT₂ (hL.quadrant_span hS₁N (Local.half_neg hT₂N) hv₁ (Submodule.neg_mem _ hv₂)
      h11 (by simp [h12]) (by simp [h21]) (by simp [h22]))
  · exact htopR hS₂ hT₁ hwS₂ hwT₁ (hL.quadrant_span (Local.half_neg hS₂N) hT₁N (Submodule.neg_mem _ hv₁) hv₂
      (by simp [h11]) (by simp [h12]) (by simp [h21]) h22)
  · exact htopR hS₂ hT₂ hwS₂ hwT₂ (hL.quadrant_span (Local.half_neg hS₂N) (Local.half_neg hT₂N)
      (Submodule.neg_mem _ hv₁) (Submodule.neg_mem _ hv₂)
      (by simp [h11]) (by simp [h12]) (by simp [h21]) (by simp [h22]))

end HibiLi.Proofs
