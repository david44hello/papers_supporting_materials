/-
LeeDiam/Sec6/SigmaGraph.lean — sec_reverse l. 91: the automorphisms of the graphs of O(P_n) and C(P_n) induced by σ,
WITHOUT Theorem 2.1: σ permutes the coordinates (`x ↦ x ∘ σ`), an affine bijection that maps each polytope onto
itself, so it maps vertices to vertices and edges to edges.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Sec1.Vertices
import LeeDiam.Sec6.Structure

namespace LeeDiam

open PnSets

section EqIso

variable {P : Type}

/-- Equal bodies have isomorphic graphs (the identity on vertices). -/
noncomputable def polyGraph_eqIso {body body' : Set (P → ℝ)} (h : body = body') : polyGraph body ≃g polyGraph body' := by
  subst h
  exact SimpleGraph.Iso.refl

theorem polyGraph_eqIso_val {body body' : Set (P → ℝ)} (h : body = body')
    (v : {v : P → ℝ // HibiLi.IsFace body {v}}) : (polyGraph_eqIso h v).1 = v.1 := by
  subst h
  rfl

end EqIso

namespace S6

variable {n : ℕ}

/-- `σ` as a permutation of `P_n`. -/
def sigmaEquiv (n : ℕ) : Pn n ≃ Pn n := ⟨sigma n, sigma n, sigma_sigma, sigma_sigma⟩

/-- The coordinate permutation `x ↦ x ∘ σ`, an affine (indeed linear) bijection of `ℝ^{P_n}`. -/
noncomputable def sigmaPerm (n : ℕ) : (Pn n → ℝ) ≃ᵃ[ℝ] (Pn n → ℝ) :=
  (LinearEquiv.funCongrLeft ℝ ℝ (sigmaEquiv n)).toAffineEquiv

theorem sigmaPerm_apply (x : Pn n → ℝ) : sigmaPerm n x = fun p => x (sigma n p) := rfl

theorem mem_sigma_image {S : Set (Pn n)} {p : Pn n} : p ∈ sigma n '' S ↔ sigma n p ∈ S := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    rwa [sigma_sigma]
  · exact fun h => ⟨sigma n p, h, sigma_sigma p⟩

theorem perm_mem_order {x : Pn n → ℝ} (hx : x ∈ orderPolytope (Pn n)) :
    (fun p => x (sigma n p)) ∈ orderPolytope (Pn n) :=
  ⟨fun p => hx.1 (sigma n p), fun _ _ hpq => hx.2 _ _ (le_sigma_iff.1 hpq)⟩

theorem perm_mem_chain {x : Pn n → ℝ} (hx : x ∈ chainPolytope (Pn n)) :
    (fun p => x (sigma n p)) ∈ chainPolytope (Pn n) := by
  refine ⟨fun p => hx.1 (sigma n p), fun K hK => ?_⟩
  have hK' : HibiLi.IsChainSet (Pn n) (K.map (sigmaEquiv n).toEmbedding) := by
    unfold HibiLi.IsChainSet at hK ⊢
    rw [Finset.coe_map]
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ hne
    rcases hK hu hv (fun h => hne (h ▸ rfl)) with h | h
    · exact Or.inl (le_sigma_iff.1 h)
    · exact Or.inr (le_sigma_iff.1 h)
  simpa [Finset.sum_map, sigmaEquiv] using hx.2 _ hK'

theorem image_order : sigmaPerm n '' orderPolytope (Pn n) = orderPolytope (Pn n) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact perm_mem_order hx
  · intro hy
    exact ⟨fun p => y (sigma n p), perm_mem_order hy, funext fun p => by simp [sigmaPerm_apply, sigma_sigma]⟩

theorem image_chain : sigmaPerm n '' chainPolytope (Pn n) = chainPolytope (Pn n) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact perm_mem_chain hx
  · intro hy
    exact ⟨fun p => y (sigma n p), perm_mem_chain hy, funext fun p => by simp [sigmaPerm_apply, sigma_sigma]⟩

theorem setVector_sigma (S : Set (Pn n)) :
    (fun p => HibiLi.setVector S (sigma n p)) = HibiLi.setVector (sigma n '' S) := by
  classical
  funext p
  simp only [HibiLi.setVector, Set.indicator_apply, mem_sigma_image]

/-- The automorphism of the graph of `O(P_n)` induced by `σ`. -/
noncomputable def orderAut : polyGraph (orderPolytope (Pn n)) ≃g polyGraph (orderPolytope (Pn n)) :=
  (polyGraph_affineIso _ (sigmaPerm n)).trans (polyGraph_eqIso image_order)

/-- The automorphism of the graph of `C(P_n)` induced by `σ`. -/
noncomputable def chainAut : polyGraph (chainPolytope (Pn n)) ≃g polyGraph (chainPolytope (Pn n)) :=
  (polyGraph_affineIso _ (sigmaPerm n)).trans (polyGraph_eqIso image_chain)

theorem orderAut_val (v : {v : Pn n → ℝ // HibiLi.IsFace (orderPolytope (Pn n)) {v}}) :
    (orderAut v).1 = sigmaPerm n v.1 := by
  unfold orderAut
  rw [RelIso.trans_apply, polyGraph_eqIso_val]
  rfl

theorem chainAut_val (v : {v : Pn n → ℝ // HibiLi.IsFace (chainPolytope (Pn n)) {v}}) :
    (chainAut v).1 = sigmaPerm n v.1 := by
  unfold chainAut
  rw [RelIso.trans_apply, polyGraph_eqIso_val]
  rfl

end S6

theorem sec6_sigma_proved (n : ℕ) :
    (∀ x : Pn n, sigma n (sigma n x) = x) ∧
    (∀ x z : Pn n, PnElem.Rel x z ↔ PnElem.Rel (sigma n x) (sigma n z)) ∧
    (∀ x z : Pn n, x ≤ z ↔ sigma n x ≤ sigma n z) ∧
    sigma n '' tgtA n = tgtB n ∧ sigma n '' tgtB n = tgtA n ∧ sigma n PnElem.h = PnElem.h ∧
    (∀ I : Set (Pn n), IsIdeal I → IsIdeal (sigma n '' I)) ∧
    (∀ X : Set (Pn n), IsAntichainSet X → IsAntichainSet (sigma n '' X)) ∧
    (∃ e : polyGraph (orderPolytope (Pn n)) ≃g polyGraph (orderPolytope (Pn n)),
      ∀ (I : Set (Pn n)) (hI : IsIdeal I) (hI' : IsIdeal (sigma n '' I)), e (oVtx I hI) = oVtx (sigma n '' I) hI') ∧
    (∃ e : polyGraph (chainPolytope (Pn n)) ≃g polyGraph (chainPolytope (Pn n)),
      ∀ (X : Set (Pn n)) (hX : IsAntichainSet X) (hX' : IsAntichainSet (sigma n '' X)),
        e (cVtx X hX) = cVtx (sigma n '' X) hX') := by
  refine ⟨S6.sigma_sigma, fun x z => ⟨S6.rel_sigma, fun hr => ?_⟩, fun x z => S6.le_sigma_iff, ?_, ?_, rfl,
    fun I hI => S6.isIdeal_sigma hI, fun X hX => S6.isAntichainSet_sigma hX,
    ⟨S6.orderAut, fun I hI hI' => Subtype.ext ?_⟩, ⟨S6.chainAut, fun X hX hX' => Subtype.ext ?_⟩⟩
  · have h2 := S6.rel_sigma hr
    rwa [S6.sigma_sigma, S6.sigma_sigma] at h2
  · ext x
    constructor
    · rintro ⟨u, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨PnElem.a j, ⟨j, rfl⟩, rfl⟩
  · ext x
    constructor
    · rintro ⟨u, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨PnElem.b i, ⟨i, rfl⟩, rfl⟩
  · rw [S6.orderAut_val, S6.sigmaPerm_apply]
    exact S6.setVector_sigma I
  · rw [S6.chainAut_val, S6.sigmaPerm_apply]
    exact S6.setVector_sigma X

end LeeDiam
