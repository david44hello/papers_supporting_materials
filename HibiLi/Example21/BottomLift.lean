/-
HibiLi/Example21/BottomLift.lean — embed coordinates by assigning zero to a new bottom element.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Example21.LinearEmbedding
import HibiLi.Example21.VertexBijection
import HibiLi.Polytope.Pyramid

namespace HibiLi

variable {P : Type*} [Fintype P]

noncomputable def bottomLift : (P → ℝ) →L[ℝ] (WithBot P → ℝ) :=
  ContinuousLinearMap.pi fun pp =>
    WithBot.recBotCoe 0 (fun qq => ContinuousLinearMap.proj qq) pp

noncomputable def bottomDrop : (WithBot P → ℝ) →L[ℝ] (P → ℝ) :=
  ContinuousLinearMap.pi fun pp => ContinuousLinearMap.proj (pp : WithBot P)

@[simp] theorem bottomLift_bot (v : P → ℝ) : bottomLift v ⊥ = 0 := rfl
@[simp] theorem bottomLift_coe (v : P → ℝ) (pp : P) : bottomLift v pp = v pp := rfl
@[simp] theorem bottomDrop_apply (v : WithBot P → ℝ) (pp : P) : bottomDrop v pp = v pp := rfl

theorem bottomDrop_leftInverse : Function.LeftInverse (bottomDrop (P := P)) bottomLift := by
  intro v
  ext pp
  rfl

theorem facePoly_bottomLift (Q : Set (P → ℝ)) : facePoly (bottomLift '' Q) = facePoly Q :=
  facePoly_image_linear_retract bottomLift bottomDrop bottomDrop_leftInverse Q

theorem IsPolytope.image_linear {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {Q : Set E} (hQ : IsPolytope Q)
    (emb : E →L[ℝ] G) : IsPolytope (emb '' Q) := by
  classical
  obtain ⟨vertices, rfl⟩ := hQ
  refine ⟨vertices.image emb, ?_⟩
  rw [Finset.coe_image]
  exact emb.toLinearMap.toAffineMap.image_convexHull _

theorem bottomLift_apex_outside (Q : Set (P → ℝ)) (apex : WithBot P → ℝ)
    (hapex : apex ⊥ ≠ 0) : apex ∉ affineSpan ℝ (bottomLift '' Q) := by
  let kernel := (ContinuousLinearMap.proj (⊥ : WithBot P) :
    (WithBot P → ℝ) →L[ℝ] ℝ).toLinearMap.ker
  have hspan : affineSpan ℝ (bottomLift '' Q) ≤ kernel.toAffineSubspace := by
    apply affineSpan_le.mpr
    rintro _ ⟨v, _, rfl⟩
    change bottomLift v ⊥ = 0
    rfl
  intro hin
  exact hapex (hspan hin)

def orderBottomApex : WithBot P → ℝ := fun _ => 1
def chainBottomApex : WithBot P → ℝ := WithBot.recBotCoe 1 (fun _ => 0)

@[simp] theorem orderBottomApex_apply (pp : WithBot P) : orderBottomApex pp = 1 := rfl
@[simp] theorem chainBottomApex_bot : chainBottomApex (P := P) ⊥ = 1 := rfl
@[simp] theorem chainBottomApex_coe (pp : P) : chainBottomApex (P := P) (pp : WithBot P) = 0 := rfl

theorem bottomLift_zeroOne {v : P → ℝ} (hv : v ∈ zeroOneVectors P) :
    bottomLift v ∈ zeroOneVectors (WithBot P) := by
  intro pp
  cases pp using WithBot.recBotCoe with
  | bot => simp
  | coe pp => exact hv pp

end HibiLi
