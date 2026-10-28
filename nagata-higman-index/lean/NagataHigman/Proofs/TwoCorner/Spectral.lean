/-
NagataHigman/Proofs/TwoCorner/Spectral.lean — the Young basis in action: (T1) diagonal coordinates, (T2) the diagonal
entry of ρ(s), the support of ρ(s), and on ν the identity ρ((N-2 N-1)) = -Y_{N-1} Y_{N-2} Y_{N-1} (v1.02 tex 357-366, 421-439).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import NagataHigman.Proofs.JucysMurphy
import NagataHigman.Defs.YoungSystem

noncomputable section

namespace NagataHigman.Proofs

open Equiv Finset Matrix NagataHigman

variable {F : Type*} [Field F] {N : ℕ} (Y : YoungSystem F N)

section YoungBasis

variable {lam : Shape N} (b : Module.Basis (SYT lam) F (Fin (Y.dim lam) → F))

/-- `b` is a Young basis: `ρ(J_k) v_T = c_T(k) v_T`. -/
def IsYoungBasis : Prop :=
  ∀ (T : SYT lam) (k : Fin N), Y.rhoAlg lam (jucysMurphy F k) *ᵥ b T = ((T.content k : ℤ) : F) • b T

/-- An element of `F[S_N]` acting diagonally on the basis `b` acts diagonally on coordinates. -/
theorem repr_mulVec_of_eigen (A : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F) (c : SYT lam → F)
    (hA : ∀ T, A *ᵥ b T = c T • b T) (w : Fin (Y.dim lam) → F) (T : SYT lam) :
    b.repr (A *ᵥ w) T = c T * b.repr w T := by
  have hlin : (b.coord T).comp (Matrix.mulVecLin A) = c T • b.coord T := by
    refine b.ext fun T' => ?_
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, hA, LinearMap.smul_apply, Module.Basis.coord_apply,
      map_smul, smul_eq_mul, Module.Basis.repr_self]
    rcases eq_or_ne T' T with rfl | h
    · rfl
    · simp [h]
  simpa using congrArg (fun L => L w) hlin

/-- (T1), coordinate form: `[ρ(J_k) w]_T = c_T(k) [w]_T`. -/
theorem repr_jucysMurphy (hb : IsYoungBasis Y b) (k : Fin N) (w : Fin (Y.dim lam) → F) (T : SYT lam) :
    b.repr (Y.rhoAlg lam (jucysMurphy F k) *ᵥ w) T = ((T.content k : ℤ) : F) * b.repr w T :=
  repr_mulVec_of_eigen Y b _ (fun T => ((T.content k : ℤ) : F)) (fun T => hb T k) w T

/-- **(T2)**, v1.02 line 365: `ρ(s)_{TT} = 1 / (c_T(k+1) - c_T(k))`, from `s J_{k+1} - J_k s = 1`. Also `c_T(k+1) ≠ c_T(k)`. -/
theorem R_diag_general (hb : IsYoungBasis Y b) (T : SYT lam) (k l : Fin N) (hkl : (l : ℕ) = k + 1) :
    ((T.content l - T.content k : ℤ) : F) ≠ 0 ∧
      b.repr (Y.rho lam (swap k l) *ᵥ b T) T = 1 / (((T.content l - T.content k : ℤ)) : F) := by
  have hrel := congrArg (Y.rhoAlg lam) (R_relation F N k l hkl)
  rw [map_sub, map_mul, map_mul, map_one, YoungSystem.rhoAlg] at hrel
  have hs : MonoidAlgebra.lift F _ (Perm (Fin N)) (Y.rho lam) (perm F (swap k l)) = Y.rho lam (swap k l) := by
    simp [perm, MonoidAlgebra.lift_single]
  rw [hs] at hrel
  have hv := congrArg (fun A => A *ᵥ b T) hrel
  simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec] at hv
  have hJl : MonoidAlgebra.lift F _ (Perm (Fin N)) (Y.rho lam) (jucysMurphy F l) *ᵥ b T =
      ((T.content l : ℤ) : F) • b T := hb T l
  rw [hJl, Matrix.mulVec_smul] at hv
  have hc := congrArg (fun w => b.repr w T) hv
  simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self,
    Finsupp.single_eq_same] at hc
  rw [show MonoidAlgebra.lift F _ (Perm (Fin N)) (Y.rho lam) (jucysMurphy F k) = Y.rhoAlg lam (jucysMurphy F k)
    from rfl, repr_jucysMurphy Y b hb k] at hc
  have hne : ((T.content l - T.content k : ℤ) : F) * b.repr (Y.rho lam (swap k l) *ᵥ b T) T = 1 := by
    push_cast; linear_combination hc
  refine ⟨left_ne_zero_of_mul_eq_one hne, ?_⟩
  rw [eq_div_iff (left_ne_zero_of_mul_eq_one hne), mul_comm, hne]

/-- **(T2)**, support (multiset form): a nonzero entry `ρ(s)_{T'T}` forces equal contents off `{k, k+1}` and the same
pair of contents at `{k, k+1}`, possibly swapped. -/
theorem R_support_contents [CharZero F] (hb : IsYoungBasis Y b) (T T' : SYT lam) (k l : Fin N)
    (hkl : (l : ℕ) = k + 1) (hne : b.repr (Y.rho lam (swap k l) *ᵥ b T) T' ≠ 0) :
    (∀ i, i ≠ k → i ≠ l → T'.content i = T.content i) ∧
      ((T'.content k = T.content k ∧ T'.content l = T.content l) ∨
        (T'.content k = T.content l ∧ T'.content l = T.content k)) := by
  set x := b.repr (Y.rho lam (swap k l) *ᵥ b T) T'
  have hs : Y.rhoAlg lam (perm F (swap k l)) = Y.rho lam (swap k l) := by
    simp [YoungSystem.rhoAlg, perm, MonoidAlgebra.lift_single]
  -- an element A of F[S_N] commuting with s and acting by eigenvalues e on the Young basis forces e T' = e T
  have key : ∀ (A : GrpAlg F N) (e : SYT lam → F), (∀ U, Y.rhoAlg lam A *ᵥ b U = e U • b U) →
      perm F (swap k l) * A = A * perm F (swap k l) → e T' = e T := by
    intro A e hA hcomm
    have hm := congrArg (fun Z => Y.rhoAlg lam Z *ᵥ b T) hcomm
    simp only [map_mul, hs, ← Matrix.mulVec_mulVec, hA] at hm
    rw [Matrix.mulVec_smul] at hm
    have hc := congrArg (fun w => b.repr w T') hm
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hc
    rw [repr_mulVec_of_eigen Y b _ e hA] at hc
    have : (e T' - e T) * x = 0 := by linear_combination -hc
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)
  have hJ : ∀ i U, Y.rhoAlg lam (jucysMurphy F i) *ᵥ b U = ((U.content i : ℤ) : F) • b U := fun i U => hb U i
  have hcast : ∀ a c : ℤ, ((a : ℤ) : F) = ((c : ℤ) : F) → a = c := fun a c h => Int.cast_injective h
  refine ⟨fun i hik hil => hcast _ _ (key _ (fun U => ((U.content i : ℤ) : F)) (hJ i)
    (perm_swap_mul_jucysMurphy_of_ne F k l i hkl hik hil)), ?_⟩
  have hsum := key (jucysMurphy F k + jucysMurphy F l) (fun U => ((U.content k : ℤ) : F) + ((U.content l : ℤ) : F))
    (fun U => by rw [map_add, Matrix.add_mulVec, hJ, hJ, add_smul]) (perm_swap_comm_jucysMurphy_add F k l hkl)
  have hprod := key (jucysMurphy F k * jucysMurphy F l)
    (fun U => ((U.content k : ℤ) : F) * ((U.content l : ℤ) : F))
    (fun U => by rw [map_mul, ← Matrix.mulVec_mulVec, hJ, Matrix.mulVec_smul, hJ, smul_smul, mul_comm])
    (perm_swap_comm_jucysMurphy_mul F k l hkl)
  have hs' : T'.content k + T'.content l = T.content k + T.content l := by exact_mod_cast hsum
  have hp' : T'.content k * T'.content l = T.content k * T.content l := by exact_mod_cast hprod
  have hq : (T'.content k - T.content k) * (T'.content k - T.content l) = 0 := by
    have : T'.content l = T.content k + T.content l - T'.content k := by linarith
    rw [this] at hp'; nlinarith [hp']
  rcases mul_eq_zero.1 hq with h | h
  · left; constructor <;> linarith
  · right; constructor <;> linarith

end YoungBasis

end NagataHigman.Proofs

end
