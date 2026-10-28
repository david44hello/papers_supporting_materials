/-
NagataHigman/Proofs/IdemPrimitive.lean — (F2), paper v1.02 line 186: each `e_λ` is a nonzero, PRIMITIVE central idempotent.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Route: `ρ_μ(e_λ) = δ_{λμ}` (CentralIdempotent.lean). For a central idempotent `e`, `ρ_λ(e)` commutes with every
`ρ_λ(σ)`, so it is a scalar `c` (Schur, Gamma.lean) with `c² = c`; Wedderburn's injectivity then gives
`e e_λ = 0` (`c = 0`) or `e e_λ = e_λ` (`c = 1`).
-/
import NagataHigman.Proofs.CentralIdempotent
import NagataHigman.Proofs.TwoCorner.Section4

noncomputable section

namespace NagataHigman.Proofs

open Equiv Matrix NagataHigman

variable {F : Type*} [Field F] [CharZero F] {N : ℕ}

namespace YoungSystem

theorem dim_pos (Y : YoungSystem F N) (lam : Shape N) : 0 < Y.dim lam :=
  Nat.pos_of_ne_zero fun h => dim_ne_zero Y lam (by rw [h, Nat.cast_zero])

/-- `e_λ ≠ 0`: `ρ_λ(e_λ) = 1` on the nonzero space `S^λ`. -/
theorem youngIdem_ne_zero (Y : YoungSystem F N) (lam : Shape N) : youngIdem F lam ≠ 0 := by
  intro h0
  have h1 := rhoAlg_youngIdem Y lam lam
  rw [ite_eq_left rfl, h0, map_zero] at h1
  have h2 := congrFun (congrFun h1 ⟨0, dim_pos Y lam⟩) ⟨0, dim_pos Y lam⟩
  simp at h2

/-- `e_λ` is primitive: for every central idempotent `e`, `e e_λ` is `0` or `e_λ`. -/
theorem youngIdem_primitive (Y : YoungSystem F N) (lam : Shape N) (e : GrpAlg F N) (he : e * e = e)
    (hc : ∀ a : GrpAlg F N, e * a = a * e) :
    e * youngIdem F lam = 0 ∨ e * youngIdem F lam = youngIdem F lam := by
  obtain ⟨c, hcs⟩ := eq_scalar_of_commute_rho Y lam (Y.rhoAlg lam e) fun σ => by
    rw [← rhoAlg_perm Y, ← map_mul, ← map_mul, hc]
  have hcc : c * c = c := by
    have h2 := congrArg (Y.rhoAlg lam) he
    rw [map_mul, hcs, smul_mul_smul_comm, mul_one] at h2
    have h3 := congrFun (congrFun h2 ⟨0, dim_pos Y lam⟩) ⟨0, dim_pos Y lam⟩
    simpa using h3
  have hrho : ∀ mu, Y.rhoAlg mu (e * youngIdem F lam) = if mu = lam then c • 1 else 0 := fun mu => by
    rw [map_mul, rhoAlg_youngIdem Y lam mu]
    split_ifs with h
    · subst h; rw [hcs, mul_one]
    · rw [mul_zero]
  have hc01 : c * (c - 1) = 0 := by linear_combination hcc
  rcases mul_eq_zero.1 hc01 with h0 | h1
  · left
    refine eq_zero_of_forall_rhoAlg Y _ fun mu => ?_
    rw [hrho mu, h0, zero_smul, ite_self]
  · right
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_rhoAlg Y _ fun mu => ?_
    rw [map_sub, hrho mu, rhoAlg_youngIdem Y lam mu, sub_eq_zero.1 h1, one_smul, sub_self]

end YoungSystem

end NagataHigman.Proofs

end
