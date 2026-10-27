/-
HibiLi/Proofs/Summation.lean — the counting step of Section 4.4 (paper lines 665–677), in abstract form, and the
monotone chain along a linear extension (lines 678–687).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.PaperDefs

namespace HibiLi.Proofs

open HibiLi Polynomial Finset

/-- Coefficients of `t^e (1+t)^2` are nonnegative. -/
lemma coeff_X_pow_mul_one_add_X_sq_nonneg (e k : ℕ) : 0 ≤ (X ^ e * (1 + X) ^ 2 : ℤ[X]).coeff k := by
  rw [coeff_X_pow_mul', coeff_one_add_X_pow]
  split_ifs <;> positivity

/-- `Σ_{j=0}^{M} C(M, j) t^{j+2}(1+t)^2 = t^2 (1+t)^{M+2}`, coefficientwise (paper lines 675–676). -/
lemma binom_sum_identity (M k : ℕ) :
    ∑ j ∈ range (M + 1), (Nat.choose M j : ℤ) * (X ^ (4 + j - 2) * (1 + X) ^ 2 : ℤ[X]).coeff k =
      (X ^ 2 * (1 + X) ^ (M + 2) : ℤ[X]).coeff k := by
  have hpow : ((1 : ℤ[X]) + X) ^ M = ∑ j ∈ range (M + 1), X ^ j * 1 ^ (M - j) * (Nat.choose M j : ℤ[X]) := by
    rw [add_comm]; exact add_pow X 1 M
  have hpoly : (X ^ 2 * (1 + X) ^ (M + 2) : ℤ[X]) =
      ∑ j ∈ range (M + 1), C (Nat.choose M j : ℤ) * (X ^ (4 + j - 2) * (1 + X) ^ 2) := by
    calc (X ^ 2 * (1 + X) ^ (M + 2) : ℤ[X]) = X ^ 2 * (1 + X) ^ 2 * (1 + X) ^ M := by ring
      _ = ∑ j ∈ range (M + 1), C (Nat.choose M j : ℤ) * (X ^ (4 + j - 2) * (1 + X) ^ 2) := by
        rw [hpow, mul_sum]
        refine sum_congr rfl fun j _ => ?_
        have hj : 4 + j - 2 = j + 2 := by omega
        rw [hj, ← map_natCast C]
        ring
  rw [hpoly, finsetSum_coeff]
  exact sum_congr rfl fun j _ => (coeff_C_mul _).symm

open scoped Classical in
/-- **The counting step of Section 4.4**, abstractly.  Let `F` be the (finite) set of faces of `B`, `d` their
dimensions, `δ` the local terms, `E₀` a face.  If every `δ_E ≥ 0` (Lemma 3.5(iii)), every face `E ⊇ E₀` has
`δ_E ≥ t^{dim E − 2}(1+t)^2` (Lemmas 4.2 and 4.6), and `E₀` (of dimension 4) lies in at least `C(M, j)` faces of each
dimension `4 + j` (Lemma 4.8, `M = dim B − 4`), then `Σ_E δ_E ≥ t^2 (1+t)^{M+2}` coefficientwise. -/
theorem gap_from_local_terms {V : Type*} (F : Finset (Set V)) (d : Set V → ℕ) (δ : Set V → ℤ[X])
    (E0 : Set V) (M : ℕ)
    (h1 : ∀ E ∈ F, ∀ k, 0 ≤ (δ E).coeff k)
    (h2 : ∀ E ∈ F, E0 ⊆ E → ∀ k, (X ^ (d E - 2) * (1 + X) ^ 2 : ℤ[X]).coeff k ≤ (δ E).coeff k)
    (h3 : ∀ j ≤ M, Nat.choose M j ≤ (F.filter (fun E => E0 ⊆ E ∧ d E = 4 + j)).card) (k : ℕ) :
    (X ^ 2 * (1 + X) ^ (M + 2) : ℤ[X]).coeff k ≤ (∑ E ∈ F, δ E).coeff k := by
  classical
  let c : ℕ → ℤ := fun e => (X ^ (e - 2) * (1 + X) ^ 2 : ℤ[X]).coeff k
  have hc0 : ∀ e, 0 ≤ c e := fun e => coeff_X_pow_mul_one_add_X_sq_nonneg _ _
  let G := F.filter (fun E => E0 ⊆ E)
  let G' := G.filter (fun E => 4 ≤ d E ∧ d E ≤ 4 + M)
  have hfiber : ∀ j ∈ range (M + 1),
      G'.filter (fun E => d E - 4 = j) = F.filter (fun E => E0 ⊆ E ∧ d E = 4 + j) := by
    intro j hj
    have hjM : j ≤ M := Nat.lt_succ_iff.mp (mem_range.mp hj)
    ext E
    simp only [G', G, mem_filter]
    constructor
    · rintro ⟨⟨⟨hEF, hE0⟩, h4, _⟩, hdj⟩
      exact ⟨hEF, hE0, by omega⟩
    · rintro ⟨hEF, hE0, hdj⟩
      exact ⟨⟨⟨hEF, hE0⟩, by omega, by omega⟩, by omega⟩
  rw [finsetSum_coeff, ← binom_sum_identity M k]
  calc ∑ j ∈ range (M + 1), (Nat.choose M j : ℤ) * c (4 + j)
      ≤ ∑ j ∈ range (M + 1), ((G'.filter (fun E => d E - 4 = j)).card : ℤ) * c (4 + j) := by
        refine sum_le_sum fun j hj => mul_le_mul_of_nonneg_right ?_ (hc0 _)
        rw [hfiber j hj]
        exact_mod_cast h3 j (Nat.lt_succ_iff.mp (mem_range.mp hj))
    _ = ∑ j ∈ range (M + 1), ∑ E ∈ G'.filter (fun E => d E - 4 = j), c (d E) := by
        refine sum_congr rfl fun j _ => ?_
        rw [sum_congr rfl fun E hE => show c (d E) = c (4 + j) by
          have h := (mem_filter.mp hE)
          have h4 := (mem_filter.mp h.1).2.1
          congr 1; omega]
        rw [sum_const, nsmul_eq_mul]
    _ = ∑ E ∈ G', c (d E) := by
        refine sum_fiberwise_of_maps_to (fun E hE => ?_) _
        have h := (mem_filter.mp hE).2
        exact mem_range.mpr (by omega)
    _ ≤ ∑ E ∈ G, c (d E) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => hc0 _)
    _ ≤ ∑ E ∈ G, (δ E).coeff k :=
        sum_le_sum fun E hE => h2 E (mem_filter.mp hE).1 (mem_filter.mp hE).2 k
    _ ≤ ∑ E ∈ F, (δ E).coeff k :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun E hE _ => h1 E hE k)

/-- **The monotone chain** (paper lines 678–687; Fourier's closing remark): if every single switch weakly increases
every face number, then so does passing from any order ideal `I` to any larger order ideal `I'`. -/
theorem mono_of_step {P : Type*} [Fintype P] [PartialOrder P]
    (step : ∀ s : Switch P, ∀ k, fNum (chainOrderPolytope P s.I) k ≤ fNum (chainOrderPolytope P (insert s.q s.I)) k)
    (I I' : Set P) (hI : IsLowerSet I) (hI' : IsLowerSet I') (hII' : I ⊆ I') (k : ℕ) :
    fNum (chainOrderPolytope P I) k ≤ fNum (chainOrderPolytope P I') k := by
  classical
  -- induction on the number of elements of `I' \ I`
  obtain ⟨n, hn⟩ : ∃ n, (Finset.univ.filter (fun p => p ∈ I' ∧ p ∉ I)).card = n := ⟨_, rfl⟩
  induction n generalizing I with
  | zero =>
    have hEq : I = I' := by
      refine Set.Subset.antisymm hII' fun p hp => by_contra fun hpI => ?_
      have : p ∈ Finset.univ.filter (fun p => p ∈ I' ∧ p ∉ I) := by simp [hp, hpI]
      rw [Finset.card_eq_zero.mp hn] at this
      simp at this
    rw [hEq]
  | succ n ih =>
    let D := Finset.univ.filter (fun p => p ∈ I' ∧ p ∉ I)
    have hD : D.Nonempty := Finset.card_pos.mp (by rw [hn]; omega)
    obtain ⟨m, hmD, hmin⟩ := D.exists_minimal hD
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hmD
    -- `m` is minimal outside `I`: everything below it lies in `I`
    have hbelow : ∀ p, p < m → p ∈ I := fun p hp => by_contra fun hpI => by
      have hpD : p ∈ D := by simp [D, hI' hp.le hmD.1, hpI]
      exact hp.not_ge (hmin hpD hp.le)
    let s : Switch P := ⟨I, hI, m, hmD.2, hbelow⟩
    have hlow : IsLowerSet (insert m I) := by
      intro x y hyx hx
      rcases hx with rfl | hx
      · rcases hyx.lt_or_eq with hlt | heq
        · exact Or.inr (hbelow y hlt)
        · exact Or.inl heq
      · exact Or.inr (hI hyx hx)
    have hsub : insert m I ⊆ I' := Set.insert_subset hmD.1 hII'
    have hcard : (Finset.univ.filter (fun p => p ∈ I' ∧ p ∉ insert m I)).card = n := by
      have hsplit : D = insert m (Finset.univ.filter (fun p => p ∈ I' ∧ p ∉ insert m I)) := by
        ext p
        simp only [D, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Set.mem_insert_iff]
        constructor
        · rintro ⟨hp, hpI⟩
          by_cases hpm : p = m
          · exact Or.inl hpm
          · exact Or.inr ⟨hp, fun h => h.elim hpm hpI⟩
        · rintro (rfl | ⟨hp, hpI⟩)
          · exact hmD
          · exact ⟨hp, fun h => hpI (Or.inr h)⟩
      have hnot : m ∉ Finset.univ.filter (fun p => p ∈ I' ∧ p ∉ insert m I) := by simp
      have := congrArg Finset.card hsplit
      rw [Finset.card_insert_of_notMem hnot] at this
      change D.card = _ at hn
      omega
    exact le_trans (step s k) (ih (insert m I) hlow hsub (by convert hcard))

end HibiLi.Proofs
