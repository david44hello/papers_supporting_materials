/-
HibiLi/Example21/XVertices.lean — explicit finite convex hulls for Example 2.1.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Vendor.HibiLi.Defs.Examples
import LeeDiam.Vendor.HibiLi.Example21.Argmax

namespace HibiLi

theorem orderPolytope_convex (P : Type*) [Fintype P] [PartialOrder P] :
    Convex ℝ (orderPolytope P) := by
  intro x hx y hy aa bb haa hbb hab
  constructor
  · intro pp
    change 0 ≤ aa * x pp + bb * y pp ∧ aa * x pp + bb * y pp ≤ 1
    constructor
    · exact add_nonneg (mul_nonneg haa (hx.1 pp).1) (mul_nonneg hbb (hy.1 pp).1)
    · nlinarith [(hx.1 pp).2, (hy.1 pp).2]
  · intro pp qq hpq
    change aa * x pp + bb * y pp ≤ aa * x qq + bb * y qq
    exact add_le_add (mul_le_mul_of_nonneg_left (hx.2 pp qq hpq) haa)
      (mul_le_mul_of_nonneg_left (hy.2 pp qq hpq) hbb)

theorem chainPolytope_convex (P : Type*) [Fintype P] [PartialOrder P] :
    Convex ℝ (chainPolytope P) := by
  intro x hx y hy aa bb haa hbb hab
  constructor
  · intro pp
    exact add_nonneg (mul_nonneg haa (hx.1 pp)) (mul_nonneg hbb (hy.1 pp))
  · intro K hK
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    nlinarith [hx.2 K hK, hy.2 K hK]

namespace Example21

open XElem

def xVec (va vb vc vg vh : ℝ) : XElem → ℝ
  | a => va | b => vb | c => vc | g => vg | h => vh

def orderVertex : Fin 8 → XElem → ℝ :=
  ![xVec 0 0 0 0 0, xVec 0 0 0 1 0, xVec 0 0 0 0 1, xVec 0 0 0 1 1,
    xVec 0 0 1 1 1, xVec 1 0 1 1 1, xVec 0 1 1 1 1, xVec 1 1 1 1 1]

def chainVertex : Fin 8 → XElem → ℝ :=
  ![xVec 0 0 0 0 0, xVec 1 0 0 0 0, xVec 0 1 0 0 0, xVec 1 1 0 0 0,
    xVec 0 0 0 1 0, xVec 0 0 0 0 1, xVec 0 0 0 1 1, xVec 0 0 1 0 0]

theorem orderVertex_mem (ii : Fin 8) : orderVertex ii ∈ orderPolytope XElem := by
  constructor
  · intro pp
    fin_cases ii <;> cases pp <;> norm_num [orderVertex, xVec]
  · intro pp qq hpq
    change pp = qq ∨ pp.rank < qq.rank at hpq
    fin_cases ii <;> cases pp <;> cases qq <;>
      simp_all [orderVertex, xVec, XElem.rank]

theorem sum_xVec (K : Finset XElem) (va vb vc vg vh : ℝ) :
    ∑ pp ∈ K, xVec va vb vc vg vh pp =
      (if a ∈ K then va else 0) + (if b ∈ K then vb else 0) +
      (if c ∈ K then vc else 0) + (if g ∈ K then vg else 0) +
      (if h ∈ K then vh else 0) := by
  rw [← Finset.sum_ite_mem_eq K]
  change (∑ pp ∈ ({a, b, c, g, h} : Finset XElem),
    if pp ∈ K then xVec va vb vc vg vh pp else 0) = _
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, reduceCtorEq,
    or_self, not_false_eq_true, Finset.sum_singleton, xVec]
  ring

theorem chainVertex_mem (ii : Fin 8) : chainVertex ii ∈ chainPolytope XElem := by
  constructor
  · intro pp
    fin_cases ii <;> cases pp <;> norm_num [chainVertex, xVec]
  · intro K hK
    have hab : ¬(a ∈ K ∧ b ∈ K) := by
      rintro ⟨ha, hb⟩
      have hh := hK.total ha hb
      change (a = b ∨ a.rank < b.rank) ∨ (b = a ∨ b.rank < a.rank) at hh
      norm_num [XElem.rank] at hh
    have hgh : ¬(g ∈ K ∧ h ∈ K) := by
      rintro ⟨hg, hh⟩
      have hn := hK.total hg hh
      change (g = h ∨ g.rank < h.rank) ∨ (h = g ∨ h.rank < g.rank) at hn
      norm_num [XElem.rank] at hn
    fin_cases ii <;> simp [chainVertex, sum_xVec] <;> split_ifs <;> simp_all

noncomputable def orderWeights (x : XElem → ℝ) : Fin 8 → ℝ :=
  ![1 - max (x g) (x h), x g - min (x g) (x h), x h - min (x g) (x h),
    min (x g) (x h) - x c, x c - max (x a) (x b),
    x a - min (x a) (x b), x b - min (x a) (x b), min (x a) (x b)]

theorem orderWeights_nonneg {x : XElem → ℝ} (hx : x ∈ orderPolytope XElem)
    (ii : Fin 8) : 0 ≤ orderWeights x ii := by
  have hac := hx.2 a c (by decide)
  have hbc := hx.2 b c (by decide)
  have hcg := hx.2 c g (by decide)
  have hch := hx.2 c h (by decide)
  have ha := hx.1 a
  have hb := hx.1 b
  have hg := hx.1 g
  have hh := hx.1 h
  fin_cases ii <;> norm_num [orderWeights]
  all_goals aesop

theorem orderWeights_sum (x : XElem → ℝ) : ∑ ii, orderWeights x ii = 1 := by
  simp [Fin.sum_univ_succ, orderWeights, min_def, max_def]
  split_ifs <;> ring

theorem orderWeights_reconstruct (x : XElem → ℝ) :
    ∑ ii, orderWeights x ii • orderVertex ii = x := by
  ext pp
  cases pp <;> simp [Fin.sum_univ_succ, orderWeights, orderVertex, xVec, min_def, max_def]
  all_goals split_ifs <;> ring

theorem orderPolytope_X_eq_convexHull :
    orderPolytope XElem = convexHull ℝ (Set.range orderVertex) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact mem_convexHull_of_exists_fintype (orderWeights x) orderVertex
      (orderWeights_nonneg hx) (orderWeights_sum x) (fun ii => Set.mem_range_self ii)
      (orderWeights_reconstruct x)
  · exact convexHull_min (Set.range_subset_iff.mpr orderVertex_mem) (orderPolytope_convex XElem)

noncomputable def chainWeights (x : XElem → ℝ) : Fin 8 → ℝ :=
  ![1 - (max (x a) (x b) + x c + max (x g) (x h)),
    x a - min (x a) (x b), x b - min (x a) (x b), min (x a) (x b),
    x g - min (x g) (x h), x h - min (x g) (x h), min (x g) (x h), x c]

theorem chain_sum_max_le {x : XElem → ℝ} (hx : x ∈ chainPolytope XElem) :
    max (x a) (x b) + x c + max (x g) (x h) ≤ 1 := by
  have hag := hx.2 {a, c, g} (by unfold IsChainSet IsChain Set.Pairwise; decide)
  have hah := hx.2 {a, c, h} (by unfold IsChainSet IsChain Set.Pairwise; decide)
  have hbg := hx.2 {b, c, g} (by unfold IsChainSet IsChain Set.Pairwise; decide)
  have hbh := hx.2 {b, c, h} (by unfold IsChainSet IsChain Set.Pairwise; decide)
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, reduceCtorEq,
    or_self, not_false_eq_true, Finset.sum_singleton] at hag hah hbg hbh
  simp only [max_def]
  split_ifs <;> linarith

theorem chainWeights_nonneg {x : XElem → ℝ} (hx : x ∈ chainPolytope XElem)
    (ii : Fin 8) : 0 ≤ chainWeights x ii := by
  have hmax := chain_sum_max_le hx
  have ha := hx.1 a
  have hb := hx.1 b
  have hc := hx.1 c
  have hg := hx.1 g
  have hh := hx.1 h
  fin_cases ii <;> norm_num [chainWeights]
  all_goals aesop

theorem chainWeights_sum (x : XElem → ℝ) : ∑ ii, chainWeights x ii = 1 := by
  simp [Fin.sum_univ_succ, chainWeights, min_def, max_def]
  split_ifs <;> ring

theorem chainWeights_reconstruct (x : XElem → ℝ) :
    ∑ ii, chainWeights x ii • chainVertex ii = x := by
  ext pp
  cases pp <;> simp [Fin.sum_univ_succ, chainWeights, chainVertex, xVec, min_def, max_def]

theorem chainPolytope_X_eq_convexHull :
    chainPolytope XElem = convexHull ℝ (Set.range chainVertex) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact mem_convexHull_of_exists_fintype (chainWeights x) chainVertex
      (chainWeights_nonneg hx) (chainWeights_sum x) (fun ii => Set.mem_range_self ii)
      (chainWeights_reconstruct x)
  · exact convexHull_min (Set.range_subset_iff.mpr chainVertex_mem) (chainPolytope_convex XElem)

end Example21
end HibiLi
