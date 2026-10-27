/-
HibiLi/Proofs/Lemma44.lean — proof of paper Lemma 4.4: `E₀` is a 4-dimensional face of `B` with the displayed description.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.PaperDefs

namespace HibiLi.Proofs

open Finset

/-- A set `F ⊆ B` is exposed when a weight `w` gives the termwise bounds `w i u_i ≤ w i v_i` (`u ∈ B`, `v ∈ F`) and
termwise equality forces membership in `F`; the exposing functional is `u ↦ Σ_i w_i u_i`. -/
lemma isExposed_of_termwise {ι : Type*} [Fintype ι] {B F : Set (ι → ℝ)} (w : ι → ℝ) (hFB : F ⊆ B)
    (hle : ∀ u ∈ B, ∀ v ∈ F, ∀ i, w i * u i ≤ w i * v i)
    (heq : ∀ u ∈ B, ∀ v ∈ F, (∀ i, w i * u i = w i * v i) → u ∈ F) : IsExposed ℝ B F := by
  rintro ⟨v, hv⟩
  refine ⟨∑ i, w i • ContinuousLinearMap.proj i, ?_⟩
  ext u
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Set.mem_ofPred_eq]
  constructor
  · intro hu
    exact ⟨hFB hu, fun y hy => Finset.sum_le_sum fun i _ => hle y hy u hu i⟩
  · rintro ⟨hu, hmax⟩
    have hle' : ∀ i ∈ univ, w i * u i ≤ w i * v i := fun i _ => hle u hu v hv i
    have hsum := (Finset.sum_eq_sum_iff_of_le hle').mp
      (le_antisymm (Finset.sum_le_sum hle') (hmax v (hFB hv)))
    exact heq u hu v hv fun i => hsum i (mem_univ i)

namespace Lemma44

variable {P : Type*} [Fintype P] [PartialOrder P] (x : HibiLi.XSwitch P)

lemma a_mem_I : x.a ∈ x.toSwitch.I := fun h => lt_irrefl _ (x.a_lt_q.trans_le h)
lemma b_mem_I : x.b ∈ x.toSwitch.I := fun h => lt_irrefl _ (x.b_lt_q.trans_le h)
lemma g'_notMem_I : x.g' ∉ x.toSwitch.I := fun h => h x.q_covby_g'.lt.le
lemma h'_notMem_I : x.h' ∉ x.toSwitch.I := fun h => h x.q_covby_h'.lt.le
lemma a_ne_b : x.a ≠ x.b := fun h => x.isX.2.2.2.2.1 h.le

/-- Every coordinate of `J' = J \ {q}` lies strictly above `q`. -/
lemma q_lt_of_notMem {r : x.toSwitch.P'} (hr : r.1 ∉ x.toSwitch.I) : x.q < r.1 :=
  lt_of_le_of_ne (not_not.mp hr) (Ne.symm r.2)

/-- On a chain `K ⊆ I`, a point vanishing on `I \ {a, b}` has chain sum at most `max(α, β)`: `K` meets at most one
of the incomparable `a, b`. -/
lemma chainSum_le_max {u : x.toSwitch.P' → ℝ} {pa pb : x.toSwitch.P'} (hpa : pa.1 = x.a) (hpb : pb.1 = x.b)
    (hz : ∀ p : x.toSwitch.P', p.1 ∈ x.toSwitch.I → p.1 ≠ x.a → p.1 ≠ x.b → u p = 0)
    (ha : 0 ≤ u pa) {K : Finset x.toSwitch.P'} (hKI : ↑K ⊆ x.toSwitch.I')
    (hK : IsChainSet x.toSwitch.P' K) : ∑ p ∈ K, u p ≤ max (u pa) (u pb) := by
  have hz' : ∀ p ∈ K, p ≠ pa → p ≠ pb → u p = 0 := fun p hp h1 h2 =>
    hz p (hKI hp) (fun h => h1 (Subtype.ext (h.trans hpa.symm)))
      (fun h => h2 (Subtype.ext (h.trans hpb.symm)))
  by_cases hA : pa ∈ K
  · have hB : pb ∉ K := by
      intro hB
      have hne : pa ≠ pb := fun h => a_ne_b x (by rw [← hpa, ← hpb, h])
      rcases hK hA hB hne with h | h
      · exact x.isX.2.2.2.2.1 (by rw [← hpa, ← hpb]; exact h)
      · exact x.isX.2.2.2.2.2.1 (by rw [← hpa, ← hpb]; exact h)
    rw [Finset.sum_eq_single_of_mem pa hA fun p hp hne => hz' p hp hne fun h => hB (h ▸ hp)]
    exact le_max_left _ _
  · by_cases hB : pb ∈ K
    · rw [Finset.sum_eq_single_of_mem pb hB fun p hp hne => hz' p hp (fun h => hA (h ▸ hp)) hne]
      exact le_max_right _ _
    · rw [Finset.sum_eq_zero fun p hp => hz' p hp (fun h => hA (h ▸ hp)) fun h => hB (h ▸ hp)]
      exact le_max_of_le_left ha

/-- A chain inequality of `B` with the one-element chain `{p}`: `u_p ≤ u_r` for `p ∈ I`, `r ∈ J'`, `p < r`. -/
lemma le_of_single {u : x.toSwitch.P' → ℝ} (hu : u ∈ x.toSwitch.B) {p r : x.toSwitch.P'}
    (hp : p ∈ x.toSwitch.I') (hr : r ∉ x.toSwitch.I') (hpr : p < r) : u p ≤ u r := by
  simpa using hu.2.2.2.1 r hr {p} (by simpa using hp) (by simp [IsChainSet]) (by simpa using hpr)

open Classical in
/-- The exposing weight: `-1` on chain coordinates other than `a, b`, `+1` on order coordinates other than
`g', h'`, and `0` on `α, β, γ, η`. -/
noncomputable def wt (p : x.toSwitch.P') : ℝ :=
  if p.1 ∈ x.toSwitch.I then (if p.1 = x.a ∨ p.1 = x.b then 0 else -1)
  else (if p.1 = x.g' ∨ p.1 = x.h' then 0 else 1)

/-- Paper Lemma 4.4, face part: `E₀` maximizes `Σ_p wt_p u_p` over `B` (the equalities `x_p = 0`, `y_r = 1` come from
valid inequalities of `B`). -/
lemma E0_isExposed : IsExposed ℝ x.toSwitch.B x.E0 := by
  refine isExposed_of_termwise (wt x) (fun u hu => hu.1) ?_ ?_
  · intro u hu v hv p
    unfold wt
    split_ifs with hp hab hab'
    · simp
    · push Not at hab
      rw [hv.2.1 p hp hab.1 hab.2]
      linarith [hu.1 p hp]
    · simp
    · push Not at hab'
      rw [hv.2.2 p hp hab'.1 hab'.2]
      linarith [(hu.2.1 p hp).2]
  · intro u hu v hv heq
    refine ⟨hu, fun p hp ha hb => ?_, fun r hr hg hh => ?_⟩
    · have h := heq p
      simp only [wt, ite_eq_left hp, ite_eq_right (not_or.mpr ⟨ha, hb⟩), hv.2.1 p hp ha hb] at h
      linarith
    · have h := heq r
      simp only [wt, ite_eq_right hr, ite_eq_right (not_or.mpr ⟨hg, hh⟩), hv.2.2 r hr hg hh] at h
      linarith

open Classical in
/-- The base point of `E₀`: `(α, β, γ, η) = (0, 0, 1, 1)` and `ζ = ζ₀`. -/
noncomputable def v0 (p : x.toSwitch.P') : ℝ := if p.1 ∈ x.toSwitch.I then 0 else 1

/-- Directions vanishing off four given coordinates. -/
def offFour {ι : Type*} (pa pb pg ph : ι) : Submodule ℝ (ι → ℝ) where
  carrier := {v | ∀ p, p ≠ pa → p ≠ pb → p ≠ pg → p ≠ ph → v p = 0}
  add_mem' := fun hv hw p h1 h2 h3 h4 => by simp [hv p h1 h2 h3 h4, hw p h1 h2 h3 h4]
  zero_mem' := fun _ _ _ _ _ => rfl
  smul_mem' := fun c v hv p h1 h2 h3 h4 => by simp [hv p h1 h2 h3 h4]

lemma ne_of_val_ne {p p' : x.toSwitch.P'} (h : p.1 ≠ p'.1) : p ≠ p' := fun e => h (congrArg _ e)

section System

variable {pa pb pg ph : x.toSwitch.P'} (hpa : pa.1 = x.a) (hpb : pb.1 = x.b) (hpg : pg.1 = x.g')
  (hph : ph.1 = x.h')
include hpa hpb hpg hph

/-- `E₀ ⊆` the displayed system (the chain inequalities with `K = {a}`, `{b}` and `r = g', h'`). -/
lemma E0_subset {u : x.toSwitch.P' → ℝ} (hu : u ∈ x.E0) :
    0 ≤ u pa ∧ 0 ≤ u pb ∧ max (u pa) (u pb) ≤ min (u pg) (u ph) ∧ u pg ≤ 1 ∧ u ph ≤ 1 := by
  have hB := hu.1
  have paI : pa ∈ x.toSwitch.I' := show pa.1 ∈ _ from hpa ▸ a_mem_I x
  have pbI : pb ∈ x.toSwitch.I' := show pb.1 ∈ _ from hpb ▸ b_mem_I x
  have pgJ : pg ∉ x.toSwitch.I' := show pg.1 ∉ _ from hpg ▸ g'_notMem_I x
  have phJ : ph ∉ x.toSwitch.I' := show ph.1 ∉ _ from hph ▸ h'_notMem_I x
  have lt : ∀ {p r : x.toSwitch.P'}, p.1 < x.q → x.q < r.1 → p < r := fun h1 h2 => h1.trans h2
  have qg : x.q < pg.1 := hpg ▸ x.q_covby_g'.lt
  have qh : x.q < ph.1 := hph ▸ x.q_covby_h'.lt
  have aq : pa.1 < x.q := hpa ▸ x.a_lt_q
  have bq : pb.1 < x.q := hpb ▸ x.b_lt_q
  refine ⟨hB.1 pa paI, hB.1 pb pbI, max_le (le_min ?_ ?_) (le_min ?_ ?_), (hB.2.1 pg pgJ).2,
    (hB.2.1 ph phJ).2⟩
  · exact le_of_single x hB paI pgJ (lt aq qg)
  · exact le_of_single x hB paI phJ (lt aq qh)
  · exact le_of_single x hB pbI pgJ (lt bq qg)
  · exact le_of_single x hB pbI phJ (lt bq qh)

/-- The displayed system `⊆ B`. -/
lemma mem_B_of_system {u : x.toSwitch.P' → ℝ}
    (hz : ∀ p : x.toSwitch.P', p.1 ∈ x.toSwitch.I → p.1 ≠ x.a → p.1 ≠ x.b → u p = 0)
    (ho : ∀ r : x.toSwitch.P', r.1 ∉ x.toSwitch.I → r.1 ≠ x.g' → r.1 ≠ x.h' → u r = 1)
    (ha : 0 ≤ u pa) (hb : 0 ≤ u pb) (hm : max (u pa) (u pb) ≤ min (u pg) (u ph)) (hg : u pg ≤ 1)
    (hh : u ph ≤ 1) : u ∈ x.toSwitch.B := by
  have hM1 : max (u pa) (u pb) ≤ 1 := hm.trans ((min_le_left _ _).trans hg)
  have upper : ∀ r : x.toSwitch.P', r ∉ x.toSwitch.I' → max (u pa) (u pb) ≤ u r ∧ u r ≤ 1 := by
    intro r hr
    by_cases h1 : r.1 = x.g'
    · obtain rfl : r = pg := Subtype.ext (h1.trans hpg.symm)
      exact ⟨hm.trans (min_le_left _ _), hg⟩
    by_cases h2 : r.1 = x.h'
    · obtain rfl : r = ph := Subtype.ext (h2.trans hph.symm)
      exact ⟨hm.trans (min_le_right _ _), hh⟩
    rw [ho r hr h1 h2]
    exact ⟨hM1, le_rfl⟩
  refine ⟨?_, fun r hr => ⟨(le_max_of_le_left ha).trans (upper r hr).1, (upper r hr).2⟩, ?_,
    fun r hr K hKI hK _ => (chainSum_le_max x hpa hpb hz ha hKI hK).trans (upper r hr).1,
    fun K hKI hK => (chainSum_le_max x hpa hpb hz ha hKI hK).trans hM1⟩
  · intro p hp
    by_cases h1 : p.1 = x.a
    · rwa [show p = pa from Subtype.ext (h1.trans hpa.symm)]
    by_cases h2 : p.1 = x.b
    · rwa [show p = pb from Subtype.ext (h2.trans hpb.symm)]
    rw [hz p hp h1 h2]
  · intro r r' hr hr' hle
    rcases hle.eq_or_lt with h | h
    · rw [h]
    have hlt : r.1 < r'.1 := h
    have hq := q_lt_of_notMem x hr
    have h1 : r'.1 ≠ x.g' := fun e => x.q_covby_g'.2 hq (e ▸ hlt)
    have h2 : r'.1 ≠ x.h' := fun e => x.q_covby_h'.2 hq (e ▸ hlt)
    rw [ho r' hr' h1 h2]
    exact (upper r hr).2

/-- Paper Lemma 4.4, third claim: `E₀` is exactly the displayed system. -/
lemma E0_eq : x.E0 = {u | (∀ p : x.toSwitch.P', p.1 ∈ x.toSwitch.I → p.1 ≠ x.a → p.1 ≠ x.b → u p = 0) ∧
    (∀ r : x.toSwitch.P', r.1 ∉ x.toSwitch.I → r.1 ≠ x.g' → r.1 ≠ x.h' → u r = 1) ∧
    0 ≤ u pa ∧ 0 ≤ u pb ∧ max (u pa) (u pb) ≤ min (u pg) (u ph) ∧ u pg ≤ 1 ∧ u ph ≤ 1} := by
  ext u
  constructor
  · intro hu
    exact ⟨hu.2.1, hu.2.2, E0_subset x hpa hpb hpg hph hu⟩
  · rintro ⟨hz, ho, ha, hb, hm, hg, hh⟩
    exact ⟨mem_B_of_system x hpa hpb hpg hph hz ho ha hb hm hg hh, hz, ho⟩

/-- The four coordinates `α, β, γ, η` are distinct. -/
lemma distinct : pa ≠ pb ∧ pa ≠ pg ∧ pa ≠ ph ∧ pb ≠ pg ∧ pb ≠ ph ∧ pg ≠ ph := by
  have hag : ∀ {p r : P}, p ∈ x.toSwitch.I → r ∉ x.toSwitch.I → p ≠ r := fun hp hr e => hr (e ▸ hp)
  exact ⟨ne_of_val_ne x (by rw [hpa, hpb]; exact a_ne_b x),
    ne_of_val_ne x (by rw [hpa, hpg]; exact hag (a_mem_I x) (g'_notMem_I x)),
    ne_of_val_ne x (by rw [hpa, hph]; exact hag (a_mem_I x) (h'_notMem_I x)),
    ne_of_val_ne x (by rw [hpb, hpg]; exact hag (b_mem_I x) (g'_notMem_I x)),
    ne_of_val_ne x (by rw [hpb, hph]; exact hag (b_mem_I x) (h'_notMem_I x)),
    ne_of_val_ne x (by rw [hpg, hph]; exact x.g'_ne_h')⟩

/-- `v0 + δ ∈ E₀` for a perturbation `δ` supported on `α, β, γ, η` that keeps the displayed system. -/
lemma perturb_mem (δ : x.toSwitch.P' → ℝ) (hδ : ∀ p, p ≠ pa → p ≠ pb → p ≠ pg → p ≠ ph → δ p = 0)
    (h1 : 0 ≤ δ pa) (h2 : 0 ≤ δ pb) (h3 : max (δ pa) (δ pb) ≤ min (1 + δ pg) (1 + δ ph)) (h4 : δ pg ≤ 0)
    (h5 : δ ph ≤ 0) : v0 x + δ ∈ x.E0 := by
  have paI : pa.1 ∈ x.toSwitch.I := hpa ▸ a_mem_I x
  have pbI : pb.1 ∈ x.toSwitch.I := hpb ▸ b_mem_I x
  have pgJ : pg.1 ∉ x.toSwitch.I := hpg ▸ g'_notMem_I x
  have phJ : ph.1 ∉ x.toSwitch.I := hph ▸ h'_notMem_I x
  have nI : ∀ {p r : x.toSwitch.P'}, p.1 ∈ x.toSwitch.I → r.1 ∉ x.toSwitch.I → p ≠ r :=
    fun hp hr e => hr (e ▸ hp)
  have nv : ∀ {p r : x.toSwitch.P'} {c : P}, r.1 = c → p.1 ≠ c → p ≠ r :=
    fun hr hp => ne_of_val_ne x (hr ▸ hp)
  rw [E0_eq x hpa hpb hpg hph]
  refine ⟨fun p hp ha hb => ?_, fun r hr hg hh => ?_, ?_⟩
  · rw [Pi.add_apply, hδ p (nv hpa ha) (nv hpb hb) (nI hp pgJ) (nI hp phJ), v0, ite_eq_left hp, add_zero]
  · rw [Pi.add_apply, hδ r (nI paI hr).symm (nI pbI hr).symm (nv hpg hg) (nv hph hh), v0, ite_eq_right hr, add_zero]
  · simp only [Pi.add_apply, v0, ite_eq_left paI, ite_eq_left pbI, ite_eq_right pgJ, ite_eq_right phJ, zero_add]
    exact ⟨h1, h2, h3, by linarith, by linarith⟩

lemma v0_mem : v0 x ∈ x.E0 := by
  simpa using perturb_mem x hpa hpb hpg hph 0 (fun _ _ _ _ _ => rfl) le_rfl le_rfl (by simp) le_rfl le_rfl

/-- `E₀` lies in the affine subspace `ζ = ζ₀`, so its directions vanish off `α, β, γ, η`. -/
lemma vectorSpan_le : vectorSpan ℝ x.E0 ≤ offFour pa pb pg ph := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro _ ⟨u, hu, v, hv, rfl⟩ p h1 h2 h3 h4
  have na : p.1 ≠ x.a := fun e => h1 (Subtype.ext (e.trans hpa.symm))
  have nb : p.1 ≠ x.b := fun e => h2 (Subtype.ext (e.trans hpb.symm))
  have ng : p.1 ≠ x.g' := fun e => h3 (Subtype.ext (e.trans hpg.symm))
  have nh : p.1 ≠ x.h' := fun e => h4 (Subtype.ext (e.trans hph.symm))
  show u p - v p = 0
  by_cases hp : p.1 ∈ x.toSwitch.I
  · rw [hu.2.1 p hp na nb, hv.2.1 p hp na nb, sub_self]
  · rw [hu.2.2 p hp ng nh, hv.2.2 p hp ng nh, sub_self]

/-- Paper Lemma 4.4, dimension part. -/
lemma E0_adim : adim x.E0 = 4 := by
  classical
  obtain ⟨hab, hag, hah, hbg, hbh, hgh⟩ := distinct x hpa hpb hpg hph
  let g : Fin 4 → x.toSwitch.P' := ![pa, pb, pg, ph]
  have hg : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [g, eq_comm]
  unfold adim
  apply le_antisymm
  · -- upper bound: reading off `(α, β, γ, η)` is injective on directions
    let π : (x.toSwitch.P' → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) := LinearMap.pi fun i => LinearMap.proj (g i)
    have hinj : Function.Injective (π ∘ₗ (vectorSpan ℝ x.E0).subtype) := by
      refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
      have hz : ∀ i, v.1 (g i) = 0 := fun i => by simpa [π] using congrFun hv i
      refine Subtype.ext (funext fun p => ?_)
      show v.1 p = 0
      by_cases h1 : p = pa; · simpa [g, h1] using hz 0
      by_cases h2 : p = pb; · simpa [g, h2] using hz 1
      by_cases h3 : p = pg; · simpa [g, h3] using hz 2
      by_cases h4 : p = ph; · simpa [g, h4] using hz 3
      exact vectorSpan_le x hpa hpb hpg hph v.2 p h1 h2 h3 h4
    simpa using LinearMap.finrank_le_finrank_of_injective hinj
  · -- lower bound: the five points `v0`, `v0 + e_a`, `v0 + e_b`, `v0 - e_g'`, `v0 - e_h'` of `E₀`
    have h0 := v0_mem x hpa hpb hpg hph
    have mem := perturb_mem x hpa hpb hpg hph
    have ea : Pi.single pa (1 : ℝ) ∈ vectorSpan ℝ x.E0 := by
      have h := mem (Pi.single pa 1) (fun p hp _ _ _ => by simp [hp])
        (by simp) (by simp [hab.symm]) (by simp [hab.symm, hag.symm, hah.symm])
        (by simp [hag.symm]) (by simp [hah.symm])
      simpa using vsub_mem_vectorSpan ℝ h h0
    have eb : Pi.single pb (1 : ℝ) ∈ vectorSpan ℝ x.E0 := by
      have h := mem (Pi.single pb 1) (fun p _ hp _ _ => by simp [hp])
        (by simp [hab]) (by simp) (by simp [hab, hbg.symm, hbh.symm])
        (by simp [hbg.symm]) (by simp [hbh.symm])
      simpa using vsub_mem_vectorSpan ℝ h h0
    have eg : Pi.single pg (1 : ℝ) ∈ vectorSpan ℝ x.E0 := by
      have h := mem (-Pi.single pg 1) (fun p _ _ hp _ => by simp [hp])
        (by simp [hag]) (by simp [hbg]) (by simp [hag, hbg, hgh.symm])
        (by simp) (by simp [hgh.symm])
      simpa using vsub_mem_vectorSpan ℝ h0 h
    have eh : Pi.single ph (1 : ℝ) ∈ vectorSpan ℝ x.E0 := by
      have h := mem (-Pi.single ph 1) (fun p _ _ _ hp => by simp [hp])
        (by simp [hah]) (by simp [hbh]) (by simp [hah, hbh, hgh])
        (by simp [hgh]) (by simp)
      simpa using vsub_mem_vectorSpan ℝ h0 h
    let fam : Fin 4 → x.toSwitch.P' → ℝ := fun i => Pi.single (g i) 1
    have hli : LinearIndependent ℝ fam := by
      simpa [Function.comp_def, fam] using (Pi.basisFun ℝ x.toSwitch.P').linearIndependent.comp g hg
    have hspan : Submodule.span ℝ (Set.range fam) ≤ vectorSpan ℝ x.E0 := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      exacts [ea, eb, eg, eh]
    simpa [finrank_span_eq_card hli] using Submodule.finrank_mono hspan

end System

end Lemma44

/-- **Lemma 4.4** (paper lines 512–530): `E₀` is a face of `B` of dimension 4, cut out by the displayed system. -/
theorem lemma_4_4_proved {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P)
    (pa pb pg ph : x.toSwitch.P') (hpa : pa.1 = x.a) (hpb : pb.1 = x.b) (hpg : pg.1 = x.g')
    (hph : ph.1 = x.h') :
    IsFace x.toSwitch.B x.E0 ∧ adim x.E0 = 4 ∧
    x.E0 = {u | (∀ p : x.toSwitch.P', p.1 ∈ x.toSwitch.I → p.1 ≠ x.a → p.1 ≠ x.b → u p = 0) ∧
               (∀ r : x.toSwitch.P', r.1 ∉ x.toSwitch.I → r.1 ≠ x.g' → r.1 ≠ x.h' → u r = 1) ∧
               0 ≤ u pa ∧ 0 ≤ u pb ∧ max (u pa) (u pb) ≤ min (u pg) (u ph) ∧ u pg ≤ 1 ∧ u ph ≤ 1} :=
  ⟨⟨⟨_, Lemma44.v0_mem x hpa hpb hpg hph⟩, Lemma44.E0_isExposed x⟩, Lemma44.E0_adim x hpa hpb hpg hph,
    Lemma44.E0_eq x hpa hpb hpg hph⟩

end HibiLi.Proofs
