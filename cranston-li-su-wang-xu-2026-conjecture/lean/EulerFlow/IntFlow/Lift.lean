/-
EulerFlow/IntFlow/Lift.lean — paper 002, Section 8 (tex l.566-633): flows and boundaries, residues of `k`-flows,
the representatives `r_f`, integer lifts (Lemma 8.3, by rounding `r_f / k`), connected fibres (Lemma 8.4, a
`{-1,0,1}` circulation times `k`), and the `ℤ₂` facts of Remark 8.8.
Helpers live in namespace `EulerFlow.Sec8` (no clash with Section 3 names).
-/
import EulerFlow.IntFlow.Rounding
import EulerFlow.Graph.MultiStep

namespace EulerFlow

namespace Sec8

open Finset MGraph

variable {V E : Type} {G : MGraph V E} [Fintype E] [DecidableEq E] [DecidableEq V]

omit [DecidableEq E] in
/-- The flow condition is "boundary zero" (tex l.571-572). -/
theorem isFlow_iff_boundary_zero {M : Type} [AddCommGroup M] (x : E → M) :
    G.IsFlow x ↔ G.boundary x = 0 := by
  constructor
  · intro h; funext v; simp [boundary, h v]
  · intro h v; have := congr_fun h v; simp only [boundary, Pi.zero_apply, sub_eq_zero] at this
    exact this.symm

omit [DecidableEq E] in
/-- The boundary of the real cast of an integer map. -/
lemma boundary_intCast (y : E → ℤ) (v : V) :
    G.boundary (fun e => (y e : ℝ)) v = ((G.boundary y v : ℤ) : ℝ) := by
  simp [boundary]

omit [DecidableEq E] in
/-- The boundary is linear: `∂(a - k b) = ∂a - k ∂b`. -/
lemma boundary_sub_mul (a b : E → ℤ) (k : ℤ) (v : V) :
    G.boundary (fun e => a e - k * b e) v = G.boundary a v - k * G.boundary b v := by
  simp only [boundary, Finset.sum_sub_distrib, ← Finset.mul_sum]; ring

omit [DecidableEq E] in
/-- A circulation multiplied by a nonzero integer: if `k h` is a flow, so is `h`. -/
lemma isFlow_of_mul (h : E → ℤ) (k : ℤ) (hk : k ≠ 0) (hf : G.IsFlow (fun e => k * h e)) : G.IsFlow h := by
  intro v
  have := hf v
  simp only [← Finset.mul_sum] at this
  exact mul_left_cancel₀ hk this

/-! ### Residues and representatives -/

omit [DecidableEq E] in
/-- `sec8_residues` (tex l.579-580): the residues of a `k`-flow are a nowhere-zero `ℤ_k`-flow. -/
theorem sec8_residues_proved [Fintype V] (k : ℕ) (hk : 2 ≤ k) (G : MGraph V E) (F : E → ℤ)
    (hF : G.IsIFlow (Ik k) F) : G.IsNZFlow (fun e => ((F e : ℤ) : ZMod k)) := by
  have : NeZero k := ⟨by omega⟩
  refine ⟨fun v => ?_, fun e => ?_⟩
  · have := hF.1 v
    simp only [← Int.cast_sum, this]
  · intro h0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    obtain ⟨c, hc⟩ := h0
    have hv := (hF.2 e)
    simp only [Ik, Set.mem_ofPred_eq] at hv
    rw [hc] at hv
    have hc0 : c ≠ 0 := by rintro rfl; simp at hv
    have : (k : ℤ) ≤ |(k : ℤ) * c| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ k)]
      exact le_mul_of_one_le_right (by positivity) (Int.one_le_abs hc0)
    omega

/-- The representative `r_f(e) ∈ {1, …, k-1}` of a nonzero residue. -/
lemma val_bounds {k : ℕ} (hk : 2 ≤ k) {a : ZMod k} (ha : a ≠ 0) : 1 ≤ a.val ∧ a.val ≤ k - 1 := by
  have : NeZero k := ⟨by omega⟩
  have h1 : a.val ≠ 0 := by rwa [ne_eq, ZMod.val_eq_zero]
  have h2 := ZMod.val_lt a
  omega

/-- `((a.val : ℤ) : ZMod k) = a`. -/
lemma intCast_val {k : ℕ} (hk : 2 ≤ k) (a : ZMod k) : (((a.val : ℕ) : ℤ) : ZMod k) = a := by
  have : NeZero k := ⟨by omega⟩
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- An integer in `Ik k` with residue `a` is `r` or `r - k`. -/
lemma eq_val_or_val_sub {k : ℕ} (hk : 2 ≤ k) {a : ZMod k} (ha : a ≠ 0) {y : ℤ} (hy : y ∈ Ik k)
    (hres : ((y : ℤ) : ZMod k) = a) : y = a.val ∨ y = (a.val : ℤ) - k := by
  have : NeZero k := ⟨by omega⟩
  have hb := val_bounds hk ha
  rw [← intCast_val hk a, ZMod.intCast_eq_intCast_iff_dvd_sub] at hres
  obtain ⟨c, hc⟩ := hres
  simp only [Ik, Set.mem_ofPred_eq] at hy
  have h1 : (1 : ℤ) ≤ (a.val : ℤ) := by exact_mod_cast hb.1
  have h2 : (a.val : ℤ) ≤ (k : ℤ) - 1 := by have := hb.2; omega
  have hk0 : (0 : ℤ) ≤ k := by positivity
  have hyb : -((k : ℤ) - 1) ≤ y ∧ y ≤ (k : ℤ) - 1 := abs_le.1 hy.2
  have hc1 : c < 2 := by
    by_contra h; push Not at h; nlinarith
  have hc2 : -1 < c := by
    by_contra h; push Not at h; nlinarith
  have : c = 0 ∨ c = 1 := by omega
  rcases this with rfl | rfl
  · left; linarith
  · right; linarith

omit [DecidableEq E] in
/-- `sec8_rf` (tex l.608-610): `∂ r_f ≡ 0 (mod k)`, and a lift takes the value `r_f(e)` or `r_f(e) - k`. -/
theorem sec8_rf_proved [Fintype V] (k : ℕ) (hk : 2 ≤ k) (G : MGraph V E) (f : E → ZMod k) (hf : G.IsNZFlow f) :
    (∀ v, (k : ℤ) ∣ G.boundary (fun e => ((f e).val : ℤ)) v) ∧
    ∀ F, G.IsIntLift k f F → ∀ e, F e = (f e).val ∨ F e = (f e).val - k := by
  have : NeZero k := ⟨by omega⟩
  refine ⟨fun v => ?_, fun F hF e => eq_val_or_val_sub hk (hf.2 e) (hF.1.2 e) (hF.2 e)⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [boundary, Int.cast_sub, Int.cast_sum, intCast_val hk]
  rw [hf.1 v, sub_self]

/-! ### Lemma 8.3: integer lifts exist -/

omit [DecidableEq E] in
/-- The integer lift `r_f - k z` from a `{0,1}` map `z` with `k ∂z = ∂r_f` is an integer lift (tex l.616-618). -/
lemma isIntLift_of_round {k : ℕ} (hk : 2 ≤ k) (f : E → ZMod k) (hf : G.IsNZFlow f) (z : E → ℤ)
    (hz : ∀ e, z e = 0 ∨ z e = 1)
    (hb : ∀ v, (k : ℤ) * G.boundary z v = G.boundary (fun e => ((f e).val : ℤ)) v) :
    G.IsIntLift k f (fun e => ((f e).val : ℤ) - k * z e) := by
  have : NeZero k := ⟨by omega⟩
  refine ⟨⟨?_, fun e => ?_⟩, fun e => ?_⟩
  · rw [isFlow_iff_boundary_zero]
    funext v
    rw [boundary_sub_mul, ← hb v, sub_self, Pi.zero_apply]
  · have hb := val_bounds hk (hf.2 e)
    simp only [Ik, Set.mem_ofPred_eq]
    rcases hz e with h | h <;> rw [h]
    · rw [mul_zero, sub_zero, abs_of_pos (by omega)]; omega
    · rw [mul_one, abs_of_neg (by omega)]; omega
  · simp

/-- `lem_8_3` (Lemma 8.3, tex l.612-619): every `ℤ_k`-flow has an integer lift (`k ≥ 2`). -/
theorem lem_8_3_proved [Fintype V] (k : ℕ) (hk : 2 ≤ k) (G : MGraph V E) (f : E → ZMod k) (hf : G.IsNZFlow f) :
    ∃ F : E → ℤ, G.IsIntLift k f F := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  set r : E → ℤ := fun e => ((f e).val : ℤ) with hr
  set x : E → ℝ := fun e => (r e : ℝ) / k with hx
  have hx01 : ∀ e, 0 ≤ x e ∧ x e ≤ 1 := by
    intro e
    have hb := val_bounds hk (hf.2 e)
    have h1 : (0 : ℝ) ≤ r e := by simp [hr]
    have h2 : (r e : ℝ) ≤ k := by simp only [hr]; exact_mod_cast (by omega : (f e).val ≤ k)
    exact ⟨div_nonneg h1 hkpos.le, (div_le_one hkpos).2 h2⟩
  have hbx : ∀ v, G.boundary x v = ((G.boundary r v : ℤ) : ℝ) / k := by
    intro v
    rw [← boundary_intCast]
    simp only [hx, boundary, ← Finset.sum_div, sub_div]
  have hint : ∀ v, ∃ n : ℤ, G.boundary x v = n := by
    intro v
    obtain ⟨c, hc⟩ := (sec8_rf_proved (V := V) k hk G f hf).1 v
    refine ⟨c, ?_⟩
    rw [hbx, show G.boundary r v = G.boundary (fun e => ((f e).val : ℤ)) v from rfl, hc]
    push_cast
    field_simp
  obtain ⟨z, hz01, hzb, _⟩ := rounding x hx01 hint
  refine ⟨_, isIntLift_of_round hk f hf z hz01 (fun v => ?_)⟩
  have := congr_fun hzb v
  rw [boundary_intCast, hbx] at this
  have h' : (((k : ℤ) * G.boundary z v : ℤ) : ℝ) = ((G.boundary r v : ℤ) : ℝ) := by
    push_cast; rw [this]; field_simp
  exact_mod_cast h'

/-! ### Lemma 8.4: the fibres are connected -/

omit [DecidableEq E] in
/-- A lift determines its residues: `f` is the residue map of `F`, hence a nowhere-zero `ℤ_k`-flow. -/
lemma isNZFlow_of_lift [Fintype V] {k : ℕ} (hk : 2 ≤ k) {f : E → ZMod k} {F : E → ℤ} (hF : G.IsIntLift k f F) :
    G.IsNZFlow f := by
  have : f = fun e => ((F e : ℤ) : ZMod k) := by funext e; exact (hF.2 e).symm
  rw [this]
  exact sec8_residues_proved k hk G F hF.1

/-- `lem_8_4` (Lemma 8.4, tex l.621-633): any two integer lifts of `f` are joined in `𝓕(G, k)`; the difference
`(F' - F)/k` is a `{-1,0,1}`-valued integer flow, and its cycle decomposition gives steps with the value `k`. -/
theorem lem_8_4_proved [Fintype V] (k : ℕ) (hk : 2 ≤ k) (G : MGraph V E) (f : E → ZMod k) (F F' : E → ℤ)
    (hF : G.IsIntLift k f F) (hF' : G.IsIntLift k f F') :
    (G.kFlowGraph k).Reachable ⟨F, hF.1⟩ ⟨F', hF'.1⟩ := by
  have hf := isNZFlow_of_lift hk hF
  have hkz : (k : ℤ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  set h : E → ℤ := fun e => if F' e = F e then 0 else if F' e = F e + k then 1 else -1 with hh
  have hFF : ∀ e, F' e = F e + h e * k := by
    intro e
    have h1 := (sec8_rf_proved k hk G f hf).2 F hF e
    have h2 := (sec8_rf_proved k hk G f hf).2 F' hF' e
    simp only [hh]
    split_ifs with ha hb <;> omega
  have hval : ∀ e, h e = -1 ∨ h e = 0 ∨ h e = 1 := by
    intro e; simp only [hh]; split_ifs <;> simp
  have hcirc : G.IsFlow h := by
    apply isFlow_of_mul h k hkz
    have : (fun e => (k : ℤ) * h e) = fun e => F' e - F e := by
      funext e; rw [hFF e]; ring
    rw [this]
    exact IsFlow.sub hF'.1.1 hF.1.1
  obtain ⟨w, _⟩ := walk_of_circ (I := Ik k) ⟨F, hF.1⟩ ⟨F', hF'.1⟩ h hval hcirc (k : ℤ) hkz
    (by funext e; simp [hFF e])
  exact ⟨w.mapLe (stepGraph_mono (Ik k) (Set.singleton_subset_iff.2 hkz))⟩

/-! ### Small claims -/

omit [DecidableEq E] in
/-- `sec8_flow_iff_boundary` (tex l.571-572). -/
theorem sec8_flow_iff_boundary_proved [Fintype V] {M : Type} [AddCommGroup M] (G : MGraph V E) (x : E → M) :
    G.IsFlow x ↔ G.boundary x = 0 :=
  isFlow_iff_boundary_zero x

/-- `sec8_chi_flow` (tex l.572: `∂χ_Q = 0`). -/
theorem sec8_chi_flow_proved [Fintype V] (G : MGraph V E) (Q : G.DirCycle) : G.IsFlow Q.chi :=
  Q.isFlow_chi

omit [DecidableEq E] in
/-- `rem_8_8_Z2` (tex l.694-695): a graph has at most one `ℤ₂`-flow, and every `2`-flow is an integer lift of it. -/
theorem rem_8_8_Z2_proved [Fintype V] (G : MGraph V E) :
    (∀ f f' : E → ZMod 2, G.IsNZFlow f → G.IsNZFlow f' → f = f') ∧
    ∀ f : E → ZMod 2, G.IsNZFlow f → ∀ F, G.IsIFlow (Ik 2) F → G.IsIntLift 2 f F := by
  have h1 : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  refine ⟨fun f f' hf hf' => funext fun e => by rw [h1 _ (hf.2 e), h1 _ (hf'.2 e)], fun f hf F hF => ⟨hF, fun e => ?_⟩⟩
  rw [h1 _ (hf.2 e)]
  have hv := hF.2 e
  simp only [Ik, Set.mem_ofPred_eq] at hv
  have : F e = 1 ∨ F e = -1 := by
    rcases abs_cases (F e) with ⟨h, _⟩ | ⟨h, _⟩ <;> push_cast at hv <;> omega
  rcases this with h | h <;> rw [h] <;> decide

end Sec8

end EulerFlow
