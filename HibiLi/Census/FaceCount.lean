/-
HibiLi/Census/FaceCount.lean — face numbers of a 0/1 polytope from a kernel-checked family of closed vertex sets.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Encoding. Ambient `Fin d → ℝ`; integer rows (`Row d`, ClosedFaces.lean). A vertex is a 0/1 point, given by its support
`m : ℕ` (bit `j` = coordinate `j`). `vs : List ℕ` lists the vertex supports; position `k` of `vs` is vertex `k`.
A set of vertices is a bitmask over POSITIONS (bit `k` = vertex `k`). `fam : List (ℕ × ℕ)` lists pairs
(vertex-set mask, dimension). `censusCheck` checks, by computation only:
 (1) `vs` = exactly the supports `m < 2^d` of the 0/1 points satisfying every row, without repetition (every entry
     of `vs` is `< 2^d`: a larger entry could encode a point outside the polytope and fake faces);
 (2) every mask in `fam` is nonzero, `< 2^nv`, and closed (its closure under the row tight-masks is itself);
 (3) the full mask is in `fam` with dimension `d`; the masks are distinct;
 (4) `fam` is closed under nonempty intersection with every row tight-mask (bitset membership test);
 (5) every entry of dimension `e > 0` strictly contains an entry of dimension `e − 1`, and every entry other than the
     full mask is strictly contained in an entry of dimension `e + 1`.
Soundness (`fNum_eq_of_check`): then `fam` lists every face exactly once, with its dimension.
-/
import HibiLi.Census.ClosedFaces
import HibiLi.Example21.ZeroOne

namespace HibiLi.Census

variable {d : ℕ}

/-- The 0/1 point with support `m`: coordinate `j` is `1` iff bit `j` of `m` is set. -/
noncomputable def ind (d m : ℕ) : Fin d → ℝ := fun j => if m.testBit j then 1 else 0

/-- The value of a row's form at the 0/1 point with support `m`, in `ℤ`. -/
def rowAt (row : Row d) (m : ℕ) : ℤ := ∑ j : Fin d, if m.testBit j then row.1 j else 0

theorem rowForm_ind (row : Row d) (m : ℕ) : rowForm row (ind d m) = (rowAt row m : ℝ) := by
  rw [rowForm_apply, rowAt, Int.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ind]
  split_ifs <;> simp

/-- Check (1): `vs` lists, without repetition, exactly the supports of the 0/1 points of `polyOf rows`. -/
def vsOK (rows : List (Row d)) (vs : List ℕ) : Bool :=
  decide vs.Nodup && vs.all (fun m => decide (m < 2 ^ d)) && (List.range (2 ^ d)).all fun m =>
    (rows.all fun row => decide (rowAt row m ≤ row.2)) == vs.contains m

/-- Bitmask over positions: bit `k` is set iff `pred (ms[k])` (positions counted from `k₀`). -/
def maskAux (pred : ℕ → Bool) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | m :: ms, k₀ => (if pred m then 1 <<< k₀ else 0) ||| maskAux pred ms (k₀ + 1)

/-- The positions of the vertices that are tight on `row`. -/
def tightMask (vs : List ℕ) (row : Row d) : ℕ := maskAux (fun m => rowAt row m == row.2) vs 0

/-- The closure of the vertex set `S`: the vertices on every tight-mask that contains `S` (`full` = all vertices). -/
def closureOf (tights : List ℕ) (full S : ℕ) : ℕ :=
  tights.foldl (fun acc t => if S &&& t == S then acc &&& t else acc) full

/-- The family as a bitset: bit `S` is set iff `S` is a mask in `fam`. -/
def famBits (fam : List (ℕ × ℕ)) : ℕ := fam.foldl (fun acc p => acc ||| (1 <<< p.1)) 0

/-- Checks (2)-(5) (see the file header). -/
def checkFam (nv : ℕ) (tights : List ℕ) (fam : List (ℕ × ℕ)) (D : ℕ) : Bool :=
  decide (fam.map Prod.fst).Nodup &&
  fam.all (fun p => p.1 != 0 && decide (p.1 < 2 ^ nv) && closureOf tights (2 ^ nv - 1) p.1 == p.1) &&
  fam.contains (2 ^ nv - 1, D) &&
  fam.all (fun p => tights.all (fun t => (p.1 &&& t == 0) || (famBits fam).testBit (p.1 &&& t))) &&
  fam.all (fun p => p.2 == 0 || fam.any (fun q => q.1 &&& p.1 == q.1 && q.1 != p.1 && q.2 + 1 == p.2)) &&
  fam.all (fun p => p.1 == 2 ^ nv - 1 || fam.any (fun q => p.1 &&& q.1 == p.1 && q.1 != p.1 && q.2 == p.2 + 1))

/-- All checks (1)-(5). -/
def censusCheck (d : ℕ) (rows : List (Row d)) (vs : List ℕ) (fam : List (ℕ × ℕ)) : Bool :=
  vsOK rows vs && checkFam vs.length (rows.map (tightMask vs)) fam d

/-! ### Bits of the masks -/

theorem testBit_one_shiftLeft (k j : ℕ) : (1 <<< k).testBit j = decide (k = j) := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]

theorem testBit_maskAux_lt (pred : ℕ → Bool) (ms : List ℕ) {k₀ j : ℕ} (hj : j < k₀) :
    (maskAux pred ms k₀).testBit j = false := by
  induction ms generalizing k₀ with
  | nil => simp [maskAux]
  | cons m ms ih =>
    simp only [maskAux, Nat.testBit_or, ih (by omega : j < k₀ + 1), Bool.or_false]
    split_ifs
    · rw [testBit_one_shiftLeft]; simp; omega
    · simp

theorem testBit_maskAux (pred : ℕ → Bool) (ms : List ℕ) (k₀ i : ℕ) :
    (maskAux pred ms k₀).testBit (k₀ + i) = if h : i < ms.length then pred ms[i] else false := by
  induction ms generalizing k₀ i with
  | nil => simp [maskAux]
  | cons m ms ih =>
    simp only [maskAux, Nat.testBit_or]
    cases i with
    | zero =>
      rw [testBit_maskAux_lt pred ms (by omega : k₀ + 0 < k₀ + 1), Bool.or_false]
      simp only [List.length_cons, Nat.zero_lt_succ, ↓reduceDIte, List.getElem_cons_zero]
      cases hm : pred m <;> simp
    | succ i =>
      rw [show k₀ + (i + 1) = (k₀ + 1) + i by omega, ih]
      have : (if pred m then 1 <<< k₀ else 0).testBit (k₀ + 1 + i) = false := by
        split_ifs
        · rw [testBit_one_shiftLeft, decide_eq_false_iff_not]; omega
        · simp
      rw [this, Bool.false_or]
      simp

theorem testBit_famBits_aux (fam : List (ℕ × ℕ)) (acc n : ℕ) :
    (fam.foldl (fun acc p => acc ||| (1 <<< p.1)) acc).testBit n = true ↔
      acc.testBit n = true ∨ ∃ p ∈ fam, p.1 = n := by
  induction fam generalizing acc with
  | nil => simp
  | cons q fam ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, testBit_one_shiftLeft]
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons, exists_eq_or_imp]
    tauto

theorem testBit_famBits (fam : List (ℕ × ℕ)) (n : ℕ) :
    (famBits fam).testBit n = true ↔ ∃ p ∈ fam, p.1 = n := by
  rw [famBits, testBit_famBits_aux]
  simp

theorem testBit_closureOf (tights : List ℕ) (acc S k : ℕ) :
    (tights.foldl (fun acc t => if S &&& t == S then acc &&& t else acc) acc).testBit k = true ↔
      acc.testBit k = true ∧ ∀ t ∈ tights, S &&& t = S → t.testBit k = true := by
  induction tights generalizing acc with
  | nil => simp
  | cons t ts ih =>
    rw [List.foldl_cons, ih]
    by_cases h : S &&& t = S
    · simp only [h, beq_self_eq_true, ↓reduceIte, Nat.testBit_and, Bool.and_eq_true, List.mem_cons,
        forall_eq_or_imp, forall_const]
      tauto
    · simp only [h, beq_iff_eq, ↓reduceIte, List.mem_cons, forall_eq_or_imp, false_implies, true_and]

theorem and_eq_self_iff (S t : ℕ) : S &&& t = S ↔ ∀ i, S.testBit i = true → t.testBit i = true := by
  constructor
  · intro h i hi
    have := congrArg (fun n => n.testBit i) h
    simp only [Nat.testBit_and, hi, Bool.true_and] at this
    exact this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hS : S.testBit i
    · simp
    · simp [h i hS]

/-- The positions `k < nv` whose bit is set in the mask `M`. -/
def bitsOf (nv M : ℕ) : Finset (Fin nv) := Finset.univ.filter fun k => M.testBit k = true

theorem mem_bitsOf {nv M : ℕ} {k : Fin nv} : k ∈ bitsOf nv M ↔ M.testBit k = true := by
  simp [bitsOf]

theorem testBit_of_lt {nv M i : ℕ} (hM : M < 2 ^ nv) (hi : nv ≤ i) : M.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hM (Nat.pow_le_pow_right (by norm_num) hi))

theorem eq_of_bitsOf_eq {nv M N : ℕ} (hM : M < 2 ^ nv) (hN : N < 2 ^ nv) (h : bitsOf nv M = bitsOf nv N) :
    M = N := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < nv
  · have := congrArg (fun s => (⟨i, hi⟩ : Fin nv) ∈ s) h
    simp only [mem_bitsOf, eq_iff_iff] at this
    cases hm : M.testBit i <;> cases hn : N.testBit i <;> simp_all
  · rw [testBit_of_lt hM (by omega), testBit_of_lt hN (by omega)]

theorem bitsOf_nonempty {nv M : ℕ} (hM : M < 2 ^ nv) (h0 : M ≠ 0) : (bitsOf nv M).Nonempty := by
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h0
  have hlt : i < nv := by
    by_contra hge
    rw [testBit_of_lt hM (by omega)] at hi
    exact Bool.false_ne_true hi
  exact ⟨⟨i, hlt⟩, mem_bitsOf.2 hi⟩

theorem and_eq_self_iff_bitsOf {nv M t : ℕ} (hM : M < 2 ^ nv) : M &&& t = M ↔ bitsOf nv M ⊆ bitsOf nv t := by
  rw [and_eq_self_iff]
  constructor
  · intro h k hk
    exact mem_bitsOf.2 (h k (mem_bitsOf.1 hk))
  · intro h i hi
    by_cases hlt : i < nv
    · exact mem_bitsOf.1 (h ((mem_bitsOf (k := ⟨i, hlt⟩)).2 hi))
    · rw [testBit_of_lt hM (by omega)] at hi
      exact absurd hi Bool.false_ne_true

theorem bitsOf_full (nv : ℕ) : bitsOf nv (2 ^ nv - 1) = Finset.univ := by
  ext k
  simp [mem_bitsOf, Nat.testBit_two_pow_sub_one]

/-! ### The 0/1 points -/

theorem ind_mem_zeroOne (m : ℕ) : ind d m ∈ zeroOneVectors (Fin d) := fun j => by
  unfold ind
  split_ifs <;> simp

theorem exists_ind_eq {x : Fin d → ℝ} (hx : x ∈ zeroOneVectors (Fin d)) : ∃ m < 2 ^ d, ind d m = x := by
  classical
  let f : Fin d → Fin 2 := fun j => if x j = 1 then 1 else 0
  refine ⟨finFunctionFinEquiv f, (finFunctionFinEquiv f).isLt, ?_⟩
  funext j
  have hval : (finFunctionFinEquiv f : ℕ) / 2 ^ (j : ℕ) % 2 = f j := by
    rw [← finFunctionFinEquiv_symm_apply_val, Equiv.symm_apply_apply]
  simp only [ind, Nat.testBit_eq_decide_div_mod_eq, hval]
  rcases hx j with h | h <;> simp [f, h]

theorem ind_mem_polyOf_iff (rows : List (Row d)) (m : ℕ) :
    ind d m ∈ polyOf rows ↔ (rows.all fun row => decide (rowAt row m ≤ row.2)) = true := by
  simp only [polyOf, Set.mem_ofPred_eq, rowForm_ind, Int.cast_le, List.all_eq_true, decide_eq_true_eq]

/-! ### The setting of `fNum_eq_of_check` -/

section Setting

variable (rows : List (Row d)) (vs : List ℕ)

/-- The vertex at position `k`. -/
noncomputable def vpt : Fin vs.length → Fin d → ℝ := fun k => ind d (vs.get k)

theorem range_vpt (hv : vsOK rows vs = true) :
    Set.range (vpt vs) = polyOf rows ∩ zeroOneVectors (Fin d) := by
  simp only [vsOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq] at hv
  obtain ⟨⟨-, hlt⟩, hrow⟩ := hv
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨(ind_mem_polyOf_iff rows _).2 ?_, ind_mem_zeroOne _⟩
    rw [hrow _ (hlt _ (List.get_mem vs k))]
    exact List.contains_iff_mem.2 (List.get_mem vs k)
  · rintro ⟨hxQ, hx01⟩
    obtain ⟨m, hm, rfl⟩ := exists_ind_eq hx01
    have hmem : m ∈ vs := by
      rw [← List.contains_iff_mem, ← hrow m hm]
      exact (ind_mem_polyOf_iff rows m).1 hxQ
    obtain ⟨k, hk⟩ := List.mem_iff_get.1 hmem
    exact ⟨k, by simp only [vpt, hk]⟩

theorem hull_vpt (hv : vsOK rows vs = true)
    (hhull : polyOf rows = convexHull ℝ (polyOf rows ∩ zeroOneVectors (Fin d))) :
    polyOf rows = convexHull ℝ (Set.range (vpt vs)) := by
  rw [range_vpt rows vs hv]
  exact hhull

theorem tight_vpt_iff (row : Row d) (k : Fin vs.length) :
    Tight (vpt vs) row k ↔ (tightMask vs row).testBit k = true := by
  have h := testBit_maskAux (fun m => rowAt row m == row.2) vs 0 k
  rw [zero_add] at h
  rw [tightMask, h, Tight, vpt, rowForm_ind]
  simp [k.isLt]

end Setting

/-! ### What `checkFam` says -/

theorem checkFam_facts {nv : ℕ} {tights : List ℕ} {fam : List (ℕ × ℕ)} {D : ℕ}
    (h : checkFam nv tights fam D = true) :
    (fam.map Prod.fst).Nodup ∧
    (∀ p ∈ fam, p.1 ≠ 0 ∧ p.1 < 2 ^ nv ∧ closureOf tights (2 ^ nv - 1) p.1 = p.1) ∧
    (2 ^ nv - 1, D) ∈ fam ∧
    (∀ p ∈ fam, ∀ t ∈ tights, p.1 &&& t = 0 ∨ (famBits fam).testBit (p.1 &&& t) = true) ∧
    (∀ p ∈ fam, p.2 = 0 ∨ ∃ q ∈ fam, q.1 &&& p.1 = q.1 ∧ q.1 ≠ p.1 ∧ q.2 + 1 = p.2) ∧
    (∀ p ∈ fam, p.1 = 2 ^ nv - 1 ∨ ∃ q ∈ fam, p.1 &&& q.1 = p.1 ∧ q.1 ≠ p.1 ∧ q.2 = p.2 + 1) := by
  simpa only [checkFam, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq, List.contains_iff_mem, and_assoc] using h

/-! ### Entries are faces, every face is an entry, labels are dimensions -/

section Main

variable {rows : List (Row d)} {vs : List ℕ} {fam : List (ℕ × ℕ)}

theorem closed_of_mem {M : ℕ} (hM : M < 2 ^ vs.length)
    (hcl : closureOf (rows.map (tightMask vs)) (2 ^ vs.length - 1) M = M) :
    IsClosedSet rows (vpt vs) (bitsOf vs.length M) := by
  intro k hk
  rw [mem_bitsOf, ← hcl, closureOf, testBit_closureOf]
  refine ⟨by simp [Nat.testBit_two_pow_sub_one], fun t ht hMt => ?_⟩
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.1 ht
  rw [and_eq_self_iff_bitsOf hM] at hMt
  exact (tight_vpt_iff vs row k).1
    (hk row hrow fun s hs => (tight_vpt_iff vs row s).2 (mem_bitsOf.1 (hMt hs)))

theorem bitsOf_and (nv M t : ℕ) : bitsOf nv (M &&& t) = bitsOf nv M ∩ bitsOf nv t := by
  ext k
  simp [mem_bitsOf, Nat.testBit_and]

theorem exists_mem_of_closed {D : ℕ} (h3 : (2 ^ vs.length - 1, D) ∈ fam)
    (h4 : ∀ p ∈ fam, ∀ t ∈ rows.map (tightMask vs), p.1 &&& t = 0 ∨ (famBits fam).testBit (p.1 &&& t) = true)
    {S : Finset (Fin vs.length)} (hS : IsClosedSet rows (vpt vs) S) (hne : S.Nonempty) :
    ∃ p ∈ fam, bitsOf vs.length p.1 = S := by
  -- intersect, starting from the full set, with every tight set that contains `S`
  have key : ∀ ts : List ℕ, (∀ t ∈ ts, t ∈ rows.map (tightMask vs)) → ∀ p ∈ fam, S ⊆ bitsOf vs.length p.1 →
      ∃ q ∈ fam, S ⊆ bitsOf vs.length q.1 ∧ bitsOf vs.length q.1 ⊆ bitsOf vs.length p.1 ∧
        ∀ t ∈ ts, S ⊆ bitsOf vs.length t → bitsOf vs.length q.1 ⊆ bitsOf vs.length t := by
    intro ts
    induction ts with
    | nil => exact fun _ p hp hSp => ⟨p, hp, hSp, subset_rfl, by simp⟩
    | cons t ts ih =>
      intro hts p hp hSp
      have hts' : ∀ t' ∈ ts, t' ∈ rows.map (tightMask vs) := fun t' ht' => hts t' (List.mem_cons_of_mem t ht')
      by_cases hSt : S ⊆ bitsOf vs.length t
      · have hne' : p.1 &&& t ≠ 0 := by
          obtain ⟨s, hs⟩ := hne
          intro h0
          have hmem : s ∈ bitsOf vs.length (p.1 &&& t) := by
            rw [bitsOf_and]
            exact Finset.mem_inter.2 ⟨hSp hs, hSt hs⟩
          rw [h0, mem_bitsOf] at hmem
          simp at hmem
        obtain ⟨p', hp', hp'1⟩ :=
          (testBit_famBits fam _).1 ((h4 p hp t (hts t List.mem_cons_self)).resolve_left hne')
        have hp'sub : bitsOf vs.length p'.1 = bitsOf vs.length p.1 ∩ bitsOf vs.length t := by
          rw [hp'1, bitsOf_and]
        obtain ⟨q, hq, hSq, hqp', hqts⟩ := ih hts' p' hp' (by rw [hp'sub]; exact Finset.subset_inter hSp hSt)
        refine ⟨q, hq, hSq, hqp'.trans (hp'sub ▸ Finset.inter_subset_left), fun t' ht' hSt' => ?_⟩
        rcases List.mem_cons.1 ht' with rfl | ht'
        · exact hqp'.trans (hp'sub ▸ Finset.inter_subset_right)
        · exact hqts t' ht' hSt'
      · obtain ⟨q, hq, hSq, hqp, hqts⟩ := ih hts' p hp hSp
        refine ⟨q, hq, hSq, hqp, fun t' ht' hSt' => ?_⟩
        rcases List.mem_cons.1 ht' with rfl | ht'
        · exact absurd hSt' hSt
        · exact hqts t' ht' hSt'
  obtain ⟨q, hq, hSq, -, hqts⟩ :=
    key (rows.map (tightMask vs)) (fun t ht => ht) _ h3 (by rw [bitsOf_full]; exact Finset.subset_univ S)
  refine ⟨q, hq, Finset.Subset.antisymm (fun k hk => hS k fun row hrow hall => ?_) hSq⟩
  have hSt : S ⊆ bitsOf vs.length (tightMask vs row) :=
    fun s hs => mem_bitsOf.2 ((tight_vpt_iff vs row s).1 (hall s hs))
  exact (tight_vpt_iff vs row k).2 (mem_bitsOf.1 (hqts _ (List.mem_map.2 ⟨row, hrow, rfl⟩) hSt hk))

theorem ssubset_of_and {nv M N : ℕ} (hM : M < 2 ^ nv) (hN : N < 2 ^ nv) (h : M &&& N = M) (hne : M ≠ N) :
    bitsOf nv M ⊂ bitsOf nv N :=
  Finset.ssubset_iff_subset_ne.2 ⟨(and_eq_self_iff_bitsOf hM).1 h, fun h' => hne (eq_of_bitsOf_eq hM hN h')⟩

/-- What every entry of `fam` satisfies (from check (2)). -/
def EntryOK (rows : List (Row d)) (vs : List ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 < 2 ^ vs.length ∧ (bitsOf vs.length p.1).Nonempty ∧ IsClosedSet rows (vpt vs) (bitsOf vs.length p.1)

theorem adim_le_label (hQ : polyOf rows = convexHull ℝ (Set.range (vpt vs))) (hdim : adim (polyOf rows) = d)
    (h1 : (fam.map Prod.fst).Nodup) (hok : ∀ p ∈ fam, EntryOK rows vs p) (h3 : (2 ^ vs.length - 1, d) ∈ fam)
    (h6 : ∀ p ∈ fam, p.1 = 2 ^ vs.length - 1 ∨ ∃ q ∈ fam, p.1 &&& q.1 = p.1 ∧ q.1 ≠ p.1 ∧ q.2 = p.2 + 1) :
    ∀ p ∈ fam, adim (vpt (d := d) vs '' ↑(bitsOf vs.length p.1)) ≤ p.2 := by
  suffices h : ∀ n, ∀ p ∈ fam, vs.length - (bitsOf vs.length p.1).card = n →
      adim (vpt (d := d) vs '' ↑(bitsOf vs.length p.1)) ≤ p.2 from fun p hp => h _ p hp rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hp hn
  rcases h6 p hp with hfull | ⟨q, hq, hpq, hne, hlab⟩
  · have hpd : p = (2 ^ vs.length - 1, d) := List.inj_on_of_nodup_map h1 hp h3 hfull
    rw [hpd, bitsOf_full, Finset.coe_univ, Set.image_univ, ← adim_convexHull, ← hQ, hdim]
  · have hss := ssubset_of_and (hok p hp).1 (hok q hq).1 hpq (Ne.symm hne)
    have hlt := adim_lt_of_ssubset hQ (hok p hp).2.2 (hok q hq).2.2 (hok p hp).2.1 hss
    have hcard := Finset.card_lt_card hss
    have hcardq : (bitsOf vs.length q.1).card ≤ vs.length :=
      (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
    have := ih (vs.length - (bitsOf vs.length q.1).card) (by omega) q hq rfl
    omega

theorem label_le_adim (hQ : polyOf rows = convexHull ℝ (Set.range (vpt vs)))
    (hok : ∀ p ∈ fam, EntryOK rows vs p)
    (h5 : ∀ p ∈ fam, p.2 = 0 ∨ ∃ q ∈ fam, q.1 &&& p.1 = q.1 ∧ q.1 ≠ p.1 ∧ q.2 + 1 = p.2) :
    ∀ p ∈ fam, p.2 ≤ adim (vpt (d := d) vs '' ↑(bitsOf vs.length p.1)) := by
  suffices h : ∀ n, ∀ p ∈ fam, p.2 = n → n ≤ adim (vpt (d := d) vs '' ↑(bitsOf vs.length p.1)) from
    fun p hp => h _ p hp rfl
  intro n
  induction n with
  | zero => exact fun _ _ _ => Nat.zero_le _
  | succ n ih =>
    intro p hp hn
    rcases h5 p hp with h0 | ⟨q, hq, hqp, hne, hlab⟩
    · omega
    · have hss := ssubset_of_and (hok q hq).1 (hok p hp).1 hqp hne
      have hlt := adim_lt_of_ssubset hQ (hok q hq).2.2 (hok p hp).2.2 (hok q hq).2.1 hss
      have := ih q hq (by omega)
      omega

end Main

/-- **Soundness.** If `polyOf rows` is the hull of its 0/1 points and has dimension `d`, and the checks pass, then the
number of `k`-dimensional faces is the number of entries of `fam` with dimension `k`. -/
theorem fNum_eq_of_check (rows : List (Row d)) (vs : List ℕ) (fam : List (ℕ × ℕ))
    (hhull : polyOf rows = convexHull ℝ (polyOf rows ∩ zeroOneVectors (Fin d)))
    (hdim : adim (polyOf rows) = d) (hc : censusCheck d rows vs fam = true) (k : ℕ) :
    fNum (polyOf rows) k = (fam.filter (fun p => p.2 == k)).length := by
  simp only [censusCheck, Bool.and_eq_true] at hc
  obtain ⟨hv, hf⟩ := hc
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := checkFam_facts hf
  have hQ := hull_vpt rows vs hv hhull
  have hok : ∀ p ∈ fam, EntryOK rows vs p := fun p hp =>
    ⟨(h2 p hp).2.1, bitsOf_nonempty (h2 p hp).2.1 (h2 p hp).1, closed_of_mem (h2 p hp).2.1 (h2 p hp).2.2⟩
  have hlab : ∀ p ∈ fam, adim (vpt (d := d) vs '' ↑(bitsOf vs.length p.1)) = p.2 := fun p hp =>
    le_antisymm (adim_le_label hQ hdim h1 hok h3 h6 p hp) (label_le_adim hQ hok h5 p hp)
  set L := fam.filter (fun p => p.2 == k) with hL
  set face : ℕ × ℕ → Set (Fin d → ℝ) := fun p => convexHull ℝ (vpt vs '' ↑(bitsOf vs.length p.1)) with hface
  have hfaces : faces (polyOf rows) k = face '' {p | p ∈ L} := by
    ext F
    simp only [faces, Set.mem_ofPred_eq, Set.mem_image, hL, List.mem_filter, beq_iff_eq, hface]
    constructor
    · rintro ⟨hF, hFk⟩
      obtain ⟨S, hSne, hScl, rfl⟩ := exists_closed_of_isFace hQ hF
      obtain ⟨p, hp, hpS⟩ := exists_mem_of_closed h3 h4 hScl hSne
      refine ⟨p, ⟨hp, ?_⟩, by rw [hpS]⟩
      rw [← hlab p hp, hpS, ← adim_convexHull, hFk]
    · rintro ⟨p, ⟨hp, hpk⟩, rfl⟩
      exact ⟨isFace_of_closed hQ (hok p hp).2.2 (hok p hp).2.1, by rw [adim_convexHull, hlab p hp, hpk]⟩
  have hinj : Set.InjOn face {p | p ∈ L} := by
    intro p hp q hq hpq
    have hp' := (List.mem_filter.1 hp).1
    have hq' := (List.mem_filter.1 hq).1
    have hbits : bitsOf vs.length p.1 = bitsOf vs.length q.1 := by
      ext j
      rw [← mem_hull_iff_of_closed hQ (hok p hp').2.2 (hok p hp').2.1 j,
        ← mem_hull_iff_of_closed hQ (hok q hq').2.2 (hok q hq').2.1 j]
      exact Iff.of_eq (congrArg (vpt vs j ∈ ·) hpq)
    exact List.inj_on_of_nodup_map h1 hp' hq' (eq_of_bitsOf_eq (hok p hp').1 (hok q hq').1 hbits)
  have hnd : L.Nodup := (List.Nodup.of_map Prod.fst h1).filter _
  rw [fNum, hfaces, hinj.ncard_image,
    show {p | p ∈ L} = (L.toFinset : Set (ℕ × ℕ)) by ext; simp, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd]

end HibiLi.Census
