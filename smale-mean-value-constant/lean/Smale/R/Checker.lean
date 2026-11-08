/-
Smale/R/Checker.lean — The packed checker for one interval of fact (R). Computation only; it carries no claim.
-/
namespace Smale.RK

abbrev SN := Bool × Nat
abbrev GS := SN × SN

def szero : SN := (false, 0)
def gzero : GS := (szero, szero)

def sneg (x : SN) : SN := (!x.1, x.2)
def sadd (x y : SN) : SN :=
  cond (Bool.xor x.1 y.1)
    (cond (Nat.ble y.2 x.2) (x.1, x.2 - y.2) (y.1, y.2 - x.2))
    (x.1, x.2 + y.2)
def smul (x y : SN) : SN := (Bool.xor x.1 y.1, x.2 * y.2)
def sshl (x : SN) (w : Nat) : SN := (x.1, x.2 <<< w)

def gadd (x y : GS) : GS := (sadd x.1 y.1, sadd x.2 y.2)
def gneg (x : GS) : GS := (sneg x.1, sneg x.2)
def gconj (x : GS) : GS := (x.1, sneg x.2)
def gmul (x y : GS) : GS :=
  (sadd (smul x.1 y.1) (sneg (smul x.2 y.2)), sadd (smul x.1 y.2) (smul x.2 y.1))
def gshl (x : GS) (w : Nat) : GS := (sshl x.1 w, sshl x.2 w)

/-- `V_0, ..., V_(n-1)` from `v = V_l`, `v' = V_(l-1)`, with `V_(l+1) = twoab V_l + d2 V_(l-1)`. -/
def vTable (twoab d2 : SN) : Nat → SN → SN → List SN
  | 0, _, _ => []
  | n + 1, v, v' => v :: vTable twoab d2 n (sadd (smul twoab v) (smul d2 v')) v

/-- `q_l = hbar_(l+1) D^(17-l) V_l`, `l = 0, ..., 17`. -/
def qList (k : Nat) (hb : List GS) (vs : List SN) : List GS :=
  (List.range 18).map fun l =>
    let h := hb.getD l gzero
    let v := vs.getD l szero
    (smul (sshl h.1 (k * (17 - l))) v, smul (sshl h.2 (k * (17 - l))) v)

/-- `Σ_i q_i x^i`. -/
def packX (w : Nat) : List GS → GS
  | [] => gzero
  | q :: qs => gadd q (gshl (packX w qs) w)

/-- `Row_j, ..., Row_(j+n-1)`, from `prev = Row_(j-1)`. -/
def rowsAux (w : Nat) (cP rP : GS) (qs : List GS) : Nat → Nat → GS → List GS
  | 0, _, _ => []
  | n + 1, j, prev =>
    let r := gadd (gadd (gshl prev w) (gmul (qs.getD j gzero) cP))
      (gneg (gmul (gconj (qs.getD (17 - j) gzero)) rP))
    r :: rowsAux w cP rP qs n (j + 1) r

/-- `acc + Σ_i a_i Row_i`. -/
def combo : List GS → List GS → GS → GS
  | a :: as, r :: rs, acc => combo as rs (gadd acc (gmul a r))
  | _, _, acc => acc

/-- The balanced digit at the bottom of a nonnegative offset number. -/
def digit (mask half u : Nat) : SN :=
  let d := Nat.land u mask
  cond (Nat.ble half d) (false, d - half) (true, half - d)

/-- Offset form of a signed packed number. -/
def toU (off : Nat) (x : SN) : Nat :=
  cond x.1 (off - x.2) (off + x.2)

/-- `acc + Σ_k (digits k of ure, uim) astar_k`. -/
def gRow (w mask half : Nat) : List GS → Nat → Nat → GS → GS
  | ast :: rest, ure, uim, acc =>
    gRow w mask half rest (ure >>> w) (uim >>> w) (gadd acc (gmul (digit mask half ure, digit mask half uim) ast))
  | [], _, _, acc => acc

/-- `acc + Σ_k |digits k|₁ col_k`. -/
def tailRow (w mask half : Nat) : List Nat → Nat → Nat → Nat → Nat
  | c :: cs, ure, uim, acc =>
    tailRow w mask half cs (ure >>> w) (uim >>> w) (acc + ((digit mask half ure).2 + (digit mask half uim).2) * c)
  | [], _, _, acc => acc

/-- `tailRow` over `n` orders of `tau`. -/
def tailAll (w mask half : Nat) (col : List Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | n + 1, ure, uim, acc =>
    tailAll w mask half col n (ure >>> (18 * w)) (uim >>> (18 * w)) (tailRow w mask half col ure uim acc)

/-- `ℓ¹` norm of `n` digits, except that the real part of digit `j` is kept apart: (sum, that digit). -/
def rowNorm (w mask half j : Nat) : Nat → Nat → Nat → Nat → Nat × SN → Nat × SN
  | 0, _, _, _, acc => acc
  | n + 1, t, ure, uim, acc =>
    let dr := digit mask half ure
    let di := digit mask half uim
    rowNorm w mask half j n (t + 1) (ure >>> w) (uim >>> w)
      (cond (Nat.beq t j) (acc.1 + di.2, dr) (acc.1 + dr.2 + di.2, acc.2))

/-- `acc +` the row norms of `G_s,j` over `n` orders of `tau`. Here `j = 99` keeps no digit apart. -/
def lowOrders (w mask half off17 : Nat) (astar : List GS) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | n + 1, ure, uim, acc =>
    let g := gRow w mask half astar ure uim gzero
    let r := rowNorm w mask half 99 17 0 (toU off17 g.1) (toU off17 g.2) (acc, szero)
    lowOrders w mask half off17 astar n (ure >>> (18 * w)) (uim >>> (18 * w)) r.1

/-- `ℓ¹` norm of a list of Gaussian numbers. -/
def l1List (r : List GS) : Nat := (r.map fun e => e.1.2 + e.2.2).foldr (· + ·) 0

/-- Row `j`: the real diagonal of `G_0` beats everything else. -/
def testRow (w mask half off off17 order : Nat) (astar : List GS) (col : List Nat) (etaScaled j : Nat) (h : GS)
    (ar : List GS) : Bool :=
  let ure := toU off h.1
  let uim := toU off h.2
  let g0 := gRow w mask half astar ure uim gzero
  let r0 := rowNorm w mask half j 17 0 (toU off17 g0.1) (toU off17 g0.2) (0, szero)
  let low := lowOrders w mask half off17 astar (order - 1) (ure >>> (18 * w)) (uim >>> (18 * w)) r0.1
  let tail := tailAll w mask half col (35 - order) (ure >>> (order * (18 * w))) (uim >>> (order * (18 * w))) low
  Nat.ble (tail + etaScaled * l1List ar + 1) (cond r0.2.1 0 r0.2.2)

/-- Column `k` of `conj A`, packed in `t`. -/
def astarCols (w : Nat) (a : List (List GS)) : List GS :=
  (List.range 17).map fun k => packX w (a.map fun r => gconj (r.getD k gzero))

def colSums (a : List (List GS)) : List Nat :=
  (List.range 17).map fun k => l1List (a.map fun r => r.getD k gzero)

/-- `half (1 + x + ... + x^(n-1))`. -/
def offsetOf (w n : Nat) : Nat := (1 <<< (w - 1)) * (((1 <<< (w * n)) - 1) / ((1 <<< w) - 1))

/-- The shape and size checks: 17 rows, each of at most 17 entries, every part at most `2^48`. -/
def aShape (amat : List (List GS)) : Bool :=
  Nat.beq amat.length 17 && amat.all fun r =>
    Nat.ble r.length 17 && r.all fun e => Nat.ble e.1.2 (1 <<< 48) && Nat.ble e.2.2 (1 <<< 48)

/-- `|D^34 (2^128 B_exact - B_rounded)_jk| ≤ 2^93 D^34`. -/
def etaBits : Nat := 93

/-- The check of one interval. `order` is S. -/
def checkInterval (hb : List GS) (a k order : Nat) (amat : List (List GS)) : Bool :=
  let w := 324 + 34 * k
  let twoab : SN := (false, 2 * a + (2 <<< (18 * w)))
  let d2 : SN := (true, 1 <<< (2 * k))
  let vs := vTable twoab d2 18 (false, 1) szero
  let qs := qList k hb vs
  let cP := gconj (packX w qs)
  let rP := packX w ((List.range 18).map fun t => qs.getD (17 - t) gzero)
  let rows := rowsAux w cP rP qs 17 0 gzero
  let mask := (1 <<< w) - 1
  let half := 1 <<< (w - 1)
  let off := offsetOf w (18 * 35)
  let off17 := offsetOf w 17
  let col := colSums amat
  let etaScaled := (col.foldr (· + ·) 0) <<< (etaBits + 34 * k)
  let astar := astarCols w amat
  aShape amat && Nat.ble (a + 1) (1 <<< k) &&
    (List.range 17).all fun j =>
      testRow w mask half off off17 order astar col etaScaled j (combo (amat.getD j []) rows gzero) (amat.getD j [])

end Smale.RK
