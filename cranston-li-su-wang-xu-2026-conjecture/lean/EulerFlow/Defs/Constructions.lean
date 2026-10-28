/-
EulerFlow/Defs/Constructions.lean — the graph operations and concrete graphs of paper 002 (Sections 3-9),
and the cyclic decomposition of a finite abelian group (Section 4).
-/
import EulerFlow.Defs.Graph

namespace EulerFlow

open Finset

namespace MGraph

variable {V E : Type} (G : MGraph V E)

/-! ### Deleting a loop (Lemma 3.1) -/

/-- `G - l`: the graph without the edge `l` (tex l.223). -/
def deleteEdge (l : E) : MGraph V {x : E // x ≠ l} where
  src x := G.src x.1
  tgt x := G.tgt x.1

/-! ### Splitting off (Lemma 3.2, tex l.234-243) -/

section Split

variable [DecidableEq V]

/-- `e` is an edge at `v`. -/
def IsAt (e : E) (v : V) : Prop := G.src e = v ∨ G.tgt e = v

/-- For an edge `e` at `v` (with no loop): the vertex of its other end (`u` for `e = vu`). -/
def otherEnd (e : E) (v : V) : V := if G.src e = v then G.tgt e else G.src e

/-- For an edge `e` at `v` (with no loop): its end at `v`. -/
def endAt (e : E) (v : V) : E × Bool := if G.src e = v then (e, false) else (e, true)

/-- The split graph `G' = G - e - e' + g` (tex l.235-239) for two edges `e = vu`, `e' = vw` at `v`. Its edges are
the edges of `G` other than `e, e'` (as `some x`) and the new edge `g = none`, directed from `u` to `w`
(a loop if `u = w`). -/
def splitOff (v : V) (e e' : E) : MGraph V (Option {x : E // x ≠ e ∧ x ≠ e'}) where
  src := fun x => match x with
    | none => G.otherEnd e v
    | some x => G.src x.1
  tgt := fun x => match x with
    | none => G.otherEnd e' v
    | some x => G.tgt x.1

/-- The map `L` of Lemma 3.2 (tex l.240-242): `L f'` agrees with `f'` on the common edges, and has on `e` in the
direction from `u` to `v`, and on `e'` in the direction from `v` to `w`, the value `x = f'(g)` of `f'` on `g` in
the direction from `u` to `w`. (Written in reference directions: `e` runs from `u` to `v` iff `tgt e = v`, and
`e'` runs from `v` to `w` iff `src e' = v`.) -/
def splitLift [DecidableEq E] {A : Type} [AddCommGroup A] (v : V) (e e' : E)
    (f' : Option {x : E // x ≠ e ∧ x ≠ e'} → A) : E → A := fun x =>
  if h : x ≠ e ∧ x ≠ e' then f' (some ⟨x, h⟩)
  else if x = e then (if G.tgt e = v then f' none else -f' none)
  else (if G.src e' = v then f' none else -f' none)

/-- `B(v; e, e')` (tex l.242-243): the flows of `G` in which the ends of `e` and of `e'` at `v` are a balanced
pair. -/
def InB [Fintype E] {A : Type} [AddCommGroup A] (v : V) (e e' : E) (f : E → A) : Prop :=
  G.IsNZFlow f ∧ dirVal f (G.endAt e v) + dirVal f (G.endAt e' v) = 0

end Split

/-! ### Contracting a triangle (Lemma 5.1, tex l.415-419) -/

section Contract

variable [DecidableEq V] [DecidableEq E]

/-- `G⁺/Δ` (tex l.418): delete the edges in `D` and identify the vertices in `X` to one new vertex `none`. Used
with `X = {x₁, x₂, x₃}` and `D` = the three edges of the triangle `Δ`. -/
def contract (X : Finset V) (D : Finset E) : MGraph (Option {y : V // y ∉ X}) {e : E // e ∉ D} where
  src e := if h : G.src e.1 ∈ X then none else some ⟨G.src e.1, h⟩
  tgt e := if h : G.tgt e.1 ∈ X then none else some ⟨G.tgt e.1, h⟩

/-- The edge `d` joins `x` and `y` (in one of the two directions). -/
def Joins (d : E) (x y : V) : Prop :=
  (G.src d = x ∧ G.tgt d = y) ∨ (G.src d = y ∧ G.tgt d = x)

/-- The hypothesis of Lemma 5.1 (tex l.416-417): `Δ` is a triangle with the vertices `x₁, x₂, x₃` and the edges
`d₁₂, d₂₃, d₃₁`, and these three edges are the only edges with both ends in `{x₁, x₂, x₃}`. -/
structure IsIsolatedTriangle (x₁ x₂ x₃ : V) (d₁₂ d₂₃ d₃₁ : E) : Prop where
  x_ne₁₂ : x₁ ≠ x₂
  x_ne₂₃ : x₂ ≠ x₃
  x_ne₃₁ : x₃ ≠ x₁
  joins₁₂ : G.Joins d₁₂ x₁ x₂
  joins₂₃ : G.Joins d₂₃ x₂ x₃
  joins₃₁ : G.Joins d₃₁ x₃ x₁
  only : ∀ e, G.src e ∈ ({x₁, x₂, x₃} : Finset V) → G.tgt e ∈ ({x₁, x₂, x₃} : Finset V) →
    e = d₁₂ ∨ e = d₂₃ ∨ e = d₃₁

/-- The restriction `p f` of a map on `E(G⁺)` to `E(G⁺/Δ) = E(G⁺) ∖ E(Δ)` (tex l.419). -/
def restrictTo {A : Type} (D : Finset E) (f : E → A) : {e : E // e ∉ D} → A := fun e => f e.1

end Contract

/-! ### Paths (for the remark after Theorem 2.5, tex l.195-196) -/

/-- A path from `u` to `w`, as the list of its darts: consecutive darts meet, it starts at `u`, ends at `w`, and
no vertex is visited twice. -/
structure Path (u w : V) where
  darts : List (E × Bool)
  ne_nil : darts ≠ []
  chain : darts.IsChain (fun d d' => G.dartHead d = G.dartTail d')
  starts : G.dartTail (darts.head ne_nil) = u
  ends : G.dartHead (darts.getLast ne_nil) = w
  verts_nodup : (darts.map G.dartTail ++ [w]).Nodup

/-- Two paths with no common edge. -/
def Path.EdgeDisjoint {G : MGraph V E} {u w : V} (P P' : G.Path u w) : Prop :=
  ∀ d ∈ P.darts, ∀ d' ∈ P'.darts, d.1 ≠ d'.1

/-! ### Multi-steps as a graph (Section 7) and a change of the reference directions (tex l.129) -/

section More

variable [Fintype E] [DecidableEq E] [DecidableEq V]

/-- The graph of nowhere-zero `A`-flows in which two flows are adjacent when one comes from the other by a multi-step
(tex l.148-151); a walk of length `N` is "a chain of at most `N` multi-steps" (Section 7, tex l.535-546). -/
def multiStepGraph (A : Type) [AddCommGroup A] : SimpleGraph {f : E → A // G.IsNZFlow f} :=
  SimpleGraph.fromRel fun f f' => ∃ t : A, G.IsMultiStep t f.1 f'.1

end More

/-- [CLSWX] (arXiv:2606.24685v1, Section 5), quoted for Remark 2.6 (tex l.205-207): "a graph is triangularly
connected if for any two of its edges, there is a sequence of triangles T1, T2, …, Tk such that the first triangle
contains one edge, the last triangle contains the other, and any two consecutive triangles share at least one edge."
Here for the subgraph with all vertices of `G` and the edge set `S` (a triangle = a directed cycle with three darts,
all of its edges in `S`). -/
def IsTriConnectedOn (S : Set E) : Prop :=
  ∀ e ∈ S, ∀ e' ∈ S, ∃ Ts : List G.DirCycle, ∃ h : Ts ≠ [],
    (∀ T ∈ Ts, T.darts.length = 3 ∧ ∀ d ∈ T.darts, d.1 ∈ S) ∧
    (∃ d ∈ (Ts.head h).darts, d.1 = e) ∧ (∃ d ∈ (Ts.getLast h).darts, d.1 = e') ∧
    Ts.IsChain (fun T T' => ∃ d ∈ T.darts, ∃ d' ∈ T'.darts, d.1 = d'.1)

/-- The same graph with the reference direction of every edge `e` with `R e = true` reversed (tex l.129: "Fix a
reference direction of every edge"; the notions of the paper do not depend on this choice). -/
def reorient (R : E → Bool) : MGraph V E where
  src e := if R e then G.tgt e else G.src e
  tgt e := if R e then G.src e else G.tgt e

end MGraph

/-! ### Concrete graphs -/

/-- The graph with two vertices and `n` parallel edges, all directed from `0` to `1` (tex l.79, l.724). -/
def dipole (n : ℕ) : MGraph (Fin 2) (Fin n) where
  src _ := 0
  tgt _ := 1

/-- The complete graph `K₅` (Remark 2.6, tex l.201), each edge directed from the smaller to the larger vertex. -/
def K5 : MGraph (Fin 5) {pr : Fin 5 × Fin 5 // pr.1 < pr.2} where
  src pr := pr.1.1
  tgt pr := pr.1.2

/-- The graph that is one cycle with `n ≥ 1` edges (Remark 9.7, tex l.860): vertices `0, …, n-1`, edge `i` from
`i` to `i + 1 (mod n)`. For `n = 1` it is a loop, for `n = 2` two parallel edges. -/
def cycleGraph (n : ℕ) : MGraph (Fin n) (Fin n) where
  src i := i
  tgt i := finRotate n i

/-! ### A cyclic decomposition of a finite abelian group (Section 4, tex l.323-332) -/

/-- `A = ⟨s₁⟩ ⊕ ⋯ ⊕ ⟨s_r⟩` with `s_k ≠ 0` (tex l.323-328): every element of `A` is in exactly one way a sum of
elements of the groups `⟨s_k⟩` (its PARTS). -/
structure CyclicDecomp (A : Type) [AddCommGroup A] where
  r : ℕ
  s : Fin r → A
  s_ne : ∀ k, s k ≠ 0
  parts_unique : ∀ a : A, ∃! c : Fin r → A,
    (∀ k, c k ∈ AddSubgroup.zmultiples (s k)) ∧ ∑ k, c k = a

namespace CyclicDecomp

variable {A : Type} [AddCommGroup A] (D : CyclicDecomp A)

/-- `S = {s₁, -s₁, …, s_r, -s_r}`, the SMALL elements (tex l.328). -/
def S : Set A := {x | ∃ k, x = D.s k ∨ x = -D.s k}

/-- `ρ(f)`: the number of the edges that are not small for `f` (tex l.331-332). -/
noncomputable def rho {E : Type} (f : E → A) : ℕ := Set.ncard {e | f e ∉ D.S}

end CyclicDecomp

/-! ### Small edges for ℤ_m (Section 6, tex l.461-463) and for (p,q)-flows (Section 9, tex l.772-774) -/

/-- `ρ(f)` for a `ℤ_m`-flow: the number of the edges whose value is not `1` or `-1` (tex l.461-462). -/
noncomputable def rhoCyc {E : Type} {m : ℕ} (f : E → ZMod m) : ℕ := Set.ncard {e | f e ≠ 1 ∧ f e ≠ -1}

/-- `ρ(f)` for a `(p,q)`-flow: the number of the edges whose value is not `q` or `-q` (tex l.772-773). -/
noncomputable def rhoPQ {E : Type} {p : ℕ} (q : ℕ) (f : E → ZMod p) : ℕ :=
  Set.ncard {e | f e ≠ (q : ZMod p) ∧ f e ≠ -(q : ZMod p)}

/-! ### Step sets of Sections 6 and 9 -/

/-- The step values `{1, -1, 2, -2}` in `ℤ_m` (Theorem 2.4, Section 6; tex l.182, l.461). -/
def Tcyc (m : ℕ) : Set (ZMod m) := {1, -1, 2, -2}

/-- The step values `{1, -1, 2q, -2q}` in `ℤ_p` (Theorem 9.1, Section 9; tex l.719, l.774). -/
def Tpq (p q : ℕ) : Set (ZMod p) := {1, -1, ((2 * q : ℕ) : ZMod p), -((2 * q : ℕ) : ZMod p)}

/-- `J` of Lemma 9.5 (tex l.790-791): the residues modulo `p` of the integers `2q, 2q+1, …, p-2q`. -/
def Jpq (p q : ℕ) : Set (ZMod p) := {x | ∃ n : ℕ, 2 * q ≤ n ∧ n ≤ p - 2 * q ∧ (n : ZMod p) = x}

end EulerFlow
