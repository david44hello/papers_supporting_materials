/-
EulerFlow/Defs/Graph.lean — multigraphs, ends, flows, directed cycles, steps (paper 002, Section 2).
Paper: Dave Goel, "Eulerian graphs are flow-connected", v0.30 (2026-10-23) = the expanded version, reference [3] of the paper.
-/
import Mathlib

namespace EulerFlow

open Finset

/-- A finite multigraph (tex l.122: "All graphs are finite multigraphs; loops and parallel edges are allowed").
Every edge `e` has a fixed reference direction (tex l.129), from `src e` to `tgt e`. Finiteness of `V` and `E`
is supplied by `Fintype` instances in every statement. -/
structure MGraph (V E : Type) where
  src : E → V
  tgt : E → V

namespace MGraph

variable {V E : Type} (G : MGraph V E)

/-- `e` is a loop: both of its ends are at one vertex. -/
def IsLoop (e : E) : Prop := G.src e = G.tgt e

/-- `G` has no loop. -/
def Loopless : Prop := ∀ e, ¬ G.IsLoop e

/-! ### Ends and darts (tex l.153-155)

An END is a pair `(e, b)`: `(e, false)` is the end of `e` at `src e`, and `(e, true)` is the end of `e` at
`tgt e` ("Every edge has two ends; both ends of a loop at v are ends at v").

The same pair `(e, b)` is also read as a DART: the traversal of `e` that LEAVES its tail vertex through the
end `(e, b)` and ENTERS its head vertex through the end `(e, !b)`. So the dart `(e, false)` passes `e` in its
reference direction and the dart `(e, true)` passes `e` in the other direction. -/

/-- The vertex of the end `i`. -/
def endVertex (i : E × Bool) : V := if i.2 then G.tgt i.1 else G.src i.1

/-- The vertex that the dart `d` leaves (through the end `d`). -/
def dartTail (d : E × Bool) : V := G.endVertex d

/-- The vertex that the dart `d` enters (through the end `(d.1, !d.2)`). -/
def dartHead (d : E × Bool) : V := G.endVertex (d.1, !d.2)

/-- The value of a map `x : E → M` on the edge `d.1` in the direction of the dart `d` (tex l.131: "The value of
f on an edge e is f(e) in the reference direction of e and -f(e) in the other direction"). For an END `i` at `v`,
`dirVal x i` is the OUTWARD value `y_i` of tex l.155: the value in the direction that leaves `v` through `i`. -/
def dirVal {M : Type} [Neg M] (x : E → M) (d : E × Bool) : M := if d.2 then -x d.1 else x d.1

section Finite

variable [Fintype E] [DecidableEq V]

/-- The degree of `v` is the number of ends at `v` (tex l.154); a loop counts twice (tex l.123). -/
def degree (v : V) : ℕ := (univ.filter fun i : E × Bool => G.endVertex i = v).card

/-- `G` is EVEN: every vertex has even degree (tex l.123). -/
def IsEven : Prop := ∀ v, Even (G.degree v)

/-- The flow condition (tex l.129-131) for a map `x : E → M` into an abelian group: at every vertex, the sum of
`x` over the edges that leave the vertex (in their reference direction) equals the sum over the edges that
enter it. A loop at `v` is in both sums. With `M = ℤ` this is an integer flow (tex l.568). -/
def IsFlow {M : Type} [AddCommGroup M] (x : E → M) : Prop :=
  ∀ v, ∑ e ∈ univ.filter (fun e => G.src e = v), x e = ∑ e ∈ univ.filter (fun e => G.tgt e = v), x e

/-- A flow all of whose values lie in the set `I`. Used with `I = {x | x ≠ 0}` (nowhere-zero `A`-flows, §2),
with `I = Ik k` (integer `k`-flows, §8) and with `I = Ipq p q` (modular `(p,q)`-flows, §9). -/
def IsIFlow {M : Type} [AddCommGroup M] (I : Set M) (x : E → M) : Prop :=
  G.IsFlow x ∧ ∀ e, x e ∈ I

/-- In the paper "a flow is a nowhere-zero A-flow: f(e) ≠ 0 for every edge e" (tex l.132). -/
def IsNZFlow {A : Type} [AddCommGroup A] (f : E → A) : Prop := G.IsIFlow {x | x ≠ 0} f

/-- The boundary `(∂x)(v)` (tex l.569-571): the sum of `x` over the edges that enter `v` minus the sum over the
edges that leave `v` (a loop at `v` is in both sums). -/
def boundary {M : Type} [AddCommGroup M] (x : E → M) (v : V) : M :=
  ∑ e ∈ univ.filter (fun e => G.tgt e = v), x e - ∑ e ∈ univ.filter (fun e => G.src e = v), x e

end Finite

/-- A balanced pair of `f` at `v` (Definition 2.1, tex l.166-169): two different ends `i, j` at `v` with
`y_i(f) + y_j(f) = 0`. (The paper defines it for graphs with no loop; every statement that uses it assumes
`G.Loopless`. WARNING: at a loop the two ends of the loop always form a balanced pair.) -/
def HasBalancedPairAt {A : Type} [AddCommGroup A] (f : E → A) (v : V) : Prop :=
  ∃ i j : E × Bool, i ≠ j ∧ G.endVertex i = v ∧ G.endVertex j = v ∧ dirVal f i + dirVal f j = 0

/-- `f` has a balanced pair at some vertex. -/
def HasBalancedPair {A : Type} [AddCommGroup A] (f : E → A) : Prop := ∃ v, G.HasBalancedPairAt f v

/-! ### Directed cycles (tex l.124-126, l.134-136) -/

/-- A DIRECTED CYCLE: a cycle ("a connected subgraph in which every vertex has degree 2", tex l.124) with one of
its two directions of traversal, written as the cyclic list of its darts. Consecutive darts meet (the head of
each dart is the tail of the next, and the last dart returns to the first), no edge is used twice, and no vertex
is left twice. A loop is the one-dart cycle; two parallel edges give a two-dart cycle (tex l.125). -/
structure DirCycle where
  darts : List (E × Bool)
  ne_nil : darts ≠ []
  chain : darts.IsChain (fun d d' => G.dartHead d = G.dartTail d')
  closes : G.dartHead (darts.getLast ne_nil) = G.dartTail (darts.head ne_nil)
  edges_nodup : (darts.map Prod.fst).Nodup
  tails_nodup : (darts.map G.dartTail).Nodup

/-- Two directed cycles with no common edge. -/
def EdgeDisjoint (Q Q' : G.DirCycle) : Prop := ∀ d ∈ Q.darts, ∀ d' ∈ Q'.darts, d.1 ≠ d'.1

section Steps

variable [DecidableEq E]

/-- `χ_Q` (tex l.134-135): `1` if `Q` passes `e` in its reference direction, `-1` if `Q` passes `e` in the
other direction, and `0` if `e` is not on `Q`. -/
def DirCycle.chi {G : MGraph V E} (Q : G.DirCycle) (e : E) : ℤ :=
  if (e, false) ∈ Q.darts then 1 else if (e, true) ∈ Q.darts then -1 else 0

variable [Fintype E] [DecidableEq V]

/-- The step graph on `I`-flows with step values in `T` (tex l.135-139, l.144-146): its vertices are the
`I`-flows, and two of them are adjacent if they differ by a step `f' = f + t χ_Q` with a directed cycle `Q` and a
value `t ∈ T`, `t ≠ 0`. (`SimpleGraph.fromRel` makes the relation symmetric and drops `f = f'`.) -/
def stepGraph {A : Type} [AddCommGroup A] (I T : Set A) : SimpleGraph {f : E → A // G.IsIFlow I f} :=
  SimpleGraph.fromRel fun f f' =>
    ∃ Q : G.DirCycle, ∃ t ∈ T, t ≠ 0 ∧ f'.1 = f.1 + fun e => Q.chi e • t

/-- The graph `𝓕(G, A)` (tex l.137): nowhere-zero `A`-flows, adjacent when they differ by a step. -/
def flowGraph (A : Type) [AddCommGroup A] : SimpleGraph {f : E → A // G.IsNZFlow f} :=
  G.stepGraph {x | x ≠ 0} {x | x ≠ 0}

/-- `G` is `A`-flow-connected (tex l.139-140): `𝓕(G, A)` is connected, where a graph with at most one vertex
counts as connected — hence `Preconnected` (Mathlib's `Connected` would also demand a vertex). -/
def FlowConnected (A : Type) [AddCommGroup A] : Prop := (G.flowGraph A).Preconnected

/-- The graph of nowhere-zero `A`-flows with `T`-steps (tex l.144-146): two flows are `T`-JOINED iff they are
`Reachable` in this graph (a chain with no step is allowed). -/
def tStepGraph {A : Type} [AddCommGroup A] (T : Set A) : SimpleGraph {f : E → A // G.IsNZFlow f} :=
  G.stepGraph {x | x ≠ 0} T

/-- A multi-step with the value `t ≠ 0` (tex l.148-151): `f' = f + t(χ_{Q_1} + ⋯ + χ_{Q_r})` with `r ≥ 1`
directed cycles no two of which have a common edge. -/
def IsMultiStep {A : Type} [AddCommGroup A] (t : A) (f f' : E → A) : Prop :=
  t ≠ 0 ∧ ∃ Qs : List G.DirCycle, Qs ≠ [] ∧ Qs.Pairwise G.EdgeDisjoint ∧
    f' = f + fun e => (Qs.map fun Q => Q.chi e).sum • t

/-- `f` is joined to `f + (t₁ + ⋯ + t_n) χ_Q` by the steps `t₁, …, t_n` along the directed cycle `Q`, all with
values in `T`, every intermediate map `f + (t₁ + ⋯ + t_j) χ_Q` an `I`-flow (the chains "by steps along Q" of
Lemmas 6.1, 6.2, 9.4, 9.5). -/
def StepsAlong {A : Type} [AddCommGroup A] (I T : Set A) (Q : G.DirCycle) (f : E → A) (ts : List A) : Prop :=
  (∀ t ∈ ts, t ∈ T ∧ t ≠ 0) ∧ ∀ j ≤ ts.length, G.IsIFlow I (f + fun e => Q.chi e • (ts.take j).sum)

end Steps

/-! ### Eulerian orientations (tex l.272-274) -/

section Orient

variable [Fintype E] [DecidableEq V]

/-- An orientation `D : E → Bool` puts each edge `e` on the arc = dart `(e, D e)` (`D e = false`: the reference
direction). It is EULERIAN if at every vertex the in-degree equals the out-degree (tex l.272); a loop is one arc
that leaves and enters its vertex. -/
def IsEulerOrient (D : E → Bool) : Prop :=
  ∀ v, (univ.filter fun e => G.dartTail (e, D e) = v).card =
    (univ.filter fun e => G.dartHead (e, D e) = v).card

end Orient

/-- `a 𝟙_D` (tex l.273): the value `a` along every arc of the orientation `D`, written in reference directions. -/
def constFlow {A : Type} [AddCommGroup A] (a : A) (D : E → Bool) : E → A :=
  fun e => if D e then -a else a

/-! ### Conditions (T1), (T2) on a step set (tex l.213-218) -/

/-- (T1): any two non-zero elements of `A` are the ends of a chain of non-zero elements of `A` in which the
difference of any two neighbours is in `T`. -/
def CondT1 {A : Type} [AddCommGroup A] (T : Set A) : Prop :=
  ∀ a b : A, a ≠ 0 → b ≠ 0 → Relation.ReflTransGen (fun x y : A => y ≠ 0 ∧ y - x ∈ T) a b

/-- (T2): there is a non-zero `a ∈ A` with `2a = 0` or `2a ∈ T`. -/
def CondT2 {A : Type} [AddCommGroup A] (T : Set A) : Prop :=
  ∃ a : A, a ≠ 0 ∧ (2 • a = 0 ∨ 2 • a ∈ T)

end MGraph

/-! ### Integer flows (tex l.568-580) and modular (p,q)-flows (tex l.701-706) -/

/-- The values allowed for an integer `k`-flow (tex l.574): `1 ≤ |F(e)| ≤ k - 1`. -/
def Ik (k : ℤ) : Set ℤ := {x | 1 ≤ |x| ∧ |x| ≤ k - 1}

/-- `I(p, q)` (tex l.701-702): the residues modulo `p` of the integers `q, q+1, …, p-q`. -/
def Ipq (p q : ℕ) : Set (ZMod p) := {x | ∃ n : ℕ, q ≤ n ∧ n ≤ p - q ∧ (n : ZMod p) = x}

namespace MGraph

variable {V E : Type} (G : MGraph V E) [Fintype E] [DecidableEq E] [DecidableEq V]

/-- `𝓕(G, k)` (tex l.574-577): the integer `k`-flows, adjacent when they differ by `λ χ_Q` with a directed cycle
`Q` and an integer `λ ≠ 0`. -/
def kFlowGraph (k : ℤ) : SimpleGraph {F : E → ℤ // G.IsIFlow (Ik k) F} :=
  G.stepGraph (Ik k) {x | x ≠ 0}

/-- `G` is `k`-flow-connected (tex l.576-577). -/
def KFlowConnected (k : ℤ) : Prop := (G.kFlowGraph k).Preconnected

/-- An integer lift of a `ℤ_k`-flow `f` (tex l.578-579): a `k`-flow `F` with `F(e) ≡ f(e) (mod k)` on every edge. -/
def IsIntLift (k : ℕ) (f : E → ZMod k) (F : E → ℤ) : Prop :=
  G.IsIFlow (Ik k) F ∧ ∀ e, ((F e : ℤ) : ZMod k) = f e

/-- `𝓕(G; p, q)` (tex l.707-709): the `(p,q)`-flows, adjacent when they differ by a step `t χ_Q`, `t ≠ 0`. -/
def pqFlowGraph (p q : ℕ) : SimpleGraph {f : E → ZMod p // G.IsIFlow (Ipq p q) f} :=
  G.stepGraph (Ipq p q) {x | x ≠ 0}

/-- `G` is `(p,q)`-flow-connected (tex l.709). -/
def PQFlowConnected (p q : ℕ) : Prop := (G.pqFlowGraph p q).Preconnected

end MGraph

end EulerFlow
