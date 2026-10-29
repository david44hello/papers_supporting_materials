/-
Cereceda/Intro/SemiFalseIII.lean — semi-false graphs, bipartite distance-hereditary graphs and bipartite OAT graphs lie
in class (iii), the 3-colour-dense graphs (short v3.90 l. 157-162 and 173-192), from the cited [BJLPP14, Thms. 8 and
10] and the paper's "the 2-colour-dense graphs, which are also 3-colour-dense" (l. 157).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Cited.BJLPP14
import Cereceda.Intro.ColourDense
import Cereceda.Intro.DistanceHereditary
import Cereceda.Intro.OAT

namespace Cereceda

/-- The graph on an empty vertex type is 3-colour-dense (a disjoint union of no cliques). -/
theorem colourDense_three_of_isEmpty {V : Type} [Finite V] [IsEmpty V] (G : SimpleGraph V) : IsColourDense 3 G :=
  IsColourDense.base G ⟨SimpleGraph.Coloring.mk (fun x => isEmptyElim x) (fun {a} => isEmptyElim a)⟩
    ⟨fun x => isEmptyElim x, fun x => isEmptyElim x⟩

/-- v3.90 l. 157-158 ("With 2 in place of 3, this defines the 2-colour-dense graphs, which are also 3-colour-dense
... Among the 2-colour-dense graphs are the semi-false graphs [BJLPP14, Thm. 10]"): every semi-false graph lies in
class (iii). The empty graph is the base case; otherwise [BJLPP14, Thm. 10] (cited: `Cited.bjlpp14_thm10`) and
`colourDense_two_three_proved`. -/
theorem intro_semiFalse_in_iii_proved {V : Type} [Fintype V] (G : SimpleGraph V) (h : IsSemiFalse G) :
    IsColourDense 3 G := by
  rcases isEmpty_or_nonempty V with hV | hV
  · exact colourDense_three_of_isEmpty G
  · exact colourDense_two_three_proved G (Cited.bjlpp14_thm10 G h)

/-- v3.90 l. 176-179: "A bipartite distance-hereditary graph ... is chordal bipartite, hence semi-false, and lies in
(iii)": `intro_dh_chordal_bipartite_proved`, then [BJLPP14, Thm. 8] (cited: `Cited.bjlpp14_thm8`), then
`intro_semiFalse_in_iii_proved`. -/
theorem intro_dh_in_iii_proved {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hbip : G.IsBipartite)
    (hdh : IsDistanceHereditary G) : IsColourDense 3 G := by
  rcases isEmpty_or_nonempty V with hV | hV
  · exact colourDense_three_of_isEmpty G
  · exact intro_semiFalse_in_iii_proved G (Cited.bjlpp14_thm8 G (intro_dh_chordal_bipartite_proved G hbip hdh))

/-- v3.90 l. 173 and 179-192: the bipartite OAT graphs lie in (iii) ("contain no bipartite graph outside (i)-(v)"):
`intro_oat_semiFalse_proved`, then `intro_semiFalse_in_iii_proved`. -/
theorem intro_oat_in_iii_proved {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : IsOAT G)
    (hbip : G.IsBipartite) : IsColourDense 3 G :=
  intro_semiFalse_in_iii_proved G (intro_oat_semiFalse_proved G hG hbip)

end Cereceda
