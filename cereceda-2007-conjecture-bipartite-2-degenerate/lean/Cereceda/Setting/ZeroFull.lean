/-
Cereceda/Setting/ZeroFull.lean — in a greedy colouring of an instance with `0 < g`, the colour `0` is full (short v3.90 l. 310-311).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.Instance

namespace Cereceda

open Finset

namespace ZeroFull

variable {W : Type} [Fintype W] [DecidableEq W]

/-- If `0 < g`, the sink's list `{g, x}` does not contain `0` (as `0 < g < x`). -/
theorem zero_notMem_L_sink (I : Instance W) (hg : 0 < I.g) : (0 : Fin 4) ∉ I.L I.sink := by
  rw [I.L_sink]
  have hx : 0 < I.x := hg.trans I.g_lt_x
  simp only [mem_insert, mem_singleton, not_or]
  exact ⟨hg.ne, hx.ne⟩

/-- A vertex whose least free colour is not `0`, while `0` is in its list, has `0` among the used colours. -/
theorem zero_mem_used_of_ne {L used : Finset (Fin 4)} {y : Fin 4} (hy : IsLeastFree L used y) (h0 : (0 : Fin 4) ∈ L)
    (hy0 : y ≠ 0) : (0 : Fin 4) ∈ used :=
  hy.2.2 0 h0 (Fin.pos_iff_ne_zero.2 hy0)

end ZeroFull

/-- Short v3.90 l. 310-311 (proof of Lemma 2.3, where `0 < g < x`): "Thus the colour $0$ is full in $\alpha$ and in
$\beta$: every vertex whose list contains $0$ is on $0$ or has an out-neighbour on $0$." Stated for every greedy
colouring `c` (any sink colour `c0`); `α` is `IsGreedy I.x` and `β` is `IsGreedy I.g`. -/
theorem lem_2_3_zero_full_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hg : 0 < I.g) (c0 : Fin 4)
    (c : W → Fin 4) (hc : I.IsGreedy c0 c) (v : W) (hv : (0 : Fin 4) ∈ I.L v) : c v = 0 ∨ ∃ u ∈ I.out v, c u = 0 := by
  have hvs : v ≠ I.sink := by
    rintro rfl
    exact ZeroFull.zero_notMem_L_sink I hg hv
  by_cases hcv : c v = 0
  · exact Or.inl hcv
  · right
    obtain ⟨u, hu, hcu⟩ := mem_image.1 (ZeroFull.zero_mem_used_of_ne (hc.2 v hvs) hv hcv)
    exact ⟨u, hu, hcu⟩

end Cereceda
