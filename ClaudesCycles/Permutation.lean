/-
Copyright (c) 2026 Claude's Cycles Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Permutation property: at every vertex, the three cycles assign three distinct
directions.  This means the three cycles together use all three outgoing arcs
at every vertex, i.e., they form an arc-disjoint decomposition.
-/
import ClaudesCycles.DirectionMap

namespace ClaudesCycles

variable {m : ℕ} [NeZero m]

/-! ## The three directions at each vertex are distinct

This is a case analysis on the six rows of the direction table.
Each row assigns a distinct permutation of {d0, d1, d2} to the three cycles.
No hypothesis on `m` is needed beyond `NeZero m`.
-/

/-- At every vertex, the direction map is injective in the cycle index:
    different cycles bump different coordinates. -/
theorem dirMap_injective (v : V m) :
    Function.Injective (fun c => dirMap c v) := by
  intro c₁ c₂ h
  unfold dirMap dirCycle0 dirCycle1 dirCycle2 at h
  cases c₁ <;> cases c₂ <;> simp_all
  all_goals split_ifs at h

/-- Corollary: the three directions assigned at any vertex are pairwise distinct. -/
theorem dirMap_ne_of_ne (v : V m) {c₁ c₂ : CycleIndex} (hc : c₁ ≠ c₂) :
    dirMap c₁ v ≠ dirMap c₂ v :=
  fun h => hc (dirMap_injective v h)

/-- The three cycle steps at any vertex produce three different successors. -/
theorem cycleStep_injective (v : V m) (hm : 1 < m) :
    Function.Injective (fun c => cycleStep c v) := by
  intro c₁ c₂ h
  simp only [cycleStep_def] at h
  have hdir := bump_injective_dir hm v h
  exact dirMap_injective v hdir

end ClaudesCycles
