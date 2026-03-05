/-
Copyright (c) 2026 Claude's Cycles Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Step-level lemmas for cycle 0's direction table.
Each lemma characterizes `cycleStep .c0` for one row of Knuth's table.
-/
import ClaudesCycles.DirectionMap

namespace ClaudesCycles

variable {m : ℕ} [NeZero m]

/-! ## Step-level lemmas for cycle 0

The direction table for cycle 0 has six rows, determined by the fiber
value `s = i + j + k` and a secondary coordinate condition.
-/

/-- Row 1: fiber = 0, j = -1 → bump i. -/
theorem c0_step_f0_jn1 (i j k : ZMod m)
    (hs : fiber (i, j, k) = 0) (hj : j = -1) :
    cycleStep .c0 (i, j, k) = (i + 1, j, k) := by
  simp only [cycleStep_def, dirMap_c0, dirCycle0, fiber] at *
  split_ifs; simp_all [bump]

/-- Row 2: fiber = 0, j ≠ -1 → bump k. -/
theorem c0_step_f0_jne (i j k : ZMod m)
    (hs : fiber (i, j, k) = 0) (hj : j ≠ -1) :
    cycleStep .c0 (i, j, k) = (i, j, k + 1) := by
  simp only [cycleStep_def, dirMap_c0, dirCycle0, fiber] at *
  split_ifs; simp_all [bump]

/-- Row 3: fiber = -1, i ≠ 0 → bump j. -/
theorem c0_step_fn1_ine (i j k : ZMod m)
    (hs : fiber (i, j, k) = -1) (hi : i ≠ 0) :
    cycleStep .c0 (i, j, k) = (i, j + 1, k) := by
  simp only [cycleStep_def, dirMap_c0, dirCycle0, fiber] at *
  split_ifs <;> simp_all [bump]

/-- Row 4: fiber = -1, i = 0 → bump k. -/
theorem c0_step_fn1_ieq (j k : ZMod m)
    (hs : fiber ((0 : ZMod m), j, k) = -1) :
    cycleStep .c0 ((0 : ZMod m), j, k) = (0, j, k + 1) := by
  simp only [cycleStep_def, dirMap_c0, dirCycle0, fiber] at *
  split_ifs <;> simp_all [bump]

/-- Row 5: intermediate fiber, i ≠ -1 → bump j. -/
theorem c0_step_mid_ine (i j k : ZMod m)
    (hs0 : fiber (i, j, k) ≠ 0) (hs1 : fiber (i, j, k) ≠ -1) (hi : i ≠ -1) :
    cycleStep .c0 (i, j, k) = (i, j + 1, k) := by
  simp only [cycleStep_def, dirMap_c0, dirCycle0, fiber] at *
  split_ifs <;> simp_all [bump]

/-- Row 6: intermediate fiber, i = -1 → bump k. -/
theorem c0_step_mid_ieq (j k : ZMod m)
    (hs0 : fiber ((-1 : ZMod m), j, k) ≠ 0)
    (hs1 : fiber ((-1 : ZMod m), j, k) ≠ -1) :
    cycleStep .c0 ((-1 : ZMod m), j, k) = (-1, j, k + 1) := by
  simp only [cycleStep_def, dirMap_c0, dirCycle0, fiber] at *
  split_ifs <;> simp_all [bump]

end ClaudesCycles
