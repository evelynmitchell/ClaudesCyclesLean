/-
Copyright (c) 2026 Claude's Cycles Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Direction map for Claude's construction (Knuth, Feb 2026).
Assigns one of three directions (which coordinate to bump) to each vertex,
for each of the three Hamiltonian cycles.
-/
import ClaudesCycles.Defs

namespace ClaudesCycles

variable {m : ℕ} [NeZero m]

/-! ## Per-cycle direction functions

Each function maps a vertex to the direction (d0/d1/d2) that the given cycle
uses at that vertex.  The case split is on the fiber `s = i + j + k`:
  - `s = 0`:  the "top" level
  - `s = -1` (i.e. `m - 1`):  the "bottom" level
  - otherwise:  the "intermediate" levels

Within each level, a secondary condition on one coordinate selects between
two direction strings from Knuth's table.
-/

/-- Direction for cycle 0.
  - s = 0:  j = -1 → d0, else d2
  - s = -1: i ≠ 0 → d1, else d2
  - else:   i = -1 → d2, else d1 -/
def dirCycle0 (v : V m) : Dir :=
  let s := fiber v
  if s = 0 then
    if v.2.1 = -1 then .d0 else .d2
  else if s = -1 then
    if v.1 ≠ 0 then .d1 else .d2
  else
    if v.1 = -1 then .d2 else .d1

/-- Direction for cycle 1.
  - s = 0:  always d1
  - s = -1: i ≠ 0 → d2, else d1
  - else:   always d0 -/
def dirCycle1 (v : V m) : Dir :=
  let s := fiber v
  if s = 0 then .d1
  else if s = -1 then
    if v.1 ≠ 0 then .d2 else .d1
  else .d0

/-- Direction for cycle 2.
  - s = 0:  j ≠ -1 → d0, else d2
  - s = -1: always d0
  - else:   i ≠ -1 → d2, else d1 -/
def dirCycle2 (v : V m) : Dir :=
  let s := fiber v
  if s = 0 then
    if v.2.1 ≠ -1 then .d0 else .d2
  else if s = -1 then .d0
  else
    if v.1 ≠ -1 then .d2 else .d1

/-! ## Combined direction map -/

/-- The direction assigned to vertex `v` by cycle `c`. -/
def dirMap (c : CycleIndex) (v : V m) : Dir :=
  match c with
  | .c0 => dirCycle0 v
  | .c1 => dirCycle1 v
  | .c2 => dirCycle2 v

/-! ## Cycle step -/

/-- Advance vertex `v` by one step along cycle `c`. -/
def cycleStep (c : CycleIndex) (v : V m) : V m :=
  bump (dirMap c v) v

/-! ## Basic simp lemmas for dirMap -/

@[simp] theorem dirMap_c0 (v : V m) : dirMap .c0 v = dirCycle0 v := rfl
@[simp] theorem dirMap_c1 (v : V m) : dirMap .c1 v = dirCycle1 v := rfl
@[simp] theorem dirMap_c2 (v : V m) : dirMap .c2 v = dirCycle2 v := rfl

@[simp] theorem cycleStep_def (c : CycleIndex) (v : V m) :
    cycleStep c v = bump (dirMap c v) v := rfl

/-- The fiber advances by 1 at every cycle step. -/
@[simp] theorem fiber_cycleStep (c : CycleIndex) (v : V m) :
    fiber (cycleStep c v) = fiber v + 1 := fiber_bump _ _

end ClaudesCycles
