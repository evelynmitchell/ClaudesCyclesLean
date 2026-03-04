/-
Copyright (c) 2026 Claude's Cycles Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Definitions for the Claude's Cycles construction from Knuth's paper (Feb 2026).
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Basic

namespace ClaudesCycles

/-! ## Basic types -/

/-- The vertex type: triples in (ℤ/mℤ)³. -/
abbrev V (m : ℕ) := ZMod m × ZMod m × ZMod m

/-- The three directions (which coordinate to bump). -/
inductive Dir : Type where
  | d0 : Dir  -- bump first coordinate (i)
  | d1 : Dir  -- bump second coordinate (j)
  | d2 : Dir  -- bump third coordinate (k)
  deriving DecidableEq, Repr

instance : Fintype Dir :=
  ⟨⟨[Dir.d0, Dir.d1, Dir.d2], by decide⟩, fun d => by cases d <;> decide⟩

/-- The three cycle indices. -/
inductive CycleIndex : Type where
  | c0 : CycleIndex
  | c1 : CycleIndex
  | c2 : CycleIndex
  deriving DecidableEq, Repr

instance : Fintype CycleIndex :=
  ⟨⟨[CycleIndex.c0, CycleIndex.c1, CycleIndex.c2], by decide⟩,
   fun c => by cases c <;> decide⟩

/-! ## Core operations -/

/-- Bump a vertex in the given direction (add 1 to one coordinate). -/
def bump {m : ℕ} [NeZero m] (d : Dir) (v : V m) : V m :=
  match d with
  | .d0 => (v.1 + 1, v.2.1, v.2.2)
  | .d1 => (v.1, v.2.1 + 1, v.2.2)
  | .d2 => (v.1, v.2.1, v.2.2 + 1)

/-- The fiber (sum of coordinates). This determines the "level" in the digraph. -/
def fiber {m : ℕ} [NeZero m] (v : V m) : ZMod m :=
  v.1 + v.2.1 + v.2.2

/-! ## Basic lemmas -/

@[simp]
theorem fiber_bump {m : ℕ} [NeZero m] (d : Dir) (v : V m) :
    fiber (bump d v) = fiber v + 1 := by
  cases d <;> simp [fiber, bump, add_assoc, add_comm, add_left_comm]

@[simp]
theorem bump_d0 {m : ℕ} [NeZero m] (v : V m) :
    bump Dir.d0 v = (v.1 + 1, v.2.1, v.2.2) := rfl

@[simp]
theorem bump_d1 {m : ℕ} [NeZero m] (v : V m) :
    bump Dir.d1 v = (v.1, v.2.1 + 1, v.2.2) := rfl

@[simp]
theorem bump_d2 {m : ℕ} [NeZero m] (v : V m) :
    bump Dir.d2 v = (v.1, v.2.1, v.2.2 + 1) := rfl

/-- 1 ≠ 0 in ZMod m when m > 1. -/
theorem one_ne_zero_of_one_lt {m : ℕ} [NeZero m] (hm : 1 < m) : (1 : ZMod m) ≠ 0 := by
  haveI : Fact (1 < m) := ⟨hm⟩
  exact one_ne_zero

/-- Bumping in different directions gives different results (when m ≥ 2). -/
theorem bump_injective_dir {m : ℕ} [NeZero m] (hm : 1 < m) (v : V m) :
    Function.Injective (fun d => bump d v) := by
  intro d₁ d₂ h
  have h1 : (1 : ZMod m) ≠ 0 := one_ne_zero_of_one_lt hm
  cases d₁ <;> cases d₂ <;> simp_all [bump, Prod.mk.injEq]

end ClaudesCycles
