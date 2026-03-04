/-
Copyright (c) 2026 Claude's Cycles Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Computational verification of Claude's construction for small values of m.
Uses `native_decide` to check that each cycle is a Hamiltonian cycle on (ℤ/mℤ)³.
-/
import ClaudesCycles.DirectionMap
import Mathlib.Data.Fintype.Basic

namespace ClaudesCycles

/-! ## Decidable instances and cardinality -/

instance {m : ℕ} [NeZero m] : DecidableEq (V m) :=
  inferInstanceAs (DecidableEq (ZMod m × ZMod m × ZMod m))

/-- The vertex set has exactly m³ elements. -/
theorem card_V (m : ℕ) [NeZero m] : Fintype.card (V m) = m ^ 3 := by
  simp [V, Fintype.card_prod, ZMod.card, pow_succ, pow_zero, mul_comm]

/-- Check that iterating `cycleStep c` from `v` for `n` steps returns to `v`. -/
def returnsInSteps {m : ℕ} [NeZero m] (c : CycleIndex) (v : V m) (n : ℕ) : Bool :=
  (cycleStep c)^[n] v == v

/-- Check that the orbit of `v` under `cycleStep c` has exactly `n` distinct elements. -/
def orbitSize {m : ℕ} [NeZero m] [Fintype (V m)] (c : CycleIndex) (v : V m) (n : ℕ) : Bool :=
  let orbit := (List.range n).map (fun k => (cycleStep c)^[k] v)
  orbit.Nodup && orbit.length == n

/-- Combined check: the orbit from `v` has size exactly `m³` and returns to start.
    Since `Fintype.card (V m) = m³` (see `card_V`), visiting m³ distinct vertices
    means the cycle is Hamiltonian. -/
def isHamiltonianFrom {m : ℕ} [NeZero m] [Fintype (V m)]
    (c : CycleIndex) (v : V m) : Bool :=
  let n := m ^ 3
  returnsInSteps c v n && orbitSize c v n

/-- Check that a cycle is Hamiltonian starting from the origin. -/
def cycleIsHamiltonian (m : ℕ) [NeZero m] [Fintype (V m)] (c : CycleIndex) : Bool :=
  isHamiltonianFrom c ((0 : ZMod m), (0 : ZMod m), (0 : ZMod m))

/-! ## Verification for m = 3

The digraph has 3³ = 27 vertices. Each cycle should visit all 27. -/

example : cycleIsHamiltonian 3 .c0 = true := by native_decide
example : cycleIsHamiltonian 3 .c1 = true := by native_decide
example : cycleIsHamiltonian 3 .c2 = true := by native_decide

/-! ## Verification for m = 5

The digraph has 5³ = 125 vertices. Each cycle should visit all 125. -/

example : cycleIsHamiltonian 5 .c0 = true := by native_decide
example : cycleIsHamiltonian 5 .c1 = true := by native_decide
example : cycleIsHamiltonian 5 .c2 = true := by native_decide

/-! ## Permutation property

The permutation property (three directions are always distinct at each vertex)
is proved in `Permutation.lean` as `dirMap_injective`, which holds for all m.
No computational check needed. -/

end ClaudesCycles
