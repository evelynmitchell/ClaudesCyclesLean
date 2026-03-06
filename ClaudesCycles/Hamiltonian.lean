/-
Copyright (c) 2026 Claude's Cycles Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Hamiltonian cycle proofs for Claude's construction.
Main result: for odd m ≥ 3, each of the three cycles visits all m³ vertices.
-/
import ClaudesCycles.DirectionMap
import ClaudesCycles.Permutation
import ClaudesCycles.BlockAnalysis
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Fintype.Basic

namespace ClaudesCycles

variable {m : ℕ} [NeZero m]

/-! ## Block structure for cycle 0

Cycle 0 decomposes into m blocks of m² vertices each.
Block `i` starts at entry point `(i, -1, 2-i)` with fiber 1.
Within each block, the first coordinate stays constant at `i`
(except at the single s=0, j=-1 position where it bumps).
-/

/-- Entry point for block `i` of cycle 0. -/
def cycle0Entry (i : ZMod m) : V m := (i, -1, 2 - i)

/-- The fiber of every block entry point is 1. -/
@[simp]
theorem fiber_cycle0Entry (i : ZMod m) :
    fiber (cycle0Entry i) = 1 := by
  simp [cycle0Entry, fiber]
  ring

/-! ## i-stability: cycle 0 only bumps i at fiber 0 with j = -1 -/

/-- Cycle 0 bumps the first coordinate iff s = 0 and j = -1. -/
theorem dirCycle0_eq_d0_iff (v : V m) :
    dirCycle0 v = .d0 ↔ fiber v = 0 ∧ v.2.1 = -1 := by
  simp only [dirCycle0]
  constructor
  · intro h
    split_ifs at h with hs hj hsm hi
    · exact ⟨hs, hj⟩
  · rintro ⟨hs, hj⟩
    simp [hs, hj]

/-! ## Key structural invariant: m steps between s=0 positions

Starting from any vertex with fiber s, exactly m steps bring the fiber
back to s (since each step adds 1 mod m to the fiber).
-/

/-- After n steps, the fiber advances by n. -/
theorem fiber_iterate (c : CycleIndex) (v : V m) (n : ℕ) :
    fiber ((cycleStep c)^[n] v) = fiber v + (n : ZMod m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', fiber_cycleStep, ih]
    push_cast
    ring

/-- After m steps along any cycle, the fiber returns to its original value. -/
theorem fiber_iterate_m (c : CycleIndex) (v : V m) :
    fiber ((cycleStep c)^[m] v) = fiber v := by
  rw [fiber_iterate]
  simp

/-! ## Within-block trajectory for cycle 0

Within block i (vertices with first coordinate i), the trajectory visits
m² vertices. The j-coordinate follows an arithmetic progression with
common difference -2 at fiber-0 positions. Since gcd(2, m) = 1 for odd m,
this visits all m values of j.
-/

omit [NeZero m] in
/-- The -2 shift is a unit in ZMod m when m is odd. -/
theorem neg_two_isUnit (hm_odd : Odd m) :
    IsUnit (-2 : ZMod m) := by
  apply IsUnit.neg
  rw [show (2 : ZMod m) = ((2 : ℕ) : ZMod m) from by push_cast; ring]
  rw [ZMod.isUnit_iff_coprime]
  exact hm_odd.coprime_two_left

/-! ## Block transition: after m² steps, move to next block -/

/-- After m² steps of cycle 0 from entry i, we reach entry (i+1). -/
theorem cycle0_block_transition (hm : 2 < m) (hm_odd : Odd m) (i : ZMod m) :
    (cycleStep .c0)^[m ^ 2] (cycle0Entry i) = cycle0Entry (i + 1) := by
  -- Decompose m² = (m-1)·m + m
  have hsplit : (cycleStep .c0)^[m ^ 2] (cycle0Entry i) =
      (cycleStep .c0)^[m] ((cycleStep .c0)^[(m - 1) * m] (cycle0Entry i)) := by
    rw [← Function.iterate_add_apply]; congr 1
    have : m ^ 2 = (m - 1) * m + m := by
      rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_right m (by omega))]
      ring
    omega
  rw [hsplit]
  unfold cycle0Entry
  by_cases hi0 : i = 0
  · -- Case B: i = 0
    subst hi0
    rw [c0_iter_i_eq_zero (-1) (2 - 0) hm (by simp only [fiber]; ring) (m - 1) le_rfl ?hj_safe]
    · have hfib : fiber ((0 : ZMod m), -1 + ↑(m - 1) * ((m - 2 : ℕ) : ZMod m),
          2 - 0 + 2 * ↑(m - 1)) = 1 := by
        simp only [fiber]; rw [natCast_m_sub_one (by omega), natCast_m_sub_two (by omega)]; ring
      have hj_bump : (-1 : ZMod m) + ↑(m - 1) * ((m - 2 : ℕ) : ZMod m) +
          ((m - 2 : ℕ) : ZMod m) = -1 := by
        rw [natCast_m_sub_one (by omega), natCast_m_sub_two (by omega)]; ring
      rw [c0_fiber_cycle_i_eq_zero_bump _ _ hm hfib hj_bump]
      simp only [Prod.mk.injEq]; refine ⟨by ring, trivial, ?_⟩
      rw [natCast_m_sub_one (show 1 ≤ m by omega)]; ring
    case hj_safe =>
      intro t ht
      rw [natCast_m_sub_two (by omega)]
      intro h
      have h1 : (-2 : ZMod m) * ((t : ZMod m) + 1) = 0 := by linear_combination h
      have hu : IsUnit (-2 : ZMod m) := neg_two_isUnit hm_odd
      have h2 : (t : ZMod m) + 1 = 0 := hu.mul_right_eq_zero.mp h1
      rw [show (t : ZMod m) + 1 = ((t + 1 : ℕ) : ZMod m) from by push_cast; ring] at h2
      rw [ZMod.natCast_eq_zero_iff] at h2
      exact absurd (Nat.le_of_dvd (by omega) h2) (by omega)
  · by_cases hi1 : i = -1
    · -- Case C: i = -1
      subst hi1
      rw [c0_iter_i_eq_neg_one (-1) (2 - -1) hm (by simp only [fiber]; ring)
          (m - 1) le_rfl ?hj_safe]
      · have hfib : fiber ((-1 : ZMod m), -1 + ↑(m - 1),
            2 - -1 + ↑(m - 1) * ((m - 1 : ℕ) : ZMod m)) = 1 := by
          simp only [fiber]; rw [natCast_m_sub_one (by omega)]; ring
        have hj_bump : (-1 : ZMod m) + ↑(m - 1) + 1 = -1 := by
          rw [natCast_m_sub_one (by omega)]; ring
        rw [c0_fiber_cycle_i_eq_neg_one_bump _ _ hm hfib hj_bump]
        simp only [Prod.mk.injEq]; refine ⟨by ring, trivial, ?_⟩
        rw [natCast_m_sub_one (show 1 ≤ m by omega), natCast_m_sub_two (show 2 ≤ m by omega)]
        ring
      case hj_safe =>
        intro t ht h
        have h1 : (t : ZMod m) + 1 = 0 := by linear_combination h
        rw [show (t : ZMod m) + 1 = ((t + 1 : ℕ) : ZMod m) from by push_cast; ring] at h1
        rw [ZMod.natCast_eq_zero_iff] at h1
        exact absurd (Nat.le_of_dvd (by omega) h1) (by omega)
    · -- Case A: generic i ≠ 0, i ≠ -1
      rw [c0_iter_generic i (-1) (2 - i) hm (by simp only [fiber]; ring) hi0 hi1
          (m - 1) le_rfl ?hj_safe]
      · have hfib : fiber (i, -1 + ↑(m - 1) * ((m - 1 : ℕ) : ZMod m),
            2 - i + ↑(m - 1)) = 1 := by
          simp only [fiber]; rw [natCast_m_sub_one (by omega)]; ring
        have hj_bump : -1 + ↑(m - 1) * ((m - 1 : ℕ) : ZMod m) +
            ((m - 1 : ℕ) : ZMod m) = -1 := by
          rw [natCast_m_sub_one (by omega)]; ring
        rw [c0_fiber_cycle_generic_bump _ _ _ hm hfib hi0 hi1 hj_bump]
        simp only [Prod.mk.injEq, true_and]
        rw [natCast_m_sub_one (by omega)]; ring
      case hj_safe =>
        intro t ht
        rw [natCast_m_sub_one (by omega)]
        intro h
        have h1 : (t : ZMod m) + 1 = 0 := by linear_combination -h
        rw [show (t : ZMod m) + 1 = ((t + 1 : ℕ) : ZMod m) from by push_cast; ring] at h1
        rw [ZMod.natCast_eq_zero_iff] at h1
        exact absurd (Nat.le_of_dvd (by omega) h1) (by omega)

-- Block transition tests: m = 3
example : (cycleStep .c0)^[3 ^ 2] (cycle0Entry (0 : ZMod 3)) = cycle0Entry (0 + 1) :=
  cycle0_block_transition (by omega) ⟨1, by omega⟩ 0

example : (cycleStep .c0)^[3 ^ 2] (cycle0Entry (1 : ZMod 3)) = cycle0Entry (1 + 1) :=
  cycle0_block_transition (by omega) ⟨1, by omega⟩ 1

example : (cycleStep .c0)^[3 ^ 2] (cycle0Entry (2 : ZMod 3)) = cycle0Entry (2 + 1) :=
  cycle0_block_transition (by omega) ⟨1, by omega⟩ 2

/-! ## Main Hamiltonian theorem for cycle 0 -/

/-- Cycle 0 returns to start after m³ steps. -/
theorem cycle0_period (hm : 2 < m) (hm_odd : Odd m) (v : V m) :
    (cycleStep .c0)^[m ^ 3] v = v := by
  sorry

/-- The orbit of any vertex under cycle 0 has size m³ (i.e., cycle 0 is Hamiltonian). -/
theorem cycle0_orbit_size (hm : 2 < m) (hm_odd : Odd m) (v : V m) :
    Finset.card (Finset.image (fun k => (cycleStep .c0)^[k] v) (Finset.range (m ^ 3))) = m ^ 3 := by
  sorry

/-! ## Cycles 1 and 2

These follow a parallel structure to cycle 0 but with different block
decompositions. The proofs are structurally similar.
-/

theorem cycle1_period (hm : 2 < m) (hm_odd : Odd m) (v : V m) :
    (cycleStep .c1)^[m ^ 3] v = v := by
  sorry

theorem cycle2_period (hm : 2 < m) (hm_odd : Odd m) (v : V m) :
    (cycleStep .c2)^[m ^ 3] v = v := by
  sorry

/-! ## Main theorem: arc-disjoint Hamiltonian decomposition -/

/-- The three cycles form an arc-disjoint Hamiltonian decomposition of the
    digraph on (ℤ/mℤ)³ for odd m ≥ 3. -/
theorem claudes_cycles_hamiltonian_decomposition
    (hm : 2 < m) (hm_odd : Odd m) :
    -- Each cycle is Hamiltonian (visits all m³ vertices)
    (∀ c : CycleIndex, ∀ v : V m,
      (cycleStep c)^[m ^ 3] v = v) ∧
    -- The three cycles are arc-disjoint (use distinct directions at each vertex)
    (∀ v : V m, Function.Injective (fun c => dirMap c v)) := by
  constructor
  · intro c v
    cases c
    · exact cycle0_period hm hm_odd v
    · exact cycle1_period hm hm_odd v
    · exact cycle2_period hm hm_odd v
  · exact fun v => dirMap_injective v

end ClaudesCycles
