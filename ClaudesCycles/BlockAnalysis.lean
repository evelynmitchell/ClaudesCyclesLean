/-
Copyright (c) 2026 Claude's Cycles Formalization Project.
Licensed under the Apache License, Version 2.0, as described in the file LICENSE.

Step-level lemmas for cycle 0's direction table.
Each lemma characterizes `cycleStep .c0` for one row of Knuth's table.
-/
import ClaudesCycles.DirectionMap
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.LinearCombination

namespace ClaudesCycles

variable {m : ℕ} [NeZero m]

/-! ## Step-level lemmas for cycle 0

The direction table for cycle 0 has six rows, determined by the fiber
value `s = i + j + k` and a secondary coordinate condition.

**Naming convention:** `c0_step_<fiber>_<coord>` where
- `f0` / `fn1` / `mid` = fiber is 0 / -1 / other
- `jn1` / `jne` / `ine` / `ieq` = secondary coordinate condition
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

/-! ## ZMod helper lemmas for fiber arithmetic

These lemmas support the intermediate run and block transition proofs.
-/

omit [NeZero m] in
theorem natCast_m_sub_one (hm : 1 ≤ m) : ((m - 1 : ℕ) : ZMod m) = -1 := by
  have h : ((m - 1 : ℕ) : ZMod m) + 1 = 0 := by
    have h1 : m - 1 + 1 = m := Nat.sub_add_cancel hm
    exact_mod_cast show ((m - 1 + 1 : ℕ) : ZMod m) = 0 by rw [h1]; exact ZMod.natCast_self m
  exact eq_neg_of_add_eq_zero_left h

omit [NeZero m] in
theorem natCast_m_sub_two (hm : 2 ≤ m) : ((m - 2 : ℕ) : ZMod m) = -2 := by
  have h : ((m - 2 : ℕ) : ZMod m) + 2 = 0 := by
    have h1 : m - 2 + 2 = m := Nat.sub_add_cancel hm
    exact_mod_cast show ((m - 2 + 2 : ℕ) : ZMod m) = 0 by rw [h1]; exact ZMod.natCast_self m
  exact eq_neg_of_add_eq_zero_left h

omit [NeZero m] in
theorem one_ne_neg_one [Fact (2 < m)] : (1 : ZMod m) ≠ -1 :=
  (ZMod.neg_one_ne_one (n := m)).symm

omit [NeZero m] in
theorem natCast_ne_zero {n : ℕ} (hn : n < m - 1) : ((1 + n : ℕ) : ZMod m) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have := Nat.le_of_dvd (by omega) h
  omega

omit [NeZero m] in
theorem natCast_ne_neg_one {n : ℕ} (hm : 2 ≤ m) (hn : n < m - 2) :
    ((1 + n : ℕ) : ZMod m) ≠ -1 := by
  obtain ⟨m', rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  intro h
  have hlt : (1 + n : ℕ) < m' + 1 := by omega
  have hv : ((1 + n : ℕ) : ZMod (m' + 1)).val = 1 + n := ZMod.val_natCast_of_lt hlt
  have hv2 : ((-1 : ZMod (m' + 1))).val = m' := ZMod.val_neg_one m'
  have := congr_arg ZMod.val h
  rw [hv, hv2] at this
  omega

/-! ## Intermediate run lemmas for cycle 0

Starting at fiber 1, consecutive steps through intermediate fibers
(1 through m−2) just bump one coordinate repeatedly.
-/

private lemma fiber_add_j (i j k n : ZMod m) : fiber (i, j + n, k) = fiber (i, j, k) + n := by
  simp [fiber]; ring

private lemma fiber_add_k (i j k n : ZMod m) : fiber (i, j, k + n) = fiber (i, j, k) + n := by
  simp [fiber]; ring

/-- i ≠ -1: each intermediate step bumps j. -/
theorem c0_intermediate_run_bump_j (i j k : ZMod m) (hm : 2 < m)
    (hfib : fiber (i, j, k) = 1) (hi : i ≠ -1) (n : ℕ) (hn : n ≤ m - 2) :
    (cycleStep .c0)^[n] (i, j, k) = (i, j + (n : ZMod m), k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn' : n ≤ m - 2 := by omega
    rw [Function.iterate_succ_apply', ih hn']
    have hfib_n : fiber (i, j + (n : ZMod m), k) = ((1 + n : ℕ) : ZMod m) := by
      rw [fiber_add_j, hfib]; push_cast; ring
    have h0 : fiber (i, j + (n : ZMod m), k) ≠ 0 := by
      rw [hfib_n]; exact natCast_ne_zero (by omega)
    have h1 : fiber (i, j + (n : ZMod m), k) ≠ -1 := by
      rw [hfib_n]; exact natCast_ne_neg_one (by omega) (by omega)
    rw [c0_step_mid_ine _ _ _ h0 h1 hi]
    push_cast; ring_nf

/-- i = -1: each intermediate step bumps k. -/
theorem c0_intermediate_run_bump_k (j k : ZMod m) (hm : 2 < m)
    (hfib : fiber ((-1 : ZMod m), j, k) = 1) (n : ℕ) (hn : n ≤ m - 2) :
    (cycleStep .c0)^[n] ((-1 : ZMod m), j, k) = (-1, j, k + (n : ZMod m)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn' : n ≤ m - 2 := by omega
    rw [Function.iterate_succ_apply', ih hn']
    have hfib_n : fiber ((-1 : ZMod m), j, k + (n : ZMod m)) = ((1 + n : ℕ) : ZMod m) := by
      rw [fiber_add_k, hfib]; push_cast; ring
    have h0 : fiber ((-1 : ZMod m), j, k + (n : ZMod m)) ≠ 0 := by
      rw [hfib_n]; exact natCast_ne_zero (by omega)
    have h1 : fiber ((-1 : ZMod m), j, k + (n : ZMod m)) ≠ -1 := by
      rw [hfib_n]; exact natCast_ne_neg_one (by omega) (by omega)
    rw [c0_step_mid_ieq _ _ h0 h1]
    push_cast; ring_nf

/-! ## Single fiber cycle lemmas for cycle 0

Starting at fiber 1, after m steps (one complete fiber cycle) we return
to fiber 1.  The net coordinate shift depends on i.  Each proof
decomposes m = (m−2) + 1 + 1: intermediate run, fiber −1 step, fiber 0 step.
-/

omit [NeZero m] in
theorem neg_one_ne_zero_of_one_lt (hm : 1 < m) : (-1 : ZMod m) ≠ 0 := by
  haveI : NeZero m := ⟨by omega⟩
  haveI : Fact (1 < m) := ⟨hm⟩
  exact neg_ne_zero.mpr one_ne_zero

/-- Case A: generic i (i ≠ 0, i ≠ -1). Net shift: j → j - 1, k → k + 1. -/
theorem c0_fiber_cycle_generic (i j k : ZMod m) (hm : 2 < m)
    (hfib : fiber (i, j, k) = 1) (hi0 : i ≠ 0) (hi1 : i ≠ -1)
    (hj_no_bump : j + ((m - 1 : ℕ) : ZMod m) ≠ -1) :
    (cycleStep .c0)^[m] (i, j, k) = (i, j + ((m - 1 : ℕ) : ZMod m), k + 1) := by
  have hm_split : (cycleStep .c0)^[m] (i, j, k) =
      (cycleStep .c0)^[1] ((cycleStep .c0)^[1]
        ((cycleStep .c0)^[m - 2] (i, j, k))) := by
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]; congr 1; omega
  rw [hm_split, c0_intermediate_run_bump_j i j k hm hfib hi1 (m - 2) (le_refl _)]
  -- Phase 2: fiber = -1, i ≠ 0 → bump j
  have hfib_n1 : fiber (i, j + ((m - 2 : ℕ) : ZMod m), k) = -1 := by
    rw [fiber_add_j, hfib, natCast_m_sub_two (by omega)]; ring
  rw [Function.iterate_one, c0_step_fn1_ine _ _ _ hfib_n1 hi0]
  -- Phase 3: fiber = 0, j + (m-2) + 1 ≠ -1 → bump k
  have hfib_0 : fiber (i, j + ((m - 2 : ℕ) : ZMod m) + 1, k) = 0 := by
    rw [fiber_add_j, fiber_add_j, hfib, natCast_m_sub_two (by omega)]; ring
  have hj' : j + ((m - 2 : ℕ) : ZMod m) + 1 ≠ -1 := by
    rw [natCast_m_sub_two (by omega)]
    rw [show j + (-2 : ZMod m) + 1 = j + ((m - 1 : ℕ) : ZMod m) from by
      rw [natCast_m_sub_one (by omega)]; ring]
    exact hj_no_bump
  rw [c0_step_f0_jne _ _ _ hfib_0 hj']
  congr 1; congr 1
  rw [natCast_m_sub_two (by omega), natCast_m_sub_one (by omega)]; ring

/-- Case B: i = 0. Net shift: j → j - 2, k → k + 2. -/
theorem c0_fiber_cycle_i_eq_zero (j k : ZMod m) (hm : 2 < m)
    (hfib : fiber ((0 : ZMod m), j, k) = 1) (hj : j ≠ 1) :
    (cycleStep .c0)^[m] ((0 : ZMod m), j, k) =
      (0, j + ((m - 2 : ℕ) : ZMod m), k + 2) := by
  have hi1 : (0 : ZMod m) ≠ -1 := Ne.symm (neg_one_ne_zero_of_one_lt (by omega))
  have hm_split : (cycleStep .c0)^[m] ((0 : ZMod m), j, k) =
      (cycleStep .c0)^[1] ((cycleStep .c0)^[1]
        ((cycleStep .c0)^[m - 2] ((0 : ZMod m), j, k))) := by
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]; congr 1; omega
  rw [hm_split, c0_intermediate_run_bump_j _ j k hm hfib hi1 (m - 2) (le_refl _)]
  -- Phase 2: fiber = -1, i = 0 → bump k (not j)
  have hfib_n1 : fiber ((0 : ZMod m), j + ((m - 2 : ℕ) : ZMod m), k) = -1 := by
    rw [fiber_add_j, hfib, natCast_m_sub_two (by omega)]; ring
  rw [Function.iterate_one, c0_step_fn1_ieq _ _ hfib_n1]
  -- Phase 3: fiber = 0, j + (m-2) ≠ -1 → bump k
  have hfib_0 : fiber ((0 : ZMod m), j + ((m - 2 : ℕ) : ZMod m), k + 1) = 0 := by
    rw [fiber_add_k, fiber_add_j, hfib, natCast_m_sub_two (by omega)]; ring
  have hj' : j + ((m - 2 : ℕ) : ZMod m) ≠ -1 := by
    rw [natCast_m_sub_two (by omega)]
    intro h; apply hj; linear_combination h
  rw [c0_step_f0_jne _ _ _ hfib_0 hj']
  simp only [Prod.mk.injEq]; exact ⟨trivial, trivial, by ring⟩

/-- Case C: i = -1. Net shift: j → j + 1, k → k - 1. -/
theorem c0_fiber_cycle_i_eq_neg_one (j k : ZMod m) (hm : 2 < m)
    (hfib : fiber ((-1 : ZMod m), j, k) = 1) (hj : j ≠ -2) :
    (cycleStep .c0)^[m] ((-1 : ZMod m), j, k) =
      (-1, j + 1, k + ((m - 1 : ℕ) : ZMod m)) := by
  have hi0 : (-1 : ZMod m) ≠ 0 := neg_one_ne_zero_of_one_lt (by omega)
  have hm_split : (cycleStep .c0)^[m] ((-1 : ZMod m), j, k) =
      (cycleStep .c0)^[1] ((cycleStep .c0)^[1]
        ((cycleStep .c0)^[m - 2] ((-1 : ZMod m), j, k))) := by
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]; congr 1; omega
  rw [hm_split, c0_intermediate_run_bump_k j k hm hfib (m - 2) (le_refl _)]
  -- Phase 2: fiber = -1, i = -1 ≠ 0 → bump j
  have hfib_n1 : fiber ((-1 : ZMod m), j, k + ((m - 2 : ℕ) : ZMod m)) = -1 := by
    rw [fiber_add_k, hfib, natCast_m_sub_two (by omega)]; ring
  rw [Function.iterate_one, c0_step_fn1_ine _ _ _ hfib_n1 hi0]
  -- Phase 3: fiber = 0, j + 1 ≠ -1 → bump k
  have hfib_0 : fiber ((-1 : ZMod m), j + 1, k + ((m - 2 : ℕ) : ZMod m)) = 0 := by
    rw [fiber_add_j, fiber_add_k, hfib, natCast_m_sub_two (by omega)]; ring
  have hj' : j + 1 ≠ -1 := by
    intro h; apply hj; linear_combination h
  rw [c0_step_f0_jne _ _ _ hfib_0 hj']
  congr 1; congr 1
  rw [natCast_m_sub_two (by omega), natCast_m_sub_one (by omega)]; ring

/-! ## Tests -/

example : ((4 : ℕ) : ZMod 5) = -1 := natCast_m_sub_one (m := 5) (by omega)
example : ((3 : ℕ) : ZMod 5) = -2 := natCast_m_sub_two (m := 5) (by omega)
example : (1 : ZMod 5) ≠ -1 := @one_ne_neg_one 5 ⟨by omega⟩
example : ((1 + 0 : ℕ) : ZMod 5) ≠ 0 := natCast_ne_zero (m := 5) (by omega)
example : ((1 + 1 : ℕ) : ZMod 5) ≠ -1 := natCast_ne_neg_one (m := 5) (by omega) (by omega)

example : (cycleStep .c0)^[3] ((0 : ZMod 5), -1, (2 : ZMod 5)) =
    ((0 : ZMod 5), -1 + (3 : ZMod 5), (2 : ZMod 5)) :=
  c0_intermediate_run_bump_j (m := 5) _ _ _
    (by omega) (by simp [fiber]; ring) (by decide) 3 (by omega)

example : (cycleStep .c0)^[3] ((-1 : ZMod 5), (0 : ZMod 5), (2 : ZMod 5)) =
    ((-1 : ZMod 5), (0 : ZMod 5), 2 + (3 : ZMod 5)) :=
  c0_intermediate_run_bump_k (m := 5) _ _
    (by omega) (by simp [fiber]; ring) 3 (by omega)

/-! ## Iterated fiber cycle lemmas for cycle 0

After n complete fiber cycles (n·m steps), j and k follow arithmetic
progressions.  The `hj_safe` hypothesis ensures no i-bump occurs at
fiber 0 during any of the n cycles.

Note: the `hn : n ≤ m - 1` bound is not used in these proofs directly,
but is included so that downstream consumers (block transition, #8) can
discharge `hj_safe` via `hn` without needing to re-state the bound.
-/

/-- Case A iterated: generic i. Each cycle shifts j by (m-1) and k by 1. -/
theorem c0_iter_generic (i j k : ZMod m) (hm : 2 < m)
    (hfib : fiber (i, j, k) = 1) (hi0 : i ≠ 0) (hi1 : i ≠ -1)
    (n : ℕ) (hn : n ≤ m - 1)
    (hj_safe : ∀ t : ℕ, t < n →
      j + (t : ZMod m) * ((m - 1 : ℕ) : ZMod m) + ((m - 1 : ℕ) : ZMod m) ≠ -1) :
    (cycleStep .c0)^[n * m] (i, j, k) =
      (i, j + (n : ZMod m) * ((m - 1 : ℕ) : ZMod m), k + (n : ZMod m)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn' : n ≤ m - 1 := by omega
    have hsplit : (cycleStep .c0)^[(n + 1) * m] (i, j, k) =
        (cycleStep .c0)^[m] ((cycleStep .c0)^[n * m] (i, j, k)) := by
      rw [← Function.iterate_add_apply]; congr 1; ring
    rw [hsplit, ih hn' (fun t ht => hj_safe t (by omega))]
    have hfib' : fiber (i, j + (n : ZMod m) * ((m - 1 : ℕ) : ZMod m), k + (n : ZMod m)) = 1 := by
      rw [fiber_add_k, fiber_add_j, hfib, natCast_m_sub_one (by omega)]; ring
    rw [c0_fiber_cycle_generic _ _ _ hm hfib' hi0 hi1 (hj_safe n (by omega))]
    simp only [Prod.mk.injEq]; exact ⟨trivial, by push_cast; ring, by push_cast; ring⟩

/-- Case B iterated: i = 0. Each cycle shifts j by (m-2) and k by 2. -/
theorem c0_iter_i_eq_zero (j k : ZMod m) (hm : 2 < m)
    (hfib : fiber ((0 : ZMod m), j, k) = 1)
    (n : ℕ) (hn : n ≤ m - 1)
    (hj_safe : ∀ t : ℕ, t < n →
      j + (t : ZMod m) * ((m - 2 : ℕ) : ZMod m) + ((m - 2 : ℕ) : ZMod m) ≠ -1) :
    (cycleStep .c0)^[n * m] ((0 : ZMod m), j, k) =
      (0, j + (n : ZMod m) * ((m - 2 : ℕ) : ZMod m), k + 2 * (n : ZMod m)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn' : n ≤ m - 1 := by omega
    have hsplit : (cycleStep .c0)^[(n + 1) * m] ((0 : ZMod m), j, k) =
        (cycleStep .c0)^[m] ((cycleStep .c0)^[n * m] ((0 : ZMod m), j, k)) := by
      rw [← Function.iterate_add_apply]; congr 1; ring
    rw [hsplit, ih hn' (fun t ht => hj_safe t (by omega))]
    have hfib' : fiber ((0 : ZMod m), j + (n : ZMod m) * ((m - 2 : ℕ) : ZMod m),
        k + 2 * (n : ZMod m)) = 1 := by
      rw [fiber_add_k, fiber_add_j, hfib, natCast_m_sub_two (by omega)]; ring
    have hj' : j + (↑n * ((m - 2 : ℕ) : ZMod m)) ≠ 1 := by
      intro h
      exact hj_safe n (by omega) (by
        rw [natCast_m_sub_two (by omega)] at h ⊢; linear_combination h)
    rw [c0_fiber_cycle_i_eq_zero _ _ hm hfib' hj']
    simp only [Prod.mk.injEq]; exact ⟨trivial, by push_cast; ring, by push_cast; ring⟩

/-- Case C iterated: i = -1. Each cycle shifts j by 1 and k by (m-1). -/
theorem c0_iter_i_eq_neg_one (j k : ZMod m) (hm : 2 < m)
    (hfib : fiber ((-1 : ZMod m), j, k) = 1)
    (n : ℕ) (hn : n ≤ m - 1)
    (hj_safe : ∀ t : ℕ, t < n →
      j + (t : ZMod m) + 1 ≠ -1) :
    (cycleStep .c0)^[n * m] ((-1 : ZMod m), j, k) =
      (-1, j + (n : ZMod m), k + (n : ZMod m) * ((m - 1 : ℕ) : ZMod m)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn' : n ≤ m - 1 := by omega
    have hsplit : (cycleStep .c0)^[(n + 1) * m] ((-1 : ZMod m), j, k) =
        (cycleStep .c0)^[m] ((cycleStep .c0)^[n * m] ((-1 : ZMod m), j, k)) := by
      rw [← Function.iterate_add_apply]; congr 1; ring
    rw [hsplit, ih hn' (fun t ht => hj_safe t (by omega))]
    have hfib' : fiber ((-1 : ZMod m), j + (n : ZMod m),
        k + (n : ZMod m) * ((m - 1 : ℕ) : ZMod m)) = 1 := by
      rw [fiber_add_k, fiber_add_j, hfib, natCast_m_sub_one (by omega)]; ring
    have hj' : j + (n : ZMod m) ≠ -2 := by
      intro h
      exact hj_safe n (by omega) (by linear_combination h)
    rw [c0_fiber_cycle_i_eq_neg_one _ _ hm hfib' hj']
    simp only [Prod.mk.injEq]; exact ⟨trivial, by push_cast; ring, by push_cast; ring⟩

-- Iterated: Case A, m = 5, 2 cycles from (2, 2, 2), fiber = 6 = 1
example : (cycleStep .c0)^[2 * 5] ((2 : ZMod 5), (2 : ZMod 5), (2 : ZMod 5)) =
    ((2 : ZMod 5), 2 + (2 : ZMod 5) * ((4 : ℕ) : ZMod 5), (2 : ZMod 5) + (2 : ZMod 5)) := by
  refine c0_iter_generic (m := 5) _ _ _ (by omega) (by decide)
    (by decide) (by decide) 2 (by omega) ?_
  intro t ht
  have : t = 0 ∨ t = 1 := by omega
  rcases this with rfl | rfl <;> decide

-- Iterated: Case B, m = 5, 2 cycles from (0, 2, 4), fiber = 6 = 1
example : (cycleStep .c0)^[2 * 5] ((0 : ZMod 5), (2 : ZMod 5), (4 : ZMod 5)) =
    ((0 : ZMod 5), 2 + (2 : ZMod 5) * ((3 : ℕ) : ZMod 5), (4 : ZMod 5) + 2 * (2 : ZMod 5)) := by
  refine c0_iter_i_eq_zero (m := 5) _ _ (by omega) (by decide)
    2 (by omega) ?_
  intro t ht
  have : t = 0 ∨ t = 1 := by omega
  rcases this with rfl | rfl <;> decide

-- Iterated: Case C, m = 5, 2 cycles from (-1, 0, 2), fiber = 1
example : (cycleStep .c0)^[2 * 5] ((-1 : ZMod 5), (0 : ZMod 5), (2 : ZMod 5)) =
    ((-1 : ZMod 5), 0 + (2 : ZMod 5), (2 : ZMod 5) + (2 : ZMod 5) * ((4 : ℕ) : ZMod 5)) := by
  refine c0_iter_i_eq_neg_one (m := 5) _ _ (by omega) (by decide)
    2 (by omega) ?_
  intro t ht
  have : t = 0 ∨ t = 1 := by omega
  rcases this with rfl | rfl <;> decide

-- Fiber cycle: Case A, m = 5, point (2, 1, 3) on fiber 1
example : (cycleStep .c0)^[5] ((2 : ZMod 5), (1 : ZMod 5), (3 : ZMod 5)) =
    ((2 : ZMod 5), 1 + ((4 : ℕ) : ZMod 5), (3 : ZMod 5) + 1) :=
  c0_fiber_cycle_generic (m := 5) _ _ _ (by omega) (by decide)
    (by decide) (by decide) (by decide)

-- Fiber cycle: Case B, m = 5, point (0, 3, 3) on fiber 1
example : (cycleStep .c0)^[5] ((0 : ZMod 5), (3 : ZMod 5), (3 : ZMod 5)) =
    ((0 : ZMod 5), 3 + ((3 : ℕ) : ZMod 5), (3 : ZMod 5) + 2) :=
  c0_fiber_cycle_i_eq_zero (m := 5) _ _ (by omega) (by decide)
    (by decide)

-- Fiber cycle: Case C, m = 5, point (-1, 0, 2) on fiber 1
example : (cycleStep .c0)^[5] ((-1 : ZMod 5), (0 : ZMod 5), (2 : ZMod 5)) =
    ((-1 : ZMod 5), 0 + 1, (2 : ZMod 5) + ((4 : ℕ) : ZMod 5)) :=
  c0_fiber_cycle_i_eq_neg_one (m := 5) _ _ (by omega) (by decide)
    (by decide)

-- Fiber cycle: Case A, m = 3 (smallest valid m), point (1, 1, 2) on fiber 1
example : (cycleStep .c0)^[3] ((1 : ZMod 3), (1 : ZMod 3), (2 : ZMod 3)) =
    ((1 : ZMod 3), 1 + ((2 : ℕ) : ZMod 3), (2 : ZMod 3) + 1) :=
  c0_fiber_cycle_generic (m := 3) _ _ _ (by omega) (by decide)
    (by decide) (by decide) (by decide)

/-! ## Bumping fiber cycle lemmas for cycle 0

Starting at fiber 1, after m steps where j lands on -1 at fiber 0,
the i-coordinate bumps.  These handle the boundary case excluded by
the non-bumping `c0_fiber_cycle_*` lemmas above.
-/

/-- Case A bump: generic i (i ≠ 0, i ≠ -1), j + (m-1) = -1 → i bumps. -/
theorem c0_fiber_cycle_generic_bump (i j k : ZMod m) (hm : 2 < m)
    (hfib : fiber (i, j, k) = 1) (hi0 : i ≠ 0) (hi1 : i ≠ -1)
    (hj_bump : j + ((m - 1 : ℕ) : ZMod m) = -1) :
    (cycleStep .c0)^[m] (i, j, k) = (i + 1, -1, k) := by
  have hm_split : (cycleStep .c0)^[m] (i, j, k) =
      (cycleStep .c0)^[1] ((cycleStep .c0)^[1]
        ((cycleStep .c0)^[m - 2] (i, j, k))) := by
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]; congr 1; omega
  rw [hm_split, c0_intermediate_run_bump_j i j k hm hfib hi1 (m - 2) (le_refl _)]
  -- Phase 2: fiber = -1, i ≠ 0 → bump j
  have hfib_n1 : fiber (i, j + ((m - 2 : ℕ) : ZMod m), k) = -1 := by
    rw [fiber_add_j, hfib, natCast_m_sub_two (by omega)]; ring
  rw [Function.iterate_one, c0_step_fn1_ine _ _ _ hfib_n1 hi0]
  -- Phase 3: fiber = 0, j + (m-2) + 1 = j + (m-1) = -1 → bump i
  have hfib_0 : fiber (i, j + ((m - 2 : ℕ) : ZMod m) + 1, k) = 0 := by
    rw [fiber_add_j, fiber_add_j, hfib, natCast_m_sub_two (by omega)]; ring
  have hj' : j + ((m - 2 : ℕ) : ZMod m) + 1 = -1 := by
    rw [natCast_m_sub_two (by omega)]
    rw [show j + (-2 : ZMod m) + 1 = j + ((m - 1 : ℕ) : ZMod m) from by
      rw [natCast_m_sub_one (by omega)]; ring]
    exact hj_bump
  rw [c0_step_f0_jn1 _ _ _ hfib_0 hj', hj']

/-- Case B bump: i = 0, j + (m-2) = -1 → i bumps. -/
theorem c0_fiber_cycle_i_eq_zero_bump (j k : ZMod m) (hm : 2 < m)
    (hfib : fiber ((0 : ZMod m), j, k) = 1)
    (hj_bump : j + ((m - 2 : ℕ) : ZMod m) = -1) :
    (cycleStep .c0)^[m] ((0 : ZMod m), j, k) = (1, -1, k + 1) := by
  have hi1 : (0 : ZMod m) ≠ -1 := Ne.symm (neg_one_ne_zero_of_one_lt (by omega))
  have hm_split : (cycleStep .c0)^[m] ((0 : ZMod m), j, k) =
      (cycleStep .c0)^[1] ((cycleStep .c0)^[1]
        ((cycleStep .c0)^[m - 2] ((0 : ZMod m), j, k))) := by
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]; congr 1; omega
  rw [hm_split, c0_intermediate_run_bump_j _ j k hm hfib hi1 (m - 2) (le_refl _)]
  -- Phase 2: fiber = -1, i = 0 → bump k (not j)
  have hfib_n1 : fiber ((0 : ZMod m), j + ((m - 2 : ℕ) : ZMod m), k) = -1 := by
    rw [fiber_add_j, hfib, natCast_m_sub_two (by omega)]; ring
  rw [Function.iterate_one, c0_step_fn1_ieq _ _ hfib_n1]
  -- Phase 3: fiber = 0, j + (m-2) = -1 → bump i
  have hfib_0 : fiber ((0 : ZMod m), j + ((m - 2 : ℕ) : ZMod m), k + 1) = 0 := by
    rw [fiber_add_k, fiber_add_j, hfib, natCast_m_sub_two (by omega)]; ring
  rw [c0_step_f0_jn1 _ _ _ hfib_0 hj_bump, hj_bump]
  simp only [Prod.mk.injEq, and_true]; ring

/-- Case C bump: i = -1, j + 1 = -1 → i bumps. -/
theorem c0_fiber_cycle_i_eq_neg_one_bump (j k : ZMod m) (hm : 2 < m)
    (hfib : fiber ((-1 : ZMod m), j, k) = 1)
    (hj_bump : j + 1 = -1) :
    (cycleStep .c0)^[m] ((-1 : ZMod m), j, k) = (0, -1, k + ((m - 2 : ℕ) : ZMod m)) := by
  have hi0 : (-1 : ZMod m) ≠ 0 := neg_one_ne_zero_of_one_lt (by omega)
  have hm_split : (cycleStep .c0)^[m] ((-1 : ZMod m), j, k) =
      (cycleStep .c0)^[1] ((cycleStep .c0)^[1]
        ((cycleStep .c0)^[m - 2] ((-1 : ZMod m), j, k))) := by
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]; congr 1; omega
  rw [hm_split, c0_intermediate_run_bump_k j k hm hfib (m - 2) (le_refl _)]
  -- Phase 2: fiber = -1, i = -1 ≠ 0 → bump j
  have hfib_n1 : fiber ((-1 : ZMod m), j, k + ((m - 2 : ℕ) : ZMod m)) = -1 := by
    rw [fiber_add_k, hfib, natCast_m_sub_two (by omega)]; ring
  rw [Function.iterate_one, c0_step_fn1_ine _ _ _ hfib_n1 hi0]
  -- Phase 3: fiber = 0, j + 1 = -1 → bump i
  have hfib_0 : fiber ((-1 : ZMod m), j + 1, k + ((m - 2 : ℕ) : ZMod m)) = 0 := by
    rw [fiber_add_j, fiber_add_k, hfib, natCast_m_sub_two (by omega)]; ring
  rw [c0_step_f0_jn1 _ _ _ hfib_0 hj_bump, hj_bump]
  simp only [Prod.mk.injEq, and_true]; ring

/-! ## Shared helper: -2 is a unit in ZMod m for odd m -/

omit [NeZero m] in
/-- The -2 shift is a unit in ZMod m when m is odd. -/
theorem neg_two_isUnit (hm_odd : Odd m) :
    IsUnit (-2 : ZMod m) := by
  haveI : NeZero m := ⟨by obtain ⟨k, hk⟩ := hm_odd; omega⟩
  apply IsUnit.neg
  rw [show (2 : ZMod m) = ((2 : ℕ) : ZMod m) from by push_cast; ring]
  rw [ZMod.isUnit_iff_coprime]
  exact hm_odd.coprime_two_left

/-! ## Step-level lemmas for cycle 1

The direction table for cycle 1 has four rows, determined by the fiber
value `s = i + j + k` and whether `i = 0` at fiber -1.

**Naming convention:** `c1_step_<fiber>_<condition>`
-/

/-- Cycle 1, fiber = 0 → bump j. -/
theorem c1_step_f0 (i j k : ZMod m)
    (hs : fiber (i, j, k) = 0) :
    cycleStep .c1 (i, j, k) = (i, j + 1, k) := by
  simp only [cycleStep_def, dirMap_c1, dirCycle1, fiber] at *
  split_ifs; simp_all [bump]

/-- Cycle 1, fiber = -1, i ≠ 0 → bump k. -/
theorem c1_step_fn1_ine (i j k : ZMod m)
    (hs : fiber (i, j, k) = -1) (hi : i ≠ 0) :
    cycleStep .c1 (i, j, k) = (i, j, k + 1) := by
  simp only [cycleStep_def, dirMap_c1, dirCycle1, fiber] at *
  split_ifs <;> simp_all [bump]

/-- Cycle 1, fiber = -1, i = 0 → bump j. -/
theorem c1_step_fn1_ieq (j k : ZMod m)
    (hs : fiber ((0 : ZMod m), j, k) = -1) :
    cycleStep .c1 ((0 : ZMod m), j, k) = (0, j + 1, k) := by
  simp only [cycleStep_def, dirMap_c1, dirCycle1, fiber] at *
  split_ifs <;> simp_all [bump]

/-- Cycle 1, intermediate fiber → bump i. -/
theorem c1_step_mid (i j k : ZMod m)
    (hs0 : fiber (i, j, k) ≠ 0) (hs1 : fiber (i, j, k) ≠ -1) :
    cycleStep .c1 (i, j, k) = (i + 1, j, k) := by
  simp only [cycleStep_def, dirMap_c1, dirCycle1, fiber] at *
  split_ifs <;> simp_all [bump]

/-! ## Intermediate run for cycle 1

Starting at fiber 1, consecutive steps through intermediate fibers
just bump i (uniform — no case split on coordinates).
-/

private lemma fiber_add_i (i j k n : ZMod m) : fiber (i + n, j, k) = fiber (i, j, k) + n := by
  simp [fiber]; ring

/-- Each intermediate step bumps i. -/
theorem c1_intermediate_run (i j k : ZMod m) (hm : 2 < m)
    (hfib : fiber (i, j, k) = 1) (n : ℕ) (hn : n ≤ m - 2) :
    (cycleStep .c1)^[n] (i, j, k) = (i + (n : ZMod m), j, k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn' : n ≤ m - 2 := by omega
    rw [Function.iterate_succ_apply', ih hn']
    have hfib_n : fiber (i + (n : ZMod m), j, k) = ((1 + n : ℕ) : ZMod m) := by
      rw [fiber_add_i, hfib]; push_cast; ring
    have h0 : fiber (i + (n : ZMod m), j, k) ≠ 0 := by
      rw [hfib_n]; exact natCast_ne_zero (by omega)
    have h1 : fiber (i + (n : ZMod m), j, k) ≠ -1 := by
      rw [hfib_n]; exact natCast_ne_neg_one (by omega) (by omega)
    rw [c1_step_mid _ _ _ h0 h1]
    push_cast; ring_nf

/-! ## Single fiber cycle lemmas for cycle 1

Starting at fiber 1, after m steps (one complete fiber cycle) we return
to fiber 1.  The net shift depends on whether `i + (m-2) = 0` (i.e., `i = 2`).
-/

/-- Non-bump case: i ≠ 2. Net shift: i → i-2, j → j+1, k → k+1. -/
theorem c1_fiber_cycle_non_bump (i j k : ZMod m) (hm : 2 < m)
    (hfib : fiber (i, j, k) = 1) (hi : i ≠ 2) :
    (cycleStep .c1)^[m] (i, j, k) =
      (i + ((m - 2 : ℕ) : ZMod m), j + 1, k + 1) := by
  have hm_split : (cycleStep .c1)^[m] (i, j, k) =
      (cycleStep .c1)^[1] ((cycleStep .c1)^[1]
        ((cycleStep .c1)^[m - 2] (i, j, k))) := by
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]; congr 1; omega
  rw [hm_split, c1_intermediate_run i j k hm hfib (m - 2) (le_refl _)]
  have hfib_n1 : fiber (i + ((m - 2 : ℕ) : ZMod m), j, k) = -1 := by
    rw [fiber_add_i, hfib, natCast_m_sub_two (by omega)]; ring
  have hi_ne : i + ((m - 2 : ℕ) : ZMod m) ≠ 0 := by
    rw [natCast_m_sub_two (by omega)]
    intro h; apply hi; linear_combination h
  rw [Function.iterate_one, c1_step_fn1_ine _ _ _ hfib_n1 hi_ne]
  have hfib_0 : fiber (i + ((m - 2 : ℕ) : ZMod m), j, k + 1) = 0 := by
    unfold fiber at hfib ⊢; rw [natCast_m_sub_two (by omega)]; linear_combination hfib
  rw [c1_step_f0 _ _ _ hfib_0]

/-- Bump case: i = 2. Net shift: i → 0, j → j+2, k unchanged. -/
theorem c1_fiber_cycle_bump (j k : ZMod m) (hm : 2 < m)
    (hfib : fiber ((2 : ZMod m), j, k) = 1) :
    (cycleStep .c1)^[m] ((2 : ZMod m), j, k) = (0, j + 2, k) := by
  have hm_split : (cycleStep .c1)^[m] ((2 : ZMod m), j, k) =
      (cycleStep .c1)^[1] ((cycleStep .c1)^[1]
        ((cycleStep .c1)^[m - 2] ((2 : ZMod m), j, k))) := by
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]; congr 1; omega
  rw [hm_split, c1_intermediate_run _ j k hm hfib (m - 2) (le_refl _)]
  have h_eq : (2 : ZMod m) + ((m - 2 : ℕ) : ZMod m) = 0 := by
    rw [natCast_m_sub_two (by omega)]; ring
  have hfib_n1 : fiber ((0 : ZMod m), j, k) = -1 := by
    have : fiber ((2 : ZMod m) + ((m - 2 : ℕ) : ZMod m), j, k) = -1 := by
      rw [fiber_add_i, hfib, natCast_m_sub_two (by omega)]; ring
    rwa [h_eq] at this
  conv_lhs =>
    rw [show ((2 : ZMod m) + ((m - 2 : ℕ) : ZMod m), j, k) = ((0 : ZMod m), j, k)
      from by ext <;> simp [h_eq]]
  rw [Function.iterate_one, c1_step_fn1_ieq _ _ hfib_n1]
  have hfib_0 : fiber ((0 : ZMod m), j + 1, k) = 0 := by
    unfold fiber at hfib_n1 ⊢; linear_combination hfib_n1
  rw [c1_step_f0 _ _ _ hfib_0]
  congr 1; congr 1; ring

/-! ## Iterated fiber cycle for cycle 1

After n non-bump fiber cycles (n·m steps), i shifts by n·(m-2),
j and k each shift by n.
-/

/-- Iterated non-bump: safe condition ensures i ≠ 2 throughout. -/
theorem c1_iter_non_bump (i j k : ZMod m) (hm : 2 < m)
    (hfib : fiber (i, j, k) = 1) (n : ℕ) (hn : n ≤ m - 1)
    (hi_safe : ∀ t : ℕ, t < n →
      i + (t : ZMod m) * ((m - 2 : ℕ) : ZMod m) ≠ 2) :
    (cycleStep .c1)^[n * m] (i, j, k) =
      (i + (n : ZMod m) * ((m - 2 : ℕ) : ZMod m), j + (n : ZMod m), k + (n : ZMod m)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn' : n ≤ m - 1 := by omega
    have hsplit : (cycleStep .c1)^[(n + 1) * m] (i, j, k) =
        (cycleStep .c1)^[m] ((cycleStep .c1)^[n * m] (i, j, k)) := by
      rw [← Function.iterate_add_apply]; congr 1; ring
    rw [hsplit, ih hn' (fun t ht => hi_safe t (by omega))]
    have hfib' : fiber (i + (n : ZMod m) * ((m - 2 : ℕ) : ZMod m), j + (n : ZMod m),
        k + (n : ZMod m)) = 1 := by
      unfold fiber at hfib ⊢; rw [natCast_m_sub_two (by omega)]; linear_combination hfib
    rw [c1_fiber_cycle_non_bump _ _ _ hm hfib' (hi_safe n (by omega))]
    simp only [Prod.mk.injEq]; exact ⟨by push_cast; ring, by push_cast; ring, by push_cast; ring⟩

/-! ## Block transition for cycle 1

After m² steps from entry point j, we reach entry point j+1.
The block decomposes into (m-1) non-bump fiber cycles + 1 bump cycle.
-/

/-- Entry point for block j of cycle 1. -/
def cycle1Entry (j : ZMod m) : V m := (0, j, 1 - j)

/-- The fiber of every cycle 1 entry point is 1. -/
@[simp]
theorem fiber_cycle1Entry (j : ZMod m) :
    fiber (cycle1Entry j) = 1 := by
  simp [cycle1Entry, fiber]

omit [NeZero m] in
/-- Different block indices give different cycle 1 entry points. -/
theorem cycle1Entry_injective : Function.Injective (cycle1Entry : ZMod m → V m) := by
  intro i j h
  simp only [cycle1Entry, Prod.mk.injEq] at h
  exact h.2.1

/-- After m² steps of cycle 1 from entry j, we reach entry (j+1). -/
theorem cycle1_block_transition (hm : 2 < m) (hm_odd : Odd m) (j : ZMod m) :
    (cycleStep .c1)^[m ^ 2] (cycle1Entry j) = cycle1Entry (j + 1) := by
  have hsplit : (cycleStep .c1)^[m ^ 2] (cycle1Entry j) =
      (cycleStep .c1)^[m] ((cycleStep .c1)^[(m - 1) * m] (cycle1Entry j)) := by
    rw [← Function.iterate_add_apply]; congr 1
    have : m ^ 2 = (m - 1) * m + m := by
      rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_right m (by omega))]; ring
    omega
  rw [hsplit]
  unfold cycle1Entry
  rw [c1_iter_non_bump (0 : ZMod m) j (1 - j) hm (by simp [fiber]) (m - 1) le_rfl ?hi_safe]
  · have h_i_eq : (0 : ZMod m) + ↑(m - 1) * ((m - 2 : ℕ) : ZMod m) = 2 := by
      rw [natCast_m_sub_one (by omega), natCast_m_sub_two (by omega)]; ring
    have hfib' : fiber ((2 : ZMod m), j + ↑(m - 1), (1 - j) + ↑(m - 1)) = 1 := by
      unfold fiber; rw [natCast_m_sub_one (by omega)]; ring
    conv_lhs =>
      rw [show ((0 : ZMod m) + ↑(m - 1) * ((m - 2 : ℕ) : ZMod m), j + ↑(m - 1),
        (1 - j) + ↑(m - 1)) = ((2 : ZMod m), j + ↑(m - 1), (1 - j) + ↑(m - 1))
        from by ext <;> simp [h_i_eq]]
    rw [c1_fiber_cycle_bump _ _ hm hfib']
    simp only [Prod.mk.injEq]
    refine ⟨trivial, by rw [natCast_m_sub_one (by omega)]; ring,
      by rw [natCast_m_sub_one (by omega)]; ring⟩
  case hi_safe =>
    intro t ht
    rw [natCast_m_sub_two (by omega)]
    intro h
    have h1 : (-2 : ZMod m) * ((t : ZMod m) + 1) = 0 := by linear_combination h
    have h2 : (t : ZMod m) + 1 = 0 := (neg_two_isUnit hm_odd).mul_right_eq_zero.mp h1
    rw [show (t : ZMod m) + 1 = ((t + 1 : ℕ) : ZMod m) from by push_cast; ring] at h2
    rw [ZMod.natCast_eq_zero_iff] at h2
    exact absurd (Nat.le_of_dvd (by omega) h2) (by omega)

/-! ## Entry point periodicity for cycle 1 -/

/-- After n block transitions, the entry point shifts by n. -/
theorem cycle1_entry_shift (hm : 2 < m) (hm_odd : Odd m) (j : ZMod m) (n : ℕ) :
    (cycleStep .c1)^[n * m ^ 2] (cycle1Entry j) = cycle1Entry (j + (n : ZMod m)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1) * m ^ 2 = m ^ 2 + n * m ^ 2 from by ring]
    rw [Function.iterate_add_apply]
    rw [ih, cycle1_block_transition hm hm_odd]
    congr 1; push_cast; ring

/-- Cycle 1 returns every entry point to itself after m³ steps. -/
theorem cycle1_period_entry (hm : 2 < m) (hm_odd : Odd m) (j : ZMod m) :
    (cycleStep .c1)^[m ^ 3] (cycle1Entry j) = cycle1Entry j := by
  rw [show m ^ 3 = m * m ^ 2 from by ring]
  rw [cycle1_entry_shift hm hm_odd j m]
  simp

/-! ## Tests -/

-- Single fiber cycle tests: m = 5
example : (cycleStep .c1)^[5] ((0 : ZMod 5), (0 : ZMod 5), (1 : ZMod 5)) =
    ((0 : ZMod 5) + ((3 : ℕ) : ZMod 5), (0 : ZMod 5) + 1, (1 : ZMod 5) + 1) :=
  c1_fiber_cycle_non_bump (m := 5) _ _ _ (by omega) (by decide) (by decide)

-- Block transition tests: m = 3
example : (cycleStep .c1)^[3 ^ 2] (cycle1Entry (0 : ZMod 3)) = cycle1Entry (0 + 1) :=
  cycle1_block_transition (by omega) ⟨1, by omega⟩ 0

example : (cycleStep .c1)^[3 ^ 2] (cycle1Entry (1 : ZMod 3)) = cycle1Entry (1 + 1) :=
  cycle1_block_transition (by omega) ⟨1, by omega⟩ 1

-- Entry point periodicity test: m = 3
example : (cycleStep .c1)^[3 ^ 3] (cycle1Entry (0 : ZMod 3)) = cycle1Entry 0 :=
  cycle1_period_entry (by omega) ⟨1, by omega⟩ 0

end ClaudesCycles
