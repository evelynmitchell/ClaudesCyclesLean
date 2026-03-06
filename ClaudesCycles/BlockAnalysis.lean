/-
Copyright (c) 2026 Claude's Cycles Formalization Project.
Licensed under the Apache License, Version 2.0, as described in the file LICENSE.

Step-level lemmas for cycle 0's direction table.
Each lemma characterizes `cycleStep .c0` for one row of Knuth's table.
-/
import ClaudesCycles.DirectionMap
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

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

end ClaudesCycles
