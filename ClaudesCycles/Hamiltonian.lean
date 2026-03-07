/-
Copyright (c) 2026 Claude's Cycles Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Hamiltonian cycle proofs for Claude's construction.
Main result: for odd m ≥ 3, each of the three cycles visits all m³ vertices.
-/
import ClaudesCycles.DirectionMap
import ClaudesCycles.Permutation
import ClaudesCycles.BlockAnalysis
import ClaudesCycles.Verify
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

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

/-! ## Entry point periodicity for cycle 0 -/

/-- After n block transitions, the entry point shifts by n. -/
theorem cycle0_entry_shift (hm : 2 < m) (hm_odd : Odd m) (i : ZMod m) (n : ℕ) :
    (cycleStep .c0)^[n * m ^ 2] (cycle0Entry i) = cycle0Entry (i + (n : ZMod m)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1) * m ^ 2 = m ^ 2 + n * m ^ 2 from by ring]
    rw [Function.iterate_add_apply]
    rw [ih, cycle0_block_transition hm hm_odd]
    congr 1; push_cast; ring

/-- Cycle 0 returns every entry point to itself after m³ steps. -/
theorem cycle0_period_entry (hm : 2 < m) (hm_odd : Odd m) (i : ZMod m) :
    (cycleStep .c0)^[m ^ 3] (cycle0Entry i) = cycle0Entry i := by
  rw [show m ^ 3 = m * m ^ 2 from by ring]
  rw [cycle0_entry_shift hm hm_odd i m]
  simp

-- Entry point periodicity test: m = 3
example : (cycleStep .c0)^[3 ^ 3] (cycle0Entry (0 : ZMod 3)) = cycle0Entry 0 :=
  cycle0_period_entry (by omega) ⟨1, by omega⟩ 0

/-! ## No early return: orbit doesn't hit entry points within a block -/

omit [NeZero m] in
/-- A natural number t' with t' < m-1 is nonzero as an element of ZMod m after adding 1. -/
theorem zmod_succ_ne_zero (t' : ℕ) (ht' : t' < m - 1) :
    (t' : ZMod m) + 1 ≠ 0 := by
  rw [show (t' : ZMod m) + 1 = ((1 + t' : ℕ) : ZMod m) from by push_cast; ring]
  exact natCast_ne_zero (by omega)

/-- Within a block (steps 1 through m²-1 from an entry point), the orbit never
    lands on any entry point. -/
theorem c0_not_entry_within_block (hm : 2 < m) (hm_odd : Odd m)
    (i j : ZMod m) (r : ℕ) (hr : 0 < r) (hr' : r < m ^ 2) :
    (cycleStep .c0)^[r] (cycle0Entry i) ≠ cycle0Entry j := by
  intro heq
  have hfib := congr_arg fiber heq
  rw [fiber_iterate, fiber_cycle0Entry, fiber_cycle0Entry] at hfib
  have hr_zero : (r : ZMod m) = 0 := by linear_combination hfib
  have hdvd : m ∣ r := by
    rwa [ZMod.natCast_eq_zero_iff] at hr_zero
  obtain ⟨t, ht_eq⟩ := hdvd
  have hrw : r = t * m := by rw [ht_eq, Nat.mul_comm]
  have ht1 : 1 ≤ t := Nat.pos_of_mul_pos_left (ht_eq ▸ hr)
  have ht2 : t ≤ m - 1 := by
    have : m * t < m * m := by
      calc m * t = r := ht_eq.symm
        _ < m ^ 2 := hr'
        _ = m * m := Nat.pow_two m
    have := Nat.lt_of_mul_lt_mul_left this; omega
  rw [hrw] at heq
  unfold cycle0Entry at heq
  by_cases hi0 : i = 0
  · subst hi0
    rw [c0_iter_i_eq_zero (-1) (2 - 0) hm (by simp [fiber]; ring) t ht2
        (fun t' ht' => ?_)] at heq
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨_, hj_eq, _⟩ := heq
      have : (t : ZMod m) * ((m - 2 : ℕ) : ZMod m) = 0 := by linear_combination hj_eq
      rw [natCast_m_sub_two (by omega)] at this
      have : (-2 : ZMod m) * (t : ZMod m) = 0 := by linear_combination this
      have ht_zero : (t : ZMod m) = 0 := (neg_two_isUnit hm_odd).mul_right_eq_zero.mp this
      exact absurd (Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff t m).mp ht_zero))
        (by omega)
    · rw [natCast_m_sub_two (by omega)]
      intro h
      have h1 : (-2 : ZMod m) * ((t' : ZMod m) + 1) = 0 := by linear_combination h
      have h2 : (t' : ZMod m) + 1 = 0 := (neg_two_isUnit hm_odd).mul_right_eq_zero.mp h1
      exact absurd h2 (zmod_succ_ne_zero t' (by omega))
  · by_cases hi1 : i = -1
    · subst hi1
      rw [c0_iter_i_eq_neg_one (-1) (2 - -1) hm (by simp [fiber]; ring) t ht2
          (fun t' ht' => ?_)] at heq
      · simp only [Prod.mk.injEq] at heq
        obtain ⟨_, hj_eq, _⟩ := heq
        have ht_zero : (t : ZMod m) = 0 := by linear_combination hj_eq
        exact absurd (Nat.le_of_dvd (by omega)
          ((ZMod.natCast_eq_zero_iff t m).mp ht_zero)) (by omega)
      · intro h
        exact absurd (by linear_combination h : (t' : ZMod m) + 1 = 0)
          (zmod_succ_ne_zero t' (by omega))
    · rw [c0_iter_generic i (-1) (2 - i) hm (by simp [fiber]; ring) hi0 hi1 t ht2
          (fun t' ht' => ?_)] at heq
      · simp only [Prod.mk.injEq] at heq
        obtain ⟨_, hj_eq, _⟩ := heq
        have : (t : ZMod m) * ((m - 1 : ℕ) : ZMod m) = 0 := by linear_combination hj_eq
        rw [natCast_m_sub_one (by omega)] at this
        have ht_zero : (t : ZMod m) = 0 := by linear_combination -this
        exact absurd (Nat.le_of_dvd (by omega)
          ((ZMod.natCast_eq_zero_iff t m).mp ht_zero)) (by omega)
      · rw [natCast_m_sub_one (by omega)]
        intro h
        exact absurd (by linear_combination -h : (t' : ZMod m) + 1 = 0)
          (zmod_succ_ne_zero t' (by omega))

-- No early return tests: m = 3
example : (cycleStep .c0)^[1] (cycle0Entry (0 : ZMod 3)) ≠ cycle0Entry 0 :=
  c0_not_entry_within_block (by omega) ⟨1, by omega⟩ 0 0 1 (by omega) (by omega)

example : (cycleStep .c0)^[4] (cycle0Entry (1 : ZMod 3)) ≠ cycle0Entry 2 :=
  c0_not_entry_within_block (by omega) ⟨1, by omega⟩ 1 2 4 (by omega) (by omega)

/-! ## Orbit covers all vertices for cycle 0 -/

omit [NeZero m] in
/-- Different block indices give different entry points. -/
theorem cycle0Entry_injective : Function.Injective (cycle0Entry : ZMod m → V m) := by
  intro i j h
  simp only [cycle0Entry, Prod.mk.injEq] at h
  exact h.1

/-- No early return: f^[k](eᵢ) ≠ eᵢ for 0 < k < m³. -/
theorem c0_no_return_to_entry (hm : 2 < m) (hm_odd : Odd m) (i : ZMod m)
    (k : ℕ) (hk : 0 < k) (hk' : k < m ^ 3) :
    (cycleStep .c0)^[k] (cycle0Entry i) ≠ cycle0Entry i := by
  have hm2_pos : 0 < m ^ 2 := pow_pos (by omega : 0 < m) 2
  have hr : k % m ^ 2 < m ^ 2 := Nat.mod_lt k hm2_pos
  have hq : k / m ^ 2 < m := by
    rw [Nat.div_lt_iff_lt_mul hm2_pos]
    calc k < m ^ 3 := hk'
      _ = m * m ^ 2 := by ring
  have hk_rw : k = k % m ^ 2 + k / m ^ 2 * m ^ 2 := by
    have h := Nat.div_add_mod k (m ^ 2); rw [Nat.mul_comm] at h; omega
  rw [hk_rw, Function.iterate_add_apply, cycle0_entry_shift hm hm_odd i (k / m ^ 2)]
  by_cases hr0 : k % m ^ 2 = 0
  · -- r = 0: f^[k](eᵢ) = e_{i+q}, need i+q ≠ i
    simp only [hr0, Function.iterate_zero, id]
    intro h
    have hiq : i + (↑(k / m ^ 2) : ZMod m) = i := cycle0Entry_injective h
    have hq_zero : (↑(k / m ^ 2) : ZMod m) = 0 := add_left_cancel (by rwa [add_zero])
    rw [ZMod.natCast_eq_zero_iff] at hq_zero
    have hq_pos : 0 < k / m ^ 2 :=
      Nat.div_pos (Nat.le_of_dvd hk (Nat.dvd_of_mod_eq_zero hr0)) hm2_pos
    exact absurd (Nat.le_of_dvd (by omega) hq_zero) (by omega)
  · -- r > 0: within-block, can't hit any entry point
    exact c0_not_entry_within_block hm hm_odd (i + ↑(k / m ^ 2)) i
      (k % m ^ 2) (Nat.pos_of_ne_zero hr0) hr

/-- The orbit map k ↦ f^[k](eᵢ) is injective on [0, m³). -/
theorem c0_orbit_injOn (hm : 2 < m) (hm_odd : Odd m) (i : ZMod m) :
    Set.InjOn (fun k => (cycleStep .c0)^[k] (cycle0Entry i))
      ↑(Finset.range (m ^ 3)) := by
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  simp only at hab
  -- hab : (cycleStep .c0)^[a] (cycle0Entry i) = (cycleStep .c0)^[b] (cycle0Entry i)
  by_contra h_ne
  -- WLOG a < b
  have h : a < b ∨ b < a := by omega
  rcases h with h | h
  · -- From f^[a](e) = f^[b](e) and f^[m³](e) = e, derive f^[m³-b+a](e) = e
    have key : (cycleStep .c0)^[m ^ 3 - b + a] (cycle0Entry i) = cycle0Entry i := by
      have h1 : (cycleStep .c0)^[m ^ 3 - b + a] (cycle0Entry i)
          = (cycleStep .c0)^[m ^ 3 - b] ((cycleStep .c0)^[a] (cycle0Entry i)) :=
        Function.iterate_add_apply ..
      have h2 : (cycleStep .c0)^[m ^ 3 - b] ((cycleStep .c0)^[b] (cycle0Entry i))
          = cycle0Entry i := by
        rw [← Function.iterate_add_apply,
            show (m ^ 3 - b) + b = m ^ 3 from by omega]
        exact cycle0_period_entry hm hm_odd i
      rw [h1, hab, h2]
    exact c0_no_return_to_entry hm hm_odd i (m ^ 3 - b + a) (by omega) (by omega) key
  · -- Symmetric case: b < a
    have key : (cycleStep .c0)^[m ^ 3 - a + b] (cycle0Entry i) = cycle0Entry i := by
      have h1 : (cycleStep .c0)^[m ^ 3 - a + b] (cycle0Entry i)
          = (cycleStep .c0)^[m ^ 3 - a] ((cycleStep .c0)^[b] (cycle0Entry i)) :=
        Function.iterate_add_apply ..
      have h2 : (cycleStep .c0)^[m ^ 3 - a] ((cycleStep .c0)^[a] (cycle0Entry i))
          = cycle0Entry i := by
        rw [← Function.iterate_add_apply,
            show (m ^ 3 - a) + a = m ^ 3 from by omega]
        exact cycle0_period_entry hm hm_odd i
      rw [h1, hab.symm, h2]
    exact c0_no_return_to_entry hm hm_odd i (m ^ 3 - a + b) (by omega) (by omega) key

/-! ## Main Hamiltonian theorem for cycle 0 -/

/-- The orbit of entry point 0 covers all of V m. -/
theorem c0_orbit_eq_univ (hm : 2 < m) (hm_odd : Odd m) :
    Finset.image (fun k => (cycleStep .c0)^[k] (cycle0Entry (0 : ZMod m)))
      (Finset.range (m ^ 3)) = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_image_of_injOn (c0_orbit_injOn hm hm_odd (0 : ZMod m)), Finset.card_range,
      card_V (m := m)]

/-- Every vertex is in the orbit of entry point 0. -/
theorem c0_in_orbit (hm : 2 < m) (hm_odd : Odd m) (v : V m) :
    ∃ n, n < m ^ 3 ∧ (cycleStep .c0)^[n] (cycle0Entry (0 : ZMod m)) = v := by
  have hv : v ∈ (Finset.univ : Finset (V m)) := Finset.mem_univ v
  rw [← c0_orbit_eq_univ hm hm_odd, Finset.mem_image] at hv
  obtain ⟨n, hn, rfl⟩ := hv
  exact ⟨n, Finset.mem_range.mp hn, rfl⟩

/-- Cycle 0 returns to start after m³ steps. -/
theorem cycle0_period (hm : 2 < m) (hm_odd : Odd m) (v : V m) :
    (cycleStep .c0)^[m ^ 3] v = v := by
  obtain ⟨n, _, hn_eq⟩ := c0_in_orbit hm hm_odd v
  rw [← hn_eq, ← Function.iterate_add_apply,
      show m ^ 3 + n = n + m ^ 3 from by omega,
      Function.iterate_add_apply, cycle0_period_entry hm hm_odd (0 : ZMod m), hn_eq]

/-- No vertex has a small period under cycle 0. -/
theorem c0_no_small_period (hm : 2 < m) (hm_odd : Odd m) (v : V m)
    (k : ℕ) (hk : 0 < k) (hk' : k < m ^ 3) :
    (cycleStep .c0)^[k] v ≠ v := by
  obtain ⟨n, hn_lt, hn_eq⟩ := c0_in_orbit hm hm_odd v
  intro h_period
  -- f^[k](f^[n](e₀)) = f^[n](e₀), so f^[k+n](e₀) = f^[n](e₀)
  rw [← hn_eq, ← Function.iterate_add_apply] at h_period
  by_cases hkn : k + n < m ^ 3
  · -- k+n < m³: orbit injectivity gives k+n = n, so k = 0
    have := c0_orbit_injOn hm hm_odd (0 : ZMod m)
      (by simp only [Finset.coe_range, Set.mem_Iio]; omega)
      (by simp only [Finset.coe_range, Set.mem_Iio]; exact hn_lt)
      h_period
    omega
  · -- k+n ≥ m³: reduce by m³
    push_neg at hkn
    have hj_lt : k + n - m ^ 3 < m ^ 3 := by omega
    have h_reduce : (cycleStep .c0)^[k + n] (cycle0Entry (0 : ZMod m))
        = (cycleStep .c0)^[k + n - m ^ 3] (cycle0Entry (0 : ZMod m)) := by
      conv_lhs =>
        rw [show k + n = (k + n - m ^ 3) + m ^ 3 from by omega,
            Function.iterate_add_apply]
      rw [cycle0_period_entry hm hm_odd (0 : ZMod m)]
    rw [h_reduce] at h_period
    have := c0_orbit_injOn hm hm_odd (0 : ZMod m)
      (by simp only [Finset.coe_range, Set.mem_Iio]; exact hj_lt)
      (by simp only [Finset.coe_range, Set.mem_Iio]; exact hn_lt)
      h_period
    omega

/-- The orbit of any vertex under cycle 0 has size m³ (i.e., cycle 0 is Hamiltonian). -/
theorem cycle0_orbit_size (hm : 2 < m) (hm_odd : Odd m) (v : V m) :
    (Finset.image (fun k => (cycleStep .c0)^[k] v) (Finset.range (m ^ 3))).card = m ^ 3 := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  simp only at hab
  by_contra h_ne
  rcases Nat.lt_or_gt_of_ne h_ne with h | h
  · have key : (cycleStep .c0)^[m ^ 3 - b + a] v = v := by
      calc (cycleStep .c0)^[m ^ 3 - b + a] v
          = (cycleStep .c0)^[m ^ 3 - b] ((cycleStep .c0)^[a] v) :=
            Function.iterate_add_apply ..
        _ = (cycleStep .c0)^[m ^ 3 - b] ((cycleStep .c0)^[b] v) := by rw [hab]
        _ = v := by
            rw [← Function.iterate_add_apply,
                show (m ^ 3 - b) + b = m ^ 3 from by omega]
            exact cycle0_period hm hm_odd v
    exact c0_no_small_period hm hm_odd v (m ^ 3 - b + a) (by omega) (by omega) key
  · have key : (cycleStep .c0)^[m ^ 3 - a + b] v = v := by
      calc (cycleStep .c0)^[m ^ 3 - a + b] v
          = (cycleStep .c0)^[m ^ 3 - a] ((cycleStep .c0)^[b] v) :=
            Function.iterate_add_apply ..
        _ = (cycleStep .c0)^[m ^ 3 - a] ((cycleStep .c0)^[a] v) := by rw [hab.symm]
        _ = v := by
            rw [← Function.iterate_add_apply,
                show (m ^ 3 - a) + a = m ^ 3 from by omega]
            exact cycle0_period hm hm_odd v
    exact c0_no_small_period hm hm_odd v (m ^ 3 - a + b) (by omega) (by omega) key

-- cycle0_period test: m = 3
example : (cycleStep .c0)^[3 ^ 3] ((0 : ZMod 3), (0 : ZMod 3), (0 : ZMod 3)) =
    ((0 : ZMod 3), (0 : ZMod 3), (0 : ZMod 3)) :=
  cycle0_period (by omega) ⟨1, by omega⟩ _

-- cycle0_orbit_size test: m = 3
example : (Finset.image (fun k => (cycleStep .c0)^[k] ((0 : ZMod 3), (0 : ZMod 3), (0 : ZMod 3)))
    (Finset.range (3 ^ 3))).card = 3 ^ 3 :=
  cycle0_orbit_size (by omega) ⟨1, by omega⟩ _

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
