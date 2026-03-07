# Issue #7: Iterated Fiber Cycle Lemmas — Verified Proof Sketches

## Signatures (all type-checked with sorry + consumer #8)

### Case A: Generic (i ≠ 0, i ≠ -1)
```lean
theorem c0_iter_generic (i j k : ZMod m) (hm : 2 < m)
    (hfib : fiber (i, j, k) = 1) (hi0 : i ≠ 0) (hi1 : i ≠ -1)
    (n : ℕ) (hn : n ≤ m - 1)
    (hj_safe : ∀ t : ℕ, t < n →
      j + (t : ZMod m) * ((m - 1 : ℕ) : ZMod m) + ((m - 1 : ℕ) : ZMod m) ≠ -1) :
    (cycleStep .c0)^[n * m] (i, j, k) =
      (i, j + (n : ZMod m) * ((m - 1 : ℕ) : ZMod m), k + (n : ZMod m))
```

### Case B: i = 0
```lean
theorem c0_iter_i_eq_zero (j k : ZMod m) (hm : 2 < m)
    (hfib : fiber ((0 : ZMod m), j, k) = 1)
    (n : ℕ) (hn : n ≤ m - 1)
    (hj_safe : ∀ t : ℕ, t < n →
      j + (t : ZMod m) * ((m - 2 : ℕ) : ZMod m) + ((m - 2 : ℕ) : ZMod m) ≠ -1) :
    (cycleStep .c0)^[n * m] ((0 : ZMod m), j, k) =
      (0, j + (n : ZMod m) * ((m - 2 : ℕ) : ZMod m), k + 2 * (n : ZMod m))
```

### Case C: i = -1
```lean
theorem c0_iter_i_eq_neg_one (j k : ZMod m) (hm : 2 < m)
    (hfib : fiber ((-1 : ZMod m), j, k) = 1)
    (n : ℕ) (hn : n ≤ m - 1)
    (hj_safe : ∀ t : ℕ, t < n →
      j + (t : ZMod m) + 1 ≠ -1) :
    (cycleStep .c0)^[n * m] ((-1 : ZMod m), j, k) =
      (-1, j + (n : ZMod m), k + (n : ZMod m) * ((m - 1 : ℕ) : ZMod m))
```

## hj_safe discharge proofs for entry points

### Case A: reduces to ↑(t+1) ≠ 0
```lean
intro t ht
rw [natCast_m_sub_one (by omega)]
intro h
have h1 : (↑t + 1 : ZMod m) * (-1) + (-1) = 0 := by linear_combination h  -- or similar
-- then: ↑(t+1) = 0 contradiction via ZMod.natCast_eq_zero_iff + omega
```

### Case B: needs Odd m, IsUnit (-2)
```lean
intro t ht
rw [natCast_m_sub_two (by omega)]
intro h
have h1 : (↑t + 1 : ZMod m) * (-2) = 0 := by linear_combination h
have hu : IsUnit ((-2 : ZMod m)) := by
  rw [show (-2 : ZMod m) = -((2 : ℕ) : ZMod m) from by push_cast; ring]
  exact (ZMod.unitOfCoprime 2 hm_odd.coprime_two_left).isUnit.neg
rwa [IsUnit.mul_right_eq_zero hu] at h1
-- then same natCast_eq_zero_iff + omega pattern
```
Key: `Odd.coprime_two_left` from `Mathlib.Data.Nat.Prime.Basic`

### Case C: simplest, just val comparison
```lean
intro t ht h
have h1 : (t : ZMod m) = -1 := by linear_combination h
rw [show (-1 : ZMod m) = ((m - 1 : ℕ) : ZMod m) from (natCast_m_sub_one (by omega)).symm] at h1
have := congr_arg ZMod.val h1
rw [ZMod.val_natCast_of_lt (show t < m by omega),
    ZMod.val_natCast_of_lt (show m - 1 < m by omega)] at this
omega
```

## #8 consumer pattern (verified)
```lean
unfold cycle0Entry
rw [c0_iter_generic i (-1) (2 - i) hm (by simp [fiber]; ring) hi0 hi1 (m - 1) le_rfl (by <safety>)]
simp only [Prod.mk.injEq]
refine ⟨rfl, ?_, ?_⟩
· rw [natCast_m_sub_one (by omega)]; ring  -- j coordinate
· rw [natCast_m_sub_one (by omega)]; ring  -- k coordinate
```

## Notes
- Case B requires `Odd m` hypothesis (not just `2 < m`)
- `hfib` uses `fiber (i, j, k) = 1` form (matches #6)
- `IsUnit.mul_right_eq_zero` is the key lemma for cancelling units in ZMod
- Proof is induction on n, applying single fiber cycle (#6) at each step
- Need to re-establish fiber = 1 after each cycle (should follow from fiber_add_j/k + ring)
