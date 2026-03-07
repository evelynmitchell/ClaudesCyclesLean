# Issue #4: ZMod Helper Lemmas — Verified Proof Sketches

## Lemma 1: natCast_m_sub_one
`((m - 1 : ℕ) : ZMod m) = -1` (needs `1 ≤ m`)
```lean
have h : ((m - 1 : ℕ) : ZMod m) + 1 = 0 := by
  have h1 : m - 1 + 1 = m := Nat.sub_add_cancel hm
  exact_mod_cast show ((m - 1 + 1 : ℕ) : ZMod m) = 0 by rw [h1]; exact ZMod.natCast_self m
exact eq_neg_of_add_eq_zero_left h
```

## Lemma 2: natCast_m_sub_two
`((m - 2 : ℕ) : ZMod m) = -2` (needs `2 ≤ m`)
Same pattern as lemma 1 with 2 instead of 1.

## Lemma 3: one_ne_neg_one
`(1 : ZMod m) ≠ -1` (needs `[Fact (2 < m)]`)
Already in Mathlib: `ZMod.neg_one_ne_one.symm`

## Lemma 4: natCast_ne_zero
`((1 + n : ℕ) : ZMod m) ≠ 0` (needs `n < m - 1`)
```lean
intro h
rw [ZMod.natCast_eq_zero_iff] at h
have := Nat.le_of_dvd (by omega) h
omega
```
Key API: `ZMod.natCast_eq_zero_iff`

## Lemma 5: natCast_ne_neg_one
`((1 + n : ℕ) : ZMod m) ≠ -1` (needs `2 ≤ m`, `n < m - 2`)
```lean
obtain ⟨m', rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
intro h
have : (1 + n : ℕ) < m' + 1 := by omega
have hv : ((1 + n : ℕ) : ZMod (m' + 1)).val = 1 + n := ZMod.val_natCast_of_lt this
have hv2 : ((-1 : ZMod (m' + 1))).val = m' := ZMod.val_neg_one m'
have := congr_arg ZMod.val h
rw [hv] at this; rw [hv2] at this
omega
```
Gotcha: Must rewrite `m` as `m'+1` for `ZMod.val_neg_one`. Watch cast ordering (`↑(1+n)` vs `1+↑n`).

## Key Mathlib API names (verified in v4.28.0)
- `ZMod.natCast_self` — `(m : ZMod m) = 0`
- `ZMod.natCast_eq_zero_iff` — `(a : ZMod b) = 0 ↔ b ∣ a`
- `ZMod.val_neg_one` — `(-1 : ZMod (n+1)).val = n`
- `ZMod.val_natCast_of_lt` — `(a : ZMod n).val = a` when `a < n`
- `ZMod.neg_one_ne_one` — `(-1 : ZMod n) ≠ 1` when `[Fact (2 < n)]`
- `eq_neg_of_add_eq_zero_left` — `a + b = 0 → a = -b`
