# Mathlib Lemma Notes

## ZMod
- `ZMod.natCast_self` (not `natCast_self_eq_zero`) — `(m : ZMod m) = 0`
- `ZMod.isUnit_iff_coprime` (not `isUnit_natCast_iff`) — `IsUnit ((n : ℕ) : ZMod m) ↔ n.Coprime m`
- `ZMod.natCast_self` is @[simp] via `natCast_self'`, no need to pass explicitly

## Nat coprimality
- `Odd.coprime_two_left` — `Odd m → Nat.Coprime 2 m` (in `Mathlib.Data.Nat.Prime.Basic`)
- `Nat.coprime_two_left` — `Nat.Coprime 2 m ↔ Odd m`

## Units
- `IsUnit.neg` — `IsUnit a → IsUnit (-a)` (in `Mathlib.Algebra.Ring.Units`)

## Iteration
- `Function.iterate_succ_apply'` — `f^[n+1] x = f (f^[n] x)` (used in inductive proofs)
- `Function.iterate_succ_apply` — `f^[n+1] x = f^[n] (f x)` (different order)
- `Function.iterate_add_apply` — `f^[m+n] x = f^[m] (f^[n] x)` (composing iterates)

## ZMod distinctness patterns
- `ZMod.natCast_eq_zero_iff (a b : ℕ) : (a : ZMod b) = 0 ↔ b ∣ a` — NOT `natCast_zmod_eq_zero_iff_dvd`
- `ZMod.val_natCast (n a : ℕ) : (↑a : ZMod n).val = a % n`
- `ZMod.val_neg_one (n : ℕ) : (-1 : ZMod (n+1)).val = n` — needs `obtain ⟨m', rfl⟩` to put m in m'+1 form
- For `(n : ZMod m) ≠ 0` when `0 < n < m`: use `ZMod.natCast_eq_zero_iff` + `Nat.le_of_dvd` + `omega`
- For `(n : ZMod m) ≠ -1` when `n < m-1`: use `congr_arg ZMod.val` + `val_natCast` + `val_neg_one` + `Nat.mod_eq_of_lt` + `omega`
- For `((m-1 : ℕ) : ZMod m) = -1`: use `Nat.sub_add_cancel` + `ZMod.natCast_self` + `eq_neg_of_add_eq_zero_left`
