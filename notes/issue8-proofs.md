# Issue #8: Block Transition — COMPLETED

PR #19, merged into Hamiltonian.lean + BlockAnalysis.lean.

## Key lessons learned during implementation

### Bumping fiber cycle results (corrected from initial sketch)
The bumping step replaces a k-bump with an i-bump, so k gets ONE FEWER bump:
- Case A: `(i, j, k) → (i+1, -1, k)` (NOT k+1)
- Case B: `(0, j, k) → (1, -1, k+1)` (NOT k+2)
- Case C: `(-1, j, k) → (0, -1, k+(m-2))` (NOT k+(m-1))

### Prod.mk.injEq + simp behavior
- `simp only [Prod.mk.injEq]` on `(a,b,c) = (x,y,z)` produces `a=x ∧ b=y ∧ c=z`
- But simp may simplify trivially-true components to `True`, giving e.g. `True ∧ a=x ∧ True`
- This makes `exact ⟨rfl, ..., rfl⟩` fail because `rfl` doesn't match `True`
- Fix: use `trivial` for True components, or use `true_and`/`and_true` simp lemmas

### IsUnit.mul_right_eq_zero pattern
- `hu.mul_right_eq_zero` matches `hu_val * x = 0`, NOT `x * hu_val = 0`
- If you have `x * unit = 0`, use `mul_comm` first or produce `unit * x = 0` via `linear_combination`

### hj_safe discharge (all 3 cases)
All reduce to `↑(t+1) ≠ 0` via:
```
rw [show (t : ZMod m) + 1 = ((t + 1 : ℕ) : ZMod m) from by push_cast; ring] at h
rw [ZMod.natCast_eq_zero_iff] at h
exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
```
Case B additionally needs `IsUnit (-2)` from `hm_odd.coprime_two_left`.

### Natural number subtraction in iterate decomposition
`m^2 = (m-1)*m + m` needs careful handling:
```lean
rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_right m (by omega))]; ring
```
Don't use `nlinarith` — it struggles with natural subtraction.
