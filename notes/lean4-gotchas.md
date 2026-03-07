# Lean 4 Gotchas

## Attributes/modifiers must come BEFORE doc comments
```lean
-- WRONG: doc comment expects a declaration keyword after it
/-- docstring -/
omit [NeZero m] in
theorem foo ...

-- CORRECT:
omit [NeZero m] in
/-- docstring -/
theorem foo ...
```
Same applies to `set_option maxHeartbeats N in` — must appear BEFORE docstring.

## Lint: `<;>` vs `;` after `split_ifs`
`split_ifs <;> simp_all` triggers `unnecessarySeqFocus` when `split_ifs` produces only one goal (hypotheses resolve the split). Use `split_ifs; simp_all` (sequential) in that case. Use `<;>` only when multiple goals remain.

## Lint: unused simp args
`ZMod.natCast_self` is already in simp set (via `natCast_self'`). Don't pass it explicitly — just use `simp`.

## `show` vs `change` linter
- `show` is now linted — use `change` when modifying the goal (e.g., unfolding definitions)
- `show` is fine only when it matches the current goal exactly (documentation)

## `refine` over `apply`
- Use `refine` (not `apply`) when lemma has mixed term/prop arguments
- `apply` can fail to infer term arguments; `refine` lets you provide `?_` placeholders

## Theorem vs Def
- If return type is a `structure` (carries data, not `Prop`), use `def` not `theorem`
- Lean rejects `theorem` for non-Prop types

## Dot notation gotcha with `Integrable`
- `Integrable` is a `def` (unfolds to `And`); dot notation may resolve to `And.method`
- Fix: use explicit namespace — `Integrable.congr h_int ...` not `h_int.congr ...`

## Parsing quirks
- `let x := e; -body` fails — wrap in parens: `((-x) + y)`
- `∂volume` in multi-line integrands can fail — omit it (volume is default)
- `≤ᵐ[μ]` must be on one line — parser doesn't handle line breaks between `≤ᵐ` and `[μ]`

## `omit` for section variables
- When a theorem doesn't use `[NeZero m]` (or other section variables), add `omit [NeZero m] in` before the theorem. Forgetting this causes lint warnings — check ALL new theorems before committing, not just the first one.

## Test examples with implicit arguments
- When testing a lemma like `foo (n : ℕ) : ((1 + n : ℕ) : ZMod m) ≠ 0`, the example must let Lean unify `n`. Writing `((1 : ℕ) : ZMod 5) ≠ 0` won't unify with `1 + n`. Instead write `((1 + 0 : ℕ) : ZMod 5) ≠ 0` so `n = 0` is inferred.
- Similarly, `Fact (2 < 5)` won't be synthesized automatically — use `@lemma 5 ⟨by omega⟩`.

## `linarith` / `linear_combination` on ZMod
- `linarith` does NOT work on `ZMod` — it requires a linear order, which `ZMod` lacks.
- Use `linear_combination h` to derive equalities (e.g., `h : j + 1 = -1 ⊢ j = -2`). Requires `import Mathlib.Tactic.LinearCombination`.
- `linarith` may also not be available if the file only imports lightweight modules.

## Rewriting `m` when it appears in types
- `rw [show m = ... from by omega]` fails when `m` appears in instance types like `NeZero m` inside `cycleStep`. The rewrite tries to substitute `m` everywhere including the type.
- Workaround: use `have hm_split : f^[m] x = f^[1] (f^[1] (f^[m-2] x)) := by rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]; congr 1; omega` to decompose the iteration without rewriting `m` globally.
- For `(n+1)*m = n*m + m`, use `congr 1; ring` (not `omega` — omega can't handle nonlinear `n*m`).

## ZMod `ring` can't see `natCast` identities
- `ring` doesn't know `↑(m-1) = -1` in ZMod m. Must `rw [natCast_m_sub_one (by omega)]` before `ring`.
- This matters for fiber re-establishment: `1 + ↑n + ↑n * ↑(m-1) = 1` needs the rewrite first.

## Case-splitting on bounded ℕ in tests
- `decide` can't handle `∀ t < n, ... ↑(m-k) ...` with nat subtraction staying symbolic.
- `native_decide` works but is linted in Mathlib-style projects.
- `fin_cases` needs `Fintype` (ℕ doesn't have it).
- Pattern: `intro t ht; have : t = 0 ∨ t = 1 := by omega; rcases this with rfl | rfl <;> decide`

## Tuple equality (`Prod.mk` goals)
- `ring` doesn't work on `(a, b, c) = (a', b', c')` — it's not a ring expression.
- `congr 1; congr 1` can isolate the differing component if only one differs.
- `simp only [Prod.mk.injEq]` splits into conjuncts but **unpredictably simplifies** trivially-true components to `True`. So `⟨rfl, rfl, rfl⟩` may fail when some components became `True`.
- Safe pattern: after `simp only [Prod.mk.injEq]`, **check the goal**, then use `rfl`/`trivial`/`by ring` as appropriate for each conjunct. Or use `true_and`/`and_true` to strip `True`.

## `IsUnit.mul_right_eq_zero` / `mul_left_eq_zero` pattern
- `hu.mul_right_eq_zero` matches `hu_val * x = 0 ↔ x = 0` (unit on LEFT)
- `hu.mul_left_eq_zero` matches `x * hu_val = 0 ↔ x = 0` (unit on RIGHT)
- The "right"/"left" refers to which side of the iff the zero-check is on, NOT the position of the unit. Use `linear_combination` to produce the multiplication order that matches.

## Natural subtraction in iterate decomposition
- `m^2 = (m-1)*m + m` in ℕ: use `Nat.sub_one_mul` + `Nat.sub_add_cancel`:
  ```lean
  rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_right m (by omega))]; ring
  ```
- `nlinarith` and `omega` alone struggle with natural subtraction involving multiplication.

## ZMod coercion: `HAdd (ZMod m) ℕ` doesn't exist
- `i + n` where `i : ZMod m` and `n : ℕ` fails — no `HAdd` instance for mixed types.
- Always cast explicitly: `i + (n : ZMod m)`.

## `Function.iterate_add_apply` argument order
- Signature: `f^[a + b] x = f^[a] (f^[b] x)` — `a` is the OUTER application.
- When decomposing `(n+1)*m² = m² + n*m²`, write it as `m² + n*m²` (not `n*m² + m²`) so the block transition (`f^[m²]`) applies to the induction hypothesis result (`f^[n*m²]`).

## `omega` is strictly linear — no multiplication
- `omega` cannot prove `m * t = t * m`, `m ^ 2 = m * m`, or any goal involving products of variables.
- Use `Nat.mul_comm`, `Nat.pow_two m` (for `m ^ 2 = m * m`), `Nat.lt_of_mul_lt_mul_left` etc.
- For `m ∣ r` giving `r = m * t`, use `Nat.mul_comm` to get `t * m` form.
- For `q < m` from `k < m³` with `k = m² * q + r`: use `Nat.div_lt_iff_lt_mul` + `calc` chain, NOT `omega`/`nlinarith`.
- For `k = k % m² + k / m² * m²`: use `have h := Nat.div_add_mod k (m^2); rw [Nat.mul_comm] at h; omega`.

## Avoid `set` for div/mod variables
- `set q := k / m ^ 2` introduces a let-binding that `omega`, `subst`, and `rw` all struggle with.
- Prefer inline `k / m ^ 2` and `k % m ^ 2` with separate `have` statements for bounds.
- `Nat.div_pos` and `Nat.div_lt_iff_lt_mul` work cleanly with inline expressions.

## `nlinarith` may not be available
- `nlinarith` is NOT transitively imported by all Mathlib modules. Check availability before using.
- Alternative for `m * m² ≤ m² * q + r` given `m ≤ q`: use `calc` with `Nat.mul_le_mul_left`.

## Type annotation needed for `cycle0Entry 0` / `Finset.univ`
- When `m` appears only in types (not values), Lean can't infer it from `0 : ℕ` alone.
- Write `cycle0Entry (0 : ZMod m)` to help typeclass resolution for `Fintype (V m)`.

## `rw` can over-rewrite with periodic lemmas
- `rw [cycle0_period_entry ...]` rewrites ALL occurrences of `f^[m³](e₀)`, including ones you want to keep.
- Use `conv_lhs => rw [...]` or `conv_rhs => rw [...]` to restrict the rewrite to one side.

## `Nat.dvd` decomposition order
- `obtain ⟨t, ht⟩ := (hdvd : m ∣ r)` gives `ht : r = m * t` (divisor first).
- If you need `r = t * m`, add `have : r = t * m := by rw [ht, Nat.mul_comm]`.

## Dry-run imports must match the file
- `lean_run_code` with `import ClaudesCycles.Foo` uses the LSP's cached environment for `Foo.lean`. If `Foo.lean` contains `sorry`, the environment is axiomatically unsound — tactics like `linarith` can prove **false statements** (e.g. `(1 : ZMod 3) + 1 = 0`). Also, tactics not in the import closure may appear available via the cache.
- For accurate dry-runs, import the file's **direct dependencies** (e.g., `ClaudesCycles.BlockAnalysis` + `Mathlib.Data.ZMod.Basic`), NOT the file itself. This avoids sorry contamination and gives the correct tactic set.
- `linarith` does NOT work on ZMod (no linear order). Use `linear_combination` instead (available via `BlockAnalysis` → `Mathlib.Tactic.LinearCombination`).

## Check existing proofs for lemma names
- Before guessing a Mathlib name, grep the current file — the lemma may already be used nearby.
- Example: `ZMod.natCast_eq_zero_iff` (correct) vs `ZMod.natCast_zmod_eq_zero_iff_dvd` (doesn't exist).

## Rewriting a single tuple component
- To substitute a computed value into one coordinate of a tuple (e.g., `2 + (m-2) → 0`), use `ext <;> simp [h_eq]` inside `conv_lhs` or `show`. This is cleaner than `Prod.mk.injEq` for substitution.
- Example: `conv_lhs => rw [show (a, b, c) = (a', b, c) from by ext <;> simp [h_eq]]`

## `fiber` proof at boundary steps
- `fiber_add_j`/`fiber_add_k`/`fiber_add_i` only match one specific shape. For fiber proofs at boundary steps (e.g., fiber = 0 after bump), use `unfold fiber at hfib ⊢; rw [natCast_m_sub_two (by omega)]; linear_combination hfib`.

## `neg_neg` normalization for entry points
- `cycle2Entry (-1)` unfolds to `(0, -1, -(-1))`, not `(0, -1, 1)`. These are not definitionally equal.
- Use `simp only [cycle2Entry, neg_neg]` before rewriting, or `show` with the normalized form.
- Entry points like `(i, -1, 2-i)` or `(0, j, 1-j)` don't have this issue since no double negation appears.

## Prefer named `have` over inline closures for safe conditions
- Inline `fun t ht => by ...` closures with multiple `have` steps can cause parse errors.
- Extract to a named `have hi_safe : ∀ t < n, ... := by ...` before the `rw` call.

## `congr 1; ring` for tuple closing
- `congr 1; ring` is more reliable than `simp only [Prod.mk.injEq]` + `⟨rfl, rfl, rfl⟩` for tuple goals where one component needs `ring`. Avoids the `True` simplification issue.

## Mathlib name gotchas (v4.28)
- `div_lt_iff` / `div_le_iff` → use `div_lt_iff₀` / `div_le_iff₀` (with subscript zero)
- `Set.indicator_of_notMem` (not `indicator_of_not_mem`)
