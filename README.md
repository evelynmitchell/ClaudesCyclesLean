# ClaudesCyclesLean

A Lean 4 formalization of Knuth's **"Claude's Cycles"** construction
([paper](https://www-cs-faculty.stanford.edu/~knuth/papers/claude-cycles.pdf)),
proving that three direction maps on (ℤ/mℤ)³ produce an arc-disjoint
Hamiltonian decomposition for all odd m ≥ 3.

## Main Result

```lean
theorem claudes_cycles_hamiltonian_decomposition
    (hm : 2 < m) (hm_odd : Odd m) :
    -- Each cycle is Hamiltonian (visits all m³ vertices)
    (∀ c : CycleIndex, ∀ v : V m,
      (cycleStep c)^[m ^ 3] v = v) ∧
    -- The three cycles are arc-disjoint (use distinct directions at each vertex)
    (∀ v : V m, Function.Injective (fun c => dirMap c v))
```

No sorry's remain. The proof is fully symbolic — it holds for all odd m ≥ 3,
not just specific values. Computational verification for m = 3 and m = 5 is
also included via `native_decide`.

## File Structure

| File | Lines | Description |
|------|------:|-------------|
| `Defs.lean` | 82 | Vertex type V m = (ℤ/mℤ)³, directions, bump, fiber |
| `DirectionMap.lean` | 91 | Direction tables for all three cycles, `cycleStep` |
| `Permutation.lean` | 44 | Arc-disjointness: three cycles use distinct directions at each vertex |
| `BlockAnalysis.lean` | 1046 | Block decomposition for all three cycles: step lemmas, fiber cycles, iterated laps, block transitions, entry point periodicity |
| `Hamiltonian.lean` | 902 | Orbit injectivity → period for all vertices, for all three cycles |
| `Verify.lean` | 65 | Computational verification for m = 3 and m = 5 |
| **Total** | **2238** | |

## Proof Architecture

The proof follows the same pipeline for each cycle:

1. **Step lemmas** — case-split the direction table by fiber value and coordinate conditions
2. **Intermediate runs** — m−2 consecutive steps through "middle" fibers bump one coordinate uniformly
3. **Fiber cycles (laps)** — m steps return to the starting fiber; net coordinate shift depends on position
4. **Iterated laps** — n laps compose; a "safe condition" ensures no case-switching mid-block
5. **Block transition** — m² steps from entry point e(x) reach entry point e(x + shift)
6. **Entry point periodicity** — m³ steps return every entry point to itself
7. **No early return** — orbit injectivity within and across blocks
8. **Period for all vertices** — every vertex is in some entry point's orbit

The shift parameter and entry point definition vary by cycle:
- **Cycle 0**: entries `(i, −1, 2−i)` at fiber 1, shift +1 per block
- **Cycle 1**: entries `(0, j, 1−j)` at fiber 1, shift +1 per block
- **Cycle 2**: entries `(0, j, −j)` at fiber 0, shift +(m−2) per block

The key algebraic ingredient is that −2 is a unit in ℤ/mℤ when m is odd
(`neg_two_isUnit`), ensuring orbit injectivity for all three cycles.

## Building

Requires Lean 4 v4.28.0 and Mathlib v4.28.0.

```bash
# First build fetches Mathlib cache (~5 min)
lake exe cache get
lake build
```

## Project Diary

This formalization was completed over 5 days (March 3–7, 2026) in a
collaboration between a human mathematician and Claude (Anthropic's AI
assistant), using the Claude Code CLI tool. The workflow followed a strict
plan-review-implement cycle: Claude proposed a plan for each PR, the human
reviewed and approved it, then Claude implemented and the human reviewed
the code before merging.

### Timeline

**Day 1 (Mar 3):** Project scaffold — type definitions, direction maps,
basic lemmas, computational verification for m = 3, 5. The permutation
property (arc-disjointness) was proved immediately by case analysis.
Four sorry's remained: `cycle0_period`, `cycle0_orbit_size`,
`cycle1_period`, `cycle2_period`. (PRs #1–#2)

**Days 2–3 (Mar 4–5):** Cycle 0 block analysis pipeline — step lemmas,
ZMod helpers, intermediate runs, fiber cycles (3 cases × bump/non-bump),
iterated fiber cycles, block transition, entry point periodicity, no
early return. This was the longest phase, establishing the proof pattern
that cycles 1 and 2 would reuse. (PRs #14–#22)

**Day 4 (Mar 6):** Cycle 1 — same pipeline but simpler (uniform
intermediate run, only 2 fiber cycle cases). Filled `cycle1_period`.
(PRs #23–#24)

**Day 5 (Mar 7):** Cycle 2 — the most complex direction table (4 lap
cases), but the established pattern made it straightforward. Discovered
that fiber-0 entry points `(0, j, −j)` give cleaner block transitions
than fiber-1 alternatives. The `not_entry_within_block` proof required a
new sub-lemma (`c2_entry_i_ne_zero_of_lap`) since fiber-0 entry points
can't be distinguished by fiber alone at multiples of m. Filled
`cycle2_period` — zero sorry's remain. (PRs #25–#26)

### Statistics

- 35 commits across 26 PRs
- 2,238 lines of Lean 4
- 4 sorry's eliminated
- ~155 lines of "gotchas" documentation accumulated

### Lessons Learned

**Prototyping proofs in isolation** (via `lean_run_code`) before inserting
them into the real file prevented most compilation surprises and saved
significant build time.

**The modular pipeline was essential.** Each cycle followed the same
7-step proof structure. Once cycle 0 was done (~700 lines across two
files), cycles 1 and 2 followed the template with only the
cycle-specific algebra changing.

**ZMod arithmetic with symbolic m is tricky.** `omega` can't handle
multiplication of variables. `ring` doesn't know `↑(m−1) = −1`. Natural
subtraction interacts badly with `rw`. These required a growing library
of helper lemmas (`natCast_m_sub_one`, `natCast_m_sub_two`,
`neg_two_isUnit`) and careful proof structuring.

**Lean 4 / Mathlib gotchas are real.** `Prod.mk.injEq` sometimes
simplifies tuple components to `True`, breaking expected proof
structure. `neg_neg` is not definitionally equal. Import visibility
(`private` lemmas) causes silent failures. Each individually small,
but collectively they accounted for a significant fraction of debugging
time.

## License

Apache 2.0 — see [LICENSE](LICENSE).
