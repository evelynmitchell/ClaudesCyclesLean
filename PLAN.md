# Formalization of Knuth's "Claude's Cycles" in Lean 4

## Context

Knuth's paper (Feb 2026) describes a decomposition of arcs of a digraph on m³ vertices into three
Hamiltonian cycles, discovered by Claude Opus 4.6. The digraph has vertices (i,j,k) in (ℤ/mℤ)³ with arcs
bumping each coordinate by 1. For odd m ≥ 3, Claude's construction assigns a direction (which
coordinate to bump) per cycle per vertex, yielding three arc-disjoint Hamiltonian cycles.

## Setup

1. Install elan + Lean toolchain: `curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain stable`
2. Initialize project: `lake init ClaudesCycles math` (creates lakefile with Mathlib dependency)
3. Fetch Mathlib cache: `lake exe cache get` (~3GB, avoids building from source)
4. Build: `lake build`

## File Structure

```
ClaudesCycles/
  Defs.lean           -- V m, Dir, bump, fiber, basic lemmas
  DirectionMap.lean    -- dirCycle0/1/2, dirMap (Claude's construction)
  Permutation.lean     -- Three directions at each vertex are a permutation
  Hamiltonian.lean     -- Main theorem: each cycle is Hamiltonian
  Verify.lean          -- native_decide checks for m=3, m=5
ClaudesCycles.lean     -- Root import file
```

## Key Design Decisions

- Use `ZMod m` for coordinates: equals `Fin m` definitionally for m ≥ 1, gives modular ring arithmetic for free. Conditions like `j = m-1` become `j = -1` in ZMod.
- Carry `{m : Nat}` with `[NeZero m]` as implicit + instance for all definitions (needed for ZMod to work). Add `(hm : 2 < m)` and `(hm_odd : Odd m)` as explicit hypotheses only where needed.
- `Dir` as inductive type (d0/d1/d2) rather than `Fin 3` — better pattern matching, no coercion noise.

## The Construction (verified against the C code)

The C code uses 5 direction strings, each a permutation of "012":

| Condition         | String | c0     | c1     | c2     |
|-------------------|--------|--------|--------|--------|
| s=0, j=m-1        | "012"  | bump i | bump j | bump k |
| s=0, j≠m-1        | "210"  | bump k | bump j | bump i |
| s=m-1, i>0        | "120"  | bump j | bump k | bump i |
| s=m-1, i=0        | "210"  | bump k | bump j | bump i |
| 0<s<m-1, i=m-1    | "201"  | bump k | bump i | bump j |
| 0<s<m-1, i≠m-1    | "102"  | bump j | bump i | bump k |

Extracted per-cycle direction functions (verified computationally for m=3,5,7,9,11):

- **Cycle 0:** s=0 → (j=-1? d0 : d2); s=-1 → (i≠0? d1 : d2); else → (i=-1? d2 : d1)
- **Cycle 1:** s=0 → d1; s=-1 → (i≠0? d2 : d1); else → d0
- **Cycle 2:** s=0 → (j≠-1? d0 : d2); s=-1 → d0; else → (i≠-1? d2 : d1)

Key ZMod encoding: `m-1 = -1`, `i > 0 ↔ i ≠ 0`, `j < m-1 ↔ j ≠ -1`

## Corner Cases Analyzed

1. **m=3 and constant 2:** When m=3, 2 = -1 in ZMod 3. Entry point (0,-1,2) = (0,2,2). Fiber s = 0+2+2 = 1 (intermediate). Works correctly — verified against paper's 27-vertex trace.
2. **Uniform entry point formula:** ALL i-block entries are (i, -1, 2-i) with fiber s = i+(-1)+(2-i) = 1. This is always in the intermediate range for m ≥ 3. For i = m-1: 2-(m-1) = 3-m = 3 in ZMod m, matching the paper's (m-1, m-1, 3).
3. **The -2 shift is really +(-2):** At s=0 positions within an i-block, j-values follow the arithmetic progression j₀, j₀-2, j₀-4, ... in ZMod m. Since gcd(2,m)=1 (m odd), this visits all m values. Verified for m=5: j-values at s=0 in i=0 block are 2,0,3,1,4 (each step is -2 mod 5).
4. **Permutation property needs NO hypothesis on m:** The six direction table entries are all distinct permutations of {d0,d1,d2}. This holds for any m ≥ 1 with NeZero m. The hypotheses m ≥ 3 and m odd are only needed for Hamiltonicity.
5. **Between s=0 positions:** Exactly m steps occur (one per fiber value 0,1,...,m-1). The fiber advances by 1 each step, cycling back to 0 after m steps. This is the key structural invariant.
6. **The i=m-1 block:** Different from other blocks — the third component k advances (instead of j) in the intermediate case, and the s=m-1 case (instead of s=0) triggers special behavior. The paper handles this separately.

## Implementation Phases

### Phase 1: Definitions + Computational Verification

- Define `V m := ZMod m × ZMod m × ZMod m`
- Define `Dir` inductive, `bump`, `fiber`
- Define `dirCycle0/1/2` and `dirMap` using if-else on s = 0 / s = -1 / else
- Define `cycleStep c v := bump (dirMap c v) v`
- Prove `fiber_bump: fiber (bump d v) = fiber v + 1`
- Verify for m=3,5 via `native_decide` (cycle length = m³, returns to start)

### Phase 2: Permutation Property

- Theorem: `∀ v, dirMap c₁ v = dirMap c₂ v → c₁ = c₂` (injective in cycle arg)
- Proof: `unfold dirMap dirCycle0 dirCycle1 dirCycle2; split_ifs <;> simp [Dir.noConfusion]`
- This is a 6-case analysis, each case trivial since the three directions are always distinct

### Phase 3: Hamiltonian Proof for Cycle 0

Following the paper's block decomposition:
1. **i-stability:** `dirMap .c0 v = .d0 ↔ fiber v = 0 ∧ v.2.1 = -1` (i only bumps when s=0, j=m-1)
2. **Block entry points:** `cycle0Entry i := (i, -1, 2-i)` with fiber = 1
3. **Within-block trajectory:** Define the m² vertices visited in i-block i explicitly
4. **Block length:** `(cycleStep .c0)^[m²] (cycle0Entry i) = cycle0Entry (i+1)`
5. **Block injectivity:** The m² vertices in an i-block are all distinct (uses gcd(2,m)=1)
6. **Combine:** `(cycleStep .c0)^[m³] v = v` and orbit has size m³

The gcd argument: -2 is a unit in ZMod m when m is odd. The orbit of j under j ↦ j - 2 has size m. Mathlib: `ZMod.isUnit_of_coprime` or `ZMod.unitOfCoprime`.

### Phase 4: Cycles 1 & 2 + Main Theorem

- Cycle 1 block structure: organized by k-coordinate (or similar)
- Cycle 2 block structure: different coordinate pattern
- Main theorem: the three cycleStep functions give an arc-disjoint Hamiltonian decomposition
- Statement: `∀ odd m ≥ 3, ∀ c, (cyclePerm c).support = Finset.univ` (each cycle visits all vertices)

### Phase 5: What may need sorry initially

- The within-block injectivity proofs (intricate `Function.Iterate` bookkeeping)
- Cycles 1 and 2 Hamiltonian proofs (parallel to cycle 0 but each needs own analysis)
- These can be filled in incrementally

## Verification Strategy

1. `lake build` — all files compile
2. `lean_diagnostic_messages` — no errors on any file
3. `lean_verify` on key theorems — check axiom usage (no sorry, only standard axioms + ofReduceBool for native_decide)
4. `native_decide` for m=3,5 — computational confidence in definitions
5. Cross-check m=3 cycle 0 output against paper's 27-vertex trace
