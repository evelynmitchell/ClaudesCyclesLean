# ClaudesCyclesLean Project Memory

## Project
Lean 4 formalization of Knuth's "Claude's Cycles" — arc-disjoint Hamiltonian decomposition of (Z/mZ)^3 for odd m >= 3.

## Build
- Lean 4 v4.28.0, uses Mathlib v4.28.0
- `lake` is at `~/.elan/bin/lake` — must add to PATH: `export PATH="$HOME/.elan/bin:$PATH"`
- Build times are 10-17 min per full module rebuild; batch all changes before rebuilding
- To rebuild only one module: `rm -rf .lake/build/{lib,ir}/ClaudesCycles/Hamiltonian.*` then `lake build ClaudesCycles.Hamiltonian`

## Workflow (from connesLean)
- **One PR per session**, push for Copilot review, wait for user approval, then merge
- Plan → **get user review of plan** → implement. Never skip plan review.
- Write Lean in ~100-150 line chunks, check diagnostics after each. Never >200 lines without check.
- Verify Mathlib API names during plan review, not during implementation
- Prototype proofs in isolation before assembling full file
- Include tests in every PR (compile-time `example` exercising each export)

## Detailed Notes
- [lean4-gotchas.md](lean4-gotchas.md) — Lean 4 syntax/parsing pitfalls
- [mathlib-notes.md](mathlib-notes.md) — Mathlib lemma names and patterns
- [review-lessons.md](review-lessons.md) — Planning and review process lessons (from connesLean)
- [issue4-proofs.md](issue4-proofs.md) — Verified proof sketches for ZMod helper lemmas
- [issue7-proofs.md](issue7-proofs.md) — Verified proof sketches for iterated fiber cycle lemmas
- [issue8-proofs.md](issue8-proofs.md) — Verified proof sketches for block transition theorem

## Current State (2026-03-07)
- PRs merged: #1, #2, #14-#24
- PR #25 open: cycle 2 block analysis (#13 part 1)
- PR #26 open: cycle 2 period (#13 part 2, based on #25)
- **0 sorry's remain** — formalization is complete
- `claudes_cycles_hamiltonian_decomposition` fully proved
- Merge order: #25 first, then rebase #26 onto main
