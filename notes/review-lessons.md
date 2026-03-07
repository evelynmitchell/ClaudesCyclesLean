# Planning & Review Lessons (from connesLean)

## Workflow
1. **Plan** — write plan, user reviews, revise
2. **Corner cases** — user asks, revise
3. **Fine-tooth-comb** — verify Mathlib API names during plan review (not implementation)
4. **User accepts** the plan
5. **Implement** — no code before step 4
6. **Push + create PR**
7. **Copilot review** — only after PR exists

## Key Principles
- Verify Mathlib API names during plan review using search tools, not during implementation
- Mark each API as "verified" or "manual proof needed" in the plan
- Write Lean in ~100-150 line chunks, check diagnostics after each
- Test helpers in isolation before assembling full file
- Prototype ENNReal/ZMod arithmetic proofs first — type system happy-path is not obvious
- When first approach gets messy (>3 edit-diagnose cycles), scrap and simplify
- Finiteness proofs are cheaper than bound proofs — only compute tight bounds when needed downstream
- Ship clean definitions + basic properties rather than attempt complex assembly with sorry

## Axiom Design (if needed)
- Weakest hypotheses needed (closest to actual theorem)
- Every axiom needs executable soundness tests, not just comments
- Try to construct axiom for pathological inputs — if trivially constructible, axiom is too strong

## Branch Management
- Check if current branch already has a PR before `gh pr create`
- For independent work, create fresh branch from main
- Include tests in every PR (compile-time `example` exercising each export)

## Implementation Discipline
- Follow proof sketches exactly — don't deviate from verified API names
- Check `omit` annotations for ALL new theorems in one pass, not one at a time
- Run diagnostics once after writing all code, not after each individual fix (reduces round-trips)
