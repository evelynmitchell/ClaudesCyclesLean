# Issue #11: cycle0_period and cycle0_orbit_size

## Dependencies
- `cycle0_period_entry` (#9) — entry points periodic with period m³
- `c0_not_entry_within_block` (#10) — no early return within blocks
- `cycle0_entry_shift` (#9) — f^[n*m²](entry i) = entry(i+n)

## Proof strategy
1. cycleStep c0 is injective (direction case analysis)
2. Orbit of entry 0 has no short period (entry_shift + not_entry_within_block)
3. Orbit of entry 0 = all of V m (card argument: m³ distinct elements = |V m|)
4. cycle0_period: any v = f^k(e0), commute f^[m³] past f^k
5. cycle0_orbit_size: injectivity of k ↦ f^k(v) from no-short-period + commutation

## Lemma 1: cycleStep_c0_injective (~8 lines)
```lean
theorem cycleStep_c0_injective (hm : 1 < m) :
    Function.Injective (cycleStep .c0 : V m → V m)
```
Proof (verified in lean_run_code with file's direct imports):
```
intro ⟨i1, j1, k1⟩ ⟨i2, j2, k2⟩ h
simp only [cycleStep_def, dirMap_c0] at h
unfold dirCycle0 at h; simp only at h
split_ifs at h <;>
  simp only [bump, Prod.mk.injEq] at h <;>
  obtain ⟨rfl, rfl, rfl⟩ := h <;>
  first | rfl | contradiction
```
- Same-direction: coord equalities give rfl
- Cross-direction: direction conditions contradict coord equalities

## Lemma 2: cycle0_no_short_period (~15 lines)
```lean
theorem cycle0_no_short_period (hm : 2 < m) (hm_odd : Odd m) (n : ℕ)
    (hn : 0 < n) (hn' : n < m ^ 3) :
    (cycleStep .c0)^[n] (cycle0Entry 0) ≠ cycle0Entry 0
```
- Write n = q * m² + r via Nat.div_add_mod (q = n / m², r = n % m²)
- Bounds: r < m², q < m (from n < m³)
- f^[n](e0) = f^[r](f^[q*m²](e0)) = f^[r](entry q) via cycle0_entry_shift
- Case r > 0: f^[r](entry q) = entry 0 contradicts c0_not_entry_within_block
- Case r = 0: entry q = entry 0 → (q : ZMod m) = 0 → m ∣ q, but 0 < q < m

## Lemma 3: card_V (~3 lines)
```lean
theorem card_V : Fintype.card (V m) = m ^ 3
```
- `simp [V, Fintype.card_prod, ZMod.card]; ring`

## Lemma 4: cycle0_orbit_eq_univ (~10 lines)
```lean
theorem cycle0_orbit_eq_univ (hm : 2 < m) (hm_odd : Odd m) :
    Finset.image (fun k => (cycleStep .c0)^[k] (cycle0Entry 0))
      (Finset.range (m ^ 3)) = Finset.univ
```
- Image card = m³ by Finset.card_image_of_injective (using no_short_period + injectivity)
- Fintype.card (V m) = m³
- Finset.eq_univ_of_card closes it

## Lemma 5: cycle0_period (~5 lines)
```lean
theorem cycle0_period (hm : 2 < m) (hm_odd : Odd m) (v : V m) :
    (cycleStep .c0)^[m ^ 3] v = v
```
- From orbit_eq_univ: v ∈ image, so ∃ k, v = f^k(e0)
- f^[m³](f^k(e0)) = f^k(f^[m³](e0)) = f^k(e0) = v
- Commutation: iterate_add_apply + Nat.add_comm

## Lemma 6: cycle0_orbit_size (~8 lines)
```lean
theorem cycle0_orbit_size (hm : 2 < m) (hm_odd : Odd m) (v : V m) :
    Finset.card (Finset.image (fun k => (cycleStep .c0)^[k] v)
      (Finset.range (m ^ 3))) = m ^ 3
```
- If f^a(v) = f^b(v) with a < b < m³: f^[b-a](v) = v by injectivity
- v = f^s(e0) → f^[b-a](e0) = e0 → contradicts no_short_period
- So k ↦ f^k(v) injective on range(m³)
- Finset.card_image_of_injective + Finset.card_range

## Key Mathlib API (verified available in file's import closure)
- `Function.Injective.iterate` — iterated injectivity
- `Finset.card_image_of_injective` — card image = card domain
- `Finset.card_range` — card range(n) = n
- `Finset.eq_univ_of_card` — full card → univ
- `Function.iterate_add_apply` — f^[a+b] x = f^[a](f^[b] x)
- `ZMod.card` / `Fintype.card_prod` — for card_V

## Estimated size: ~50 lines

## Risks
- Nat arithmetic for extracting q, r from Nat.div_add_mod + bounds
- Constructing InjOn proof for Finset.card_image argument
- omega can't handle m² or m³ (need Nat.pow_two, explicit calc)
