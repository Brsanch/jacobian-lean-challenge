# Downstream-consumer audit for `DBarSolvabilityAtGenusZero`

> **⚠️ SUPERSEDED snapshot. Canonical current state for Item 14 lives
> in [`HANDOFF_ITEM14.md`](HANDOFF_ITEM14.md) "ACTIVE ARC — CANONICAL
> CURRENT STATE". This file remains for the analytical content but
> its "honest options going forward" recommendations are framed as
> if `DBarSolvabilityAtGenusZero X` were the load-bearing wall on its
> own; the canonical statement clarifies it is ONE of five
> textbook-equivalent names for the same classical wall. Discharging
> the wall via any of those names closes Item 14 via in-tree
> transport. The cost framing in this audit (multi-month / multi-
> thousand-LOC for abstract X) remains accurate.**

**Date**: 2026-05-26.
**Context**: Before committing 600-900 LOC to Phase B (Behnke-Stein
on the disk), check whether the named hypothesis can be discharged
for `RiemannSphere` alone, or whether it strictly requires the
abstract-`X` formulation for downstream closure.

## The consumer chain (verbatim from the repo)

```
DBarSolvabilityAtGenusZero X + ChartAtConstantOnSource p
    ↓ (Manifold/ForsterCutoffPoleConstruction.lean:1354,
       theorem existsSimplePoleGermAtSomePoint_of_dbarSolvability_under_chartConst)
ExistsSimplePoleGermAtSomePoint X       (hSP X)
    ↓ (Topology/Item14FromHSPOnly.lean:63,
       theorem genus_eq_zero_iff_homeo_from_hSP)
genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2)        (Item 14 headline)
```

Every link in the chain takes abstract
`X : Type u` with `[TopologicalSpace X] [T2Space X] [CompactSpace X]
[ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]` —
no concrete-`X` specialization.

## Can the discharge be RiemannSphere-only?

**No.** The Item 14 headline is universally quantified over `X` (a
biconditional about any compact connected Hausdorff complex
1-manifold). Discharging `DBarSolvabilityAtGenusZero RiemannSphere`
alone closes the forward direction of Item 14 *only* for
`X = RiemannSphere`, which is trivially closed: `RiemannSphere ≃ₜ
StandardS2` by construction, so the biconditional reduces to
`genus RiemannSphere = 0 ↔ True`, and the forward direction is
`genus RiemannSphere = 0 → True`, vacuous.

The non-trivial content of Item 14 is the universal-`X` closure.
For that, the discharge must hold on the abstract `X`.

## What does abstract-`X` discharge require?

`H¹(X, O) = 0` for compact genus-0 `X`. Classical proofs:

1. **Uniformization** (`X compact + genus 0 → X ≃_holomorphic ℂℙ¹`) +
   Cousin I on `ℂℙ¹`. **Uniformization is a major theorem not in
   mathlib at this pin.** Estimated formalization cost: years, not
   months.

2. **Riemann-Roch / Serre duality + degree counting**. Algebraic,
   uses index theory + Hodge theory tools. Comparable to (1) in
   mathlib-formalization cost.

3. **Hodge / L² ∂̄**. Green's-function-of-Laplacian construction.
   Requires L² Sobolev infrastructure not at this pin.

4. **Behnke-Stein iteration on X directly**. Classical Behnke-Stein
   is for non-compact (Stein) RS where `H¹(X, F) = 0` for all
   coherent `F`. **Compact-`X` is NOT covered by classical
   Behnke-Stein** — confirmed by Forster Ch.14 / McMullen Berkeley
   241/96 audit.

5. **Direct partition-of-unity / OmegaForm path**. Original Route I.
   **Fails: chart-transition factors do not cancel via
   partition-of-unity on functions** (see
   `ROUTE_5_5C_FORSTER_AUDIT.md`). Even under the additional
   structural hypothesis `ChartAtConstantOnSource p` globally on
   `X` (chartAt locally constant on each chart's source — a global
   strengthening of the per-point hypothesis the Forster cutoff
   already takes), there is still a residual **outer-ring
   cutoff-leakage error** `Σ_i ∂̄χ_i · K_i(chart_{i.val} y)` that
   does not cancel without iteration.

## Where this leaves Phase B

**Phase B (Behnke-Stein iteration on the disk)** remains the right
analytic primitive to build, but it **does not by itself close
`DBarSolvabilityAtGenusZero X`** on compact genus-0 `X`. Phase B
gives:

* On each chart of `X`, a smooth function with the right
  `∂̄`-derivative.
* Local solvability of `∂̄u = α` on every disk / open subset of `ℂ`.

The compact-`X` closure additionally needs **one** of:

* (A) Uniformization → ℂℙ¹ + Cousin I (Phases C/D + uniformization
  proof).
* (B) An iteration scheme that ACTUALLY converges on the compact `X`
  (needs new analytic content not in classical references — the
  outer-ring leakage error doesn't have a partition-of-unity
  cancellation, so a non-trivial contraction estimate is required).
* (C) Direct algebraic-topology proof of `H¹(X, O) = 0` for
  compact genus-0 `X`. Equivalent in difficulty to (A).

## Honest re-assessment

Closing `DBarSolvabilityAtGenusZero X` for abstract `X` at this
mathlib pin is **substantially harder** than the original Route III
plan estimated. The 800-1200 LOC / 5-6 session estimate from the
`ROUTE_5_5C_AUDIT.md` addendum is too optimistic; the realistic
estimate for any of (A), (B), or (C) is **multi-month, multi-
thousand-LOC** work.

## Honest options going forward

1. **Stop chip work on `DBarSolvabilityAtGenusZero X` discharge.**
   Treat it as a permanent "named classical hypothesis" of the
   challenge response — like Buzzard's original challenge signature
   leaving difficult classical theorems as named inputs. Document
   clearly that this is the irreducible bottleneck at this mathlib
   pin. Item 14 closure remains conditional on the named
   hypothesis. **Honest, accepts limits, no LOC bloat.**

2. **Build Phase B as a foundational mathlib-style contribution.**
   `H¹(Δ, O) = 0` and `H¹(ℂ, O) = 0` are valuable in their own
   right. Land Phase B (600-900 LOC) as analytic infrastructure
   without claiming it closes Item 14. Then revisit Phases C/D
   later if uniformization-light or another path becomes feasible.

3. **Pursue the abstract path despite the cost** — Route III revised:
   Phase B (~600-900 LOC) + Phase C/D (Cousin I + uniformization,
   ~3000-5000+ LOC). Multi-month, no guarantee of closure.

4. **Re-architect the challenge response** to avoid the
   `DBarSolvabilityAtGenusZero X` bottleneck. Replace the Forster
   §16.9 simple-pole construction with a different forward-leg
   route that avoids requiring `H¹(X, O) = 0` directly. Highly
   speculative — no known alternative architecture at this
   mathlib pin.

## Recommendation

Option (1) or Option (2). The cost of (3) is not justified by the
expected value at this mathlib pin. (4) is speculative.

Option (2) ships valuable analytic content with no false claims
about Item 14 closure. Option (1) is the most honest about the
permanent bottleneck.
