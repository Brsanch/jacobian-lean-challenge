# Item 14 — handoff

Last refreshed: 2026-05-24 (after the chartLocalPrimitive maxAtlas
cascade, 16 commits this session, branch
`feat/item14-affineChartTriangleSimplex-ball`, not yet pushed).

## TL;DR

The reverse leg of Item 14 (`S2ImpliesGenus0 X`) on arbitrary compact
connected complex 1-manifold X has been reduced — unconditionally —
to **one named classical input**:

```
SimplyConnectedSpace X → BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀
```

(per `s2ImpliesGenus0_of_basedSmoothLoopsBoundHypothesis_unconditional`
in `Topology/S2ImpliesGenus0FromBSLBUnconditional.lean`).

Equivalently: every smooth loop on a simply-connected X bounds *some*
smooth 2-chain.

All other analytic + topological inputs are unconditionally discharged
in tree:
* `simplyConnectedS2_holds`,
* `smoothPathConnected_of_preconnected`,
* `chartContainedLoopVanishingHypothesis_holds_unconditional`,
* `holomorphicStokesHypothesis_holds_unconditional`,
* and (new this session) `chartLocalPrimitive{SmoothExt,FTC}Max_convexBallChartAt`.

## Read this on entry

* `AUDIT_LOOP_PERIOD_VANISHES.md` — full audit of the remaining gap,
  including four alternative routes and why none is a "shortcut".
* This file.
* `OPEN.md` — repo-wide per-item status (look for the "Authoritative
  current state" header).
* `REPO_AUDIT.md` — chain-trace per `sorry`.
* `tools/chip-prompt-preamble.md` — 7 anti-paraphrase gates (load
  before any new chip).

## What landed this session (16 commits)

The "chartLocalPrimitive maxAtlas cascade" — a structural refactor of
the chart-local primitive arc to take charts in the ℝ-`⊤` maximal
atlas instead of the canonical `atlas`. The maxAtlas form accepts
`convexBallChartAt y` (= `(chartAt ℂ y).restr (chartBallSourcePreimage y)`,
which has convex target unconditionally), eliminating the previous
"convex target of `chartAt ℂ y`" obstruction that blocked the chip-A/B/D
arc on arbitrary X.

Steps:
1. `chartLocalPrimitiveMax` data def + basepoint identity.
2. `chartLocalPrimitiveExtendMax` total-function wrapper (incl.
   pathPrimitive bridge lemmas).
3a. `pathPrimitive ↔ chartLocalPrimitiveMax` bridge (Max-form chip-B3
   foundation).
3b. ContMDiffAt / mfderiv transfer Max.
3c. Named hypotheses `ChartLocalPrimitive{SmoothExt,FTC}Max` +
   composition theorems.
4a. Max-form lifts of chartAt-form chip-A/B/D headlines (intermediate
   step, useful when chartAt y happens to have convex target).
4b. rfl bridges showing `chartLocalPrimitiveMax (convexBallChartAt y) =
   chartLocalPrimitiveMax (chartAt ℂ y) (subset_maximalAtlas)` at the
   path and value levels.
4b SmoothExt. `chartLocalPrimitiveSmoothExtMax (convexBallChartAt y)`
   UNCONDITIONALLY on arbitrary X — the genuine analytic content,
   ~250 LOC. Uses chip-A on the ball + generalised chip-B3 + chart
   smoothness via `contMDiffOn_of_mem_maximalAtlas`.
4b FTC. `chartLocalPrimitiveFTCMax (convexBallChartAt y)` UNCONDITIONALLY,
   ~180 LOC. D4-Max chain rule + D5 atlas reuse.
5. `pathPrimitiveGlobalSmoothFTCMax` admissibility predicate + global
   composition theorems.
6. `pathPrimitiveAdmissibleChartCoverMax_holds` — admissibility
   UNCONDITIONAL via convexBallChartAt y centered at each x. Payoff:
   `pathPrimitive_contMDiff_unconditional` + `pathPrimitive_eval_eq_mfderiv_unconditional`
   on arbitrary X under `LoopPeriodVanishes om x₀`.
7. `s2ImpliesGenus0_of_loopPeriodVanishesOnSimplyConnected` — final
   composition using the cascade.

Plus three follow-up reduction-clarification commits:
* `S2ImpliesGenus0FromSubdivisionTelescopingUnconditional.lean` —
  composes the cascade with `chartContainedLoopVanishingHypothesis_holds_unconditional`.
* `S2ImpliesGenus0FromBSLBUnconditional.lean` — composes via single-
  basepoint BSLB.
* `AUDIT_LOOP_PERIOD_VANISHES.md` — audit + four alternative routes.

## The gap precisely

`HolomorphicStokesHypothesis X` is unconditional in tree
(`Manifold/UniformChartContainmentDepth.lean:289` — Lebesgue + iterated
midpoint subdivision). So the smooth-Stokes side is fully discharged.

Combined with `loopPeriodVanishes_of_basedSmoothLoopsBoundHypothesis`,
a smooth loop γ has zero period **iff** `single γ ∈ stokesBoundaries`
(= the smooth-2-chain boundary image).

Therefore the open content is exactly:

> On simply-connected X, every smooth loop bounds some smooth 2-chain.

Mathlib's `SimplyConnectedSpace` only gives a *continuous* null-
homotopy. Bridging continuous → smooth-bordism is the genuine open
classical content.

## How to continue — four alternative routes

See `AUDIT_LOOP_PERIOD_VANISHES.md` for details. Summary:

| Route | Approach | LOC est | Pro | Con |
|---|---|---|---|---|
| **A** | Polygonal approximation + Van Kampen induction | 500-700 | Reuses fan-triangulation in tree | Van Kampen step is significant Lean |
| **B** | Étale space of primitives + mathlib `monodromy_theorem` | 600-900 | Cleanest math; uses mathlib's monodromy off-the-shelf | Étale-space construction is novel to the tree |
| **C** | Continuous-cell telescoping with Čech-coboundary | 500-800 | Direct cascade reuse | Coboundary content equivalent to smooth Hurewicz |
| **D** | Sard generalisation + chart-by-chart loop completion | 300-500 | Sard generalises beyond RS | `X \ {q} ≅ ℂ` obstruction at factoring step |

All four require the *same classical content* (cohomology of
locally-constant ℂ sheaf vanishes on simply-connected X) packaged
differently. None is a shortcut.

**Recommendation**: Alt B (étale space + mathlib monodromy). It uses
mathlib's `Mathlib.Topology.Homotopy.Lifting.monodromy_theorem` and
`existsUnique_continuousMap_lifts`, which are purpose-built for this
problem and not currently used in tree for anything.

Concrete first chip for Alt B:

1. **Define the étale space of primitives** Et(ω) := `{(x, c) : x ∈ X, c ∈ ℂ}`
   with the topology where a neighborhood of `(x₀, c₀)` is
   `{(x, c) : x ∈ (convexBallChartAt y).source, c = chartLocalPrimitiveMax y x − chartLocalPrimitiveMax y x₀ + c₀}`
   for any y with x₀, x in the chart source. The projection
   `p : Et(ω) → X, (x, c) ↦ x` is a local homeomorphism by the
   cascade's chart-local primitive uniqueness.

2. **Show `p` is a covering map** (or just a local homeomorphism with
   the path-lifting needed for `existsUnique_continuousMap_lifts`).
   The fiber over `x` is ℂ.

3. **Apply `existsUnique_continuousMap_lifts`** with `f := id : X → X`,
   `a₀ := x₀`, `e₀ := (x₀, 0)`. Hypotheses (existence + uniqueness of
   path lifts) come from chart-local-primitive analytic continuation
   + simply-connectedness.

4. **Conclude**: a global section X → Et(ω). Its second component is
   the global primitive F : X → ℂ. Smoothness from local sections
   smoothness (cascade).

5. **Compose with `s2ImpliesGenus0_of_loopPeriodVanishesOnSimplyConnected`**
   (this session, in `Topology/S2ImpliesGenus0FromLoopPeriodVanishesUnconditional.lean`)
   — closes Item 14 reverse leg on arbitrary X.

## Key files added this session

In `JacobianChallenge/Manifold/`:
* `ChartLocalPrimitiveMax.lean`
* `ChartLocalPrimitiveExtendMax.lean`
* `PathPrimitiveChartLocalBridgeMax.lean`
* `PathPrimitiveSmoothnessFromChartLocalMax.lean`
* `PathPrimitiveLocalSmoothFTCNamedMax.lean`
* `ChartLocalPrimitiveSmoothExtFTCChartAtMax.lean`
* `ChartLocalPrimitiveMaxConvexBallChartAt.lean`
* `ChartLocalPrimitiveSmoothExtMaxConvexBallChartAt.lean`
* `ChartLocalPrimitiveFTCMaxConvexBallChartAt.lean`
* `PathPrimitiveGlobalSmoothFTCMax.lean`
* `PathPrimitiveAdmissibleChartCoverMaxUnconditional.lean`

In `JacobianChallenge/Topology/`:
* `S2ImpliesGenus0FromLoopPeriodVanishesUnconditional.lean`
* `S2ImpliesGenus0FromSubdivisionTelescopingUnconditional.lean`
* `S2ImpliesGenus0FromBSLBUnconditional.lean`

Root-level docs:
* `AUDIT_LOOP_PERIOD_VANISHES.md`
* `HANDOFF_ITEM14.md` (this file, refreshed)

## Forward leg status (unchanged this session)

`Genus0ImpliesS2 X` reduces to `RR_DimGE2_GenusZero_Germ X` (Riemann-Roch
at genus 0). The downstream chain (PrincDivWitnessExtraction → degree-1
mero function → bijectiveAnalyticIsBiholomorphism_holds →
genus_eq_zero_iff_homeo_of_HolomorphicEquiv_RiemannSphere) is
unconditional. See HSP_AUDIT.md §4.5 for the cleanest deliverable.
Independent of this session's cascade.

## Discipline notes for next session

The cascade chips are mechanical Max ports of an atlas-form arc — they
collectively reduced a named hypothesis on arbitrary X (per the
anti-paraphrase test). Future work should NOT add more "Max-form" or
"intermediate-bridge" chips; the maxAtlas refactor is complete. The
next chip should attack the smooth-bordism gap directly via one of
the four alternative routes.

**Do not** route through BSLB → smooth Hurewicz via the
RS-specific missed-point + Möbius pattern. That pattern requires
`X \ {q} ≅ ℂ`, which is essentially uniformization — circular for
arbitrary X.

**Do not** add more chips that further reformulate
LoopPeriodVanishes / BSLB / SubdivisionTelescopingToLoop_named into
"from N inputs" forms. The reformulations are exhausted; what's owed
is genuine classical content.

## Worktree commands

```bash
git worktree list      # confirm worktree still pinned
cd "/Volumes/4TB SD/ClaudeCode/jacobian-lean-challenge-item14"
git log --oneline feat/item14-affineChartTriangleSimplex-ball...origin/main
```

The original checkout at `/Volumes/4TB SD/ClaudeCode/jacobian-lean-challenge`
is used by a parallel session on a different branch. Don't `cd` into it.

The branch is **not yet pushed**. Verify with `git log
origin/feat/item14-affineChartTriangleSimplex-ball..HEAD` before
claiming "pushed" anywhere.
