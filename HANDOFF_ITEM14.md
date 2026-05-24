# Item 14 — handoff

Last refreshed: 2026-05-24 (Alt-B étale-space arc, Chip 3 landed and
pushed: branch `feat/item14-affineChartTriangleSimplex-ball` @ b278adb,
new file `Manifold/EtalePrimitivesIsLocalHomeomorph.lean`).

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

## Alt-B progress (this session, 3 chips landed)

Chips 1-3 below are now in tree on
`feat/item14-affineChartTriangleSimplex-ball`. Next chip (4) is the
monodromy application.

* **Chip 1** (`Manifold/EtalePrimitives.lean`, e3d9672) — étale space
  `EtalePrimitives om := { point : X, primValue : ℂ }`, basic-sheet
  topology, `proj : EtalePrimitives om → X` with continuity.
* **Chip 2** (`Manifold/ChartLocalPrimitiveOverlapLocallyConst.lean`,
  d1acae3) — `chartLocalPrimitive_diff_locallyConstant_at_overlap`:
  `F_y − F_{y'}` is locally constant on the chart-ball overlap. Proof
  via `mfderiv_sub` + cascade FTC + chart-pullback +
  `IsOpen.is_const_of_fderiv_eq_zero` on a Euclidean ball.
* **Chip 3** (`Manifold/EtalePrimitivesIsLocalHomeomorph.lean`, b278adb)
  — `isLocalHomeomorph_proj : IsLocalHomeomorph (proj om)`. For each
  `(y, c_off)`, the basic sheet at `(y, source(y), c_off)` is the source
  of an `OpenPartialHomeomorph` to `(convexBallChartAt y).source`,
  with `proj` as forward and `chartSectionTotal om y c_off` as inverse.
  Continuity of the inverse uses Chip 2 via
  `tendsto_nhds_generateFrom_iff`.

**Next chip (4): apply mathlib monodromy.**

The remaining ingredient on simply-connected X is mathlib's
`IsLocalHomeomorph.existsUnique_continuousMap_lifts` (in
`Mathlib.Topology.Homotopy.Lifting`). It requires:
- `IsLocalHomeomorph (proj om)` ✓ (Chip 3).
- `SimplyConnectedSpace X` — assumption of the BSLB-discharge target.
- `LocPathConnectedSpace X` — follows from `ChartedSpace ℂ X` since `ℂ`
  is locally path-connected; check mathlib for the relevant instance,
  may need a small bridge lemma.
- `PathConnectedSpace X` — follows from `ConnectedSpace X` +
  `LocPathConnectedSpace X`; mathlib has
  `ConnectedSpace.pathConnectedSpace` or similar.
- Lifting hypotheses: existence + uniqueness of path lifts. For our
  étale space these are exactly the analytic-continuation properties
  Chip 3 packages.

Concrete first chip for Alt B (now Chip 4):

1. ~~Define the étale space~~ — DONE in Chip 1.

2. ~~Show `p` is a local homeomorphism~~ — DONE in Chip 3 as
   `isLocalHomeomorph_proj`. (Whether it's also a covering map is
   stronger than what `existsUnique_continuousMap_lifts` requires.)

3. **Apply `existsUnique_continuousMap_lifts`** with `f := id : X → X`,
   `a₀ := x₀`, `e₀ := ⟨x₀, 0⟩`. Provide the existence + uniqueness of
   path lifts using `IsLocalHomeomorph.existsUnique_continuousMap_lifts`'s
   hypotheses. The two hypotheses to verify are the same shape mathlib
   uses for any étale-space monodromy argument.

4. **Conclude**: a continuous section `s : X → EtalePrimitives om` with
   `proj ∘ s = id` and `s x₀ = ⟨x₀, 0⟩`. Its primValue component
   `F := primValue ∘ s : X → ℂ` is the candidate global primitive.
   Smoothness of `F` follows from
   `continuousOn_chartSectionTotal` + uniqueness (`s` agrees locally
   with `chartSectionTotal om y c_off` on each chart-ball source, by
   uniqueness of path lifts through `proj`).

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

As of Chip 3 (b278adb), the branch IS pushed to origin. Always
re-verify with `git log origin/feat/item14-affineChartTriangleSimplex-ball..HEAD`
before claiming "pushed" or "not pushed" — state changes per session.
