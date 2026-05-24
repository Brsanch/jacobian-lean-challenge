# Item 14 — handoff

Last refreshed: 2026-05-23 (BSLB scope correction + path-partition chip).

## Actual state (verified by tracing the in-tree named-hypothesis chain to leaves)

Item 14 is `Basic.lean:73` —
```
genus_eq_zero_iff_homeo : genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2)
```
on arbitrary compact connected complex 1-manifold X.

The cleanest in-tree reduction is
[`Item14ViaSubsingletonFromBSLBAndAdmissibility.lean`](JacobianChallenge/Topology/Item14ViaSubsingletonFromBSLBAndAdmissibility.lean):

```lean
genus_eq_zero_iff_homeo_via_subsingleton_from_BSLB_and_universalAdmissibility
    (x₀ : X)
    (hSP : ExistsSimplePoleGermAtSomePoint X)
    (h_bslb : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀)
    (h_admit : ∀ om, PathPrimitiveAdmissibleChartCover om) :
    genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2)
```

`h_admit` is auto-provided by the `HasAdmissibleChartCover` typeclass
+ the chart-cover-lift instance shipped 2026-05-23.

**So item 14 closes on arbitrary X once we discharge TWO named hypotheses:**

1. **`hSP : ExistsSimplePoleGermAtSomePoint X`** — Riemann-Roch dim ≥ 2 at
   genus 0. Bottom of the chain (`Topology/RRGenusZeroFinrankChain.lean`
   → `Topology/RRDimensionFormGerm.lean`) is `RR_DimGE2_GenusZero_Germ X`
   (germ-form RR dim bound). Not in mathlib. Single classical statement.

2. **`BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀`** — every smooth based
   loop bounds a smooth 2-chain. Per
   [`Manifold/BasedSmoothLoopsBoundFromFactorisation.lean`](JacobianChallenge/Manifold/BasedSmoothLoopsBoundFromFactorisation.lean),
   reduces to `LoopFactorsThroughVectorSpaceHypothesis ℂ X x₀`. On RS,
   discharged via missed-point + chartN-pullback. The
   **missed-point part is generic** (Sard via Hausdorff dimension,
   `SmoothLoopHasMissedPointDischarge.lean`) — just specialized to RS.
   General-X discharge has two known routes:
   - (a) `Smooth2Simplex` refactor from `ContMDiff` to
     `ContMDiffOn [0,1]²`, which unblocks the chain-assembly path
     already in tree. Per earlier HANDOFF: "one chip away once the
     refactor lands."
   - (b) Generalize missed-point + chart-pullback factorisation to
     arbitrary X (needs an analog of RS's chartN/Möbius structure).

## What is UNCONDITIONAL in tree (verified sorry-free 2026-05-23)

Don't re-derive these; they exist:

- `FiniteDimensional ℂ (HolomorphicOneForm X)` — `DiskChartCover.holomorphicOneFormFiniteDim_holds`.
- `ramificationSumEqualsDegree_holds_unconditional` (Riemann-Hurwitz sum).
- `surjective_of_NonConstant_Analytic_Manifold_holds`.
- `bijectiveAnalyticIsBiholomorphism_holds`.
- `liouvilleOnCompactConnected_holds` (holomorphic on compact connected ⟹ constant).
- `RiemannSphere.toSphereHomeo : RiemannSphere ≃ₜ StandardS2`.
- `meromorphicIdentityPropagation_holds`.
- `Subsingleton (HolomorphicOneForm RiemannSphere)` (via overlap-formula).
- All of chip-D arc (chartLocal primitive smoothness + FTC at chartAt ℂ y).
- `HasAdmissibleChartCover` typeclass + instances on RS and `ℂ ⧸ L` via
  `HasConvexChartAtTarget`.

## What was the 2026-05-23 session's actual contribution

Net useful: ONE typeclass + instance — `HasConvexChartAtTarget X` →
`HasAdmissibleChartCover X` (auto-provides `h_admit`). Repo did not
need the redundant `Item14From2InputsUnderConvexChartAt.lean` (duplicates
the existing `Item14ViaSubsingletonFromBSLBAndAdmissibility.lean`) or
the chip-D arc ω-level work in the critical path (the existing in-tree
machinery already worked at the needed regularity level).

Net negative: ~385 LOC of paraphrase chips that look like progress but
don't move the actual frontier. See
`tools/chip-prompt-preamble.md` (added 2026-05-23) for the 7 hard
anti-paraphrase gates installed afterwards.

## Path A progress (branch `feat/item14-affineChartTriangleSimplex-ball`, 3 commits, 2026-05-23)

The handoff above estimated Path A as a `Smooth2Simplex` ContMDiff →
ContMDiffOn refactor cascading through ~79 files. On inspection the
actual blockage was narrower: one single definition
(`affineChartTriangleSimplex_univ`) required `h_univ`, propagating
through `chartStraightLinePath_univ`, `fanChain`, etc. A focused
ball-data path was built instead — no structural refactor of
`Smooth2Simplex`, no cross-file cascade.

What landed on the branch (verified, full manifest green,
LEAN_NUM_THREADS=1 single-threaded; ~1,035 LOC across 3 new files):

1. `Manifold/AffineChartTriangleSimplexBall.lean` — drops `h_univ` from
   the chart-triangle simplex constructor. Takes chart-image-in-ball
   data (`Metric.ball z_c r ⊆ (chartAt ℂ q).target` and three corner
   points in the ball). Construction: bump-extend the affine map via
   `exists_contMDiffMap_zero_one_of_isClosed` on the standard simplex
   inside an open neighborhood where the affine map lands in the ball;
   convex-combine with the ball center for global ambient extension;
   compose with `(chartAt ℂ q).symm` (ContMDiffOn on chart target) via
   `ContMDiffOn.comp_contMDiff`.

2. `Manifold/ChartStraightLinePathBall.lean` — `chartStraightLinePath_ball`
   defined canonically as `face2` of the degenerate ball triangle
   `(z₀, z₁, z₀)`. Three face-equality lemmas + the ball-triangle
   boundary identity.

3. `Manifold/FanTriangulationBall.lean` — ball-data analog of
   FanTriangulation.lean. `fanChain_ball`, `polygonalChain_ball`,
   `spokeResidue_ball` (List ℂ + `∀ z ∈ zs, z ∈ ball` hypothesis;
   uses Lean 4 proof irrelevance for spoke cancellation across adjacent
   triangles). Same induction structure as the univ version's
   `boundary₂_fanChain`, with revert/intro ceremony for the dependent
   hypothesis and a `chartStraightLinePath_ball_congr_tgt` helper for
   `getLast` rewrites under proof irrelevance. **Headline**:
   `polygonalChain_ball_smoothCycle_mem_stokesBoundaries_of_closed`
   — on arbitrary compact connected complex 1-manifold X, a closed
   polygonal loop with all vertices in a common chart-image ball has
   its SmoothCycle in `stokesBoundaries`.

This is the chart-local building block for the BSLB chain-assembly
arc. `UniformChartContainmentDepth_named X` (already unconditional in
tree, see `Manifold/UniformChartContainmentDepth.lean`) provides the
per-subdivision chart-image ball.

## Audit findings (2026-05-23, after deep top-down trace from `Basic.lean`)

Item 14's `genus_eq_zero_iff_homeo X` factors through
`SurfaceClassificationGenus.toIff` into **two independent named
hypotheses** (`Genus0ImpliesS2` and `S2ImpliesGenus0`), each of which
has its own discharge chain in tree. They do not need to be closed by
the same route.

**Reverse leg (`S2ImpliesGenus0 X`)** reduces, via
`s2ImpliesGenus0_from_subsingletonOfSimplyConnected X` +
`simplyConnectedS2_holds` (unconditional, in tree), to a single
classical theorem:

> *On a simply-connected compact connected complex 1-manifold X, the
> space of holomorphic 1-forms is trivial.*

[`Topology/SubsingletonFromPrimitiveExistence.lean:185`](JacobianChallenge/Topology/SubsingletonFromPrimitiveExistence.lean)
further reduces this to: **every holomorphic 1-form on simply-connected
X admits a global smooth primitive** (the holomorphic Poincaré lemma).
The `subsingleton_of_primitiveExistence` lemma is unconditional in tree
via Liouville on compact connected manifolds.

This is the **cleanest** reverse-leg route. It avoids BSLB and the
Whitney-smoothing-of-a-2-D-homotopy gap. Instead it needs only
chart-by-chart primitive gluing along 1-D paths, which uses the chart
ball partition + chart-local primitive arc (chip-D + mathlib's
`DifferentiableOn.isExactOn_ball`).

**Forward leg (`Genus0ImpliesS2 X`)** reduces to the named hypothesis
`ExistsSimplePoleGermAtSomePoint X` (= `hSP`), whose bottom is
`RR_DimGE2_GenusZero_Germ X` — Riemann-Roch at genus 0. The downstream
chain in tree (PrincDivWitnessExtraction → degree-1 mero function →
`bijectiveAnalyticIsBiholomorphism_holds` → `genus_eq_zero_iff_homeo_of_HolomorphicEquiv_RiemannSphere`)
is unconditional, so the forward leg is purely gated on RR at genus 0.

**The original BSLB framing was a red herring.** BSLB is one of several
named-hypothesis discharges of subsingleton, but not the simplest. The
primitive-existence route is structurally cleaner.

## Why the original BSLB framing was tempting (and wrong)

The previous version of this handoff said "discharge BSLB on arbitrary
X". That is **structurally impossible**: BSLB asserts every smooth
loop bounds a smooth 2-chain, which is just false on, e.g., a torus —
a loop winding around a generator does not bound. BSLB is a
simply-connected property; on compact connected complex 1-manifolds it
holds iff genus = 0, which by uniformization means X ≃ RS.

So the honest forms of "BSLB outside RS-specific code" are:

* `BasedSmoothLoopsBoundHypothesis_of_simplyConnected`
  (`[SimplyConnectedSpace X] → BSLB X p₀`). This is the actual
  classical statement.
* `BasedSmoothLoopsBoundHypothesis_of_genus_zero`
  (`genus X = 0 → BSLB X p₀`), wired through whatever
  genus → simply-connected step is in tree.

Both still need substantial classical content past what is already
discharged:

* Continuous null-homotopy of γ from `SimplyConnectedSpace X` is
  already in tree:
  `SmoothPath.continuousHomotopyOfSimplyConnected` (in
  `Manifold/SmoothPathHomotopyFromSimplyConnected.lean`).
* **The remaining gap is Whitney smoothing for manifold-valued maps**:
  given a continuous `H : I × I → X` interpolating two smooth paths,
  produce a smooth `H' : I × I → X` with the same boundary data.
  mathlib's `Continuous.exists_contMDiff_approx_and_eqOn` requires the
  codomain to be a normed vector space, not a general manifold, so it
  does not apply directly. This is the same Whitney-approximation gap
  that has blocked the cleanest cross-chart BSLB / Stokes routes for
  months.

There are two practical workarounds, neither short:

1. **Missed-point + factor-through-ℂ, generalized.** The RS discharge
   (`basedSmoothLoopsBoundHypothesis_RS_holds` via
   `loopFactorsThroughVectorSpaceHypothesis_of_missedPoint`) uses
   Sard-style "loop image has measure zero in dim-2" + the Möbius
   shift to identify RS \ {q} ≅ ℂ. The Sard step generalizes (every
   smooth loop on a 2-manifold has a missed point); the chart-shift
   step needs a global biholomorphism between `X \ {q}` and a vector
   space, which on simply-connected compact complex 1-manifolds is
   uniformization at genus 0.

2. **Polygonal subdivision + chart-local bordism + null-bordism of
   the polygonal loop.** Use the path-level chart-ball partition (the
   chip below) to replace γ by a polygonal loop crossing one
   chart-image ball per segment. The γ-to-polygon homotopy in each
   ball uses `affineChartTriangleSimplex_ball` material. The
   *remaining* gap is null-bordism of the chart-crossing polygonal
   loop — which by an inductive Van Kampen-style argument under
   `[SimplyConnectedSpace X]` reduces to null-bordism of
   single-chart-ball loops (already discharged by
   `polygonalChain_ball_smoothCycle_mem_stokesBoundaries_of_closed`),
   but the inductive step itself needs the Whitney smoothing above.

Either route is a multi-week classical-content effort, not a
single-chip closure.

## Path A progress (2026-05-23, continued)

The 2026-05-23 follow-up commit on this branch added:

* `Manifold/UniformPathChartBallDepth.lean` (~210 LOC) —
  `exists_chartBall_anchor_partition`: for every smooth path
  `γ : SmoothPath 𝓘(ℝ, ℂ) X` on an arbitrary complex 1-manifold X
  (`[ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]`), there is an
  equidistant `Fin N` partition of `[0, 1]` plus per-segment chart
  anchors `qs : Fin N → X` such that on each `[k/N, (k+1)/N]`,
  `γ.ambient s ∈ chartBallSourcePreimage (qs k)` (i.e., γ lands in
  `(chartAt ℂ (qs k)).source` and its chart-image lands in the
  canonical chart-ball at `qs k`).

  Pairs with `AffineChartTriangleSimplexBall`,
  `ChartStraightLinePathBall`, and `FanTriangulationBall` to give a
  chart-local polygonal approximation of any smooth path on X. Same
  Lebesgue-number-lemma pattern as
  `ComplexTorus.exists_chartAnchor_partition` (specific to ℂ ⧸ L) but
  for arbitrary X.

  Verified: `taskpolicy -b nice -n 19 env LEAN_NUM_THREADS=1 lake
  build JacobianChallenge.Manifold.UniformPathChartBallDepth`. Full
  manifest single-file check green.

  This is reusable infrastructure for **either** of the two BSLB
  workarounds above, plus for any other arc that wants a per-segment
  chart-ball partition of a smooth path (e.g. complex-period
  decomposition, Stokes-on-curved-loops, etc.).

## Additional 2026-05-23 chips — foundation of the maximal-atlas cascade

* `Manifold/ConvexBallChartAtMaximalAtlas.lean` (~200 LOC) —
  `convexBallChartAt (x : X) := (chartAt ℂ x).restr (chartBallSourcePreimage x)`.
  Headline lemmas: `convexBallChartAt_target_eq` (target = ball),
  `convexBallChartAt_target_convex`,
  `convexBallChartAt_mem_maximalAtlas` (in `(𝓘(ℂ, ℂ)) ω` maxAtlas via
  `restr_mem_maximalAtlas`), and `convexBallChartAt_mem_maximalAtlas_real`
  (the ℝ-`⊤` model variant — what the chartLocalPrimitive cascade
  actually consumes).

  Packages, for every `x` on arbitrary X, a chart in BOTH maximal
  atlases with convex (ball) target. The canonical `chartAt ℂ x` does
  not in general have convex target, so the existing
  `HasConvexChartAtTarget X` typeclass cannot be instantiated on
  arbitrary X. This chip is the structural answer.

* `Manifold/SmoothPathLinearInChartMax.lean` (~140 LOC) —
  `SmoothPath.linearInChartSegmentMax`: parallel to the existing
  `SmoothPath.linearInChartSegment`, parameterised by `h_max : φ ∈
  IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X` instead of `h_atlas : φ ∈
  atlas ℂ X`. Body identical minus the `subset_maximalAtlas` call
  (uses `h_max` directly). Bridge lemma
  `linearInChartSegmentMax_eq_linearInChartSegment` shows the two
  produce the **same SmoothPath** when both apply — proven by `rfl`
  via Prop irrelevance on the `smooth` field.

  This is the foundation of the cascade. The atlas-membership
  parameter is consumed exactly once across the entire cascade (in
  `linearInChartSegment`'s smoothness proof, via
  `subset_maximalAtlas`); removing it here unblocks every downstream
  function from atlas-only-membership.

  Verified: full project `taskpolicy lake build` of both targets
  succeeds (2648 jobs).

## What to do next session — continue the maxAtlas cascade

The structural foundation is in place (`convexBallChartAt` +
`linearInChartSegmentMax`). To close the reverse leg on arbitrary X,
build the parallel maxAtlas variants up the cascade. The work is
mechanical and chip-sized for one session each:

**Cascade order** (file → defs/lemmas that need a `Max` parallel
variant taking `h_max` instead of `h_atlas`):

1. `Manifold/ChartLocalPrimitive.lean` (6 decls, ~230 LOC) →
   `ChartLocalPrimitiveMax.lean`. The def `chartLocalPrimitive` plus
   `chartLocalPrimitive_self` (basepoint identity). Each lemma is a
   direct parallel; same body modulo `h_atlas → h_max`.

2. `Manifold/ChartLocalPrimitiveExtend.lean` → `ChartLocalPrimitiveExtendMax.lean`.
   The `chartLocalPrimitiveExtend` def (extension to total function)
   plus its source-restriction and `EventuallyEq` lemmas.

3. `Manifold/PathPrimitiveLocalSmoothFTCNamed.lean` →
   `PathPrimitiveLocalSmoothFTCNamedMax.lean`. The named hypotheses
   `ChartLocalPrimitiveSmoothExt`, `ChartLocalPrimitiveFTC` and the
   two `pathPrimitive_*_of_*` bridge lemmas.

4. `Manifold/ChartLocalPrimitiveSmoothExtChartAt.lean` /
   `Manifold/ChartLocalPrimitiveFTCChartAt.lean` →
   per-chart discharges of the named hypotheses. Trickier — these are
   the actual classical content (parameter-integral smoothness +
   chain-rule FTC). They currently discharge for `chartAt ℂ x` only.
   For the maxAtlas variant, they need to discharge for ANY chart in
   maxAtlas — but the proof is generic (only uses chart smoothness),
   so it carries.

5. `Manifold/PathPrimitiveGlobalSmoothFTC.lean` →
   `PathPrimitiveGlobalSmoothFTCMax.lean`. The
   `PathPrimitiveAdmissibleChartCover` predicate (taking maxAtlas
   charts) and the two `pathPrimitive_*_of_admissible` global theorems.

6. `Manifold/HasAdmissibleChartCoverClass.lean` /
   `Manifold/HasAdmissibleChartCoverFromConvexChartAtTarget.lean` →
   the maxAtlas typeclass + UNCONDITIONAL instance on arbitrary X
   via `convexBallChartAt` (no `HasConvexChartAtTarget X` needed).

**Final composition** (single chip after the cascade lands):

7. `holomorphicOneFormSubsingletonOfSimplyConnected_of_universalAdmissibilityMax`
   — composes the new admissibility chain with
   `subsingleton_of_BSLB_and_pathPrimitive` (or
   `subsingleton_of_primitiveExistence`).
   Composing with `s2ImpliesGenus0_from_subsingletonOfSimplyConnected`
   gives `S2ImpliesGenus0 X` on arbitrary X — the reverse leg of
   item 14, UNCONDITIONALLY closed.

   Caveat: `subsingleton_of_BSLB_and_pathPrimitive` still requires
   BSLB. To bypass BSLB entirely, the cleanest route is
   `subsingleton_of_primitiveExistence` (in tree, unconditional in
   the sense that it consumes only "primitive exists"). For that, the
   maxAtlas chain delivers BOTH smoothness AND FTC of `pathPrimitive`
   given `LoopPeriodVanishes`, and the question becomes how to
   discharge `LoopPeriodVanishes` on simply-connected X. The
   chart-by-chart monodromy argument noted in the previous handoff
   version still applies and is independent of the maxAtlas
   cascade — that's the genuine remaining classical content beyond
   the cascade.

**For the forward leg**: classical Riemann-Roch at genus 0
(`RR_DimGE2_GenusZero_Germ X`). Multi-chip, but no Whitney smoothing
gap. The surrounding infrastructure (divisor degree, linear systems,
MeromorphicNonzero lift) is already in tree.

Per the chip-prompt-preamble anti-paraphrase gates, the cascade above
is borderline: each `Max` chip parallels an existing function. The
test for "not paraphrase" is that the cascade collectively reduces a
named hypothesis on arbitrary X (admissibility — and once landed,
discharges `S2ImpliesGenus0` on arbitrary X via the existing
subsingleton-of-pathPrimitive chain).

## Discipline

Do not write more "from N inputs" chips. Do not write more per-X
instance chips. Do not write more parallel route chips. Each of these
adds LOC without removing the `sorry`. See
[`tools/chip-prompt-preamble.md`](tools/chip-prompt-preamble.md) for the
hard gates.

## Worktree commands

```bash
git worktree list      # confirm worktree still pinned
cd "/Volumes/4TB SD/ClaudeCode/jacobian-lean-challenge-item14"
```

The original checkout at `/Volumes/4TB SD/ClaudeCode/jacobian-lean-challenge`
is used by a parallel session on a different branch. Don't `cd` into it.
