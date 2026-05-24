# Item 14 — handoff

Last refreshed: 2026-05-23 (post deep-audit corrections).

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

## What to do next session

**Assemble BSLB on arbitrary X** by chaining the chart-local ball
machinery into a full discharge of
`BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀`. Outline:

1. Take a smooth loop γ : SmoothPath 𝓘(ℝ, ℂ) X at x₀.
2. Use `UniformChartContainmentDepth_named X` (unconditional in tree)
   to subdivide [0,1] into segments each mapped by γ into a single
   chart-image ball.
3. Per-segment chart-local polygonal approximation: replace γ on each
   segment by a chart-straight-line path between its endpoints (same
   chart, in the ball — uses `chartStraightLinePath_ball`).
4. Per-segment bordism between γ-piece and chart-straight-line-piece:
   needs a small homotopy 2-chain. The triangle simplex from
   `affineChartTriangleSimplex_ball` is the natural piece. Polygonal
   and straight-line pieces are the boundary; γ-piece is the third
   edge (or a thin 2-chain interpolation).
5. Glue: assembled 2-chain whose boundary is γ minus the closed
   polygonal loop. By `polygonalChain_ball_smoothCycle_mem_stokesBoundaries_of_closed`
   the polygonal loop is in stokesBoundaries; therefore γ is too.

Steps 3-4 are the substantive remaining classical content. Step 2 has
the existing in-tree compactness machinery. Step 5 is mostly
list/sum bookkeeping.

The other open named hypothesis remains:

- **Path B (hSP / RR-g0 dim bound).** Discharge `RR_DimGE2_GenusZero_Germ X`
  classically — Serre duality at genus 0 + canonical divisor degree.
  The surrounding infrastructure (divisor degree, linear systems,
  MeromorphicNonzero lift) is in tree.

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
