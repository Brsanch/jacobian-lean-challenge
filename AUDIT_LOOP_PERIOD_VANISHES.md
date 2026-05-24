# Audit — `LoopPeriodVanishes` on simply-connected X

Date: 2026-05-24.

## Context

The chartLocalPrimitive maxAtlas cascade (this session, 13 chips on
`feat/item14-affineChartTriangleSimplex-ball`) reduces Item 14's
reverse leg to **one named hypothesis** on arbitrary compact connected
complex 1-manifold X:

```
SimplyConnectedSpace X → BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀
```

(per `s2ImpliesGenus0_of_basedSmoothLoopsBoundHypothesis_unconditional`
in `Topology/S2ImpliesGenus0FromBSLBUnconditional.lean`).

The previous handoff identified this as "smooth Hurewicz" — the gap
between mathlib's continuous null-homotopy (from `SimplyConnectedSpace`)
and a smooth 2-chain bound on a loop. That framing is correct for the
BSLB route, but it is **not the only route**.

This audit identifies why the gap is structural-to-the-current-Lean-
architecture, not mathematical, and lists concrete alternatives.

## Classical mathematics: there is no Hurewicz gap

The standard classical theorem
"holomorphic 1-form on simply-connected Riemann surface is exact"
(Forster §10, §16) is proved via **monodromy of analytic continuation**.
It does **not** invoke smooth Hurewicz / Whitney smoothing.

Outline:
1. ω is closed (holomorphic 1-form on complex 1-manifold ⇒ closed).
2. Locally exact (Poincaré lemma on chart balls).
3. Chart-local primitives F_y exist on each `(convexBallChartAt y).source`.
4. Two F_y, F_{y'} on overlap differ by a (locally) constant by FTC
   (mfderiv F_y = mfderiv F_{y'} = om.eval on overlap).
5. Chart-transition constants form a Čech 1-cocycle on the cover
   `{convexBallChartAt y | y : X}`.
6. On simply-connected X, every locally-constant ℂ-cocycle is a
   coboundary (H¹(simply-connected, ℂ) = 0; equivalently, monodromy is
   trivial).
7. Coboundary gives constants c_y such that F_y − c_y agree on
   overlaps, hence glue to a global primitive.

Step 6 is the only topological-deep step. It uses simply-connectedness
in a **purely topological** way — no smooth structure of the homotopy
is required.

The cascade fully discharges steps 1–4 unconditionally on arbitrary X.
The gap is step 6.

## Lean status

### Mathlib

- `Mathlib.Topology.Homotopy.Lifting.monodromy_theorem` — the abstract
  monodromy theorem applied to local homeomorphisms. Suitable for
  étale-space-based analytic continuation. **Exists but unused for our
  problem.**
- `Mathlib.Topology.Homotopy.Lifting.existsUnique_continuousMap_lifts`
  — path-independent lifts through a local homeomorphism on a
  path-connected, locally path-connected space.
- `Mathlib.Analysis.Complex.HasPrimitives.DifferentiableOn.isExactOn_ball`
  — primitive exists on a disk in ℂ. **Subdomain of ℂ only**, not
  simply-connected open subset.
- **No** mathlib lemma "holomorphic on simply-connected open in ℂ
  has primitive" yet (despite the file's stated long-term goal). The
  whole-ℂ case (`isExactOn_univ`) is the closest available.
- **No** mathlib lemma "closed 1-form on simply-connected manifold is
  exact".

### In-tree

- `Manifold/PointwiseChartEvalUnconditional.lean`:
  `chartContainedLoopVanishingHypothesis_holds_unconditional`
  — chart-contained loops have zero period, **unconditional**.
- `Manifold/SmoothLoopHasMissedPointDischarge.lean`:
  `smoothLoopHasMissedPointHypothesis_holds`
  — Sard-via-Hausdorff-dim argument that every smooth loop on
  `RiemannSphere` misses a point. **Proof uses `chartN` specifically
  but the Sard argument generalises to any 2-manifold.**
- `Manifold/LoopFactorsThroughVectorSpaceFromMissedPoint.lean`:
  `loopFactorsThroughVectorSpaceHypothesis_of_missedPoint`
  — converts missed-point to "loop factors through ℂ", **RS-specific**
  (uses the global biholomorphism `RS \ {q} ≅ ℂ` via Möbius).
- `Manifold/FanTriangulationBall.lean`:
  `polygonalChain_ball_smoothCycle_mem_stokesBoundaries_of_closed`
  — chart-contained polygonal loops bound smooth 2-chains, **unconditional**
  on arbitrary X.

## Why the Hurewicz blocker exists in the current architecture

The current architecture routes:

```
S2ImpliesGenus0 X
  ⟸ LoopPeriodVanishes om x₀
    ⟸ BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀   (= BSLB)
      ⟸ LoopFactorsThroughVectorSpaceHypothesis ℂ X x₀
        ⟸ X \ {q} biholomorphic to ℂ (uniformization at genus 0,
          known only on RiemannSphere)
```

The BSLB step asks for a **smooth 2-chain** bounding each loop. This is
strictly stronger than what mathlib's `SimplyConnectedSpace` (continuous
null-homotopy) provides — hence the Whitney smoothing gap.

The classical monodromy proof bypasses this entire chain. The Lean
implementation chose the BSLB route because:
- `stokesBoundaries` / `Smooth2Chain` machinery was developed first.
- `SubsingletonFromBSLBAndPathPrimitive.lean` predates the cascade.
- The path-primitive smoothness/FTC ingredients had been deferred as
  per-basis inputs (only now discharged unconditionally by the cascade).

## Concrete alternative routes (Lean-implementable)

### Alt A: Polygonal-loop bridge + Van Kampen induction

The in-tree `polygonalChain_ball_smoothCycle_mem_stokesBoundaries_of_closed`
already discharges BSLB for **single-chart-ball polygonal loops** on
arbitrary X. The full BSLB requires extending to multi-ball loops.

For a polygonal loop ℓ crossing balls B₁, …, Bₙ on simply-connected X:

1. **Polygonal approximation**: replace a general smooth loop γ by a
   polygonal loop ℓ with chart-line edges. Each edge lies in a single
   chart ball. The chord-replacement integrals match by chart-local
   FTC (cascade). [Modest Lean work, ~150 LOC.]
2. **Van Kampen reduction**: a polygonal loop on simply-connected X
   crossing two balls B, B' (with non-empty overlap) decomposes as
   ℓ = ℓ_B ⋆ ℓ_{B'} where each piece is in a single ball, via a
   "pivot vertex" in B ∩ B'. Inductive on the number of balls.
   [Substantial Lean work, ~400 LOC.]
3. **Base case**: single-ball polygonal loop bounds via
   `polygonalChain_ball_smoothCycle_mem_stokesBoundaries_of_closed`.
   [Already in tree.]

**Estimated total**: 500-700 LOC across 3-4 chips. Avoids both Whitney
smoothing and uniformization.

### Alt B: Monodromy of analytic continuation via étale space

Build the étale space `E := {(x, germ_x F) : x : X, F ∈ chart-local
primitive of ω near x}`, with projection `p : E → X`. Show:

1. `p` is a local homeomorphism (chart-local primitives are unique up
   to constant on connected chart sources).
2. Apply `Mathlib.Topology.Homotopy.Lifting.existsUnique_continuousMap_lifts`
   with `f := id : X → X`, `e₀ := (x₀, F_{x₀})`, the ex/uniq inputs
   from `monodromy_theorem` applied to E.
3. Result: a continuous section X → E, projecting to a global primitive
   F : X → ℂ.

Smoothness of F follows from the local sections being smooth (FTC
chips give mfderiv = om.eval everywhere).

**Estimated**: 600-900 LOC across 4-6 chips. Higher conceptual
complexity (étale space, sheaf-of-primitives torsor structure) but
uses mathlib's monodromy theorem off-the-shelf.

### Alt C: Direct path-homotopy invariance

Skip the global primitive entirely. Show directly that
`LoopPeriodVanishes`:

1. For γ : SmoothPath at x₀ a loop, take a continuous null-homotopy
   H : I × I → X via `SmoothPath.continuousHomotopyOfSimplyConnected`
   (in tree).
2. Subdivide H so each cell maps into a single chart ball
   (`subdivide_continuous_through_charts`, in tree).
3. For each cell (s, t) ∈ [0,1]², the H-image of the cell's boundary
   is a CONTINUOUS loop in a chart ball. By the cascade's chart-local
   primitive (smoothness + FTC), this continuous loop integrates to
   zero against ω: ∫_∂cell ω = F_y(H(s_max, t_max)) − F_y(H(s_max, t_min))
   − (similar) = 0 by FTC + chart-local primitive value at corners.
4. Telescope cells over the unit square: internal edges cancel
   (each internal edge appears in two adjacent cells with opposite
   orientation). Boundary edges form γ (on s=0) and constant (on s=1).
5. Conclude ∫_γ ω = 0.

The chart-pullback Cauchy on continuous loops (step 3) requires
extending the cascade's FTC from smooth-loop boundary integrals to
continuous-loop boundary integrals via the chart-local primitive's
continuity (the primitive itself is smooth, but evaluating it at the
endpoints of a continuous arc still gives a definite value).

**Estimated**: 400-600 LOC across 3-5 chips. Most direct; requires
extending FTC application from smooth to continuous loops within a
chart (the chart-pullback of ω is holomorphic on the chart ball, so
Cauchy's theorem applies to any continuous loop within the ball).

### Alt D: Sard generalisation + chart-by-chart loop completion

The RS-specific Sard discharge generalises: every smooth loop on a
2-manifold has image of Hausdorff dim ≤ 1, hence misses a point of
*any chart* it intersects. After missing such a point in a chart, the
loop can be locally retracted away from that chart, then fan-triangulated.

This route shares structural ideas with Alt A but uses Sard rather
than Van Kampen at the inductive step.

**Estimated**: 300-500 LOC. Sard generalisation is the main new piece;
the rest reuses in-tree fan-triangulation.

## Recommendation

**Alt C is the most direct and reuses the most cascade infrastructure.**
The cascade's chart-local primitives + FTC give exactly the data
needed for the cell-by-cell argument. The only new ingredient is
extending chart-pullback Cauchy from smooth to continuous loops
within a chart — a small lemma about
`Complex.IsExactOn_ball ⇒ loop integral zero` for any continuous loop
in the ball.

Alt A (polygonal + Van Kampen) is also viable but the Van Kampen
induction is significantly more Lean-intensive.

Alt B (étale space + monodromy) is mathematically the cleanest but
the étale-space setup is the most foreign to the current tree.

## What this session's cascade actually accomplished

Re-stating clearly: the cascade did **not** close Item 14 reverse leg
on arbitrary X. It cleared the entire **analytic prerequisite chain**
so that whichever of Alt A/B/C ships first will close the leg
immediately. Specifically:

* Before this session: the analytic side of the reverse leg was tangled
  with the topological/Hurewicz side via the convex-target-of-chartAt
  restriction. The chartAt-only chip-A/B/D arc could not even discharge
  primitive smoothness/FTC on arbitrary X.
* After this session: primitive smoothness + FTC are unconditional on
  arbitrary X given `LoopPeriodVanishes`. The only remaining content
  is the single classical topological reduction (Alt A/B/C/D).

The "Hurewicz gap" was a property of the BSLB route, which the cascade
made avoidable by exposing the chart-local primitives as a usable
intermediate step. Future work along Alt A/B/C/D should NOT route
through BSLB.
