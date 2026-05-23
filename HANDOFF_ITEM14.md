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

## What to do next session (anti-paraphrase)

**Pick ONE of the two open named hypotheses and commit to its discharge.**

Each is single-arc multi-session. Neither requires mathlib-class
theorems that mathlib lacks; each requires real but bounded Lean work:

- **Path A (BSLB on arbitrary X via `Smooth2Simplex` refactor).**
  Refactor `Smooth2Simplex` from `ContMDiff` to `ContMDiffOn [0,1]²`
  (cascades through `boundary`, `boundary₂`, `boundary₂Cycle`,
  integration machinery). Once done, the chain-assembly +
  fan-triangulation + chart-local straight-line bordism (all in tree)
  glue across chart boundaries, giving BSLB on arbitrary
  simply-connected X. Estimated 1-3k LOC of refactor; no new classical
  content needed.

- **Path B (hSP / RR-g0 dim bound).** Discharge `RR_DimGE2_GenusZero_Germ X`
  classically — Serre duality at genus 0 + canonical divisor degree.
  Estimated 1.5-4k LOC of classical content. The surrounding
  infrastructure (divisor degree, linear systems, MeromorphicNonzero
  lift) is in tree.

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
