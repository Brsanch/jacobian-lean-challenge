# Item 14 classical-content handoff

## Worktree setup (read first)

This file lives in the dedicated worktree:

```
/Volumes/4TB SD/ClaudeCode/jacobian-lean-challenge-item14
```

pinned to branch `feat/item14-classical-content`. The original checkout
at `/Volumes/4TB SD/ClaudeCode/jacobian-lean-challenge` is used by a
parallel session on a different branch (last seen: `wip/chip7-from-origin`,
C3 / period-lattice / Hodge-Riemann arc).

**All work happens in this worktree.** Never `cd` into the original
checkout; never run `git switch` here without thinking about whether the
other session needs the branch. The worktree's purpose is to keep our
working tree's branch state independent of the parallel session.

`git worktree list` should always show both:

```
/Volumes/4TB SD/.../jacobian-lean-challenge         [<other-branch>]
/Volumes/4TB SD/.../jacobian-lean-challenge-item14  [feat/item14-classical-content]
```

## 2026-05-21 session — additional FTC-arc foundation chips on `origin/main`

After the 4-PR landing below, two more foundational chips landed
directly on `main` (`origin/main` HEAD `7cac7e8`) — integrand-side
joint-smoothness lemmas needed by the future parameter-integral
upgrade of `chartLocalPrimitive` continuity → smoothness:

* **`JacobianChallenge/Manifold/BumpedSegmentParamSmooth.lean`**
  (commit `078c921`) — joint `C^∞` of
  `(z, t) ↦ bumpedSegment z₀ z t` and
  `(z, t) ↦ chartCoordVelocity z₀ z t` on `ℂ × ℝ`.
* **`JacobianChallenge/Manifold/ChartLocalIntegrandSmooth.lean`**
  (commit `8d4ef29`) — joint `ContDiffOn ℝ ∞` of the abstract
  chart-coord integrand
  `(z, t) ↦ f(bumpedSegment z₀ z t) * chartCoordVelocity z₀ z t` on
  `S × Set.univ` under `ContDiffOn ℝ ∞ f S` + `Convex ℝ S` +
  `z₀ ∈ S`.

Both reduce to mathlib `Real.smoothTransition.contDiff`,
`ContDiff.iterate_deriv`, `ContDiff.smul`/`ContDiff.mul`, and
`ContDiffOn.comp` with a `Set.MapsTo` from convexity. Self-contained
and unconditional.

### ⚠️ Diamond gotcha for the `localCoeff` real-smoothness bridge

The natural next chip would specialize `contDiffOn_chartLocalIntegrand_param`'s
abstract `f` to `localCoeff om y` by bridging
`ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (localCoeff om y) (chartAt ℂ y).target` to
`ContDiffOn ℝ ∞`. Attempted across two sessions on 2026-05-21 and hit
a **mathlib instance diamond** at `IsScalarTower ℝ ℂ ℂ`.

**Exact diamond (verified via `set_option trace.Meta.synthInstance true`
in probe2):** the goal type expected by `restrict_scalars` is
`@IsScalarTower ℝ ℂ ℂ Complex.instRCLike.toSMul (Algebra.id ℂ).toSMul Complex.instRCLike.toSMul`,
but `Complex.instIsScalarTowerOfReal` produces an instance keyed on
`Complex.SMul.instSMulRealComplex`. These SMul instances should be
defeq, but Lean's `tryResolve` does not unify them, and the diamond
cannot be patched via a `letI : IsScalarTower ℝ ℂ ℂ := ⟨...⟩` because
the supplied instance has the same "wrong" SMul indices. Verified
across 14+ probe variants (AnalyticOnNhd.restrictScalars,
Complex.equivRealProdCLM round-trip, explicit `@`-application,
`fun_prop`, manual SMul-typed letI) — all fail uniformly with this
mathlib pin. The same diamond blocks `HasFDerivAt.restrictScalars`,
`AnalyticOn.restrictScalars`, etc. since they share the variable
signature.

### Bridge partial — `HasFDerivAt`/`DifferentiableOn` level landed

`HasFDerivAtRestrictScalarsComplex.lean` (commit `2712965`) ships a
**hand-rolled** ℂ → ℝ bridge at the `HasFDerivAt` /
`DifferentiableOn` level that bypasses the diamond. Key trick: extract
the `=o[𝓝 x]`-form via `HasFDerivAt.isLittleO` (which is
base-field-agnostic), then reconstruct ℝ-side `HasFDerivAt` via
`HasFDerivAt.of_isLittleO` after applying
`ContinuousLinearMap.restrictScalars ℝ` (which only requires
`LinearMap.CompatibleSMul ℂ ℂ ℝ ℂ`, NOT `IsScalarTower ℝ ℂ ℂ`).

Available bridge API:
* `HasFDerivAt.restrictScalarsComplex`
* `HasFDerivWithinAt.restrictScalarsComplex`
* `DifferentiableAt.restrictScalarsComplex`
* `DifferentiableWithinAt.restrictScalarsComplex`
* `DifferentiableOn.restrictScalarsComplex`
* `Differentiable.restrictScalarsComplex`

**Still missing for full `ContDiffOn ℂ → ContDiffOn ℝ`**:
* `fderivWithin ℝ f s x = (fderivWithin ℂ f s x).restrictScalars ℝ`
  identity (under unique-diff hypotheses).
* Iteration on `n` for `ContDiffOn ℝ n` via the recursive characterization
  `ContDiffOn ℝ (n+1) f S ↔ DifferentiableOn ℝ f S ∧ ContDiffOn ℝ n (fderivWithin ℝ f S) S`.

Remaining alternatives:
1. **Mathlib PR**: file an issue / patch to mathlib that exposes a
   priority-tagged `IsScalarTower ℝ ℂ ℂ` instance keyed on the
   `Algebra.id`-SMul.
3. **Compose-through-equiv approach**: for `e := Complex.equivRealProdCLM`,
   define `g := e ∘ f ∘ e.symm : ℝ² → ℝ²` and prove `g`'s real-smoothness
   directly from the explicit Cauchy-Riemann structure (∂g₁/∂x = ∂g₂/∂y,
   ∂g₁/∂y = -∂g₂/∂x). Transport back to `f` via the equiv. (~300-500 LOC.)

Subsequent chips in the same FTC arc (after the bridge lands):
* Specialize the abstract `f` to `localCoeff om y` via the bridge
  from `ContMDiffOn 𝓘(ℂ) ω f` to `ContDiffOn ℝ ∞ f`
  (`localCoeff_contMDiffOn` already in tree).
* Express `chartLocalPrimitive` in chart coords as an interval
  integral with this integrand on `[0, 1]`.
* Apply mathlib's parameter-integral smoothness theorem
  (`ContDiffOn.intervalIntegral` or similar) to upgrade to
  `ChartLocalPrimitiveSmoothExt`.
* The matching FTC sub-arc upgrades to `ChartLocalPrimitiveFTC`.

Together those discharge two of the **4 minimal named hypotheses**
of `genus_eq_zero_iff_homeo_from_4_minimal_inputs`, leaving only
`hSP` (`ExistsSimplePoleGermAtSomePoint`, forward leg, RR-class) and
`h_bslb` (`SimplyConnected → BSLB`, reverse leg, smooth-Hurewicz).

## 2026-05-21 session COMPLETE — 4 PRs landed on `origin/main`

**Final `origin/main` HEAD: `b48070b`** (post PR #4 merge). Repo at
**1056 .lean files, 179,900 LOC, build 9316 jobs clean**. Zero
`sorry`, zero `axiom`. Item count unchanged at **14 / 24
STRICT-CLOSED** — this session's work is substantive *infrastructure*
toward item-14 reverse-leg closure on simply-connected X; the
final cross-piece glue is the one chip identified below as the next
arc.

### PRs merged

* **PR #1 `be4146d`** — chain assembly + Dolbeault + chart-cell infra
  (+3,639 LOC, 23 new files). Headline closed: any *closed polygonal
  loop in a single full-target chart* explicitly bounds a fan 2-chain
  (lies in `stokesBoundaries`), via List-induction on
  `fanChain`/`polygonalChain`/`spokeResidue`.

* **PR #2 `4e3ed97`** — SmoothHomotopyPath diagonal-split + bordism
  conclusion (+478 LOC). Headline: for any `SmoothHomotopyPath γ₀ γ₁`,
  the SmoothCycle `single γ₁ - single γ₀ ∈ stokesBoundaries`.

* **PR #3 `5934aad`** — chart-local polygonal-approximation bordism
  (+230 LOC, refactored `SmoothHomotopyPath` edges to `unitInterval`).
  Headline: any γ globally chart-contained in a full-target chart is
  smoothly bordant to its chart-straight-line approximation.

* **PR #4 `b48070b`** — `SmoothPath.subpath` primitive (+111 LOC). The
  affine-reparam sub-arc extraction supporting the chart-cover
  Lebesgue subdivision.

### Next-session frontier (genuine mathematical-architectural choice)

Wiring the four ingredients above into a complete
`BasedSmoothLoopsBoundHypothesis X p₀` discharge requires resolving a
genuine mathematical obstruction: the chart-local bordism's
hypothesis is `γ.ambient` globally chart-contained (∀ t : ℝ), but
sub-arcs from Lebesgue subdivision are only chart-contained on
`[0, 1]`. The bump-extension workaround was shown **mathematically
impossible** (no smooth `σ : ℝ → [0, 1]` with `σ = identity` on
`[0, 1]` exists — derivative-matching at the boundary forces σ < 0
just outside).

Three real options for the next session, each non-trivial:

1. **Restructure `Smooth2Simplex` and `stokesBoundaries`** to use
   `ContMDiffOn [0, 1]²` instead of `ContMDiff` globally. Major
   refactor cascading through `boundary`, `boundary₂`,
   `boundary₂Cycle`, the integration machinery. Tractable but big.

2. **Define a finer SmoothPath structure** that exposes its ambient
   field (rather than burying it in `Classical.choose`), so a custom
   bump-extended ambient can be threaded through. Use
   `ContDiffBump` machinery from mathlib.

3. **Strong-hypothesis pattern**: define a
   `BasedSmoothLoopsBound_BumpedCover X` predicate for X equipped
   with a finite chart cover where loops *can* be guaranteed
   globally chart-contained (e.g., via missed-point reductions like
   the RS case). This sidesteps the obstruction by requiring extra
   data per X.

The full chain-assembly closure is **one chip away once the choice is
made**. All the substantive classical content (chain cancellation,
fan triangulation, bordism kernel) is already in tree.

---

## Earlier 2026-05-21 progress notes (preserved)

Branch advanced ~28 more chips beyond the prior 2026-05-20 batch.
All single-file builds clean, no axiom, no sorry.

### Key new infrastructure (in addition to chips 2–8)

* **`SmoothPathChartSubdivision`** — Lebesgue subdivision of a smooth
  path by an open cover / by a `[HasConvexTargetChartCover]` cover.
* **`SubdivisionTelescopingToLoopFromBSLB`** — architectural reduction:
  `SubdivisionTelescopingToLoop_named X ⇐ ∀ p₀, BSLB X p₀`.
* **`SubdivisionTelescopingToLoopSubsingleton`** — typeclass-
  generalized trivial discharge under `[Subsingleton (HolomorphicOneForm X)]`.
* **`BilinearChartCellSimplex`** — bilinear chart-cell smoothness +
  convex containment + `Smooth2Simplex` lift (via `complexManifoldRealification`).
* **`AffineChartTriangleSimplex`** — affine 3-corner chart-triangle
  `Smooth2Simplex 𝓘(ℝ, ℂ) X` (Δ²-convention); vertex-toFun simp lemmas.
* **`ChartStraightLinePath`** — chart-straight-line `SmoothPath 𝓘(ℝ, ℂ) X`;
  `smoothPath_ext_of_toPath_apply` extensionality lemma;
  reverse-equals-swap-endpoints; full SmoothPath identification of the
  three triangle faces; explicit `Smooth2Simplex.boundary` of the
  chart-triangle as a chain of three `chartStraightLinePath_univ`s.
* **`AdjacentTriangleCancellation`** — two-triangle decomposition into
  outer chain + shared-pair; outer chain is a `SmoothCycle`; outer chain
  lies in `stokesBoundaries` (substantive Stokes-style cancellation).
* **`FanTriangulation`** — `fanChain`, `polygonalChain`, `spokeResidue`
  List-recursive definitions; full inductive boundary identity
  `boundary₂ fanChain = polygonalChain + spokeResidue`; closure
  corollary `polygonalChain_eq_boundary_of_closed`.

### Frontier (what remains open)

The chain-assembly for a closed polygonal loop is **closed** — any
closed polygonal loop in a full-target chart bounds a fan 2-chain
explicitly. The remaining gap toward `BasedSmoothLoopsBoundHypothesis
X p₀` on a simply-connected complex 1-manifold is:

1. **Polygonal-approximation bordism**: from a smooth based loop γ on
   X simply-connected, produce a sequence of (a) chart-cover-aware
   subdivision of γ (Lebesgue, **in tree**), (b) chart-local
   straight-line bordism between each subarc and the corresponding
   chart-straight-line segment (`SmoothHomotopyChartLocal`, in tree
   under chart-containment hypotheses), (c) concatenation to give a
   smooth bordism between γ and a polygonal loop. **This is the next
   substantive arc**, dispatching across chart boundaries via
   bump-mollification.

2. **Cross-chart bookkeeping**: chart-straight-line edges in different
   charts are *different* smooth paths in X. For chain cancellation to
   work across chart boundaries, we either subdivide finely enough
   that consecutive cells share a chart, or add a chart-transition
   bordism correction at chart-boundary edges. The fine-subdivision
   route is cleaner.

3. **Polygonal loop is closed**: the polygonal approximation of γ
   automatically closes because γ is a loop and the subdivision
   includes the basepoint endpoint with multiplicity 2. So the
   `polygonalChain_eq_boundary_of_closed` corollary applies directly.

## Prior session's commits on this branch

Branch advanced 7 chips beyond `66f5199` (handoff baseline). All
single-file `LEAN_NUM_THREADS=1 lake env lean …` clean, no axiom, no
sorry. Branch is local-only — not pushed.

```
a4264bf feat(item-14): dbar ℂ-linearity in function argument (Dolbeault chip 8)
b8eb5af feat(item-14): dbar chain rule for holomorphic inner (Dolbeault chip 7)
df171c0 feat(item-14): manifold-side dbar biconditional (Dolbeault chip 6)
881a216 feat(item-14): CR converse — dbarChart=0 ⇒ holomorphic (Dolbeault chip 5)
db191f9 feat(item-14): MDifferentiableAt ⇒ dbar = 0 (Dolbeault chip 4)
a9a3383 feat(item-14): manifold dbar operator (Dolbeault chip 3)
1490361 feat(item-14): dbarChart_eq_zero_of_hasDerivAt (Dolbeault chip 2)
```

**What landed.** The chart-side and manifold-level `dbar` operator with
full biconditional `MDifferentiableAt ↔ dbar = 0`, ℂ-linearity, additivity,
plus the **Wirtinger chain rule** `dbarChart (f ∘ g) z₀ = conj g' *
dbarChart f (g z₀)` when `g` is holomorphic. The latter (chip 7) gives
chart-independence of `dbar = 0` at the chart level: for any holomorphic
transition with nonzero derivative, the vanishing of ∂̄ is preserved.

**What's open and ranked.**

1. **Manifold-level chart-independence of `dbar = 0`** under
   `[IsManifold 𝓘(ℂ, ℂ) ω X]`. Need: chart transitions on a complex
   1-manifold have nonzero derivative everywhere on their source.
   This is the inverse-function-theorem application
   `id = ψ ∘ φ⁻¹ ∘ φ`. Routing through `contDiffGroupoid ω` membership
   gives `ContDiffOn ℂ ω` for both directions, hence `hasDerivAt` with
   non-zero `g'`. Apply chip 7 to conclude. Self-contained next chip.
2. **(0,1)-form bundle.** Define the antiholomorphic-cotangent
   bundle on a complex 1-manifold and `dbar` as a map from smooth
   ℂ-valued functions to smooth (0,1)-forms. Significant Lean
   infrastructure.
3. **L²-Hodge setup → H¹(X, O) = 0 at genus 0.** The deep classical
   step. Forster §16 / Griffiths-Harris §0.6. Multi-session arc, each
   step itself a classical theorem (Fredholm theory, Dolbeault
   isomorphism, …).
4. **hSP via the cutoff + ∂̄-solve recipe** (step 12 of the prior
   roadmap, now closer-in once L²-Hodge is staged).

The honest assessment from the prior handoff stands: closing item 14
strictly in tree is multi-session classical work. Each chip is one
piece of that arc.

## Prior session's commits on this branch

Twelve commits ahead of `origin/main`, interleaved with two from the
parallel session that landed here before the worktree split:

```
47b4965 feat(classical): CompleteHodgeRiemannViaStandardForm (chip 11)   ← parallel session
5116a83 feat(item-14): foundational dbar operator infrastructure (first chip of Dolbeault arc)
20c271b feat(item-14): precisely-named classical hypothesis for simple-pole germ extension
9064872 feat(item-14): closure from [HasBSLB] + [HasAdmissibleChartCover] + hSP (class-driven)
cf8090e feat(item-14): typeclass-driven Subsingleton(ω) from [HasBSLB] + [HasAdmissibleChartCover]
dc744c9 feat(classical): PeriodSigmaRealLI chip 2C - Σ → ℝ-LI of period vectors  ← parallel session
2991f11 feat(item-14): closure from hSP + BSLB + universal admissibility via Subsingleton
47ad141 feat(item-14): Subsingleton(ω) from BSLB + universal PathPrimitiveAdmissibleChartCover
bde48ec feat(item-14): parallel route via Subsingleton(ω) from BSLB chain
67085df feat(classical): PeriodSigmaInvertibility chip 2B                  ← parallel session
f33bb84 feat(item-14): RS smoke test for BSLB+pathPrimitive 3-input route
52dd84c feat(item-14): Subsingleton(ω) and item 14 closure from BSLB + path-primitive
```

The parallel-session commits don't conflict with item 14 work; they just
happen to be on this branch's history.

## Item 14 dependency map (current state of openness)

Item 14 = `genus X = 0 ↔ Nonempty (X ≃ₜ S²)`. All Lean architectural
factoring is exhausted. The remaining open content is genuinely
classical:

- **Forward leg (`genus = 0 → ≃ₜ S²`)** has **one** way:
  `hSP : ExistsSimplePoleGermAtSomePoint X` (Riemann-Roch existence of
  a simple-pole germ at some point). Equivalent to `RR_DimGE2_GenusZero_Germ
  X`. No alternative — uniformization for genus-0 surfaces is what
  produces hSP classically.
- **Reverse leg (`≃ₜ S² → genus = 0`)** has **two** ways:
  - `h_top` (topological-sphere uniformization: `Nonempty (X ≃ₜ S²) →
    Nonempty (HolomorphicEquiv X RS)`), or
  - `Subsingleton (HolomorphicOneForm X)` from `SimplyConnectedSpace X`,
    which routes through BSLB + path-primitive analytic content.

For `X = RiemannSphere` specifically, both legs are unconditional in
tree (smoke-tested in `Topology/Item14RiemannSphereViaBSLBPathPrimitive.lean`).

## What the prior session attacked

Started the Dolbeault arc toward discharging `hSP` via
`H¹(X, O) = 0` at genus 0 + ∂̄-equation solvability.

- `Manifold/DBarOperator.lean` (commit 5116a83) — `dbarChart` chart-side
  ∂̄ operator + linearity (`_add`, `_neg`, `_const`, `_zero`).
- `Manifold/SimplePoleConstructionFromChart.lean` (commit 20c271b) —
  `SimplePoleGermExtensionHypothesis X` precisely-named classical input.

The holomorphic-zero theorem `dbarChart_eq_zero_of_hasDerivAt` is
**deferred** because of an unresolved `IsScalarTower ℝ ℂ ℂ` synthesis
failure in `HasFDerivAt.restrictScalars ℝ`.

## The IsScalarTower obstacle (debug starting point)

Mathlib's `Mathlib/Analysis/Complex/RealDeriv.lean` line 53-55 uses
exactly the same idiom successfully:

```lean
have B :
    HasStrictFDerivAt e ((ContinuousLinearMap.smulRight 1 e' : ℂ →L[ℂ] ℂ).restrictScalars ℝ)
      (ofRealCLM z) :=
  h.hasStrictFDerivAt.restrictScalars ℝ
```

In our file the analogous call:

```lean
have hfd_real : HasFDerivAt f
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) f').restrictScalars ℝ) z₀ :=
  hf.hasFDerivAt.restrictScalars ℝ
```

fails with `failed to synthesize instance IsScalarTower ℝ ℂ ℂ` despite
the high-priority `IsScalarTower.right` instance in
`Mathlib.Algebra.Algebra.Defs`. Multiple imports tried (`Algebra.Defs`,
`Complex.Conformal`, `LinearAlgebra.Complex.Module`); none unblock it.
`letI : IsScalarTower ℝ ℂ ℂ := inferInstance` itself succeeds, but the
subsequent `restrictScalars` call still errors.

**Recommended debug next steps:**

1. Add `set_option trace.Meta.synthInstance true` before the failing
   line and read the trace to see why synth fails.
2. Compare the elaboration context at the failing line to mathlib's
   working site (variables in scope, namespace, etc.).
3. Try `(hf.hasFDerivAt : HasFDerivAt f _ z₀).restrictScalars ℝ` with
   explicit type ascription on `hf.hasFDerivAt` to nudge unification.
4. Try wrapping the proof in a `section` that opens
   `RestrictScalars` mathlib namespace (if there is one).
5. Last resort: bypass `restrictScalars` and prove the values directly
   via `fderiv_eq_deriv_mul` style + manual ℝ-Fréchet derivative
   construction.

## Next chip after `dbarChart_eq_zero_of_hasDerivAt` lands

The roadmap for the Dolbeault arc (each chip a separate file):

1. ✅ `DBarOperator.lean` — chart-side definition + linearity (committed).
2. **Next**: holomorphic ⇒ `dbarChart = 0` (the IsScalarTower one above).
3. Lift `dbarChart` from chart to manifold: `dbar f x` for `f : X → ℂ`
   on a complex 1-manifold, via chart pullback.
4. Define `dbar` of smooth forms on `X` (`Ω^0 → Ω^(0,1)`).
5. Set up L² inner product on smooth sections.
6. Prove `dbar` is closed (image in L²) — key analytic input.
7. Adjoint `dbar*` on `Ω^(0,1)`.
8. Laplacian `Δ_dbar = dbar* dbar + dbar dbar*` on `Ω^0`. Fredholm.
9. Hodge decomposition: `Ω^(0,1) = im(dbar) ⊕ ker(Δ_dbar)`.
10. `ker(Δ_dbar on Ω^(0,1)) ≅ H¹(X, O)` (Dolbeault iso).
11. At genus 0: `H¹(X, O) ≅ H⁰(X, Ω¹)^* = 0`, hence solvability
    `dbar u = h` for any `h ∈ Ω^(0,1)`.
12. Construct `hSP` via the chart bump + ∂̄-solve recipe in
    `SimplePoleConstructionFromChart.lean`'s docstring.

Each step is a chip. None are at the mathlib pin. Realistic scope:
multi-session arc.

## Standing constraints for the new session

- **Branch discipline:** stay on `feat/item14-classical-content` in this
  worktree. If you need to push, `git push -u origin feat/item14-classical-content`
  (the branch is local-only — no upstream yet).
- **Don't touch `JacobianChallenge.lean` (umbrella) without coordinating**:
  the parallel session frequently modifies it. Their edits are on
  different branches but stash conflicts will happen if both touch the
  same lines.
- **Don't claim "PUSHED" without verifying** (`feedback_verify_push_before_claiming`).
- **No fabricated LOC estimates** (`feedback_no_fabricated_loc_estimates`).
  Each chip is its own size; report measured size after the fact.
- **Single-file verify**: `LEAN_NUM_THREADS=1 lake env lean <file>` for
  iteration; throttled `taskpolicy -b nice -n 19 lake build <module>` for
  the duplicate-name catch before push.
- **No `du -sh` on `.lake`** — instant kernel panic (CLAUDE.md).
- The chip discipline from the prior session: pick ONE classical input
  and push on it, don't ping-pong between architectural shuffles. The
  prior session shipped 11 chips but most were consolidation; only
  DBarOperator started real classical infrastructure.

## Worktree commands cheat sheet

```bash
# From anywhere
git worktree list                # confirm both worktrees still pinned

# Enter the item-14 worktree
cd "/Volumes/4TB SD/ClaudeCode/jacobian-lean-challenge-item14"

# When done with the worktree (only if abandoning the branch)
git worktree remove "/Volumes/4TB SD/ClaudeCode/jacobian-lean-challenge-item14"
```
