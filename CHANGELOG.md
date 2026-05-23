# Changelog

## 2026-05-23 — holomorphic parametric integral arc closure: `ChartLocalPrimitiveSmoothExt` at `chartAt ℂ y` UNCONDITIONAL (6 chips, +1,376 Lean LOC across 6 new files)

State: build single-file clean for each chip, repo now **1,072 `.lean`
files / 182,183 LOC** (vs. 1,066 / 180,807 baseline). Zero `sorry`,
zero `axiom`. New chips not yet wired into the umbrella build
(`lake build` still 9,326 jobs; per-file `LEAN_NUM_THREADS=1 lake env
lean` clean). All 6 commits local on `main` (verified
`git log origin/main..HEAD`). Item count in `Basic.lean` unchanged at
**14 / 24 STRICT-CLOSED** — these chips factor item 14's analytic-side
named hypothesis `h_smooth_b` to *unconditional* at the natural
per-point chart cover, but item 14 itself requires the remaining
classical inputs (`h_ftc_b`, `hSP`, `h_bslb`) to flip.

### Headline

`ChartLocalPrimitiveSmoothExt (chartAt ℂ y) … y … om` is now
**unconditional** for every `y : X` and every `om : HolomorphicOneForm X`
(modulo the convex chart-target hypothesis already in the
definition). This discharges one of the four minimal named
hypotheses of item 14's reverse leg via the holomorphic parametric
integral route — bypassing the ℂ→ℝ scalar-restriction diamond
entirely (the 2026-05-21 sub-arc B work was tangential).

### Chip sequence

* **Chip A — `Manifold/AnalyticOnChartLocalIntegrand.lean`** (`3e8da0a`,
  +378 LOC). `analyticOn_chartLocalIntegrand_param`: for any
  `AnalyticOn ℂ f S` on convex open `S ∋ z₀`,
  `fun z ↦ ∫ t in 0..1, f(B(z₀, z, t)) · V(z₀, z, t)` is
  `AnalyticOn ℂ` on `S`. Combines chips 10 + 11 with an explicit
  `∂z`-derivative `chartLocalIntegrandDerivInZ`, compactness-based
  uniform bound via `IsCompact.exists_isMaxOn`, and Goursat. Notable
  Lean gotcha indexed at top of MEMORY.md: the derivative def is
  marked `@[irreducible]` to dodge a `maxHeartbeats` blowup
  (sum-of-products body of multiple `bumpedSegment`/`chartCoordVelocity`
  calls triggers `whnf` cascades on every downstream `Continuous`
  lemma, even at 2M heartbeats).

* **Chip B1 — `Manifold/ComplexChainPeriodSinglePathIntegral.lean`**
  (`b395089`, +183 LOC). Path-only generalization of
  `ChartContainedClosedLoop.complexChainPeriod_single_eq_complex_integral`:
  drops the loop hypothesis. For any smooth path γ and any
  HolomorphicOneForm α, with the ℂ-valued integrand continuous on [0,1],
  `complexChainPeriod (single γ) α = ∫ t in 0..1, (α.eval (γ.ambient t)) (γ.velocity t)`.
  The loop hypothesis was unused in the original proof — this is the
  substantive observation.

* **Chip B2 — `Manifold/PointwiseChartEvalPath.lean`** (`cf5d1f7`,
  +265 LOC). Path-only generalization of
  `ChartContainedClosedLoop.pointwiseChartEvalIdentity_unconditional`:
  for any smooth path γ, base point y with `γ.ambient t ∈ (chartAt y).source`,
  `(α.eval (γ.ambient t)) (γ.velocity t) = α.localCoeff y ((chartAt y) (γ.ambient t)) · deriv ((chartAt y) ∘ γ.ambient) t`.
  Mirrors the unconditional proof structure (T_yx/T_xy cocycle +
  localCoeff chart-image unfold + deriv chartPath = T_xy v chain rule),
  but with loop-data field accesses replaced by direct (γ, y, t, h_src)
  hypotheses. Helper trio restated locally (originals are `private`).

* **Chip B3 — `Manifold/ChartLocalPrimitiveChartIntegral.lean`**
  (`5e0c4e4`, +251 LOC). Headline chip-B identity:
  `chartLocalPrimitive (chartAt y) … y … om x = ∫ t in 0..1, om.localCoeff y (B((chartAt y) y, (chartAt y) x, t)) · chartCoordVelocity ((chartAt y) y, (chartAt y) x, t)`.
  Combines chip B1 (structural bridge) + chip B2 (per-t identity) +
  two structural identifications for `γ := linearInChartSegment φ y x`:
  `(chartAt y) (γ.ambient t) = B(t)` on `Icc 0 1` via
  `ambient_eq_on_unitInterval` + `left_inv`; and
  `deriv ((chartAt y) ∘ γ.ambient) t = chartCoordVelocity t` on
  `Ioo 0 1` via `EventuallyEq.deriv_eq`. Glued by
  `intervalIntegral.integral_congr_ae` (the endpoint `{1}` is
  measure zero in `Ioc 0 1`). Plus `hasDerivAt_bumpedSegment_in_t`
  /  `deriv_bumpedSegment_eq_chartCoordVelocity` helper: the
  time-derivative formula proved directly via ℝ-smul +
  `HasDerivAt.smul_const`, avoiding the `Complex.ofRealCLM ∘ ·`
  scomp-vs-cast unification gymnastics.

* **Chip C — `Manifold/ChartLocalPrimitiveSmoothExtChartAt.lean`**
  (`f42f7a6`, +152 LOC). **`ChartLocalPrimitiveSmoothExt` at
  `chartAt ℂ y` UNCONDITIONAL**. Pipeline: `localCoeff_analyticOn`
  → chip A → `AnalyticOn.contDiffOn` → `ContDiffOn.contMDiffOn`
  → `contMDiffOn_chart` + `ContMDiffOn.comp` + chip B3 +
  `chartLocalPrimitiveExtend_eq_chartLocalPrimitive` +
  `ContMDiffOn.congr`. Scope: the chip's natural chart `chartAt ℂ y`
  (which is what item 14's reverse leg uses when covering X by
  per-point natural charts). A fully general φ ∈ atlas would need a
  chart-transition argument relating `om.localCoeff y` across charts;
  not needed here.

* **Chip D1 — `Manifold/ChartLocalIntegrandDerivIntegral.lean`**
  (`9d3c610`, +147 LOC). FTC atom for chip D:
  `∫₀¹ chartLocalIntegrandDerivInZ f z₀ z t dt = f(z)` for `f`
  analytic on convex open `S ∋ z₀, z`. Proof: the integrand-`z`
  derivative is the time-derivative of `aux(t) := ((σ(t):ℝ):ℂ) · f(B(z₀, z, t))`
  (product + chain rule + `HasDerivAt.smul_const` /
  `HasDerivAt.ofReal_comp`); FTC over `[0, 1]` collapses to
  `aux(1) − aux(0) = 1·f(z) − 0·f(z₀) = f(z)` using `σ(0)=0, σ(1)=1,
  B(0)=z₀, B(1)=z`.

### Remaining chip-D pieces (next session)

* **D2** — `HasDerivAt g (f(z)) z` at every `z ∈ S`, combining chip
  A's parametric Fréchet output with D1.
* **D3** — `mfderiv` version on chart target via the standard
  `HasDerivAt.hasMFDerivAt`-style lift.
* **D4** — chain rule for `chartLocalPrimitive = g ∘ chartAt y` to
  get `mfderiv chartLocalPrimitive x` in chart-coords.
* **D5** — identify `mfderiv chartLocalPrimitive x = om.eval x` via
  chip B2 + ℂ-linearity (both sides are CLMs ℂ → ℂ; agree on
  `1 : ℂ`).

Once D2–D5 land, `h_ftc_b` is also unconditional → **2 of the 4
minimal item-14 inputs** done, leaving only `hSP` (RR-class
existence of simple-pole germ) and `h_bslb` (smooth-Hurewicz
`BasedSmoothLoopsBoundHypothesis`) as actual classical content.

## 2026-05-21 post-PR-#4 continuation — FTC-arc foundation, ℂ→ℝ diamond bypass, and holomorphic parametric integral atom (11 chips, ~907 LOC)

Final state: build **9326 jobs**, **1066 `.lean` files**, **180,807
LOC**. Zero `sorry`, zero `axiom`. Item count unchanged at **14 / 24
STRICT-CLOSED**. `origin/main` HEAD `fe55640`.

After PR #4, the session continued through several `/compact` rounds,
landing **eleven foundation chips directly on `main`** (no PR-grouped
review). Three sub-arcs:

### Sub-arc A — FTC integrand-smoothness foundation (chips 1-3, ~290 LOC)

* `Manifold/BumpedSegmentParamSmooth.lean` (`078c921`) — joint `C^∞`
  of `(z, t) ↦ bumpedSegment z₀ z t` and `chartCoordVelocity z₀ z t`
  on `ℂ × ℝ`.
* `Manifold/ChartLocalIntegrandSmooth.lean` (`8d4ef29`) — joint
  `ContDiffOn ℝ ∞` of the abstract chart-coord integrand product
  on `S × Set.univ` (convex `S` + `z₀ ∈ S` + `ContDiffOn ℝ ∞ f`).
* `Manifold/ChartLocalIntegrandRealImag.lean` (`c1a20c9`) — Re/Im
  part smoothness via `Complex.reCLM`/`Complex.imCLM` composition.

### Sub-arc B — Hand-rolled ℂ→ℝ scalar-restriction bridge (chips 4-9, ~430 LOC)

The mathlib `IsScalarTower ℝ ℂ ℂ` diamond between
`Complex.SMul.instSMulRealComplex` and `Algebra.id ℂ`-derived SMul
blocks `ContDiffOn.restrict_scalars ℝ` (and friends) for `ℂ → ℂ`
functions in `HolomorphicOneFormChartCoeffOnTarget`-imported contexts.
Bypassed via three layered hand-rolled bridges:

* `Manifold/HasFDerivAtRestrictScalarsComplex.lean` (`2712965`) — base
  case at `HasFDerivAt` level via the base-field-agnostic `IsLittleO`
  form: extract `=o[𝓝 x]` via `.isLittleO`, apply
  `ContinuousLinearMap.restrictScalars ℝ` (which only needs
  `LinearMap.CompatibleSMul ℂ ℂ ℝ ℂ`, NOT `IsScalarTower`),
  reconstruct via `.of_isLittleO`. Variants for `HasFDerivWithinAt`,
  `DifferentiableAt`, `DifferentiableWithinAt`, `DifferentiableOn`,
  `Differentiable`.
* `Manifold/FDerivRestrictScalarsComplexIdentity.lean` (`f6a07ed`) —
  `fderiv ℝ f x = (fderiv ℂ f x).restrictScalars ℝ` (and within-set
  variant under `UniqueDiffWithinAt ℝ`).
* `Manifold/LocalCoeffDifferentiableOnReal.lean` (`0c09753`) —
  `HolomorphicOneForm.localCoeff_differentiableOn_real`: concrete
  `DifferentiableOn ℝ (localCoeff om y) (chartAt ℂ y).target`.
* `Manifold/RestrictScalarsContinuityComplex.lean` (`aab8f8d`) —
  hand-rolled function-level continuity of
  `(·.restrictScalars ℝ) : (ℂ →L[ℂ] ℂ) → (ℂ →L[ℝ] ℂ)` via
  `opNorm_le_bound` (1-Lipschitz on differences). Bypasses mathlib's
  `continuous_restrictScalars` which also hits the diamond.
* `Manifold/ContDiffOnRealOneComplex.lean` (`aab8f8d`) — abstract
  `ContDiffOn.complex_top_to_real_one` (`ContDiffOn ℂ ⊤ f S` on open
  `S` → `ContDiffOn ℝ 1 f S` for `f : ℂ → ℂ`) plus
  `HolomorphicOneForm.localCoeff_contDiffOn_real_one`. Uses
  `contDiffOn_succ_iff_fderivWithin` at `n = 0`; composed from chips
  4 / 5 / 7.

**Diamond-bypass status:** `DifferentiableOn ℝ` and `ContDiffOn ℝ 1`
for `localCoeff` are now in tree. Full `ContDiffOn ℝ ω` is still open
— iterating the bridge to second-derivative codomain `ℂ → (ℂ →L[ℂ] ℂ)`
needs `CompatibleSMul ℂ (ℂ →L[ℂ] ℂ) ℝ ℂ` which doesn't synthesize
automatically.

### Sub-arc C — Holomorphic parametric integral atom (chips 10-11, ~220 LOC)

After confirming via re-reading `PathPrimitiveLocalSmoothFTCNamed.lean`
that `ChartLocalPrimitiveSmoothExt` requires `ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω`
(= `ContDiffOn ℂ ω`, holomorphic), the ℂ→ℝ bridge work was **partially
tangential** — the actual blocker is the **holomorphic parametric
integral**. Pivot:

* `Manifold/AnalyticOnIntervalIntegralParam.lean` (`dda33b4`) —
  `analyticOn_intervalIntegral_param`: for `f : ℂ → ℝ → ℂ` with
  per-point ℂ-derivative + local ε-ball domination on `f'`, the
  parameter map `z ↦ ∫ t in a..b, f z t` is `AnalyticOn ℂ` on
  open `S`. Wraps mathlib
  `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
  at `𝕜 = ℂ` with `DifferentiableOn.analyticOn` (Goursat).
* `Manifold/ChartLocalIntegrandAnalyticInZ.lean` (`5738903`) —
  `analyticAt_chartLocalIntegrand_in_z`: for analytic `f` on convex
  open `S ∋ z₀`, the chart-coord integrand
  `fun z' => f (bumpedSegment z₀ z' t) * chartCoordVelocity z₀ z' t`
  is `AnalyticAt ℂ` at every `z ∈ S` for each `t`. Plus helper
  lemmas `analyticAt_bumpedSegment_in_z` and
  `analyticAt_chartCoordVelocity_in_z` (both ℂ-linear/affine in z).

### Item-14 frontier after this session

Closed in tree on RS and ℂ via in-tree discharges of the 4 minimal
named hypotheses. For general genus-0 simply-connected `X`, the 4
named hypotheses remain open:

1. `hSP` (forward leg, RR-class) — no active chip arc.
2. `h_bslb` (reverse leg, smooth-Hurewicz at genus 0) — chain-assembly
   arc (PRs #1-#4) is at the architectural-choice point: either
   restructure `Smooth2Simplex` to use `ContMDiffOn [0,1]²`, define a
   finer SmoothPath structure exposing `ContDiffBump`-extended
   ambient, or strong-hypothesis pattern.
3. `h_smooth_b` (reverse leg, analytic pathPrimitive) — **path clear
   through sub-arc C**: combine chip 11's per-`t` analyticity with
   chip 10's parametric AnalyticOn, then chart-pulled identity
   (still TBD) + chart transport → `ChartLocalPrimitiveSmoothExt`.
4. `h_ftc_b` (reverse leg, FTC) — analogous arc once `h_smooth_b`
   tooling is in place.

3 named hypothesis discharges away from full general-X item-14
closure, plus the architectural choice for h_bslb.

## 2026-05-21 PR #4 — Item-14 reverse leg: `SmoothPath.subpath` primitive (1 commit + merge, +111 LOC)

Final state: build **9316 jobs**, **1056 `.lean` files**, **179,900
LOC**. Zero `sorry`, zero `axiom`. Item count unchanged at **14 / 24
STRICT-CLOSED**. `origin/main` HEAD `b48070b` (merge of
`feat/item14-bslb-chain-assembly` via PR #4).

Single new file `Manifold/SmoothPathSubpath.lean`:

* `SmoothPath.subpathAmbient γ a b t := γ.ambient (a + t * (b - a))` —
  the affine reparam of `γ.ambient` onto `[a, b]`.
* `subpathAmbient_zero` / `_one` — endpoint identifications.
* `contMDiff_subpathAmbient` — smoothness via composition of `γ.ambient`'s
  `ContMDiff ∞` with the affine reparam's `ContDiff ∞`.
* `SmoothPath.subpath γ a b ha hab hb : SmoothPath IM X` — the packaged
  sub-arc as a `SmoothPath`, with `src := γ.ambient a` and
  `tgt := γ.ambient b`.
* `subpath_src` / `_tgt` simp lemmas.

This is the **foundational primitive for chart-cover Lebesgue
subdivision of a smooth loop**. Combined with
`lebesgueSubdivision_of_chartCover` (PR #1), it extracts each piece
of γ as a `SmoothPath` qualifying for the chart-local polygonal-
approximation bordism (PR #3).

### Architectural blocker identified for the final concatenation chip

Investigating the next chip — concatenating sub-arc bordisms across
the Lebesgue subdivision — revealed a genuine mathematical
obstruction. The chart-local bordism (PR #3) requires `γ_n.ambient`
to be **globally** chart-contained (∀ t : ℝ). But `γ.subpath.ambient`
outside `[0, 1]` is `Classical.choose`-determined and might not stay
in the chart's source.

The "bump-extension" workaround (constructing a smooth `σ : ℝ → [0, 1]`
with `σ = identity` on `[0, 1]`) was shown **mathematically
impossible**: `σ`'s smoothness at `t = 0` forces matching derivatives
`σ'(0⁻) = σ'(0⁺) = 1`, which forces `σ < 0` just left of `0`,
contradicting `σ ≥ 0`.

Genuine fixes available (next session):

1. **Restructure `Smooth2Simplex`** to use `ContMDiffOn [0, 1]²`
   instead of `ContMDiff` globally on `Fin 2 → ℝ`. Major refactor:
   `boundary`, `boundary₂`, `boundary₂Cycle`, the integration
   machinery, `stokesBoundaries` would all need parallel adaptation.
2. **Explicit bump extension via `ContDiffBump`** in a finer SmoothPath
   structure that exposes its ambient (rather than burying it in
   `Classical.choose`).
3. **Strong-hypothesis pattern**: define a `BasedSmoothLoopsBound_BumpedCover`
   predicate for X with finite chart cover where loops can be
   guaranteed globally chart-contained.

## 2026-05-21 PR #3 — Item-14 reverse leg: chart-local polygonal-approximation bordism (3 commits + merge, +230 LOC)

Final state: build **9316 jobs**, **1055 `.lean` files**, **179,789
LOC**. Zero `sorry`, zero `axiom`. Item count unchanged at **14 / 24
STRICT-CLOSED**. `origin/main` HEAD `5934aad` (merge of
`feat/item14-bordism-constructor` via PR #3).

Three commits:

* **refactor**: `SmoothHomotopyPath.left_edge` / `right_edge` restricted
  to `unitInterval` (was `∀ t : ℝ`). Identifies against `γ_i.toPath`
  rather than `γ_i.ambient`. Sidesteps `Classical.choose`-opacity of
  `γ_line.ambient` outside the unit interval that would otherwise
  block any constructor pairing `chartHomotopyMap` with
  `chartStraightLinePath_univ`. Cascades through `face0_lowerRight_eq`
  and `face1_upperLeft_eq` in `SmoothHomotopyPathDiagonalSplit.lean`
  — both simplified to direct edge applications (no longer need the
  `ambient_eq_on_unitInterval` bridge step).

* **feat**: `Manifold/SmoothHomotopyPathChartStraightLine.lean` —
  `chartHomotopyMapDirect q γ x` inlines the chart-straight-line
  formula directly:

      H(s, t) := chart.symm(
        (1 - s) • chart(γ.amb t)
          + s • ((1 - t) • chart(γ.src) + t • chart(γ.tgt)))

  This avoids `γ_line.ambient` entirely. Global smoothness
  `contMDiff_chartHomotopyMapDirect_univ` follows from `chart ∘ γ.amb`
  smoothness (γ.amb globally in chart.source by hypothesis) +
  in-chart-target linear interpolation smoothness + `chart.symm`
  global smoothness (chart.target = univ).

* **feat**: `chartStraightLineHomotopy` constructor + headline
  `chartStraightLine_singleSub_mem_stokesBoundaries`:

      For γ globally chart-contained in a full-target chart,
        single (chartStraightLinePath γ.src γ.tgt) - single γ
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) Y.

  Constructor: package `chartHomotopyMapDirect` + smoothness + all
  four edge identities into a `SmoothHomotopyPath γ γ_line`. Edge
  identities discharged by `module` collapses of the linear-
  interpolation formulas + `OpenPartialHomeomorph.left_inv` for the
  chart-symm-of-chart identifications. Apply
  `SmoothHomotopyPath.singleSub_smoothCycle_mem_stokesBoundaries`
  from PR #2.

### Net contribution

**The chart-local polygonal-approximation bordism is closed.** Any
smooth subarc of γ that lies entirely in a single full-target chart
is smoothly bordant to its chart-straight-line approximation between
the same endpoints, with explicit 2-chain witness.

The chain-assembly toward `BasedSmoothLoopsBoundHypothesis X p₀` on
chart-cover-equipped simply-connected X now decomposes into:
* chart-cover Lebesgue subdivision of γ → chart-contained subarcs ✓ (PR #1)
* per-subarc bordism to chart-straight-line ✓ (this PR)
* closed polygonal-chain ∈ stokesBoundaries ✓ (PR #1)
* concatenate sub-bordisms + match outer edges — mechanical, next PR.

## 2026-05-21 PR #2 — Item-14 reverse leg: SmoothHomotopyPath diagonal-split + bordism (4 commits + merge, +478 LOC)

Final state: build **9316 jobs**, **1054 `.lean` files**, **179,559
LOC**. Zero `sorry`, zero `axiom`. Item count unchanged at **14 / 24
STRICT-CLOSED**. `origin/main` HEAD `4e3ed97` (merge of
`feat/item14-reverse-leg-bordism` via PR #2).

Single new file `Manifold/SmoothHomotopyPathDiagonalSplit.lean`,
~480 LOC, containing the **SmoothHomotopyPath bordism arc**:
diagonal-split into two `Smooth2Simplex`es (`lowerRightSimplex` +
`upperLeftSimplex`) with vertex evaluations, `diagonalPath H`, all
six face identifications, boundary sum theorem
`boundary_lowerRight_plus_upperLeft`, and the headline
`singleSub_smoothCycle_mem_stokesBoundaries` — for any
`SmoothHomotopyPath γ₀ γ₁`, the SmoothCycle `single γ₁ - single γ₀`
lies in `stokesBoundaries 𝓘(ℝ, ℂ) Y`.

Architectural blocker hit on the chart-straight-line `SmoothHomotopyPath`
constructor: `γ_line.ambient` (from `chartStraightLinePath_univ` via
`Classical.choose`) isn't definitionally equal to `chartStraightLineMap`
outside the unit interval, so the structure's universally-quantified
edge identity `∀ t : ℝ, toFun ![1, t] = γ_line.ambient t` can only
be proven on the unit interval. Resolved by either a unitInterval-
restricted refactor of `SmoothHomotopyPath`'s edges or a separate
ambient-witnessing structure — tracked for the next PR.

## 2026-05-21 PR #1 — Item-14 classical-content arc: chain assembly + Dolbeault + chart-cell infra (57 commits + merge via PR #1, +3,639 LOC)

Final state: build **9316 jobs**, **1053 `.lean` files**, **179,081
LOC**. Zero `sorry`, zero `axiom`. Item count unchanged at **14 / 24
STRICT-CLOSED** — substantive classical infrastructure toward item-14
reverse-leg closure on simply-connected X. `origin/main` HEAD
`be4146d` (merge of `feat/item14-classical-content` via PR #1).

### Arc — Item-14 reverse leg toward BSLB on simply-connected X (~37 chips, ~3,300 LOC across 23 new files)

**Dolbeault foundational (chips 2-8, prior session within branch).**

* `Manifold/DBarOperator.lean` — chart-side `dbarChart f z₀` on `ℂ → ℂ`,
  linearity (`_add`/`_neg`/`_const`/`_zero`/`_const_mul`), holomorphic
  ⇒ `dbarChart = 0` via mathlib's `HasDerivAt.complexToReal_fderiv`,
  CR-converse `differentiableAt_complex_of_dbarChart_eq_zero` via
  `differentiableAt_complex_iff_differentiableAt_real`.
* `Manifold/DBarManifold.lean` — manifold-side `dbar f x` via
  `extChartAt 𝓘(ℂ,ℂ) x` + linearity + `_const_mul`
  + `dbar_eq_zero_of_chartPullback_differentiableAt`.
* `Manifold/DBarManifoldMDiff.lean` — bridge to `MDifferentiableAt
  𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ)`: `mdifferentiableAt_target_complex_iff_chartPullback_differentiableAt`,
  manifold-side CR converse, and the full biconditional
  `mdifferentiableAt_iff_dbar_eq_zero`.
* `Manifold/DBarChartChainRule.lean` — Wirtinger chain rule
  `dbarChart (f ∘ g) z₀ = conj g'(z₀) · dbarChart f (g z₀)` for
  holomorphic inner `g`, giving chart-independence of ∂̄-vanishing on
  a complex 1-manifold under nonzero transition derivative.

**Architectural reductions.**

* `Manifold/SmoothPathChartSubdivision.lean` — `SmoothPath.lebesgueSubdivision`
  for an arbitrary open cover, plus `_of_chartCover` specialization
  using `[HasConvexTargetChartCover X]`.
* `Manifold/SubdivisionTelescopingToLoopFromBSLB.lean` —
  `SubdivisionTelescopingToLoop_named X ⇐ ∀ p₀, BSLB X p₀`. Reduces
  the in-tree TelescopingTo-Loop hypothesis to universal BSLB.
* `Manifold/SubdivisionTelescopingToLoopSubsingleton.lean` —
  typeclass-generalized trivial discharge under
  `[Subsingleton (HolomorphicOneForm X)]`.

**Chart-cell `Smooth2Simplex` constructor.** Bridges
`[IsManifold 𝓘(ℂ,ℂ) ω X]` to the ℝ-model expected by `Smooth2Simplex`
via the in-tree `complexManifoldRealification` instance.

* `Manifold/BilinearChartCellSimplex.lean` — bilinear chart-cell:
  `bilinearChartInterp` definition + smoothness on ℝ² via `ContDiff`
  + convex containment `bilinearChartInterp_in_target_on_unit_square`
  via `Convex.sum_mem` + `Fin.sum_univ_four` + Fin 2 reindexing +
  `bilinearChartCellSimplex_univ : Smooth2Simplex 𝓘(ℝ,ℂ) X` (full-
  target chart case).
* `Manifold/AffineChartTriangleSimplex.lean` — affine 3-corner
  variant matching `Smooth2Simplex`'s Δ²-convention. `affineChartTriangle`
  + smoothness + 3-point convex containment via `Convex.sum_mem` +
  `Fin.sum_univ_three` + `affineChartTriangleSimplex_univ : Smooth2Simplex
  𝓘(ℝ,ℂ) X` + vertex-toFun simp lemmas (`_v0`/`_v1`/`_v2`).

**Chart-straight-line `SmoothPath` + boundary identification.**

* `Manifold/ChartStraightLinePath.lean` — `chartStraightLinePath_univ`
  via `chart.symm((1-t) • z₀ + t • z₁)` + smoothness +
  `_src`/`_tgt` simp lemmas. **`smoothPath_ext_of_toPath_apply`**
  extensionality lemma (SmoothPath has no `@[ext]` in-tree). Full
  SmoothPath identification of the three triangle faces:
  `face0/1/2_eq_chartStraightLinePath_univ` via the toFun-level
  identifications + the new ext lemma. `chartStraightLinePath_univ_reverse`:
  `(path z₀ z₁).reverse = path z₁ z₀` (proven via `module` on the
  linear-interpolation identity). Explicit `Smooth2Simplex.boundary`
  of the chart-triangle as a 3-path `SmoothChain`:
  `affineChartTriangleSimplex_univ_boundary`.

**Chain cancellation.**

* `Manifold/AdjacentTriangleCancellation.lean` —
  `chartStraightLinePath_pair_eq_reverseSum` (forward+reverse pair as
  a SmoothCycle) + `chartStraightLinePath_pair_smoothCycle_mem_stokesBoundaries`
  (using in-tree `single_smoothPath_plus_reverse_mem_stokesBoundaries`).
  `two_chart_triangle_boundary_eq` (explicit two-triangle boundary
  expansion) + `outerChain` definition (4-edge non-shared chain) +
  `two_chart_triangle_boundary_decomp`. **`outerChain_mem_smoothCycle`**
  (boundary in `X →₀ ℤ` vanishes by endpoint cancellation) and
  **`outerChain_mem_stokesBoundaries`** — substantive Stokes-style
  cancellation conclusion proven from first principles via
  `boundary₂Cycle (single σ₁ + single σ₂) - sharedPair = outerChain`
  + AddSubgroup closure under subtraction.

**Fan triangulation.**

* `Manifold/FanTriangulation.lean` —
  `affineChartTriangleSimplex_boundary_as_loop_plus_spokes` (single
  triangle's boundary = polygonal-edge + spoke-pair). List-recursive
  defs: `fanChain` (the 2-chain over consecutive pairs of `zs`),
  `polygonalChain` (the SmoothChain of polygonal edges),
  `spokeResidue` (head→last residue spokes).
  **`boundary₂_fanChain`** — full inductive boundary identity
  `boundary₂ (fanChain z_c zs) = polygonalChain zs + spokeResidue z_c zs`,
  proven by List induction with nested cases on the tail and
  `List.getLast` alignment. **`spokeResidue_eq_zero_of_closed`** —
  spoke residue vanishes when `zs.getLast = zs.head`.
  **`polygonalChain_eq_boundary_of_closed`** and
  **`polygonalChain_smoothCycle_mem_stokesBoundaries_of_closed`** —
  any closed polygonal loop traced by chart-straight-line paths in a
  single full-target chart is the explicit boundary of a fan
  2-chain, hence lies in `stokesBoundaries`. *Headline chip of the
  arc.*

**`SmoothHomotopyPath` toolkit.**

* `Manifold/SmoothHomotopyPath.lean` — structure
  `SmoothHomotopyPath γ₀ γ₁ h_src h_tgt` (analog of
  `SmoothHomotopyBasedLoop` for paths sharing endpoints) with four
  edge identities. `chartHomotopyMap q γ₀ γ₁ x := chart.symm((1 - x 0)
  • chart(γ₀.amb (x 1)) + x 0 • chart(γ₁.amb (x 1)))`. All four edge
  lemmas: `chartHomotopyMap_left_edge`, `_right_edge` (via
  `OpenPartialHomeomorph.left_inv`), `_bottom_edge`, `_top_edge`
  (constant at the shared src/tgt; interpolation cancellation
  discharged by `module`). Smoothness lemma
  **`contMDiff_chartHomotopyMap_univ`** under full-target chart +
  global containment of both paths.

### Net contribution

No items in `Basic.lean`'s open list flip from this batch, but the
chain-assembly skeleton for `BasedSmoothLoopsBoundHypothesis X p₀` on
simply-connected X is **substantially advanced**: chain cancellation
works, polygonal-loop bounding works, all chart-cell building blocks
exist. The remaining frontier (documented in `HANDOFF_ITEM14.md`):
package the full `SmoothHomotopyPath` constructor from the toolkit;
diagonal-split into two `Smooth2Simplex`es realizing
`single γ₁ - single γ₀ ∈ stokesBoundaries`; concatenate across the
chart-cover Lebesgue subdivision to bordism γ to a polygonal loop;
combine with the closed-polygonal-loop ∈ stokesBoundaries chip to
conclude BSLB.


---

## Older entries (pre-2026-05-21)

Trimmed 2026-05-23 to reduce bloat. ~6,000 lines of session-by-session
chronological entries (2026-04-26 → 2026-05-20) removed; full history
is available via `git log --oneline CHANGELOG.md` or per-commit `git
show <sha>:CHANGELOG.md`.

Key historical milestones (for reference):

- **v0.1.0 (2026-04-26)**: initial scaffold; Buzzard's challenge
  signature verbatim, every decl `:= sorry`. Mathlib pinned to commit
  `8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (2026-04-15).
- **2026-05-11/12**: items 2, 3, 6, 7, 8, 15, 19, 20, 22, 23, 24
  STRICT-CLOSED via honest `PrincDiv := PrincDivHonestCandidate` +
  `Pic0` + Pic0-functorial pushforward/pullback (the "ZZ256" arc).
  Item 9 STRICT-CLOSED via `degreeFiber` + well-definedness.
- **2026-05-17 (post-Forster)**: item 1 STRICT-CLOSED via
  `DiskChartCover.holomorphicOneFormFiniteDim_holds` (unconditional
  finite-dim of `HolomorphicOneForm X` on compact connected complex
  1-manifold). 10-chip arc.
- **2026-05-XX**: item 16 STRICT-CLOSED via
  `JacobianChallenge.ofCurve_inj_holds` (unconditional discharge chain
  through `PrincDivWitnessExtraction` → degree-1 mero function →
  biholomorphism → genus = 0 contradiction).
- **2026-05-18 to 2026-05-20**: chip-D arc + period-lattice three-atom
  packaging + item 14 multi-input reformulations. Most was paraphrase
  / structural reduction (see `feedback_lean_paraphrase_antipattern.md`
  in NoetherSolve memory); the genuine substantive chips include
  `HolomorphicStokesHypothesis` unconditional, period-lattice on T_L
  unconditional, `smoothBordant_of_smoothHomotopy`, `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) RS p₀` unconditional via Sard +
  Möbius shift + chartN pullback.
- **2026-05-20 (table-audit)**: item-count corrected to 14/24
  STRICT-CLOSED (item 16 flip recognized).
