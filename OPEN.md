# OPEN

> **Note on dates (audit 2026-05-16):** Earlier sessions wrote
> *future-dated* labels in this file (`2026-05-17` through `2026-05-20`)
> driven by anchoring on inflated dates in prior memory files instead
> of the system-provided `currentDate`. Those have been remapped to
> their real git-timestamp dates: `2026-05-17/18/—2026-05-19-afternoon`
> → `2026-05-15`, `2026-05-19-late-afternoon/evening` and `2026-05-20`
> → `2026-05-16`. A residual `+1`-day drift may remain on some narrative
> references to `2026-05-15` / `2026-05-16` (originally `+1` from real
> work on `2026-05-14` / `2026-05-15`); when in doubt, **git commit
> timestamps are the authoritative source**.

The 24 challenge items in `JacobianChallenge/Basic.lean`, mapped to Buzzard's
spec. Three statuses, with one tag for partial progress:

- **OPEN** — `sorry` still present in `Basic.lean`.
- **STUB** — `sorry` replaced by a body that compiles against the verbatim
  signature but is not the intended mathematics. Either the formula is wrong
  (`pullback := 0`, `degree := 0/1 indicator`, `TopologicalSpace := ⊥`), the
  underlying object the lemma is about is itself a stub (`Jacobian := Pic⁰`
  with `PrincDiv := ⊥`), or the proof crucially depends on a placeholder
  being a placeholder.
- **STRICT-CLOSED** — Buzzard-acceptable: the implementation is honest, the
  underlying object is the intended analytic Jacobian, and the lemma is
  what a strict reviewer would sign off on with no further qualification.
  This is the *only* "closed" bar in this repo.
- *(tag)* **PROOF-HONEST** — applies to a STUB item whose proof body is
  honest and would survive future honest replacement of the upstream
  placeholders. Not closure; it's a tag indicating the proof is real even
  though the underlying object is a stub.

**Current scoreboard:**

- **STRICT-CLOSED:** **13 / 24** — items **1, 2, 3, 6, 7, 8, 9, 15, 19, 20,
  22, 23, 24**. Honest `PrincDiv := PrincDivHonestCandidate` and `Pic0`
  (honest, with manifold instances) live in
  `Divisor/PrincipalDivisorRange.lean`. `Pic0.pushforward (hf)` uses
  `JacobianPushforward.lean`; `Pic0.pullbackWeighted (h_desc)` uses
  `Pic0.divPullbackWeighted_descent_of_smooth` in `JacobianPullback.lean`.
  **Item 1** (`genus X : ℕ`) became STRICT-CLOSED via the 10-chip Forster
  density-bound arc (2026-05-17, `DiskChartCoverDensity*.lean` +
  `DiskChartCoverRiesz.lean` + `DiskChartCoverFiniteDim.lean`):
  `HolomorphicOneFormFiniteDim X` is **unconditional** on a compact
  connected complex 1-manifold via the cover-refinement → cotangent
  transition continuity → per-point density identity → per-`x` aggregate
  → density inequality `seminormVal ≤ M · seminormValInner` → outer
  closed ball seq-compact → Riesz → `FiniteDimensional` chain.
  `Module.finrank ℂ (HolomorphicOneForm X)` thus equals the actual
  ℂ-dimension (no junk-zero), so the genus definition is the honest
  geometric genus.
- **STUB (placeholder topology / target / pending discharge):** items
  **4, 10** = 2 items.

  **C3 cascade infrastructure complete (2026-05-17)**: items 4, 5, 10,
  11, 12, 13, 16, 17, 18, 21 all discharge on the analytic Jacobian
  `JacobianAnalyticChoice X` under `[Nonempty (C3FullInputExt X)]`
  (single typeclass-bundled classical existence input). The chain:

  * `C3FullInput X` (basis from item 1 + discreteness + Abel-Jacobi
    input + Abel + Jacobi inversion) → items 4, 5, 10, 11, 12, 13 on
    the analytic Jacobian (`C3FullInputInstances.lean`).
  * `C3FullInputExt X` (+ smoothness + point-injectivity) → items 16,
    17 (`C3FullInputExtClosures.lean`).
  * `C3FullInputCurve B_X B_Y f hf` (per-curve lattice-match) → items
    18, 21 (`C3FullInputCurveClosures.lean`).
  * `JacobianAnalyticChoice X` — full instance bundle on the
    classical-choice analytic Jacobian (`JacobianAnalyticChoice.lean`).
  * `picZeroEquiv : Pic⁰ X ≃+ JacobianAnalyticChoice X` AddEquiv —
    bridge to Basic.lean's `Jacobian X = Pic⁰ X`.

  **Remaining for Basic.lean items 4, 5, 10, 11, 12, 13, 16, 17, 18,
  21 to flip:** the classical existence `Nonempty (C3FullInputExt X)`
  + per-curve `Nonempty (C3FullInputCurve B_X B_Y f hf)`. Both require
  Riemann bilinear + H₁(X; ℤ) ≅ ℤ²ᵍ + Abel's theorem + Jacobi
  inversion + point-injectivity + smoothness — i.e., the full
  classical content of period-lattice + Abel-Jacobi theory, not
  achievable without significant additional formalization.
- **OPEN (sorry in `Basic.lean` or transitively via downstream sorry):**
  items **5, 11, 12, 13, 14, 16, 17, 18, 21** = 9 items. Item 16
  (`ofCurve_inj`) reverted from STUB to OPEN as CLOSURE_MAP predicted —
  it requires Abel-Jacobi (Phase 2).

**Item 14 open content factors onto four named classical inputs**
(`MeromorphicIdentityPropagation X` was discharged via
`Topology/LiftNonvanishingFromIdentityTheorem.lean`'s
`meromorphicIdentityPropagation_holds`):
1. `HolomorphicOneFormFiniteDim X` — Hodge finite-dim gap
   (`Manifold/HodgeFiniteDimensional.lean`).
2. `ExistsSimplePoleGermAtSomePoint X` — RR-existence at genus 0
   (`Topology/RRStrictLtFromSimplePole.lean`).
3. `S2ImpliesGenus0 X` — geometric-vs-topological genus bridge
   (`Topology/SurfaceClassificationGenus.lean`).

   **Two architectural reductions exist for input 3**; downstream callers
   can pick whichever route their auxiliary inputs match best:

   * *Uniformization route* (`Topology/S2ImpliesGenus0Unconditional.lean`):
     reduces to `HolomorphicOneFormEquivRiemannSphere X` (a ℂ-linear
     equivalence between `H⁰(X, Ω¹)` and `H⁰(RS, Ω¹)`). The Riemann-sphere
     side is unconditional via `genus_RiemannSphere_statement_holds`. The
     remaining open input is the linear equivalence itself, which
     classically follows from uniformization + 1-form pullback.

   * *Simple-connectedness route* (new 2026-05-13,
     `Topology/S2ImpliesGenus0FromSimplyConnected.lean`): reduces to
     two precise classical facts — (a) `SimplyConnectedS2`
     (= `SimplyConnectedSpace StandardS2`, formerly the small mathlib
     gap on π₁(S²) = 0), and (b) `HolomorphicOneFormSubsingletonOfSimplyConnected
     X` (the analytic chain `simply connected ⇒ closed 1-forms have
     primitives via Stokes ⇒ primitive is constant by Liouville ⇒ form
     is zero`). **`SimplyConnectedS2` is now UNCONDITIONAL** at the
     mathlib pin via the 15-chip Phase-3 smoothing arc landed on
     `feat/phase3-s2-simply-connected` on 2026-05-15: chart cover →
     Lebesgue partition → stereographic straight-line approximation →
     line-segment empty interior → finite-union Baire argument → loop
     non-surjectivity (`simplyConnectedS2_holds` in
     `Topology/SimplyConnectedS2Unconditional.lean`). The simple-
     connectedness route now reduces to input (b) ALONE.

     **Input (b) further reduces to primitive-existence** (2026-05-16,
     13-chip analytic-side closure arc in
     `Topology/SubsingletonFromPrimitiveExistence.lean` +
     `Topology/LiouvilleForContMDiffOmega.lean` + supporting
     `complexChainPeriod` algebra and `chartLocalPrimitive` data):

     ```
     HolomorphicOneFormSubsingletonOfSimplyConnected X
       ⇐ holomorphicOneFormSubsingletonOfSimplyConnected_of_primitiveExistence
         needs: ∀ om : HolomorphicOneForm X, ∃ F : X → ℂ,
                  ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω F ∧
                    ∀ x, om.eval x = mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) F x
                (every holomorphic 1-form admits a smooth primitive
                 under simple-connectedness)
     ```

     The unconditional Liouville for `ContMDiff ω F : X → ℂ` on
     compact connected `X`
     (`Topology/LiouvilleForContMDiffOmega.lean`'s
     `contMDiff_omega_isConstant`, via the `exp ∘ F` trick) discharges
     the analytic constancy side completely; only the smooth-Stokes /
     path-integral primitive construction on simply-connected
     manifolds remains as a named classical input — structurally the
     `StokesCompactSurfacePartitionOfUnity_hypothesis` content in
     `Manifold/StokesCompactSurface.lean`, plus the regularity
     bootstrap to `ContMDiff ω F`.

     `s2ImpliesGenus0_of_primitiveExistence` provides the full-arc
     composition.

4. Universal at-pole-germ-compatible continuity strengthening of L(δp)
   — operational germ-field refactor
   (`Topology/LiftNonConstancyFromContinuity.lean`'s
   `IsBoundedByDeltaPContinuousAtPole`).

Each input above is citable textbook content. Item 14 remains OPEN;
the four named inputs are real classical math not at the mathlib pin
`8e3c989...`.

> **`CLOSURE_MAP.md` (repo root) is the live source of truth.** It has
> the per-item map, mathlib status verified against this repo's pin
> (`8e3c989...`), Phase 1–4 chip plans with per-component LOC ranges,
> dependency DAG, and verification audit log. Update
> `CLOSURE_MAP.md`, not this file, when items flip.

**Remaining LOC for full 24/24 STRICT-CLOSED (verified per-component):
~28,500–55,000 LOC.** Phase 1 essentially done (A1 + A2 discharged;
genus-0 Abel-Jacobi iso on RiemannSphere now **unconditional** in-tree
post-2026-05-14; C1 chart-cover lift remains, blocked on the ω-level
structural caveat). Phase 2 ~14–28k (period lattice + Abel-Jacobi at
genus ≥ 1, blocked on classical mathlib gaps), Phase 3 ~7.1–15k
(surface classification, blocked), Phase 4 ~6.9–12.8k (Hodge,
blocked). See `CLOSURE_MAP.md` section F.

**Current repo size:** **~126,700 LOC across 696 files** (2026-05-17
late-evening, +~5,900 LOC across 36 chips on top of the late-morning
post-functoriality state). Major landings this session:

* **Item 1 → STRICT-CLOSED.** Full Forster Riesz arc: 10 chips,
  ~1,430 LOC (`DiskChartCoverDensity*.lean` + `DiskChartCoverRiesz.lean`
  + `DiskChartCoverFiniteDim.lean`). `HolomorphicOneFormFiniteDim X`
  unconditional on compact connected complex 1-manifolds.
* **C3 cascade conditional discharges** for items 4, 5, 10, 11, 12,
  13, 16, 17, 18, 21 on the analytic Jacobian. 8 chips, ~1,090 LOC
  (`C3FullInput*.lean`, `JacobianAnalyticChoice.lean`). Single
  typeclass `[Nonempty (C3FullInputExt X)]` + per-curve `Nonempty
  (C3FullInputCurve B_X B_Y f hf)` ⇒ all ten items discharge on the
  analytic Jacobian.
* **Item 14 reverse leg structural reduction.** 7 chips, ~870 LOC
  (`PrimitiveOnSmoothPathConnected.lean`, `PrimitiveSubsingletonReduction.lean`,
  `PrimitiveRiemannSphere.lean`, `PathPrimitiveLinear.lean`,
  `PathPrimitiveBasisReduction.lean`, `PathPrimitiveBasisFTC.lean`,
  `LoopPeriodConstant.lean`). `HolomorphicOneFormSubsingletonOfSimplyConnected`
  factored to per-basis-element `LoopPeriodVanishes` +
  `ContMDiff (pathPrimitive (b i))` + FTC at `eval` (3g concrete
  per-basis analytic statements).

  **FTC basis-reduction now landed (2026-05-17 late evening,
  `pathPrimitiveFTC_of_basis` in `PathPrimitiveBasisFTC.lean`).** The
  formerly-deferred counterpart of `pathPrimitiveSmoothness_of_basis`
  closes: both `PathPrimitiveSmoothness` and `PathPrimitiveFTC` of
  item 14's reverse leg are now factored through a ℂ-basis via
  `Submodule.span_induction` + ℂ-linearity of `pathPrimitive`. The
  remaining open work is at most `2 · genus X` individual analytic
  checks (one smoothness + one FTC per basis element of
  `HolomorphicOneForm X`).

**Prior-state landings (still relevant)**:

* **`lieAddGroup_quotient_of_zlattice`** (chip 2) — unconditional
  `LieAddGroup 𝓘(ℂ, Fin g → ℂ) ω ((Fin g → ℂ) ⧸ L)` instance for any
  discrete full-rank ℤ-lattice `L`. Discharges OPEN.md item 13's
  content on the lattice-quotient construction.
* **`PeriodLatticeOfRankTwoG.lieAddGroupHypothesis_holds`** (chip 3) —
  the **third and final** named-hypothesis discharge on the
  `PeriodLatticeOfRankTwoG` bundle, sister to
  `compactSpaceHypothesis_holds` (item 11) and
  `chartedSpaceHypothesis_holds` (items 5 + 12). Items 4, 5, 10, 11,
  12, 13 on `JacobianOfLattice X data` are now **all unconditional**
  once `[DiscreteTopology] [IsZLattice ℝ]` instance arguments are
  supplied.
* **`quotientLinearMap_contMDiff`** (chip 4) — building block for
  items 18, 21: ℂ-linear maps descended to lattice quotients are
  ContMDiff. Discharges the smoothness side of analytic-Jacobian-level
  pushforward and pullback unconditionally.
* **Named predicates `AbelJacobiSmoothness` (item 17) and
  `AbelJacobiInjective` (item 16)** + composite
  `JacobianAnalyticClosureBundle` packaging both — give Basic.lean a
  clean per-item handle, with discharge routes documented (C1 +
  FTC for 17, Abel's theorem for 16).

**Prior session** (2026-05-16 late night, +2,663 LOC across 32 new
chips for the **HolomorphicTraceExtension X item-(2) descent +
Hurwitz form arc** — see CHANGELOG):

* **ZZ24** chart-pullback-AnalyticAt-on-target lemma (chip 3d-21) —
  long-flagged owed in `AnalyticContinuationGlobalization.lean`, now
  unconditional in tree.
* **Manifold f-regularity at Hurwitz fibre points** (chip 3d-22) —
  discharged unconditionally modulo the standard small-disc continuity
  argument for chart-source containment.
* Complete pure-analytic + chart-pullback + manifold-level fibre
  enumeration foundation in tree for the trace 1-form's chart-coefficient
  extension across critical values.

Layered on prior 2026-05-16 arcs: RLSL-from-AGPC (+310), HolomorphicTrace
Extension day (+2,436), HolomorphicTraceExtension item-(2) algebraic
core (+1,501), and 2026-05-15 Hodge Forster scaffolding (+2,948) +
C3 structural-reduction + chain-rule arc (+2,280) + per-`t` trace
identity (+~975) + eventually-form composition (+~720) + global
integrand-trace integral identity (+~985). Build green as of
2026-05-16 HEAD post-3d-23.

**2026-05-15 evening — `RegularLevelSetLatticeClause` per-`t` trace identity.**
The arc closes the **algebraic** content of the per-`t` lattice clause
discharge by composing surjectivity-by-cardinality with cross-sheet
cotangent pullback identification. Six chips:

* `MeromorphicNonzeroFiberFinsetCard.lean` (~140 LOC) — bridges
  `(fiberFinset hv).card` to `degreeFiber f.toRiemannSphere`; constancy
  across regular values.
* `SourceFiberPathAmbientSurjOnAt.lean` (~210 LOC) — surjectivity of
  `(extend t)` at general `t`, image-eq-fiberFinset, `Set.BijOn`
  packaging.
* `CotangentPullbackAtCongr.lean` (~85 LOC) — cotangent pullback is
  germ-determined.
* `LocalSheetDataUnique.lean` (~140 LOC) — local right-inverse
  uniqueness; both two-sheet and general (sheet vs. arbitrary local
  right-inverse) versions.
* `CotangentPullbackSheetIdentification.lean` (~190 LOC) — cross-sheet
  cotangent pullback identification at a regular value.
* `SourceSheetSumEqTraceAt.lean` (~210 LOC) — headline per-`t`
  identity: `∑_{p ∈ sourceFiber} sheetCotPullback sheet_p.g (β(σ t)) ω
  = traceAt f hnc hβσt_reg ω`, parametrized over the sub-interval +
  lift-equality conditions (discharged downstream on uniform-δ).

**Remaining for `RegularLevelSetLatticeClause`:** σ-reparametrisation
(`s = σ t`, requires integrand-as-function-of-s continuity = `f_*ω`
smoothness), `f_*ω` smooth-on-`regularValueSet` packaging, and residue
theorem adaptation from `principalDivisorMap` to `f_*ω`'s residue
divisor on ℙ¹.

**2026-05-15 (later session) — `RegularLevelSetLatticeClause` arc, six
more chips landed (+~1,156 LOC, build at 8854 jobs).**

* `MeromorphicNonzeroFStarOmegaDef.lean` (137 LOC) — `fStarOmega f hnc om :
  (v : RiemannSphere) → CotangentSpace _ v` returning `traceAt` at regular
  values and `0` (junk) elsewhere; ℝ-linear in `om`.
* `ChainDifferenceCycle.lean` (76 LOC) — generalises `singleDiff_isCycle`:
  `boundary c₁ = boundary c₂ ⇒ c₁ - c₂ ∈ SmoothCycle`.
* `RegularLevelSetChainBoundaryAJ.lean` (154 LOC) — `regularLevelSetCycleWitness`
  packages `regularLevelSetChain f + principalDivisorAJChain (principalDivisorMap f)`
  as a `SmoothCycle` via boundary cancellation. **Note**: this gives
  `period(Z) ≡ -period(AJ) (mod lattice)`, NOT `period(Z) ∈ lattice` —
  the lattice clause still needs the residue input independently.
* `MeromorphicNonzeroFiberLocallyConst.lean` (411 LOC) — `localFiberLabelingNbhd`
  is an open nbhd of `v₀ ∈ regularValueSet` on which `p ↦ (fiberSheetAt p).g v`
  is a Finset bijection `fiberFinset hv₀ ≃ fiberFinset hv` (via cardinality
  + InjOn-from-disjoint-shrunk-sheets).
* `FStarOmegaLocalAt.lean` (151 LOC) — fixed-Finset rewrite of `fStarOmega`
  on the labelling nbhd: `fStarOmega om v = ∑_{p ∈ fiberFinset hv₀}
  cotangentPullbackAt sheet_p.g v om`. Composes `fiberSheetAt_g_image_eq_fiberFinset`
  (above) + `cotangentPullbackAt_localSheet_eq_at_target_sheet` (in tree).
* `IntegrateLevelSetChainSigmaReparam.lean` (227 LOC, **conditional**) —
  σ-reparametrisation `s = σ(t)` via `intervalIntegral.integral_deriv_smul_comp'`,
  conditional on a named hypothesis `IntegrandContinuousAlongBeta`
  (continuity of `s ↦ applyCotangent (traceAt … (β s) om) (mfderiv β s 1)`
  on `Icc 0 1`).

**Remaining for unconditional `RegularLevelSetLatticeClause`:**
1. **`IntegrandContinuousAlongBeta` discharge** — **CLOSED 2026-05-15**
   via `Manifold/IntegrandContinuousAlongBetaUnconditional.lean`'s
   `integrandContinuousAlongBeta_holds`. Build 8870 jobs, zero
   sorry/axiom. Discharge routes through the chart-coord-pair
   architecture (chips 9–12) + chain-rule per-sheet reduction
   (`SheetCotPullbackPairingContinuity.lean`) + fixed-Finset sum
   continuity at each `s₀ ∈ Icc 0 1` with `β s₀ ∈ regularValueSet`
   (`FStarOmegaPairingContinuity.lean`). Headline:
   ```
   theorem integrandContinuousAlongBeta_holds
       (f : MeromorphicNonzero X)
       (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
       (hβ_smooth : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) ∞ β)
       (hβ_reg : ∀ s ∈ Icc 0 1, β s ∈ f.regularValueSet)
       (om : SmoothOneForm 𝓘(ℝ,ℂ) X) :
       f.IntegrandContinuousAlongBeta hnc hβ_smooth hβ_reg om
   ```
   The sheet-side smoothness (`f-5`) is implicit in the chain-rule
   reduction: each per-sheet pairing factors through the smoothness
   of the local sheet inverse `sheet_p.g` realified to `𝓘(ℝ,ℂ) ∞` on
   an open nbhd of `β s₀` (via `exists_contMDiffOn_localSheet_g_near_basePoint`
   + `ContMDiffOn.complex_to_real_of_isOpen`).

   **2026-05-15 evening — 9-chip groundwork arc** (build 8863 jobs, zero
   sorry/axiom). Two API entry points now land in tree:
   * **Factor-decomposed** (chips 1–8, e.g.
     `Manifold/IntegrandContinuousAlongBetaPerSheetVel.lean`'s
     `integrandContinuousAlongBeta_of_per_sheet_univ_and_velocity`) —
     discharges `IntegrandContinuousAlongBeta` from a universal per-sheet
     `ContinuousOn` hypothesis on `(cotangentEquiv (sheetCotPullback p v om)
     : ℂ →L[ℝ] ℝ)` plus velocity `ContinuousOn`. **Architectural caveat**:
     this routes through *absolute-coord* `cotangentEquiv` which is NOT
     globally continuous for non-trivial cotangent bundles (chart-cocycle
     cancels only inside the pairing); discharge-friendly only for paths
     whose labelling nbhds and sheet images each fit within single charts
     of RS / X respectively (i.e. paths not crossing `∞`).
   * **Chart-coord-pair** (chip 9, `Manifold/ChartBetaVelocity.lean`'s
     `chartBetaVelocity` + `contMDiffAt_chartBetaVelocity`) — first
     primitive of the architecturally correct architecture (mirrors
     `SmoothPathIntegrability.continuous_integrand_at`).

     **2026-05-15 — chart-coord-pair architecture: SmoothOneForm
     pairing continuity (3 chips, ~351 LOC, build 8866):**
     * `ChartBetaVelocitySelfEval.lean` (`chartBetaVelocity_self`):
       at the anchor `s₀`, both cocycles collapse, giving
       `chartBetaVelocity I β s₀ s₀ = mfderiv β s₀ (1 : ℝ)`.
     * `ChartBetaPairingInvariance.lean`
       (`applyCotangent_eq_chart_pairing_beta`): for any cotangent
       `φ` at `β s` with `β s` in the chart source at `β s₀`, the
       pairing `applyCotangent φ (mfderiv β s 1)` equals the
       chart-coord pairing with `chartBetaVelocity I β s₀ s`.
       Stated for a *free* cotangent (not a SmoothOneForm), ready to
       compose with `traceAt` directly.
     * `PairingContinuityBeta.lean`
       (`continuousAt_pairing_smoothOneForm_beta`,
       `continuous_pairing_smoothOneForm_beta`): for any
       `om : SmoothOneForm I M`, the pairing
       `s ↦ applyCotangent (om (β s)) (mfderiv β s 1)` is
       `ContinuousAt s₀` (and hence `Continuous`).

     **Remaining blocker:** `chartFStarOmega` / `f-5` — section
     smoothness of `fStarOmega` on `regularValueSet` (or its
     `SmoothOneFormOn` upgrade). Once `f_*ω` is a `SmoothOneForm`
     (or `SmoothOneFormOn regularValueSet`), the
     `continuousAt_pairing_smoothOneForm_beta` lemma above directly
     discharges `IntegrandContinuousAlongBeta` for the trace-pairing
     along `β`.

2. **Residue theorem on 1-forms on `ℙ¹`** — adapts the in-tree
   `JacobianChallenge.residue_theorem` (function level) to
   meromorphic 1-forms. The chain-difference reduction in
   `RegularLevelSetChainBoundaryAJ.lean` does NOT bypass this: it
   gives `period(regularLevelSetChain) ≡ -period(AJ-chain) (mod lattice)`,
   and `period(AJ-chain) ∈ lattice` is the very `AbelGeneratorPeriodCondition`
   we're trying to discharge — circular reduction. The 1-form residue
   theorem is genuine new classical input (~1,500–2,500 LOC realistically).

**Lebesgue gluing is no longer required** — the lifted-point sheet
breakthrough (2026-05-15 late evening) gave a global integrand
identity at any `t ∈ Ioo 0 1` directly, bypassing Hurwitz
subdivision.

**2026-05-16 — `fStarOmegaOn` arc + `HolomorphicTraceExtension`
structural reduction (6 chips, ~974 LOC).** Pushes the regular-case
clause discharge one structural step further than the 2026-05-16
trace-vanishing route:

* `fStarOmegaOn` (`Manifold/FStarOmegaOn.lean`) — packages
  `f.fStarOmega hnc om` as a `SmoothOneFormOn 𝓘(ℝ, ℂ) RiemannSphere
  f.regularValueSet`. Smoothness on the open regular set is now
  **unconditional**, via four supporting chips:
  - `SheetCotangentPullbackContMDiffAt` — holomorphic per-sheet
    pullback section smoothness (local-sheet analogue of
    `HolomorphicEquiv.pullbackSection_contMDiffAt`).
  - `SheetCotPullbackContMDiffAtReal` — realified `𝓘(ℝ, ℂ) ⊤`
    counterpart (field-generic bridge identity at 𝕜 := ℝ); also
    ships `complex_to_real_omega`, a regularity-preserving variant
    of `ContMDiffRealification.complex_to_real`.
  - `FStarOmegaContMDiffAt` — pointwise `ContMDiffAt ⊤` at regular
    values via mathlib's `ContMDiffAt.sum_section` + the
    `FStarOmegaLocalAt` fixed-Finset rewrite.

* `HolomorphicTraceExtension`
  (`Manifold/TraceAtVanishesOnHolomorphicReduction.lean`) — the new
  named hypothesis: for every non-constant `f` and every
  `α : HolomorphicOneForm X`, ∃ `α' : HolomorphicOneForm RiemannSphere`
  whose realified components agree pointwise on `f.regularValueSet`
  with the realified trace of `α`. Discharged conditionally:
  `traceAtVanishesOnHolomorphic_of_extension` + composition with
  `regularLevelSetLatticeClause_of_traceVanishing` gives
  `regularLevelSetLatticeClause_of_holomorphicTraceExtension`. The
  unconditional `Subsingleton (HolomorphicOneForm RiemannSphere)`
  (`Manifold/RiemannSphereChartSCoeffOverlap.lean`) closes the
  vanishing side once the extension provides the global α'.

* `HolomorphicOneFormOn` (`Manifold/HolomorphicOneFormOn.lean`) —
  partial-domain holomorphic 1-form type (analogue of
  `SmoothOneFormOn` in `𝓘(ℂ, ℂ) ω`). Target type for the eventual
  on-regular-set holomorphic trace; sets up the next-stage chip arc
  (holomorphic-side parallel to `fStarOmegaOn`).

**Net state after 2026-05-16.** Regular-case lattice clause discharge
reduces to **one** named hypothesis (`HolomorphicTraceExtension X`).
Its construction needs:
  1. The **holomorphic** analogue of `fStarOmegaOn` — a
     `HolomorphicOneFormOn 𝓘(ℂ, ℂ) RiemannSphere f.regularValueSet`,
     built by mirroring sub-chips B/C in the `𝓘(ℂ, ℂ) ω` bundle.
     Sub-chip A already provides the per-sheet input; estimated
     ~300-500 LOC.
  2. **Extension across critical values** — n-th-root cancellation +
     Riemann removable singularity theorem on 1-forms on `ℙ¹`. This
     is the genuinely-new classical content not at the mathlib pin.
  3. **Realification compatibility** — pointwise
     `realComponent α' v = traceAt (realComponent α) v` on the
     regular set, gluing (1)+(2) to the realified
     `TraceAtVanishesOnHolomorphic` form.

Build (all 6 chips of this session): single-file
`LEAN_NUM_THREADS=1 lake env lean` clean, zero `sorry`, zero `axiom`.

**2026-05-16 (afternoon) — `fStarOmegaHolOn` arc: item (1) closed,
holomorphic-side parallel built (6 chips, 828 LOC).** Mirrors the
morning's `fStarOmegaOn` arc on the holomorphic `𝓘(ℂ, ℂ) ω` bundle:

* `HolomorphicCotangentPullbackAt` — pointwise holomorphic pullback
  primitive with ℂ-linearity in α + germ congruence in g.
* `MeromorphicNonzeroHolTraceAt` — `holTraceAt`, `holSheetCotPullback`,
  cross-sheet identification (parallel to
  `cotangentPullbackAt_localSheet_eq_at_target_sheet`).
* `MeromorphicNonzeroFStarOmegaHolDef` — total `fStarOmegaHol α v`
  with `if hv then holTraceAt else 0`, ℂ-linearity, apply lemmas.
* `FStarOmegaHolLocalAt` — fixed-Finset rewrite on labelling nbhd
  (mirror of the realified `fStarOmega_eq_sum_sheetCotPullback_at_v0`,
  reusing the bundle-independent `fiberSheetAt` machinery).
* `FStarOmegaHolContMDiffAt` — pointwise `ContMDiffAt ω` at every
  regular value (per-sheet from sub-chip A + `ContMDiffAt.sum_section`
  + `congr_of_eventuallyEq`).
* `FStarOmegaHolOn` — final `HolomorphicOneFormOn RiemannSphere
  f.regularValueSet` packaging.

**Item (1) is now CLOSED.** The on-regular-set holomorphic 1-form
`f.fStarOmegaHolOn hnc α` is built unconditionally.

**Remaining for `HolomorphicTraceExtension X`** (next-session chip
arcs):

* **Item (2) — Extension across critical values.** The genuinely-new
  classical content. Build `globalize : HolomorphicOneFormOn RS s →
  HolomorphicOneForm RS` under the conditions that `s = f.regularValueSet`
  is open-cofinite and the on-set form has the n-th-root cancellation
  behavior at each critical value. Mathematical content: n-th-root
  cancellation + Riemann removable singularity for 1-forms on `ℙ¹`.
  Not at mathlib pin; estimated 1500-2500 LOC.

  **2026-05-16 (night) update — algebraic foundation COMPLETE.** 11
  chips (~1501 LOC) landed in `JacobianChallenge/Manifold/`: bridge
  primitives (removable-singularity adapter, on-set `localCoeff` +
  chart-target `ContMDiffOn` with full cocycle, critical-value chart
  shrink) + n-th-root cancellation algebraic core (roots-of-unity
  orthogonality; **general-`k` `KthRootSubstitution` closing a named
  gap**; cyclic-sum symmetry + first-order vanishing +
  vanishing-to-order-`(k-1)`; bounded-trace bound
  `‖cyclicSum‖ ≤ C·‖ξ‖^(k-1)`; ω-invariance + full cyclic-group
  invariance of the analytic factor `q`). Remaining for item (2):
  (a) **descent** of `q` to an analytic function of `ξ^k` via
  `FormalMultilinearSeries` Taylor-subseries (~300-500 LOC); (b)
  **manifold/cotangent-bundle wiring** of the per-preimage trace
  cluster at critical values, applying the bound +
  removable-singularity adapter (~400-600 LOC). See CHANGELOG
  `2026-05-16 (night)` entry for the chip-by-chip breakdown.

* **Item (3) — Realification compatibility.** Reduces to the manifold
  derivative identity `(mfderiv 𝓘(ℂ, ℂ) g x).restrictScalars ℝ =
  mfderiv 𝓘(ℝ, ℂ) g x` for ℂ-smooth `g`. Path: lift through
  `HasMFDerivAt ↔ HasFDerivWithinAt` + the chart-pullback identity
  `HasFDerivAt.restrictScalars`. Mathlib provides
  `DifferentiableAt.fderiv_restrictScalars`; manifold bridging is
  in-tree work, estimated 200-400 LOC.

Net: once items (2) + (3) ship, `HolomorphicTraceExtension X` is
unconditional and `RegularLevelSetLatticeClause X α_basis h_bundle` is
unconditional. Item (1)'s sub-chips also unlock any future use of
`fStarOmegaHolOn` for non-RLSL purposes (residue theorem, Hodge
theory, period-pairing finite-dim arguments).

**2026-05-16 (late afternoon) — Realification compat: chips 1+2 of 3
shipped (289 LOC).** Per-summand realification compatibility for the
holomorphic cotangent pullback is now unconditional:

* `mfderiv_complex_to_real_apply` (`MFDerivComplexToRealApply.lean`,
  171 LOC) — **manifold-derivative apply-level realification**: for
  ℂ-differentiable `g`, `(mfderiv 𝓘(ℝ, ℂ) g x) w = (mfderiv 𝓘(ℂ, ℂ) g x) w`
  as elements of `ℂ`. The typed `.restrictScalars`-statement attempted
  on the prior commit was blocked by `Module ℂ (TangentSpace 𝓘(ℝ, ℂ) x)`
  synth failure. Workaround: apply-level statement +
  explicit-`@`-form wrappers around `DifferentiableAt.restrictScalars`
  / `HasFDerivAt.restrictScalars` to manually pass
  `IsScalarTower ℝ ℂ ℂ` (mathlib's discrimination tree doesn't try
  `IsScalarTower.right` in this position).

* `realPartCLM_holCotangentPullbackAt_apply` /
  `imagPartCLM_holCotangentPullbackAt_apply`
  (`HolCotangentPullbackRealification.lean`, 118 LOC) —
  **per-summand realification compatibility**: for ℂ-differentiable
  `g`, `(realPartCLM (holCotangentPullbackAt g y α)) w
  = Complex.re ((α.eval (g y)) ((mfderiv 𝓘(ℝ, ℂ) g y) w))`
  (and analogously for `imagPartCLM`). Reduces to chip 1.

**2026-05-16 (evening) — Realification compat chip 3 shipped (345 LOC).**
Trace-level real / imag realification compatibility:

* `realPartCLM_fStarOmegaHol_apply` /
  `imagPartCLM_fStarOmegaHol_apply` (`FStarOmegaHolRealification.lean`,
  345 LOC) — at every regular value `v` and tangent vector `w : ℂ`:

      (realPartCLM (f.fStarOmegaHol hnc α v)) w
        = SmoothPath.applyCotangent (f.fStarOmega hnc (realComponent α) v) w

  (and analogously for `imagPartCLM` / `imagComponent`). Sums chip 2
  over the fiber via a generalised inner lemma + `Finset.induction_on`
  (working around the `map_sum realPartCLM` pattern-match failure that
  blocked the direct approach).

**Item (3) is now CLOSED.** Both real and imaginary realification
compatibilities hold unconditionally on `f.regularValueSet`.

**Remaining for `HolomorphicTraceExtension X`:** only item (2) —
extension across critical values (n-th-root cancellation + Riemann
removable singularity for 1-forms on `ℙ¹`). Genuinely-new classical
content not at the mathlib pin.

**2026-05-15 evening — Integrand-trace identity in full eventually
form (5 additional chips, ~720 LOC).** Lifts the algebraic per-`t`
trace identity to integrand-level + fully eventually form near `t = 0`:

```
∀ᶠ t in 𝓝[Ioc 0 1] 0, ∃ hβσt_reg : β(σ t) ∈ regularValueSet,
  ∑ p ∈ sourceFiber, (sourceFiberPath p).integrand om t
    = applyCotangent (traceAt f hnc hβσt_reg om) (β'(σ t) σ'(t))
```

Five chips:

* `PerFiberSheetEventually.lean` — sub-interval V-membership +
  lift-equality eventually.
* `SourceSheetSumEqTraceAtEventually.lean` — per-`t` trace identity
  in eventually form.
* `LevelSetIntegrandEqTraceAtApply.lean` — integrand-level per-`t`
  identity (chain rule + trace).
* `SheetGRealSmoothEventually.lean` — realified sheet.g smoothness
  eventually.
* `PerFiberChainRuleEventually.lean` — per-fibre chain rule promoted
  to filter form.
* `LevelSetIntegrandEqTraceAtApplyEventually.lean` — full eventually
  composition headline.

This is the integrand of `(levelSetChain f β).integrate ω` equating
to the integrand of the line integral of `f_*ω` along β (modulo
σ-reparam). Build at **8836 jobs**.

**2026-05-15 late evening — Lifted-point local identification +
global integrand-trace integral identity (8 chips, ~1,330 LOC).**
Architectural breakthrough: the **lifted-point sheet** `sheet_q` at
`q := extend t₀ p` automatically satisfies the sub-interval
condition (`sheet_q.V ∋ β(σ t₀)` by construction), so the chain
rule based at `sheet_q` works at **every** `t₀` — bypassing
Hurwitz subdivision entirely. Eight chips:

* `SourceFiberPathExtendEqSheetGAtT.lean` (~218 LOC) — local
  identification at general `t₀` via lifted-point sheet.
* `SourceFiberPathIntegrandLocalSheetGAtT.lean` (~127 LOC) — per-
  fibre integrand at general `t₀` via lifted-point sheet (composes
  with `integrand_eq_of_ambient_eqOn_Icc_fun`).
* `SourceFiberPathIntegrandChainAtT.lean` (~238 LOC) — chain-rule-
  unfolded per-fibre integrand at general `t₀` via two
  `mfderiv_comp_apply` applications + `applyCotangent_cotangentPullbackAt`.
* `GlobalIntegrandTraceIdentity.lean` (~165 LOC) — global per-`t`
  identity at any `t ∈ Ioo 0 1`:
  ```
  ∑ p, (sourceFiberPath p).integrand om t
    = applyCotangent (traceAt f hnc hβσt_reg om)
        (mfderiv β (σ t) (mfderiv σ t 1))
  ```
  No sub-interval restriction. Composes per-fibre chain-rule + Finset
  bijection (sourceFiber ↔ fiberFinset(β(σ t))) +
  `applyCotangent_traceAt`.
* `IntegrateLevelSetChainEqTraceAt.lean` (~125 LOC) — integrated
  identity: `SmoothChain.integrate (levelSetChain f β) om = ∫ t in
  0..1, applyCotangent (traceAt … (β(σ t)) om) (mfderiv β (σ t)
  (mfderiv σ t 1))`. Composes via `integrate_levelSetChain` (chain →
  ∑_p) + `intervalIntegral.integral_finset_sum` (swap ∑/∫) +
  `intervalIntegral.integral_congr_ae` (boundary `{1}` measure-zero)
  + global per-`t` identity.
* `IntegrandSigmaSmulFactor.lean` (~162 LOC) — factors out
  `derivσ(t)`:
  ```
  SmoothChain.integrate (levelSetChain f β) om
    = ∫ t in 0..1, derivσ(t) *
        applyCotangent (traceAt … (β(σ t)) om) (mfderiv β (σ t) 1)
  ```
  Via `mfderiv_eq_fderiv` + ℝ-linearity of CLM and `cotangentEquiv`.
  This is exactly the shape required by
  `intervalIntegral.integral_comp_mul_deriv` for the σ-reparam
  conversion to `∫ s in 0..1, applyCotangent (traceAt … (β s) om)
  (mfderiv β s 1) ds`.

Build green at **8842 jobs**. Zero `sorry`, zero `axiom`.

**2026-05-16 evening — C3 structural reduction + chain-rule pathway 1-3.**
The arc delivers a two-tier reduction of `AbelHypothesis B`:

*Tier 1.* Two named classical inputs:

* `RegularLevelSetLatticeClause X α h` — period vector of
  `regularLevelSetChain f hnc h0 h∞` ∈ `periodLatticeImage`. The
  substantive analytic core (residue theorem for `f_*ω` on `ℙ¹`).
* `AbelLatticeWitnessCriticalCase X α h` — witness chain for `f` with
  `0` or `∞` critical (Möbius substitution residual).

Headlines:
`AbelJacobiInput.forall_abelHypothesis_of_split hRL hCR : ∀ B, AbelHypothesis B`,
`dischargedGenerators_eq B B' : B.dischargedGenerators = B'.dischargedGenerators`.

*Tier 2.* Structural per-`t` identity for the level-set chain integral
on `Ioo 0 δ`:
`∑_p integrand(sourceFiberPath p) ω t = applyCotangent (∑_p cotangentPullbackAt sheet_p.g (β(σ t)) ω) (β'(σ t) σ'(t))`.

The **injection half** of the sourceFiber ↔ `f⁻¹(β(σ t))` bijection is
fully proved (`sourceFiberPath_toPath_extend_injOn_at` at arbitrary
`t ∈ Icc 0 1`, plus `Set.InjOn`-form and image ⊆ fiberFinset). The
surjectivity half (cardinality argument via
`degreeFiber_eq_card_of_regular_witness` or time-reversal at general
`t`) remains.

**2026-05-15 — Hodge finite-dim Forster scaffolding.** Sixteen chips,
+2,948 LOC. The full Forster/Montel/Riesz proof of
`HolomorphicOneFormFiniteDim X` is reduced to **two remaining steps**:
(i) seminorm convergence (inner-disk uniform → outer-disk seminorm via
the multi-chart density bound); (ii) `NormedAddCommGroup` wrapper +
separating + Riesz `FiniteDimensional.of_isCompact_closedBall₀`.
Per-chip breakdown:

* `localCoeff` API (chart-coord coefficient of a holomorphic 1-form,
  +340) — `HolomorphicOneFormChartCoeff.lean`.
* `localCoeff_contMDiffOn` on chart target via cocycle (+338) —
  `HolomorphicOneFormChartCoeffOnTarget.lean`.
* `DiskChartCover X` (finite chart cover with disk hierarchy on
  compact `X`, +201) — `CompactDiskChartCover.lean`.
* `localCoeffMax` per-chart sup (+252) — `DiskChartCoverSeminorm.lean`.
* `seminormVal` aggregation (+119) — `DiskChartCoverSeminormAggregate.lean`.
* Cauchy first-derivative estimate (+204) —
  `DiskChartCoverCauchyEstimate.lean`.
* Lipschitz bound via MVT (+154) — `DiskChartCoverLipschitz.lean`.
* Arzelà-Ascoli per chart (+188) — `DiskChartCoverArzela.lean`.
* Diagonal subsequence across base points (+114) —
  `DiskChartCoverDiagonal.lean`.
* Scalar pointwise limit at any `y ∈ X` (+113) —
  `DiskChartCoverPointwiseLimit.lean`.
* CLM-level pointwise limit (+192) — `DiskChartCoverCLMLimit.lean`.
* Analyticity of chart limit on inner ball via
  `TendstoLocallyUniformlyOn.differentiableOn` (+173) —
  `DiskChartCoverLimitAnalytic.lean`.
* `limitSectionToFun` via `Classical.choose` (+79) —
  `DiskChartCoverLimitSection.lean`.
* Chart-frame CLM identification of the limit (+188) —
  `DiskChartCoverLimitSmooth.lean`.
* Composed `smulRight 1 ∘ bcfExtend ∘ chart-x` ContMDiffAt
  (+109) — `DiskChartCoverLimitContMDiff.lean`.
* End-to-end packaging as `HolomorphicOneForm X` (+184) —
  `DiskChartCoverLimitPackage.lean`. Headline:
  `DiskChartCover.limitHolomorphicOneForm cover om_n h_diag :
  HolomorphicOneForm X` — given a `seminormVal`-bounded
  sequence + the diagonal subsequence convergence at every base
  point, packages the pointwise CLM limit as a smooth section.

**Net effect.** The full Forster/Montel/Riesz proof of
`HolomorphicOneFormFiniteDim X` is reduced to **two remaining steps**:
(i) seminorm convergence — upgrade the per-inner-disk uniform
convergence to outer-disk seminorm convergence (the standard fix uses
the multi-chart density bound via the cotangent transition's
continuity); (ii) `NormedAddCommGroup` wrapper + separating (cotangent
coord-change invertibility on the fibre) + Riesz application
(`FiniteDimensional.of_isCompact_closedBall₀`).

**Prior 2026-05-16 wave** (10 chips, +1,573 LOC; cumulative session
note retained for context):

* `h_AJ_boundary` discharge (+125) — `PrincipalDivisorAJChainBoundary.lean`.
* Regular β: 0→∞ existence on ℙ¹ (+431) — `MeromorphicNonzeroRegularPath.lean`.
* Concrete regular level-set chain + boundary identification (+146)
  — `MeromorphicNonzeroConcreteLevelSetChain.lean`.
* Real-model RS manifold + open-set realification (+96)
  — `RiemannSphereRealManifold.lean`.
* Pointwise cotangent pullback primitive (+94) — `CotangentPullbackAt.lean`.
* Pointwise trace `f_*ω` at a regular value (+117)
  — `MeromorphicNonzeroTraceAt.lean`.
* `SmoothOneFormOn` partial-section type + `restrictOnSet` (+88)
  — `SmoothOneFormOn.lean`.
* Scalar evaluation of cotangent pullback and trace (+123)
  — `CotangentPullbackAtApply.lean`.
* `ContinuousOn` variant of `path_lift_eqOn_Icc` (+131)
  — `MeromorphicNonzeroPathLiftUniqueOnContinuousOn.lean`.
* Local identification of `sourceFiberPath` with `sheet.g ∘ β ∘ σ`
  (+222) — `MeromorphicNonzeroSourceFiberPathSheetEq.lean`.

**13 additional chips (2026-05-16 later) — `HolomorphicOneFormSubsingletonOfSimplyConnected` arc** (+1,510 LOC, 7 new files):

* Continuous homotopy of smooth paths from `SimplyConnectedSpace` (+111)
  — `SmoothPathHomotopyFromSimplyConnected.lean`.
* `chartCoeffAt` for `HolomorphicOneForm X` + pointwise linearity (+100)
  — `HolomorphicOneFormChartCoeff.lean`.
* **Unconditional Liouville for `ContMDiff ω F : X → ℂ`** via exp trick (+373)
  — `Topology/LiouvilleForContMDiffOmega.lean`.
* **Subsingleton from primitive existence + bridge to named predicate**
  + full-arc `S2ImpliesGenus0_of_primitiveExistence` (+268)
  — `Topology/SubsingletonFromPrimitiveExistence.lean`.
* `complexChainPeriod` form-side algebra: linearity / smul_real /
  smul_complex / reverse / concat / `→ₗ[ℂ]` / bilinear bundle (+244)
  — `ComplexChainPeriodFormLinear.lean`.
* `chartLocalPrimitive` data + basepoint identity `F(x₀) = 0` (+236)
  — `ChartLocalPrimitive.lean`.
* E foundation: joint continuity of `bumpedSegment` /
  `chart.symm ∘ bumpedSegment` / `chartCoordVelocity σ'(t)·(z-z₀)` (+178)
  — `ChartLocalPrimitiveSmoothness.lean`.

Cumulative delta vs. 2026-05-14 snapshot (86,894 LOC / 416 files):
**+17,134 LOC / +104 files** (Hodge Forster +2,948 / 16 files plus
the 2026-05-16-evening C3 reduction +2,280 / 13 files on top of the
prior +13,400 / 82 files baseline). Build green at 8808 jobs (last
verified at HEAD `59a72b1` pre-Hodge-rebase), zero `sorry`, zero
`axiom`. See `CHANGELOG.md` for the per-branch history.

**Remaining LOC to 24/24** (full breakdown in `CLOSURE_MAP.md` §F):
**~11,000–21,000 LOC** for the realistic **23/24** target (deferring
uniformization at genus 0 as a named classical hypothesis).
Highest-leverage chunk: PL-4 discharge (steps 1–3 of the priority order)
flips 6 items (4, 5, 10, 11, 12, 13) for ~3,300–7,600 LOC.
Closing item 14 strictly requires uniformization in-tree (multi-month).

Do not regenerate this list from context — query this file. Update this file
whenever a status changes.

## Definitions (data) — Basic.lean items 1–9 in OPEN.md numbering

| # | Item | Status | Notes |
|---|---|---|---|
| 1 | `genus X : ℕ` | **STUB** | Body: `JacobianChallenge.genus X = Module.finrank ℂ (HolomorphicOneForm X)`. Returns `0` by convention if `HolomorphicOneForm X` is infinite-dimensional, and finite-dimensionality on compact connected `X` is **not yet proved** (Hodge theory). The anti-hack pair (item 14, `genus_eq_zero_iff_homeo`) is **OPEN**. |
| 2 | `Jacobian X : Type u` | **STRICT-CLOSED** *(post-ZZ256, 2026-05-12)* | Body: `Jacobian X := Pic0 X` with `Pic0 X = Div0 X ⧸ (PrincDiv X).addSubgroupOf (Div0 X)` and **`PrincDiv X := PrincDivHonestCandidate X`** (honest principal-divisor subgroup, in `Divisor/PrincipalDivisorRange.lean`). |
| 3 | `instance : AddCommGroup (Jacobian X)` | **STRICT-CLOSED** *(post-ZZ256)* | Inherits from the honest `Pic0` quotient. |
| 4 | `instance : TopologicalSpace (Jacobian X)` | **STUB** | Discrete (`⊥`). The challenge wants the complex-manifold topology (item 5 `ChartedSpace`); discrete is not it. |
| 5 | `instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` | **OPEN** | Requires the analytic-Jacobian construction (period-lattice). The parallel `AnalyticTorus X` carries an honest `ChartedSpace` instance (`Manifold/PeriodLattice.lean`), but is not wired into `Jacobian`. |
| 6 | `Jacobian.ofCurve : X → Jacobian X` | **STRICT-CLOSED** *(post-ZZ256)* | Body: `Q ↦ [δQ − δP]` in honest `Pic⁰`. |
| 7 | `Jacobian.pushforward f hf` | **STRICT-CLOSED** *(post-ZZ256)* | Body: `JacobianChallenge.Jacobian.pushforward hf` in `JacobianPushforward.lean`. Descent via P1.4 (`PrincDivHonestCandidate_addSubgroupOf_Div0_le_comap_divPushforward`) on the non-constant branch + degree-zero trivialization on the constant branch. |
| 8 | `Jacobian.pullback f hf` | **STRICT-CLOSED** *(post-ZZ256)* | Body: `Jacobian.pullbackHonest_of_rsum`, which dispatches to either `0` (constant `f`) or `Jacobian.pullbackWeighted` with `e := manifoldRamificationIndex f` and `N := degreeFiber f hf`. The `Pic0.pullbackWeighted` descent obligation is discharged unconditionally by `Pic0.divPullbackWeighted_descent_of_smooth` (`JacobianPullback.lean`) — sister chip to P1.4 in the contravariant direction. |
| 9 | `ContMDiff.degree f hf : ℕ` | **STRICT-CLOSED** *(post-zzITEM9, 2026-05-12)* | Body: `JacobianChallenge.ContMDiff.degreeFiber f hf`. Well-definedness across regular witnesses is `JacobianChallenge.degreeFiber_eq_card_of_regular_witness` in `Manifold/DegreeWellDefined.lean`, composing `Manifold/HPkgUnconditional.lean` (`h_pkg_holds_unconditional`, from chip A `LocalSheetData.ofRegularValueWitnessReg` + chip B `critical_value_set_finite` + RVE deriv-bridge + HLcUnconditional) through `fibre_card_well_defined_at_regular_holds_of_h_pkg`. |

## Theorems (Prop) — Basic.lean items 10–24 in OPEN.md numbering

| # | Item | Status | Notes |
|---|---|---|---|
| 10 | `instance : T2Space (Jacobian X)` | **STUB** | Discrete ⇒ T2 is honest, but the topology itself is wrong (item 4). |
| 11 | `instance : CompactSpace (Jacobian X)` | **OPEN** | `sorry` in `Basic.lean`. Compactness needs the analytic-Jacobian quotient topology (period-lattice), Phase 2. |
| 12 | `instance : IsManifold ... ω (Jacobian X)` | **OPEN** | `sorry`. Requires analytic-Jacobian construction. `AnalyticTorus X` has an honest `IsManifold` instance modulo `Λ = ⊥`; not wired into `Jacobian`. |
| 13 | `instance : LieAddGroup ... ω (Jacobian X)` | **OPEN** | `sorry`. Requires item 12 plus smoothness of group ops. |
| 14 | `genus_eq_zero_iff_homeo` (anti-hack vs. `genus := 0`) | **OPEN** | `sorry`. Architecturally closed via `genus_eq_zero_iff_homeo_from_all_conditionals` in [`Topology/Item14FinalComposition.lean`](JacobianChallenge/Topology/Item14FinalComposition.lean). Open content factors onto the four named classical inputs listed at the top of this file. |
| 15 | `ofCurve_self : ofCurve P P = 0` | **STRICT-CLOSED** *(post-ZZ256)* | Real proof reducing to `[δP − δP] = 0` in honest `Pic⁰`. |
| 16 | `ofCurve_inj` (anti-hack vs. `Jacobian := PUnit`) | **OPEN** *(post-ZZ256 regression)* | The previous STUB proof exploited `PrincDiv X = ⊥` to make the quotient faithful. Under honest `PrincDiv` that argument fails; `Jacobian.lean`'s `ofCurve_inj` is now `sorry` (Basic.lean transitively). Genuinely requires Abel–Jacobi (Phase 2). |
| 17 | `Jacobian.ofCurve_contMDiff` | **OPEN** | `sorry`. Requires item 5 (`ChartedSpace`) plus a real `ofCurve`. |
| 18 | `Jacobian.pushforward_contMDiff` | **OPEN** | `sorry`. Requires item 5 plus a real `pushforward`. |
| 19 | `pushforward_id_apply` | **STRICT-CLOSED** *(post-ZZ256)* | Real proof via `Pic0.pushforward_id` (in `JacobianPushforward.lean`) ↦ `Div.singletonMap_id_apply`. |
| 20 | `pushforward_comp_apply` | **STRICT-CLOSED** *(post-ZZ256)* | Real proof via `Pic0.pushforward_comp` (in `JacobianPushforward.lean`) ↦ `Div.singletonMap_comp_apply`. |
| 21 | `Jacobian.pullback_contMDiff` | **OPEN** | `sorry`. Requires item 5 plus a real `pullback`. |
| 22 | `pullback_id_apply` | **STRICT-CLOSED** *(post-ZZ256)* | Body: `JacobianChallenge.Jacobian.pullbackHonest_of_rsum_id _ P` — case-splits on `IsConstantMap (id : X → X)`, with the non-constant branch reducing to `divPullbackWeighted_id_apply` (single-fibre `id ⁻¹' {y} = {y}`, weight 1 everywhere). |
| 23 | `pullback_comp_apply` | **STRICT-CLOSED** *(post-ZZ256)* | Body: `pullbackHonest_of_rsum_comp` — the both-non-constant case delegates to `Div.fiberSumWeighted_comp_apply` with multiplicative ramification weights `manifoldRamificationIndex_comp_unconditional`. |
| 24 | `pushforward_pullback : pushforward f (pullback f P) = degree f • P` | **STRICT-CLOSED** *(post-ZZ256)* | Body: `pushforward_pullbackHonest_of_rsum` — case-splits on `IsConstantMap f`. Constant case: both sides zero. Non-constant: reduces to `Pic0.pushforward_pullbackWeighted` (in `JacobianPullback.lean`, using the new honest `Pic0.pushforward (hf)` signature). |

## Architectural issue: RR-thread linear system (resolved, merged to main 2026-05-14)

The legacy `linearSystemDeltaP p : Submodule ℂ (X → ℂ)` is defined over
*pointwise* functions `X → ℂ`. This admits "essentially-zero" elements
(e.g. `g(p_0) = 100, g(y) = 0 otherwise`) that satisfy `IsBoundedByDeltaP
p g` and are not in `span ℂ {1}` (non-constant) yet have
`germLimitLift g ≡ 0` — making the canonicalised lift unusable.
Consequences:

1. **`finrank ℂ (linearSystemDeltaP p) = ∞` trivially**, by the family of
   "blip-at-`p_0`" functions. So `RR_DimGE2_GenusZero X := ∃ p, 2 ≤
   finrank ℂ (linearSystemDeltaP p)` is vacuously true with no
   Riemann-Roch content.
2. **Inputs #2, #3, #5, #6** of the six-input split
   (`riemannRochGenusZero_from_six_inputs` in
   [`Topology/RRGenusZeroFinalComposition.lean`](JacobianChallenge/Topology/RRGenusZeroFinalComposition.lean))
   — `LiftMMeromorphicOn`, `LiftNonvanishingGerm`, `LiftOrderPreserved`,
   `LiftNotConstant` — are **false as stated** against the blip
   counterexample.
3. **Input #4** (`LiftRegularContinuousAt`, reduced to germ-coherence
   hypotheses via zz380 + zz381) is the only sub-input where the
   reduction stands cleanly; even so, the germ-coherence hypotheses
   themselves are about elements of the broken `linearSystemDeltaP`.

**Resolution (`feat/linear-system-divisor`, merged to main 2026-05-14).** The germ-field
ambient called for above has been built. `MeromorphicFunctionField X`
(in `Manifold/MeromorphicFunctionField.lean`) provides the ℂ-algebra
of meromorphic-function germs, and `linearSystemDivisor D` (in
`Topology/LinearSystemDivisor.lean`) is the honest `L(D)` Submodule
for any divisor `D : Div X`, with `linearSystemGermDeltaP p` as the
`D = Div.single p` specialisation. The full chain — existence side
via `HolomorphicEquiv X RiemannSphere` + finite-dim transport — is
built. After the 2026-05-14 A1 + A2 discharges, the genus-0 RR
`dim_ℂ L(δp) ≥ 2` content on the germ field reduces to **one**
remaining named classical input:

1. **Uniformization at genus 0**:
   `genus X = 0 → Nonempty (HolomorphicEquiv X RiemannSphere)`.

Both of the RS-side inputs are now **discharged unconditionally**:

* `LinearSystemAtInftyRS_BoundedBySimplePoleSpan` (A1, 2026-05-14):
  via `Analysis/PolynomialLiouville.lean` +
  `Topology/LinearSystemAtInftyRSDischarge.lean` (~870 LOC).
* `ExistsMobiusToInftyRS` (A2, 2026-05-14): via
  `Manifold/RiemannSphereAntipodeSmooth.lean` (~255 LOC) +
  `Manifold/RiemannSphereTranslate.lean` (~322 LOC) +
  `Manifold/MobiusTransitivityRS.lean` (~80 LOC).

Headline composition lives in
`Topology/LinearSystemGermDeltaPFiniteDimRSUnconditional.lean`:

* `linearSystemGermDeltaPFiniteDim_RiemannSphere_unconditional :
  LinearSystemGermDeltaPFiniteDim RiemannSphere` —
  **unconditional**.
* `rr_DimGE2_GenusZero_Germ_of_uniformization_unconditional_RSFiniteDim`
  — for any compact connected complex 1-manifold `X`, RR dim ≥ 2 on
  the germ field reduces to genus-conditional uniformization alone.

See `CHANGELOG.md` for the per-file map.

## Smooth-path-connectedness sub-arc (C1, **CLOSED** 2026-05-15)

The `AbelJacobiInput α h` named-hypothesis bundle
(`Manifold/AbelJacobiPoint.lean`) is the C1 input of CLOSURE_MAP §F.3.
Its existence on a compact connected complex 1-manifold is classical
("smooth path-connectedness + a chosen base point"). The full chain
is now **closed unconditionally** for any preconnected complex
1-manifold (which includes every compact connected complex 1-manifold).
Five primitives ship:

1. `SmoothPathConnected I X : Prop` (`Manifold/SmoothPathConnected.lean`,
   2026-05-14) — the classical predicate "every two points of `X`
   joined by a smooth path", with `AbelJacobiInput.ofSmoothPathConnected`
   / `nonempty_of_smoothPathConnected` reducing `AbelJacobiInput α h`
   existence to `SmoothPathConnected 𝓘(ℝ, ℂ) X + Nonempty X`. This is
   the named-hypothesis layer for the sub-arc.

2. `SmoothPath.linearInChart` (`Manifold/SmoothPathLinearInChart.lean`,
   2026-05-14) — the analytic affine constructor: given a chart
   `φ ∈ atlas ℂ X`, two points in `φ.source`, and the hypothesis that
   the entire chart-coordinate line through their images lies in
   `φ.target`, produce a `SmoothPath 𝓘(ℝ, ℂ) X` between them. Now
   downcast at C^∞ via `ContMDiffAt.of_le` since the structure was
   relaxed to C^∞.

3. `SmoothPath.linearInChartSegment` (`Manifold/SmoothPathLinearInChart.lean`,
   2026-05-15) — the C^∞ constructor with **segment-in-target**
   hypothesis. Strict weakening of `linearInChart`'s line-in-target,
   built on `bumpedSegment a b t = (1 - σ t) • a + σ t • b` where
   `σ = Real.smoothTransition`.

4. `SmoothPath.concat`
   (`Manifold/SmoothPathConcat.lean`, 2026-05-15) — binary
   concatenation of two smooth paths sharing an endpoint, via
   bump-flatten reparameterisations
   `concatRepLeft t = σ(4(t - 1/8))` and
   `concatRepRight t = σ(4(t - 5/8))` that make both halves
   identically equal to the junction point on `(3/8, 5/8)`. C^∞
   globally; would be obstructed at ω by analytic germ-determination.

5. `exists_smooth_path_connected_chart_nbhd p`
   (`Manifold/SmoothPathLocalConvex.lean`, 2026-05-15) — local
   smooth-path-connected neighborhood at every point, via the
   chart-restricted-to-Euclidean-ball construction
   `U := φ.source ∩ φ ⁻¹' Metric.ball z r` (where `z = φ p` and
   `r > 0` with `ball z r ⊆ φ.target`). Convexity of the ball plus
   `SmoothPath.linearInChartSegment` gives the smooth-path-connected
   property of `U`.

**ω-level caveat resolved (2026-05-15).** The `SmoothPath` structure
was refactored from `ContMDiff ⊤` (= ω = analytic) to `ContMDiff ∞`
(= C^∞) — the docstring intent. Concatenation and segment-in-chart
reparameterisations are now both directly available; analytic
germ-determination no longer obstructs them.

**Headlines (2026-05-15).**

* `smoothPathConnected_RiemannSphere : SmoothPathConnected 𝓘(ℝ, ℂ)
   RiemannSphere`
  (`Manifold/SmoothPathConnectedRiemannSphere.lean`) — first
  end-to-end discharge on a concrete compact connected complex
  1-manifold. Case-splits on the two-chart cover with
  `SmoothPath.concat` for the `{∞, (0 : ℂ)}` edge case.

* `smoothPathConnected_of_preconnected [PreconnectedSpace X] :
   SmoothPathConnected 𝓘(ℝ, ℂ) X`
  (`Manifold/SmoothPathLocalConvex.lean`) — **the general
  discharge**. The standard open-closed argument applied to the
  reachable set `{q | ∃ γ, γ.src = p ∧ γ.tgt = q}`, which is open
  by `concat` with the local lemma, and closed by the symmetric
  argument on its complement. A nonempty clopen set in a
  preconnected space is the whole space (`IsClopen.eq_univ`); `p`
  is in its own reachable set via `SmoothPath.const`.

**Net.** Via `AbelJacobiInput.nonempty_of_smoothPathConnected`,
`Nonempty (AbelJacobiInput α h)` is now **unconditional on any
nonempty preconnected complex 1-manifold**. The C1 input of
CLOSURE_MAP §F.3 is closed.

## C3 + C4 sub-arc progress (2026-05-14, 12 chips; merged to main)

`AbelHypothesis B` (Abel forward, `Manifold/AbelJacobiPic0.lean`)
and `JacobiInversion B hAbel` (`Manifold/AbelJacobiIso.lean`) are
the C3 + C4 named hypotheses. Together they give `Pic⁰ X ≃+
AnalyticJacobian X` (`abelJacobiEquiv`) — the gate for items 4, 5,
10, 11, 12, 13.

Twelve chips landed 2026-05-14 reducing C3 to a single sharp
atomic statement, closing C4 at genus 0, and unconditionally
discharging `Pic⁰(ℙ¹) = 0` to make the Abel-Jacobi iso on the
Riemann sphere axiom-free. All on `main` (merged from
`feat/linear-system-divisor`).

First half (named-hypothesis reductions, 7 chips):

**C3 (1) genus-0 corner** (`Manifold/AbelHypothesisGenusZero.lean`).
At `genus X = 0`, `AnalyticJacobian` is subsingleton, so
`AbelHypothesis B` is trivially true.

**C3 (2) chain-level reduction**
(`Manifold/AbelHypothesisFromPeriodCondition.lean`).
* `principalDivisorAJChain B D` — explicit AJ chain for `D : Div X`,
  `Σ D(x) • single (B.pathFromBase x)`.
* `abelJacobiChain_principalDivisorAJChain_eq_abelJacobiDivHom` —
  the diagram identity.
* `AbelChainPeriodCondition B : Prop` — for every principal divisor
  `D`, the period vector of its AJ chain lies in `periodLatticeImage`.
* `abelHypothesis_of_abelChainPeriodCondition` — the reduction.

**C3 (3) algebra layer** (same file).
* `principalDivisorAJChain_add` — chain is additive in `D`.
* `principalDivisorAJChainHom : Div X →+ SmoothChain 𝓘(ℝ, ℂ) X` —
  bundled `AddMonoidHom`.
* `complexChainPeriodVector_principalDivisorAJChain_{add,neg}_mem` —
  closure of "period vector ∈ periodLatticeImage" under + and -.

**C3 (4) per-generator reduction** (same file).
* `AbelGeneratorPeriodCondition B : Prop` — for each `f :
  MeromorphicNonzero X`, period vector of AJ chain of `div(f)`
  ∈ `periodLatticeImage`. **The sharpest atomic form of Abel
  forward — one meromorphic function at a time.**
* `abelChainPeriodCondition_of_abelGeneratorPeriodCondition` —
  closure induction on `PrincDiv X = AddSubgroup.closure (Set.range
  principalDivisorMap)`.
* `abelHypothesis_of_abelGeneratorPeriodCondition` — composite.

**C4 (genus-0)** (`Manifold/JacobiInversionGenusZero.lean`).
* `jacobiInversion_of_genus_zero_and_subsingleton_pic0` — builds
  `JacobiInversion B hAbel` from `genus X = 0` + `Subsingleton (Pic0
  X)`. Surjectivity automatic (codomain subsingleton); injectivity
  reduces to source subsingleton.
* `abelJacobiEquiv_of_genus_zero` — the full Abel-Jacobi iso `Pic0
  X ≃+ AnalyticJacobian` at genus 0, given `Subsingleton (Pic0 X)`.

Second half (RS-side unconditional discharge, 5 chips):

**RS principal-divisor generators (3 chips):**
* `mnRSSimplePole` (`Manifold/MeromorphicNonzeroRSSimplePole.lean`,
  ~110 LOC) — `MeromorphicNonzero RS` packaging of the function
  `some z ↦ z`, with principal divisor `δ_{some 0} - δ_∞`.
* `mnRSInversion` (`Manifold/MeromorphicNonzeroRSInversion.lean`,
  ~200 LOC) — packaging of `z ↦ z⁻¹`, with principal divisor
  `δ_∞ - δ_{some 0}`.
* `mnRSAffineFactor a` (`Manifold/MeromorphicNonzeroRSAffineFactor.lean`,
  ~190 LOC) — packaging of `z ↦ z - a`, with principal divisor
  `δ_{some a} - δ_∞`. Built as `RSSimplePole - (const a)`.

**Elementary divisor identity (1 chip):**
* `Manifold/Pic0RiemannSphereTrivial.lean` (~140 LOC) —
  `principalDivisorMap_mnRSAffineFactor a = Div.single (some a) -
  Div.single ∞`, and `elementaryDivisor_mem_PrincDiv` corollary.

**Closure decomposition + final discharge (1 chip):**
* `Manifold/Pic0RiemannSphereSubsingleton.lean` (~190 LOC) — the
  reconstruction sum `Σ_{x ∈ supp(D), x ≠ ∞} D(x) • (Div.single x -
  Div.single ∞)` equals `D` pointwise for any `D : Div0 RS`.
  `subsingleton_pic0_RiemannSphere : Subsingleton (Pic0 RiemannSphere)`
  is now **unconditional**, and via the bridge from earlier in the
  day, `AbelJacobiInput.abelJacobiEquiv_of_RiemannSphere_unconditional`
  gives `Pic0 RS ≃+ AnalyticJacobian RS` axiom-free.

**Net open content after today's 12 chips:**

| Input | Open content |
|---|---|
| `AbelHypothesis B` (general genus) | `AbelGeneratorPeriodCondition B` — discharge for each `f : MeromorphicNonzero X` (Abel forward via level-set chain, ~1,000–2,500 LOC of Stokes content) |
| `AbelHypothesis B` (genus 0) | **done** unconditionally |
| `JacobiInversion B hAbel` (general genus) | Abel converse (injectivity) + Jacobi inversion theorem (surjectivity) |
| `JacobiInversion B hAbel` (genus 0) | **done** unconditionally (`Subsingleton (Pic0 X)` for `X = RS` discharged) |
| `Pic⁰ RS ≃+ AnalyticJacobian RS` | **done** unconditionally |
| `Pic⁰ X ≃+ AnalyticJacobian X` (general `X`) | Needs both C3 general-genus and C4 general-genus |

Items 4, 5, 10, 11, 12, 13 still STUB/OPEN — the unconditional iso
on `RiemannSphere` does not flip them because they require the iso on
**arbitrary** compact connected complex 1-manifolds `X`.

## C3 sub-arc progress (2026-05-15 evening, 25 additional chips merged to main)

Extending the same-day morning chips with 25 further chips delivering
algebra-side closure + the full path-lift infrastructure for the
level-set chain.  All on `main`, build green at 8746 jobs, zero
`sorry`, zero `axiom`.

**Algebra-side closure** (chips 1–3, `Manifold/AbelGeneratorDischargedSet.lean`).
* `dischargedGenerators B` set: closed under `1`, constants, `*`,
  `invMer`, quotients.
* Case-split reduction: `AbelGeneratorPeriodCondition B` reduces to
  the non-constant `toFun` case.

**Regular-value framework** (chip 4,
`Manifold/MeromorphicNonzeroRegularValueSet.lean`).
* `regularValueSet f := (criticalValues f)ᶜ` + openness under
  non-constancy.

**Planar local biholomorphism** (chips 5–6).
* `chartPullback f x`, analyticity, non-zero derivative at regular
  points via `DerivBridgeData.hCompat`, planar `OpenPartialHomeomorph`
  form via `HasStrictFDerivAt.toOpenPartialHomeomorph`.

**Manifold-level local sheet** (chip 7,
`Manifold/MeromorphicNonzeroLocalSheet.lean`).
* `manifoldLocalOph` via double `restrOpen` of the chart-trans-chart
  composition; `localSheetData_at_regular` packaging `LocalSheetData
  f.toRiemannSphere (f.toRiemannSphere x₀) x₀`.

**Topological packaging** (chips 8–10).
* `IsLocalHomeomorphOn f.toRiemannSphere f.regularSet`.
* Fiber finiteness at every regular value
  (`fiber_finite_of_mem_regularValueSet`).
* `HurwitzPatchingData` at every regular value via
  `HurwitzPatchingData.ofLocalSheets`.

**Continuous path lift primitives** (chips 11, 16, 19, 20–22).
* `exists_continuous_local_lift_of_continuous` — local lift on `β ⁻¹'
  sheet.V`.
* `path_lift_unique` / `path_lift_eqOn_Icc` — uniqueness clopen
  argument (global / partial-domain).
* `extend_lift_across_sheet` — single-sheet piecewise extension.
* `exists_sheet_data_extending_to_right` + `extend_continuous_lift_to_right`
  — per-point extension primitive.
* `lifts_agree_globally` / `lifts_agree_at` — choice-independence.

**Smooth path lift primitives** (chips 12–15).
* Pointwise `ContMDiffAt ω` of `sheet.g` at base point
  (`contMDiffAt_localSheet_g_at_basePoint`).
* Open-nbhd `ContMDiffOn ω` extension via
  `contMDiffAt_iff_contMDiffOn_nhds` (valid for ω ≠ ∞).
* Smooth local lift `ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) ∞` at base point
  via `ContMDiffAt.complex_to_real` + `ContMDiffAt.comp`.
* Smooth local lift `ContMDiffOn` on open neighbourhood
  (`exists_contMDiffOn_local_lift`).

**Global lift scaffolding** (chips 17, 18, 23–25).
* `exists_subdivision_hurwitzPatching` — Lebesgue subdivision of
  `unitInterval` adapted to a regular path.
* `exists_continuous_lift_single_sheet` — global lift when β maps into
  one sheet (no gluing).
* `liftReachable f β x₀ T` def + downward closure + zero membership.
* `liftReachable_extends_right` — **openness** via clip+if_le
  construction (globally continuous lift built by clipping `t` to
  `[b, b + ε]` before applying β).
* Boundedness + sSup bounds for the sSup/clopen argument.

**Net open content after today's 25 evening chips** (revised):

| Step | Status | LOC estimate (uncalibrated) |
|---|---|---|
| 1. Closedness `sSup ∈ liftReachable` (sequential limit + local sheet) | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroPathLiftClosed.lean`, 331 LOC) | 250–350 |
| 2. Global continuous lift `sSup = T` (clopen finish) | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroPathLiftExistsOnIcc.lean`, 117 LOC; `sSup_liftReachable_eq_T` + `exists_continuous_lift_on_Icc`) | 80–120 |
| 3. Smooth upgrade of global lift to `ContMDiffOn ∞` | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroPathLiftSmoothOnIcc.lean`, 225 LOC; `contMDiffOn_lift_of_continuous_lift` + `exists_contMDiffOn_lift_on_Icc`) | 150–250 |
| 4. `SmoothPath` bundle from global smooth lift | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroPathLiftSmoothPath.lean`, 141 LOC; `exists_smoothPath_of_lift_on_unitInterval` — uses `Real.smoothTransition` reparametrisation + `ContMDiffOn.comp_contMDiff` to package the lift into `SmoothPath 𝓘(ℝ, ℂ) X`) | 100–150 |
| 5. `levelSetChain f β` definition | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroLevelSetChain.lean`, 152 LOC; `sourceFiber` + `sourceFiberPath` + `levelSetChain` + characterising lemmas. Each fiber-point path is Classical-chosen via step 4) | 150–250 |
| 6. Boundary computation `∂ = δ_tgt − δ_src` | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroLevelSetChainBoundary.lean`, 111 LOC; `sourceFiberDivisor` + `targetFiberDivisor` + `boundary_levelSetChain`) | 200–400 |
| 7a. Target-map injectivity (foundation for bijection) | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroLevelSetTargetInjective.lean`, 151 LOC; `sourceFiberPath_tgt_injOn` via `Path.extend` + `path_lift_eqOn_Icc` on `β ∘ Real.smoothTransition`) | (split from step 7) |
| 7b. Target-map surjectivity onto target fiber | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroLevelSetTargetSurjective.lean`, 240 LOC; `sourceFiberPath_tgt_surjOn` via time-reverse β + step 4 at y + step 2 raw lift + double `path_lift_eqOn_Icc`) | (split from step 7) |
| 7c. Boundary = `Σ targetFiber − Σ sourceFiber` (Finsupp form) | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroLevelSetTargetFiber.lean`, 193 LOC; `targetFiber` def + `sourceFiberPath_tgt_image_eq_targetFiber` (Finset bijection from 7a+7b) + `boundary_levelSetChain_eq_fiberDiff`) | (split from step 7) |
| 7d-a. Off-fiber vanishing of principalDivisorMap | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroPrincipalDivisorOffFiber.lean`, 110 LOC; `principalDivisorMap_toFun_eq_zero_off_fiber` via chart-pullback `tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero`) | (split from step 7d) |
| 7d-b. Order = 1 at simple zero (regular value some 0) | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroPrincipalDivisorAtZero.lean`, 198 LOC; `principalDivisorMap_toFun_eq_one_at_simple_zero` via chart-pullback eventual equality + `AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero`) | 150–250 |
| 7d-c. Order = -1 at simple pole (regular value ∞) | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroPrincipalDivisorAtPole.lean`, 188 LOC; uses `MMeromorphicAt.iff_of_isManifold` for chart-independence → `MeromorphicOn.eventually_analyticAt` for pole isolation → `meromorphicOrderAt_inv` to flip sign) | 150–250 |
| 7d-d. Final identification ∂(levelSetChain) = −principalDivisorMap f pointwise | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroLevelSetPrincipalDivisorIdentification.lean`, 147 LOC; `boundary_levelSetChain_eq_neg_principalDivisorMap_pointwise` via case-split on sourceFiber/targetFiber/off-fiber, composing 7d-a/b/c) | 100–200 |
| 8. Pushforward 1-form `f_*ω` + integral identity | **LANDED 2026-05-15 (bookkeeping)** (`Manifold/MeromorphicNonzeroLevelSetIntegrate.lean`, 98 LOC; `integrate_levelSetChain` Finset-sum expansion via `SmoothChain.integrateLinearMap` + `integrateLinearMap_single`. Substantive `f_*ω` construction layered on top via existing `SmoothPath.integrate_compSmoothPath`.) | 300–500 |
| 9. Structural reduction `AbelGenerator ← (Z period in lattice) + (Z boundary = -principalDivisor)` | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroAbelGeneratorFromLevelSet.lean`, 138 LOC; `abelGeneratorPeriodCondition_of_levelSet_lattice` — cycle Z+AJ has boundary 0, period vector in lattice tautologically; linearity gives AJ's period as lattice element. Named input: `h_struct` (the Z with right boundary AND lattice period). `h_AJ_boundary` (AJ chain's boundary identity) **DISCHARGED 2026-05-16** in `Manifold/PrincipalDivisorAJChainBoundary.lean` (~125 LOC; pure ℤ-linearity + `JacobianChallenge.residue_theorem`) and inlined into the step-9 proof. The β-existence input for the boundary clause of `h_struct` (smooth path 0→∞ avoiding critical values) **DISCHARGED 2026-05-16** in `Manifold/MeromorphicNonzeroRegularPath.lean` (~431 LOC; `exists_regular_path_zero_to_infty` via two `linearInChartSegment` paths through `r := some(s + i)` for generic `s`, concat'd). Concrete witness `regularLevelSetChain f hnc h0 h∞` with its boundary identity (`boundary = -principalDivisorMap f` pointwise) shipped in `Manifold/MeromorphicNonzeroConcreteLevelSetChain.lean` (~146 LOC; `Classical.choose` extraction + composition with step 7d-d). **f_*ω stack scaffolded 2026-05-16**: real-model RS manifold instance (`RiemannSphereRealManifold.lean`, ~96 LOC), pointwise cotangent pullback primitive (`CotangentPullbackAt.lean`, ~94 LOC), pointwise trace `f_*ω` at regular values (`MeromorphicNonzeroTraceAt.lean`, ~117 LOC), `SmoothOneFormOn` partial-section type (`SmoothOneFormOn.lean`, ~88 LOC), scalar evaluation of pullback + trace (`CotangentPullbackAtApply.lean`, ~123 LOC), `ContinuousOn` variant of `path_lift_eqOn_Icc` (`MeromorphicNonzeroPathLiftUniqueOnContinuousOn.lean`, ~131 LOC), and local identification `sourceFiberPath ↔ sheet.g ∘ β ∘ σ` on a sub-interval (`MeromorphicNonzeroSourceFiberPathSheetEq.lean`, ~222 LOC). The chain-rule pathway from `(levelSetChain f β).integrate om` to `∫ applyCotangent (traceAt ...) (β.velocity ·)` is now scaffolded end-to-end pointwise; only the global identification (Lebesgue subdivision over sheet-domain cover) + Stokes/residue argument for the lattice clause remain.) | 400–800 |

**Caveat on estimates.** Today's 25 chips delivered ~2,900 LOC, much
more than the ~300–500 LOC pre-session estimate for "global path
lift".  My historical LOC estimates are 2–6× off; the table above
should be read as a lower bound, with the actual cost likely
considerably higher.

## Mathlib-prerequisite candidates (likely needed before strict closure)

These are *not* part of the challenge directly, but the constructions for
items 1, 2, 5, 8, 9 will need infrastructure not in mathlib at the pin.

- **Finite-dimensionality of `HolomorphicOneForm X`** on compact connected
  Riemann surface — needed for `genus X` to be the right integer. Hodge
  theory; not yet proved.
- **Honest `PrincDiv X`** — *landed.* `PrincDiv X := PrincDivHonestCandidate X`
  in `Divisor/PrincipalDivisorRange.lean` (post-ZZ256). The residue theorem
  on a compact Riemann surface (∑_x ord_x f = 0) is **discharged
  unconditionally** in-tree as `JacobianChallenge.residue_theorem`
  (`Manifold/ResidueTheoremUnconditional.lean`), composing the R1+R2+R3+R4
  chain via `R5Unconditional.R5_principal_degree_zero_statement_holds`.
  Supporting infrastructure: chart-independence of `mmeromorphicOrderAt`
  (`Manifold/MeromorphicAt.lean`), local finiteness
  (`Manifold/MeromorphicDivisor.lean`'s `MMeromorphicOn.divisor`),
  `principalDivisorMap` (`Divisor/PrincipalDivisor.lean`), and
  pole-extension to `RiemannSphere` (`Manifold/MeromorphicExtension.lean`).
- **Honest period lattice** as a rank-`2g` `Submodule ℤ` of `ℂ^g` — requires
  H₁(X; ℤ) for compact Riemann surfaces (not in mathlib at the pin) plus
  period-pairing integration of holomorphic 1-forms over loops.
- **Topological degree of proper holomorphic maps** between Riemann
  surfaces. `fibres_finite_statement` and `regular_value_exists_statement`
  are discharged unconditionally (`Manifold/FibresFiniteUnconditional.lean`
  / `RegularValueExistsUnconditional.lean`). Only
  `fibre_card_well_defined_at_regular_statement` remains, and it still
  needs the analytic local normal form `z ↦ z^k` (not at the mathlib pin).
- **`genus_eq_zero_iff_homeo`** — closed-orientable-surface classification
  plus Riemann-sphere `ChartedSpace`. Multi-month.

## Local infrastructure

The repo's per-file map lives in `JacobianChallenge.lean` (the import
manifest) and the file system. `CHANGELOG.md` documents which files
landed in which branch / wave. This OPEN.md is intentionally not a
duplicate file listing.

## Paths to the next STRICT-CLOSED

Reaching the next **STRICT-CLOSED** requires landing one of:
(a) honest period lattice → `ChartedSpace` on `Jacobian` (flips items 4,
5, 10, plus 11/12/13 cascade),
(b) Abel-Jacobi (flips item 16),
(c) closed-orientable-surface classification (item 14), or
(d) Hodge L² finite-dimensionality of `HolomorphicOneForm` (item 1).
