# Changelog

## 2026-05-20 — `fStarOmegaOn` arc + `HolomorphicTraceExtension` reduction (6 chips, ~974 LOC, direct to `main`)

**6 new files** (`JacobianChallenge/Manifold/`):

* `SheetCotangentPullbackContMDiffAt.lean` (238 LOC) — per-sheet
  cotangent-pullback section smoothness at a regular value in the
  **holomorphic** `𝓘(ℂ, ℂ) ω` bundle. Local-sheet analogue of
  `HolomorphicEquiv.pullbackSection_contMDiffAt`
  (`PullbackSectionSmoothness.lean`) with the global smoothness witness
  replaced by a pointwise `ContMDiffAt ω g y₀` hypothesis. Three lemmas
  shipped:
  - `localSheetPullbackPointwise` — dependently-typed pointwise pullback
    `∀ y : Y, CotangentSpace 𝓘(ℂ, ℂ) y` (mirrors
    `HolomorphicEquiv.pullbackPointwise` to avoid bundle-instance
    ambiguity).
  - `cotangent_inCoordinates_flip_eventually_eq_of_continuousAt` —
    local eventually-form of the cotangent↔tangent inCoordinates bridge
    from `PullbackSectionSmoothness`.
  - `pullbackSection_contMDiffAt_of_localSheet` — headline.
  - `MeromorphicNonzero.sheetPullbackSection_contMDiffAt` — wrapper
    discharging the smoothness witness via
    `f.contMDiffAt_localSheet_g_at_basePoint`.

* `SheetCotPullbackContMDiffAtReal.lean` (292 LOC) — realified
  companion in the `𝓘(ℝ, ℂ) ⊤` bundle. Same `clm_apply_of_inCoordinates`
  scaffold with 𝕜 := ℝ; underlying mathlib lemmas
  (`inCotangentCoordinates_eq`, `cotangentBundleCore_coordChange_apply`,
  `inTangentCoordinates_eq`, `ContMDiffAt.mfderiv_transpose`) are
  field-generic. Includes:
  - `cotangent_inCoordinates_flip_eq_flip_inTangentCoordinates_real` —
    realified bridge identity.
  - `ContMDiffAt.complex_to_real_omega` — regularity-preserving
    complex-to-real realification (companion to the existing
    `complex_to_real` which drops `ω → ∞`; this variant skips the
    final `.of_le`).
  - `pullbackSection_contMDiffAt_of_localSheet_real` — headline.
  - `MeromorphicNonzero.sheetCotPullback_contMDiffAt` — wrapper for
    `sheetCotPullback`.

* `FStarOmegaContMDiffAt.lean` (118 LOC) — pointwise `ContMDiffAt ⊤` of
  `f.fStarOmega hnc om` at every regular value, by combining the
  per-sheet smoothness across `(f.fiberFinset hv₀).attach` via
  mathlib's `ContMDiffAt.sum_section` and bridging to `fStarOmega` via
  `FStarOmegaLocalAt.fStarOmega_eq_sum_sheetCotPullback_at_v0` on the
  labelling neighbourhood.

* `FStarOmegaOn.lean` (81 LOC) — final packaging as a
  `SmoothOneFormOn 𝓘(ℝ, ℂ) RiemannSphere f.regularValueSet`. Ships:
  - `fStarOmega_contMDiffOn` — `ContMDiffOn ⊤` on `regularValueSet`
    (open ⇒ `ContMDiffAt`-at-every-point suffices).
  - `MeromorphicNonzero.fStarOmegaOn` — the bundled structure.

* `TraceAtVanishesOnHolomorphicReduction.lean` (147 LOC) —
  **structural reduction** of `TraceAtVanishesOnHolomorphic X` to a
  single named hypothesis:
  - `HolomorphicTraceExtension X` — for every non-constant `f` and
    `α : HolomorphicOneForm X`, ∃ `α' : HolomorphicOneForm
    RiemannSphere` whose realified components agree pointwise on
    `f.regularValueSet` with the realified trace of `α`.
  - `traceAtVanishesOnHolomorphic_of_extension` — discharge via
    `Subsingleton (HolomorphicOneForm RiemannSphere)` (unconditional,
    in tree) + `realComponent_zero` / `imagComponent_zero`.
  - `regularLevelSetLatticeClause_of_holomorphicTraceExtension` —
    composes with `regularLevelSetLatticeClause_of_traceVanishing` to
    discharge the regular-case lattice clause from a single named
    input.

* `HolomorphicOneFormOn.lean` (98 LOC) — partial-domain holomorphic
  1-form type (analogue of `SmoothOneFormOn` in `𝓘(ℂ, ℂ) ω`). Ships
  the type, `CoeFun` instance, and `HolomorphicOneForm.restrictHolOn`
  canonical restriction. Sets up the target type for the eventual
  on-regular-set holomorphic trace.

**Net effect on RLSL closure.** Pre-session, RLSL discharge reduced to
`TraceAtVanishesOnHolomorphic X` (a *global pointwise vanishing*
hypothesis, opaque to construction). Post-session, this further
reduces to `HolomorphicTraceExtension X` — *existence* of a global
holomorphic 1-form on `ℙ¹` agreeing with the realified trace on the
regular set. The smoothness side of that extension (on the open
regular set) is now **unconditional** via `fStarOmegaOn`. The
remaining classical content for the next chip arc is the
holomorphic-side parallel (target type now exists via
`HolomorphicOneFormOn`) + extension across critical values (n-th-root
cancellation + Riemann removable singularity theorem on 1-forms on
`ℙ¹`); this is genuinely new content not at the mathlib pin.

**Gotchas surfaced during writing** (next-session hazards):

* Bundle topology instance ambiguity — raw
  `(α.toFun (g v)).comp (mfderiv g v) : ℂ →L[ℂ] ℂ` doesn't bind the
  `CotangentSpace` bundle structure; need a typed
  `∀ y, CotangentSpace _ y` wrapper definition first.
* `clm_apply_of_inCoordinates` requires **named arguments**
  `(hϕ := …) (hv := …) (hb₂ := …)` to pin the `VectorBundle`
  metavariables.
* `congr_of_eventuallyEq` direction: `f₁ =ᶠ f + ContMDiffAt f →
  ContMDiffAt f₁`, *not* the reverse.
* `SmoothOneForm`'s regularity is `⊤` (= `ω`, the analytic top of
  `WithTop ℕ∞`), strictly above `∞`. `ContMDiffAt.complex_to_real`
  drops to `∞` via a final `.of_le`; for `⊤`-preserving realification
  use `complex_to_real_omega` (shipped in
  `SheetCotPullbackContMDiffAtReal.lean`).

**Build**: all 6 chips single-file `LEAN_NUM_THREADS=1 lake env lean`
clean; zero `sorry`, zero `axiom`. Full `lake build` deferred to
next-session merge gate.

## 2026-05-19 (evening) — `RegularLevelSetLatticeClause` from holomorphic-trace vanishing (1 chip, ~180 LOC, direct to `main`)

**1 new file** (`JacobianChallenge/Manifold/`):

* `RegularLevelSetLatticeClauseFromTraceVanishing.lean` — second
  structural reduction route for the regular-case lattice clause,
  parallel to `RegularLevelSetLatticeClauseFromAJ.lean`. Ships:

  - `TraceAtVanishesOnHolomorphic X` — named hypothesis: for every
    non-constant `f`, every `α : HolomorphicOneForm X`, and every
    regular value `v`,
    `f.traceAt hnc hv (realComponent α) = 0` and
    `f.traceAt hnc hv (imagComponent α) = 0`.

  - `regularLevelSetLatticeClause_of_traceVanishing` — conditional
    discharge. Composes today's σ-1 chip (now unconditional via
    `integrandContinuousAlongBeta_holds`) + the real-imag split of
    `complexChainPeriod` + `applyCotangent_zero` + integral of zero is
    zero, to conclude the period vector is zero (hence in lattice).

**Status**: this isolates the *irreducible analytic content* of Abel
forward at the regular-case clause as a single named hypothesis. The
hypothesis is equivalent to: the trace map
`HolomorphicOneForm X → HolomorphicOneForm RiemannSphere` lands in a
subsingleton group (`HolomorphicOneForm ℙ¹ = 0`, in tree). The
construction of the trace map is the remaining classical work
(n-th-root cancellation at critical values + Riemann removable
singularity theorem on 1-forms).

**Build**: 8872 jobs, zero `sorry`, zero `axiom`.

## 2026-05-19 (late afternoon) — `RegularLevelSetLatticeClause` ↔ `AbelGeneratorPeriodCondition` structural reduction (1 chip, ~130 LOC, direct to `main`)

**1 new file** (`JacobianChallenge/Manifold/`):

* `RegularLevelSetLatticeClauseFromAJ.lean` — completes the structural
  loop in the regular-case lattice clause. Two theorems:

  - `regularLevelSetLatticeClause_of_abelGeneratorPeriodCondition`:
    given any `B : AbelJacobiInput α h` and the per-`f` AJ-chain period
    condition `AbelGeneratorPeriodCondition B`, the regular-case
    lattice clause `RegularLevelSetLatticeClause X α h` follows.

    **Proof**: cycle witness `Z + AJ ∈ SmoothCycle`
    (`regularLevelSetCycleWitness`, in tree) gives
    `period(Z + AJ) ∈ lattice` automatically. `period(AJ) ∈ lattice`
    by hypothesis. `period(Z) = period(Z + AJ) - period(AJ) ∈ lattice`
    via `AddSubgroup.sub_mem`.

  - `regularLevelSetLatticeClause_of_genus_zero`: at genus zero, the
    period vector is a subsingleton (`Fin 0 → ℂ`), so the lattice
    clause holds unconditionally.

**Status**: the structural gap between
`RegularLevelSetLatticeClause` (a clause on the analytic chain) and
`AbelGeneratorPeriodCondition` (a clause on the formal AJ chain) is
now closed. The substantive analytic content of Abel forward —
discharging `AbelGeneratorPeriodCondition` for arbitrary non-constant
`f` at genus ≥ 1 — remains open and is the residue theorem on 1-forms
on `ℙ¹` / Stokes on 2-chains content (~1,500–2,500 LOC of genuine
classical infrastructure).

**Build**: 8871 jobs, zero `sorry`, zero `axiom`.

## 2026-05-19 (afternoon) — `IntegrandContinuousAlongBeta` UNCONDITIONAL (4 chips, ~600 LOC, direct to `main`)

End-to-end discharge of `MeromorphicNonzero.IntegrandContinuousAlongBeta`
via the chart-coord-pair architecture extended through the f-5 sheet
smoothness layer. Closes the named hypothesis blocking
`IntegrateLevelSetChainSigmaReparam.lean`'s σ-1 chip and one of the two
remaining inputs to `RegularLevelSetLatticeClause` discharge.

**4 new files** (`JacobianChallenge/Manifold/`):

* `PairingContinuityBetaLocal.lean` — chip 12 relaxed from
  `ContMDiff β` (global) to `ContMDiffAt β s₀` (pointwise). Ships:
  - `chartBetaVelocity_contMDiffAt_local` (local chip 9).
  - `chartBetaVelocity_continuousAt_local`.
  - `continuousAt_pairing_smoothOneForm_beta_local` (local chip 12).
  Chart-preimage nbhd obtained via `ContinuousAt.preimage_mem_nhds`
  rather than `IsOpen.preimage Continuous`. Identical chart-coord-pair
  structure otherwise.

* `SheetCotPullbackPairingContinuity.lean` — per-sheet pairing
  continuity at `s₀`. Headline: for `β s₀ ∈ u` (open) with
  `sheet.g := (localSheetData_at_regular hnc hp_reg).g` real-smooth
  on `u`, the pairing
  ```
  s ↦ applyCotangent (sheetCotPullback hnc hp_reg (β s) om) (mfderiv β s 1)
  ```
  is `ContinuousAt s₀`. **Proof**: on the open nbhd `β ⁻¹' u` of `s₀`,
  the chain rule (`mfderiv_comp_apply`) + `applyCotangent_cotangentPullbackAt`
  rewrites the LHS to the pairing of `om` along the composed smooth
  path `γ := sheet.g ∘ β : ℝ → X`. Then the local chip 12 applied to
  `ContMDiffAt γ s₀` (= compose `β` smooth at `s₀` with `sheet.g` smooth
  at `β s₀`) gives `ContinuousAt s₀` of the RHS. `ContinuousAt.congr`
  transfers via the open-nbhd EqOn.

* `FStarOmegaPairingContinuity.lean` — `fStarOmega`-pairing
  `ContinuousAt s₀` for `β s₀ ∈ regularValueSet`. **Proof**: on the
  open nbhd `β ⁻¹' localFiberLabelingNbhd hnc hβs₀_reg`, the `f-3`
  rewrite `fStarOmega_eq_sum_sheetCotPullback_at_v0` expresses
  `fStarOmega om (β s)` as a fixed Finset sum over `fiberFinset hβs₀_reg`.
  `applyCotangent_finset_sum` distributes the pairing. Each summand
  is `ContinuousAt s₀` via the per-sheet chip (instantiated with the
  realified ω-smooth nbhd from
  `exists_contMDiffOn_localSheet_g_near_basePoint`). Finset induction
  with `ContinuousAt.add` collapses the sum. `ContinuousAt.congr`
  finishes via the open-nbhd EqOn.

* `IntegrandContinuousAlongBetaUnconditional.lean` — assembles
  `continuousOn_fStarOmega_pairing_Icc01` (point-by-point on
  `Icc 0 1` via `hβ_reg`) and plugs it into the in-tree
  `integrandContinuousAlongBeta_of_fStarOmega_pairing_continuousOn`
  reduction. **Headline**:
  ```
  theorem integrandContinuousAlongBeta_holds
      (f : MeromorphicNonzero X)
      (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
      (hβ_smooth : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) ∞ β)
      (hβ_reg : ∀ s ∈ Icc 0 1, β s ∈ f.regularValueSet)
      (om : SmoothOneForm 𝓘(ℝ,ℂ) X) :
      f.IntegrandContinuousAlongBeta hnc hβ_smooth hβ_reg om
  ```

**Architectural caveat dissolved:** the prior factor-decomposed route
(2026-05-18 evening, chips 1–8) routed through `cotangentEquiv` which
is NOT globally continuous for non-trivial cotangent bundles. The
chart-coord-pair route from today bypasses this entirely — the
pairing is chart-invariant (chip 11) so the per-sheet pairing
continuity uses only ω-smooth-on-open data, which IS chart-cocycle-
clean by composing with the bundle's natural trivialisation
internal to `cotangentPullbackAt`.

**Status post-f-5 close**: `RegularLevelSetLatticeClause` discharge
now requires only the **residue theorem on 1-forms on `ℙ¹`**
(`paper/jacobian.md`, ~1,500–2,500 LOC). Chain-difference reduction
in `RegularLevelSetChainBoundaryAJ.lean` reduces `period(Z) ∈ lattice`
to `period(AJ-chain) ∈ lattice`, which IS
`AbelGeneratorPeriodCondition` — circular w.r.t. our goal. The
residue theorem is the genuinely new classical input needed.

**Build:** 8870 jobs, zero `sorry`, zero `axiom`.

## 2026-05-19 — Chart-coord-pair architecture: SmoothOneForm pairing continuity (3 chips, ~351 LOC, direct to `main`)

Three chips completing the SmoothOneForm side of the chart-coord-pair
architecture for `IntegrandContinuousAlongBeta` (started 2026-05-18
evening with chip 9, `ChartBetaVelocity`).

**3 new files** (`JacobianChallenge/Manifold/`):

* `ChartBetaVelocitySelfEval.lean` (90 LOC) —
  `chartBetaVelocity_self`: at the anchor `s₀`, both source-side
  (`tangentBundleCore_coordChange_model_space` on `ℝ`) and target-side
  (`coordChange_self` at base `β s₀`) cocycles collapse, giving
  `chartBetaVelocity I β s₀ s₀ = mfderiv 𝓘(ℝ, ℝ) I β s₀ (1 : ℝ)`.

* `ChartBetaPairingInvariance.lean` (145 LOC) —
  `applyCotangent_eq_chart_pairing_beta`: for any cotangent
  `φ : CotangentSpace I (β s)` with `β s ∈ (chartAt H (β s₀)).source`,
  the pairing
  `applyCotangent φ (mfderiv β s 1)`
  equals the chart-coord pairing of `φ` (transported to chart at
  `β s₀`) with `chartBetaVelocity I β s₀ s`. Mirrors
  `SmoothPath.integrand_eq_chart_pairing` but stated for a *free*
  cotangent, decoupling it from any `SmoothOneForm` wrapping — ready
  to compose with `traceAt` directly. The cancellation is the
  tangent-bundle cocycle `coordChange j i x ∘ coordChange i j x = id`
  at `x = β s`, paired with `cotangentBundleCore_coordChange_apply`.

* `PairingContinuityBeta.lean` (116 LOC) —
  `continuousAt_pairing_smoothOneForm_beta` and
  `continuous_pairing_smoothOneForm_beta`: for smooth `β : ℝ → M` and
  `om : SmoothOneForm I M`, the function
  `s ↦ applyCotangent (om (β s)) (mfderiv β s 1)` is `ContinuousAt s₀`
  for every `s₀`, hence `Continuous`. β-analogue of
  `SmoothPath.continuous_integrand_at`. Assembled from the three
  primitives above plus `cotangentSection_contMDiffAt_iff` (factored
  through `Continuous β`) and `ContinuousAt.clm_apply`. When
  `fStarOmega` is upgraded to a `SmoothOneForm` (post-`f-5`), this
  lemma directly discharges `IntegrandContinuousAlongBeta` for the
  trace-pairing along `β`.

**Remaining blocker for unconditional `IntegrandContinuousAlongBeta`:**
`f-5` — section smoothness of `fStarOmega` on `regularValueSet` (or
the `SmoothOneFormOn` upgrade). Once `f_*ω` is a `SmoothOneForm` (or
`SmoothOneFormOn regularValueSet`), the SmoothOneForm pairing
continuity above gives the conclusion.

**Build:** 8866 jobs (was 8863), zero `sorry`, zero `axiom`.

## 2026-05-18 (evening) — `IntegrandContinuousAlongBeta` groundwork (9 chips, ~893 LOC, direct to `main`)

Nine chips toward unconditional discharge of
`MeromorphicNonzero.IntegrandContinuousAlongBeta` — the named hypothesis
introduced by the σ-1 chip
(`integrate_levelSetChain_eq_traceAt_lineIntegral`,
`IntegrateLevelSetChainSigmaReparam.lean`) and the remaining analytic
input to step 6 of the `RegularLevelSetLatticeClause` discharge (the
other being the residue theorem for `f_*ω` on `ℙ¹`).

The first eight chips build a **factor-decomposed entry point** (trace
factor × velocity factor), reaching a single API
`integrandContinuousAlongBeta_of_per_sheet_univ_and_velocity` that
discharges `IntegrandContinuousAlongBeta` from two plain `ContinuousOn`
hypotheses on `Icc 0 1`. The ninth chip (`ChartBetaVelocity`) is the
first primitive of the **chart-coord-pair architecture** (mirroring
`SmoothPathIntegrability.continuous_integrand_at`), which is the
architecturally correct path to *unconditional* discharge for general
regular-value paths (see caveat below).

**9 new files** (`JacobianChallenge/Manifold/`):

* `ApplyCotangentContinuity.lean` (107 LOC) — bilinear continuity of
  `SmoothPath.applyCotangent` lifting mathlib's
  `ContinuousOn.clm_apply` / `Continuous.clm_apply` /
  `ContinuousAt.clm_apply` / `ContinuousWithinAt.clm_apply` through
  `cotangentEquiv`. Reduces joint continuity of `applyCotangent (φ y)
  (v y)` to continuity of the cotangent factor (as a CLM via
  `cotangentEquiv`) and the vector factor.

* `IntegrandContinuousAlongBetaFStarOmega.lean` (111 LOC) — dependent-if
  kill. Reduces `IntegrandContinuousAlongBeta` (which uses `if hs : s ∈
  Icc 0 1 then …`) to a plain `ContinuousOn` of the un-guarded
  `fStarOmega`-pairing on `Icc 0 1`, via `fStarOmega_apply_of_regular`
  + `ContinuousOn.congr`.

* `IntegrandContinuousAlongBetaFactors.lean` (104 LOC) — factor-decomposed
  entry point. Composes the previous two chips to discharge
  `IntegrandContinuousAlongBeta` from trace-factor `ContinuousOn` +
  velocity-factor `ContinuousOn` (both on `Icc 0 1`, both plain).

* `CotangentEquivFStarOmegaSum.lean` (76 LOC) — CLM-level Finset-sum
  rewrite. Lifts the `f-3` identity
  `fStarOmega = ∑_p sheetCotPullback` through `cotangentEquiv` (which
  commutes with `Finset.sum` since it is a `LinearEquiv`) on the
  labelling nbhd.

* `TraceFactorContinuousOnFromSheets.lean` (99 LOC) — trace-factor
  `ContinuousOn` on the labelling nbhd from per-sheet `ContinuousOn`
  inputs, via `continuousOn_finset_sum` + the prior CLM-level rewrite.

* `TraceFactorContinuousOnAlongBeta.lean` (94 LOC) — pullback along
  continuous `β : ℝ → RiemannSphere`. Trace-factor `ContinuousOn` on
  any `S ⊆ β ⁻¹' (labelling nbhd)` via `ContinuousOn.comp` +
  `MapsTo`-of-preimage.

* `TraceFactorContinuousOnIcc01.lean` (111 LOC) — pointwise gluing to
  global `ContinuousOn (Icc 0 1)`. At each `s₀ ∈ Icc 0 1`, the labelling
  nbhd at `β s₀` is an open nhd of `β s₀` (by
  `mem_localFiberLabelingNbhd_self`), so the β-preimage is an open ℝ-nhd
  of `s₀`; `ContinuousOn` ⇒ `ContinuousAt` ⇒ `ContinuousWithinAt
  (Icc 0 1)`. Discharge input is a single **universal**
  `h_per_sheet_univ` hypothesis.

* `IntegrandContinuousAlongBetaPerSheetVel.lean` (102 LOC) — top-level
  API endpoint composing the trace-factor `Icc 0 1` lifting with the
  factor-decomposed entry point. Headline:
  `integrandContinuousAlongBeta_of_per_sheet_univ_and_velocity`.

* `ChartBetaVelocity.lean` (89 LOC) — direct-smooth-map analogue of
  `SmoothPath.chartVelocity` (which is `SmoothPath`-only). For smooth
  `β : ℝ → M` and base parameter `s₀`, defines the chart-coord
  representative of `β'(s) := mfderiv β s 1` trivialised via
  `chartAt H (β s₀)`. Three lemmas: `chartBetaVelocity` def,
  `contMDiffAt_chartBetaVelocity ∞` at `s₀` (via
  `ContMDiffAt.mfderiv_const`), and `continuousAt_` corollary. First
  primitive of the chart-coord-pair architecture.

### Architectural caveat on chips 1–8 (cotangentEquiv factor-decomposition)

The factor-decomposition API in chips 4–8 routes through `cotangentEquiv
(φ v) : ℂ →L[ℝ] ℝ` as an *absolute-coord* function `v ↦ (CLM : ℂ
→L[ℝ] ℝ)`. **For non-trivial cotangent bundles (RS has 2 charts,
non-identity chart transitions), this absolute-coord view is NOT
globally continuous in general** — sections are continuous *in the
bundle topology*, which differs from absolute-coord at chart boundaries.

The chart-cocycle cancellation only happens inside the *pairing*
`applyCotangent (om v) (vel v)`, which is why
`SmoothPathIntegrability.continuous_integrand` proves the whole
integrand continuous **without** factoring through individual
covector/vector continuities.

**Consequence:** the `h_per_sheet_univ` discharge in chip 8 is
discharge-friendly only when (i) the labelling nbhd fits within a single
RS chart and (ii) each `sheet.g`'s image fits within a single X chart.
For paths that don't cross `∞`, this holds. For general regular-value
paths, the architecturally correct discharge is the **chart-coord-pair
architecture** (mirroring `SmoothPathIntegrability.continuous_integrand_at`):
chart-coord cotangent representative (`chartFStarOmega β s₀ s`) +
chart-coord velocity (chip 9's `chartBetaVelocity`) +
chart-invariant pairing.

### Remaining for unconditional `IntegrandContinuousAlongBeta`

* `chartFStarOmega β s₀ s` — chart-coord representative of
  `fStarOmega(β s)` anchored at chart `chartAt H (β s₀)`. Requires
  `fStarOmega` as a smooth section on `regularValueSet` (i.e. the
  `f-5` chip: `SmoothOneFormOn 𝓘(ℝ, ℂ) RiemannSphere
  (regularValueSet f)`), which in turn requires per-sheet section
  smoothness for `cotangentPullbackAt sheet.g`. The latter is the
  `f-4` analogue of `PullbackSectionSmoothness.HolomorphicEquiv
  .pullbackSection_contMDiffAt`, adapted from global biholomorphisms to
  local sheets (estimated ~300–500 LOC).
* Same-point self-evaluation
  `chartBetaVelocity β s₀ s₀ = mfderiv β s₀ 1` (via
  `inTangentCoordinates_eq` at `(s₀, s₀)` + `coordChange_self`,
  ~30–50 LOC).
* Chart-invariance of pairing on chart preimage near `s₀` (analogue of
  `SmoothPathIntegrability.integrand_eq_chart_pairing`).
* Pointwise gluing to `ContinuousOn (Icc 0 1)` via chart-coord pairing
  + `ContinuousOn.congr`.

Plus the unrelated track for step 6 of `RegularLevelSetLatticeClause`:
the **residue theorem on 1-forms on `ℙ¹`** (adaptation of the in-tree
`JacobianChallenge.residue_theorem`, function-level, to meromorphic
1-forms; estimated ~1,500–2,500 LOC).

### Verification

Build green at **8863 jobs** (was 8854 pre-session). Zero `sorry`,
zero `axiom`. All chips locally verified via
`taskpolicy -b nice -n 19 env LEAN_NUM_THREADS=1 lake build` (serial,
no parallel sub-agents).

### Per-commit history

* `4830b71` — chip 1 (`ApplyCotangentContinuity`)
* `f4fdbc2` — chip 2 (`IntegrandContinuousAlongBetaFStarOmega`)
* `8d009a8` — chip 3 (`IntegrandContinuousAlongBetaFactors`)
* `c4c393a` — chip 4 (`CotangentEquivFStarOmegaSum`)
* `b18ddb7` — chip 5 (`TraceFactorContinuousOnFromSheets`)
* `62507b3` — chip 6 (`TraceFactorContinuousOnAlongBeta`)
* `b4a7acf` — chip 7 (`TraceFactorContinuousOnIcc01`)
* `e22807b` — chip 8 (`IntegrandContinuousAlongBetaPerSheetVel`)
* `b142751` — chip 9 (`ChartBetaVelocity`)

## 2026-05-17 — Global integrand-trace integral identity (4 chips, ~640 LOC, direct to `main`)

Lifts the lifted-point local-identification arc to a **global**
integrand-trace integral identity:

```
SmoothChain.integrate (levelSetChain f β) om
  = ∫ t in 0..1, derivσ(t) *
      applyCotangent (traceAt … (β(σ t)) om) (mfderiv β (σ t) 1)
```

This is the **integrated source-side equality** with the traceAt-based
RHS in `derivσ` factored form — exactly the shape needed for the
σ-reparametrisation change-of-variables (which would convert to
`∫ s in 0..1, applyCotangent (traceAt … (β s) om) (mfderiv β s 1) ds`,
modulo continuity of the integrand-as-function-of-s = f_*ω smoothness).

**4 new files** (`JacobianChallenge/Manifold/`):

* `SourceFiberPathIntegrandChainAtT.lean` (~238 LOC) — chain-rule-
  unfolded per-fibre integrand at general `t₀`. Composes local
  identification with two `mfderiv_comp_apply` applications and
  `applyCotangent_cotangentPullbackAt`. Headline:
  ```
  ∃ a b ∈ [0,1], a ≤ t₀ ≤ b, ∀ u ∈ Ioo a b,
    (sourceFiberPath p).integrand om u
      = applyCotangent (cotangentPullbackAt sheet_q.g (β(σ u)) om)
          (mfderiv β (σ u) (mfderiv σ u 1))
  ```
  Required exposing strict bounds `0 < t₀ → a < t₀` and `t₀ < 1 → t₀ < b`
  in upstream chips (SourceFiberPathExtendEqSheetGAtT,
  SourceFiberPathIntegrandLocalSheetGAtT) for downstream use at
  `u = t` strictly.

* `GlobalIntegrandTraceIdentity.lean` (~165 LOC) — global per-`t`
  identity at any `t ∈ Ioo 0 1`:
  ```
  ∑ p, (sourceFiberPath p).integrand om t
    = applyCotangent (traceAt f hnc hβσt_reg om)
        (mfderiv β (σ t) (mfderiv σ t 1))
  ```
  No sub-interval restriction. Composes per-fibre chain-rule + Finset
  bijection (sourceFiber ↔ fiberFinset(β(σ t)) via `extend t`) +
  `applyCotangent_traceAt`. Boundary cases `t = 0, 1` are Lebesgue-
  null and not needed for integration.

* `IntegrateLevelSetChainEqTraceAt.lean` (~125 LOC) — integrated
  identity:
  ```
  SmoothChain.integrate (levelSetChain f β) om
    = ∫ t in 0..1, applyCotangent (traceAt … (β(σ t)) om)
        (mfderiv β (σ t) (mfderiv σ t 1))
  ```
  Composes `integrate_levelSetChain` (chain → ∑_p path-integrals) +
  `intervalIntegral.integral_finset_sum` (swap ∑ and ∫) +
  `intervalIntegral.integral_congr_ae` (boundary `{1}` measure-zero) +
  global per-`t` identity.

* `IntegrandSigmaSmulFactor.lean` (~162 LOC) — factors out `derivσ(t)`:
  ```
  ∫ t in 0..1, applyCotangent (…) (mfderiv β (σ t) (mfderiv σ t 1))
    = ∫ t in 0..1, derivσ(t) * applyCotangent (…) (mfderiv β (σ t) 1)
  ```
  Via `mfderiv_eq_fderiv` (mfderiv σ t 1 = derivσ(t) on ℝ → ℝ),
  `ContinuousLinearMap.map_smul` (mfderiv β linearity), and
  `cotangentEquiv` ℝ-linearity (applyCotangent φ (c • w) = c * apply
  Cotangent φ w).

Build green at **8842 jobs** (up from 8838). Zero `sorry`, zero
`axiom`. No item flips.

**Remaining for `RegularLevelSetLatticeClause` discharge:**
1. σ-reparametrisation `s = σ t` via
   `intervalIntegral.integral_comp_mul_deriv`. Requires
   continuity of the integrand-as-function-of-s, which is the
   `f_*ω` smooth-on-`regularValueSet` packaging.
2. `f_*ω` smooth-on-`regularValueSet` packaging.
3. Residue theorem adaptation `principalDivisorMap → f_*ω` on ℙ¹
   → period ∈ `periodLatticeImage`.

## 2026-05-17 — Lifted-point local identification at general t₀ (2 chips, ~345 LOC, direct to `main`)

Generalises the existing local-identification chip
`sourceFiberPath_toPath_extend_eq_sheet_g_locally` (at `t₀ = 0`) to
**arbitrary** `t₀ ∈ Icc 0 1`, using the **lifted-point sheet**
`sheet_q` centered at `q := (sourceFiberPath p).toPath.extend t₀`
instead of the source-fibre sheet `sheet_x` centered at `x ∈
sourceFiber(β 0)`.

The key observation: `sheet_q.V` is automatically a nbhd of
`f.toRiemannSphere q = β(σ t₀)` (via `sheet_q.mem_V`), so the
sub-interval condition is dischargeable at every `t₀` — bypassing
the β 0-centered sub-interval restriction of the original chain
rule. This opens the path to a **global** integrand-trace identity
without Hurwitz subdivision.

**2 new files**:

* `SourceFiberPathExtendEqSheetGAtT.lean` (~218 LOC) — local
  identification at general `t₀`. Same proof template as the existing
  `t₀ = 0` chip, generalised via `Metric.ball t₀ ε` constructions
  using `ε := min ε₁ ε₂` from the two preimage nbhds. Headline:
  ```
  ∃ a b ∈ [0,1], a ≤ t₀ ≤ b, ∀ t ∈ Icc a b,
    (sourceFiberPath p).toPath.extend t = sheet_q.g (β(σ t))
  ```

* `SourceFiberPathIntegrandLocalSheetGAtT.lean` (~127 LOC) — composes
  with `SmoothPath.integrand_eq_of_ambient_eqOn_Icc_fun` to give the
  per-fibre integrand identity at general `t₀`:
  ```
  ∃ a b ∈ [0,1], a ≤ t₀ ≤ b, ∀ u ∈ Ioo a b,
    (sourceFiberPath p).integrand om u
      = applyCotangent (om (sheet_q.g(β(σ u))))
          (mfderiv (sheet_q.g ∘ β ∘ σ) u 1)
  ```
  Bridges `extend` equality to `ambient` equality via
  `ambient_eq_on_unitInterval` + `Path.extend_extends'`.

The chain-rule unfolding into
`applyCotangent (cotangentPullbackAt sheet_q.g (β(σ u)) om) (...)` form
is the natural next chip; combined with the bijection re-indexing,
gives the **global integrand-trace identity** at any regular `t`,
which integrates to the global integral identity without Lebesgue
subdivision.

Build green at **8838 jobs** (up from 8836). Zero `sorry`, zero
`axiom`. No item flips.

## 2026-05-17 — Integrand-trace identity in full eventually form (5 chips, ~720 LOC, direct to `main`)

Building on the per-`t` trace identity arc, lifts the integrand-level
chain-rule + trace identity to a fully eventually-quantified form
near `t = 0`. Composing all hypotheses (per-fibre chain-rule realified
smoothness, sub-interval V-membership, lift-equality, regularity)
gives:

```
∀ᶠ t in 𝓝[Ioc 0 1] 0, ∃ hβσt_reg : β(σ t) ∈ regularValueSet,
  ∑ p ∈ sourceFiber, (sourceFiberPath p).integrand om t
    = applyCotangent (traceAt f hnc hβσt_reg om) (β'(σ t) σ'(t))
```

This is the integrand of `(levelSetChain f β).integrate ω` equating to
the integrand of the line integral of `f_*ω` along β (modulo σ-reparam).
Lebesgue subdivision over Hurwitz patches of `[0, 1]` lifts to global
integral identity.

**5 new files** (`JacobianChallenge/Manifold/`):

* `PerFiberSheetEventually.lean` (~125 LOC) — per-fibre + uniform
  filter forms of the lift-equality and sub-interval V-membership
  conditions near `t = 0`.

* `SourceSheetSumEqTraceAtEventually.lean` (~120 LOC) — eventually
  form of the per-`t` trace identity:
  `∀ᶠ t in 𝓝[Icc 0 1] 0, ∃ hβσt_reg, source-sum = traceAt(...)`.

* `LevelSetIntegrandEqTraceAtApply.lean` (~145 LOC) — integrand-level
  per-`t` identity composing chain-rule structural identity with the
  trace identity:
  `∑ p, integrand(sourceFiberPath p) om t
     = applyCotangent (traceAt f hnc hβσt_reg om) (β'(σt) σ'(t))`.

* `SheetGRealSmoothEventually.lean` (~125 LOC) — realified sheet.g
  smoothness eventually near `t = 0`, via
  `exists_contMDiffOn_localSheet_g_near_basePoint` +
  `ContMDiffAt.complex_to_real`. Uniform-over-sourceFiber form.

* `PerFiberChainRuleEventually.lean` (~125 LOC) — promotes the
  per-fibre chain-rule chip from `∃ δ > 0, ...` to filter form
  `∀ᶠ t in 𝓝[>] 0, ...` via intersection with realified-smoothness
  filter.

* `LevelSetIntegrandEqTraceAtApplyEventually.lean` (~125 LOC) — the
  full eventually composition headline.

Build green at **8836 jobs** (up from 8829). Zero `sorry`, zero
`axiom`. No item flips.

## 2026-05-17 — `RegularLevelSetLatticeClause` per-`t` trace identity (6 chips, ~975 LOC, direct to `main`)

Closes the substantive analytic primitives needed to bridge the
chain-rule structural identity (`sum_sourceFiber_integrand_chain_at`)
with the trace `traceAt(f)(β(σ t))(ω)` at any `t ∈ Icc 0 1` on a
sub-interval where `β(σ t) ∈ sheet_p.V` for every fibre point `p`. This
is the second-to-last step in discharging `RegularLevelSetLatticeClause`
(the substantive named input for `AbelHypothesis B` in general genus
that, combined with `AbelLatticeWitnessCriticalCase`, flips items
4, 5, 10, 11, 12, 13).

**6 new files** (`JacobianChallenge/Manifold/`):

* `MeromorphicNonzeroFiberFinsetCard.lean` (~140 LOC) — bridges
  `(f.fiberFinset hv).card` to `JacobianChallenge.ContMDiff.degreeFiber
  f.toRiemannSphere` via a `RegularValueWitnessReg`-builder
  (`regularValueWitnessReg_of_mem_regularValueSet`). Headlines:
  `fiberFinset_card_eq_degreeFiber` and the constancy corollary
  `fiberFinset_card_const : (fiberFinset hv₁).card = (fiberFinset hv₂).card`.

* `SourceFiberPathAmbientSurjOnAt.lean` (~210 LOC) — surjectivity-by-
  cardinality. Headlines:
  - `sourceFiberPath_toPath_extend_image_eq_fiberFinset_at` — Finset
    equality `image of sourceFiber.attach under (extend t) = fiberFinset
    (β(σ t))` via the existing image ⊆ inclusion + injection +
    cardinality match (from `fiberFinset_card_const`).
  - `sourceFiberPath_toPath_extend_surjOn_at` — surjectivity statement.
  - `sourceFiberPath_toPath_extend_bijOn_at` — `Set.BijOn` packaging.

* `CotangentPullbackAtCongr.lean` (~85 LOC) — `cotangentPullbackAt` is
  germ-determined: `cotangentPullbackAt_congr_of_eventuallyEq` (via
  `Filter.EventuallyEq.mfderiv_eq`) and `_of_eqOn_open` corollary.

* `LocalSheetDataUnique.lean` (~140 LOC) — uniqueness of local right-
  inverses. Two versions:
  - `g_eventuallyEq_of_g_eq` — between two `LocalSheetData`s sharing a
    base point: agreeing at `y₀` implies eqOn a nbhd.
  - `g_eventuallyEq_of_isLocalRightInverse` — general version against
    arbitrary local right-inverse `g : Y → X` near `y` with `g y ∈ s.U`,
    `f ∘ g = id` near `y`. Used by the cross-sheet identification.

* `CotangentPullbackSheetIdentification.lean` (~190 LOC) — cross-sheet
  cotangent pullback identification at a regular value:
  `cotangentPullbackAt_localSheet_eq_at_target_sheet` — for source-side
  sheet `sheet_p` (centered at `p` over a *different* base value) and
  the target-side sheet `sheet_q` (where `q := sheet_p.g v`) at
  `v ∈ sheet_p.V`, the cotangent pullbacks at `v` agree.

* `SourceSheetSumEqTraceAt.lean` (~210 LOC) — the headline per-`t`
  trace identity. `sheetCotPullback` wrapper fixes both model arguments
  at `𝓘(ℝ, ℂ)` (dodging an `open scoped unitInterval` parser
  interference with the `(I := …)` named-arg syntax in the conclusion
  position). `source_sheet_sum_eq_traceAt`:
  ```
  ∑_{p ∈ sourceFiber} sheetCotPullback sheet_p.g (β(σ t)) ω
    = traceAt f hnc hβσt_reg ω
  ```
  parametrized over the sub-interval condition `h_sub_interval`
  (`β(σ t) ∈ sheet_p.V` for every `p`) and the lift-equality condition
  `h_lift_eq` (`(sourceFiberPath p).toPath.extend t = sheet_p.g (β(σ t))`).
  Both will be discharged downstream on a uniform-δ sub-interval.

**Net effect on `RegularLevelSetLatticeClause`.** The cycle path from
sourceFiber → fiberFinset bijection (chip 2) and the trace identity
(chip 6) together complete the **algebraic** content of the per-`t`
lattice clause discharge — what remains for the full clause is:

1. Lebesgue gluing across the Hurwitz subdivision (composing per-sheet
   sub-interval identities to a global `[0, 1]` identity), via the
   already-built `exists_subdivision_hurwitzPatching`.
2. σ-reparametrisation reducing the integrand to the natural β-form.
3. Residue theorem for `f_*ω` on `ℙ¹` → period in `periodLatticeImage`,
   layered on top of `JacobianChallenge.residue_theorem`
   (`Manifold/ResidueTheoremUnconditional.lean`) adapted from the
   principal-divisor case to `f_*ω`'s residue divisor on RS.

Build green at **8829 jobs** (up from 8808). Zero `sorry`, zero
`axiom`. No item flips.

## 2026-05-17 — Hodge finite-dim Forster scaffolding through HolomorphicOneForm packaging (16 chips, 2948 LOC, direct to `main`)

End-to-end scaffolding of the elementary Forster/Montel/Riesz proof of
`HolomorphicOneFormFiniteDim X` for compact complex 1-manifolds. The
final chip packages the limit of a seminorm-bounded subsequence as an
honest `HolomorphicOneForm X`; only the seminorm-convergence upgrade
(inner-disk uniform → outer-disk seminorm) and the Riesz application
remain.

**16 new files** (`JacobianChallenge/Manifold/`):

* `HolomorphicOneFormChartCoeff.lean` (340 LOC) — chart-coord coefficient
  `localCoeff om y : ℂ → ℂ` of a holomorphic 1-form `om` via canonical
  chart at base point `y`. Pointwise linearity (`_zero`, `_add`, `_neg`,
  `_sub`, `_smul`) + ℂ-linear map `localCoeffₗ y`. `ContMDiffAt` at the
  chart image of `y` via `cotangentSection_contMDiffAt_iff`.
  **Supersedes the prior `chartCoeffAt` API from the 2026-05-16
  HolomorphicOneFormSubsingleton arc** — the local-coeff content is a
  proper extension; downstream `chartCoeffAt`-only consumers can rebase
  onto `localCoeff`.
* `HolomorphicOneFormChartCoeffOnTarget.lean` (338 LOC) —
  `localCoeff_contMDiffOn` on the whole chart target via the cocycle
  transport: at any `y' ∈ (chartAt ℂ y).source`, the chart-`y'` and
  chart-`y` frames are bridged by `coordChange_comp` applied through
  `ContMDiffAt.clm_apply` on the chart-`y'`-frame smoothness (canonical
  bridge) and chart-transition smoothness from
  `cotangentBundleCore.isContMDiff`.
* `CompactDiskChartCover.lean` (201 LOC) — `DiskChartCover X` structure:
  finite base points with outer/inner radii (`outerRadius > innerRadius
  > 0`), `closedDisk_in_target`, and chart-preimage of inner ball
  covers `X`. Existence via `IsCompact.elim_finite_subcover` on
  compact nonempty `X`.
* `DiskChartCoverSeminorm.lean` (252 LOC) — `localCoeffMax cover x om`
  = sup of `‖localCoeff om x ·‖` on the outer closed disk. Bounded
  via `IsCompact.exists_isMaxOn`. Subadditive / smul-homogeneous /
  sign-invariant via `Real.sSup_smul_of_nonneg` + standard sSup api.
* `DiskChartCoverSeminormAggregate.lean` (119 LOC) — `seminormVal cover
  om` = `Finset.sup'` of `localCoeffMax` over base points. Seminorm
  axioms (`_zero`, `_neg`, `_add_le`, `_smul`) via `Finset.sup'_le`,
  `Finset.sup'_congr`, `Finset.mul₀_sup'`.
* `DiskChartCoverCauchyEstimate.lean` (204 LOC) — Cauchy's first-derivative
  estimate on the inner disk via `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`
  with radius `R := outerRadius - dist w (center)`, sharpened to
  `localCoeffMax / (outerRadius - innerRadius)` via
  `div_le_div_of_nonneg_left`.
* `DiskChartCoverLipschitz.lean` (154 LOC) — Lipschitz bound on the
  inner disk via `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`
  + `norm_deriv_eq_norm_fderiv` to bridge `deriv` (used in chip 4) and
  `fderiv` (used by the convex MVT). Strengthened to
  `localCoeff_lipschitz_innerDisk_of_seminorm_le`: Lipschitz constant
  `M / (outerRadius - innerRadius)` independent of `om`.
* `DiskChartCoverArzela.lean` (188 LOC) — per-chart Arzelà-Ascoli via
  `BoundedContinuousFunction.arzela_ascoli`. Packages
  `localCoeff om x | _closedBall (innerRadius)` as
  `localCoeffBcf cover om hx : BoundedContinuousFunction
  ↥(closedBall (innerRadius)) ℂ`. Equicontinuity input via chip 5a's
  Lipschitz bound. Extracts a strictly monotone subsequence convergent
  in the BCF metric.
* `DiskChartCoverDiagonal.lean` (114 LOC) — diagonal subsequence
  convergent at every base point. `Finset.induction_on` builds the
  subseq one base point at a time, refining `ψ_S' ∘ φ` at each step.
* `DiskChartCoverPointwiseLimit.lean` (113 LOC) — `chosenBasePoint cover
  y` (via `Classical.choose` on `cover.covers y`) gives a base point
  with `y` in its inner-ball preimage. `chartLimit_tendsto` produces a
  scalar limit `c_y` for `localCoeff (om_n (ψ k)) (chosenBasePoint y)
  ((chartAt ℂ ...) y) → c_y`.
* `DiskChartCoverCLMLimit.lean` (192 LOC) — CLM-level pointwise limit:
  `(om_n (ψ k)).toFun y → T_lim_y` in `ℂ →L[ℂ] ℂ` (cotangent fibre).
  Uses `clm_eq_smulRight_value_at_one` (a `ℂ →L[ℂ] ℂ` CLM equals
  `smulRight 1 (T 1)`) + `coordChange_comp` cocycle inverse for the
  transport back from chart-`x_y` frame.
* `DiskChartCoverLimitAnalytic.lean` (173 LOC) — `bcfExtend cover g_lim`
  is `AnalyticOn ℂ` on the open inner ball. From BCF convergence on
  closedBall (uniform via `BoundedContinuousFunction.dist_coe_le_dist`)
  → `TendstoLocallyUniformlyOn` on ball (via
  `TendstoUniformlyOn.tendstoLocallyUniformlyOn` + `.mono`) →
  `DifferentiableOn` (via `TendstoLocallyUniformlyOn.differentiableOn`)
  → `AnalyticOn` (via `DifferentiableOn.analyticOn`).
* `DiskChartCoverLimitSection.lean` (79 LOC) — `limitSectionToFun cover
  om_n h_diag : ∀ y, CotangentSpace 𝓘(ℂ) y` via `Classical.choose` on
  the chip 5e existential. `limitSectionToFun_tendsto` packages
  pointwise convergence.
* `DiskChartCoverLimitSmooth.lean` (188 LOC) — chart-`x`-frame
  identification: for `y` in `chart-x.source` with chart-image in the
  inner closed disk, the chart-`x`-frame CLM at `y` of the limit
  equals `smulRight 1 (g_lim_x ⟨(chartAt ℂ x) y, _⟩)`. Proof:
  pointwise convergence (chip 5g) + continuity of `coordChange ...` +
  `tendsto_nhds_unique` against the BCF point-evaluation convergence.
* `DiskChartCoverLimitContMDiff.lean` (109 LOC) — composed
  `smulRight 1 (bcfExtend cover g_lim_x ((chartAt ℂ x) y'))` is
  `ContMDiffAt` at `y` in chart-`x` preimage of the open inner ball.
  Composition of: `chartAt ℂ x` ContMDiffAt (via
  `contMDiffOn_of_mem_maximalAtlas`), `bcfExtend` analytic → ContMDiffAt
  via `AnalyticAt.contDiffAt` + `contMDiffAt_iff_contDiffAt`, and
  `smulRight 1` continuous linear via
  `ContinuousLinearMap.smulRightL`.
* `DiskChartCoverLimitPackage.lean` (184 LOC) — **end-to-end packaging**:
  `limitHolomorphicOneForm cover om_n h_diag : HolomorphicOneForm X`.
  Uses mathlib's `Trivialization.contMDiffAt_section_iff` at
  `trivializationAt _ x` (auto `MemTrivializationAtlas`) for each
  base point `x = chosenBasePoint y`, identifies the snd component
  with the chip 5h+5f form on a neighborhood (via
  `cotangentBundle_trivializationAt_snd_apply` +
  `chartFrame_limit_eq_smulRight` + `bcfExtend_apply`), then applies
  `ContMDiffAt.congr_of_eventuallyEq` with chip 5i's composed
  smoothness.

Build green at **8802 jobs** (+16 from 8786 at session start), zero
`sorry`, zero `axiom`. **2948 LOC across 16 commits.** Remaining
~1,000-1,800 LOC: seminorm convergence (inner→outer multi-chart
bound) + NormedAddCommGroup + separating + Riesz
`FiniteDimensional.of_isCompact_closedBall₀`.

## 2026-05-16 — C3 structural reduction + chain-rule pathway segments 1-3 (13 chips, ~2,280 LOC, FF to `main`)

Two-tier delivery on top of the May-15 path-lift infrastructure, off
`origin/main` at `4081de3` via branch `feat/abel-generator-input-independence`,
fast-forward-merged into `main` at `9a9d45c`.

### Tier 1 — Structural reductions (3 chips, ~822 LOC)

* `Manifold/AbelGeneratorInputIndependence.lean` (+314 LOC) —
  `dischargedGenerators` and `AbelGeneratorPeriodCondition` are
  **invariant under the choice of `AbelJacobiInput`** (basePoint and
  pathFromBase). Proof: the difference of two AJ-chains for a divisor
  `D` has boundary `D.degree • (δ_{B'.base} − δ_{B.base})`; for
  principal divisors `(principalDivisorMap f).degree = 0` via
  `residue_theorem`, so the difference is a smooth cycle and its
  period vector lies in `periodLatticeImage`.

* `Manifold/AbelHypothesisFromLatticeWitness.lean` (+193 LOC) — C3
  reduces to **one named classical input** `AbelLatticeWitness X α h`
  (the Abel-forward existence statement, restricted to non-constant
  `f.toFun`). Constant-`toFun` discharge is internal via
  `principalDivisorMap_of_toFun_const`.

* `Manifold/AbelLatticeWitnessFromRegular.lean` (+192 LOC) +
  `Manifold/MeromorphicNonzeroConstantBridge.lean` (+181 LOC) —
  splits `AbelLatticeWitness` into:
  - `RegularLevelSetLatticeClause` (substantive analytic core: period
    of `regularLevelSetChain f hnc h0 h∞` ∈ `periodLatticeImage`).
  - `AbelLatticeWitnessCriticalCase` (small residual for `0`/`∞`
    critical, classically a Möbius substitution).
  Public bridge `not_isConstantMap_toRiemannSphere_of_toFun_nonconst`
  replicates `R4FibreSumBalance.lean`'s private `isConst_toFun_of_toRS_const`
  / `not_isConstantMap_toRS_infty` (chart-ball + `poles_finite`).

### Tier 2 — Chain-rule pathway segments 1-3 (10 chips, ~1,458 LOC)

Targets the substantive analytic content inside
`RegularLevelSetLatticeClause`. Builds the per-`t` chain-rule identity
on a sub-interval `Ioo 0 δ` end-to-end at the structural level.

* `Manifold/SmoothPathVelocityEqLocal.lean` (+132 LOC) +
  `Manifold/SmoothPathVelocityFromFun.lean` (+132 LOC) — generic
  primitives: `velocity`, `integrand`, and `∫_s^t integrand` are
  invariant under `ambient` pointwise-equality on `Icc s t` (template
  from `velocity_compSmoothPath_of_mem_Ioo`). The `_FromFun` variant
  compares against an external function `f : ℝ → X` (used for
  `f := sheet.g ∘ β ∘ σ`).

* `Manifold/SourceFiberPathAmbientSheetEq.lean` (+121 LOC) — lifts
  `sourceFiberPath_toPath_extend_eq_sheet_g_locally` from
  `toPath.extend` to `ambient`, then composes with
  `integrand_eq_of_ambient_eqOn_Icc_fun` to give the per-fiber-point
  integrand on `Ioo 0 δ` as a chart-level expression.

* `Manifold/SheetGBetaSigmaChainRule.lean` (+140 LOC) — chain rule
  `mfderiv (sheet.g ∘ β ∘ σ) t (1) = mfderiv sheet.g (β(σ t)) (mfderiv β (σ t) (mfderiv σ t (1)))`
  via two `mfderiv_comp_apply` applications, plus a specialised version
  at the base value with realified smoothness from
  `contMDiffAt_localSheet_g_at_basePoint` + `ContMDiffAt.complex_to_real`.

* `Manifold/SourceFiberPathIntegrandChainExpand.lean` (+135 LOC) —
  combines the integrand identification with the chain rule to fully
  expand the per-fiber-point integrand on `Ioo 0 δ`.

* `Manifold/SourceFiberPathIntegrandPullback.lean` (+103 LOC) —
  repackages via `applyCotangent_cotangentPullbackAt`:
  `integrand = applyCotangent (cotangentPullbackAt sheet_p.g (β(σ t)) ω) (β'(σ t) σ'(t))`.

* `Manifold/SumSourceFiberIntegrandPullback.lean` (+93 LOC) — pulls
  `applyCotangent` outside the sourceFiber sum via
  `applyCotangent_finset_sum`.

* `Manifold/LevelSetIntegralChainRuleStructural.lean` (+140 LOC) —
  **structural headline** `sum_sourceFiber_integrand_chain_at`:
  `∑_p integrand(sourceFiberPath p) ω t = applyCotangent (∑_p cotangentPullbackAt sheet_p.g (β(σ t)) ω) (β'(σ t) σ'(t))`.

* `Manifold/SourceFiberUniformDelta.lean` (+195 LOC) — uniform `δ`
  across sourceFiber via `Finset.min'`. Headlines: `perFiberDelta`,
  `uniformFiberDelta` (with `1`-fallback when empty), and the bounds
  `0 < uniformFiberDelta`, `uniformFiberDelta ≤ 1`,
  `uniformFiberDelta ≤ perFiberDelta p`.

* `Manifold/SourceFiberPathAmbientInjOn.lean` (+124 LOC) —
  `sourceFiberPath_toPath_extend_injOn_at`: generalises
  `sourceFiberPath_tgt_injOn` to **any** `t₀ ∈ Icc 0 1`.

* `Manifold/SourceFiberPathAmbientImageAt.lean` (+148 LOC) —
  lift-at-t, fiberFinset membership, `Set.InjOn`-form, and Finset
  image ⊆ `fiberFinset (β(σ t))`. The **injection half** of the
  sourceFiber ↔ `f⁻¹(β(σ t))` bijection is now structurally closed.

### Net status

* `AbelHypothesis B` (any `B`) ← `RegularLevelSetLatticeClause` +
  `AbelLatticeWitnessCriticalCase`. Two named classical inputs.
* Build green at 8808 jobs (+15 over baseline 8793). Zero `sorry`,
  zero `axiom`. No item flips (12/24 unchanged).
* Item-flip blockers for `RegularLevelSetLatticeClause`: the
  surjectivity half of the bijection (cardinality argument via
  `degreeFiber_eq_card_of_regular_witness`, or time-reversal
  generalisation), Lebesgue gluing across the
  `exists_subdivision_hurwitzPatching` cover, σ-reparametrisation,
  and the residue theorem for meromorphic 1-forms on `ℙ¹`.

### Hazards captured

* `Basis` is in `namespace Module` post-mathlib-refactor —
  `open Module` (or `open Submodule Module`) needed in chips that use
  `Basis` directly; transitive import is not enough.
* `Path.extend_extends` deprecated to `Path.extend_apply`.
* `LinearMap.map_smul_of_tower` (for `→ₗ[ℤ]` maps) requires
  `CompatibleSMul` typically unavailable for `SmoothChain` boundary;
  use the unbundled `map_smul` instead.

## 2026-05-16 — `HolomorphicOneFormSubsingletonOfSimplyConnected` arc (13 chips, ~1,510 LOC, direct to `main`)

End-to-end **analytic-side closure** of Item 14's reverse leg via the
simple-connectedness route. Reduces
`HolomorphicOneFormSubsingletonOfSimplyConnected X` (input (b) on the
simple-connectedness route in
`Topology/S2ImpliesGenus0FromSimplyConnected.lean`) to **one named
classical input**: smooth primitive existence under
simple-connectedness (`∀ om, ∃ F smooth with om.eval = mfderiv F`).

### Headline architectural reduction

```lean
theorem holomorphicOneFormSubsingletonOfSimplyConnected_of_primitiveExistence
    (h_primitive_exists : SimplyConnectedSpace X →
        ∀ om : HolomorphicOneForm X,
          ∃ F : X → ℂ,
            ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω F ∧
              ∀ x : X, om.eval x = mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) F x) :
    HolomorphicOneFormSubsingletonOfSimplyConnected X
```

Composed with the existing unconditional `simplyConnectedS2_holds`
(`SimplyConnectedS2Unconditional.lean`) and
`s2ImpliesGenus0_from_simplyConnected`, the reverse leg of Item 14
(`S2ImpliesGenus0 X`) now reduces to a **single named classical
input** — the smooth-Stokes / path-integral primitive on simply-
connected manifolds — captured in
`s2ImpliesGenus0_of_primitiveExistence`.

### Foundation: continuous-homotopy from simple-connectedness

* `Manifold/SmoothPathHomotopyFromSimplyConnected.lean` (~111 LOC) —
  for `[SimplyConnectedSpace X]`, any two `SmoothPath I X` with
  matching endpoints have *continuously* homotopic underlying `Path`s.
  Wraps mathlib's `SimplyConnectedSpace.paths_homotopic` and exposes a
  concrete `Path.Homotopy` witness plus the underlying
  `C(unitInterval × unitInterval, X)` map for downstream smooth-
  approximation chips. `apply_zero` / `apply_one` simp lemmas at the
  homotopy boundaries.

### Liouville chain — unconditional for `ContMDiff ω` on compact connected

* `Manifold/HolomorphicOneFormChartCoeff.lean` (~100 LOC) — general-X
  `HolomorphicOneForm.chartCoeffAt om x : ℂ → ℂ` with pointwise
  linearity (zero / add / neg / sub / smul). General-X analog of
  `RiemannSphere.chartNCoeff`.

* `Topology/LiouvilleForContMDiffOmega.lean` (~373 LOC) — the
  unconditional Liouville for `ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω F : X → ℂ`.
  Three layers:

  1. `mmeromorphicOn_univ_of_contMDiff_omega` +
     `mmeromorphicOrderAt_nonneg_of_contMDiff_omega` — chart-pullback
     analyticity gives `MMeromorphicOn _ univ` and order ≥ 0
     everywhere, via `contMDiff_omega_analyticAt_chart_pullback` +
     `AnalyticAt.meromorphicAt` + `AnalyticAt.meromorphicOrderAt_nonneg`.

  2. `MeromorphicNonzero.ofContMDiffOmega` +
     `contMDiff_omega_isConstant_of_nonvanishGerm` — Liouville
     conditional on a `nonvanishingGerm` hypothesis, via
     `MeromorphicNonzero.ofContinuousMeromorphic` and the existing
     `liouvilleOnCompactConnected_holds`.

  3. `mmeromorphicOrderAt_ne_top_of_contMDiff_omega_neverZero` +
     `contMDiff_omega_isConstant_of_neverZero` — discharges the
     `nonvanishingGerm` hypothesis for never-zero functions via
     `AnalyticAt.analyticOrderAt_eq_zero` (analyticOrderAt = 0 at a
     point where the value is non-zero).

  4. **`contMDiff_omega_complex_exp`** +
     **`contMDiff_omega_complex_exp_comp`** +
     **`contMDiff_omega_isConstant`** — **the unconditional Liouville**.
     Strategy: `exp ∘ F` is `ContMDiff ω` and never zero, so constant
     by layer 3; then `F x − F x₀ ∈ 2π i · ℤ` (kernel of `exp`); a
     continuous `F` into this discrete set is locally constant on
     each `Metric.ball (F x) (2π)`, hence constant by
     `IsLocallyConstant.eq_const` on `PreconnectedSpace X`.

### Closing composition: Subsingleton ⇐ primitive existence

* `Topology/SubsingletonFromPrimitiveExistence.lean` (~268 LOC) —

  - `HolomorphicOneForm.eq_zero_iff_eval` — general-X analog of
    `RiemannSphere.eq_zero_iff_eval_eq_zero`. `om = 0` iff
    `om.eval x = 0` pointwise; via `ContMDiffSection.ext`.

  - `HolomorphicOneForm.eq_zero_of_primitive_const` — pure algebra:
    `om.eval = mfderiv F` pointwise with `F` constant ⇒ `om = 0`, via
    `mfderiv_const`.

  - **`holomorphicOneForm_eq_zero_of_smooth_primitive`** — combines the
    unconditional Liouville (`F` constant) with `mfderiv_const`
    (constant derivative = 0) to land `om = 0`.

  - **`subsingleton_of_primitiveExistence`** — the headline. From
    `∀ om, ∃ F smooth primitive`, derive `Subsingleton`.

  - `HolomorphicOneForm.eq_zero_iff_eval_at_one` +
    `subsingleton_of_eval_at_one_eq_zero` — general-X analogs of the
    RS-specific scalarised variants.

  - **`holomorphicOneFormSubsingletonOfSimplyConnected_of_primitiveExistence`**
    — bridge to the named predicate from
    `S2ImpliesGenus0FromSimplyConnected.lean`.

  - **`s2ImpliesGenus0_of_primitiveExistence`** — full-arc composition.

### `complexChainPeriod` algebraic toolkit

* `Manifold/ComplexChainPeriodFormLinear.lean` (~244 LOC) — completes
  the form-side algebra of `complexChainPeriod c om` (cycle-level
  `complexPeriod` was already in
  `Manifold/ComplexPeriodPairing.lean` /
  `Manifold/ComplexPeriodSmulRight.lean`; this fills the chain level):

  - `complexChainPeriod_zero_right`, `_add_right`, `_neg_right`,
    `_sub_right`, `_smul_real_right` — pointwise linearity in `om`.
  - `complexChainPeriod_smul_complex_right` — full ℂ-scaling via the
    `realComponent_smul` / `imagComponent_smul` real-vs-complex
    mixing.
  - `complexChainPeriod_single_reverse` — `complexChainPeriod (single γ.reverse) om
    = -complexChainPeriod (single γ) om`. Via `SmoothPath.integrate_reverse`.
  - `complexChainPeriod_single_concat` — additivity over path
    concatenation. Via `SmoothPath.integrate_concat`.
  - `complexChainPeriodHomRight` (additive in form), `complexChainPeriodLinearMap`
    (ℂ-linear in form for fixed chain), `complexChainPeriodBilinear`
    (ℤ-additive in chain ⊗ ℂ-linear in form).

### `chartLocalPrimitive` infrastructure (E sub-chips)

* `Manifold/ChartLocalPrimitive.lean` (~236 LOC) —

  - **`chartLocalPrimitive`** — the candidate primitive
    `F(x) := complexChainPeriod (single γ_{x₀,x}) om` where
    `γ_{x₀,x} := SmoothPath.linearInChartSegment φ x₀ x` is the
    C^∞-bumped affine segment in chart coordinates (convex chart target
    discharges the segment-in-target precondition).

  - `bumpedSegment_self` — `bumpedSegment a a t = a` (algebraic).

  - `linearInChartSegment_self_{ambient_eq_on_unitInterval,
    ambient_eventuallyEq_const, velocity_of_mem_Ioo,
    integrand_of_mem_Ioo, integrate}` — the constant-ambient chain at
    coinciding endpoints, mirroring `SmoothPath.integrate_const`'s
    structure.

  - **`chartLocalPrimitive_self`** — `F(x₀) = 0` basepoint identity.

* `Manifold/ChartLocalPrimitiveSmoothness.lean` (~178 LOC) — joint
  continuity foundation for the eventual smoothness-of-F-in-endpoint
  argument:

  - `continuous_bumpedSegment_param z₀` — joint continuity of
    `(z, t) ↦ bumpedSegment z₀ z t` on `ℂ × ℝ`. Routes through
    `Complex.real_smul` to avoid the `ContinuousSMul ℝ ℂ` synth issue.

  - `continuous_chartSymm_bumpedSegment` — joint continuity of
    `(z, t) ↦ φ.symm (bumpedSegment z₀ z t)` on
    `φ.target ×ˢ Set.univ` (uses convex-target hypothesis).

  - `chartCoordVelocity z₀ z t := σ'(t) · (z − z₀)` +
    `continuous_chartCoordVelocity_param z₀` — the chart-coordinate
    path velocity (explicit formula, sidesteps the opaque
    `Classical.choose` of `SmoothPath.ambient`) and its joint
    continuity in `(z, t)`.

These joint-continuity foundations are the first sub-step of the
*continuity-of-`chartLocalPrimitive`-in-endpoint* sub-chip. Completing
the full `Continuous (fun x ↦ chartLocalPrimitive ... x)` requires
expressing `γ_z.integrand om` as a chart-coord formula equal a.e. on
`Ioo 0 1` to a jointly-continuous expression, then applying
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`.
The remaining gap is the chart-coord identification of `γ_z.velocity`
with `chartCoordVelocity` post-`dφ.symm`, which needs the
`mfderiv`-of-chart-inverse joint continuity in the bundle setting.

### Net effect on the strict-closed scoreboard

No item flips in this commit. Item 14 remains OPEN, but **input (b)
of the simple-connectedness route**
(`HolomorphicOneFormSubsingletonOfSimplyConnected X`) now reduces
cleanly to a single named classical input (primitive existence under
simple-connectedness). The full chain:

```
Item 14 (genus_eq_zero_iff_homeo)
  reverse leg ⇐ s2ImpliesGenus0_of_primitiveExistence (this commit)
    ⇐ SimplyConnectedS2 (discharged unconditionally 2026-05-15)
    ⇐ primitive existence under simple-connectedness ← THE remaining input
```

Build: 8793 jobs, zero `sorry`, zero `axiom`.

## 2026-05-16 — Local identification of `sourceFiberPath` with `sheet.g ∘ β ∘ σ` (1 chip, ~222 LOC, direct to `main`)

Concrete identification of the `Classical.choose`-opaque
`sourceFiberPath p` with the explicit local-sheet pullback
`sheet_p.g ∘ β ∘ Real.smoothTransition` on a sub-interval `[0, δ]`.

**New file** (`Manifold/MeromorphicNonzeroSourceFiberPathSheetEq.lean`,
~222 LOC):

* `sourceFiberPath_toPath_extend_eq_sheet_g_locally` — for `x` over
  `β 0` and the local sheet centered at `x`, there exists `δ ∈ (0, 1]`
  such that `(sourceFiberPath p).toPath.extend t = sheet.g (β (σ t))`
  pointwise for `t ∈ [0, δ]`.

The proof composes:

* Continuity of `β ∘ σ` at `0`, with `β 0 ∈ sheet.V` (sheet target
  neighborhood of `f x`), gives `δ₁ > 0` such that `β(σ [0, δ₁]) ⊆
  sheet.V`.
* Continuity of `toPath.extend` at `0`, with `x ∈ sheet.U` (sheet
  source neighborhood), gives `δ₂ > 0` such that `toPath.extend [0,
  δ₂] ⊆ sheet.U`.
* `δ := min (min δ₁ δ₂) 1`. On `[0, δ]`:
  - Both paths lift `β ∘ σ` (one via `sourceFiberPath_toPath_lifts`,
    the other via `sheet.rightInvOn` at the codomain side).
  - Both agree at `t = 0` (`(sourceFiberPath p).src = x` and
    `sheet.g (f x) = x` via `sheet.leftInvOn`).
* Apply `path_lift_eqOn_Icc_of_continuousOn` (just landed in
  `MeromorphicNonzeroPathLiftUniqueOnContinuousOn.lean`).

This is the **local** identification. The global identification on
`[0, 1]` requires a subdivision argument over a finite open cover of
the β-image by sheet domains (a future chip).

Net for the trace integral: combined with the scalar bridging in
`CotangentPullbackAtApply.lean`, the chain-rule identity
`(sourceFiberPath p).integrand om t = applyCotangent
(cotangentPullbackAt sheet_p.g (β(σ t)) om)
(mfderiv (β ∘ σ) ...)` becomes derivable on `Ioo 0 δ`, since on this
sub-interval the source-fiber-path coincides explicitly with the
sheet pullback.

Build: 8786 jobs (was 8785), zero `sorry`, zero `axiom`.

## 2026-05-16 — `ContinuousOn` variant of `path_lift_eqOn_Icc` (1 chip, ~131 LOC, direct to `main`)

Sister lemma to `path_lift_eqOn_Icc` that accepts `ContinuousOn γᵢ
(Icc a b)` instead of global `Continuous γᵢ`. The variant needed to
identify `(sourceFiberPath p).toPath` with the locally-defined
`sheet_p.g ∘ β ∘ σ` on sub-intervals where `sheet_p.g` is only
continuous on a neighborhood of `β(σ ·)`'s image.

**New file** (`Manifold/MeromorphicNonzeroPathLiftUniqueOnContinuousOn.lean`,
~131 LOC):

* `path_lift_eqOn_Icc_of_continuousOn` — two lifts of `β` on `Icc a b`
  that are merely `ContinuousOn (Icc a b)` (not globally continuous on
  ℝ) and agree at some `t₀ ∈ Icc a b` agree on all of `Icc a b`.

The proof mirrors the existing `path_lift_eqOn_Icc`'s clopen argument
in the subspace topology, with `continuousOn_iff_continuous_restrict`
replacing `Continuous.comp continuous_subtype_val` to extract
subspace-level continuity from the `ContinuousOn` hypothesis. The
`preimage_mem_nhds` step stays inside the subspace via the
subspace-restricted function's `ContinuousAt`.

This unblocks the next chip in the f_*ω stack: identification of
`(sourceFiberPath p).toPath` with `sheet_p.g ∘ β ∘ σ` on sub-intervals
where `β(σ ·)` lands in `sheet_p.V`. Combined with the scalar bridging
of `cotangentPullbackAt` + `traceAt` (in
`CotangentPullbackAtApply.lean`), the chain-rule statement
`(sourceFiberPath p).integrand om t = applyCotangent
(cotangentPullbackAt sheet_p.g (β t) om) (β.velocity t)` becomes
provable on each sub-interval, and via subdivision over the cover of
`[0, 1]` by sheet pre-images, globally on `Ioo 0 1`.

Build: 8785 jobs (was 8784), zero `sorry`, zero `axiom`.

## 2026-05-16 — Scalar evaluation of cotangent pullback and trace (1 chip, ~123 LOC, direct to `main`)

Scalar-level bridging lemmas between `cotangentPullbackAt`/`traceAt`
and the path-integral machinery (`applyCotangent` + `SmoothPath.integrand`).

**New file** (`Manifold/CotangentPullbackAtApply.lean`, 123 LOC):

* `applyCotangent_cotangentPullbackAt` — for any smooth `g : Y → X`,
  `y : Y`, `om : SmoothOneForm I X`, `v : E'`:
  `applyCotangent (cotangentPullbackAt g y om) v = applyCotangent (om (g y))
  (mfderiv g y v)`. Pure definitional unfold.

* `applyCotangent_finset_sum` — pairing is linear in the cotangent
  argument: `applyCotangent (Σ_i φ_i) v = Σ_i applyCotangent (φ_i) v`.
  Via `ContinuousLinearMap.sum_apply` + `cotangentEquiv`'s identity-as-CLM.

* `MeromorphicNonzero.applyCotangent_traceAt` — scalar pairing of the
  trace: `applyCotangent (traceAt f hnc hv om) w = Σ_{p ∈ fiberFinset}
  applyCotangent (cotangentPullbackAt sheet_p.g v om) w`. Follows from
  the linear-sum lemma applied to the definition of `traceAt`.

These are the scaffolding for the eventual Stokes-type integral
identity

  `(levelSetChain f β).integrate om = ∫ t in 0..1, applyCotangent
    (traceAt f hnc (hβ_reg t) om) (β.velocity t)`

which expresses the X-chain integral as a ℙ¹-line integral against the
trace 1-form `f_*ω`. The chain-rule piece tying
`(sourceFiberPath p).integrand om t` to `applyCotangent
(cotangentPullbackAt sheet_p.g (β t) om) (β.velocity t)` requires the
identification `(sourceFiberPath p).toPath ≡ sheet_p.g ∘ β ∘
Real.smoothTransition`, which is opaque (Classical.choose) in the
current infrastructure and will be the next chip's content.

Build: 8784 jobs (was 8783), zero `sorry`, zero `axiom`.

## 2026-05-16 — `SmoothOneFormOn` partial-section type (1 chip, ~74 LOC, direct to `main`)

Foundational chip for the trace `f_*ω` as a smooth 1-form on the open
subset `regularValueSet f`.

**New file** (`Manifold/SmoothOneFormOn.lean`, 74 LOC):

* `SmoothOneFormOn I X s` — a structure bundling:
  - `toFun : ∀ x : X, CotangentSpace I x` (global function-valued
    section; junk allowed outside `s`).
  - `contMDiffOn_section` : the total-space lift
    `x ↦ ⟨x, toFun x⟩ : X → Bundle.TotalSpace (E →L[ℝ] ℝ)
    (CotangentSpace I)` is `ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ⊤`
    on `s`.

This mirrors `SmoothOneForm I X` (which uses `ContMDiffSection` for
global sections) but allows the smoothness witness to be restricted to
a subset. Required for `f_*ω` whose natural domain is the open subset
`regularValueSet f ⊂ ℙ¹`.

Subsequent chips will:

* Show that the pointwise `traceAt f hnc hv om` (from
  `MeromorphicNonzeroTraceAt.lean`) assembles into a
  `SmoothOneFormOn 𝓘(ℝ, ℂ) RiemannSphere (regularValueSet f)`.
* Define `SmoothPath.integrateOn` for paths landing in the partial
  domain.

This file ships only the type definition + a `CoeFun` instance.
Algebra (`AddCommGroup`, `Module ℝ`) and a `restrictOn` map from
`SmoothOneForm` are deferred.

Build: 8783 jobs (was 8782), zero `sorry`, zero `axiom`.

## 2026-05-16 — Pointwise trace `f_*ω` at a regular value (1 chip, ~117 LOC, direct to `main`)

Combines `cotangentPullbackAt` with the fibre-finiteness infrastructure
to give the **pointwise trace** `f_*om` at a regular value.

**New file** (`Manifold/MeromorphicNonzeroTraceAt.lean`, 117 LOC):

* `fiberFinset f hv : Finset X` — the fiber `f⁻¹({v})` at a regular
  value `v`, packaged as a `Finset`. Uses
  `fiber_finite_of_mem_regularValueSet`.
* `mem_fiberFinset_iff` — membership characterised by
  `f.toRiemannSphere x = v`.
* `traceAt f hnc hv om : CotangentSpace 𝓘(ℝ, ℂ) v` — the trace, a
  finite sum of per-sheet `cotangentPullbackAt` contributions over the
  fiber. Each sheet's local inverse comes from
  `f.localSheetData_at_regular hnc hp_reg` where `hp_reg` is derived
  from `mem_regularSet_of_preimage_regularValue`.
* `traceAt_zero`, `traceAt_add`, `traceAt_smul` — ℝ-linearity of the
  trace in the 1-form argument, via the underlying
  `cotangentPullbackAt_{zero, add, smul}` + `Finset.sum_{zero,
  add_distrib, smul_sum}`.

This is the **pointwise** `f_*ω`. Smoothness of `v ↦ traceAt f hnc hv
om` as a function of `v` is a separate downstream layer.

Build: 8782 jobs (was 8781), zero `sorry`, zero `axiom`.

## 2026-05-16 — Pointwise cotangent pullback primitive (1 chip, ~94 LOC, direct to `main`)

The foundational pointwise primitive for the trace construction
`f_*ω` on regular values.

**New file** (`Manifold/CotangentPullbackAt.lean`, 94 LOC):

* `cotangentPullbackAt (g : Y → X) (y : Y) (om : SmoothOneForm I X) :
  CotangentSpace I' y` — defined as `(om (g y)).comp (mfderiv g y)`.
  Takes a smooth map between real C^∞ manifolds and a 1-form on the
  codomain; produces the pulled-back cotangent vector at the domain
  point.
* `cotangentPullbackAt_zero` — zero 1-form pulls back to zero.
* `cotangentPullbackAt_add` — additivity in the 1-form.
* `cotangentPullbackAt_smul` — ℝ-linearity in the 1-form.

This is the per-point/per-sheet primitive for the trace `f_*ω` at a
regular value `y`: summing `cotangentPullbackAt sheet.g y om` over the
finite fiber (`f.sourceFiber y`) of `f` produces the trace cotangent.
Smoothness of the trace as a function of `y` is a separate layer
(needs the smooth local-sheet structure + sum continuity).

Build: 8781 jobs (was 8780), zero `sorry`, zero `axiom`.

## 2026-05-16 — Real-model RS manifold + open-set realification (1 chip, ~96 LOC, direct to `main`)

Foundation chip for downstream `SmoothOneForm 𝓘(ℝ, ℂ) RiemannSphere`
work (in particular the `f_*ω` trace construction on `regularValueSet`).

**New file** (`Manifold/RiemannSphereRealManifold.lean`, 96 LOC):

* Documents the auto-derived real-model RS instances via `inferInstance`
  examples for `n : WithTop ℕ∞`, `∞`, `⊤`. The instance chain is
  `RiemannSphere.instIsManifold` (complex-analytic ω) →
  `complexManifoldRealification` (generic conversion) →
  `IsManifold 𝓘(ℝ, ℂ) n RiemannSphere`. No new content — just a
  discoverable reference point for downstream files.

* `ContMDiffOn.complex_to_real_of_isOpen` — sister lemma to the
  existing pointwise `ContMDiffAt.complex_to_real` (in
  `Manifold/ContMDiffRealification.lean`), generalised to smoothness
  on an *open* subset. Converts `ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g u`
  to `ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ g u` via pointwise application of
  `ContMDiffAt.complex_to_real` on each `x ∈ u` (using `IsOpen.mem_nhds`
  to extract `ContMDiffAt` from `ContMDiffOn`).

This is the workhorse for converting the complex-analytic local-sheet
smoothness (`exists_contMDiffOn_localSheet_g_near_basePoint` produces
`ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω`) into the real-smooth regularity
required by `SmoothOneForm` pullbacks.

Build: 8780 jobs (was 8779), zero `sorry`, zero `axiom`.

## 2026-05-16 — Concrete regular level-set chain (1 chip, ~146 LOC, direct to `main`)

Wires the β-existence chip into the level-set chain construction.

**New file** (`Manifold/MeromorphicNonzeroConcreteLevelSetChain.lean`, 146 LOC):

* `regularBeta f hnc h0_reg h_inf_reg : ℝ → RiemannSphere` — the
  `Classical.choose` extraction of the regular path from
  `exists_regular_path_zero_to_infty`.
* `regularBeta_{smooth, zero, one, regular}` — the four spec properties,
  re-exported from `Classical.choose_spec` as standalone lemmas
  (`@[simp]` on the endpoint ones).
* `regularLevelSetChain f hnc h0_reg h_inf_reg : SmoothChain 𝓘(ℝ, ℂ) X`
  — the level-set chain on the concrete β, built by composing
  `f.levelSetChain` with the smooth + regular witnesses.
* `boundary_regularLevelSetChain` — the boundary identification
  `(boundary regularLevelSetChain).toFun x = -principalDivisorMap f x`
  pointwise. One-line composition of step 7d-d's
  `boundary_levelSetChain_eq_neg_principalDivisorMap_pointwise` with
  `regularBeta_zero` and `regularBeta_one`.

**Net.** For `f` with `0, ∞ ∈ regularValueSet`, the boundary clause of
`h_struct` in `abelGeneratorPeriodCondition_of_levelSet_lattice` is
now **mechanically discharged** for the explicit witness
`Z := f.regularLevelSetChain hnc h0_reg h_inf_reg`. Only the
**lattice-period clause** remains — the analytical residual
(`f_*ω` SmoothOneForm construction + Stokes/residue argument).

Build: 8779 jobs (was 8778), zero `sorry`, zero `axiom`.

## 2026-05-16 — Regular β: 0→∞ existence on ℙ¹ (1 chip, ~431 LOC, direct to `main`)

Lands the **β-existence input** for step 9's structural reduction. Given
`f : MeromorphicNonzero X` non-constant with both `0` and `∞` regular
values, produces a smooth `β : ℝ → RiemannSphere` with `β 0 = 0`,
`β 1 = ∞`, and `β t ∈ f.regularValueSet` for all `t ∈ [0, 1]`.

This is the β that the level-set chain construction
(`MeromorphicNonzeroLevelSetChain.lean` + downstream) consumes. Combined
with step 7d-d's boundary identification, it concretely wires the
boundary clause of `h_struct` in
`abelGeneratorPeriodCondition_of_levelSet_lattice` — only the
**lattice-period clause** for `levelSetChain f β` remains as the
analytical residual.

**New file** (`Manifold/MeromorphicNonzeroRegularPath.lean`, 431 LOC):

* `exists_s_avoiding_critical` — for any finite `S ⊂ ℂ`, there exists
  `s : ℝ` such that `s * w.im ≠ w.re` for every `w ∈ S` with `w.im > 0`.
  (Pure cardinality: ℝ infinite, the forbidden set `{w.re / w.im}` finite.)
* `chartN_segment_mem_regularValueSet` — for such `s`, the chartN
  segment `{t (s + i) | t ∈ [0, 1]}` in ℂ avoids `chartN`-images of
  critical values. Uses `0 ∈ regularValueSet` to kill the `t = 0`
  endpoint.
* `chartS_segment_mem_regularValueSet` — symmetric. The chartS segment
  from `1/(s + i)` to `0` avoids `chartS`-images of critical values
  via the reciprocal formula `arg(1/w) = -arg w` (reduced to the same
  `s = w.re/w.im` condition by direct computation). Uses
  `∞ ∈ regularValueSet` for the `0` endpoint.
* `exists_regular_path_zero_to_infty` — the headline. Builds two
  `SmoothPath.linearInChartSegment` paths through the bridge point
  `r := some(s + i)`, concatenates via `SmoothPath.concat`, and extracts
  the underlying `ℝ → RS` ambient smooth function from
  `SmoothPath.ambient`. Endpoint identities via
  `ambient_eq_on_unitInterval` + `Path.source'/target'`. Regularity on
  `[0, 1]` by case-splitting `t ≤ 1/2` vs `t > 1/2` and applying the two
  segment lemmas to each half's chart-pullback.

Build: 8778 jobs (was 8777), zero `sorry`, zero `axiom`.

## 2026-05-16 — `h_AJ_boundary` discharged (1 chip, ~125 LOC, direct to `main`)

Discharges the second named-hypothesis input of step 9
(`abelGeneratorPeriodCondition_of_levelSet_lattice`) unconditionally.

After yesterday's C3 staircase steps 1–9 landed, step 9's structural
reduction still took two named inputs: `h_struct` (existence of a chain
`Z` with the boundary identity AND lattice period) and `h_AJ_boundary`
(boundary of `principalDivisorAJChain` = principal divisor pointwise).
This chip dispatches `h_AJ_boundary` to a discharged lemma, leaving only
the analytical-content `h_struct` (`f_*ω` pushforward + Stokes/residue)
as the residual.

**New file** (`Manifold/PrincipalDivisorAJChainBoundary.lean`, 125 LOC):

* `AbelJacobiInput.boundary_principalDivisorAJChain_apply_of_degree_zero`
  — for any `D : Div X` with `D.degree = 0`,
  `(boundary (principalDivisorAJChain D)).toFun y = D y` pointwise. Pure
  ℤ-linearity: unfold the sum, push `boundary` through with
  `LinearMap.map_smul`, evaluate at `y`, split as `D y − D.degree •
  δ_basePoint(y)`, and absorb the second term via `hD : D.degree = 0`.
* `AbelJacobiInput.boundary_principalDivisorAJChain_principalDivisorMap`
  — the `D := principalDivisorMap f` specialisation, discharging the
  degree hypothesis via `JacobianChallenge.residue_theorem`.

**Refactor**
(`Manifold/MeromorphicNonzeroAbelGeneratorFromLevelSet.lean`): the
`h_AJ_boundary` parameter is dropped from
`abelGeneratorPeriodCondition_of_levelSet_lattice`; the proof now uses
the discharged lemma internally. No callers had bound the old
signature.

**Net.** Step 9's structural reduction now takes one named-hypothesis
input (`h_struct`) instead of two. The residual analytical content for
full step 9 — the `f_*ω` pushforward 1-form construction + Stokes on
β: 0 → ∞ in ℙ¹ — is unchanged in scope (~800–1,500 LOC by the
CLOSURE_MAP §F.3 estimate).

## 2026-05-15 — C3 staircase steps 1–9 fully landed (15 chips, ~2,582 LOC, `feat/c3-staircase` direct to `main`)

Discharges the entire 9-step C3 general-genus staircase (HANDOFF
`HANDOFF_2026_05_15_C3_PATH_LIFT.md`) as 15 chip files. Step 7 was
split into 7a/b/c/d-a/d-b/d-c/d-d to keep each chip standalone-useful;
step 9 landed as a structural reduction with a named-hypothesis
`h_struct` input for the residual `f_*ω + Stokes` content.

**Path-lift trunk** (steps 1–4, ~823 LOC):

* `MeromorphicNonzeroPathLiftClosed.lean` (331 LOC) — closedness
  `sSup ∈ liftReachable` via `CompactSpace.tendsto_subseq` (with
  `ChartedSpace.secondCountable_of_sigmaCompact` deriving
  SecondCountable ⇒ FirstCountable ⇒ SeqCompact on `X`) + clip+if_le
  patching from chip 24 of c3_path_lift.
* `MeromorphicNonzeroPathLiftExistsOnIcc.lean` (117 LOC) — clopen
  finish `sSup = T` (openness contradicts strict <T) + headline
  `exists_continuous_lift_on_Icc`.
* `MeromorphicNonzeroPathLiftSmoothOnIcc.lean` (225 LOC) — smooth
  upgrade `ContMDiffOn ∞ γ (Icc 0 T)` via per-point
  `ContMDiffWithinAt.congr_of_eventuallyEq_of_mem` against
  chip 15's local smooth lift.
* `MeromorphicNonzeroPathLiftSmoothPath.lean` (~150 LOC, also exposes
  the toPath lift identity via a follow-up amend) —
  `exists_smoothPath_of_lift_on_unitInterval` packages the smooth lift
  into `SmoothPath 𝓘(ℝ, ℂ) X` via the `Real.smoothTransition` σ
  reparametrisation trick (γ ∘ σ is globally `ContMDiff ∞` because
  σ([0,1]) ⊆ [0,1] and γ is `ContMDiffOn ∞` on `[0,1]`).

**Level-set chain** (steps 5–6, ~281 LOC):

* `MeromorphicNonzeroLevelSetChain.lean` (~170 LOC) — `sourceFiber`
  as Finset, `sourceFiberPath` classical-chosen per fiber point,
  `levelSetChain` as the Finset sum, plus `sourceFiberPath_toPath_lifts`
  bridging to the underlying β ∘ σ reparametrisation.
* `MeromorphicNonzeroLevelSetChainBoundary.lean` (111 LOC) —
  `sourceFiberDivisor` + `targetFiberDivisor` + `boundary_levelSetChain
  = target - source` via `boundary_single` linearity.

**Target-map bijection** (steps 7a/b/c, 584 LOC):

* `MeromorphicNonzeroLevelSetTargetInjective.lean` (151 LOC) —
  `sourceFiberPath_tgt_injOn` via `Path.extend` + `path_lift_eqOn_Icc`
  on `β ∘ Real.smoothTransition`.
* `MeromorphicNonzeroLevelSetTargetSurjective.lean` (240 LOC) —
  `sourceFiberPath_tgt_surjOn` via time-reverse β + step 4 at y +
  step 2 raw lift + double `path_lift_eqOn_Icc` (one for β ∘ τ from
  back-path, one for β ∘ σ from forward-path, common γ_raw).
* `MeromorphicNonzeroLevelSetTargetFiber.lean` (193 LOC) — `targetFiber`
  Finset, `sourceFiberPath_tgt_image_eq_targetFiber` Finset bijection,
  `boundary_levelSetChain_eq_fiberDiff` headline.

**Principal-divisor identification** (step 7d, 643 LOC):

* `MeromorphicNonzeroPrincipalDivisorOffFiber.lean` (110 LOC) — order
  = 0 off-fiber via `tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero`
  using `f.regular_continuousAt` for chart-pullback continuity.
* `MeromorphicNonzeroPrincipalDivisorAtZero.lean` (198 LOC) — order
  = 1 at simple zero via chart-pullback eventual equality
  (`chartPullback_eventuallyEq_toFun_at_finite`) +
  `AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero` +
  `deriv_chartPullback_ne_zero_of_regular`.
* `MeromorphicNonzeroPrincipalDivisorAtPole.lean` (188 LOC) — order
  = -1 at simple pole via `MMeromorphicAt.iff_of_isManifold`
  (chart-independence lifting `f.toFun ∘ chart.symm` to
  `MeromorphicOn chart.target`) +
  `MeromorphicOn.eventually_analyticAt` (pole isolation) +
  `meromorphicOrderAt_inv` (sign flip).
* `MeromorphicNonzeroLevelSetPrincipalDivisorIdentification.lean`
  (147 LOC) — pointwise `(∂ levelSetChain) x = -(principalDivisorMap
  f) x` via `boundary_levelSetChain_eq_fiberDiff` + case split on
  fiber membership + Finset.sum_ite_eq' evaluation of the indicator
  Finsupp sums.

**Integral linearity + structural reduction** (steps 8, 9, 236 LOC):

* `MeromorphicNonzeroLevelSetIntegrate.lean` (98 LOC) —
  `integrate(levelSetChain)` Finset-sum expansion via
  `SmoothChain.integrateLinearMap` ℤ-linearity.
* `MeromorphicNonzeroAbelGeneratorFromLevelSet.lean` (138 LOC) —
  `abelGeneratorPeriodCondition_of_levelSet_lattice`: if any chain
  Z exists with boundary = -principalDivisorMap f (Finsupp pointwise)
  AND `complexChainPeriodVector α Z ∈ periodLatticeImage`, then
  `AbelGeneratorPeriodCondition B` holds. Cycle Z + AJ has boundary
  0, period in lattice tautologically, linearity gives AJ's period
  ∈ lattice − period(Z) ⊆ lattice (AddSubgroup.sub_mem).

**LOC calibration:** every chip landed within or below HANDOFF
estimate. Aggregate session LOC (~2,582) vs aggregate HANDOFF
estimate (1,830–3,220 LOC for steps 5–9) is in the middle of the
estimate range — first session this has held cleanly.

**Build:** `taskpolicy lake build` green at 8776 jobs across 17 chip
+ doc commits. Zero `sorry`, zero `axiom`. Items 4/5/10/11/12/13
remain STUB/OPEN — these flip when the residual `f_*ω + Stokes`
content for `h_struct`'s lattice clause discharges.

## 2026-05-15 — `SimplyConnectedS2` UNCONDITIONAL via polygonal approximation (15 chips, branch `feat/phase3-s2-simply-connected`)

Closes the Phase-3 item-14 reverse-leg's named hypothesis
`SimplyConnectedS2 = SimplyConnectedSpace JacobianChallenge.StandardS2`
unconditionally at this mathlib pin. The simple-connectedness route in
`Topology/S2ImpliesGenus0FromSimplyConnected.lean` now reduces to a
single remaining input — the analytic chain
`HolomorphicOneFormSubsingletonOfSimplyConnected X` — instead of two.

**Reduction-chain chips** (chips 1-3, ~390 LOC).

* `SimplyConnectedS2Reduction.lean` — narrows `SimplyConnectedS2` to
  `S2LoopsNullHomotopic` by discharging path-connectedness of the
  unit sphere in `EuclideanSpace ℝ (Fin 3)`
  (`isPathConnected_sphere` + rank ≥ 2 + subtype lift).
* `S2PuncturedSimplyConnected.lean` — for any unit `v`, the punctured
  sphere `↥(stereographic hv).source` is `ContractibleSpace` via the
  stereographic homeomorphism into `(ℝ ∙ v)ᗮ` (a real top vec space),
  hence `SimplyConnectedSpace`. `s2LoopAvoidingNullHomotopic` follows
  by lifting the loop through the inclusion + `paths_homotopic` +
  `Path.Homotopic.map`.
* `S2LoopsNullHomotopicReduction.lean` — single-hypothesis composition.

**Smoothing-infrastructure chips** (chips 4a-c, ~430 LOC).

* `S2TwoChartCover.lean` — two stereographic charts at `v` and `-v`
  cover the sphere (witness `ne_neg_self_of_norm_one`).
* `S2LoopLebesgueSubdivision.lean` — `lebesgue_number_lemma` applied
  to the two-chart preimage cover of `unitInterval`, converted to a
  metric `δ > 0` via `Metric.mem_uniformity_dist`.
* `S2LoopChartPartition.lean` — equidistant `Fin N → Set` chart
  assignment with `1/N < δ` from `exists_nat_gt`; midpoint argument
  bounds each `[k/N, (k+1)/N]` inside `Metric.ball (ck k) δ`.

**Smoothing reduction** (chips 4e, 4i', 4i'', ~250 LOC).

* `S2LoopAvoidingFromNonSurjective.lean` — reduces
  `S2LoopHomotopicToAvoidingLoop` to the pure-topology hypothesis
  `EveryS2LoopHomotopicToNonSurjective`. Picks the missing point as
  the chart's pole.
* `S2SingleChartLoopNonSurjective.lean` — single-chart corollary.
* `S2PartitionVertices.lean` — `Fin (N+1) → unitInterval`, `k ↦ ⟨k/N, _⟩`.

**Dimensional argument** (chips 4d, 4f, 4g, 4h, ~580 LOC).

* `S2EquatorialBeltPathConnected.lean` — `S² ∖ {v, -v}` is
  path-connected. Uses `finrank_orthogonal_span_singleton` to show
  `(ℝ ∙ v)ᗮ` has rank 2, then `isPathConnected_compl_singleton_of_one_lt_rank`
  on `(ℝ ∙ v)ᗮ ∖ {0}` and transport via the stereographic
  homeomorphism (using `stereographic_apply_neg` to identify
  `⟨-v, _⟩ ↦ 0`).
* `S2StereographicStraightLine.lean` — canonical
  `(stereographic hv).symm`-pullback of a line segment in `(ℝ ∙ v)ᗮ`
  as a `Path p q`. Any in-chart `γ` is `Path.Homotopic` to it via
  chip 2's `S2Punctured.instSimplyConnectedSpace`.
* `S2SegmentEmptyInterior.lean` — line segment in `(ℝ ∙ v)ᗮ` has
  empty interior. Uses `Convex.interior_nonempty_iff_affineSpan_eq_top`
  + `vectorSpan_pair` + `finrank_span_singleton ≤ 1` vs `finrank ⊤ = 2`.
* `S2StraightLineNowhereDense.lean` — transports the segment's
  empty-interior result to the sphere level via the stereographic
  homeomorphism + `Homeomorph.isOpenMap`.

**Polygonal closure** (chip 4j, ~370 LOC + capstone, ~50 LOC).

* `S2EveryLoopHomotopicNonSurjective.lean` — `everyS2LoopHomotopicToNonSurjective_holds`.
  Builds `γ' := Path.concat (γ ∘ partitionVertex) stereographicStraightLine_k . cast _ _`,
  shows `γ ≃ γ'` via `Path.Homotopic.concat_subpath.symm + concat_hcomp`
  + a `Path.cast = γ.subpath (pV 0) (pV last)` path-equality via
  `DFunLike.coe_injective + Icc.coe_convexCombo + ring`. Cast across
  endpoint types via local `homotopyRecastEndpoints` helper
  (reusing the underlying continuous function). Non-surjectivity
  via `range_concat_subset_iUnion_of_pos + interior_iUnion_closed_empty`
  Baire-style induction.
* `SimplyConnectedS2Unconditional.lean` — capstone:
  `simplyConnectedS2_holds : SimplyConnectedS2` by composing
  `everyS2LoopHomotopicToNonSurjective_holds` with the chip-1/3/4e
  reduction chain. **Zero hypotheses.**

Total: **15 chips, ~3000 LOC, zero `sorry`, zero `axiom`**, all
locally verified via `LEAN_NUM_THREADS=1 lake env lean FILE.lean`.

## 2026-05-15 — C3 sub-arc: algebra closure + path-lift infrastructure (25 chips)

Continued past the 19-chip set above with six further chips on the
inductive global path lift:

* `Manifold/MeromorphicNonzeroPathLiftAtPoint.lean` (chip 20) —
  `exists_sheet_data_extending_to_right` and
  `extend_continuous_lift_to_right`: per-point extension primitive
  using local sheet at the current lift endpoint plus chip 19.

* `Manifold/MeromorphicNonzeroPathLiftSequencePatch.lean` (chip 21) —
  `lifts_agree_globally` and `lifts_agree_at`: choice-independence of
  patched lifts via chip 16 (uniqueness).

* `Manifold/MeromorphicNonzeroPathLiftUniqueOn.lean` (chip 22) —
  `path_lift_eqOn_Icc`: strengthens chip 16 to lifts defined only on
  `Icc a b`.  Clopen argument inside the connected subspace.

* `Manifold/MeromorphicNonzeroPathLiftGlobal.lean` (chip 23) —
  `liftReachable f β x₀ T` definition + `zero_mem_liftReachable` +
  `liftReachable_downward_closed`.

* `Manifold/MeromorphicNonzeroPathLiftGlobalOpen.lean` (chip 24) —
  `liftReachable_extends_right`: openness via clip+if_le construction.
  Globally-continuous lift built as `if t ≤ b then γ t else sheet.g
  (β (clip t))` where `clip t := max b (min (b + ε) t)` keeps β
  inside `sheet.V`; both pieces globally continuous + agreement at b
  ⇒ `Continuous.if_le`.

* `Manifold/MeromorphicNonzeroPathLiftGlobalClosed.lean` (chip 25) —
  `liftReachable_subset_Icc`, `liftReachable_bddAbove`,
  `sSup_liftReachable_le`, `sSup_liftReachable_nonneg`: boundedness +
  sSup bounds setting up the closedness/clopen argument for the
  global lift.

**Net open content after the 25 chips.** Closing C3 (general genus)
reduces to: (i) the substantive closedness `sSup ∈ liftReachable`
(local-sheet-limit argument); (ii) clopen+univ in connected
`[0, T]`; (iii) smoothness upgrade of the global lift to SmoothPath
regularity; (iv) `levelSetChain f β` definition; (v) boundary
computation + Stokes/lattice argument.

Build at HEAD: `taskpolicy lake build` green, 8746 jobs. Zero `sorry`,
zero `axiom`. +~2,900 LOC across 19 new files today.

## 2026-05-15 — C3 sub-arc: algebra closure + path-lift infrastructure (19 chips)

Extending the same-day work past the 11-chip set, eight further chips
landed on the path-lift portion:

* `Manifold/MeromorphicNonzeroLocalSheetSmooth.lean` (chip 12, ~190 LOC)
  — `contMDiffAt_localSheet_g_at_basePoint`: pointwise `ContMDiffAt ω`
  of the manifold local-sheet inverse at the base point.  Via
  `contMDiffAt_omega_of_analyticAt_chart_pullback` applied to
  `manifoldLocalOph.symm`, with the chart pullback shown to locally
  equal `φ.symm` (planar inverse from chip 6) on an open subset of `ℂ`
  containing `d v₀`.

* `Manifold/MeromorphicNonzeroSmoothLocalLift.lean` (chip 13, ~90 LOC)
  — `contMDiffAt_local_lift_at_basepoint`: the lift `sheet.g ∘ β` is
  `ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞` at `t₀`.  Composition: chip 12 +
  `ContMDiffAt.complex_to_real` (realification) + `ContMDiffAt.comp`.

* `Manifold/MeromorphicNonzeroLocalSheetSmoothOn.lean` (chip 14, ~65
  LOC) — `exists_contMDiffOn_localSheet_g_near_basePoint`: extracts
  open nbhd of `v₀` with `ContMDiffOn 𝓘(ℂ, ℂ) ω sheet.g` via
  `contMDiffAt_iff_contMDiffOn_nhds` (valid at `ω ≠ ∞`).

* `Manifold/MeromorphicNonzeroSmoothLocalLiftOn.lean` (chip 15, ~125
  LOC) — `exists_contMDiffOn_local_lift`: globally `ContMDiff` β yields
  a smooth (`ContMDiffOn ∞` in SmoothPath regularity) local lift on
  an open neighbourhood `W ⊆ ℝ` of `t₀`, via `ContMDiffOn.contMDiffAt`
  + complex-to-real realification + `ContMDiffAt.comp` at every `t ∈ W`.

* `Manifold/MeromorphicNonzeroPathLiftUnique.lean` (chip 16, ~120
  LOC) — `path_lift_unique`: two continuous lifts of a regular-valued
  `β` agreeing at one point agree everywhere.  Clopen argument on
  the agreement set: closed (equalizer into T2), open (local
  injectivity at regular preimages), non-empty, in connected `ℝ`.

* `Manifold/MeromorphicNonzeroPathLiftPartition.lean` (chip 17, ~105
  LOC) — `exists_subdivision_hurwitzPatching`: Lebesgue-number-lemma
  subdivision of `unitInterval` such that on each subinterval, `β`
  maps into one `HurwitzPatchingData.W`.

* `Manifold/MeromorphicNonzeroPathLiftSingleSheet.lean` (chip 18, ~85
  LOC) — `exists_continuous_lift_single_sheet`: if `β` maps the entire
  `ℝ` into one local sheet's `V`-set with `x₀` in its `U`-set, then
  `sheet.g ∘ β` is a continuous global lift.

* `Manifold/MeromorphicNonzeroPathLiftExtend.lean` (chip 19, ~145
  LOC) — `extend_lift_across_sheet`: the inductive step.  Given a
  continuous lift on `Icc a b` and `β` mapping `Icc b c` into one
  local sheet's `V`, the piecewise function `if t ≤ b then γ t else
  sheet.g (β t)` is `ContinuousOn (Icc a c)` and lifts `β` there.
  Continuity via `ContinuousOn.if` + agreement at `b` from
  `leftInvOn`.

**Net open content after the 19 chips.** Closing C3 (general genus)
reduces to: (i) iterate `extend_lift_across_sheet` across the
partition from chip 17 to produce a global continuous lift on
`unitInterval`; (ii) upgrade to `SmoothPath`-class smoothness using
chip 15 at every junction; (iii) define `levelSetChain f β` as the
sum-over-fiber of single-preimage smooth lifts; (iv) compute the
chain boundary; (v) the Stokes / lattice argument for the period
vector.  The path-lift infrastructure for (i)–(ii) is now in-tree
axiom-free; the level-set chain Stokes work (iii)–(v) is the
remaining classical content.

Build at HEAD: `taskpolicy lake build` green, 8740 jobs. Zero `sorry`,
zero `axiom`. +~2,200 LOC across 14 new files.
## 2026-05-15 — C3 sub-arc: algebra closure + path-lift infrastructure (11 chips)

Six chips landed reducing the open content of `AbelHypothesis B`
(the C3 named hypothesis) from "discharge `AbelGeneratorPeriodCondition
B` for every `f : MeromorphicNonzero X`" to "discharge it on a
multiplicative generating set of *non-constant* meromorphic functions."
The chips also lay analytic foundations (regular-value set, planar
local biholomorphism at every regular point) consumed by the level-set
chain construction.

**Algebra-side closure** (3 chips, `Manifold/AbelGeneratorDischargedSet.lean`,
~280 LOC).

* `dischargedGenerators B := { f | period vector of AJ chain of (f) ∈
   periodLatticeImage }`. Closed under `1` (`one_mem`), constants
   (`const_mem`), `*` (`mul_mem`), `invMer` (`invMer_mem`), and
   quotients (`mul_invMer_mem`).
* `mem_dischargedGenerators_of_principalDivisor_zero` — vacuous-divisor
   discharge.
* `principalDivisorMap_of_toFun_const` + `toFun_const_mem_dischargedGenerators`
   — closes the constant-function case via
   `mmeromorphicOrderAt_const_ne_zero`.
* `toFun_ne_const_zero` — the `c = 0` branch is blocked by
   `nonvanishing_germ`.
* `abelGeneratorPeriodCondition_iff_dischargedGenerators_eq_univ` and
  `abelGeneratorPeriodCondition_of_forall_nonconst_toFun` — case-split
   reduction to the non-constant `toFun` case.

**Regular-value set** (1 chip,
`Manifold/MeromorphicNonzeroRegularValueSet.lean`, ~120 LOC).

* `MeromorphicNonzero.regularValueSet f := (f.criticalValues)ᶜ`.
* `criticalValues_finite` / `criticalValues_isClosed` /
  `regularValueSet_isOpen` under non-constancy.

**Planar local biholomorphism at every regular point** (2 chips,
~280 LOC).

* `MeromorphicNonzero.chartPullback f x := (chartAt ℂ (f.toRiemannSphere
   x)) ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm`
  (`Manifold/MeromorphicNonzeroLocalBiholomorphism.lean`).
* `analyticAt_chartPullback` — ω-smoothness ⇒ analytic chart pullback.
* `deriv_chartPullback_ne_zero_of_regular` — non-zero derivative at
   every regular point, pulled directly from `DerivBridgeData.hCompat`
   via the existing `criticalSet_finite_unconditional` infrastructure.
* `exists_local_biholomorphism_chartPullback` — planar local inverse via
   `AnalyticAt.exists_local_biholomorphism`.
* `chartPullback_oph` (`Manifold/MeromorphicNonzeroLocalSheet.lean`,
   ~120 LOC) — packages the planar inverse as a canonical
   `OpenPartialHomeomorph ℂ ℂ` via
   `HasStrictFDerivAt.toOpenPartialHomeomorph`.

**Manifold-level local sheet** (1 chip, +223 LOC inside `MeromorphicNonzeroLocalSheet.lean`).

* `manifoldLocalOph` — `OpenPartialHomeomorph X RiemannSphere` built
  via two `restrOpen`s of `c.trans (φ'.trans d.symm)`: planar source
  ∩ `c.target`, then outer ∩ `f.toRiemannSphere ⁻¹' d.source`.  Resulting
  underlying function agrees with `f.toRiemannSphere` on its source
  via `d.left_inv`.
* `manifoldLocalOph_apply` / `mem_source_manifoldLocalOph` /
  `mem_target_manifoldLocalOph`.
* `localSheetData_at_regular` — assembles `LocalSheetData
  f.toRiemannSphere (f.toRiemannSphere x₀) x₀` from `manifoldLocalOph`'s
  fields.

**`IsLocalHomeomorphOn` packaging** (1 chip,
`MeromorphicNonzeroLocalSheet.lean`, +39 LOC).

* `isLocalHomeomorphOn_toRiemannSphere` — `IsLocalHomeomorphOn
  f.toRiemannSphere f.regularSet` via `IsLocalHomeomorphOn.mk` +
  `manifoldLocalOph` + `manifoldLocalOph_apply`.
* `continuousAt_toRiemannSphere_of_regular` /
  `map_nhds_eq_of_regular` — corollaries.

**Fiber finiteness at regular values** (1 chip,
`Manifold/MeromorphicNonzeroFiberFinite.lean`, ~135 LOC).

* `fiber_isClosed` — preimage of singleton in T1 codomain under
  continuous `f.toRiemannSphere`.
* `mem_regularSet_of_preimage_regularValue` — preimages of regular
  values are regular points.
* `fiber_finite_of_mem_regularValueSet` — compactness + isolation via
  `IsCompact.elim_nhds_subcover` + `choose!`.

**`HurwitzPatchingData` at every regular value** (1 chip,
`Manifold/MeromorphicNonzeroHurwitzPatching.lean`, ~90 LOC).

* `hurwitzPatchingData_at_regularValue` — composes
  `HurwitzPatchingData.ofLocalSheets` with chip 7 (`localSheetData_at_regular`)
  and chip 9 (`fiber_finite_of_mem_regularValueSet`).  Provides the
  evenly-covered nbhd structure of a topological covering map at every
  regular value.

**Continuous local path lift** (1 chip,
`Manifold/MeromorphicNonzeroLocalPathLift.lean`, ~120 LOC).

* `exists_continuous_local_lift_of_continuous` — for `β : ℝ →
  RiemannSphere` continuous with `β t₀ ∈ f.regularValueSet` and any
  preimage `x₀`, produces an open `W ⊆ ℝ` ∋ t₀, a continuous local lift
  `γ : ℝ → X = sheet.g ∘ β`, with `γ t₀ = x₀` and
  `f.toRiemannSphere (γ t) = β t` for all `t ∈ W`.

**Net open content after the 11 chips.** `AbelHypothesis B` (general
genus) reduces to: discharge `f ∈ dischargedGenerators B` for every
`f : MeromorphicNonzero X` whose `toRiemannSphere` is non-constant. The
covering-map structure on `f.toRiemannSphere : f.toRiemannSphere ⁻¹'
regularValueSet → regularValueSet` is now in-tree (via `LocalSheetData`,
`HurwitzPatchingData`, `IsLocalHomeomorphOn`, fiber-finiteness, and
continuous local path lift).  The remaining classical content is the
*smooth* upgrade of the lift, *global* lift over the unit interval,
the level-set chain definition, and the Stokes argument.

Build at HEAD: `taskpolicy lake build` green, 8731 jobs. Zero `sorry`,
zero `axiom`. +~1,400 LOC across 7 new files.

## 2026-05-15 — C1 sub-arc CLOSED: `SmoothPathConnected` on any preconnected complex 1-manifold

The four chips of 2026-05-15 (SmoothPath refactor, `linearInChartSegment`,
`concat`, local-convex + open-closed) close the C1 sub-arc of
CLOSURE_MAP §F.3 unconditionally for any preconnected complex
1-manifold.

**`Manifold/SmoothPathLocalConvex.lean`** (182 LOC, new). Two
top-level theorems:

* `exists_smooth_path_connected_chart_nbhd p` — for every `p : X`,
  there is an open neighborhood `U ∋ p` such that any two points of
  `U` are joined by a smooth path. Construction: `U := φ.source ∩
  φ ⁻¹' Metric.ball z r` where `φ = chartAt ℂ p`, `z = φ p`,
  `r > 0` with `Metric.ball z r ⊆ φ.target`. Convexity of the ball
  plus `linearInChartSegment` gives the smooth-path-connected
  property of `U`.

* `smoothPathConnected_of_preconnected [PreconnectedSpace X] :
   SmoothPathConnected 𝓘(ℝ, ℂ) X` — the open-closed argument
  applied to the reachable set
  `reachableFrom p := {x | ∃ γ : SmoothPath I X, γ.src = p ∧
   γ.tgt = x}`. Helper lemmas (private):
  - `p_mem_reachableFrom` via `SmoothPath.const`.
  - `reachableFrom_isOpen` via `concat` + local lemma.
  - `compl_reachableFrom_isOpen` via the symmetric argument.
  - `reachableFrom_isClopen` combines.
  Then `IsClopen.eq_univ` closes it.

**`Manifold/SmoothPathConnectedRiemannSphere.lean`** (223 LOC,
landed earlier today). `smoothPathConnected_RiemannSphere` + the
composed `nonempty_abelJacobiInput_RiemannSphere`.

**`Manifold/SmoothPathConcat.lean`** (337 LOC, landed earlier
today). `SmoothPath.concat` via bump-flatten reparameterisations
`concatRepLeft t = σ(4(t - 1/8))` and `concatRepRight t = σ(4(t -
5/8))` (with `σ = Real.smoothTransition`), making both halves
identically equal to the junction point on `(3/8, 5/8)`.

Net (combined with `nonempty_of_smoothPathConnected` from
`Manifold/SmoothPathConnected.lean`): **`Nonempty (AbelJacobiInput
α h)` is now unconditional on any nonempty preconnected complex
1-manifold.** Items 4/5/10/11/12/13 remain blocked on the C3 and
C4 general-genus discharges (Stokes-on-2-chains, Abel converse,
Jacobi inversion).

Build across all four chips: `taskpolicy lake build` green, 8713
jobs at HEAD. Zero `sorry`, zero `axiom`. +742 LOC total.

## 2026-05-15 — `SmoothPath` refactored ω → C^∞ + `linearInChartSegment`

**Headline.** The `SmoothPath` structure's smoothness witness was
declared at `ContMDiff ... ⊤` where `⊤ : WithTop ℕ∞` resolves to the
analytic level `ω` despite a docstring stating the intent was `C^∞`.
The mismatch obstructed chart-cover lifts (analytic functions on `ℝ`
are germ-determined; concatenation across charts cannot satisfy the
analytic-germ agreement at junction points). The refactor brings the
implementation in line with the docstring and unblocks the C1
chart-cover sub-arc.

Files modified (5):

* `Manifold/SmoothChain.lean` — SmoothPath.smooth field type
  `ContMDiff (𝓘(ℝ, ℝ)) I ∞ f` (C^∞ = `((⊤ : ℕ∞) : WithTop ℕ∞)`)
  instead of `⊤`. File docstring updated.

* `Manifold/SmoothPathIntegral.lean` — `ambient_contMDiff` returns
  `ContMDiff (𝓘(ℝ, ℝ)) I ((⊤ : ℕ∞) : WithTop ℕ∞)` (the explicit form
  is used because `open scoped ContDiff` would clash with the file's
  `ω : SmoothOneForm I X` binders).

* `Manifold/SmoothPathChartCompat.lean` — `mdifferentiableAt_ambient`
  consumes the C^∞ witness; `n ≠ 0` discharged by `decide`.

* `Manifold/SmoothPathIntegrability.lean` —
  `contMDiffAt_chartVelocity` returns C^∞; `ContMDiffAt.mfderiv_const`
  invoked with `∞ + 1 ≤ ∞` (top of `ℕ∞` is absorptive in `WithTop`).

* `Manifold/SmoothPathLinearInChart.lean` — existing `linearInChart`
  retained; its ω-level chart-inverse smoothness is downcast to C^∞
  via `ContMDiffAt.of_le (by decide)`. New constructors:
    - `bumpedSegment a b t = (1 - σ t) • a + σ t • b` where
      `σ = Real.smoothTransition`.
    - `bumpedSegment_mem_segment`: image of `bumpedSegment a b` on
      all of `ℝ` lies in `segment ℝ a b` (the closed convex hull).
    - `contDiff_bumpedSegment` / `contMDiff_bumpedSegment` at `∞`.
    - `SmoothPath.linearInChartSegment` — **segment-in-target**
      smooth path constructor. Strict weakening of
      `linearInChart`'s line-in-target hypothesis. Only available at
      C^∞ because `Real.smoothTransition` is C^∞ but not analytic.
    - `linearInChartSegment_src` / `_tgt`.

Build: `taskpolicy lake build` green, 8710 jobs. Zero `sorry`, zero
`axiom`. +212 / -68 LOC.

Net unblock: chart-cover lift to `SmoothPathConnected I X` on a
compact connected complex 1-manifold is no longer obstructed by
analytic germ-determination. The remaining steps are (i) a C^∞
concatenation primitive (next sub-chip, ~150–300 LOC via partition
of unity); (ii) a chart-cover argument exploiting convex chart
targets to discharge segment-in-target trivially (~400–800 LOC).

## 2026-05-14 — `Subsingleton (Pic0 RiemannSphere)` UNCONDITIONAL — Pic⁰(ℙ¹) = 0 in-tree

**Headline.** Closes the closure decomposition for every degree-zero
divisor on the Riemann sphere as a finite ℤ-linear combination of
elementary divisors `Div.single (some a) - Div.single ∞`, each of
which is the principal divisor `principalDivisorMap (mnRSAffineFactor
a)`. Result: `Subsingleton (Pic0 RiemannSphere)` is **unconditional**,
and consequently `Pic⁰ RiemannSphere ≃+ AnalyticJacobian RiemannSphere`
is unconditional too.

New file: `Manifold/Pic0RiemannSphereSubsingleton.lean` (~190 LOC).

* `Div.finset_sum_apply` — `(∑ n ∈ s, F n : Div RS) y = ∑ n ∈ s, F n y`.
  Pointwise eval pushed through finite sums via `Finset.induction` plus
  the existing `Div.add_apply`.

* `single_sub_infty_mem_PrincDiv` — `Div.single x - Div.single ∞ ∈
  PrincDiv RS` for any `x ≠ ∞`, via `elementaryDivisor_mem_PrincDiv`.

* `sum_elementary_eq_div0 D y` — for `D : Div0 RS`,
  `(∑ x ∈ supp(D).filter (· ≠ ∞), D(x) • (Div.single x - Div.single ∞)) y
   = D y`. Split on `y = ∞` (uses `D.degree = 0` to balance contributions
  via `Finset.sum_filter_add_sum_filter_not`) vs `y` finite (isolates
  the `y`-th term via `Finset.sum_eq_single_of_mem`).

* `subsingleton_pic0_RiemannSphere : Subsingleton (Pic0 RiemannSphere)`
  — the final discharge. `AddSubgroup.sum_mem` plus
  `AddSubgroup.zsmul_mem` plus the elementary divisor lemma combine
  through the reconstruction.

* `AbelJacobiInput.abelJacobiEquiv_of_RiemannSphere_unconditional` —
  full Abel-Jacobi iso `Pic0 RS ≃+ AnalyticJacobian RS` on RS,
  **axiom-free**.

Build: `taskpolicy lake build` green, 8710 jobs. Zero `sorry`, zero
`axiom`.

## 2026-05-14 — `mnRSAffineFactor` + elementary-divisor identity

Lands the translation generator `f(z) = z - a` on the Riemann sphere
as `MeromorphicNonzero RS`, with principal divisor `δ_{some a} - δ_∞`.

New files (302 LOC across two):

* `Manifold/MeromorphicNonzeroRSAffineFactor.lean` (~190 LOC) —
  `RSAffineFactor a = RSSimplePole - (const a)`, packaged as
  `mnRSAffineFactor a : MeromorphicNonzero RiemannSphere`. The
  chart-S pullback proof reuses `RSSimplePole_comp_chartS_symm_eq`
  to reduce to `w⁻¹ - a` on a punctured nbhd of `0`, whose
  meromorphic order is `-1` (via factoring `w⁻¹ - a = (1 - a w)/w`
  and `meromorphicOrderAt_div`).

* `Manifold/Pic0RiemannSphereTrivial.lean` (~140 LOC) —
  `principalDivisorMap_mnRSAffineFactor a` and
  `elementaryDivisor_mem_PrincDiv`. The divisor computation uses
  `meromorphicOrderAt_comp_of_deriv_ne_zero` (translating `id` by
  `-a`) for the order-`1` zero at `some a`, plus
  `analyticOrderAt_eq_zero` for the order-`0` regular points.

## 2026-05-14 — `mnRSInversion`: second principal-divisor generator on RS

Sister chip to `mnRSSimplePole`. Builds the inversion function
`RSInversion : RiemannSphere → ℂ` (`some z ↦ z⁻¹`, `∞ ↦ 0`)
and packages it as a `MeromorphicNonzero RiemannSphere` with
principal divisor `δ_∞ - δ_{some 0}` (simple zero at `∞`, simple
pole at `some 0`).

New file: `Manifold/MeromorphicNonzeroRSInversion.lean` (~200 LOC).

* Chart-pullback identities: `RSInversion ∘ chartN.symm = (·)⁻¹`,
  `RSInversion ∘ chartS.symm = id`.
* `mnRSInversion : MeromorphicNonzero RiemannSphere` — packaged form.
* Order at `∞` is `1` (chart-S pullback is `id`,
  `meromorphicOrderAt_id`); order at finite is `≠ ⊤`; order at
  `some 0` is `-1` (chart-N pullback is `(·)⁻¹`,
  `meromorphicOrderAt_inv ∘ meromorphicOrderAt_id`).
* Continuity at non-pole points: at finite `z ≠ 0` via
  `continuousAt_inv₀`; at `∞` via `tendsto_inv₀_cobounded` (the
  `1/w → 0` as `|w| → ∞` limit).

Together with `mnRSSimplePole`, this gives two non-constant
principal-divisor generators on RS whose divisors are
sign-flipped (`δ_{some 0} - δ_∞` and `δ_∞ - δ_{some 0}`). Combined
with future translation generators (`δ_{some a} - δ_∞`), they
generate `Div0 RiemannSphere` and unblock unconditional
`Subsingleton (Pic0 RiemannSphere)`.

Build: 8707 jobs clean. Zero `sorry`, zero `axiom`.

## 2026-05-14 — `mnRSSimplePole`: first non-trivial principal-divisor generator on RS

Lands the first non-constant `MeromorphicNonzero RiemannSphere` — the
explicit packaging of `RSSimplePole : RiemannSphere → ℂ` (zero at
`some 0`, simple pole at `∞`) — used as the base case for any
constructive discharge of `Subsingleton (Pic0 RiemannSphere)`.

New file: `Manifold/MeromorphicNonzeroRSSimplePole.lean` (~110 LOC).

* `RSSimplePole_continuousAt_coe` — continuity at every finite
  point, via the open embedding `(↑) : ℂ → RiemannSphere`.
* `mnRSSimplePole : MeromorphicNonzero RiemannSphere` — bundled
  packaging via `MeromorphicNonzero.ofRegularContinuous`.

The non-vanishing-germ proof at finite points uses
`meromorphicOrderAt_ne_top_iff_eventually_ne_zero` on the
chart-pulled-back `id`. The `regular_continuousAt` field is
discharged at finite points via the continuity lemma above;
at `∞` the order is `-1`, making the hypothesis vacuous (proven
by contradiction on `0 ≤ -1`).

The principal divisor of `mnRSSimplePole` is `δ_{some 0} - δ_∞`.
Future chips build the translation `δ_{some a} - δ_∞` and inversion
`δ_∞ - δ_{some 0}` generators, plus the closure argument turning
these into a full discharge of `Subsingleton (Pic0 RiemannSphere)`
(equivalently `Pic⁰(ℙ¹) = 0`).

Build: 8706 jobs clean. Zero `sorry`, zero `axiom`.

## 2026-05-14 — C4 bridge: Subsingleton (Pic0 X) ↔ every Div0 is principal

New file: `Manifold/Pic0SubsingletonBridge.lean` (~85 LOC).

* `subsingleton_pic0_iff_every_div0_principal` — the bridge.
  Forward via `Subsingleton.elim` + `QuotientAddGroup.eq_zero_iff`;
  backward via `QuotientAddGroup.induction_on`.
* `subsingleton_pic0_of_every_div0_principal` — one-way form.

Why this matters: lets a future discharge of `Subsingleton (Pic0
RiemannSphere)` produce the equivalent existential statement —
constructing explicit meromorphic representatives (rational
functions on `ℂ`) for every degree-0 divisor on `RS`.

Build: 8705 jobs clean. Zero `sorry`, zero `axiom`.

## 2026-05-14 — Abel-Jacobi iso on `RiemannSphere` from Pic⁰(ℙ¹) = 0

New file: `Manifold/AbelJacobiEquivRiemannSphere.lean` (~75 LOC).
Specialises `abelJacobiEquiv_of_genus_zero` to `X = RiemannSphere`
using the unconditional `genus_RiemannSphere_eq_zero`.

* `abelJacobiEquiv_of_RiemannSphere` — from `Subsingleton (Pic0
  RiemannSphere)` and an AJ input, build `Pic0 RS ≃+ AnalyticJacobian`.
  After this commit the Abel-Jacobi iso on RS sits on exactly one
  named classical input.

Build: 8704 jobs clean. Zero `sorry`, zero `axiom`.

## 2026-05-14 — C4 genus-0: JacobiInversion ← Subsingleton (Pic0 X)

Parallel chip to the C3 genus-0 corner, closing the C4 (Jacobi
inversion) input at genus 0 down to a single textbook hypothesis.

New file: `Manifold/JacobiInversionGenusZero.lean` (~90 LOC).

* `jacobiInversion_of_genus_zero_and_subsingleton_pic0` — builds
  `JacobiInversion B hAbel` from `genus X = 0` + `Subsingleton (Pic0
  X)`. Surjectivity is automatic at genus 0 (codomain subsingleton);
  injectivity reduces to source-side subsingleton.
* `abelJacobiEquiv_of_genus_zero` — packages the full Abel-Jacobi
  isomorphism `Pic0 X ≃+ AnalyticJacobian` at genus 0 by composing
  `abelHypothesis_of_genus_zero` with the new JacobiInversion discharge.

After this commit, both halves of `Pic⁰ ≃+ AnalyticJacobian` at
genus 0 reduce to a single classical input — `Subsingleton (Pic0 X)`
(genus-0 case of Abel's converse, equivalent to Pic⁰(ℙ¹) = 0). The
general-genus content of C4 remains the open work.

Build: 8703 jobs clean. Zero `sorry`, zero `axiom`.

## 2026-05-14 — C3 per-generator reduction: AbelChainPeriodCondition ← AbelGeneratorPeriodCondition

Fourth C3 piece. Reduces `AbelChainPeriodCondition B` to the
per-generator statement `AbelGeneratorPeriodCondition B`: for each
`f : MeromorphicNonzero X`, the period vector of the AJ chain of
`div(f)` lies in `periodLatticeImage`. This is Abel forward in its
sharpest atomic form — one meromorphic function at a time.

Extends `Manifold/AbelHypothesisFromPeriodCondition.lean`.

* `AbelGeneratorPeriodCondition B : Prop` — per-`f` form of the
  period-lattice condition.
* `abelChainPeriodCondition_of_abelGeneratorPeriodCondition` —
  closure induction on `PrincDiv X = AddSubgroup.closure (Set.range
  principalDivisorMap)` using the algebra-side closure lemmas.
* `abelHypothesis_of_abelGeneratorPeriodCondition` — direct
  composite to `AbelHypothesis`.

Build: 8702 jobs clean. Zero `sorry`, zero `axiom`.

## 2026-05-14 — C3 algebra layer: additivity + closure of AbelChainPeriodCondition

Third C3 piece. Algebraic infrastructure for the C3 chain-level
reduction.

Extends `Manifold/AbelHypothesisFromPeriodCondition.lean`.

* `principalDivisorAJChain_add` — additivity of the AJ chain in the
  divisor.
* `principalDivisorAJChainHom : Div X →+ SmoothChain 𝓘(ℝ, ℂ) X` —
  bundled `AddMonoidHom` form.
* `complexChainPeriodVector_principalDivisorAJChain_add_mem` and
  `_neg_mem` — closure of "period vector ∈ periodLatticeImage" under
  addition and negation of divisors.

Build: 8702 jobs clean. Zero `sorry`, zero `axiom`.

## 2026-05-14 — C3 chain-level reduction: AbelHypothesis ← AbelChainPeriodCondition

Second piece of C3 (Abel's theorem forward direction). Lands a
concrete chain-level reduction of `AbelHypothesis B` to a single,
textbook-citable hypothesis `AbelChainPeriodCondition B` on period
vectors of explicit Abel-Jacobi chains. After this commit, the open
content of C3 at arbitrary genus is exactly the period-vector
condition.

New file: `Manifold/AbelHypothesisFromPeriodCondition.lean` (~210
LOC).

* `AbelJacobiInput.principalDivisorAJChain B D` — explicit
  Abel-Jacobi chain for any `D : Div X`:
  `Σ x ∈ D.supportFinset, D(x) • SmoothChain.single (B.pathFromBase x)`.
  Boundary on `Div0` equals `D` as a 0-chain.

* `abelJacobiChain_principalDivisorAJChain_eq_abelJacobiDivHom` —
  diagram identity routing the chain through the AJ formalism
  (`map_sum` + `AddMonoidHom.map_zsmul` + `abelJacobiChain_single`).

* `complexChainPeriodVector_principalDivisorAJChain` — period-
  vector form of the chain.

* `AbelChainPeriodCondition B : Prop` — the reduction hypothesis:
  for every principal divisor `D`, the period vector of its AJ
  chain lies in `periodLatticeImage`. Classical content: for `D
  = div(f)`, the period vector decomposes as an integer
  combination of basis periods via the level-set chain of `f`.

* `abelHypothesis_of_abelChainPeriodCondition` — the reduction
  itself. Proof via the diagram identity + `QuotientAddGroup.eq_zero_iff`
  + `PeriodLatticeOfRankTwoG.ofBundle_lattice`.

* `abelChainPeriodCondition_of_genus_zero` — sanity check
  recovering the prior genus-0 discharge through the new reduction.

Build: 8702 jobs clean. Zero `sorry`, zero `axiom`.

## 2026-05-14 — C3 corner: AbelHypothesis trivially holds at genus 0

Lands a small but real piece of C3 (Abel's theorem). At genus 0 the
analytic Jacobian collapses to a single point, so the named
hypothesis `AbelHypothesis B` of `Manifold/AbelJacobiPic0.lean`
holds vacuously. The general-genus content of `AbelHypothesis`
(classical Abel forward via Stokes on a 2-chain whose boundary
represents the principal divisor) is unaffected by this corner; it
remains the open content of C3 (CLOSURE_MAP §F.3, est.
1,200–2,800 LOC).

New file: `Manifold/AbelHypothesisGenusZero.lean` (99 LOC).

* `subsingleton_pi_fin_genus_zero` — `Subsingleton (Fin (genus X)
  → ℂ)` whenever `genus X = 0` (via `Pi.uniqueOfIsEmpty`).
* `Subsingleton.analyticJacobian_of_genus_zero` — the analytic
  Jacobian collapses to a single point at genus 0, since
  `JacobianOfLattice = (Fin (genus X) → ℂ) ⧸ lattice` quotients a
  subsingleton group.
* `AbelJacobiInput.abelHypothesis_of_genus_zero` — `AbelHypothesis
  B` unconditionally from `genus X = 0`. Every value of
  `B.abelJacobiDiv0Hom` collapses to `0` in the subsingleton
  codomain.

Build: `taskpolicy lake build` green, 8701 jobs. Zero `sorry`,
zero `axiom`.

## 2026-05-14 — A2 closed + genus-0 RR chain unconditional (modulo uniformization)

Merges `feat/antipode-smoothness` (parallel branch off `main`) into
the linear-system-divisor trunk and composes with the A1 discharge
that landed earlier today. The genus-0 Riemann–Roch `dim_ℂ L(δp) ≥
2` chain on the germ field is now reduced to exactly **one** named
classical input — uniformization at genus 0.

New files merged from `feat/antipode-smoothness` (660 LOC total):

* `Manifold/RiemannSphereAntipodeSmooth.lean` (255 LOC) — discharges
  the `contMDiff_antipode_TODO` follow-up from
  `RiemannSphereMobius.lean`: `ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω antipode` via
  `contMDiffAt_iff_of_mem_source` on the three-case `OnePoint.rec`
  split (chart pairs at `∞`, at `coe 0`, and at `coe w` with `w ≠
  0`; chart-coord maps `z ↦ -z` for the first two and `z ↦ -z⁻¹`
  for the third). Packages as `antipodeEquiv : HolomorphicEquiv RS RS`
  (self-inverse).
* `Manifold/RiemannSphereTranslate.lean` (322 LOC) — `translateBy c`
  on RS (fixing `∞`, `coe z ↦ coe (z + c)`) as `ContMDiff 𝓘(ℂ) 𝓘(ℂ)
  ω` and packaged as `translateEquiv c : HolomorphicEquiv RS RS`
  with inverse `translateEquiv (-c)`.
* `Manifold/MobiusTransitivityRS.lean` (80 LOC) —
  `RiemannSphere.existsMobiusToInftyRS`: ∀ `p : RS`, ∃ `e :
  HolomorphicEquiv RS RS`, `e p = ∞`. Concrete witnesses: identity
  for `p = ∞`; `translateEquiv(-z₀).trans antipodeEquiv` for `p =
  coe z₀` (sending `coe z₀ ↦ coe 0 ↦ ∞`).

New trunk-side file (this commit):

* `Topology/LinearSystemGermDeltaPFiniteDimRSUnconditional.lean`
  (109 LOC) — composes the two unconditional discharges:
  - `existsMobiusToInftyRS_holds : ExistsMobiusToInftyRS` — 1-line
    bridge identifying the in-tree theorem with the named-hypothesis
    Prop (definitionally equal, `rfl`-level).
  - `linearSystemGermDeltaPFiniteDim_RiemannSphere_unconditional :
    LinearSystemGermDeltaPFiniteDim RiemannSphere` — the headline,
    no hypothesis.
  - `rr_DimGE2_GenusZero_Germ_of_uniformization_unconditional_RSFiniteDim`
    — for any compact connected complex 1-manifold `X`, genus-0 RR
    dim ≥ 2 on the germ field reduces to genus-conditional
    uniformization alone.

**Net post-this-commit state.** The genus-0 RR `dim_ℂ L(δp) ≥ 2`
content on:

* **`RiemannSphere`**: **unconditional**.
* **Arbitrary compact connected complex 1-manifold `X`**: depends on
  **one** named classical input — `genus X = 0 → Nonempty
  (HolomorphicEquiv X RiemannSphere)` (uniformization at genus 0).

Build: 8700 jobs clean. Zero `sorry`, zero `axiom`.

## 2026-05-14 — `feat/c1-smooth-path-connected` merged: SmoothPathConnected predicate + linearInChart (ω-level)

Two-commit branch off `main` (`d97dcd5..c189052`) merged into
`feat/linear-system-divisor` after the A1 discharge below. Net +371
LOC, two new files in `JacobianChallenge/Manifold/`, zero `sorry`,
zero `axiom`. Full `taskpolicy lake build` green post-merge (8696
jobs). Disjoint from the linear-system-divisor RR work: files live
in `Manifold/SmoothPath*` only.

**Smooth-path-connectedness layer** — `Manifold/SmoothPathConnected.lean`
(177 LOC):

- `SmoothPathConnected I X : Prop` — every two points of `X` joined
  by a `SmoothPath I X`; smooth analogue of mathlib's
  `PathConnectedSpace`.
- `SmoothPathConnected.diagonal` — the `p = p` case is uniform via
  `SmoothPath.const`.
- `AbelJacobiInput.ofSmoothPathConnected` — constructor producing
  the bundle from `SmoothPathConnected 𝓘(ℝ, ℂ) X` + a chosen base
  point. Path-picker via `Classical.choose`.
- `AbelJacobiInput.nonempty_of_smoothPathConnected` — packaging:
  `Nonempty X + SmoothPathConnected 𝓘(ℝ, ℂ) X ⇒ Nonempty
  (AbelJacobiInput α h)`.
- `AbelJacobiInput.exists_smoothPath_from_basePoint` — one-sided
  back-projection.

Splits the `AbelJacobiInput α h` named-hypothesis bundle along a
textbook fault line: from "base point + per-target picker" down to
the classical predicate plus `Nonempty X`. CLOSURE_MAP §F.5 step 2
(C1) now factors through `SmoothPathConnected` as a single citable
classical input.

**Linear-in-chart primitive** — `Manifold/SmoothPathLinearInChart.lean`
(192 LOC):

- `affineSegment a b t = (1 - t) • a + t • b` — affine map `ℝ → ℂ`
  with `affineSegment_zero/one` endpoint identities.
- `contDiff_affineSegment` / `contMDiff_affineSegment` — affine maps
  are `C^ω`; manifold-side lift via `contMDiff_iff_contDiff`.
- `SmoothPath.linearInChart φ h_atlas p q hp hq h_line` — constructor
  of a `SmoothPath 𝓘(ℝ, ℂ) X` between `p, q` whose chart-coordinate
  line `{(1-t) • φ p + t • φ q : t ∈ ℝ}` lies entirely in
  `φ.target`. Ambient `t ↦ φ.symm (affineSegment (φ p) (φ q) t)`,
  smooth at ω-regularity via `contMDiffAt_symm_of_mem_maximalAtlas
  ∘ contMDiff_affineSegment`.
- `SmoothPath.linearInChart_src` / `_tgt` — endpoint identities.

**ω-level structural finding** (documented in the file's docstring
and accompanying commit):

The `SmoothPath` structure demands `ContMDiff 𝓘(ℝ, ℝ) I ⊤ f` with
`⊤ : WithTop ℕ∞`, which mathlib's `Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries`
notes equals `ω` (analytic). Globally analytic functions are
germ-determined, so the standard `C^∞` trick of smoothly extending
by constants outside `[0, 1]` does *not* produce an analytic path.
This forces `linearInChart` to require the *entire chart-coordinate
line* (not merely the segment) in `φ.target`. The hypothesis is
unconditional on the affine chart of `RiemannSphere` (target = ℂ);
on a generic Riemann surface chart with bounded target it fails.
Closing the "segment-only" case at the ω level genuinely requires
either changing the `SmoothPath` definition (downgrade to `C^∞`) or
an analytic-continuation argument; neither is in scope of this chip.

**Net post-this-merge state.** CLOSURE_MAP §F.5 step 2 (C1
`AbelJacobiInput`) factors through `SmoothPathConnected 𝓘(ℝ, ℂ) X +
Nonempty X`, with `linearInChart` as the first chart-side primitive.
Full chart-cover discharge remains open.

## 2026-05-14 — A1 closed: `LinearSystemAtInftyRS_BoundedBySimplePoleSpan` discharged

Two new files (~870 LOC total) discharging the polynomial-growth
Liouville bound at `∞` on the Riemann sphere, the first of the two
remaining classical inputs in the genus-0 RR `dim_ℂ L(δp) ≥ 2`
chain.

`Analysis/PolynomialLiouville.lean` (~180 LOC) — foundational
mathlib-style lemma: an entire `f : ℂ → ℂ` with `‖f z‖ ≤ C ‖z‖` for
`‖z‖ ≥ R₀` is an affine function `f z = f 0 + (deriv f 0) · z`.
Proven via the Cauchy first-derivative estimate
(`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`) plus basic
Liouville (`Differentiable.exists_const_forall_eq_of_bounded`) and
constancy from zero derivative (`is_const_of_deriv_eq_zero`).

`Topology/LinearSystemAtInftyRSDischarge.lean` (~690 LOC) —
discharge of `LinearSystemAtInftyRS_BoundedBySimplePoleSpan` for an
arbitrary germ in `linearSystemGermDeltaP (∞ : RS)`:

1. Affine-chart restriction `affineChartFun f := f.toFun ∘ some`,
   with `mmeromorphicOrderAt (some z) = meromorphicOrderAt
   (affineChartFun f) z`.
2. Entire normal-form representative `entireRep f := toMeromorphicNFOn
   (affineChartFun f) Set.univ`, analytic on all of `ℂ` by
   `MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd`.
3. Linear growth bound at infinity: `id ∘ (f ∘ chartS.symm)` has
   order `≥ 0` at `0` (additivity), so bounded near `0` by
   `tendsto_nhds_of_meromorphicOrderAt_nonneg`. Translating via the
   substitution `w = z⁻¹` gives `‖entireRep f z‖ ≤ M ‖z‖` for `‖z‖`
   large (limit-comparison lift across continuity).
4. Polynomial Liouville: `entireRep f w = a + b w` for all `w`.
5. Germ identity at `some 0`: `f.toFun =ᶠ[𝓝[≠] (some 0)] (a + b ·
   RSSimplePole)` by composing the chart-side EvEq with the
   polynomial identity.
6. Identity theorem (`mmeromorphicOrderAt_ne_top_forall`):
   single-point germ identity propagates globally to all of RS.
7. Final: `mk f = a • 1 + b • RSSimplePoleGerm ∈ span ℂ {1,
   RSSimplePoleGerm}`.

**Net post-this-commit state.** `LinearSystemGermDeltaPFiniteDim
RiemannSphere` reduces to a single remaining classical input
(`ExistsMobiusToInftyRS` — Möbius transitivity on RS). Combined
with uniformization at genus 0, the genus-0 RR `dim_ℂ L(δp) ≥ 2`
chain reduces to **two** named classical inputs: uniformization +
Möbius transitivity. Build: 8694 jobs clean (pre-C1 merge). Zero
`sorry`, zero `axiom`.

## 2026-05-14 — RS-FiniteDim architectural reduction (feat/linear-system-divisor cont.)

New file `Topology/LinearSystemGermDeltaPFiniteDimRSFromInputs.lean`
(~210 LOC) architecturally reduces `LinearSystemGermDeltaPFiniteDim
RiemannSphere` (the second of the two remaining classical inputs in
the genus-0 RR `dim_ℂ L(δp) ≥ 2` chain) to **exactly two** named
classical inputs:

1. `LinearSystemAtInftyRS_BoundedBySimplePoleSpan` — polynomial-growth
   Liouville bound at `∞`: `linearSystemGermDeltaP (∞ : RS) ≤
   Submodule.span ℂ {1, RSSimplePoleGerm}`. Classical content: entire
   `ℂ → ℂ` with `|f| = O(|z|)` at ∞ is a polynomial of degree ≤ 1.
   Mathlib at the pin has basic Liouville
   (`Complex.liouville_theorem_aux`) but not the polynomial-growth
   extension; Cauchy-estimate-based proof.
2. `ExistsMobiusToInftyRS` — Möbius transitivity on RS: ∀ `p : RS`,
   `∃ e : HolomorphicEquiv RS RS, e p = ∞`. Concrete witnesses are
   identity (for `p = ∞`) and antipode-composed-with-translation
   (for finite `p = z₀`); packaging requires checking smoothness on
   the two-chart atlas.

Helpers:
- `linearSystemGermDeltaP_finite_of_holomorphicEquiv` — per-point
  version of the existing `LinearSystemGermDeltaPFiniteDim.of_holomorphicEquiv`
  (the ∀-quantified one). Direct `Module.Finite.equiv` wrap of
  `linearSystemGermDeltaPLinearEquiv_via_holomorphicEquiv`.
- `linearSystemGermDeltaP_finite_of_le_span_pair` — pure linear-algebra:
  `L(δp) ≤ span ℂ {1, ψ} ⇒ Module.Finite ℂ (L(δp))`. Proof via
  `Module.Finite.span_of_finite` + `Module.Finite.of_injective` on
  `Submodule.inclusion`.

Headline `linearSystemGermDeltaPFiniteDim_RiemannSphere` composes the
two: the polynomial bound gives finiteness at `∞`; transitivity
transports it to every `p` via per-point transport.

**Post-this-commit state.** Combined with the existing
`feat/linear-system-divisor` branch, the genus-0 RR `dim_ℂ L(δp) ≥ 2`
on the germ field reduces to exactly **three** named classical inputs:
(i) uniformization at genus 0 (`genus X = 0 → Nonempty (HolomorphicEquiv
X RS)`), (ii) `LinearSystemAtInftyRS_BoundedBySimplePoleSpan`
(polynomial-growth Liouville on RS at ∞), (iii) `ExistsMobiusToInftyRS`
(Möbius transitivity on RS). All three are citable textbook content;
(ii) and (iii) are smaller-scale than (i) (which is full uniformization
theory). Zero `sorry`, zero `axiom`.

## 2026-05-14 — `feat/linear-system-divisor` branch (germ-field RR layer)

15-commit branch (`957fdd0..380ac85`) building the full architectural
reduction for genus-0 RR `dim_ℂ L(δp) ≥ 2` on the germ field. Net
+2807 LOC, zero `sorry`, zero `axiom`. After this branch, the
content reduces to exactly two classical inputs: (i) uniformization at
genus 0, and (ii) `LinearSystemGermDeltaPFiniteDim RiemannSphere`.

**L(D) ambient on the germ field** (closes the architectural issue
flagged earlier — pointwise `linearSystemDeltaP` was vacuously infinite
via "blip" elements):
- `Topology/LinearSystemDivisor.lean` — `linearSystemDivisor D :
  Submodule ℂ (MeromorphicFunctionGerm X)` for any `D : Div X`, with
  closure under `zero`/`add`/`smul`. Specialises to
  `linearSystemGermDeltaP p` at `D = Div.single p`.
- `Topology/LinearSystemDivisorConstants.lean` — `constantsToLinearSystemDivisor`
  for effective `D`, with injectivity under `ConnectedSpace`.
- `Topology/LinearSystemDivisorMono.lean` — monotonicity in `D`.
- `Topology/LinearSystemDivisorMul.lean` — multiplicative grading
  `L(D₁) · L(D₂) ⊆ L(D₁ + D₂)`.

**Dim-bound layer**:
- `Topology/LinearSystemDivisorZeroLiouville.lean` —
  `linearSystemDivisor 0 = constantsGerm X` and
  `finrank_linearSystemDivisor_zero_eq_one` (UNCONDITIONAL via
  the existing `liouvilleOnCompactConnected_holds`).
- `Topology/LinearSystemDivisorSimplePoleRank.lean` —
  `LinearIndependent ℂ ![1, ψ]` from a simple-pole germ, then
  `2 ≤ Module.rank ℂ (linearSystemGermDeltaP p)` (unconditional) and
  `RR_DimGE2_GenusZero_Germ` discharge from `ExistsSimplePoleGerm` +
  `LinearSystemGermDeltaPFiniteDim` (named hypothesis added).

**Existence side — RS base case + transport**:
- `Manifold/RiemannSphereSimplePole.lean` — explicit `RSSimplePole :
  RiemannSphere → ℂ` (`some z ↦ z`, `∞ ↦ 0`), packaged as
  `RSSimplePoleGerm` with simple pole at `∞`. Discharges
  `ExistsSimplePoleGermAtSomePoint RiemannSphere` UNCONDITIONALLY.
- `Manifold/MMeromorphicHolomorphicEquivTransport.lean` —
  `mmeromorphicOrderAt` preservation through a `HolomorphicEquiv`
  (composes existing `contMDiff_omega_analyticAt_chart_pullback` +
  `deriv_chart_pullback_ne_zero_of_injective` + mathlib's
  `meromorphicOrderAt_comp_of_deriv_ne_zero`).
- `Topology/ExistsSimplePoleGermFromHolomorphicEquivRS.lean` —
  `Nonempty (HolomorphicEquiv X RS) → ExistsSimplePoleGermAtSomePoint X`.

**Finite-dim side — transport**:
- `Manifold/MeromorphicFunctionGermHolomorphicEquivPullback.lean` —
  germ-field pullback `MeromorphicFunctionGerm Y → MeromorphicFunctionGerm
  X` via composition with `e`, preserving `orderAt`.
- `Topology/LinearSystemGermDeltaPHolomorphicEquivTransport.lean` —
  `IsBoundedByDeltaPGerm` iff under pullback; bundled `LinearMap`
  between `L(δ(e p))` and `L(δp)`.
- `Topology/LinearSystemGermDeltaPFiniteDimTransport.lean` —
  `LinearEquiv` packaging + `Module.Finite.equiv` to transport
  `LinearSystemGermDeltaPFiniteDim`.

**Final assembly**:
- `Topology/RRDimGE2FromUniformizationAndFiniteDim.lean` /
  `Topology/RRDimGE2FromUniformizationAndFiniteDimRS.lean` —
  `rr_DimGE2_GenusZero_Germ_of_uniformization_and_RSFiniteDim` and
  variants. Headline assembly.

## 2026-05-13 — Period-lattice arc PL-1 closed + germfield arc to main

**Germfield arc (item 14 reduction)** — `2e5cfb4..main`:
- 9 chips landed reducing item 14's `genus_eq_zero_iff_homeo` from 5 named
  classical hypotheses to **one classical input**
  (`ExistsSimplePoleGermAtSomePoint X`) modulo the **structural typeclass**
  `[Subsingleton (HolomorphicOneForm X)]`.
- New files: `Manifold/MeromorphicFunctionField.lean`,
  `Manifold/MeromorphicFunctionGermCanonicalize.lean`,
  `Manifold/MeromorphicFunctionGermIdentityCorollary.lean`,
  `Topology/LinearSystemGermDeltaP.lean`,
  `Topology/RRDimensionFormGerm.lean`,
  `Topology/RRGenusZeroGermComposition.lean`,
  `Topology/RRStrictLtFromSimplePole.lean`,
  `Topology/Item14FromGermfield.lean`,
  `Topology/HTopFromSubsingleton.lean`.

**Period-lattice arc PL-1** — `60ba76d`, `df0227c`, `8f4e0a7`:

- `Manifold/ComplexManifoldRealification.lean` — bridging
  `instance complexManifoldRealification : IsManifold 𝓘(ℝ, ℂ) n X` from
  `[IsManifold 𝓘(ℂ, ℂ) ω X]`. Unblocks `SmoothOneForm 𝓘(ℝ, ℂ) X` as the
  ambient type for the real-side period pairing.
- `Manifold/HolomorphicOneFormRealComponent.lean` (400 LOC) — the bundled
  PL-1 step in full. Provides:
  - `realPartCLM`, `imagPartCLM : (ℂ →L[ℂ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℝ)` as
    bundled continuous **ℝ**-linear maps.
  - `tangentBundleCore_coordChange_restrictScalars_eq` — the two manifold
    structures' tangent transitions related by `restrictScalars ℝ`.
  - `cotangentBundleCore_coordChange_realPartCLM` / `_imagPartCLM` —
    cotangent coordinate change commutes with the fibrewise CLMs.
  - `ContMDiffAt_restrictScalars_to_real` — manifold-level scalar
    restriction bridge.
  - `realPart_section_contMDiff` / `_imag` — section smoothness over the
    real cotangent bundle.
  - `realComponent`, `imagComponent : HolomorphicOneForm X → SmoothOneForm
    𝓘(ℝ, ℂ) X` — the bundled deliverable.

  Recurring obstacle navigated throughout: the `NormedSpace ℝ ℂ` instance
  diamond (between `NormedSpace.complexToReal` priority-900 and
  `NormedAlgebra.toNormedSpace`) breaks `IsScalarTower.right`'s unifier
  whenever the synth context has `NormedSpace ℂ ℂ` resolved first. Pinned
  with `letI : NormedSpace ℝ ℂ := @NormedAlgebra.toNormedSpace ℝ ℂ _ _ _`
  per def at every `restrictScalars` site.

  Build: 8650 jobs, clean. PL-1 unblocks the holomorphic-side period
  pairing construction (PL-2).

## v0.1.0 (2026-04-26) — initial scaffold

- Repo scaffold (`lakefile.toml`, `lean-toolchain`, CI workflows, `.gitignore`).
- Mathlib pinned to commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (the
  exact rev Buzzard's challenge gist v0.3 specifies, dated 2026-04-15).
- `JacobianChallenge/Basic.lean` contains Buzzard's challenge signature
  verbatim; every `def`/`lemma`/`theorem` is `:= sorry`. Each `sorry`
  corresponds to one open item in `OPEN.md`.
- `DEVELOPMENT.md` carries the apfsd kernel-panic rules and CI-as-default
  workflow inherited from `sqg-lean-proofs` and `ns-lean-proofs`.
