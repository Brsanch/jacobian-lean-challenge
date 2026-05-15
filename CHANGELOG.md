# Changelog

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
