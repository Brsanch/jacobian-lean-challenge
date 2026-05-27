# Item 14 — handoff

---

## ✅ WALL DOCUMENTED — SHIPPED CONDITIONAL (2026-05-26)

**Status decision**: Item 14 is shipped CONDITIONAL on the named
classical hypothesis `ExistsMeroSimplePole_GenusZero X` (= Forster
Thm 16.9, defined at
[`Topology/RiemannRochGenusZeroDecomposition.lean:101`](JacobianChallenge/Topology/RiemannRochGenusZeroDecomposition.lean#L101)).
All structural reductions on both legs are proven and compile-verified;
the remaining gap is one classical theorem requiring multi-thousand-LOC
mathlib-grade infrastructure not at this pin. Per Buzzard's challenge
spirit, packaging difficult classical content as a named open hypothesis
is the appropriate finish at this mathlib pin. Further chip-by-chip
progress on Item 14 abstract-X closure is not on the roadmap.

* **Item 14 on `X = RiemannSphere`**: UNCONDITIONALLY closed
  ([`Topology/Item14ForRiemannSphere.lean`](JacobianChallenge/Topology/Item14ForRiemannSphere.lean)).
* **Item 14 on abstract X**: conditional on `ExistsMeroSimplePole_GenusZero X`
  via the chain documented below.
* **The chain entry-point (1-input composition)**:
  [`Topology/RiemannRochGenusZeroSingleInput.lean:54`](JacobianChallenge/Topology/RiemannRochGenusZeroSingleInput.lean#L54)
  `riemannRochGenusZero_from_existence : ExistsMeroSimplePole_GenusZero X → RiemannRochGenusZero X`,
  then
  [`Topology/UniformizationFromRiemannRoch.lean`](JacobianChallenge/Topology/UniformizationFromRiemannRoch.lean)
  → `UniformizationToRiemannSphere X` (genus=0 branch),
  then
  [`Topology/Item14FromSingleUniformization.lean:168`](JacobianChallenge/Topology/Item14FromSingleUniformization.lean#L168)
  `genus_eq_zero_iff_homeo_of_uniformizationToRiemannSphere` →
  `genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2)`, then
  [`Topology/Item14ClassTransport.lean`](JacobianChallenge/Topology/Item14ClassTransport.lean)
  to land in the `Basic.lean` signature shape.
* **Equivalent textbook names of the same wall** (any closes Item 14
  on abstract X via in-tree transport):
  `hSP X` = `ExistsSimplePoleGermAtSomePoint X`,
  `DBarSolvabilityAtGenusZero X` + `ChartAtConstantOnSource`,
  `RR_DimGE2_GenusZero X`,
  `Nonempty (HolomorphicEquiv X RiemannSphere)` at `genus X = 0`.
  These are textbook-equivalent (Dolbeault ↔ Serre duality ↔ RR ↔
  uniformization).
* **Authoritative LOC audit of remaining classical work** (2026-05-26,
  four parallel sub-agents with 6,500-LOC-per-substantial-theorem
  calibration from the measured Pompeiu chain at
  `Analysis/Pompeiu*.lean` + `Analysis/InvNorm*.lean` = 6,587 LOC,
  250 declarations, 1 substantial theorem `partialZBar_pompeiuKernel_eq_self`):
  closure costs **~28k–35k LOC for Arc 1** (RR + Serre),
  **~26k–46k LOC for Arc 3** (Dirichlet / Green's),
  or **~38k–56k LOC for Arc 2 abstract X** (Behnke-Stein + Cousin I
  with required uniformization step). Multi-month at this repo's chip
  velocity. No external Lean project will land any arc soon; mathlib
  pin bump saves <1k LOC.

The rest of this section remains the canonical structural picture.

## 🟢 ACTIVE ARC — CANONICAL CURRENT STATE (2026-05-26)

**This section is the single source of truth for Item 14's frontier.**
All other audit docs in this directory (DBAR_CONSUMER_AUDIT,
REARCHITECTURE_AUDIT, UNIFORMIZATION_ROUTE_AUDIT, HSP_AUDIT,
ROUTE_5_5C_*, the older sections below) are frozen analytical
snapshots and may contradict this one. **Read this first.**

Verified by compile 2026-05-26: `LEAN_NUM_THREADS=1 lake env lean
JacobianChallenge/Topology/HTopFromSubsingleton.lean` exits 0.

### Item 14 status on concrete X = RiemannSphere

**Unconditionally closed.** `Topology/Item14ForRiemannSphere.lean:
genus_eq_zero_iff_homeo_RiemannSphere`.

### Item 14 status on abstract X

**Open. Reduces to ONE classical theorem, with multiple equivalent
textbook names — none of them in mathlib at this pin.** Pick any one
of:

* `ExistsMeroSimplePole_GenusZero X` (Forster Thm 16.9: compact
  genus-0 Riemann surface admits a non-constant meromorphic function
  with a single simple pole)
* `ExistsSimplePoleGermAtSomePoint X` (= `hSP X`, the germ form of
  the above)
* `DBarSolvabilityAtGenusZero X` + `ChartAtConstantOnSource p` (the
  Dolbeault form, `H¹(X, 𝒪) = 0` at genus 0)
* `RR_DimGE2_GenusZero X` (the RR dimension inequality at genus 0)
* `Nonempty (HolomorphicEquiv X RiemannSphere)` at `genus X = 0`
  (uniformization)

These are textbook-equivalent (Dolbeault ↔ Serre duality ↔ RR ↔
uniformization). The repo's transport machinery converts a discharge
of any one into a closure of the others, so they are NOT independent
routes — they are five names for the same wall.

### What IS unconditional in tree (no longer hypotheses)

| Fact | File:line |
|---|---|
| `surjective_of_NonConstant_Analytic_Manifold_holds` | [`Manifold/SurjectiveOfNonConstantDischarge.lean:391`](JacobianChallenge/Manifold/SurjectiveOfNonConstantDischarge.lean#L391) |
| `nearbyRegularWitnessHypothesis_holds_unconditional` | [`Manifold/NearbyRegularWitnessHolds.lean:32`](JacobianChallenge/Manifold/NearbyRegularWitnessHolds.lean#L32) |
| `ramificationSumEqualsDegree_holds_unconditional` | [`Manifold/RamificationSumEqualsDegreeUnconditional.lean:471`](JacobianChallenge/Manifold/RamificationSumEqualsDegreeUnconditional.lean#L471) (composes nearbyRegularWitness + wd_reg) |
| `bijectiveAnalyticIsBiholomorphism_holds` | [`Manifold/BijectiveAnalyticToBiholomorphismDischarge.lean`](JacobianChallenge/Manifold/BijectiveAnalyticToBiholomorphismDischarge.lean) |
| `DegreeOneIsBiholomorphic_RS X` | composed unconditionally at [`Topology/Item14FinalComposition.lean:66`](JacobianChallenge/Topology/Item14FinalComposition.lean#L66) from the three above |
| `existsSimplePoleGermAtSomePoint_of_holomorphicEquiv_RS` | [`Topology/ExistsSimplePoleGermFromHolomorphicEquivRS.lean:172`](JacobianChallenge/Topology/ExistsSimplePoleGermFromHolomorphicEquivRS.lean#L172) (transport along a biholomorphism) |
| Reverse leg `S2ImpliesGenus0 X` | [`Topology/S2ImpliesGenus0FromEtalePrimitives.lean`](JacobianChallenge/Topology/S2ImpliesGenus0FromEtalePrimitives.lean) (étale-primitives arc) |
| `riemannRochGenusZero_from_existence` (1-input reduction) | [`Topology/RiemannRochGenusZeroSingleInput.lean:54`](JacobianChallenge/Topology/RiemannRochGenusZeroSingleInput.lean#L54) |
| One-input composition of Item 14 from hSP | [`Topology/Item14FromHSPOnly.lean:genus_eq_zero_iff_homeo_from_hSP`](JacobianChallenge/Topology/Item14FromHSPOnly.lean) |

### Implications for chip work

**There is no chip-sized step left between current state and Item 14
abstract-X closure.** The remaining gap is one classical theorem
(equivalently named in five ways above). At the project's measured
chip velocity this is multi-month / multi-thousand-LOC work,
consistent with what the repo's own files (e.g.
`RiemannRochGenusZeroSingleInput.lean:28-30`) and external audits
agree on.

Honest next moves on Item 14 are:

1. **Commit to a multi-month classical formalization arc.** Pick one
   of {Forster §16.9 = `ExistsMeroSimplePole_GenusZero X`, Forster
   Ch.27 + Dirichlet's principle = direct uniformization, RR + Serre
   duality} and ship it as a multi-thousand-LOC sub-project. Each is
   independently a mathlib-scale contribution.
2. **Document the wall and move to other items.** Item 14 stays
   conditional on a named classical hypothesis; closure for `X =
   RiemannSphere` is already shipped; submission caveat is honest.
3. **Build foundational pieces (no Item-14 closure claim).** E.g.
   Phase B of `ROUTE_5_5C_III_FORSTER_PINNED.md` ships `H¹(Δ, O) = 0`
   as standalone analytic infrastructure (~600–900 LOC), useful for
   any of the three arcs above without committing to any.

**What is NOT a productive chip:** further reduction of the named
hypothesis to another named hypothesis (paraphrase, blocked by
[[feedback_lean_paraphrase_antipattern]]), or further decomposition
of the partition-Pompeiu candidate (the `outerRingLeakage` doesn't
cancel via partition-of-unity per `DBAR_CONSUMER_AUDIT.md` §5; closing
it is the same multi-month classical content).

### Historical sections below

The rest of this file is the per-session deliverable history and
older planning notes, preserved for `git blame` continuity. **It is
not authoritative current state.** Where it conflicts with the
section above, the section above wins.

---

## 🔵 HISTORICAL — previous "ACTIVE ARC" framing (pre-canonical, 2026-05-26 AM)

The 2026-05-26 AM ACTIVE ARC framing presented three "independent
routes" (Partition-Pompeiu, RR+Serre, Direct uniformization). The
canonical section above replaces this with: they are not
independent — they are five textbook-equivalent names for the same
classical wall. Architecturally, the in-tree transport machinery
makes a discharge of any one of them closure of all.

Original three-route framing (kept for `git log` traceability):

* Partition-Pompeiu route: `globalSolutionCandidate` candidate built;
  `outerRingLeakage = 0` is the remaining frontier; doesn't cancel
  via partition-of-unity per `DBAR_CONSUMER_AUDIT.md`.
* RR + Serre route: `RR_DimGE2_GenusZero_Germ` reduces to
  uniformization-or-equivalent on abstract X.
* Direct uniformization route: build `HolomorphicEquiv X RS` from
  genus = 0; Forster Ch.16-17 or Ch.27.

### This session's deliverables (2026-05-26, ~1660 LOC, 11 commits)

* **5.5c-III-1a** ([`Analysis/InvNormIntegralBound.lean`](JacobianChallenge/Analysis/InvNormIntegralBound.lean), 115 LOC):
  `∫ ζ in closedBall 0 r, ‖ζ‖⁻¹ ∂volume ≤ r · 2π`. Real-integral
  form of Chip 1b's lintegral polar bound. De-privatizes
  `lintegral_inv_enorm_closedBall_le` for downstream reuse.

* **5.5c-III-1b** ([`Analysis/PompeiuKernelSupNormBound.lean`](JacobianChallenge/Analysis/PompeiuKernelSupNormBound.lean), 241 LOC):
  `‖pompeiuKernel α z‖ ≤ 2(R + ‖z‖) · M` for `tsupport α ⊆
  closedBall 0 R`, `‖α ζ‖ ≤ M`. Foundational Schauder-grade bound;
  holds without continuity (Bochner convention).

* **5.5c-I-c** ([`Manifold/OmegaPartitionSum.lean`](JacobianChallenge/Manifold/OmegaPartitionSum.lean), 232 LOC):
  `omegaPartitionSum P h_α : OmegaForm X` (the partition sum
  `Σ_i ofChartLocalFunction i.val (ρ_i α)`) + canonical-chart recovery
  `ω.coeff y (chart_y y) = α y` under global `ChartAtConstantOnSource`.
  `evalCoeffHom y z : OmegaForm X →+ ℂ` pushes Finset.sum through
  `.coeff` via `map_sum`.

* **5.5c-I-d** ([`Manifold/PartialZBarManifoldLocalPompeiuChartConst.lean`](JacobianChallenge/Manifold/PartialZBarManifoldLocalPompeiuChartConst.lean), 159 LOC):
  Sub-chip 5.5b's chart-anchored factor-free identity transported
  to canonical chart-y under chart-const: on `support (P.rhoC i)`,
  `partialZBarManifold (v_i) y = (P.rhoC i * α) y`.
  Aux `deriv_chart_transition_eq_one_under_chart_const`.

* **5.5c-I-e** ([`Manifold/GlobalSolutionUnderChartConst.lean`](JacobianChallenge/Manifold/GlobalSolutionUnderChartConst.lean), 138 LOC):
  conditional global identity `partialZBarManifold (Σ v_i) y = α y`
  under chart-const + per-call outer-ring-vanish hypothesis. No new
  named Prop introduced; outer-ring hypothesis is inline per-call.

* **5.5c-I-f** ([`Manifold/LocalPompeiuSolutionLeibniz.lean`](JacobianChallenge/Manifold/LocalPompeiuSolutionLeibniz.lean), 222 LOC):
  chart-anchored Leibniz decomposition
  `partialZBarManifoldAtChart i.val v_i y = ∂̄_chart χ · K_i + χ · (ρ_i α)`.
  Auxs: `localPompeiuSolutionGlobal_chart_symm_eqOn_target`,
  `differentiableAt_chiC_chart_symm`,
  `differentiableAt_pompeiuKernel_chartPullbackZero`.

* **5.5c-I-g** ([`Manifold/LocalPompeiuSolutionLeibnizChartConst.lean`](JacobianChallenge/Manifold/LocalPompeiuSolutionLeibnizChartConst.lean), 161 LOC):
  lifts the chart-anchored Leibniz (5.5c-I-f) to canonical chart-y
  under chart-const. Aux
  `partialZBarManifoldAtChart_eq_partialZBarManifold_under_chart_const`.

* **5.5c-I-h** ([`Manifold/OuterRingLeakage.lean`](JacobianChallenge/Manifold/OuterRingLeakage.lean), 215 LOC):
  defines `outerRingLeakageAt P α χs i y` and `outerRingLeakage P α χs y`;
  proves the **explicit-leakage global identity**
  `partialZBarManifold (globalSolutionCandidate) y = α y +
  outerRingLeakage y` under chart-const. Corollary
  `partialZBarManifold_globalSolutionCandidate_eq_α_of_outerRing_zero`.

* **5.5c-I-i** ([`Manifold/OuterRingIndices.lean`](JacobianChallenge/Manifold/OuterRingIndices.lean), 178 LOC):
  filtered-Finset form `outerRingIndices P χs y` + structural lemmas
  (membership characterization, per-i vanishing on `support(ρ_i)`
  and off `tsupport(χ_i)`, subset of chart sources). Removes
  if-then-else; clean sum form for downstream cancellation work.

### Audit docs landed this session

* [`ROUTE_5_5C_FORSTER_AUDIT.md`](ROUTE_5_5C_FORSTER_AUDIT.md) — original audit ruling out
  the OmegaForm partition-sum route under abstract chartAt (later
  refined: works under global `ChartAtConstantOnSource` modulo
  outer-ring cancellation).

* [`ROUTE_5_5C_III_PLAN.md`](ROUTE_5_5C_III_PLAN.md) — Behnke-Stein-on-disk planning.
  Phase A landed (5.5c-III-1a + 1b); Phase B-E not started.

* [`ROUTE_5_5C_III_FORSTER_PINNED.md`](ROUTE_5_5C_III_FORSTER_PINNED.md) — McMullen Berkeley
  241/96 + Anagol Berkeley 213b confirmation that compact-ℂℙ¹
  classical proof = Behnke-Stein on disk + Cousin-I on annulus.

* [`DBAR_CONSUMER_AUDIT.md`](DBAR_CONSUMER_AUDIT.md) — downstream consumers of
  `DBarSolvabilityAtGenusZero`.

* [`REARCHITECTURE_AUDIT.md`](REARCHITECTURE_AUDIT.md) — survey of alternative routes to
  `hSP X` that avoid `H¹(X, O) = 0`.

* [`UNIFORMIZATION_ROUTE_AUDIT.md`](UNIFORMIZATION_ROUTE_AUDIT.md) — catalog of 6 parallel
  named-hypothesis routes in tree to Item 14.

Last rewrite: 2026-05-26 (Sub-chip 5.5c-I-b-final landed — the `OmegaForm.ofChartLocalFunction` constructor + `localFormCoeff_transition_general` upgrading the anchor-relative cocycle to a cocycle for arbitrary chart pairs via chain rule + case-split. The 5.5c-I-b sub-chip family is now end-to-end COMPLETE: definition (5.5c-I-b def+cocycle, 312 LOC) + smoothness (5.5c-I-b-smoothness, 356 LOC) + constructor (5.5c-I-b-final, 240 LOC) = 908 LOC, all axiom-free. Route I ((0,1)-form record encoding from `ROUTE_5_5C_AUDIT.md`) is now operational for the partition-sum step). Headlines —

* **`partialZBar_pompeiuKernel_eq_self`** ([`Analysis/PompeiuKernelCauchyPompeiu.lean`](JacobianChallenge/Analysis/PompeiuKernelCauchyPompeiu.lean), 213 LOC, Chip 3c-F-4): the unconditional Cauchy-Pompeiu identity on ℂ.
* **`partialZBar_pompeiuKernelChart_eq_α_on_chart_source`** ([`Manifold/ChartPompeiuKernel.lean`](JacobianChallenge/Manifold/ChartPompeiuKernel.lean), 462 LOC, Chip 4): chart-x view local identity — for `y ∈ (chartAt ℂ x).source`, `partialZBar (pompeiuKernelChart x α ∘ chart_x.symm) (chart_x y) = α y`.
* **`partialZBarManifold_pompeiuKernelChart_at_basepoint`** (Chip 4): the manifold-level identity at the construction basepoint `x` — `partialZBarManifold (pompeiuKernelChart x α) x = α x`.
* **`partialZBarManifold_pompeiuKernelChart_eq_α_mul_transition`** (Chip 4): the manifold-level identity at any `y ∈ (chartAt ℂ x).source`, with the chart-transition conjugate-derivative factor `conj(deriv (chart_y ∘ chart_x.symm)(chart_x y))` absorbing the (0,1)-form transformation under chart change.
* **`contDiffOn_pompeiuKernelChart_chart_symm`** (Chip 4): `pompeiuKernelChart x α ∘ chart_x.symm` is `C^∞` on `(chartAt ℂ x).target`.
* **`FiniteChartCover X`** + **`FiniteChartCover.exists_of_compact`** ([`Manifold/CompactnessChartCover.lean`](JacobianChallenge/Manifold/CompactnessChartCover.lean), 120 LOC, Sub-chip 5.1): bundled `Finset` of base points whose chart sources cover a compact charted-ℂ space `X`, plus its existence theorem (no nonemptiness assumption). Supporting lemma `iUnion_source_eq_univ` restates the cover as `(⋃ x ∈ basePoints, (chartAt ℂ x).source) = univ` for downstream rewriting.
* **`chartPullbackZero x α : ℂ → ℂ`** + **`hasCompactSupport_chartPullbackZero`** ([`Manifold/ChartPullbackExtendZero.lean`](JacobianChallenge/Manifold/ChartPullbackExtendZero.lean), 252 LOC, Sub-chip 5.3a): `Set.indicator`-based extension `α ∘ chart_x.symm` to a globally-defined ℂ → ℂ function (zero outside `chart_x.target`), with **`HasCompactSupport`** under `[CompactSpace X]` + `tsupport α ⊆ (chartAt ℂ x).source`. This handles the structural obstruction that `(chartAt ℂ x).symm` is junk outside `chart_x.target` and the bare composition `α ∘ chart_x.symm` need not be compactly supported.
* **`partialZBarManifold_chartPompeiuSolution_eq_α_mul_transition`** ([`Manifold/ChartPompeiuSolutionManifoldIdentity.lean`](JacobianChallenge/Manifold/ChartPompeiuSolutionManifoldIdentity.lean), 260 LOC, Sub-chip 5.4c-final): manifold-side `∂̄` identity for `chartPompeiuSolution` with chart-transition factor. `partialZBarManifold (chartPompeiuSolution i P α) y · conj(deriv (chart_y ∘ chart_xi.symm)(chart_xi y)) = (P.rhoC i * α) y` for `y ∈ chart_xi.source`. Uses Chip 4's content-agnostic bridge `partialZBar_chart_x_eq_manifold_mul_transition` plus a chart-x view computation: agreement on `chart_xi.target` via `chart_xi.right_inv` + germ-dependence of `partialZBar` + Chip 3c-F-4 + Sub-chip 5.3a + `chart_xi.left_inv`. Requires `[IsManifold (𝓘(ℂ, ℂ)) ω X]` (in addition to `[IsManifold 𝓘(ℝ, ℂ) ⊤ X]`), matching `DBarSolvabilityAtGenusZero`'s assumptions.
* **`partialZBarManifold_eventuallyEq_congr`** + **`partialZBarManifold_localPompeiuSolutionGlobal_eq_chartPompeiuSolution_on_support_rhoC`** ([`Manifold/LocalPompeiuSolutionGlobalPartialZBar.lean`](JacobianChallenge/Manifold/LocalPompeiuSolutionGlobalPartialZBar.lean), 156 LOC, Sub-chip 5.4c-prep): germ-dependence of `partialZBarManifold` (via `Filter.EventuallyEq.fderiv_eq` on the chart pullback) + the local-coincidence statement: on `support(P.rhoC i)` (open since `P.rhoC i` is continuous), `∂̄_man v_i = ∂̄_man (chartPompeiuSolution i P α)` because `χ_i ≡ 1` on a neighborhood of any such point. Reduces the cutoff to the chart-pullback-zero Pompeiu kernel; the chart-transition factor analysis is split off to the next sub-chip.
* **`localPompeiuSolutionGlobal P i α χ`** + **`tsupport_…_subset`** + **`contMDiff_…`** ([`Manifold/LocalPompeiuSolutionGlobal.lean`](JacobianChallenge/Manifold/LocalPompeiuSolutionGlobal.lean), 243 LOC, Sub-chip 5.4b): the **global Pompeiu solution** `v_i := (χ_i : ℂ) · pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α)) ∘ chart_xi`. Total function `X → ℂ`. `tsupport v_i ⊆ chart_xi.source` via support ⊆ support χ + closure-monotonicity. Global ContMDiff via two-set open cover `{chart_xi.source, (tsupport χ)ᶜ}`: on chart_xi.source product of smooth factors (contMDiffOn_chart at level ⊤ lowered to ∞ via `.of_le`, pompeiuKernel C^∞ via Chip 2d, χ smooth, product via `contMDiffRing_complex_over_real`); on (tsupport χ)ᶜ identically zero (via congr_of_eventuallyEq with constant zero).
* **`PartitionChartSourceCutoff P i`** + **`exists_partitionChartSourceCutoff`** ([`Manifold/PartitionChartSourceCutoff.lean`](JacobianChallenge/Manifold/PartitionChartSourceCutoff.lean), 180 LOC, Sub-chip 5.4a): the **second cutoff** `χ_i : X → ℝ`, smooth with `χ_i ≡ 1` on `tsupport (P.rhoC i)`, `0 ≤ χ_i ≤ 1`, and crucially `tsupport χ_i ⊆ (chartAt ℂ i.val).source`. Existence via `normal_exists_closure_subset` (T2 + CompactSpace ⇒ NormalSpace) to shrink chart.source to an open V with closure ⊆ source, then `exists_contMDiffMap_zero_one_of_isClosed` between `Vᶜ` and `tsupport (P.rhoC i)`.
* **`partialZBar_pompeiuKernel_chartPullbackZero_partition_mul_eq`** ([`Manifold/LocalPompeiuSolutionChart.lean`](JacobianChallenge/Manifold/LocalPompeiuSolutionChart.lean), 181 LOC, Sub-chip 5.3c): the **chart-x view local identity** — for `y ∈ (chartAt ℂ i.val).source`, `partialZBar (pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))) ((chartAt ℂ i.val) y) = (P.rhoC i * α) y`. Combines 5.3a (HasCompactSupport) + 5.3b (ContDiff ℝ ∞, brought down to C¹ via `.of_le`) + Chip 3c-F-4 (`partialZBar_pompeiuKernel_eq_self`) + `chart.left_inv` to collapse `chart.symm (chart y) = y`. Also registers a missing-from-mathlib `instance contMDiffRing_complex_over_real : ContMDiffRing 𝓘(ℝ, ℂ) ∞ ℂ` (mirrors `instFieldContMDiffRing`'s proof for the `𝓘(𝕜) n 𝕜` case), unlocking `(P.rhoC i).mul α` for the manifold-side product smoothness needed to feed Sub-chip 5.3b.
* **`contDiff_chartPullbackZero`** ([`Manifold/ChartPullbackExtendZeroSmooth.lean`](JacobianChallenge/Manifold/ChartPullbackExtendZeroSmooth.lean), 186 LOC, Sub-chip 5.3b): **`ContDiff ℝ ∞ (chartPullbackZero x α)`** globally on `ℂ`, under `[CompactSpace X] [IsManifold 𝓘(ℝ, ℂ) ⊤ X]` + `ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α` + `tsupport α ⊆ (chartAt ℂ x).source`. Glues two open lemmas: `contDiffOn_chartPullbackZero_target` (on `chart_x.target`, via `contMDiffOn_chart_symm`-bridge + manifold composition + `contMDiffOn_iff_contDiffOn` for the ℂ → ℂ end) and `contDiffOn_chartPullbackZero_compl_image` (on the open complement of the compact chart image `chart_x '' (tsupport α)`, where the function is identically zero). These two open sets cover `ℂ` because `chart_x '' (tsupport α) ⊆ chart_x.target`, so any `ζ ∉ chart_x.target` is in the second.
* **`FiniteChartCoverPartition cover`** + **`exists_of_cover`** ([`Manifold/PartitionOfUnitySubordinateToCover.lean`](JacobianChallenge/Manifold/PartitionOfUnitySubordinateToCover.lean), 233 LOC, Sub-chip 5.2): smooth partition of unity indexed by `{x // x ∈ cover.basePoints}`, subordinate to chart sources. Thin wrapper over mathlib's `SmoothPartitionOfUnity.exists_isSubordinate` at `I := 𝓘(ℝ, ℂ)`, `s := univ`. Exposes `P.rho i : X → ℝ` (smooth ℝ-valued partition) and `P.rhoC i : X → ℂ` (`Complex.ofRealCLM` cast, the form Chip 5.3 multiplies by `α : X → ℂ`). Properties shipped: `rho_nonneg`, `rho_le_one`, `sum_rho_eq_one`, `tsupport_rho_subset`, `rho_smooth`, `rho_continuous`; plus ℂ-side counterparts `rhoC_smooth` (`ContinuousLinearMap.contMDiff` + `ContMDiff.comp`), `rhoC_continuous`, `tsupport_rhoC_subset` (via `Complex.ofReal_eq_zero`-injective support equality), and `sum_rhoC_eq_one` (via `Complex.ofReal_sum` to push the cast through the finite sum). Hypotheses: `[T2Space X] [IsManifold 𝓘(ℝ, ℂ) ⊤ X]` (plus `[CompactSpace X]` for existence).

### Assembly layer (7 chips beyond the 5.4 trilogy)

* **Combined per-i identity** ([`Manifold/LocalPompeiuSolutionManifoldIdentity.lean`](JacobianChallenge/Manifold/LocalPompeiuSolutionManifoldIdentity.lean), 86 LOC): single-statement composition of 5.4c-prep + 5.4c-final: `partialZBarManifold v_i y · conj(transition factor) = (P.rhoC i * α) y` on `support(P.rhoC i)`. Aux `support_rhoC_subset_chart_source` (subset_tsupport + 5.2's `tsupport_rhoC_subset`) bridges the support inclusion.
* **Basepoint identity** ([`Manifold/LocalPompeiuSolutionAtBasepoint.lean`](JacobianChallenge/Manifold/LocalPompeiuSolutionAtBasepoint.lean), 112 LOC): at `y = i.val`, the chart "self-transition" `chart_i ∘ chart_i.symm` agrees with `id` on the open nbhd `chart_i.target`, so its derivative at `chart_i(i.val)` is 1 (`EventuallyEq.deriv_eq` + `deriv_id`), and `conj 1 = 1`. The combined identity collapses to `partialZBarManifold v_i (i.val) = (P.rhoC i * α) i.val` (under `i.val ∈ support (P.rhoC i)`).
* **Global solution candidate** ([`Manifold/GlobalSolutionCandidate.lean`](JacobianChallenge/Manifold/GlobalSolutionCandidate.lean), 86 LOC): `globalSolutionCandidate P α χs y := ∑ i, localPompeiuSolutionGlobal P i α (χs i) y`. Global ContMDiff via `contMDiff_finset_sum` (uses `ContMDiffAdd 𝓘(ℝ, ℂ) ∞ ℂ` derived from 5.3c's `contMDiffRing_complex_over_real` instance).
* **`partialZBarManifold_finset_sum`** ([`Manifold/PartialZBarManifoldFinsetSum.lean`](JacobianChallenge/Manifold/PartialZBarManifoldFinsetSum.lean), 91 LOC): `partialZBarManifold` distributes over finite Finset sums under per-summand chart-pullback differentiability. Proof by Finset.induction with `partialZBarManifold_zero` + `partialZBarManifold_add`. Uses `DifferentiableAt.fun_sum` (not `.sum`) for the recursive-sum differentiability.
* **`partialZBarManifold_globalSolutionCandidate_eq_finset_sum`** ([`Manifold/GlobalSolutionCandidatePartialZBar.lean`](JacobianChallenge/Manifold/GlobalSolutionCandidatePartialZBar.lean), 138 LOC): the assembly identity `partialZBarManifold (globalSolutionCandidate P α χs) y = ∑ i, partialZBarManifold (v_i) y`. Also ships the chart-pullback differentiability bridge `differentiableAt_extChartAt_pullback_of_contMDiff` (mirrors a private lemma in `ForsterCutoffPoleConstruction.lean`, exposed here in slightly more general form).
* **Trivial vanishing case** ([`Manifold/LocalPompeiuSolutionGlobalZeroOffTsupport.lean`](JacobianChallenge/Manifold/LocalPompeiuSolutionGlobalZeroOffTsupport.lean), 90 LOC): `partialZBarManifold v_i y = 0` for `y ∉ tsupport χ.toFun`. On an open neighborhood of `y`, `χ = 0` ⇒ `v_i = 0`; germ-dependence (5.4c-prep) ⇒ `∂̄_man v_i = ∂̄_man (const 0) = 0`.
* **Target partition-of-unity identity** ([`Manifold/PartitionSumMulAlpha.lean`](JacobianChallenge/Manifold/PartitionSumMulAlpha.lean), 73 LOC): `∑ i, ((P.rhoC i) * α) y = α y`. Lifts 5.2's `sum_rhoC_eq_one` (finsum form) to the pointwise finite-sum form via `Finset.sum_mul` + `finsum_eq_sum_of_fintype`. This is the **target** the ∂̄_man sum should equal once the (0,1)-form transition factor is handled.

### Sub-chips 5.5a + 5.5b — chart-anchored ∂̄ + per-i recovery (Path A, 2026-05-25)

* **`partialZBarManifoldAtChart`** ([`Manifold/PartialZBarManifoldAtChart.lean`](JacobianChallenge/Manifold/PartialZBarManifoldAtChart.lean), 207 LOC): `partialZBarManifoldAtChart x f y := partialZBar (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)` — the chart-anchored ∂̄. Distinct from `partialZBarManifold f y` (which uses chart-at-y); here the chart depends only on the anchor `x`. Ships zero/const/add/neg/sub algebra, `partialZBarManifoldAtChart_finset_sum` distributivity (parallel to `PartialZBarManifoldFinsetSum`), and the **transfer lemma** `partialZBarManifoldAtChart_eq_manifold_mul_transition`: for `y ∈ (chartAt ℂ x).source` with `(f ∘ chart_y.symm)` ℝ-differentiable at `chart_y y`, `partialZBarManifoldAtChart x f y = partialZBarManifold f y · conj(deriv (chart_y ∘ chart_x.symm)(chart_x y))`. The transfer lemma is a re-export of the existing Chip 4 content-agnostic bridge `partialZBar_chart_x_eq_manifold_mul_transition`; the only new content is the unified API + finset-sum lemma, but the architectural payoff is that subsequent 5.5 work happens in this anchored frame where partition sums are factor-free per-summand, and the chart-y reconciliation is consumed **once** at the end of 5.6 (not once per `i` in the sum).

  **Why Path A (vs Paths B/C)**: a 2026-05-25 inspection of `Manifold/ForsterCutoffPoleConstruction.lean` showed Forster's cutoff doesn't have an analogous τ-factor problem — its construction is single-chart-anchored and its Leibniz collapse trick depends on `chartInv`'s chart-y pullback being **ℂ-holomorphic** (via biholomorphic chart transitions), which `pompeiuKernel(...)` outputs are not (only ℝ-smooth). So no copy-paste from Forster cutoff. Path B (bake conj(τ_i) into the Pompeiu source) was ruled out because `τ_i(y)` involves `chart_y` which varies discontinuously over y in a charted space, so the Pompeiu source isn't smooth. Path C (carry τ_i factors through every assembly lemma) costs comparable to Path A but adds (0,1)-form bundle theory that isn't in mathlib at this pin. Path A — re-state each chip's identity in the anchored frame — keeps the chain-rule application local to the transfer lemma.

* **`partialZBarManifoldAtChart_localPompeiuSolutionGlobal_eq_rhoC_mul_alpha_on_support_rhoC`** ([`Manifold/LocalPompeiuSolutionAtChartIdentity.lean`](JacobianChallenge/Manifold/LocalPompeiuSolutionAtChartIdentity.lean), 132 LOC, Sub-chip 5.5b): the **factor-free per-i recovery in the construction chart**. On `support (P.rhoC i)`, `partialZBarManifoldAtChart i.val v_i y = (P.rhoC i * α) y` — no transition factor on the RHS. Proof composes (a) Sub-chip 5.4c-prep's local-coincidence `v_i =ᶠ[𝓝 y] chartPompeiuSolution i P α`, (b) the new germ-bridge `partialZBarManifoldAtChart_eventuallyEq_congr` (chart-anchored analogue of `partialZBarManifold_eventuallyEq_congr`, via `chart_x.continuousAt_symm` at `(chartAt ℂ x) y ∈ chart_x.target` + `Filter.EventuallyEq.fderiv_eq`), and (c) Sub-chip 5.4c-final's chart-x view evaluation `partialZBar_chartPompeiuSolution_chart_xi_symm_eq`. The hypothesis `y ∈ chart_xi.source` needed by (b) is supplied by the assembly layer's `support_rhoC_subset_chart_source`.

All axiom-free (`propext, Classical.choice, Quot.sound` only).

**Honest assessment of Path A reach (added 2026-05-25 after 5.5b):** 5.5b confirms the chart-anchored frame eliminates the τ factor *for the i-th summand evaluated in the i-th construction chart*. **However, the cross-summand contribution in the SAME anchored frame is NOT factor-free**: for `j ≠ i`, computing `partialZBarManifoldAtChart i.val v_j y` (i.e., the chart-x_i view of v_j's ∂̄) requires a Leibniz + chain-rule expansion that introduces `conj(τ_{j,i}(y)) := conj(deriv(chart_xj ∘ chart_xi.symm)(chart_xi y))`. Summing across j with the partition-of-unity target identity then gives `partialZBarManifoldAtChart i.val u y = Σ_j ρ_j(y) α(y) · conj(τ_{j,i}(y)) + cutoff_errors`, which equals `α(y) · conj(τ_i(y))` (the desired RHS) only if `Σ_j ρ_j(y) · τ_{j,i}(y) = τ_i(y)` — an identity that is **not generally true** as a partition-of-unity statement on derivatives of chart transitions. Path A relocates the τ factor from "per-`j` factor in chart-y identity" to "per-`j` factor in chart-anchored identity", but doesn't make the partition sum compose cleanly.

The structural obstruction is the same one that motivates (0,1)-form theory: α as a *function* `X → ℂ` is implicitly being treated as a (0,1)-form coefficient in some chart. Partition-of-unity of functions equals α; partition-of-unity of (0,1)-forms equals α-as-form. The two conflict under per-summand chart transitions. The codebase represents α as a function, so the per-summand chart-y / chart-anchored views don't sum coherently.

Concrete options for Sub-chip 5.5c (architectural choice needed):

* **5.5c-I — (0,1)-form theory build-out.** Lift α from `X → ℂ` to a section of the (0,1) bundle (or its concrete equivalent: a chart-coefficient family with explicit transition rule). The τ factors then cancel automatically. **Cost: ~1000–1500 LOC of bundle theory not in mathlib at this pin.** Highest functoriality cost but cleanest mathematical content.

* **5.5c-II — single-chart genus-0 globalization.** Skip the partition-of-unity assembly entirely. Use the fact that on a genus-0 compact RS, a single chart covers `X \ {p_∞}`. Build u as the Pompeiu solution in that single chart, then verify the smooth extension across p_∞ (requires bounded behavior at infinity, comes from compact support of α). **Cost: ~600–1000 LOC, but requires X ≃ ℂℙ¹ (uniformization-light) to reduce to a single-chart cover.** Requires more research into mathlib's RS uniformization assets.

* **5.5c-III — Behnke-Stein iteration (Forster Ch. 14 as originally planned).** Accept the τ-laden error `δ_0 := α · conj(τ_i) − partialZBarManifoldAtChart i.val u_0 y` on each support patch and prove this error is "smaller" in a norm sense, then iterate to convergence. This is the classical approach but requires Schauder-type estimates + geometric-series convergence on contracting annuli. **Cost: ~800–1200 LOC of analytic infrastructure**, comparable to the original Sub-chip 5.5 plan.

5.5a + 5.5b together = **clean primitives** in the anchored frame, useful in any of these three paths but not by themselves a partition-sum solution.

### Sub-chip 5.5c-I-a — `OmegaForm X` record + algebra (Route I, Option b, 2026-05-26)

* **`OmegaForm X`** ([`Manifold/OmegaForm.lean`](JacobianChallenge/Manifold/OmegaForm.lean), 234 LOC): a `(0,1)`-form on a complex 1-manifold `X`, encoded as a chart-coefficient family record (Option b from the audit — no full anti-cotangent bundle, just enough structure to support the partition-of-unity argument). Fields:
  * `coeff : X → (ℂ → ℂ)` — chart-`x` view as a function on `ℂ`.
  * `coeff_contDiffOn x : ContDiffOn ℝ ∞ (coeff x) ((chartAt ℂ x).target)` — smoothness on chart target.
  * `transition` — the `(0,1)` chart-change cocycle `coeff y (chart_y p) · conj(deriv (chart_y ∘ chart_x.symm)(chart_x p)) = coeff x (chart_x p)` for `p ∈ chart_x.source ∩ chart_y.source`.
  Algebra: `Zero`, `Add`, `Neg`, `Sub` (defined as `f + (-g)` for definitional `sub_eq_add_neg`), `SMul ℂ`, `AddCommGroup`, `Module ℂ`. Plus `OmegaForm.ext` and `transition_at_basepoint` sanity. Naming note: variable `ω` collides with the analytic-regularity literal `ω` opened via `Manifold` scope, so the file uses `f`, `g`, `h` for forms throughout. Sorry-free, axiom-free.

  **Open question surfaced while building 5.5c-I-a (TODO for 5.5c-I-b):** the *function-to-form lift* `OmegaForm.ofFunction α` for arbitrary smooth `α : X → ℂ` is **not straightforward**. Defining `coeff x := α ∘ chart_x.symm` on chart_x.target does *not* satisfy the transition cocycle (it would require `conj(Φ'(z_x)) = 1`, i.e., trivial atlas). The canonical-chart-coefficient interpretation — `α(y)` *is* the chart-`y` coefficient at `y` — uniquely determines a form-coefficient family ONLY if the resulting cocycle-extended chart-`x` coefficients are smooth functions, which depends on the chart at `y` varying locally constantly in `y`. For finite atlases (e.g. `RiemannSphere`'s two-chart atlas), `chartAt ℂ y` IS locally constant on the interior of each chart's source, so the lift works there; at chart-boundary points where canonical chart switches, extra care is needed. This means **5.5c-I-b should NOT be a general `OmegaForm.ofFunction`** — instead, the right primitive is `OmegaForm.ofChartLocalFunction xi (β : X → ℂ)` lifting a function supported in `chart_xi.source` to a form by specifying its chart-`xi` view as `β ∘ chart_xi.symm` and propagating to other charts via the cocycle (which IS automatic since `β` vanishes off `chart_xi.source` where the cocycle is vacuous).

  This shifts 5.5c-I-b's signature from "lift arbitrary smooth α" to "lift `ρ_i α` (supported in `chart_xi.source` by Sub-chip 5.4a) via chart-`xi` anchor" — directly compatible with how 5.4b's `localPompeiuSolutionGlobal P i α χ_i` is built. The partition sum `Σ_i (OmegaForm.ofChartLocalFunction i.val (ρ_i α))` is then a well-defined form on X, and 5.5c-I-c will show it equals `α-as-form` (under whatever interpretation lifts α coherently).

### Sub-chip 5.5c-I-b — chart-local coeff family + cocycle (2026-05-26)

* **`localFormCoeff x β y z`** ([`Manifold/OmegaFormOfChartLocal.lean`](JacobianChallenge/Manifold/OmegaFormOfChartLocal.lean), 312 LOC): the chart-`y` view of "β-as-form-anchored-at-`x`", defined via the cocycle formula `β(chart_y.symm z) / conj(deriv(chart_y ∘ chart_x.symm)(chart_x(chart_y.symm z)))` when `chart_y.symm z ∈ chart_x.source`, and `0` otherwise. Structural lemmas:
  * `localFormCoeff_of_mem` / `localFormCoeff_of_not_mem` — branch unfoldings.
  * `localFormCoeff_eq_zero_of_not_mem_tsupport` — vanishing off `tsupport β` for `p ∈ chart_y.source`.
  * `localFormCoeff_at_anchor_eqOn_target` — at `y = x` the coeff agrees with `chartPullbackZero x β` on `chart_x.target` (degenerate cocycle: `deriv (chart_x ∘ chart_x.symm) z = 1`, `conj 1 = 1`).
  * `deriv_chart_transition_ne_zero` — chart-transition derivatives don't vanish on chart overlaps (via the analyticity of both directions + chain-rule reduction to `deriv id = 1`).
  * **`localFormCoeff_transition`** — the headline `(0,1)`-form chart-change cocycle: for `p ∈ chart_x.source ∩ chart_y.source`, `localFormCoeff x β y (chart_y p) · conj(deriv(chart_y ∘ chart_x.symm)(chart_x p)) = localFormCoeff x β x (chart_x p)`.

  This file ships **definition + structural lemmas + cocycle only**. The smoothness proof `ContDiffOn ℝ ∞ (localFormCoeff x β y) ((chartAt ℂ y).target)` — needed to feed `OmegaForm`'s `coeff_contDiffOn` field — is a separate follow-up sub-chip (5.5c-I-b-smoothness, ~250–400 LOC: glue across the open cover `{chart_y.target ∩ chart_y.symm⁻¹(chart_x.source), chart_y.target \ chart_y '' (tsupport β ∩ chart_y.source)}`, smooth via Sub-chip 5.3b on the first piece + constantly zero on the second). Sorry-free, axiom-free.

### Sub-chip 5.5c-I-b-smoothness — smoothness of `localFormCoeff` on chart_y.target (2026-05-26)

* **`localFormCoeff_contDiffOn`** ([`Manifold/OmegaFormOfChartLocalSmoothness.lean`](JacobianChallenge/Manifold/OmegaFormOfChartLocalSmoothness.lean), 356 LOC): for `β : X → ℂ` manifold-smooth with `tsupport β ⊆ (chartAt ℂ x).source` and any `y : X`, `ContDiffOn ℝ ∞ (localFormCoeff x β y) ((chartAt ℂ y).target)`. Glue across two open sets:
  * **Set A** = `chart_y.target ∩ chart_y.symm⁻¹(chart_x.source)`: smoothness of the formula via `contDiffOn_formula_setA` (composition of smooth pieces: `β ∘ chart_y.symm`, `chart_x ∘ chart_y.symm`, `(deriv (chart_y ∘ chart_x.symm)) ∘ ...` via `analyticAt_chart_transition_of_isManifold` + `AnalyticAt.deriv` + `AnalyticAt.contDiffAt` + restrict-scalars via a local wrapper `contDiffAt_restrictScalars_R_C_C_local`, `Complex.conjCLE.contDiff` for `conj`, division as `mul ∘ inv` since `ContDiffOn.div` over ℝ with ℂ codomain isn't directly available).
  * **Set B** = `chart_y.target ∩ chart_y.symm⁻¹((tsupport β)ᶜ)`: `localFormCoeff x β y` vanishes here via `localFormCoeff_eq_zero_of_not_mem_tsupport`; `ContDiffOn.congr` against `contDiffOn_const`.
  Glue via `ContDiffOn.union_of_isOpen` (both sets manifestly open as intersections of open sets), with the cover identity `A ∪ B = chart_y.target` consuming the precondition `tsupport β ⊆ chart_x.source`: for any `p ∈ chart_y.source` with `p ∉ chart_x.source`, we have `p ∉ tsupport β` (contrapositive of `h_supp`), so `p ∈ (tsupport β)ᶜ`. Sorry-free, axiom-free.

### Sub-chip 5.5c-I-b-final — `OmegaForm.ofChartLocalFunction` constructor + general cocycle (2026-05-26)

* **`localFormCoeff_transition_general`** + **`OmegaForm.ofChartLocalFunction`** ([`Manifold/OmegaFormOfChartLocalConstructor.lean`](JacobianChallenge/Manifold/OmegaFormOfChartLocalConstructor.lean), 240 LOC):
  * `localFormCoeff_transition_general` upgrades the anchor-relative cocycle from 5.5c-I-b to a cocycle for **arbitrary chart pair** `(x1, y1)`. Case-split on `p ∈ chart_anchor.source`: if yes, apply the anchor-relative cocycle twice (to y1 and x1) and use the chain-rule identity `τ_{x → y1} = τ_{x1 → y1} · τ_{x → x1}` (via `deriv_comp` on `chart_y1 ∘ chart_x.symm = (chart_y1 ∘ chart_x1.symm) ∘ (chart_x1 ∘ chart_x.symm)` locally + `EventuallyEq.deriv_eq`) to cancel the anchor-shared factor. If no, `p ∉ tsupport β` (via `h_supp`), so both sides vanish via `localFormCoeff_eq_zero_of_not_mem_tsupport`. Final algebra: `mul_right_cancel₀` of conj(τ_{x → x1}) (nonzero by `deriv_chart_transition_ne_zero`).
  * **`OmegaForm.ofChartLocalFunction x β h_β_smooth h_β_supp`** — the headline constructor. Anchor `x`, source `β`, smoothness + `tsupport β ⊆ chart_x.source`. Yields an `OmegaForm X` with `coeff := localFormCoeff x β`, smoothness from `localFormCoeff_contDiffOn`, and the general cocycle from `localFormCoeff_transition_general`.
  * **Re-exports**: `ofChartLocalFunction_coeff` (`rfl`-unfolding), `ofChartLocalFunction_coeff_anchor_eqOn_target` (agreement with `chartPullbackZero` on chart_x.target), `ofChartLocalFunction_coeff_eq_zero_of_not_mem_tsupport`.

  Sub-chip 5.5c-I-b is now COMPLETE end-to-end: definition + cocycle + smoothness + constructor. Total LOC across the 5.5c-I-b sub-chip family: 312 (def+cocycle) + 356 (smoothness) + 240 (constructor) = 908 LOC, all axiom-free.

**Route I revised after this session's work (2026-05-26 end-of-day):**
the original audit's "OmegaForm partition-sum can't close" finding was
**too strong**. Under the additional global structural hypothesis
`∀ p, ChartAtConstantOnSource p` (innocuous on every concrete X — same
property the Forster §16.9 cutoff already takes at one point), the
partition-Pompeiu candidate `u := Σ_i v_i` satisfies the explicit
identity

```
partialZBarManifold u y = α y + outerRingLeakage P α χs y
```

(see `Manifold/OuterRingLeakage.lean`). The remaining content is the
**explicit computational statement** `outerRingLeakage = 0`, which
is the sum of cutoff-derivative-times-Pompeiu-kernel terms over the
outer rings of the χ_i — concrete, not a new named Prop.

The 5.5c-I-{a, b family, c, d, e, f, g, h, i} arc (~2280 LOC total,
includes this session's 1305 LOC) is now an OPERATIONAL FRAMEWORK
for the partition-Pompeiu route. Closing the outer-ring leakage
discharges DBarSolvabilityAtGenusZero X under the chart-locality
hypothesis.

Route: **Route III (Behnke-Stein iteration)** — user-selected
2026-05-26. Planning doc:
[`ROUTE_5_5C_III_PLAN.md`](ROUTE_5_5C_III_PLAN.md).

**Phase A landed (2026-05-26)** — sup-norm bound on `pompeiuKernel`:

* **5.5c-III-1a** ([`Analysis/InvNormIntegralBound.lean`](JacobianChallenge/Analysis/InvNormIntegralBound.lean), 115 LOC):
  `integral_inv_norm_closedBall_le (r : ℝ) (hr : 0 ≤ r) :
   ∫ ζ in closedBall (0 : ℂ) r, ‖ζ‖⁻¹ ∂volume ≤ r * (2 * π)`.
  Real-integral form of Chip 1b's lintegral polar bound. Side change:
  de-privatize `lintegral_inv_enorm_closedBall_le` in
  `InvNormIntegrability.lean` for downstream reuse.

* **5.5c-III-1b** ([`Analysis/PompeiuKernelSupNormBound.lean`](JacobianChallenge/Analysis/PompeiuKernelSupNormBound.lean), 241 LOC):
  `norm_pompeiuKernel_le_of_compact_support_in_ball`:
  for `tsupport α ⊆ closedBall 0 R` (R ≥ 0) + `‖α ζ‖ ≤ M`,
  `‖pompeiuKernel α z‖ ≤ 2 · (R + ‖z‖) · M` (no continuity needed).
  Method: Chip 2a's translated form + `norm_integral_le_of_norm_le`
  against `(closedBall (-z) R).indicator (M · ‖·‖⁻¹)` +
  `setIntegral_mono_set` via the inclusion
  `closedBall (-z) R ⊆ closedBall 0 (R + ‖z‖)` + Sub-chip 5.5c-III-1a.

**Critical risk RESOLVED 2026-05-26** via Forster Ch.14 / Berkeley
241/96 + 213b audit. Audit doc:
[`ROUTE_5_5C_III_FORSTER_PINNED.md`](ROUTE_5_5C_III_FORSTER_PINNED.md).

**Finding**: the original Behnke-Stein-iteration-on-X framing was
wrong. The classical compact-ℂℙ¹ proof has TWO distinct ingredients:

1. **Behnke-Stein iteration on the disk Δ** (Forster Thm 14 /
   McMullen Berkeley Thm 7.2): cutoff partition `g = Σ g_n` →
   per-piece Pompeiu solutions `f_n` → polynomial corrections `h_n`
   from Taylor truncation + `2^{-n}` Schwarz error → geometric-series
   `f := Σ (f_n - h_n)` converges in `C^∞`. **On the disk, not on
   `X`.**

2. **Cousin I / Laurent decomposition on the chart overlap `ℂ*`**
   (McMullen Cor 7.6 / Anagol §52): split `g_{12} ∈ O(ℂ*)` Laurent
   series into positive part `f_2 ∈ O(U_1)` and negative part
   `-f_1 ∈ O(U_2)`. Cocycle is coboundary, `H¹(ℂℙ¹, O) = 0`.

Iteration alone (without Cousin I) does **not** discharge the
compact case. The original Route III plan's Phases B-E (contraction
mapping on `X`) was based on a misreading; the corrected chip arc
is in `ROUTE_5_5C_III_FORSTER_PINNED.md`.

Phase A (the 356 LOC already landed) **carries over unchanged** —
it is the analytic foundation for both ingredients.

## Next-session entry — start here

The architectural compression after this session is:

```
∀ p, ChartAtConstantOnSource p           (structural — innocuous on concrete X)
                +
outerRingLeakage P α χs y = 0           (analytic — concrete computation)
        ⟹ DBarSolvabilityAtGenusZero X
        ⟹ hSP X
        ⟹ Item 14 (+ items 5, 11, 12, 13 via UniformizationGenus0Hypothesis)
```

`outerRingLeakage` is the **explicit Finset sum** over outer-ring
indices i of `partialZBarManifold (χ_i : ℂ) y · K_i(chart_{i.val} y)`,
defined in [`Manifold/OuterRingLeakage.lean`](JacobianChallenge/Manifold/OuterRingLeakage.lean)
+ [`Manifold/OuterRingIndices.lean`](JacobianChallenge/Manifold/OuterRingIndices.lean).
No new named Prop required.

### Three concrete next-chip options

1. **Cancellation argument for `outerRingLeakage = 0`.** Most
   direct continuation of this session. Needs either:
   * a specific choice of cover + cutoffs making the sum cancel
     (cover refinement; mostly already in tree from 5.1 + 5.4a;
     may need adjustment of cutoff overlap structure);
   * OR a Behnke-Stein-style iteration on the leakage operator
     (Phase B of [`ROUTE_5_5C_III_PLAN.md`](ROUTE_5_5C_III_PLAN.md);
     ~600-1000 LOC for the disk-level iteration, Phase A foundations
     already in tree from 5.5c-III-1a + 1b).

2. **Direct uniformization route.** Build `HolomorphicEquiv X RS`
   from `genus X = 0` + the existing
   `feat(jacobian-arc)` infrastructure (`UniformizationGenus0Hypothesis`,
   `FactUniformizationToRiemannSphere`, `pic0_holomorphicEquivCongr_*`,
   `BijectiveAnalyticToBiholomorphism`). Closes items 5, 11, 12, 13, 14
   simultaneously.

3. **RR + Serre on abstract X.**
   `LinearSystemGermDeltaPFiniteDim RiemannSphere` is unconditional;
   `RR_DimGE2_GenusZero_Germ X` reduces to uniformization-or-equivalent
   ([`Topology/LinearSystemGermDeltaPFiniteDimRSUnconditional.lean`](JacobianChallenge/Topology/LinearSystemGermDeltaPFiniteDimRSUnconditional.lean)).
   Pursue if uniformization is a wall but RR-on-abstract-X has a
   shorter path via classical RR formula formalization.

### Files modified / created this session

Created (~1660 LOC):
* `Analysis/InvNormIntegralBound.lean` (5.5c-III-1a, 115)
* `Analysis/PompeiuKernelSupNormBound.lean` (5.5c-III-1b, 241)
* `Manifold/OmegaPartitionSum.lean` (5.5c-I-c, 232)
* `Manifold/PartialZBarManifoldLocalPompeiuChartConst.lean` (5.5c-I-d, 159)
* `Manifold/GlobalSolutionUnderChartConst.lean` (5.5c-I-e, 138)
* `Manifold/LocalPompeiuSolutionLeibniz.lean` (5.5c-I-f, 222)
* `Manifold/LocalPompeiuSolutionLeibnizChartConst.lean` (5.5c-I-g, 161)
* `Manifold/OuterRingLeakage.lean` (5.5c-I-h, 215)
* `Manifold/OuterRingIndices.lean` (5.5c-I-i, 178)

Modified:
* `JacobianChallenge.lean` — library imports for all new files.
* `JacobianChallenge/Analysis/InvNormIntegrability.lean` —
  de-privatized `lintegral_inv_enorm_closedBall_le`.

Audit docs (5 new):
* `ROUTE_5_5C_FORSTER_AUDIT.md`, `ROUTE_5_5C_III_PLAN.md`,
  `ROUTE_5_5C_III_FORSTER_PINNED.md`, `DBAR_CONSUMER_AUDIT.md`,
  `REARCHITECTURE_AUDIT.md`, `UNIFORMIZATION_ROUTE_AUDIT.md`.

After exhaustive audit (2026-05-24) confirmed no route exists at this mathlib pin to close Item 14 without formalizing classical content, the **Pompeiu kernel + Riemann existence at genus 0** route was selected as the path with lowest expected surprise. Estimated remaining (post Chip 4): Chips 5-7 (~10-18 sessions).

### Where we are right now

* **Chip 1a — DONE** ([`Analysis/PompeiuKernel.lean`](JacobianChallenge/Analysis/PompeiuKernel.lean), commit `bcf6951`).
  - `pompeiuIntegrand`, `pompeiuKernel` definitions.
  - Measurability lemmas for the integrand.
  - `integrableOn_inv_norm_sub_iff_origin` — translation reduction.
  - `integrableOn_inv_norm_sub_of_not_mem_compact` — trivial case.
  - Sorry-free, axiom-free. Library entry added.
* **Chip 1b — DONE** ([`Analysis/InvNormIntegrability.lean`](JacobianChallenge/Analysis/InvNormIntegrability.lean), 163 LOC).
  - `integrableOn_inv_norm_closedBall (R : ℝ) : IntegrableOn (fun ζ : ℂ => ‖ζ‖⁻¹) (closedBall (0 : ℂ) R) volume`.
  - Auxiliary `lintegral_inv_enorm_closedBall_le` gives the quantitative
    bound `∫⁻ ζ in closedBall 0 R, ‖(‖ζ‖⁻¹ : ℝ)‖ₑ ∂volume ≤ (max R 0) * 2π`,
    proved by changing to polar coordinates via
    `Complex.lintegral_comp_polarCoord_symm`; the Jacobian factor cancels
    the integrand factor on `polarCoord.target` leaving an integrand
    bounded by `1`.
  - Sorry-free, axiom-free (`propext`, `Classical.choice`, `Quot.sound`
    only). Library entry added.
* **Chip 1c — DONE** ([`Analysis/PompeiuIntegrandIntegrability.lean`](JacobianChallenge/Analysis/PompeiuIntegrandIntegrability.lean), 140 LOC).
  - `integrable_pompeiuIntegrand_of_continuous_hasCompactSupport
      {α : ℂ → ℂ} (h_cont : Continuous α) (h_supp : HasCompactSupport α) (z : ℂ) :
      Integrable (pompeiuIntegrand α z) volume`.
  - Combines `Continuous.bounded_above_of_compact_support` (uniform
    bound `M` on `‖α‖`), `HasCompactSupport.isBounded.subset_closedBall`
    (`tsupport α ⊆ closedBall 0 R`), the geometric inclusion
    `closedBall 0 R ⊆ closedBall z (R + ‖z‖)`, Chip 1a's
    `integrableOn_inv_norm_sub_iff_origin`, and Chip 1b's
    `integrableOn_inv_norm_closedBall`. Pointwise domination is via the
    enorm identity `‖w⁻¹‖ₑ = ‖(‖w‖⁻¹ : ℝ)‖ₑ` for `w : ℂ`.
  - Sorry-free, axiom-free. Library entry added.
* **Chip 2a — DONE** ([`Analysis/PompeiuKernelTranslation.lean`](JacobianChallenge/Analysis/PompeiuKernelTranslation.lean), 114 LOC).
  - `pompeiuKernel_eq_translated_integrand (α : ℂ → ℂ) (z : ℂ) :
      pompeiuKernel α z = -((Real.pi : ℂ)⁻¹) * ∫ η, α (η + z) * η⁻¹`.
  - Companion `integrable_translated_pompeiuIntegrand_of_continuous_hasCompactSupport`
    transports Chip 1c's integrability to the translated integrand
    via `measurePreserving_add_right`.
  - Pushes the `z`-dependence out of the singular factor `(ζ - z)⁻¹`
    and into the regular factor `α (η + z)`. With the singularity now
    pinned at `η = 0` (independent of `z`), differentiation under the
    integral (Chips 2b/2c) reduces to a routine dominated-convergence
    argument: the dominating function is integrable once (Chip 1c)
    rather than once per `z`.
  - Sorry-free, axiom-free. Library entry added.
* **Chip 2c-prep — DONE** ([`Analysis/PompeiuKernelDirectionalIntegrand.lean`](JacobianChallenge/Analysis/PompeiuKernelDirectionalIntegrand.lean), 135 LOC).
  - `αDeriv α v ζ := fderiv ℝ α ζ v` — directional derivative as a
    `ℂ → ℂ` function.
  - `αDeriv_hasCompactSupport` (from `HasCompactSupport.fderiv_apply`)
    and `αDeriv_continuous` (from `ContDiff.continuous_fderiv` +
    `ContinuousLinearMap.apply` continuity) — input shape for Chips
    1c and 2b.
  - `integrable_pompeiuIntegrand_αDeriv` and
    `continuous_pompeiuKernel_αDeriv` — Chips 1c and 2b applied to
    `αDeriv α v`, giving integrability and continuity of the
    directional-derivative Pompeiu integrand and kernel.
  - `exists_fderiv_norm_bound` — uniform bound `M'` with
    `‖fderiv ℝ α ζ‖ ≤ M'` for all `ζ`, via
    `Continuous.bounded_above_of_compact_support` on `fderiv ℝ α`
    (which has compact support and is continuous for `α ∈ C^1`).
  - `norm_αDeriv_le` — pointwise `‖αDeriv α v ζ‖ ≤ M' · ‖v‖` from the
    uniform bound and `ContinuousLinearMap.le_opNorm`.
  - Sorry-free, axiom-free. Library entry added.
* **Chip 2b — DONE** ([`Analysis/PompeiuKernelContinuity.lean`](JacobianChallenge/Analysis/PompeiuKernelContinuity.lean), 157 LOC).
  - `continuous_pompeiuKernel_of_continuous_hasCompactSupport
      {α : ℂ → ℂ} (h_cont : Continuous α) (h_supp : HasCompactSupport α) :
      Continuous (pompeiuKernel α)`.
  - For each `z₀`, the dominating function `K.indicator (fun η => M · ‖η‖⁻¹)`
    with `K := closedBall 0 (R + ‖z₀‖ + 1)` works uniformly for
    `z ∈ closedBall z₀ 1`: outside `K`, the triangle inequality
    `‖η + z‖ ≥ ‖η‖ - ‖z‖ > R` forces `α (η + z) = 0`; inside `K`,
    the bound is `M · ‖η‖⁻¹`. Integrability via Chip 1b's
    `integrableOn_inv_norm_closedBall` + `IntegrableOn.const_mul`
    + `IntegrableOn.integrable_indicator`. Apply
    `MeasureTheory.continuousAt_of_dominated` for each `z₀` and lift
    via `continuous_iff_continuousAt`.
  - Sorry-free, axiom-free. Library entry added.

* **Chip 2c-main — DONE** ([`Analysis/PompeiuKernelDerivative.lean`](JacobianChallenge/Analysis/PompeiuKernelDerivative.lean), 292 LOC).
* **Chip 2d — DONE** ([`Analysis/PompeiuKernelSmoothness.lean`](JacobianChallenge/Analysis/PompeiuKernelSmoothness.lean), 515 LOC, commit pending).
  - `pompeiuFDerivIntegrand α z η := (η⁻¹ : ℂ) • fderiv ℝ α (η + z) : ℂ →L[ℝ] ℂ` — CLM-valued integrand for the complex-parameter derivative.
  - `hasFDerivAt_translated_integral` — `HasFDerivAt` for `z ↦ ∫ η, α(η + z) * η⁻¹` at any `z₀`, derivative `∫ η, pompeiuFDerivIntegrand α z₀ η`. Proven by `MeasureTheory.hasFDerivAt_integral_of_dominated_of_fderiv_le` with `K := closedBall 0 (R + ‖z₀‖ + 1)` and uniform-in-`z ∈ ball z₀ 1` dominating function `K.indicator (M' · ‖η‖⁻¹)`.
  - `integrable_pompeiuFDerivIntegrand` — integrability of the CLM-valued integrand (needed for `ContinuousLinearMap.integral_apply`).
  - `hasFDerivAt_pompeiuKernel` — scaled by `-(π⁻¹)` via `HasFDerivAt.const_mul`, with the function side rewritten using Chip 2a's translated form.
  - `fderiv_pompeiuKernel_apply` — **the inductive engine**: `fderiv ℝ (pompeiuKernel α) z₀ v = pompeiuKernel (αDeriv α v) z₀`. Proven by `ContinuousLinearMap.integral_apply` + commutativity + Chip 2a applied to `αDeriv α v`.
  - `contDiff_αDeriv` — `α ∈ C^(n+1)` ⇒ `αDeriv α v ∈ C^n` (via `contDiff_succ_iff_fderiv` + `ContinuousLinearMap.apply` smoothness).
  - `contDiff_pompeiuKernel_of_nat` — **the induction**: `∀ n : ℕ`, `ContDiff ℝ n α → HasCompactSupport α → ContDiff ℝ n (pompeiuKernel α)`. Base case `n = 0` via Chip 2b's continuity. Successor via `contDiff_succ_iff_fderiv_apply` (uses finite-dimensionality of `ℂ` over `ℝ`): differentiability from `hasFDerivAt_pompeiuKernel`, ω case vacuous (`(k : WithTop ℕ∞) ≠ ⊤`), and for each `v`, `(fun z => fderiv ℝ (pompeiuKernel α) z v) = pompeiuKernel (αDeriv α v)` is `C^n` by IH on `αDeriv α v`.
  - `contDiff_pompeiuKernel_infty` — **main theorem**: `ContDiff ℝ ∞ α → HasCompactSupport α → ContDiff ℝ ∞ (pompeiuKernel α)`. Via `contDiff_infty : ContDiff 𝕜 ∞ f ↔ ∀ n : ℕ, ContDiff 𝕜 n f`.
  - Sorry-free, axiom-free (`propext`, `Classical.choice`, `Quot.sound` only). Library entry added.
  - `hasDerivAt_pompeiuKernel_real_direction
      {α : ℂ → ℂ} (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
      (v z₀ : ℂ) :
      HasDerivAt (fun t : ℝ => pompeiuKernel α (z₀ + (t : ℝ) • v))
        (pompeiuKernel (αDeriv α v) z₀) 0`.
  - Applies `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
    on Chip 2a's translated parametric integral. Dominating function
    `K.indicator (fun η => M' · ‖v‖ · ‖η‖⁻¹)` with
    `K := closedBall 0 (R + ‖z₀‖ + ‖v‖ + 1)`. Outside `K`, the path
    `η + z₀ + t • v` stays outside `tsupport α` for all
    `t ∈ Ioo (-1) 1`, so `fderiv ℝ α (η + z₀ + t • v) = 0`
    (`fderiv_of_notMem_tsupport`). Identifies both function and
    derivative with `pompeiuKernel` via Chip 2a + `HasDerivAt.const_mul (-π⁻¹)`.
  - Sorry-free, axiom-free. Library entry added.

* **Chip 3c-E — DONE** (two files: [`Analysis/PompeiuKernelPlaneIntegral.lean`](JacobianChallenge/Analysis/PompeiuKernelPlaneIntegral.lean), ~230 LOC + [`Analysis/PompeiuKernelDCTLimit.lean`](JacobianChallenge/Analysis/PompeiuKernelDCTLimit.lean), ~406 LOC; 636 LOC total).
  - **Section A — Fubini bridge** ([`PompeiuKernelPlaneIntegral.lean`](JacobianChallenge/Analysis/PompeiuKernelPlaneIntegral.lean)):
    `integral_complex_eq_iteratedIntegral_of_tsupport_in_ball
        {f : ℂ → ℂ} (h_int : Integrable f) {L : ℝ} (hL_pos : 0 < L)
        (h_supp : tsupport f ⊆ Metric.ball 0 L) :
        ∫ ζ : ℂ, f ζ = ∫ x in -L..L, ∫ y in -L..L, f ((x : ℂ) + y * I)`.
    Converts Chip 3c-D's iterated-integral form into the plane
    (Bochner-over-ℂ) form. Chain: `Complex.volume_preserving_equiv_real_prod`
    (`ℂ ↔ ℝ × ℝ` change of variables) → `MeasureTheory.integral_prod`
    (Fubini) → `setIntegral_eq_integral_of_forall_compl_eq_zero` (cut both
    `ℝ`-integrals to `Ioc (-L) L` using compact support in `ball 0 L`)
    → `intervalIntegral.integral_of_le` (convert to interval integrals).
  - **Section B — plane-form balance equation** ([`PompeiuKernelDCTLimit.lean`](JacobianChallenge/Analysis/PompeiuKernelDCTLimit.lean)):
    `balance_plane_eq_zero
        (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
        (z : ℂ) {ε : ℝ} (hε : 0 < ε)
        {L : ℝ} (hL_pos : 0 < L) (hL_supp : tsupport α ⊆ Metric.ball 0 L) :
        ∫ ζ : ℂ, partialZBar α ζ * regularizedInvSub z hε ζ
          + α ζ * partialZBar (regularizedInvSub z hε) ζ = 0`.
    Applies Section A's Fubini bridge to Chip 3c-D's iterated balance,
    using `tsupport_partialZBar_subset` (Wirtinger-derivative support
    bound via `tsupport_fderiv_apply_subset` + `tsupport_mul_subset_right`
    + `tsupport_add`) and `tsupport_mul_subset_left` to certify the
    integrand support sits in `tsupport α ⊆ Metric.ball 0 L`.
    Supporting: continuity + compact-support preservation lemmas for
    both summands (`integrable_partialZBar_mul_regInvSub`,
    `integrable_alpha_mul_partialZBar_regInvSub`).
  - **Section C — DCT limit on the first summand** ([`PompeiuKernelDCTLimit.lean`](JacobianChallenge/Analysis/PompeiuKernelDCTLimit.lean)):
    `tendsto_integral_partialZBar_alpha_mul_regInvSub
        (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α) (z : ℂ) :
        Tendsto (fun ε : ℝ =>
            ∫ ζ : ℂ, partialZBar α ζ * regularizedInvSubReal z ε ζ)
          (𝓝[>] (0 : ℝ))
          (𝓝 (∫ ζ : ℂ, partialZBar α ζ * (ζ - z)⁻¹))`.
    Mathlib's `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`
    on filter `𝓝[>] (0 : ℝ)` (countably-generated), with:
    - Dominator `‖partialZBar α ζ‖ * ‖(ζ - z)⁻¹‖` integrable via Chip 1c
      (`integrable_pompeiuIntegrand_of_continuous_hasCompactSupport`)
      applied to `partialZBar α` (continuous + compactly-supported, via
      `partialZBar_continuous` + `partialZBar_hasCompactSupport`).
    - Pointwise convergence: at `ζ ≠ z`, the wrapper is eventually
      `(ζ - z)⁻¹` (because `pompeiuCutoff z hε ζ = 1` for `ε < dist ζ z`);
      at `ζ = z`, both function values and the limit value are `0` (since
      `(z - z)⁻¹ = 0` and `pompeiuCutoff z hε z = 0`).
    - Pointwise norm bound `‖regularizedInvSub z hε ζ‖ ≤ ‖(ζ - z)⁻¹‖`
      via `|pompeiuCutoff z hε ζ| ≤ 1`.
    Wrapper `regularizedInvSubReal z ε : ℂ → ℂ` is `regularizedInvSub z hε`
    for `0 < ε` and defaults to `(·-z)⁻¹` on `ε ≤ 0` (matches the limit),
    eliminating the dependent-type complication for `Tendsto`.
  - The RHS `∫ ζ, partialZBar α ζ * (ζ - z)⁻¹` equals
    `-π · pompeiuKernel (partialZBar α) z` by definition of `pompeiuKernel`.
  - Sorry-free, axiom-free (`propext`, `Classical.choice`, `Quot.sound`
    only). Library entries added.
  - **What is NOT in this chip (deferred to Chip 3c-F):**
    1. The matching DCT limit on the second summand
       `∫ ζ : ℂ, α ζ * partialZBar (regularizedInvSub z hε) ζ → π · α z`.
       This needs the radial-bump rescaling `η = z + ε·w` + polar-coords
       calculation `∫∫ (∂̄φ_1)(w)/w dA = -π`, which depends on accessing
       the radial structure of mathlib's `ContDiffBump` (currently abstract
       via the `HasContDiffBump`/`someContDiffBumpBase` typeclass mechanism;
       the inner-product instance `ofInnerProductSpace` IS radially
       symmetric in `‖x‖`, but extracting that for the `pompeiuBump`
       requires either a typeclass-unfolding workaround or constructing
       an explicit radial bump from scratch — both are substantive).
    2. Combining the two DCT limits with `balance_plane_eq_zero` to get
       `pompeiuKernel (partialZBar α) z = α z` (the trivial step once
       Item 1 is in hand).
    3. Composition with Chip 3b's
       `partialZBar_pompeiuKernel_eq_pompeiuKernel_partialZBar` to give
       the final `partialZBar (pompeiuKernel α) z = α z` (trivial).
  - **Estimate for Chip 3c-F**: ~600-1500 LOC, 3-6 sessions. The radial-bump
    machinery is the heaviest classical content in the entire Pompeiu arc.

* **Chip 3c-D — DONE** ([`Analysis/PompeiuKernelStokes.lean`](JacobianChallenge/Analysis/PompeiuKernelStokes.lean), ~370 LOC).
  - **Main theorem (Stokes-for-`∂̄`)**:
    `iteratedIntegral_partialZBar_eq_zero
        {f : ℂ → ℂ} (h_smooth : ContDiff ℝ 1 f) {L : ℝ} (hL_pos : 0 < L)
        (hL_supp : tsupport f ⊆ Metric.ball 0 L) :
        ∫ x in -L..L, ∫ y in -L..L, partialZBar f (x + y * I) = 0`.
    For any compactly-supported `C¹` function `f`, the iterated `∂̄`
    integral over a large enough square rectangle vanishes.
  - **Application (balance equation)**:
    `balance_iteratedIntegral_eq_zero
        {α : ℂ → ℂ} (h_α : ContDiff ℝ 1 α) (z : ℂ) {ε : ℝ} (hε : 0 < ε)
        {L : ℝ} (hL_pos : 0 < L) (hL_supp : tsupport α ⊆ Metric.ball 0 L) :
        ∫ x in -L..L, ∫ y in -L..L,
          partialZBar α (x+y*I) * regularizedInvSub z hε (x+y*I)
            + α (x+y*I) * partialZBar (regularizedInvSub z hε) (x+y*I) = 0`.
    The iterated-integral form of integration-by-parts in the
    Cauchy-Pompeiu argument.
  - Proof of Stokes-for-`∂̄`:
    1. Apply mathlib's
       `Complex.integral_boundary_rect_of_differentiableOn_real` on the
       square `[-L, L]²` (corners `z₀ := -L - L·I`, `w₀ := L + L·I`).
    2. All four boundary line integrals vanish:
       `intervalIntegral_zero_on_uIcc_{horiz,vert}` + helpers
       `norm_horiz_ge`, `norm_vert_ge` (every boundary point has
       Euclidean norm `≥ L`, hence outside `ball 0 L`, hence outside
       `tsupport f`, hence `f = 0` there).
    3. Algebraic identity `partialZBar_eq_integrand_div_two_I`:
       `I • fderiv ℝ f x 1 - fderiv ℝ f x I = 2 * I * partialZBar f x`
       (direct from the Wirtinger definition).
    4. Pull `2 * I` out of both interval integrals (via
       `intervalIntegral.integral_const_mul`); divide by the nonzero
       scalar.
  - Application: combine Stokes with Leibniz expansion
    `partialZBar_alpha_mul_regInvSub` (using existing
    `partialZBar_mul` from `Manifold/PartialZBar.lean` + Chip 3c-C₂'s
    `regularizedInvSub_contDiff`) and
    `tsupport_alpha_mul_regInvSub_subset` (product support is in
    factor support).
  - Sorry-free, axiom-free (`propext`, `Classical.choice`, `Quot.sound`
    only). Library entry added.

* **Chip 3c-C₂ — DONE** ([`Analysis/PompeiuKernelRegularizedInv.lean`](JacobianChallenge/Analysis/PompeiuKernelRegularizedInv.lean), ~140 LOC).
  - `regularizedInvSub z hε : ℂ → ℂ` —
    `regularizedInvSub z hε η := (η - z)⁻¹ * ((pompeiuCutoff z hε η : ℝ) : ℂ)`.
  - `regularizedInvSub_contDiff
      (z : ℂ) {ε : ℝ} (hε : 0 < ε) {n : ℕ∞} :
      ContDiff ℝ n (regularizedInvSub z hε)`.
  - Proof: case-split on `ζ = z` vs `ζ ≠ z` via
    `contDiff_iff_contDiffAt`:
    * `ζ ≠ z` — `regularizedInvSub_contDiffAt_of_ne`. Product of
      `(·-z)⁻¹` (smooth at `ζ` via `contDiffAt_inv` over `ℂ` composed
      with `sub_const` and `restrict_scalars ℝ` under the same
      `set_option backward.isDefEq.respectTransparency false in`
      diamond workaround as 3c-A/3c-B) and `((pompeiuCutoff · : ℝ) : ℂ)`
      (smooth via `Complex.ofRealCLM.contDiff` ∘ `pompeiuCutoff_contDiff`).
    * `ζ = z` — `regularizedInvSub_contDiffAt_of_eq`. Use
      `regularizedInvSub =ᶠ[𝓝 z] 0` (from Chip 3c-C₁'s
      `pompeiuCutoff_eventuallyEq_zero` carried through via
      `filter_upwards`), so `ContDiffAt.congr_of_eventuallyEq` with
      `contDiffAt_const` finishes.
  - Supporting helpers: `contDiff_ofReal`, `contDiffAt_inv_sub_const`,
    `regularizedInvSub_eventuallyEq_zero`.
  - Sorry-free, axiom-free (`propext`, `Classical.choice`, `Quot.sound`
    only). Library entry added.

* **Chip 3c-C₁ — DONE** ([`Analysis/PompeiuKernelCutoff.lean`](JacobianChallenge/Analysis/PompeiuKernelCutoff.lean), ~160 LOC).
  - `pompeiuCutoff (z : ℂ) {ε : ℝ} (hε : 0 < ε) : ℂ → ℝ` — the cutoff
    function `χ_ε(η) := 1 - bump(η)` where `bump : ContDiffBump z` has
    `rIn := ε/2`, `rOut := ε`. The underlying bump is exposed as
    `pompeiuBump z hε`.
  - Key properties (all sorry- and axiom-free):
    * `pompeiuCutoff_eq_zero_of_mem_closedBall_half` — `χ_ε(ζ) = 0` on
      `closedBall z (ε/2)`.
    * `pompeiuCutoff_eq_one_of_not_mem_ball` — `χ_ε(ζ) = 1` outside
      `ball z ε`.
    * `pompeiuCutoff_nonneg`, `pompeiuCutoff_le_one` — `0 ≤ χ_ε ≤ 1`.
    * `pompeiuCutoff_contDiff` — `ContDiff ℝ n χ_ε` for all `n`.
    * `pompeiuCutoff_eventuallyEq_zero` — `χ_ε =ᶠ[𝓝 z] 0`. This is
      the key fact that makes the regularized integrand `α · (·-z)⁻¹ · χ_ε`
      smooth even at `η = z`.
    * `one_sub_pompeiuCutoff_eq_bump`, `tsupport_one_sub_pompeiuCutoff_subset` —
      the "interior" `(1 - χ_ε)` equals the bump, hence is compactly
      supported in `closedBall z ε`.
  - Uses mathlib's `ContDiffBump` (`Analysis/Calculus/BumpFunction/Basic.lean`)
    with `HasContDiffBump ℂ` via the inner-product-space instance
    (`Analysis/Calculus/BumpFunction/InnerProduct.lean:57`).
  - Library entry added.

* **Chip 3c-B — DONE** ([`Analysis/PompeiuKernelMulInvFDeriv.lean`](JacobianChallenge/Analysis/PompeiuKernelMulInvFDeriv.lean), ~130 LOC).
  - `hasFDerivAt_mul_inv_sub
      {α : ℂ → ℂ} {ζ : ℂ}
      (h_α : HasFDerivAt α (fderiv ℝ α ζ) ζ) (z : ℂ) (hζ : ζ ≠ z) :
      HasFDerivAt (fun η : ℂ => α η * (η - z)⁻¹)
        (α ζ • ((smulRight (1 : ℂ →L[ℂ] ℂ) (-((ζ-z)^2)⁻¹)).restrictScalars ℝ)
          + (ζ - z)⁻¹ • fderiv ℝ α ζ)
        ζ`. Plus the `ContDiff ℝ 1`-input corollary
    `hasFDerivAt_mul_inv_sub_of_contDiff`.
  - This is the **input shape** required by mathlib's rectangle Stokes
    (`Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable`),
    whose `Hd` hypothesis demands `HasFDerivAt f (f' x) x` pointwise
    off a countable bad set. With Chip 3c-B, the lone singularity `z`
    becomes the only point we exclude (`s = {z}`).
  - Proof: build `HasDerivAt (fun η => (η - z)⁻¹) (-(ζ-z)⁻²) ζ` over `ℂ`
    via `hasDerivAt_inv` composed with `sub_const` and `HasDerivAt.comp`,
    convert to `ℂ`-`HasFDerivAt`, restrict scalars to `ℝ` (with the same
    `set_option backward.isDefEq.respectTransparency false in` diamond
    workaround as Chip 3c-A), then product-rule via `HasFDerivAt.mul`.
  - Supporting helpers:
    * `hasDerivAt_inv_sub_const` — the `ℂ`-`HasDerivAt`.
    * `hasFDerivAt_real_inv_sub_const` — the `ℝ`-`HasFDerivAt` of `(·-z)⁻¹`.
  - Sorry-free, axiom-free (`propext`, `Classical.choice`, `Quot.sound`
    only). Library entry added.

* **Chip 3c-A — DONE** ([`Analysis/PompeiuKernelLeibniz.lean`](JacobianChallenge/Analysis/PompeiuKernelLeibniz.lean), ~115 LOC).
  - `partialZBar_mul_inv_sub
      {α : ℂ → ℂ} {ζ : ℂ} (h_diff : DifferentiableAt ℝ α ζ) (z : ℂ) (hζ : ζ ≠ z) :
      partialZBar (fun η : ℂ => α η * (η - z)⁻¹) ζ
        = partialZBar α ζ * (ζ - z)⁻¹`.
  - This is the pointwise off-singularity Leibniz reduction that drives
    Chip 3c's rectangle-Stokes argument: on `ζ ≠ z`, the antiholomorphic
    derivative of the Pompeiu integrand collapses to `(∂̄α)(ζ) · (ζ-z)⁻¹`
    because the singular factor `(η - z)⁻¹` is `ℂ`-holomorphic at `η = ζ`
    (Cauchy-Riemann ⇒ `partialZBar = 0`).
  - Proof: apply existing `partialZBar_mul` (Leibniz) from
    `Manifold/PartialZBar.lean` to `f := α`, `g := (· - z)⁻¹`; the second
    Leibniz term vanishes via `partialZBar_eq_zero_of_differentiableAt`
    applied to the `ℂ`-differentiability of `g` at `ζ ≠ z`.
  - Supporting helpers:
    * `differentiableAt_inv_sub_const` — `DifferentiableAt ℂ ((· - z)⁻¹)`
      at `ζ ≠ z`, via `differentiableAt_inv_iff` composed with
      `differentiableAt_id.sub_const`.
    * `differentiableAt_real_inv_sub_const` — the same fact over `ℝ`,
      using `DifferentiableAt.restrictScalars ℝ`. The
      `set_option backward.isDefEq.respectTransparency false in`
      annotation mirrors mathlib's `HasDerivAt.real_of_complex`
      (`Mathlib/Analysis/Complex/RealDeriv.lean:44`) and dodges the
      `IsScalarTower ℝ ℂ ℂ` instance-synthesis diamond flagged in
      `feedback_jacobian_complex_real_diamond` memory.
    * `partialZBar_inv_sub_const_eq_zero` — the Cauchy-Riemann step.
  - Sorry-free, axiom-free (`propext`, `Classical.choice`, `Quot.sound`
    only). Library entry added.

* **Chip 3b — DONE** ([`Analysis/PompeiuKernelPartialZBarBridge.lean`](JacobianChallenge/Analysis/PompeiuKernelPartialZBarBridge.lean), ~180 LOC).
  - `partialZBar_pompeiuKernel_eq_pompeiuKernel_partialZBar
      {α : ℂ → ℂ} (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
      (z : ℂ) :
      partialZBar (pompeiuKernel α) z = pompeiuKernel (partialZBar α) z`.
  - This algebraic bridge reduces the full Cauchy-Pompeiu identity to
    the single classical statement `pompeiuKernel (partialZBar α) z = α z`
    (Chip 3c).
  - Proof: Chip 2d's `fderiv_pompeiuKernel_apply` specialized at
    `v = 1` and `v = I` rewrites the LHS as
    `(1/2) · (pompeiuKernel (αDeriv α 1) z + I · pompeiuKernel (αDeriv α I) z)`.
    By definition `partialZBar α ζ = (1/2) · (αDeriv α 1 ζ) + ((1/2)·I) · (αDeriv α I ζ)`
    pointwise, so the RHS expands the same way via `pompeiuKernel` linearity.
  - Supporting infrastructure (general-purpose, used here and useful
    downstream):
    * `pompeiuKernel_add` — additivity, for continuous compactly-supported
      `α, β` (both integrands integrable by Chip 1c, then
      `MeasureTheory.integral_add`).
    * `pompeiuKernel_const_mul` — `pompeiuKernel (c · α) z = c · pompeiuKernel α z`.
      Unconditional in `α` (Bochner's `integral_const_mul` does not need
      integrability — when not integrable both sides are zero).
    * `pompeiuIntegrand_add`, `pompeiuIntegrand_const_mul` — pointwise
      integrand helpers.
  - Sorry-free, axiom-free (`propext`, `Classical.choice`, `Quot.sound`
    only). Library entry added.

* **Chip 3a — DONE** ([`Analysis/PompeiuKernelSmallDiscLimit.lean`](JacobianChallenge/Analysis/PompeiuKernelSmallDiscLimit.lean), ~250 LOC).
  - `tendsto_circleIntegral_pompeiu_smallDisc
      {α : ℂ → ℂ} (h_cont : Continuous α) (z : ℂ) :
      Tendsto (fun ε : ℝ => ∮ ζ in C(z, ε), α ζ * (ζ - z)⁻¹) (𝓝[>] 0)
        (𝓝 (α z * (2 * ↑π * I)))`.
  - Pointwise decomposition
    `α ζ · (ζ - z)⁻¹ = α z · (ζ - z)⁻¹ + (α ζ - α z) · (ζ - z)⁻¹`
    is lifted to circle integrals on `C(z, ε)` for `ε > 0` via
    `circleIntegral.integral_add`. Both pieces are circle-integrable
    because the singularity at `ζ = z` sits at the centre, not on the
    sphere.
  - Constant piece evaluates exactly: `∮ α z · (ζ - z)⁻¹ = α z · (2πi)`
    via `circleIntegral.integral_const_mul` +
    `circleIntegral.integral_sub_inv_of_mem_ball` with `w = z, c = z,
    R = ε > 0` (so `z ∈ ball z ε`).
  - Remainder is controlled by the modulus of continuity at `z`:
    `‖(α ζ - α z) · (ζ - z)⁻¹‖ ≤ C / ε` on `sphere z ε` where
    `‖ζ - z‖ = ε`, hence
    `‖∮ (α ζ - α z) · (ζ - z)⁻¹‖ ≤ 2 * π * ε * (C / ε) = 2 * π * C`
    via `circleIntegral.norm_integral_le_of_norm_le_const`. For
    `ε < r` from continuity-at-`z` with tolerance `δ / (2π + 1)`, the
    full bound is `2π · δ / (2π + 1) < δ`.
  - Helpers: `circleIntegrable_smul_inv_sub_of_continuous`,
    `circleIntegrable_const_smul_inv_sub`,
    `circleIntegrable_remainder`, `circleIntegral_constant_smul_sub_inv`,
    `norm_circleIntegral_remainder_le`,
    `circleIntegral_pompeiu_decompose`.
  - Sorry-free, axiom-free (`propext`, `Classical.choice`, `Quot.sound`
    only). Library entry added.

### Chip 3c-F — **IN FLIGHT**: radial-bump limit on second summand + final identity

Chip 3c-F broke into sub-pieces. Option (b) above (build an explicit
radial bump from scratch) was chosen — much cleaner than chasing
typeclass-unfolding workarounds for mathlib's abstract `ContDiffBump`.

#### Sub-pieces landed

* **Chip 3c-F-1 — DONE** (commit `d99d822`, two files):
  - [`Analysis/PompeiuKernelRadialBump.lean`](JacobianChallenge/Analysis/PompeiuKernelRadialBump.lean) (~160 LOC):
    `psiBump ε r := Real.smoothTransition (2 - 2r/ε)` (1D radial profile),
    `radialBump z ε η := psiBump ε ‖η - z‖` (the bump on ℂ — radially
    symmetric by construction), `radialCutoff z ε η := 1 - radialBump z ε η`.
    Mirrors `pompeiuBump`/`pompeiuCutoff`'s properties (= 1 on
    `closedBall z (ε/2)`, = 0 outside `ball z ε`, bounded by 1, `ContDiff`,
    `=ᶠ[𝓝 z] 0`).
  - [`Analysis/PompeiuKernelRadialWirtinger.lean`](JacobianChallenge/Analysis/PompeiuKernelRadialWirtinger.lean) (~200 LOC):
    `partialZBar_radial_of_ne : η ≠ z → HasDerivAt ψ ψ' ‖η-z‖ →
       partialZBar (fun w => (ψ ‖w-z‖ : ℂ)) η = (ψ'/2) * (η - z) / ‖η - z‖`.
    Proven via `hasFDerivAt_norm_sq_sub_const` (mathlib's
    `fderiv_norm_sq_apply` + chain rule for `(· - z)`), `HasFDerivAt.sqrt`,
    `Complex.ofRealCLM.hasFDerivAt`, `innerSL_{one,I}_complex` evaluations
    via `Complex.inner`, and `Complex.re_add_im` for the final assembly.

* **Chip 3c-F-2-prep — DONE** (commit `07333c8`, two files):
  - [`Analysis/PompeiuKernelRadialIntegrand.lean`](JacobianChallenge/Analysis/PompeiuKernelRadialIntegrand.lean) (~80 LOC):
    `partialZBar_radial_div_eq_radial : η ≠ 0 → HasDerivAt ψ ψ' ‖η‖ →
       partialZBar (fun w => (ψ ‖w‖ : ℂ)) η / η = (ψ' / (2·‖η‖) : ℂ)`.
    The `η/‖η‖` factor from Wirtinger cancels with the dividing `η`.
  - [`Analysis/PompeiuKernelRadialIntegral.lean`](JacobianChallenge/Analysis/PompeiuKernelRadialIntegral.lean) (initial ~150 LOC):
    `unitRadialBumpC w := (radialBump 0 1 w : ℂ)` (unit-scale ℂ-valued bump),
    boundary values (`psiBump_one_{zero,one,...}`), polar-point invariants
    (`complex_polarCoord_symm_ne_zero`, `norm_complex_polarCoord_symm_of_pos`),
    `integrand_at_polar_symm : 0 < r →
       partialZBar unitRadialBumpC (polarCoord.symm (r, θ)) / polarCoord.symm (r, θ)
         = ((deriv (psiBump 1) r / (2·r)) : ℂ)`.

* **Chip 3c-F-2 polar transformation — DONE** (commit `945aa34`,
  extends `PompeiuKernelRadialIntegral.lean` by ~50 LOC):
  - `scaled_integrand_at_polar_symm`: the Jacobian `r` cancels `1/(2r)`,
    leaving `((deriv (psiBump 1) r / 2) : ℂ)`.
  - `integral_partialZBar_div_eq_polar_integral`:
    ```
    ∫ ζ : ℂ, partialZBar unitRadialBumpC ζ / ζ
      = ∫ p in Ioi 0 ×ˢ Ioo (-π) π, ((deriv (psiBump 1) p.1 / 2) : ℂ).
    ```
    Via `Complex.integral_comp_polarCoord_symm` + `setIntegral_congr_fun`
    on the polar target.

* **Chip 3c-F-2 bound lemma — DONE** (commit `e55dbfb`,
  extends `PompeiuKernelRadialIntegral.lean` by ~30 LOC):
  - `exists_bound_deriv_psiBump_one`: `∃ M, ∀ r, ‖deriv (psiBump 1) r‖ ≤ M`.
  - `deriv_psiBump_one_eq_zero_of_{neg, one_lt}`: derivative vanishes
    outside `[0, 1]` (locally constant there).

* **Chip 3c-F-2-final — DONE** (commit `750bab2`,
  [`Analysis/PompeiuKernelRadialIntegralFinal.lean`](JacobianChallenge/Analysis/PompeiuKernelRadialIntegralFinal.lean),
  ~205 LOC):
  - **Headline**: `integral_partialZBar_unitRadialBumpC_div_eq_neg_pi :
    ∫ ζ : ℂ, partialZBar unitRadialBumpC ζ / ζ = -π`.
  - **FTC on `[0, 1]`** via `intervalIntegral.integral_deriv_eq_sub`
    + `psiBump_one_{zero,one}`: `∫ r in 0..1, deriv (psiBump 1) r =
    0 - 1 = -1` (`intervalIntegral_deriv_psiBump_one`,
    `setIntegral_Ioc_deriv_psiBump_one`).
  - **Extension to `Ioi 0`** via decomposition
    `Ioi 0 = Ioc 0 1 ∪ Ioi 1` (`Set.Ioc_union_Ioi_eq_Ioi`) with
    `deriv_psiBump_one_eq_zero_of_one_lt` giving a.e. vanishing on
    `Ioi 1`, then `setIntegral_union` to combine
    (`setIntegral_Ioi_deriv_psiBump_one`).
  - **ℂ-lift** via `MeasureTheory.integral_ofReal` (Bochner integration
    commutes with `Complex.ofReal`) + `MeasureTheory.integral_mul_const`:
    `∫ r in Ioi 0, ((deriv (psiBump 1) r / 2 : ℝ) : ℂ) = (-1/2 : ℂ)`
    (`setIntegral_Ioi_ofReal_deriv_psiBump_one_div_two`).
  - **θ-integral** via `MeasureTheory.setIntegral_const` +
    `Real.volume_real_Ioo_of_le` + `Complex.real_smul` (the smul
    rewrite forced via `show` because `rw` doesn't unify the smul-
    instance form): `∫ _ in Ioo (-π) π, (1 : ℂ) = (2π : ℂ)`
    (`setIntegral_Ioo_neg_pi_pi_one_complex`).
  - **Fubini + combine**: `MeasureTheory.setIntegral_prod_mul` with
    `g ≡ 1` (explicit `μ, ν := volume` to resolve SFinite metavariables;
    `show` aligns the goal's `volume` with `volume.prod volume`;
    `Eq.trans` instead of `rw` to bypass alpha-equivalence pattern-
    matching failures). Final `(-1/2) * (2π) = -π`.
  - Sorry-free, axiom-free. Library entry added.

All sub-pieces sorry-free, axiom-free (`propext`, `Classical.choice`,
`Quot.sound`).

#### Chip 3c-F-3 (radial-cutoff replays) sub-pieces

Chip 3c-F-3 (DCT on second summand) needs the radial-cutoff replays
of Chip 3c-E + the new substitution + DCT argument. Route (a) was
chosen — re-derive instead of transfer-from-pompeiuCutoff.

* **Chip 3c-F-3a — DONE** (commit `299034a`,
  [`Analysis/PompeiuKernelRegularizedInvRadial.lean`](JacobianChallenge/Analysis/PompeiuKernelRegularizedInvRadial.lean),
  ~131 LOC):
  - `regularizedInvSubRadial z ε η := (η - z)⁻¹ · ((radialCutoff z ε η : ℝ) : ℂ)`.
  - `regularizedInvSubRadial_eventuallyEq_zero` inherited from
    `radialCutoff_eventuallyEq_zero` (Chip 3c-F-1).
  - `regularizedInvSubRadial_contDiff` via case-split on `ζ = z` vs
    `ζ ≠ z` (product of two smooth factors off `z`; eventuallyEq 0 at `z`).
  - Also fills the docstring-promised but missing `radialBump_contDiff`
    and `radialCutoff_contDiff` in `PompeiuKernelRadialBump.lean`
    (~30 LOC; case-split on `η = z` locally constant 1 vs `η ≠ z`
    chain rule via `psiBump_contDiff ∘ contDiffAt_norm`).

* **Chip 3c-F-3b — DONE** (commit `44dd309`,
  [`Analysis/PompeiuKernelStokesRadial.lean`](JacobianChallenge/Analysis/PompeiuKernelStokesRadial.lean),
  ~136 LOC):
  - `balance_iteratedIntegral_eq_zero_radial` — radial-bump analog of
    Chip 3c-D's iterated Stokes balance. Line-for-line replay applying
    the generic `iteratedIntegral_partialZBar_eq_zero` (Chip 3c-D,
    unchanged) to `α · regularizedInvSubRadial`, then Leibniz rewrite
    via `partialZBar_mul`.
  - Supporting helpers: `contDiff_/hasCompactSupport_/tsupport_/partialZBar_
    alpha_mul_regInvSubRadial`.

* **Chip 3c-F-3c — DONE** (commit `22f6898`,
  [`Analysis/PompeiuKernelDCTLimitRadial.lean`](JacobianChallenge/Analysis/PompeiuKernelDCTLimitRadial.lean),
  ~303 LOC):
  - Section B replay: `balance_plane_eq_zero_radial` via 3c-F-3b's
    iterated balance + Chip 3c-E's Fubini bridge (unchanged).
  - Section C replay: `tendsto_integral_partialZBar_alpha_mul_regInvSubRadial`
    via mathlib's `tendsto_integral_filter_of_dominated_convergence`.
    Pointwise convergence: at `ζ ≠ z`, eventually `radialCutoff z ε ζ = 1`,
    so the wrapper equals `(ζ-z)⁻¹`; at `ζ = z`, both sides vanish via
    `(z-z)⁻¹ = 0⁻¹ = 0`. Dominator reused from Chip 3c-E
    (`integrable_dominator_partialZBar`).
  - Defines `regularizedInvSubRadialReal z ε` wrapping the dependent
    `regularizedInvSubRadial` into a `ℝ → ℂ → ℂ` function.

* **Chip 3c-F-3d-1 — DONE** (commit `3068824`,
  [`Analysis/PompeiuKernelSecondSummandIdentity.lean`](JacobianChallenge/Analysis/PompeiuKernelSecondSummandIdentity.lean),
  ~144 LOC):
  - `partialZBar_regInvSubRadial : ∀ z ε η, 0 < ε →
       partialZBar (regularizedInvSubRadial z ε) η
         = (η - z)⁻¹ · partialZBar (radialCutoffComplex z ε) η`,
    where `radialCutoffComplex z ε η := ((radialCutoff z ε η : ℝ) : ℂ)`.
  - Off `z`: Leibniz on the product + `partialZBar_inv_sub_const_eq_zero`
    from Chip 3c-A.
  - At `η = z`: both sides vanish via `regularizedInvSubRadial =ᶠ[𝓝 z] 0`
    and `(z - z)⁻¹ = 0` in ℂ.
  - Powers Chip 3c-F-3d-2's substitution η = z + ε·w.

* **Chip 3c-F-3d-2-prep, 3d-2a, 3d-2b — DONE** (commits `c9b8c7c`,
  `83f1e81`, `08479b1`, all in
  [`Analysis/PompeiuKernelRadialRescaling.lean`](JacobianChallenge/Analysis/PompeiuKernelRadialRescaling.lean),
  total ~246 LOC):
  - **3d-2-prep** (algebraic): `psiBump_rescale : 0 < ε →
    psiBump ε (ε * r) = psiBump 1 r`; `norm_z_add_smul_sub`;
    `radialBump_at_rescaled`; `radialBumpComplex_at_rescaled`;
    `radialCutoff{,Complex}_at_rescaled`.
  - **3d-2a** (derivative rescaling): `deriv_psiBump_rescale : 0 < ε →
    deriv (psiBump ε) (ε * r) = ε⁻¹ * deriv (psiBump 1) r`. Proven by
    differentiating `psiBump_rescale` both sides via `HasDerivAt.unique`
    + chain rule, then solving via `field_simp`/`linarith`.
  - **3d-2b** (pointwise ∂̄ rescaling, headline of this sub-chip):
    `partialZBar_radialBumpComplex_rescaled : 0 < ε →
       partialZBar (fun η => ((radialBump z ε η : ℝ) : ℂ)) (z + ε·w)
         = ε⁻¹ * partialZBar unitRadialBumpC w` for all `w`.
    Case-split: at `w = 0` both sides vanish via the eventually-constant-1
    lemma `radialBumpComplex_eventuallyEq_one`; at `w ≠ 0` apply
    `partialZBar_radial_of_ne` (Chip 3c-F-1) to each side + `deriv_psiBump_rescale`
    + norm/algebraic identities + `push_cast`/`field_simp`.

#### Sub-pieces remaining for Chip 3c-F

* **Chip 3c-F-3d-2c — DONE** (this session,
  [`Analysis/PompeiuKernelRadialSubstitution.lean`](JacobianChallenge/Analysis/PompeiuKernelRadialSubstitution.lean),
  ~231 LOC):
  - **Pointwise step** (`partialZBar_regInvSubRadial_at_rescaled`):
    `∂̄(regularizedInvSubRadial z ε)(z + ε·w) = -((ε : ℂ)²)⁻¹ · (∂̄(unitRadialBumpC)(w) / w)`.
    Chain: Chip 3c-F-3d-1 (`∂̄(regInvSubRadial) = (·-z)⁻¹ · ∂̄(cutoffℂ)`)
    + `partialZBar_radialCutoffComplex_eq_neg` (linearity on `1 - f`
    via `partialZBar_sub` + `partialZBar_const`) + Chip 3c-F-3d-2b
    (bump rescaling) + `mul_inv` (valid in a CommGroupWithZero).
  - **Integral step** (`integral_alpha_mul_partialZBar_regInvSubRadial_eq_substituted`):
    Translation `ζ = z + η` via `integral_add_left_eq_self` on Lebesgue
    measure (left-invariant Haar) + rescaling `η = ε·w` via
    `Measure.integral_comp_smul` (additive Haar, `Module.finrank ℝ ℂ = 2`
    → Jacobian `|ε²|⁻¹` after `abs_of_nonneg`). The pointwise step
    introduces the `-((ε:ℂ)²)⁻¹` factor; the Jacobian `(ε:ℝ)²` cancels
    it via `Complex.real_smul` + cast.
  - Sorry-free, axiom-free (`propext`, `Classical.choice`, `Quot.sound`
    only). Library entry added.

* **Chip 3c-F-3d-3 — DONE** (this session,
  [`Analysis/PompeiuKernelSubstitutedDCT.lean`](JacobianChallenge/Analysis/PompeiuKernelSubstitutedDCT.lean),
  ~226 LOC):
  - `tendsto_integral_alpha_substituted : Continuous α → HasCompactSupport α →
    Tendsto (fun ε ↦ ∫ w, α(z + ε·w) · (∂̄(unitRadialBumpC)(w) / w))
      (𝓝[>] 0) (𝓝 (α z · (-π : ℂ)))`.
  - Supporting infrastructure: `unitRadialBumpC_continuous`,
    `unitRadialBumpC_hasCompactSupport` (via
    `tsupport_unitRadialBumpC_subset ⊆ closedBall 0 1` and
    `IsCompact.of_isClosed_subset`), `partialZBar_unitRadialBumpC_continuous`,
    `partialZBar_unitRadialBumpC_hasCompactSupport` (via Chip 3c-E helpers),
    `integrable_partialZBar_unitRadialBumpC_div` (Chip 1c at `z := 0`).
  - DCT via `tendsto_integral_filter_of_dominated_convergence` with
    dominator `M · ‖∂̄(unitRadialBumpC)(w)/w‖` (`M` from
    `Continuous.bounded_above_of_compact_support` on α). Pointwise:
    `tendsto_alpha_at_substituted` (continuity of α at `z` ∘ continuous
    `ε ↦ z + (ε:ℂ)·w`). Final value: `integral_const_mul` +
    Chip 3c-F-2-final's universal `-π`.
  - Sorry-free, axiom-free. Library entry added.

* **Chip 3c-F-4 — DONE** (this session,
  [`Analysis/PompeiuKernelCauchyPompeiu.lean`](JacobianChallenge/Analysis/PompeiuKernelCauchyPompeiu.lean),
  ~213 LOC):
  - `partialZBar_pompeiuKernel_eq_self : ContDiff ℝ 1 α → HasCompactSupport α →
    ∀ z, partialZBar (pompeiuKernel α) z = α z` —
    **the unconditional Cauchy-Pompeiu identity on ℂ**.
  - Helpers: `tendsto_integral_partialZBar_alpha_mul_regInvSubRadial_unwrapped`
    (3c-F-3c reformulated without the `Real`-wrapper via
    `regularizedInvSubRadialReal_of_pos`),
    `tendsto_integral_alpha_mul_partialZBar_regInvSubRadial` (combines
    3c-F-3d-2c symmetric form + 3c-F-3d-3 + negation to give the
    second-summand limit `α z · π`), `sum_summand_integrals_eq_zero`
    (splits `balance_plane_eq_zero_radial` via `integral_add` with
    `integrable_partialZBar_mul_regInvSubRadial` and
    `integrable_alpha_mul_partialZBar_regInvSubRadial`; gets the L bound
    from `IsBounded.subset_ball_lt`).
  - Headline algebraic step (`integral_partialZBar_alpha_mul_inv_sub_eq_neg_pi_mul`):
    `∫ ζ, ∂̄α(ζ) · (ζ-z)⁻¹ = -π · α(z)` via the constant-zero
    Tendsto of `A(ε) + B(ε)` and uniqueness of limits in ℂ (T2).
  - Final identity via Chip 3b's bridge
    (`partialZBar_pompeiuKernel_eq_pompeiuKernel_partialZBar`) + unfolding
    `pompeiuKernel` + `field_simp` with `Real.pi_ne_zero`.
  - Sorry-free, axiom-free. Library entry added.

**Chip 3c-F COMPLETE.** Net Pompeiu arc LOC (Chips 1a-4): ~6,500 LOC,
~25 sessions. Next: Chip 4 (chart pull-back).

**Chips 4-7** (after Chip 3c-F) — refined 2026-05-25 via direct repo
scouting (see "Chip 5 scouting report" below):

* **Chip 4 (~600-1,200 LOC, 3-5 sessions)** — chart pull-back: lift the
  Pompeiu kernel from ℂ to a chart-disk on X. Lighter than the original
  ~1-2k estimate because `PartialZBarManifold.lean` (215 LOC),
  `PartialZBarManifoldChartPullbackVanish.lean` (146 LOC), and
  `ChartPullbackDataConstruction.lean` already exist and are reusable.
* **Chip 5 (~1,800-2,800 LOC, 7-12 sessions)** — globalize to compact X
  at genus 0 via partition of unity over a finite chart cover + the
  genus-0-specific spreading-function construction (Forster Ch. 14,
  Behnke-Stein-light). The substantive classical-content step. See
  scouting report below for the floor/ceiling and dominant uncertainty.
* **Chip 6 (~200 LOC, 1 session)** — wire to the existing
  `ofCurve_inj_under_genus_pos`-style chain at
  [`OfCurveInjFromDegreeOne.lean:90`](JacobianChallenge/Manifold/OfCurveInjFromDegreeOne.lean)
  to get `δQ - δP ∈ PrincDiv X`, then through the unconditional chain
  to `X ≃ₜ S²`.
* **Chip 7 (<50 LOC, <1 session)** — close `Basic.lean:73` by composition.

**Net (remaining, Chips 3c-F-rest through 7): ~3,250-5,250 LOC,
~13-22 sessions.** (Refined down from the original 20-45 sessions /
4-9k LOC: Chip 4 shrank thanks to pre-existing chart-pullback
infrastructure; Chip 5 tightened via direct mathlib + repo coverage
audit. The original wide band reflected pre-scouting uncertainty.)

### Chip 5 scouting report (2026-05-25)

**Target hypothesis** — [`ExistsSimplePoleGermFromGenusZeroDBarSolvability.lean:121`](JacobianChallenge/Manifold/ExistsSimplePoleGermFromGenusZeroDBarSolvability.lean):
```
def DBarSolvabilityAtGenusZero : Prop :=
  JacobianChallenge.genus X = 0 →
  ∀ α : X → ℂ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α →
  ∃ u : X → ℂ,
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u ∧
    ∀ x : X, partialZBarManifold u x = α x
```
i.e. `∂̄` is surjective on `C∞(X)` whenever `genus X = 0`. Equivalent
to `H¹(X, 𝒪) = 0`. For **arbitrary** genus-0 compact RS, not just
the Riemann sphere — we cannot use uniformization (Item 14 IS the
uniformization-side result).

**Discharge chain already wired** — [`ForsterCutoffPoleConstruction.lean:1357`](JacobianChallenge/Manifold/ForsterCutoffPoleConstruction.lean) closes
`DBarSolvabilityAtGenusZero + ChartAtConstantOnSource →
ExistsSimplePoleGermAtSomePoint` via Chip 2c-Final. So Chip 5 only
needs to PROVE `DBarSolvabilityAtGenusZero X` itself, then composition
through the existing chain closes Item 14.

**In-repo infrastructure usable for Chip 5**:
- `PartialZBarManifold.lean` (215 LOC) + chart-pullback transfer (146 LOC).
- 32 chart-cover files, ~4,200 LOC of `DiskChartCover*` machinery.
  Caveat: most target the C3/Hodge chain (genus-positive); some
  reusable for the partition-of-unity gluing step in Chip 5.
- `CompactDiskChartCover.lean` constructs finite covers with
  inner/outer disk radii — exactly the input shape Chip 5 needs.
- `HasConvexTargetChartCover.lean` / `HasAdmissibleChartCoverClass.lean`
  — chart-cover type classes that may extend cleanly to the Chip-5
  setting.

**Mathlib coverage**:
- ✅ `Mathlib/Geometry/Manifold/PartitionOfUnity.lean` — partition of
  unity on smooth manifolds.
- ✅ `Mathlib/Geometry/Manifold/BumpFunction.lean`,
  `WhitneyEmbedding.lean`, `SmoothApprox.lean`.
- ❌ NO Dolbeault complex.
- ❌ NO sheaf cohomology of holomorphic structure sheaf on Riemann
  surfaces. Mathlib has abstract sheaf cohomology in
  `AlgebraicGeometry/`, but not connected to the analytic side.
- ❌ NO Behnke-Stein / Stein manifold theorem.

**Textbook length**: Forster Ch. 14's proof of `H¹(X, 𝒪) = 0` for
genus-0 compact RS via Cauchy-Pompeiu + partition of unity + spreading
function is **4-6 dense pages**. At observed Pompeiu-arc cadence of
~300-600 LOC/session for substantive analytical work (Chip 3c-E =
636 LOC/session, Chip 2d = 515 LOC/session), 4-6 pages × ~200-400
LOC/page = **1,200-2,400 LOC core**, plus framework/setup (Dolbeault
iso shortcut, partition-of-unity gluing on ℂ-valued smooth functions,
spreading-function construction) brings the realistic estimate to
**1,800-2,800 LOC** (7-12 sessions).

**Floors and ceilings**:
- **Optimistic floor (~1,200 LOC, 5 sessions)**: tight tracking of
  Forster + no Dolbeault framework needed (direct Cauchy-Pompeiu +
  spreading function chain).
- **Pessimistic ceiling (~3,500-4,000 LOC, 14-18 sessions)**: the
  spreading-function construction needs new functional-analysis
  machinery, OR sheaf cohomology has to be wired in.

**Dominant uncertainty source**: whether `H¹(genus-0 compact RS, 𝒪) = 0`
is provable via a direct Cauchy-Pompeiu + partition-of-unity argument
(2,000-2,500 LOC range) or whether some Dolbeault/Hodge/sheaf-cohomology
framework needs building (pushes toward 3,500+). The Forster route
assumes the former; plausible but unverified at the Lean level until
the first 2-3 Chip 5 sessions land.

### Discipline lesson learned today (KEEP)

**No backing out.** The pattern of writing → hitting an error → deleting and restarting eats session time and produces nothing. When stuck:

1. **Debug in place.** Don't delete.
2. **For typeclass synth errors,** decompose the prerequisites and test each in isolation. The fix is usually a missing import 1–2 dependency-hops away.
3. **For tactic failures,** read the actual goal at the failure point and pick the right replacement tactic. `linarith` doesn't work on complex sub-eq-zero; use `sub_ne_zero.mpr` or `sub_eq_zero.mp` directly.
4. **Pull the file only after the session ends with a sorry-free result OR after a clear decision to descope.** Don't pull mid-debug.

This was a real failure mode in the Chip 1a session (three deletion cycles before pushing through). After committing to debug-in-place, the import calibration resolved in ~5 minutes.

---

## 🚀 Session 5 entry plan (Chip 5 kickoff)

Chip 5 globalizes Chip 4's local Pompeiu identity to discharge
`DBarSolvabilityAtGenusZero X` for every genus-0 compact Riemann surface
(not just RS — uniformization is precisely Item 14's *output*, so we
cannot assume it). The Forster Ch. 14 strategy: partition-of-unity glue
+ Behnke-Stein spreading correction. Estimated 1,800-2,800 LOC,
7-12 sub-chip sessions.

### Recommended sub-chip decomposition

**Sub-chip 5.1 — finite chart cover from compactness** (~150-300 LOC,
1 session).
Goal: from `CompactSpace X` (which follows from any path to `genus X = 0`
via the existing chain), extract a finite chart cover
`{(x_i, chart_{x_i})}_{i ∈ Fin n}` with `X = ⋃ (chart_{x_i}.source)`.
Use mathlib's `IsCompact.elim_nhds_subcover` applied to the open cover
by chart sources, plus `IsCompact.elim_finite_subcover` for the finite
reduction. Wraps these into a clean data structure that Chip 4's
`pompeiuKernelChart` accepts.

**Sub-chip 5.2 — partition of unity on a complex 1-manifold**
(~200-400 LOC, 1-2 sessions). Goal: lift mathlib's
`Mathlib/Geometry/Manifold/PartitionOfUnity.lean` to produce a smooth
ℝ-valued partition `{ρ_i}_{i ∈ Fin n}` subordinate to the chart cover,
with `ρ_i : X → ℝ` smooth, `0 ≤ ρ_i ≤ 1`, `tsupport ρ_i ⊆ chart_{x_i}.source`,
and `Σ ρ_i = 1` pointwise on `X`. Cast to `ℂ`-valued (multiply by
`Complex.ofRealCLM` or compose). Mathlib has the real-manifold version;
the ℝ ↔ ℂ trivial model rewrites are the only fiddly bit.

**Sub-chip 5.3 — local Pompeiu solutions with cutoffs** (~300-500 LOC,
2 sessions). Goal: for each `i`, define
`u_i := pompeiuKernelChart x_i (ρ_i · α) : X → ℂ`. Use Chip 4's
`pompeiuKernelChart`. Apply `partialZBar_pompeiuKernelChart_eq_α_on_chart_source`
to get the chart-x_i view local identity `∂̄ (u_i^chart_x_i) = (ρ_i · α)^chart_x_i`
on `chart_{x_i}.source`. Note: each `u_i` is C^∞ ON `chart_{x_i}.source`
(via Chip 4's smoothness lemma) but generally NOT compactly supported
in `chart_{x_i}.source` — the Pompeiu kernel decays like `1/|z|`, not
to zero. This produces the error term that Sub-chip 5.4 corrects.

**Sub-chip 5.4 — cutoff multiplication + error analysis** (~300-500 LOC,
2 sessions). Multiply each `u_i` by another smooth cutoff `χ_i` with
`χ_i ≡ 1` on a neighborhood of `supp(ρ_i)` and `tsupport χ_i ⊆ chart_{x_i}.source`,
giving `v_i := χ_i · u_i : X → ℂ` smooth and supported in
`chart_{x_i}.source` (so extendable by 0 to a smooth global function).
Apply the Leibniz rule
(`partialZBarManifold_mul`) to `v_i`:
`∂̄(χ_i · u_i) = χ_i · ∂̄u_i + ∂̄χ_i · u_i`.
On `supp(ρ_i)` the first term gives `χ_i · ρ_i · α = ρ_i · α` (since
χ_i = 1). Summing over `i`: `Σ ∂̄v_i = α + e` where the error
`e := Σ ∂̄χ_i · u_i` has support disjoint from any neighborhood of
`⋃ supp(ρ_i) = X` — i.e., `e ≡ 0` on `X`! Actually e is NOT zero
because `∂̄χ_i` is supported in the cutoff annulus where `χ_i` transitions
from 1 to 0; this annulus is *inside* `chart_{x_i}.source` but *outside*
`supp(ρ_i)`. So `e` has support inside `X \ supp(ρ_i)` for each `i`,
which is non-trivial — this is the genuine error term that Sub-chip 5.5
must correct via spreading.

**Sub-chip 5.5 — Behnke-Stein spreading correction** (~600-1,000 LOC,
3-5 sessions). The heaviest sub-chip. Iteratively correct the error
`e_0 := α - ∂̄v` by re-solving `∂̄w_1 = e_0` (smaller-supported), then
`∂̄w_2 = e_1`, etc. On genus-0 X this iteration converges to a smooth
global solution. The classical proof uses Forster Ch. 14's
spreading-function lemma (a strengthening of Schauder estimates +
geometric-series convergence on contracting annuli). At the Lean
level: ~600-1,000 LOC of analytic infrastructure for the convergence
argument, possibly with a Stein-manifold-light variant if direct
spreading proves too heavy.

**Sub-chip 5.6 — assembly and manifold identity** (~150-300 LOC,
1 session). Combine all `v_i + w_k` into the final `u : X → ℂ`,
discharge `ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u`, and show
`partialZBarManifold u x = α x` for all `x`. The chart-transition factor
analysis from Chip 4 handles the manifold-side identity at arbitrary
`x` — at each `x`, the canonical chart's view of `u` satisfies the
local identity from Sub-chips 5.3-5.5, and the manifold-side identity
follows by the same `extChartAt = chartAt` reduction used in Chip 4's
basepoint theorem.

### Entry checklist (first thing next session)

1. **Read `Manifold/ChartPompeiuKernel.lean`** (462 LOC) — the API
   that Chip 5 consumes.
2. **Confirm `git status` clean + `lake build` green** on
   `feat/item14-forward-dbar-mul`. Last commit `ed468fb`.
3. **Search mathlib** for partition-of-unity API:
   `grep -rn "IsOpen.*PartitionOfUnity\|exists.*partition.*unity\|smoothPartitionOfUnity"
    .lake/packages/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
   — confirm what's available, and what cast/lift work is needed
   for ℝ → ℂ.
4. **Start Sub-chip 5.1**: `CompactnessChartCover.lean` (new file).
   Use `IsCompact.elim_finite_subcover` on
   `{(chartAt ℂ x).source | x : X}`. Output: a `FiniteChartCover X`
   structure (or just an `∃ s : Finset X, X ⊆ ⋃ ...` proposition).

### Risk register for Chip 5

* **R1 (high)** — Behnke-Stein spreading is the biggest unknown.
  Classical reference (Forster §14) assumes underlying functional
  analysis (uniform convergence on compact sets) that mathlib may not
  have packaged. Plan B if 5.5 stalls: try Dolbeault iso shortcut
  (`H¹(X, 𝒪) = H^{0,1}_{∂̄}(X)`) — but this requires building
  Dolbeault cohomology from scratch (3,000+ LOC). Plan C: assume an
  axiom `behnkeSteinSpreading` for the inductive step, document, and
  push for external review.
* **R2 (medium)** — The chart-transition factor from Chip 4
  (`partialZBarManifold_pompeiuKernelChart_eq_α_mul_transition`)
  makes the manifold-side identity non-trivial when summing local
  contributions. If the partition-of-unity sum doesn't yield a clean
  manifold identity (due to mismatched chart-transition factors),
  may need to refactor to a chart-invariant variant of
  `partialZBarManifold`.
* **R3 (low)** — `ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞` is in the
  `DBarSolvabilityAtGenusZero` predicate, but the chart-side
  smoothness lemma uses `ContDiff ℝ ∞`. Bridge via mathlib's
  `contMDiff_iff_contDiff_on_charts` style lemmas.

---

## TL;DR — current frontier

**`Basic.lean:73 genus_eq_zero_iff_homeo`** still has a `sorry`. The reduction chain in tree, after this session's work:

```
genus_eq_zero_iff_homeo X
  ⇐ Topology/Item14FromHSPOnly.genus_eq_zero_iff_homeo_from_hSP             (in tree, sorry/axiom-free)
  + Topology/S2ImpliesGenus0FromEtalePrimitives.s2ImpliesGenus0_etalePrimitivesArc  (unconditional, in tree)
  + ExistsSimplePoleGermAtSomePoint X                                       ← THE ONE OPEN INPUT

ExistsSimplePoleGermAtSomePoint X
  ⇐ Manifold/ForsterCutoffPoleConstruction.existsSimplePoleGermAtSomePoint_of_dbarSolvability_under_chartConst
                                                                            (in tree, sorry/axiom-free)
  + (p : X)                                                                 ← any p
  + ChartAtConstantOnSource p                                               ← per-p structural; innocuous on
                                                                              every concrete X (RS at finite p,
                                                                              ℂ/L tori, single-chart spaces)
  + DBarSolvabilityAtGenusZero X                                            ← THE ONE CLASSICAL-CONTENT GAP
  + (hg : genus X = 0)                                                      ← available from iff direction
```

**Net**: one classical-content gap (DBar at genus 0) plus a per-`p` structural assumption that's discharge-free on every X anyone cares about in practice.

**BSLB is obsolete for Item 14.** Older HANDOFF / OPEN.md framings of "Item 14 = hSP + BSLB" predate the 2026-05-24 étale-leg merge.

## What's in tree (file by file)

### Forward leg

* [`Manifold/PartialZBarManifold.lean`](JacobianChallenge/Manifold/PartialZBarManifold.lean) — manifold-side `partialZBarManifold f y` (chart-y based), algebraic lemmas (`_add`, `_sub`, `_neg`, `_mul`), Forster specializations, and the "vanishing on holomorphic-pullback functions" theorem. Chip 1 deliverable.
* [`Manifold/PartialZBarManifoldChartPullbackVanish.lean`](JacobianChallenge/Manifold/PartialZBarManifoldChartPullbackVanish.lean) — chart-pullback ∂̄ vanishing transfer lemma. Without `LocallyConstantChartAt` typeclass, transfers `partialZBarManifold f y = 0` (chart-y view) to `partialZBar (f ∘ chart_x.symm) (chart_x y) = 0` (chart-x view) via the holomorphic chart transition.
* [`Manifold/ExistsSimplePoleGermFromGenusZeroDBarSolvability.lean`](JacobianChallenge/Manifold/ExistsSimplePoleGermFromGenusZeroDBarSolvability.lean) — definition of `DBarSolvabilityAtGenusZero X`, classical pole-order keystone `meromorphicOrderAt_inv_sub_const_sub_analytic_eq_neg_one`, **Forster §16.9 consolidator** `existsSimplePoleGermAtSomePoint_of_chartPullback_data` (the unconditional assembly lemma). Chip 2 deliverable.
* [`Manifold/ForsterCutoffPoleConstruction.lean`](JacobianChallenge/Manifold/ForsterCutoffPoleConstruction.lean) — **Chip 2c + 2c-Final**. Bump function `b`, local pole `g₀`, compactly-supported source `α`, off-pole identity `partialZBarManifold_g₀_eq_α_off_pole`, α smoothness `α_contMDiff_under_const`, and the **main theorem `existsSimplePoleGermAtSomePoint_of_dbarSolvability_under_chartConst`**.

### Reverse leg (étale-primitives arc, merged from `feat/item14-affineChartTriangleSimplex-ball`)

* [`Manifold/EtalePrimitives.lean`](JacobianChallenge/Manifold/EtalePrimitives.lean) — étale space of ω-primitives over X. Alt-B foundation.
* [`Manifold/ChartLocalPrimitiveOverlapLocallyConst.lean`](JacobianChallenge/Manifold/ChartLocalPrimitiveOverlapLocallyConst.lean) — overlap locally constant. Alt-B keystone.
* [`Manifold/EtalePrimitivesIsLocalHomeomorph.lean`](JacobianChallenge/Manifold/EtalePrimitivesIsLocalHomeomorph.lean) — `proj : EtalePrimitives om → X` is a local homeomorphism. Chip 3.
* [`Manifold/EtalePrimitivesCovering.lean`](JacobianChallenge/Manifold/EtalePrimitivesCovering.lean) + [`EtalePrimitivesCoveringInfra.lean`](JacobianChallenge/Manifold/EtalePrimitivesCoveringInfra.lean) — `proj` is a covering map. Chip 4a-4b.
* [`Manifold/EtalePrimitivesGlobalSection.lean`](JacobianChallenge/Manifold/EtalePrimitivesGlobalSection.lean) + [`EtalePrimitivesGlobalSmooth.lean`](JacobianChallenge/Manifold/EtalePrimitivesGlobalSmooth.lean) — global primitive on simply-connected X. Chips 4c-4d.
* [`Topology/S2ImpliesGenus0FromEtalePrimitives.lean`](JacobianChallenge/Topology/S2ImpliesGenus0FromEtalePrimitives.lean) — **`s2ImpliesGenus0_etalePrimitivesArc : S2ImpliesGenus0 X`** unconditional. Chip 4e (commit `829a6e8`).

### Integration

* [`Topology/Item14ForwardFromCompactConnected.lean:68`](JacobianChallenge/Topology/Item14ForwardFromCompactConnected.lean) — `genus_eq_zero_iff_homeo_from_existsSimplePoleGerm`, the existing two-input form (`hSP X + S2ImpliesGenus0 X` → iff).
* [`Topology/Item14FromHSPOnly.lean`](JacobianChallenge/Topology/Item14FromHSPOnly.lean) — **`genus_eq_zero_iff_homeo_from_hSP`**, the post-merge one-input form. Composes the existing two-input theorem with the unconditional `s2ImpliesGenus0_etalePrimitivesArc`.

## The ONE open input: `DBarSolvabilityAtGenusZero X`

Stated as the named hypothesis:

```
DBarSolvabilityAtGenusZero X : Prop :=
  genus X = 0 → ∀ α : X → ℂ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α →
    ∃ u : X → ℂ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u ∧ ∀ x : X, partialZBarManifold u x = α x
```

Equivalent classical statements:
- `H¹(X, 𝒪) = 0` at genus 0 (sheaf cohomology).
- Surjectivity of `∂̄` on smooth (0,1)-forms at genus 0 (Dolbeault).
- `Nonempty (HolomorphicEquiv X RiemannSphere)` at genus 0 (uniformization), which separately discharges hSP via the in-tree transport `existsSimplePoleGermAtSomePoint_of_holomorphicEquiv_RS`.

None of these are in mathlib at the pinned commit. Three discharge routes, in order of estimated effort:

| Route | Effort | What it gives |
|---|---|---|
| **Cauchy-Pompeiu kernel + uniformization for genus 0** | ~5–8k LOC, 4–8 person-months focused mathlib-quality work | Targeted route to DBar at genus 0 only. Pompeiu kernel is upstreamable independently (~1k LOC, 2–4 weeks). |
| **Hörmander L² methods for ∂̄** | ~8k LOC, 10–20 person-months | Generic ∂̄-solvability; applies beyond genus 0. Heavy. |
| **Full Hodge / Dolbeault apparatus** | ~15–18k LOC, 18–36 person-months | Reusable across complex geometry. Heaviest. |

## Phase B verdict (2026-05-24): Cauchy-Pompeiu alone does not short-circuit

What mathlib has:
- Building blocks for Pompeiu kernel: rectangle Stokes for real-differentiable functions ([CauchyIntegral.lean:187](.lake/packages/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean) `integral_boundary_rect_of_hasFDerivAt_real_off_countable`), circle integrals, divergence theorem, 2D Lebesgue integration.

What mathlib lacks:
- Explicit Pompeiu kernel formula `u(z) = -(1/π) ∫∫ α(ζ)/(ζ-z) dA(ζ)` and its regularity / `∂̄u = α` proof.
- Dolbeault complex isomorphism with sheaf cohomology.
- Hodge decomposition on Riemann surfaces.
- Sheaf cohomology applied to `𝒪_X` (only abstract `CategoryTheory/Sites/SheafCohomology` exists, no analytic instantiation).

Why Pompeiu alone is not enough: the Pompeiu kernel solves `∂̄u = α` locally on a disk in ℂ, but `u` has `1/z` tails at infinity (not compactly supported even when α is). Globalizing to compact X via partition of unity introduces a residual `(∂̄η)·u` term that requires `H¹(𝒪) = 0` to discharge — exactly the statement we're trying to prove. So Pompeiu + cutoff is circular.

A genus-0-specific route avoiding the circularity must use either uniformization (X ≃ RS biholomorphically, then transport from RS) or a Behnke-Stein-style "spreading function" construction, both of which are textbook content not in mathlib at the pin.

## What's NOT a route to closure

- **`ChartAtConstantOnSource p` removal via mfderiv refactor.** Investigated 2026-05-24. The intrinsic ∂̄ on complex 1-manifolds requires canonical-bundle / `Ω^{0,1}` line-bundle machinery (not in mathlib). The chain-rule alternative (carry the chart-transition factor through ~10 lemmas) is ~1500–2500 LOC of real work but yields only a cosmetically smaller hypothesis list — DBar remains the actual gap. **Not worth pursuing as a standalone effort.**
- **RR-direct route via lifting from RS without biholom.** Audited 2026-05-24, see [`RR_AUDIT.md`](RR_AUDIT.md). Every in-tree route to `RiemannRochGenusZero X` on arbitrary X consumes either `hSP X` or `Nonempty (HolomorphicEquiv X RS)`. No biholom-free transport exists. The "RR-direct" framing relabels the gap rather than shortening it.
- **`SimplePoleGermExtensionHypothesis X` reformulations.** The genus-conditional form (`genus = 0 → hSP X`) is definitionally equivalent to hSP X under the iff's forward direction. Reformulating does not reduce the open content.

## Practical next directions (if you want to keep moving)

1. **Pompeiu kernel as a standalone mathlib PR.** 2–4 weeks focused work, ~1k LOC, upstream-able even without item 14 context. Would be the first concrete step of the Route-1 path above, and is useful infrastructure regardless.
2. **Documentation cleanup pass.** This rewrite + the doc updates this session leave the audit pile in a coherent state. No further code work needed if you want to pause.
3. **Wait for organic mathlib progress on complex geometry.** Estimated 1–3 years for the relevant infrastructure (Hodge, Dolbeault, or uniformization) to land via other contributors.
4. **Sponsor a focused arc** (mathlib-experienced contributor, ~6 months for Route 1). Realistic if Item 14 closure is a hard goal.

The current branch state (`feat/item14-forward-dbar-mul`, tip `bcf6951`) is a stable handoff point: both legs present, single named-hypothesis reduction, Pompeiu Chip 1a landed, all assemblies sorry/axiom-free and individually verified. See the **ACTIVE ARC** section at the top for the in-flight chip breakdown and next-session entry point.

## Pointers

- [`OPEN.md`](OPEN.md) — per-item Buzzard-spec status (item 14 row updated 2026-05-24).
- [`HSP_AUDIT.md`](HSP_AUDIT.md) — hSP-family chain-trace (audit 2026-05-23, post-Chip-2c-Final + post-merge banner added 2026-05-24).
- [`RR_AUDIT.md`](RR_AUDIT.md) — RR-direct route audit (2026-05-24).
- [`ROUTE_5_5C_AUDIT.md`](ROUTE_5_5C_AUDIT.md) — Sub-chip 5.5c route audit (2026-05-26): mathlib + in-repo + Forster Ch. 14 review for Routes I/II/III, working conclusion Route I.
- [`C3_AUDIT.md`](C3_AUDIT.md) — Jacobian-side sorries (items 5/11/12/13/17/18/21).
- [`RESIDUE_AUDIT.md`](RESIDUE_AUDIT.md) — residue-theorem sub-tree.
- [`REPO_AUDIT.md`](REPO_AUDIT.md) — repo-wide audit per sorry.

## Discipline notes (apply to any continuation)

- **No paraphrase chips.** Don't introduce new named hypotheses, "from N inputs" reformulations, or per-X structural variants that don't discharge classical content. See `tools/chip-prompt-preamble.md` for the 7 anti-paraphrase gates.
- **No bundling.** One chip per commit; one direction per branch.
- **Local-verify primary.** `LEAN_NUM_THREADS=1 lake env lean FILE.lean`. Never `lake build` (parallel default → apfsd panic on this machine, per CLAUDE.md).
- **Audits live in-repo.** Don't summarize per-item state in commit messages or external notes — update the relevant `*_AUDIT.md` / `OPEN.md` / this file.
