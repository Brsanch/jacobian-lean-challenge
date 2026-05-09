# OPEN

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

**Current scoreboard (audited against `Basic.lean` HEAD `5e601e8`, 2026-05-09):**

- **STRICT-CLOSED:** 0 / 24 (under the strict-bar definition above —
  requires both honest implementation AND the underlying `Jacobian X`
  being the intended analytic Jacobian).
- **STUB but with HONEST BODY (Phase 0, 2026-05-09):** items **8, 22, 23,
  24** (rsum thread). Implementations honest, no `sorry`/`axiom`; auto-flip
  to STRICT-CLOSED the moment Phase 1 lands honest
  `Jacobian X = Pic⁰ X / honest PrincDiv`.
- **PROOF-HONEST stubs (auto-flip after Phase 1):** items 15, 19, 20.
- **STUB (placeholder topology / target):** items 4, 10.
- **OPEN (sorry still in `Basic.lean`):** 1, 5, 11, 12, 13, 14, 16, 17,
  18, 21 = 10 items.

> **`CLOSURE_MAP.md` (authored 2026-05-09, repo root) is now the live
> source of truth.** It has the per-item map, mathlib status verified
> against this repo's pin (`8e3c989...`), Phase 1–4 chip plans with
> per-component LOC ranges, dependency DAG, and verification audit log.
> Update `CLOSURE_MAP.md`, not this file, when items flip.

**Remaining LOC for full 24/24 STRICT-CLOSED (verified per-component):
31,500–59,700 LOC.** Phase 1 ~2k (chippable now), Phase 2 ~15.5–29.6k
(period lattice + Abel-Jacobi, blocked on classical mathlib gaps),
Phase 3 ~7.1–15k (surface classification, blocked), Phase 4 ~6.9–12.8k
(Hodge, blocked). See `CLOSURE_MAP.md` section F.

**Phase 0 LOC merged this session (2026-05-09):** ~12,000 LOC (rsum
thread + residue theorem unconditional + RegFix architectural fix).
Repo size at end of session: ~49,323 LOC.

Do not regenerate this list from context — query this file. Update this file
whenever a status changes.

## Definitions (data) — Basic.lean items 1–9 in OPEN.md numbering

| # | Item | Status | Notes |
|---|---|---|---|
| 1 | `genus X : ℕ` | **STUB** | Body: `JacobianChallenge.genus X = Module.finrank ℂ (HolomorphicOneForm X)`. Returns `0` by convention if `HolomorphicOneForm X` is infinite-dimensional, and finite-dimensionality on compact connected `X` is **not yet proved** (Hodge theory). The anti-hack pair (item 14, `genus_eq_zero_iff_homeo`) is **OPEN**. |
| 2 | `Jacobian X : Type u` | **STUB** | Body: `Jacobian X := Pic0 X` where `Pic0 X = Div0 X ⧸ (PrincDiv X).addSubgroupOf (Div0 X)` and **`PrincDiv X := ⊥`** (placeholder; honest version requires the residue theorem). Mathematically `Jacobian X ≃ Div0 X` here, **not** the analytic Jacobian `ℂ^g / Λ`. |
| 3 | `instance : AddCommGroup (Jacobian X)` | **STUB** | Inherits from the `Pic0` quotient. The group structure is honest; the underlying type is not (item 2). |
| 4 | `instance : TopologicalSpace (Jacobian X)` | **STUB** | Discrete (`⊥`). The challenge wants the complex-manifold topology (item 5 `ChartedSpace`); discrete is not it. |
| 5 | `instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` | **OPEN** | Requires the analytic-Jacobian construction (period-lattice or honest `Pic⁰`); not landable on the current discrete-topology placeholder. The parallel `AnalyticTorus X` carries an honest `ChartedSpace` instance (`Manifold/PeriodLattice.lean`), but is not wired into `Jacobian`. |
| 6 | `Jacobian.ofCurve : X → Jacobian X` | **STUB** | Body: `Q ↦ [δQ − δP]` in `Pic⁰` (honest formula). Lands in stub `Pic⁰`, so the *object* of the map is wrong. |
| 7 | `Jacobian.pushforward f hf` | **STUB** | Body: honest `Pic⁰` pushforward via `Div.singletonMap` + descent. Object is stub `Pic⁰`. |
| 8 | `Jacobian.pullback f hf` | **STUB** | Body: zero `ContinuousAddMonoidHom`. **Wrong implementation** (honest map is the divisor fiber-sum). `Div.fiberSum` (`Divisor/FiberSum.lean`) and `Pic0.pullback (f, hf, N, hN)` (`Divisor/FiberPullback.lean`) are landed; the swap into `Basic.lean` waits on a derivation of finite-fibres + constant-card from `ContMDiff` smoothness alone. |
| 9 | `ContMDiff.degree f hf : ℕ` | **STUB** | Body: `degreeStub f hf` (0 for constant, 1 otherwise). `degreeFiber` infrastructure (with `RegularValueWitness` bundle) merged at `2985cdd` in `Manifold/Degree.lean`; not wired into `Basic.lean` yet because honest fibre-cardinality requires three classical inputs not in mathlib. |

## Theorems (Prop) — Basic.lean items 10–24 in OPEN.md numbering

| # | Item | Status | Notes |
|---|---|---|---|
| 10 | `instance : T2Space (Jacobian X)` | **STUB** | Discrete ⇒ T2 is honest, but the topology itself is wrong (item 4). |
| 11 | `instance : CompactSpace (Jacobian X)` | **OPEN** | Pic⁰ with `PrincDiv = ⊥` is `Div⁰ X`, a free abelian group on the (in general infinite) underlying set of `X`. Not compact in any sensible topology. Requires real period-lattice quotient. |
| 12 | `instance : IsManifold ... ω (Jacobian X)` | **OPEN** | Requires analytic-Jacobian construction. `AnalyticTorus X` has an honest `IsManifold` instance modulo `Λ = ⊥`; not wired into `Jacobian`. |
| 13 | `instance : LieAddGroup ... ω (Jacobian X)` | **OPEN** | Requires item 12 plus smoothness of group ops. |
| 14 | `genus_eq_zero_iff_homeo` (anti-hack vs. `genus := 0`) | **OPEN** | Genus 0 ↔ `X ≃ₜ S²`. Multi-month: requires closed-orientable-surface classification + Riemann sphere as `ChartedSpace` + bridge to geometric genus. |
| 15 | `ofCurve_self : ofCurve P P = 0` | **STUB** *(PROOF-HONEST)* | Real proof reducing to `[δP − δP] = 0` in `Pic⁰`. Proof would survive future honest `PrincDiv`. Not STRICT-CLOSED because the *target* `Jacobian X` is itself a stub. |
| 16 | `ofCurve_inj` (anti-hack vs. `Jacobian := PUnit`) | **STUB** | Currently provable because `PrincDiv = ⊥` makes the quotient faithful — but the proof **uses the placeholder** and will not survive honest `PrincDiv` (under which the Abel–Jacobi theorem becomes load-bearing). Listed STUB rather than STRICT-CLOSED because the proof's correctness is contingent on the stub. |
| 17 | `Jacobian.ofCurve_contMDiff` | **OPEN** | Requires item 5 (`ChartedSpace`) plus a real `ofCurve`. |
| 18 | `Jacobian.pushforward_contMDiff` | **OPEN** | Requires item 5 plus a real `pushforward`. |
| 19 | `pushforward_id_apply` | **STUB** *(PROOF-HONEST)* | Real proof via `Pic0.pushforward_id` ↦ `Div.singletonMap_id_apply`. Functoriality of `singletonMap` survives any honest `PrincDiv`. Not STRICT-CLOSED because the underlying `Jacobian` is stub. |
| 20 | `pushforward_comp_apply` | **STUB** *(PROOF-HONEST)* | Real proof via `Pic0.pushforward_comp` ↦ `Div.singletonMap_comp_apply`. Same survives-future-honest argument as 19. |
| 21 | `Jacobian.pullback_contMDiff` | **OPEN** | Requires item 5 plus a real `pullback`. |
| 22 | `pullback_id_apply` | **OPEN** | Genuinely false for the zero-stub `pullback`; remains `sorry`. |
| 23 | `pullback_comp_apply` | **STUB** | Vacuously `0 ∘ 0 = 0`. Not STRICT-CLOSED: the proof crucially depends on `pullback` being the zero stub. |
| 24 | `pushforward_pullback : pushforward f (pullback f P) = degree f • P` | **OPEN** | Headline degree formula; fails for the current zero-pullback stub. |

## Mathlib-prerequisite candidates (likely needed before strict closure)

These are *not* part of the challenge directly, but the constructions for
items 1, 2, 5, 8, 9 will need infrastructure not in mathlib at the pin.

- **Finite-dimensionality of `HolomorphicOneForm X`** on compact connected
  Riemann surface — needed for `genus X` to be the right integer. Hodge
  theory; not yet proved.
- **Honest `PrincDiv X`** — requires the residue theorem on a compact Riemann
  surface (∑_x ord_x f = 0). The other two classical inputs are now landed:
  chart-independence of `mmeromorphicOrderAt` is unconditional in
  `Manifold/MeromorphicAt.lean`, and local finiteness lives in
  `Manifold/MeromorphicDivisor.lean` (`MMeromorphicOn.divisor`). The
  `principalDivisorMap : MeromorphicNonzero X → Div X` is built in
  `Divisor/PrincipalDivisor.lean`; the eventual honest `PrincDiv X` is
  `AddSubgroup.range principalDivisorMap` once the residue-theorem leg
  shows the range lands in `Div⁰`.
- **Honest period lattice** as a rank-`2g` `Submodule ℤ` of `ℂ^g` — requires
  H₁(X; ℤ) for compact Riemann surfaces (not in mathlib at the pin) plus
  period-pairing integration of holomorphic 1-forms over loops.
- **Topological degree of proper holomorphic maps** between Riemann surfaces.
  Three classical inputs were originally named in `Manifold/Degree.lean`. As of
  2026-05-07: `fibres_finite_statement` and `regular_value_exists_statement`
  are now **discharged unconditionally** in `Manifold/FibresFiniteUnconditional.lean`
  and `Manifold/RegularValueExistsUnconditional.lean`. Only
  `fibre_card_well_defined_statement` remains — and per ZZ127's audit the
  original universe-quantified form is false at branched points; the viable
  shape is `fibre_card_well_defined_at_regular_statement` (regular-value-restricted)
  which still needs analytic local normal form `z ↦ z^k` (not in mathlib).
  ZZ129 added a regular-value certificate to `RegularValueWitness`; ZZ134
  reduced the regular-restricted statement to two analytic hypotheses.
- **`genus_eq_zero_iff_homeo`** — closed-orientable-surface classification
  plus Riemann-sphere `ChartedSpace`. Multi-month.

## Local infrastructure landed (honest, mathlib-PR-shape)

- `Manifold/Cotangent.lean` (~285 LOC) — `CotangentBundle` as dual of `Tangent.lean`, with `ContMDiffVectorBundle` instance.
- `Manifold/HolomorphicOneForm.lean` (~113 LOC) — `HolomorphicOneForm X` and `JacobianChallenge.genus X`.
- `Manifold/MeromorphicAt.lean` (~580 LOC) — `MMeromorphicAt`, `MMeromorphicOn`, `mmeromorphicOrderAt`, **unconditional** chart-independence.
- `Manifold/PathIntegral.lean` (~260 LOC) — `pathIntegralOnInterval` + 4 linearity lemmas.
- `Manifold/RiemannSphere.lean` (~625 LOC) — `OnePoint ℂ` carrier, two-chart atlas, `IsManifold 𝓘(ℂ) ω` instance, `RiemannSphere ≃ₜ S²` homeomorphism.
- `Manifold/PeriodLattice.lean` (~387 LOC) — `AnalyticTorus X := ℂ^g ⧸ ⊥` with full `ChartedSpace` + `IsManifold` instances modulo `Λ = ⊥` placeholder.
- `Manifold/RiemannSphereMobius.lean` (~204 LOC) — `z ↦ −1/z` involution.
- `Manifold/LocalMultiplicity.lean` (~155 LOC) — `degreeStub` (constant indicator).
- `Manifold/Degree.lean` (~247 LOC, 2026-04-26) — `degreeFiber` + `RegularValueWitness` + named owed classical statements.
- `Manifold/MeromorphicDivisor.lean` (~224 LOC, 2026-04-26) — `MMeromorphicOn.orderFun` + `divisor` packaging as `Function.locallyFinsuppWithin`.
- `Divisor/FiberSum.lean` (~361 LOC, 2026-04-26) — `Div.fiberSum f hf` (divisor pullback under finite-fibres) + `fiberSum_id_apply` + `fiberSum_comp_apply` (full contravariant functoriality).
- `Divisor/FiberPullback.lean` (~456 LOC after H1+H2+H3, 2026-04-26) — `Pic0.pullback (f, hf, N, hN)` via `divPullback` descent under constant-fibre-cardinality, plus full contravariant functoriality (`pullback_id`, `pullback_comp_apply`) and the divisor-side of item 24 (`Pic0.pushforward_pullback = N • id`, with `Div.singletonMap_fiberSum` as the divisor-level identity).
- `Divisor/PrincipalDivisor.lean` (~350 LOC after I1, 2026-04-26) — `MeromorphicNonzero X` + `principalDivisorMap : MeromorphicNonzero X → Div X` + `CommMonoid (MeromorphicNonzero X)` + `principalDivisorMap_one` + `principalDivisorMap_mul` (multiplicativity).
- `Divisor/PrincipalDivisorRange.lean` (~331 LOC, 2026-04-26) — `class PrincipalDivisorMultiplicative` (the `CommGroup`+lemmas typeclass) + `principalDivisorAddHom : Additive (MeromorphicNonzero X) →+ Div X` + `PrincDivHonestCandidate := principalDivisorAddHom.range` + `ResidueTheorem X : Prop` + `residueTheorem_iff_range_le_Div0` equivalence.
- `Manifold/ResidueTheorem.lean` (~338 LOC, 2026-04-26) — `residue_theorem` skeleton with one named gap (R5) + Route A breakdown (R1+R2+R3+R4) + sorry-free `residue_theorem_of_routeA` conditional discharge. **The only file in the repo where `sorry` is allowed.**
- `Topology/SurfaceGenus.lean` (~108 LOC) — `TopologicalGenus = finrank ℚ H₁` + invariance.
- `Divisor.lean` (~225 LOC) — `Div X`, `Div.degree`, `degreeHom`, `Div0`, `Pic0` modulo `PrincDiv := ⊥` placeholder.
- `Divisor/Single.lean` (~150 LOC) — `Div.single`, `degree_single = 1`, `single_sub_single_mem_Div0`.
- `Jacobian.lean` (~470 LOC) — honest `ofCurve`, honest `Pic⁰` pushforward via `Div.singletonMap`, zero-stub pullback.

### 2026-05-07 wave (R5 partition-of-unity-Stokes infrastructure + Hodge L² + period-lattice quotient + Hurwitz refactor)

- `Manifold/SmoothOneForm.lean` (~105 LOC, ZZ113) — `SmoothOneForm` type + `AddCommGroup` + `Module ℝ` + `CoeFun`.
- `Manifold/CotangentInCoordinates.lean` (ZZ117) — `inCotangentCoordinates` analogue of mathlib's `inTangentCoordinates`.
- `Manifold/CotangentBundleSmoothness.lean` (ZZ119) — `cotangentSection_contMDiffAt_iff` + `cotangentBundle_trivializationAt_snd_apply`.
- `Manifold/ContMDiffAnalyticBridge.lean` (~119 LOC, ZZ124) — `contMDiffAt_omega_iff_analyticAt_chart_pullback` (full iff for analytic manifolds).
- `Manifold/MFDerivTranspose.lean` (ZZ125) — `ContMDiffAt.mfderiv_transpose`.
- `Manifold/CotangentPullbackBridge.lean` (ZZ133) — `pullback_section_in_cotangent_coordinates_apply`.
- `Manifold/CotangentTangentBridge.lean` (ZZ141) — `inCotangentCoordinates_eq_compL_flip_inTangentCoordinates_apply`.
- `Manifold/SmoothOneFormPullback.lean` (ZZ138/142) — `SmoothOneForm.pullback` end-to-end smooth.
- `Manifold/SmoothChain.lean` (ZZ132) — `SmoothPath` + `SmoothChain` (Finsupp ℤ-linear).
- `Manifold/SmoothPathIntegral.lean` (ZZ139) — `SmoothPath.integrate` + `SmoothChain.integrate` + linearity.
- `Manifold/PeriodLatticeCompactQuotient.lean` (~53 LOC, ZZ114) — `compactSpace_quotient_of_zlattice`.
- `Manifold/PeriodLatticeChartedSpace.lean` (~175 LOC, ZZ116) — `chartedSpace_quotient_of_zlattice` + `localChart` infrastructure.
- `Manifold/PeriodLatticeLieGroup.lean` (ZZ118) — `IsManifold` instance on `E ⧸ L`.
- `Manifold/PeriodLatticeOfRankTwoG_Wiring.lean` (ZZ137) — `compactSpaceHypothesis_holds`.
- `Manifold/PeriodLatticeComplexQuotient.lean` (ZZ140) — `IsManifold 𝓘(ℂ, ·) ω` for the lattice quotient (analytic/complex variant).
- `Analysis/L2OnManifold.lean` (ZZ128) — `L2NormSq` + `IsL2 := MemLp _ 2 _`.
- `Analysis/CompactManifoldMeasure.lean` (ZZ135) — `partitionPushforwardSum` finite-measure helper.
- `Analysis/CompactManifoldMeasureExistence.lean` (ZZ136) — `compactManifoldMeasureOfData` conditional on `SubordinateChartData`.
- `Analysis/CompactManifoldMeasureFromCharts.lean` (ZZ143) — unconditional `SubordinateChartData.ofCompactManifold`.
- `Topology/OnePointHomeoSphere.lean` (~68 LOC, ZZ130) — `TopologicalGenus RiemannSphere = TopologicalGenus StandardS2`.
- `Manifold/FibresFiniteUnconditional.lean` (ZZ46/47-era, surfaced 2026-05-07) — discharges `fibres_finite_statement` unconditionally.
- `Manifold/RegularValueExistsUnconditional.lean` (same) — discharges `regular_value_exists_statement`.
- `Manifold/FibreCardOnRegularSubset.lean` (ZZ134) — `fibre_card_well_defined_on_regular_subset_holds_of_locallyConstant` (conditional on 2 analytic hypotheses).
- `Manifold/NcardMultiplicityBridge.lean` (ZZ105) — real ncard↔multiplicity bridge for regular fibres at `{0}`/`{∞}`.
- `Manifold/AnalyticLocalNormalForm.lean` (ZZ151) — `analytic_local_normal_form`: for analytic `f` at `x₀` with `analyticOrderAt (f - w₀) x₀ = k`, builds analytic `ψ` on closed ball with `ψ x₀ = 0`, `deriv ψ x₀ ≠ 0`, `f z = w₀ + (ψ z)^k`. **Hurwitz local model — the deepest classical content.**
- `Manifold/LocalBiholomorphism.lean` (ZZ152) — `AnalyticAt.exists_local_biholomorphism` packaging `HasStrictFDerivAt.toOpenPartialHomeomorph` + `AnalyticAt.analyticAt_localInverse` into a biholomorphism witness.
- `Manifold/FibreCardLocallyConstantFromNormalForm.lean` (ZZ153) — `HurwitzPatchingData` + `fibreCard_isLocallyConstant_on_subset_of_pointwiseHurwitz` (locally constant from patching data).
- `Manifold/RegularSubsetPreconnected.lean` (ZZ154) — `regularSubset_isPreconnected_of_finite_complement_hypothesis`: complement of finite C is preconnected on Y.
- `Manifold/HurwitzPatchingDataConstruction.lean` (ZZ157) — `HurwitzPatchingData.ofRegularValue`: constructs the patching data unconditionally at a regular value from ZZ151+ZZ152.
- `Manifold/FibreCardWellDefinedAtRegular.lean` (ZZ155) — `fibre_card_well_defined_at_regular_holds_of_lc_ncard_and_topo`: composes ZZ134+ZZ153+ZZ154 into the unfolded Hurwitz constant-card statement.
- `Manifold/DegreeUnconditional.lean` (ZZ156) — `Basic.lean`'s `ContMDiff.degree` aligns with honest `degreeFiber` (signature-preserving swap demonstrated).

Cumulative across all sessions: **~37,840 LOC across 162 files**. None of which strict-closes any item by itself. The path to first STRICT-CLOSED runs through `Manifold/ResidueTheorem.lean`'s named R5 gap: discharging R5 makes `PrincipalDivisorMultiplicative X` constructible (via the I1 lemmas + a `CommGroup` upgrade) and `ResidueTheorem X` true, after which the one-line swap in `Divisor.lean` (`PrincDiv := principalDivisorAddHom.range`) flips items 15, 19, 20 from STUB *(PROOF-HONEST)* to STRICT-CLOSED simultaneously. Per the 2026-05-07 cluster audits, R5 is **~60-80% built** (closest wall); other walls 5-40%.

## Honest scoring

- **STRICT-CLOSED**: 0 (no item is yet Buzzard-acceptable; every filled item
  routes through the stub `Jacobian X = Pic⁰ X` with `PrincDiv := ⊥` or
  through stub `pullback`/`degree`).
- **STUB**: 14, of which **3 are PROOF-HONEST** (items 15, 19, 20 — proof
  bodies survive future honest routing; the bottleneck is the underlying
  object).
- **OPEN**: 10.

Reaching the first **STRICT-CLOSED** requires landing one of: the residue theorem
on compact Riemann surfaces, an honest period lattice, the
closed-orientable-surface classification, or honest fibre-cardinality
for proper holomorphic maps.
