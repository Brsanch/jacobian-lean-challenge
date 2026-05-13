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

**Current scoreboard (post-ZZ256 P1.5, 2026-05-12):**

- **STRICT-CLOSED:** **12 / 24** — items **2, 3, 6, 7, 8, 9, 15, 19, 20, 22,
  23, 24**. ZZ256 landed `PrincDiv := PrincDivHonestCandidate` and
  `Pic0` (honest, with manifold instances) in
  `Divisor/PrincipalDivisorRange.lean`. `Pic0.pushforward (hf)` uses P1.4
  via `JacobianPushforward.lean`. `Pic0.pullbackWeighted (h_desc)` uses
  the sister descent `Pic0.divPullbackWeighted_descent_of_smooth` in
  `JacobianPullback.lean` (genuine analytic chip).
- **STUB (placeholder topology / target / pending discharge):** items
  **1, 4, 10** = 3 items.
- **OPEN (sorry in `Basic.lean` or transitively via downstream sorry):**
  items **5, 11, 12, 13, 14, 16, 17, 18, 21** = 9 items. Item 16
  (`ofCurve_inj`) reverted from STUB to OPEN as CLOSURE_MAP predicted —
  it requires Abel-Jacobi (Phase 2).
- **Previous scoreboard (2026-05-09, HEAD `5e601e8`):** 0/24 STRICT-CLOSED.

**Period-lattice arc PL-1 closed 2026-05-13 (HEAD `8f4e0a7`):**
Scoreboard unchanged (the PL-1 infrastructure does not directly flip
items, but unblocks downstream PL-2 → PL-4 → period-lattice → items
5/11/12/13/16/17/18/21).
- `Manifold/ComplexManifoldRealification.lean` — `instance : IsManifold
  𝓘(ℝ, ℂ) n X` from holomorphic structure.
- `Manifold/HolomorphicOneFormRealComponent.lean` (400 LOC) — bundled
  `realComponent` / `imagComponent : HolomorphicOneForm X → SmoothOneForm
  𝓘(ℝ, ℂ) X` with full bundle-section smoothness chain (tangent-bundle
  compatibility + cotangent commutativity + manifold scalar-restriction
  bridge + section smoothness packaging).

**Period-lattice arc PL-2 closed 2026-05-13 (HEAD `fbb137f`):** Scoreboard
unchanged (PL-2 is structural; unblocks PL-3 / PL-4 / the period-lattice
items). 545 LOC across 3 new files.
- `Manifold/SmoothCycle.lean` (173 LOC) — `SmoothCycle I X :=
  ker(SmoothChain.boundary) : AddSubgroup (SmoothChain I X)`, basic API,
  cycle-restricted real `integrate` and `integratePairingHom`.
- `Manifold/H1SmoothMod.lean` (256 LOC) — named-hypothesis bundle
  `StokesBoundaryInvariance I X` carrying `boundaries`, `closedForms`,
  and the invariance gap; `H1 := SmoothCycle ⧸ boundaries` quotient;
  `periodPairing : H1 → closedForms → ℝ` factored via `Quotient.liftOn'`
  with half-bilinearity (zero/scalar in form arg, full additive in
  chain arg).
- `Manifold/ComplexPeriodPairing.lean` (116 LOC) — complex-valued
  `complexPeriod c om := Re ∫_c om + i · Im ∫_c om` on
  `SmoothCycle 𝓘(ℝ, ℂ) X × HolomorphicOneForm X`, plus
  `complexPeriodHom` (additive in cycle arg) and `re_`/`im_`
  projection lemmas. ℂ-linearity in the form arg is deferred
  (needs `intervalIntegrable` chart-pullback witnesses).

**Germfield arc closed 2026-05-13 (HEAD `2e5cfb4`):** item 14's
`genus_eq_zero_iff_homeo` reduced to **one classical input**
(`ExistsSimplePoleGermAtSomePoint X`) modulo the structural typeclass
`[Subsingleton (HolomorphicOneForm X)]`. See `Topology/HTopFromSubsingleton.lean`
for the single-input capstone.

(CLOSURE_MAP §A col 4 originally predicted 12 items flip; with item 9 now
STRICT-CLOSED via `Manifold/HPkgUnconditional.lean` +
`Manifold/DegreeWellDefined.lean` the actual is 12.)

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

**Phase 0 LOC merged this session (2026-05-09):** net **+9,200** total
(11,310 added / 2,108 deleted, including doc files; .lean-only net +8,776).
Repo size at end of session: **49,526 LOC** total in `*.lean` files
(49,323 inside `JacobianChallenge/` + 203-line top-level import manifest).

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
| 14 | `genus_eq_zero_iff_homeo` (anti-hack vs. `genus := 0`) | **OPEN** | `sorry`. Architecturally closed via zz331's `genus_eq_zero_iff_homeo_from_all_conditionals` ([Topology/Item14FinalComposition.lean](JacobianChallenge/Topology/Item14FinalComposition.lean)). After zz302–zz388 (~7,500+ LOC, 34 chips for RR-thread alone in zz337–zz370, +zz381 / zz382 / zz383–zz388). zz381 reduces `LiftRegularContinuousAt X` to germ-coherence (`UniversalGermCoherent`, `UniversalGermCoherentAtPole`) in [Topology/LiftRegularContinuousAtPole.lean](JacobianChallenge/Topology/LiftRegularContinuousAtPole.lean). zz382 discharges **input #3 unconditionally** (`Surjective_of_NonConstant_Analytic_Manifold X Y` is now a THEOREM in [Manifold/SurjectiveOfNonConstantDischarge.lean](JacobianChallenge/Manifold/SurjectiveOfNonConstantDischarge.lean), 412 LOC). zz383–zz388 discharge **input #4 unconditionally** (`BijectiveAnalyticIsBiholomorphism X` is now a THEOREM in [Manifold/BijectiveAnalyticDischarge.lean](JacobianChallenge/Manifold/BijectiveAnalyticDischarge.lean), 75 LOC, sitting on the Hurwitz-corollary chain `deriv_ne_zero_of_injOn_ball` (zz383) → chart-pullback inverse (zz384/zz385) → manifold inverse `ContMDiffAt` (zz386) → global `Function.invFun` smoothness (zz387)). **Status of remaining open inputs after 2026-05-13 architectural review + zz388 close:** (1) `RR_DimGE2_GenusZero X` — vacuously true under broken `linearSystemDeltaP` (see "Architectural issue" section below); needs germ-field refactor before it has Riemann-Roch content. (2) `LiftToMeromorphicNonzero X` — depends on sub-inputs #2/#3/#5/#6 of the six-input RR split which are false against the blip counterexample under current `linearSystemDeltaP`. (3) ~~`Surjective_of_NonConstant_Analytic_Manifold`~~ **CLOSED zz382**. (4) ~~`BijectiveAnalyticIsBiholomorphism`~~ **CLOSED zz388**. (5) topological-sphere-uniformization branch (`X ≃ₜ S² → ∃ HolomorphicEquiv X RS`) — multi-thousand LOC, classical surface theory. **Conclusion**: item 14 is blocked on either the germ-field refactor (RR side, inputs #1/#2) or the topological-sphere-uniformization branch (input #5). Inputs #3 and #4 are now closed. See CLOSURE_MAP.md §D.2 for the per-input LOC table. |
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

## ⚠️ Architectural issue: RR-thread linear system (flagged 2026-05-13)

The current `linearSystemDeltaP p : Submodule ℂ (X → ℂ)` is defined over
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

**Fix requires germ-based ambient.** The honest L(δp) is a Submodule of
germs (or equivalence classes modulo "essentially zero") of meromorphic
functions, not raw `(X → ℂ)`. Patching `linearSystemDeltaP` to a
sub-Submodule with the germ-canonicity predicate fails closure under
addition (poles with cancelling residues create regular sums whose
pointwise values at the pole are unconstrained → not germ-canonical).
Similarly for `MeromorphicNonzero`-based formulations.

**Right architecture**: define `MeromorphicFunctionField X` as the
ℂ-algebra of germs of meromorphic functions on a connected complex
1-manifold (using the existing `MMeromorphicOn` infrastructure but
quotiented by punctured-nhd EventuallyEq), then `L(D)` as a Submodule of
this field for any divisor `D`. This is mathlib-scale work (~800–1500
LOC for the germ field, ~300–500 LOC for L(D)), not chip-scale.

**Future-session guidance**: do not attempt to close inputs #2, #3, #5,
#6 against the current `linearSystemDeltaP`. They cannot be discharged
without rebuilding the ambient. Treat the RR-thread as blocked on the
germ-field refactor.

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

Cumulative across all sessions: **~37,840+ LOC across 162+ files**. ZZ256 (P1.5) routed `PrincDiv := PrincDivHonestCandidate` (the multiplicative range of `principalDivisorAddHom`) — this bypassed the R5 gap as the entry path; the residue theorem still gates `PrincDiv ⊆ Div⁰` (item 11 `CompactSpace`) but is no longer the bottleneck for strict-closing the functoriality stack. Eleven items strict-closed via the P1.4/P1.5 cascade: items 2, 3 (honest `Jacobian` + group), 6, 7, 8 (honest `ofCurve`, pushforward, pullback through divisor-level descent), 15, 19, 20 (proof-honest functoriality bodies, now over honest objects), 22, 23, 24 (honest pullback functoriality + degree formula via `pushforward_pullbackHonest_of_rsum`).

## Honest scoring (post-ZZ256, 2026-05-12)

- **STRICT-CLOSED**: **12** — items 2, 3, 6, 7, 8, 9, 15, 19, 20, 22, 23, 24.
- **STUB**: **3** — items 1 (`genus` needs Hodge finite-dimensionality),
  4 (discrete `TopologicalSpace`, wants Phase 2 manifold topology),
  10 (T2 honest but underlying topology stub).
- **OPEN**: **9** — items 5, 11, 12, 13, 14, 16, 17, 18, 21.

Reaching the next **STRICT-CLOSED** requires landing one of: (a) Hurwitz
constant-card across regular values (flips item 9, builds on the ZZ151-156
chain already ~50-80% landed), (b) honest period lattice → `ChartedSpace`
on `Jacobian` (flips items 4, 5, 10, plus 11/12/13 cascade), (c) Abel-Jacobi
(flips item 16), (d) closed-orientable-surface classification (item 14), or
(e) Hodge L² finite-dimensionality of `HolomorphicOneForm` (item 1).
