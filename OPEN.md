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
  projection lemmas. (ℂ-scaling in form arg still deferred.)

**Period-lattice arc PL-3e + ℂ-scaling closed 2026-05-13:** Scoreboard
unchanged (structural; completes ℂ-linearity of the complex-valued
period pairing in the form argument). +307 LOC PL-3e + 165 LOC ℂ-scaling,
2 new files.

* `Manifold/ComplexPeriodSmulRight.lean` (~205 LOC) — `realPart_smul` /
  `imagPart_smul` (pointwise + bundled), `realComponent_smul` /
  `imagComponent_smul` (`SmoothOneForm`-valued), `complexPeriod_smul_right
  : complexPeriod c (z • om) = z * complexPeriod c om`, the bundled
  `complexPeriodLinearMap : HolomorphicOneForm X →ₗ[ℂ] ℂ` (with cycle
  fixed), and the fully bundled ℂ-bilinear pairing
  `complexPeriodBilinear : SmoothCycle 𝓘(ℝ, ℂ) X →+ HolomorphicOneForm X →ₗ[ℂ] ℂ`
  (cycle-additive + form-ℂ-linear). Closes the algebraic-mixing-of-Re/Im
  step orthogonal to PL-3e's integrability work, and packages the full
  pairing API.

* `Manifold/ComplexPeriodH1.lean` (266 LOC) — factors the complex pairing
  through the `StokesBoundaryInvariance.H1` quotient against
  `closedHolomorphicForms S : Submodule ℂ (HolomorphicOneForm X)`
  (holomorphic forms whose real and imaginary components are both
  Stokes-closed). Delivers
  `complexPeriodH1 S : S.H1 → S.closedHolomorphicForms → ℂ` and the
  bundled `complexPeriodH1Bilinear S : S.H1 →+ S.closedHolomorphicForms
  →ₗ[ℂ] ℂ` — the H₁-side of the eventual Abel-Jacobi map. ℂ-scaling
  closure of `closedHolomorphicForms` uses the PL-3e ℂ-scaling
  identities (`realComponent (z • ω)` as ℝ-linear combination).


- `Manifold/SmoothPathIntegrability.lean` (307 LOC) — proves
  `SmoothPath.intervalIntegrable_integrand` (the integrand of the path
  integral is `IntervalIntegrable` on `[0, 1]`) via pointwise
  `Continuous.intervalIntegrable`, with continuity proved on chart-source
  neighborhoods using `inTangentCoordinates` / `mfderiv_const` on the
  velocity side, `cotangentSection_contMDiffAt_iff` on the form side,
  and tangent-cocycle chart-invariance of the pairing. Drops the
  integrability hypotheses from `SmoothPath.integrate_add`
  (`integrate_add_unconditional`); promotes chain/cycle integrals to
  form-additive (`SmoothChain.integrate_add_form`,
  `SmoothCycle.integrate_add_form`); delivers
  `complexPeriod_add_right` and the bundled `complexPeriodHomRight :
  HolomorphicOneForm X →+ ℂ` in `ComplexPeriodPairing.lean`.

**Germfield arc closed 2026-05-13 (HEAD `2e5cfb4`):** item 14's
`genus_eq_zero_iff_homeo` reduced to **one classical input**
(`ExistsSimplePoleGermAtSomePoint X`) modulo the structural typeclass
`[Subsingleton (HolomorphicOneForm X)]`. See `Topology/HTopFromSubsingleton.lean`
for the single-input capstone.

**Item 14 forward-leg refactor 2026-05-13 (HEAD `f38de0f`):**
`Topology/Item14ForwardFromFiniteDim.lean` (129 LOC) replaces the
`[Subsingleton (HolomorphicOneForm X)]` typeclass on the germfield
capstone with the weaker, Hodge-standard `[FiniteDimensional ℂ
(HolomorphicOneForm X)]`. Under finite-dim + `ExistsSimplePoleGerm`,
the open hypothesis `Genus0ImpliesS2 X` (forward leg of
`SurfaceClassificationGenus`) is discharged: `genus X = 0` →
`Subsingleton` (via existing `holomorphicOneForm_subsingleton_of_genus_eq_zero`)
→ germfield capstone fires → homeomorphism `X ≃ₜ S²`. The reverse leg
`S2ImpliesGenus0 X` (topological→geometric genus bridge) remains an
explicit named hypothesis. Scoreboard unchanged (12/24); item 14's
forward leg now sits on the single Hodge gap
(`HolomorphicOneFormFiniteDim`) plus the single RR-side existence input
(`ExistsSimplePoleGermAtSomePoint`).

**Item 14 RR-thread `LiftToMeromorphicNonzero` refactor 2026-05-13
(HEAD `88511d1`):** five new files (~990 LOC) factoring zz362's
five-fold `LiftDecomposition` onto two named classical hypotheses via
the continuity-strengthening axis. Each input of the decomposition is
discharged separately:
- `Topology/UniversalGermCoherentFromContinuity.lean` (223 LOC) —
  inputs related to germ-coherence under off-pole continuity
  (strengthened `IsBoundedByDeltaPContinuous`).
- `Topology/LiftMeroOrderFromContinuity.lean` (190 LOC) — inputs (i)
  `LiftMMeromorphicOn` and (iv) `LiftOrderPreserved` via
  `MeromorphicAt.congr` + `meromorphicOrderAt_congr`.
- `Topology/LiftNonConstancyFromContinuity.lean` (165 LOC) — input
  (v) `LiftNotConstant` via the at-pole-germ-compatibility
  strengthening `IsBoundedByDeltaPContinuousAtPole`.
- `Topology/LiftNonvanishingFromIdentityTheorem.lean` (230 LOC) —
  input (ii) `LiftNonvanishingGerm` via the named
  `MeromorphicIdentityPropagation X` hypothesis (classical identity
  theorem on connected complex 1-manifolds).
- `Topology/LiftToMeromorphicNonzeroFromTwo.lean` (170 LOC) — final
  composition: `LiftToMeromorphicNonzero X` from the two named
  hypotheses (universal at-pole-germ-compatible continuity strengthening
  + `MeromorphicIdentityPropagation X`).

**Item 14 open content, after this session, factors onto four precise
named classical inputs (down from five, post-`meromorphicIdentityPropagation_holds`):**
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
     (= `SimplyConnectedSpace StandardS2`, a small mathlib gap on
     π₁(S²) = 0), and (b) `HolomorphicOneFormSubsingletonOfSimplyConnected
     X` (the analytic chain `simply connected ⇒ closed 1-forms have
     primitives via Stokes ⇒ primitive is constant by Liouville ⇒ form
     is zero`). This route bypasses uniformization entirely.

4. Universal at-pole-germ-compatible continuity strengthening of L(δp)
   — operational germ-field refactor
   (`Topology/LiftNonConstancyFromContinuity.lean`'s
   `IsBoundedByDeltaPContinuousAtPole`).

~~5. `MeromorphicIdentityPropagation X`~~ — **discharged unconditionally
2026-05-13** by `meromorphicIdentityPropagation_holds` in
`Topology/LiftNonvanishingFromIdentityTheorem.lean`, as a direct
contrapositive of the pre-existing
`MeromorphicFunctionField.mmeromorphicOrderAt_ne_top_forall` (clopen-on-`X`
argument over mathlib's chart-pullback `meromorphicOrderAt_eq_top_iff`).
`LiftToMeromorphicNonzeroFromTwo.liftToMeromorphicNonzero_from_strengthening_and_identity`
no longer takes the identity-theorem hypothesis as an argument.

**Note on consumption:** input (4) and the `LiftToMeromorphicNonzero*`
thread feed `LiftToMeromorphicNonzeroFromTwo`, which is currently
imported only by the top-level manifest — no Item 14 closure currently
routes through it. The active Item 14 routes are
`Item14ForwardFromFiniteDim` (inputs 1/2/3) and `Item14FromGermfield`
(`RR_DimGE2_GenusZero_Germ` + topological-sphere uniformization). The
five-input enumeration is the count if/when the pointwise-thread
discharge route is wired in.

Each is citable textbook content. Scoreboard remains 12/24 (item 14 is
still OPEN; the four remaining inputs above are real classical math
that isn't at the mathlib pin `8e3c989...`).

**Period-lattice arc PL-3e closed 2026-05-13 (HEAD `9cc83c8`):** four
new commits (~four files) closing the chart-pullback integrability of
`SmoothPath.integrand` and lifting the complex period pairing to a
fully bundled ℂ-bilinear `H₁ × closedHolomorphic →ₗ[ℂ] ℂ`. Files added:
`Manifold/SmoothPathIntegrandIntegrability.lean`,
`Manifold/ComplexPeriodPairing*.lean`'s ℂ-scaling and bilinear
factor-through extensions. Net effect: the previously-deferred
ℂ-linearity-in-form-arg from PL-2's `ComplexPeriodPairing.lean` is now
fully wired through PL-3a's `PeriodPairingData` bridge into
`PeriodLatticeOfRankTwoG`.

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

**Phase 0 LOC merged 2026-05-09:** net **+9,200** total (11,310 added /
2,108 deleted, including doc files; .lean-only net +8,776). Repo size at
end of 2026-05-09 session: 49,526 LOC total in `*.lean` files (49,323
inside `JacobianChallenge/` + 203-line top-level import manifest).

**Current repo size (post-2026-05-13, HEAD `9cc83c8`):** **78,454 LOC**
total in `*.lean` files (78,093 inside `JacobianChallenge/` + 361-line
top-level import manifest). Net **+28,928** LOC since 2026-05-09 across
the germfield arc + period-lattice arc PL-1/PL-2/PL-3a-e + item-14
forward refactor + item-14 RR-thread refactor (five-fold
LiftDecomposition → two named hypotheses) + the zz302–zz388 /
zz344–zz380 RR-thread chips + residue-theorem headline closure.

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
| 14 | `genus_eq_zero_iff_homeo` (anti-hack vs. `genus := 0`) | **OPEN** | `sorry`. Architecturally closed via zz331's `genus_eq_zero_iff_homeo_from_all_conditionals` ([Topology/Item14FinalComposition.lean](JacobianChallenge/Topology/Item14FinalComposition.lean)). After zz302–zz388 (~7,500+ LOC, 34 chips for RR-thread alone in zz337–zz370, +zz381 / zz382 / zz383–zz388). zz381 reduces `LiftRegularContinuousAt X` to germ-coherence (`UniversalGermCoherent`, `UniversalGermCoherentAtPole`) in [Topology/LiftRegularContinuousAtPole.lean](JacobianChallenge/Topology/LiftRegularContinuousAtPole.lean). zz382 discharges **input #3 unconditionally** (`Surjective_of_NonConstant_Analytic_Manifold X Y` is now a THEOREM in [Manifold/SurjectiveOfNonConstantDischarge.lean](JacobianChallenge/Manifold/SurjectiveOfNonConstantDischarge.lean), 412 LOC). zz383–zz388 discharge **input #4 unconditionally** (`BijectiveAnalyticIsBiholomorphism X` is now a THEOREM in [Manifold/BijectiveAnalyticDischarge.lean](JacobianChallenge/Manifold/BijectiveAnalyticDischarge.lean), 75 LOC, sitting on the Hurwitz-corollary chain `deriv_ne_zero_of_injOn_ball` (zz383) → chart-pullback inverse (zz384/zz385) → manifold inverse `ContMDiffAt` (zz386) → global `Function.invFun` smoothness (zz387)). **Status of remaining open inputs after 2026-05-13 architectural review + zz388 close:** (1) `RR_DimGE2_GenusZero X` — vacuously true under broken `linearSystemDeltaP` (see "Architectural issue" section below); needs germ-field refactor before it has Riemann-Roch content. (2) `LiftToMeromorphicNonzero X` — depends on sub-inputs #2/#3/#5/#6 of the six-input RR split which are false against the blip counterexample under current `linearSystemDeltaP`. (3) ~~`Surjective_of_NonConstant_Analytic_Manifold`~~ **CLOSED zz382**. (4) ~~`BijectiveAnalyticIsBiholomorphism`~~ **CLOSED zz388**. (5) topological-sphere-uniformization branch (`X ≃ₜ S² → ∃ HolomorphicEquiv X RS`) — multi-thousand LOC, classical surface theory. **Conclusion**: item 14 is blocked on either the germ-field refactor (RR side, inputs #1/#2) or the topological-sphere-uniformization branch (input #5). Inputs #3 and #4 are now closed. See CLOSURE_MAP.md §D.2 for the per-input LOC table. **Post-2026-05-13 (HEAD `88511d1`)**: forward leg + `LiftToMeromorphicNonzero` discharge both refactored. Item 14's open content now sits on exactly four named classical inputs: (1) `HolomorphicOneFormFiniteDim X`, (2) `ExistsSimplePoleGermAtSomePoint X`, (3) `S2ImpliesGenus0 X`, (4) universal at-pole-germ-compatible continuity strengthening of L(δp) [operational germ-field refactor]. The fifth `MeromorphicIdentityPropagation X` was discharged 2026-05-13 by `meromorphicIdentityPropagation_holds` (contrapositive of `MeromorphicFunctionField.mmeromorphicOrderAt_ne_top_forall`). See the chip log between `f38de0f` and the identity-theorem discharge for details. |
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

**Germ-field L(D) generalisation landed 2026-05-13** (HEAD on `feat/linear-system-divisor`):
[`Topology/LinearSystemDivisor.lean`](JacobianChallenge/Topology/LinearSystemDivisor.lean)
(~270 LOC) defines `IsBoundedByDivisor D φ := ∀ y, -D(y) ≤ φ.orderAt y`
and packages `linearSystemDivisor D : Submodule ℂ (MeromorphicFunctionGerm
X)` for **any** divisor `D : Div X`, with closure under `zero`/`add`/`smul`
via chart-pullback `meromorphicOrderAt_add` and `meromorphicOrderAt_smul`.
Specialisation `linearSystemDivisor (Div.single p) = linearSystemGermDeltaP
p` recovers the existing single-pole subspace. This completes the
divisor-level half of the germ-field ambient called for above; what
remains for the RR thread is dim-bound content (`finrank ℂ` machinery on
top of an existence input like `ExistsSimplePoleGermAtSomePoint X`).

**First dim-bound layer landed 2026-05-13** (same branch):
[`Topology/LinearSystemDivisorConstants.lean`](JacobianChallenge/Topology/LinearSystemDivisorConstants.lean)
(~170 LOC) ships `constantsToLinearSystemDivisor D hD : ℂ →ₗ[ℂ]
linearSystemDivisor D` (the bundled embedding via
`Algebra.linearMap.codRestrict`) for effective `D`, plus the injectivity
`constantsToLinearSystemDivisor_injective` under `ConnectedSpace X` (via
`RingHom.injective` from the `Field` instance on
`MeromorphicFunctionGerm X`). Gives the trivial `1 ≤ dim_ℂ L(D)` for
effective `D` on a connected compact complex 1-manifold.

**Final assembly: genus-0 RR dim ≥ 2 reduces to uniformization + L(δp) finite-dim ON RS landed 2026-05-14** (same branch):
[`Topology/RRDimGE2FromUniformizationAndFiniteDimRS.lean`](JacobianChallenge/Topology/RRDimGE2FromUniformizationAndFiniteDimRS.lean)
(~75 LOC). Composes the existence transport, the finite-dim transport,
and the dim-form discharge into the headline
`rr_DimGE2_GenusZero_Germ_of_uniformization_and_RSFiniteDim`. After
this chip, the genus-0 RR dim ≥ 2 content on the germ field reduces
to two classical inputs: (i) uniformization at genus 0, and (ii)
`LinearSystemGermDeltaPFiniteDim RiemannSphere` (the finite-dim claim
on the SINGLE reference manifold `RS`, a concrete Laurent-series
computation).

**Transport infrastructure landed 2026-05-14** (same branch):
* [`Manifold/MeromorphicFunctionGermHolomorphicEquivPullback.lean`](JacobianChallenge/Manifold/MeromorphicFunctionGermHolomorphicEquivPullback.lean)
  (~155 LOC) — pullback on `MeromorphicFunctionGerm` via
  `HolomorphicEquiv`, with `orderAt` preservation.
* [`Topology/LinearSystemGermDeltaPHolomorphicEquivTransport.lean`](JacobianChallenge/Topology/LinearSystemGermDeltaPHolomorphicEquivTransport.lean)
  (~210 LOC) — `IsBoundedByDeltaPGerm` iff under pullback; bundled
  `LinearMap` between `L(δ(e p))` and `L(δp)`.
* [`Topology/LinearSystemGermDeltaPFiniteDimTransport.lean`](JacobianChallenge/Topology/LinearSystemGermDeltaPFiniteDimTransport.lean)
  (~205 LOC) — `LinearEquiv` packaging + `Module.Finite.equiv`
  transport for `LinearSystemGermDeltaPFiniteDim`.

**Transport: `ExistsSimplePoleGermAtSomePoint X` from `HolomorphicEquiv X RS` landed 2026-05-14** (same branch):
[`Manifold/MMeromorphicHolomorphicEquivTransport.lean`](JacobianChallenge/Manifold/MMeromorphicHolomorphicEquivTransport.lean)
(~265 LOC) + [`Topology/ExistsSimplePoleGermFromHolomorphicEquivRS.lean`](JacobianChallenge/Topology/ExistsSimplePoleGermFromHolomorphicEquivRS.lean)
(~160 LOC) discharge the uniformization step:

* `HolomorphicEquiv.chartTransition_analyticAt` — chart transition is
  analytic (via existing `contMDiff_omega_analyticAt_chart_pullback`).
* `HolomorphicEquiv.chartTransition_deriv_ne_zero` — derivative non-zero
  (via existing `deriv_chart_pullback_ne_zero_of_injective`).
* `mmeromorphicOrderAt_holomorphicEquiv_comp` — order equality
  `mmeromorphicOrderAt (f ∘ e) x = mmeromorphicOrderAt f (e x)` via
  mathlib's `meromorphicOrderAt_comp_of_deriv_ne_zero`.
* `MMeromorphicAt.holomorphicEquiv_comp_iff` — same for MMeromorphicAt.
* `existsSimplePoleGermAtSomePoint_of_holomorphicEquiv_RS` — headline:
  `Nonempty (HolomorphicEquiv X RiemannSphere) → ExistsSimplePoleGermAtSomePoint X`.

Composing this with the unconditional RS base case (from the prior
chip), the genus-0 RR existence side now reduces to **the
uniformization theorem alone**: `genus X = 0 → Nonempty (HolomorphicEquiv
X RiemannSphere)`. That input is the remaining classical content.

**Simple-pole germ on `RiemannSphere` landed 2026-05-13** (same branch):
[`Manifold/RiemannSphereSimplePole.lean`](JacobianChallenge/Manifold/RiemannSphereSimplePole.lean)
(~225 LOC) constructs `RSSimplePole : RiemannSphere → ℂ` (`some z ↦ z`,
`∞ ↦ 0`), packages as `MMer RiemannSphere`, and proves the germ has
`orderAt ∞ = -1` and `orderAt (some z₀) ≥ 0`. Composing through
`linearSystemGermDeltaP` gives
**`existsSimplePoleGermAtSomePoint_RiemannSphere : ExistsSimplePoleGermAtSomePoint
RiemannSphere`** — the base case of the genus-0 RR existence side.

The general statement `ExistsSimplePoleGermAtSomePoint X` for a compact
connected complex 1-manifold `X` at genus 0 reduces to this via a
`HolomorphicEquiv X RiemannSphere` (uniformization at genus 0). That
transport is the next chip.

**Multiplicative grading `L(D₁) · L(D₂) ⊆ L(D₁ + D₂)` landed 2026-05-13** (same branch):
[`Topology/LinearSystemDivisorMul.lean`](JacobianChallenge/Topology/LinearSystemDivisorMul.lean)
(~115 LOC) ships `MeromorphicFunctionGerm.orderAt_mul : (φ * ψ).orderAt y =
φ.orderAt y + ψ.orderAt y` (via chart pullback + mathlib's
`meromorphicOrderAt_mul`), then `IsBoundedByDivisor.mul` and the
Submodule-level inclusion `linearSystemDivisor_mul_le_linearSystemDivisor_add`
(using `Submodule.mul` from `Algebra/Algebra/Operations`). The L(D)
family is a graded ℂ-subalgebra structure on `MeromorphicFunctionGerm X`.

**`L(D)` monotonicity in `D` landed 2026-05-13** (same branch):
[`Topology/LinearSystemDivisorMono.lean`](JacobianChallenge/Topology/LinearSystemDivisorMono.lean)
(~125 LOC) ships `linearSystemDivisor_mono : D₁ ≤ D₂ →
linearSystemDivisor D₁ ≤ linearSystemDivisor D₂` (pointwise divisor
order from `Function.locallyFinsuppWithin.le_def`), plus
`linearSystemDivisor_zero_le_of_effective : L(0) ≤ L(D)` for effective
`D` and `constantsGerm_le_linearSystemDivisor_of_effective`. Factors
the constants embedding through `constantsGerm = L(0) ≤ L(D)` for the
effective case.

**`rank L(δp) ≥ 2` from a simple-pole germ landed 2026-05-13** (same branch):
[`Topology/LinearSystemDivisorSimplePoleRank.lean`](JacobianChallenge/Topology/LinearSystemDivisorSimplePoleRank.lean)
(~150 LOC) shows `LinearIndependent ℂ ![1, ψ]` whenever `ψ.orderAt p =
-1` via `LinearIndependent.pair_iff'` and order arithmetic at the pole
(constants have order `0` or `⊤`, never `-1`). Transfers through
`LinearMap.linearIndependent_iff` on `Submodule.subtype` and
`LinearIndependent.cardinal_lift_le_rank` to give
`rank_linearSystemGermDeltaP_ge_two_of_existsSimplePole :
ExistsSimplePoleGermAtSomePoint X → ∃ p, 2 ≤ Module.rank ℂ
(linearSystemGermDeltaP p)`. (Cardinal-valued rank, unconditional. The
`Module.finrank ≥ 2` form needs finite-dimensionality of L(δp), which
is the Riemann-Roch upper-bound side.)

**`dim_ℂ L(0) = 1` UNCONDITIONAL landed 2026-05-13** (same branch):
[`Topology/LinearSystemDivisorZeroLiouville.lean`](JacobianChallenge/Topology/LinearSystemDivisorZeroLiouville.lean)
(~220 LOC) proves `linearSystemDivisor (0 : Div X) = constantsGerm X`
**unconditionally** via composition with the existing
`liouvilleOnCompactConnected_holds` discharge in
[`Topology/HolomorphicLocallyConstantDischarge.lean`](JacobianChallenge/Topology/HolomorphicLocallyConstantDischarge.lean)
(itself a clopen globalisation of `MaxModLocalConstancy`'s chart-level
max-modulus + connectedness). Headline:
`finrank_linearSystemDivisor_zero_eq_one_unconditional :
Module.finrank ℂ (linearSystemDivisor 0) = 1`. The remaining work for
full genus-0 Riemann-Roch `dim_ℂ L(δp) ≥ 2` is `ExistsSimplePoleGerm`
content (the non-trivial RR + Serre-duality piece).

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
- `Manifold/ResidueTheorem.lean` (2026-04-26, headline retired 2026-05-13) — five named statements `R1`–`R5` (Route A breakdown) + sorry-free `residue_theorem_of_routeA` conditional discharge. No `sorry`. Headline `JacobianChallenge.residue_theorem` lives in `Manifold/ResidueTheoremUnconditional.lean`; R1–R5 discharges in `Manifold/ResidueTheoremFromRsum.lean` + `Manifold/R4FibreSumBalance.lean` + `Manifold/R5Unconditional.lean`.
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

Cumulative across all sessions: **~37,840+ LOC across 162+ files**. ZZ256 (P1.5) routed `PrincDiv := PrincDivHonestCandidate` (the multiplicative range of `principalDivisorAddHom`) — this bypassed the R5 gap as the entry path for strict-closing the functoriality stack. The residue theorem itself (R5 / `PrincDiv ⊆ Div⁰`) is now **discharged unconditionally** in `Manifold/ResidueTheoremUnconditional.lean` (2026-05-13), so the `PrincDivHonestCandidate ≤ Div0`/R5 trigger in `Divisor/StrictClosurePath.lean` is no longer conditional; what remains for item 11 (`CompactSpace (Jacobian X)`) is the Phase-2 period-lattice quotient topology, not the residue theorem. Eleven items strict-closed via the P1.4/P1.5 cascade: items 2, 3 (honest `Jacobian` + group), 6, 7, 8 (honest `ofCurve`, pushforward, pullback through divisor-level descent), 15, 19, 20 (proof-honest functoriality bodies, now over honest objects), 22, 23, 24 (honest pullback functoriality + degree formula via `pushforward_pullbackHonest_of_rsum`).

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
