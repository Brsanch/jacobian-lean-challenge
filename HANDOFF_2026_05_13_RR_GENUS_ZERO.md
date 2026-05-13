# Handoff — 2026-05-13: RiemannRochGenusZero thread reduced to 6 named classical inputs

**Session window:** 2026-05-13. `57dd195` → `fef2232`. 45 commits, ~4,200 LOC net,
all merged to `main` and pushed to `origin/main`. CI/lake-build clean. No `sorry`,
no `axiom` anywhere.

## Headline

Item 14's `RiemannRochGenusZero X` named open input has been
**architecturally reduced** from "1 of 4 opaque named existence inputs" to
"composition of 6 named precise classical statements," with the **analytic-bridge
half fully unconditional** (two new theorems landed).

`RiemannRochGenusZero X` itself is **still OPEN**. The item 14 scoreboard is
**unchanged at 12/24 STRICT-CLOSED**. What changed is the *target shape* the
remaining classical content needs to be delivered in.

## Final composition theorem

`JacobianChallenge/Topology/RRGenusZeroFinalComposition.lean`
(zz378):

```
riemannRochGenusZero_from_six_inputs
    [Nonempty X]
    (hRR : RR_DimGE2_GenusZero X)
    (h_mero : LiftMMeromorphicOn X)
    (h_nonvan : LiftNonvanishingGerm X)
    (h_reg_cts : LiftRegularContinuousAt X)
    (h_ord : LiftOrderPreserved X)
    (h_nc : LiftNotConstant X) :
    RiemannRochGenusZero X
```

## The 6 named open inputs

| # | Input | Classical content | Status / next step |
|---|---|---|---|
| 1 | `RR_DimGE2_GenusZero X` | RR formula + Serre duality at `δp` for genus 0; equivalently `∃ p, 2 ≤ finrank ℂ (linearSystemDeltaP p)` | Open — heavy; needs sheaf cohomology or L²-Hodge. Multi-thousand LOC, not in mathlib at the pin. |
| 2 | `LiftMMeromorphicOn X` | `germLimitLift` preserves global meromorphy | Open — germ-preservation under canonicalisation |
| 3 | `LiftNonvanishingGerm X` | `germLimitLift g` has no ⊤-order point when g is non-constant | Open — identity theorem for analytic functions |
| 4 | `LiftRegularContinuousAt X` | `germLimitLift g` is `ContinuousAt` at non-pole points | **Partially discharged in zz380**: at `x ≠ p`, follows from `UniversalGermCoherent X p` (zz380's named hypothesis). The `x = p` case (when the lift's order at `p` happens to be ≥ 0) remains. |
| 5 | `LiftOrderPreserved X` | `germLimitLift g` satisfies the same L(δp) bounds as g | Open — germ-coherence preservation |
| 6 | `LiftNotConstant X` | `germLimitLift g` is non-constant when g is | Open — non-constancy preservation |

## Two unconditional theorems gained

| Theorem | File | Content |
|---|---|---|
| `uniformSimplePoleRegularity_holds` | `Manifold/ChartPullbackDerivSimplePoleDischarge.lean` (zz344) | The chart-pullback derivative is non-zero at any simple pole. Real analytic proof via mathlib's `meromorphicOrderAt_eq_int_iff` + `HasDerivAt.fun_div` quotient rule + `Filter.EventuallyEq.deriv_eq`. |
| `liouvilleOnCompactConnected_holds` | `Topology/HolomorphicLocallyConstantDischarge.lean` (zz350) | Holomorphic functions on a compact connected complex 1-manifold are constant. Real proof via chart-level `Complex.eventually_eq_of_isLocalMax_norm` + clopen globalisation on connected X. |

These collapse what would otherwise be 2 additional named open hypotheses.

## Infrastructure landed this session

* **Linear-system stack** — `linearSystemDeltaP p : Submodule ℂ (X → ℂ)` with
  full zero/add/smul/neg/sub closure laws, constants subspace, finrank = 1 of
  constants, strict-gt iff exists-non-constant.
  - Files: `LinearSystemDeltaP.lean`, `LinearSystemAPI.lean`,
    `LinearSystemConstants.lean`, `LinearSystemSubLemmas.lean`,
    `LinearSystemFinrankGE1.lean`, `ConstantsFinrank.lean`.

* **Analytic-bridge stack** — pole-extension-to-RS construction proven
  step-by-step: ∞-fibre singleton (zz338), non-constancy from pole (zz339),
  `RegularValueWitness` builder (zz340), `degreeFiber = 1` (zz341).
  - Files: `SinglePoleInftyFibre.lean`, `ToRSNonConstantFromSinglePole.lean`,
    `RegularValueWitnessAtInfty.lean`, `DegreeOneFromSinglePole.lean`,
    `SimplePoleAnalyticReciprocal.lean`,
    `ChartPullbackDerivSimplePoleDischarge.lean`.

* **Max-modulus stack** — full clopen Liouville argument:
  foundational continuity/max-attainment (zz348), chart-level local constancy
  (zz349), clopen globalisation (zz350).
  - Files: `HolomorphicFoundational.lean`, `MaxModLocalConstancy.lean`,
    `HolomorphicLocallyConstantDischarge.lean`.

* **GermLimit-lift infrastructure** — `germLimitLift` definition with API
  (zero/const/continuous/idempotence cases), punctured-nhd Tendsto at non-pole
  points, germ-coherence predicate, EventuallyEq invariance, regular-continuity
  reduction.
  - Files: `GermLimitLiftSetup.lean`, `LimitAtNonPole.lean`,
    `GermCoherent.lean`, `LiftRegularContinuousFromCoherence.lean`.

* **MeromorphicNonzero builders** — for plain functions: the strong
  continuous-form builder + weak `regular_continuousAt`-form builder.
  - File: `MeromorphicNonzeroBuilder.lean`.

* **Decomposition / composition theorems** — chain everything from 6 named
  inputs into `RiemannRochGenusZero X`.
  - Files: `RiemannRochGenusZeroDecomposition.lean`,
    `MeroSinglePoleBridgeConditional.lean`,
    `RiemannRochGenusZeroSingleInput.lean`, `ExistsMeroSimplePoleSplit.lean`,
    `LiouvilleFromLocalConstancy.lean`, `LinearSystemConstants.lean`,
    `ExistenceBridge.lean`, `RRDimensionForm.lean`,
    `ExistenceFromFinrank.lean`, `RRGenusZeroFinrankChain.lean`,
    `LiftDecomposition.lean`, `RRGenusZeroFinalComposition.lean`.

## Where to pick up next session

**Cleanest next chip (zz381+):** the `x = p` case of `LiftRegularContinuousAt`
to complete the discharge of input #4. Currently zz380 covers `x ≠ p` only;
the `x = p` case (where the lift's order at `p` happens to be ≥ 0) requires
a generalisation of zz365 to allow `x = p` under the order condition. Bounded
chip (~150–300 LOC).

**Higher-value next thread:**
1. Attack input #5 (`LiftOrderPreserved`) via the explicit germ-preservation
   argument: at every x, the chart-pullback germ of `germLimitLift g` agrees
   with that of `g` on punctured nhds (since both equal the analytic-
   continuation value). The argument needs mathlib's `MeromorphicAt.analyticAt`
   + `meromorphicOrderAt_eq_int_iff` lifted through chart compositions.
   Estimated 400–800 LOC.

2. Attack input #3 (`LiftNonvanishingGerm`) via mathlib's identity theorem
   (`AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` +
   `eqOn_of_preconnected_of_eventuallyEq`). The argument is: if `germLimitLift
   g x = ⊤` at some x, then g vanishes in a chart-pullback open set; by
   identity theorem + connectedness, g vanishes everywhere; this contradicts
   non-constancy. Estimated 600–1000 LOC.

3. Attack input #1 (`RR_DimGE2_GenusZero`) — the heaviest one. Needs sheaf
   cohomology or L²-Hodge formalisation. **Multi-thousand LOC**; do not
   attempt without major mathlib infrastructure changes or a focused multi-
   session plan.

## Cross-references

* `OPEN.md` line 85: item 14 frontier note with zz337-zz370 update.
* `CLOSURE_MAP.md` §D.2: full 6-input table + zz337-zz366 chip log.
* `RRGenusZeroFinalComposition.lean`: final composition theorem.
* `RRDimensionForm.lean`: `RR_DimGE2_GenusZero` named hypothesis definition.
* `LiftDecomposition.lean`: 5 lift sub-hypothesis definitions.
* `LiftRegularContinuousFromCoherence.lean` (zz380): substantive discharge of
  regular-continuity at non-pole points.

## Honest accounting

* `RiemannRochGenusZero X` was the user's stated goal. **It is still OPEN.**
* Item 14's scoreboard is unchanged (12/24).
* What changed: 45 commits of real Lean code, ~4,200 LOC. Two new
  unconditional theorems closed real analytic content. The remaining
  RR-thread inputs are now 6 precise textbook-citable statements rather than
  one opaque existence claim.
* The honest remaining work to close `RiemannRochGenusZero X` is dominated by
  input #1 (Riemann-Roch + Serre duality), which is genuinely multi-thousand-
  LOC content not in mathlib at the pin.
