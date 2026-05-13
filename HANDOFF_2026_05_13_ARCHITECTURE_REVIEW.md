# Handoff — 2026-05-13 (architecture review + zz381/zz382 closures)

**Session window:** 2026-05-13. Main HEAD `6570172`. Two chips landed
(zz381, zz382). One major architectural finding documented in `OPEN.md`.

## What landed

### zz381 — discharge of `x = p` case of `LiftRegularContinuousAt`
* New file: [`JacobianChallenge/Topology/LiftRegularContinuousAtPole.lean`](JacobianChallenge/Topology/LiftRegularContinuousAtPole.lean) (180 LOC).
* New theorems:
  * `exists_tendsto_punctured_of_isBoundedByDeltaP_of_order_nonneg`
    (generalisation of zz365 dropping the `x ≠ p` premise).
  * `continuousAt_germLimitLift_at_p_of_universalGermCoherentAtPole`
    (substantive at-pole discharge).
  * `liftRegularContinuousAt_of_universalGermCoherent_both` (composes
    zz380's off-pole and zz381's at-pole into `LiftRegularContinuousAt X`).
* `LiftRegularContinuousAt X` (input #4 of the six-input split) factors
  through two precise germ-coherence statements, both classical
  identity-theorem content.

### zz382 — discharge of `Surjective_of_NonConstant_Analytic_Manifold`
* New file: [`JacobianChallenge/Manifold/SurjectiveOfNonConstantDischarge.lean`](JacobianChallenge/Manifold/SurjectiveOfNonConstantDischarge.lean) (412 LOC).
* New theorems:
  * `isOpen_setOf_isLocConstAt` / `isClosed_setOf_isLocConstAt`
    (identity-theorem clopen-globalisation: `LocConst f` is clopen on
    connected `X` for any `ContMDiff … ω f`).
  * `globally_const_of_isLocConstAt` (locally constant at one point ⇒
    globally constant on connected `X`).
  * `range_mem_nhds_of_nonConstant` (chart-level open-map dichotomy
    filter-chased to `range f ∈ 𝓝 (f x₀)`).
  * `isOpen_range_of_nonConstant`, plus the headline
    `surjective_of_NonConstant_Analytic_Manifold_holds`.
* **Closes input #3 of the item-14 six-input composition unconditionally.**

## What did NOT land (and why)

### The RR-thread linear-system architectural issue (documented in `OPEN.md`)

While re-evaluating input #3 of the RR-thread (`LiftNonvanishingGerm`),
discovered a real counterexample: `g(p_0) = 100, g(y) = 0 otherwise`
satisfies `IsBoundedByDeltaP p g` and is not a constant function (so
`g ∉ span ℂ {1}`), yet `germLimitLift g ≡ 0` with
`mmeromorphicOrderAt … = ⊤` everywhere. This violates the conclusion
of `LiftNonvanishingGerm` as stated.

Consequences:

1. `finrank ℂ (linearSystemDeltaP p) = ∞` trivially via the "blip"
   family. So `RR_DimGE2_GenusZero X` is vacuously true with no
   Riemann-Roch content.
2. Inputs #2 (`LiftMMeromorphicOn`), #3 (`LiftNonvanishingGerm`), #5
   (`LiftOrderPreserved`), #6 (`LiftNotConstant`) of the six-input split
   are **false as stated** against the blip counterexample.
3. Input #4 (`LiftRegularContinuousAt`, now reduced via zz380+zz381) is
   the only sub-input that survives the architectural review, but the
   germ-coherence hypotheses it now factors through are themselves about
   elements of the broken `linearSystemDeltaP`.

Explored fix options:
* **Option 1 (strengthen non-constancy hypothesis to
  `germLimitLift g ∉ span {1}`)**: closes inputs #3 and #6 but doesn't
  fix the structural issue — input #1's vacuous truth remains, and
  inputs #2, #5 still have closure issues.
* **Option 2 (germ-canonical sub-Submodule)**: fails closure under
  addition due to pole interactions (cancelling residues create regular
  sums whose pointwise values at the pole are unconstrained, so
  germ-canonicity is broken in the sum).
* **Option 3 (quotient by essentially-zero kernel)**: `germLimitLift`
  is not ℂ-linear (same pole-cancellation case), so the kernel isn't a
  Submodule and the quotient construction doesn't work.
* **Option 4 (use `MeromorphicNonzero X ∪ {0}` as ambient)**: same
  closure issue at poles. `MeromorphicNonzero` itself has only `Mul`/`One`
  instances, no `Add`/`Zero` — for a good reason.

**Conclusion**: the right ambient is *germs of meromorphic functions*
on a Riemann surface (not raw `(X → ℂ)`). Building this is multi-session
mathlib-grade work, not a chip-sized refactor.

### Attempted: `BijectiveAnalyticIsBiholomorphism` (input #4 of item 14)

Started the chip targeting input #4 (the last chip-sized item in the
item-14 frontier outside the broken RR thread). The proof structure is
clean (apply `localKFoldMultiplicity_preimage_card_fully_unconditional`
to derive ≥ 2 preimages, contradicting bijectivity; chain to
`AnalyticAt.analyticAt_localInverse` for local analytic inverse; glue
globally to `Diffeomorph`).

Real LOC estimate landed at **~1500–2000**, larger than initial
**800–1500** estimate, primarily because the lemma's `ε` (preimage-
ball radius) needs to be exposed as `≤ R₀` to put preimages inside
the injection neighbourhood. The existing `localKFoldMultiplicity_*`
chain bounds `ε ≤ ρ' ≤ R` internally but doesn't expose this in the
return type. Fix requires either modifying the existing lemma (touches
6+ caller files) or duplicating the proof — both real refactor work,
not chip-sized.

## Mathlib-PR-ready candidates (proposed, not yet built)

Per the durable principle saved 2026-05-13 ("mathlib work is part of the
total pool of work"), the right way to unblock the remaining chips is to
contribute classical infrastructure to mathlib rather than patch the
challenge repo. Concrete gaps identified:

* **Hurwitz corollary**:
  `AnalyticAt.deriv_ne_zero_of_locally_injective` for `f : ℂ → ℂ`.
  Classical, missing from mathlib at the pin. ~300–500 LOC including the
  `ε ≤ R₀`-exposed cardinality wrapper.
* **Local preimage cardinality with radius bound**: wrapper around the
  repo's `localKFoldMultiplicity_*` chain exposing `ε ≤ R₀`. ~200–300 LOC.
* **Identity theorem for `MMeromorphicOn` connected complex manifolds**:
  repackaging of zz382's clopen pattern in mathlib generality. ~300–600
  LOC.
* **Germ-based meromorphic function field on a Riemann surface**:
  multi-session arc. The honest architectural foundation for L(D),
  Riemann-Roch, Serre duality. Probably 800–1500 LOC for the field, plus
  300–500 LOC for `L(D)` as a Submodule of the field.

## Repository state

* Branch `main`, HEAD `6570172`.
* All commits CI-green (zz381 + zz382 both verified via full `lake build`).
* No `sorry`, no `axiom` anywhere in repo (modulo the deliberately-
  documented residue-theorem placeholder in
  `Manifold/ResidueTheorem.lean`).
* `OPEN.md` updated with the architectural-review section above item 14.

## Where to pick up next session

Either:

1. **Hurwitz corollary mathlib contribution** (`AnalyticAt.deriv_ne_zero
   _of_locally_injective` + `analyticPreimageCard_eq_order_within_radius`
   helper). ~500–700 LOC, mathlib-PR-ready. Unblocks input #4
   (`BijectiveAnalyticIsBiholomorphism`) once paired with the gluing chip.

2. **Germ-field arc start** — define `MeromorphicFunctionField X` with
   the right algebraic structure (ℂ-algebra/field via germ-quotient on
   `MMeromorphicOn`). First chip of multi-session arc. Unblocks the RR
   thread (input #1) once the field + L(D) layer is built.

3. **Item 10/11/12/13 (Jacobian instances)** — `T2Space`, `CompactSpace`,
   `IsManifold`, `LieAddGroup` on `Jacobian X`. These need the period-
   lattice quotient already partially built in
   `Manifold/PeriodLatticeChartedSpace.lean`. Probably chip-sized once
   the lattice quotient is wired into `Jacobian.lean`.

Order recommendation: (1) is most surgical and unblocks item 14 input
#4 cleanly. (2) is the right long-term move but multi-session. (3) is a
side-quest from item 14 but lets us flip Jacobian items.
