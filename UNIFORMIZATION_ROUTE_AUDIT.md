# Uniformization-named-hypothesis route audit

> **⚠️ SUPERSEDED snapshot. Canonical current state for Item 14 lives
> in [`HANDOFF_ITEM14.md`](HANDOFF_ITEM14.md) "ACTIVE ARC — CANONICAL
> CURRENT STATE". This audit's "six parallel routes A-F" framing is
> still correct as a Lean-level catalog of distinct named hypotheses,
> but it overstates parallelism: per the canonical statement, all six
> are textbook-equivalent to one classical theorem, and in-tree
> transport machinery means closing any one closes them all. The
> audit's "small equivalence-proving chip" recommendation is also
> reframed by the canonical view as helpful but not closure-bearing.**

**Date**: 2026-05-26.
**Context**: After `DBAR_CONSUMER_AUDIT.md` showed abstract-`X`
discharge of `DBarSolvabilityAtGenusZero X` is multi-month at this
mathlib pin, and `REARCHITECTURE_AUDIT.md` showed no classical
alternative is lighter, the user asked: are there pre-existing
*named-hypothesis* routes through uniformization that compress the
open frontier into a more tractable shape?

**Finding**: yes — the repo has already done this work. **Item 14 is
already reducible (via parallel routes) to several different named
classical hypotheses**, any one of which closes Item 14 if
discharged.

## The parallel routes already in tree

### Route A — DBarSolvabilityAtGenusZero (the Pompeiu/Forster-cutoff arc)

* Named hypothesis: `DBarSolvabilityAtGenusZero X`
  ([`ExistsSimplePoleGermFromGenusZeroDBarSolvability.lean:121`](JacobianChallenge/Manifold/ExistsSimplePoleGermFromGenusZeroDBarSolvability.lean#L121))
  + per-`p` `ChartAtConstantOnSource p` (innocuous on concrete X).
* Closes via Forster §16.9 cutoff →
  `ExistsSimplePoleGermAtSomePoint X` → Item 14.
* This is the route the Pompeiu kernel arc (Chips 1-5, ~3000+ LOC of
  in-tree analytic content) targets. Phase A of the analytic
  iteration landed 2026-05-26.

### Route B — UniformizationToRiemannSphere (single-input uniformization)

* Named hypothesis: `UniformizationToRiemannSphere X`
  ([`Item14FromSingleUniformization.lean`](JacobianChallenge/Topology/Item14FromSingleUniformization.lean)):
  ```
  (genus X = 0 ∨ Nonempty (X ≃ₜ StandardS2)) → Nonempty (HolomorphicEquiv X RS).
  ```
* Closes BOTH directions of Item 14 directly via `Or.inl` (forward,
  genus = 0 ⇒ biholomorphic to RS) / `Or.inr` (reverse, S² ⇒
  biholomorphic to RS). Each side composes with the unconditional
  transport machinery.
* **Single open input.** Combined with
  [`Item14ClassTransport.lean`](JacobianChallenge/Topology/Item14ClassTransport.lean)
  (transport through biholomorphisms) + the unconditional discharge
  for `RiemannSphere`
  ([`UniformizationInputsRiemannSphere.lean`](JacobianChallenge/Topology/UniformizationInputsRiemannSphere.lean)).

### Route C — RiemannRochGenusZero (degree-1 meromorphic function)

* Named hypothesis: `RiemannRochGenusZero X`
  ([`UniformizationFromRiemannRoch.lean`](JacobianChallenge/Topology/UniformizationFromRiemannRoch.lean)):
  ```
  genus X = 0 → ∃ (f : X → RS) (hf : ContMDiff ω f),
    ¬ IsConstantMap f ∧ ContMDiff.degreeFiber f hf = 1.
  ```
* Closes via the degree-1 → biholomorphism argument, which feeds into
  Route B's `UniformizationToRiemannSphere`.
* Classical content: Riemann-Roch + Serre duality for `O(δp)` on
  genus-0 RS.

### Route D — Two-input uniformization

* Named hypotheses: `UniformizationGenus0 X` + `HolomorphicOneFormEquivRiemannSphere X`
  ([`Item14FromUniformization.lean`](JacobianChallenge/Topology/Item14FromUniformization.lean)).
* Closes via the bundled `surfaceClassificationGenus_of_uniformization_inputs`.
* Two separate inputs but no harder than Route B's single input.

### Route E — Four-input minimal

* Named hypotheses: `ExistsSimplePoleGermAtSomePoint X` +
  `BasedSmoothLoopsBoundHypothesis` + per-basis smoothness/FTC
  ([`Item14From4MinimalInputs.lean`](JacobianChallenge/Topology/Item14From4MinimalInputs.lean)).
* This is the "splayed" version — distributes the forward + reverse
  legs across multiple named inputs. Some are unconditional on
  concrete X (RiemannSphere); only `ExistsSimplePoleGermAtSomePoint`
  remains for abstract X.

### Route F — Two minimal classical inputs

* Named hypotheses: `RiemannRochGenusZero X` + topological-sphere
  uniformization input
  ([`Item14From2MinimalClassicalInputs.lean`](JacobianChallenge/Topology/Item14From2MinimalClassicalInputs.lean)).
* Discharges the 3 unconditional inputs of Route E's 5-input form,
  leaving the 2 deep classical ones.

## What this means

Item 14's open content is **multi-route**: closing ANY of the named
hypotheses in Routes A-F discharges Item 14. The repo has already
factored the architecture so that the "open wall" can be approached
from several angles.

**Mathematical equivalence**: all routes are equivalent in
mathematical difficulty (each requires uniformization-class
machinery: H¹(X, O) = 0, Riemann-Roch + Serre, or uniformization
itself). They are convertible via standard equivalences:

```
DBarSolvabilityAtGenusZero X (Route A's input)
    ⟺ H¹(X, O) = 0 (Dolbeault)
    ⟺ (by RR + Serre) RiemannRochGenusZero X (Route C's input)
    ⟹ UniformizationToRiemannSphere X (Route B's input,
       restricted to the genus = 0 disjunct)
```

**Formalization-cost equivalence**: at this mathlib pin, NONE of
these named hypotheses is closer to mathlib than any other. The
"easiest" route is whichever one the future formalizer can plug
into mathlib's eventual sheaf-cohomology / Riemann-Roch /
uniformization additions. Today they are all equally open.

## What's already in `OPEN.md` vs what's missing

`OPEN.md` line 59 currently presents Route A (DBarSolvability) as
THE bottleneck. It does **not** mention:

* Route B's `UniformizationToRiemannSphere X` (the single-input
  reduction in `Item14FromSingleUniformization.lean`).
* Route C's `RiemannRochGenusZero X`.
* Route D's two-input bundle.
* Route F's two-input compression.

This makes the open frontier look narrower than it actually is.
**Multiple equally-valid named hypotheses are the actual open
frontier**, and OPEN.md should reflect this.

## Concrete recommendation

Update `OPEN.md` Item 14 entry to list all of Routes A-F as
parallel open frontiers, citing the files that consolidate each
named-hypothesis bundle. This makes the project state honest about
what's open without overstating the difficulty of any one path.

## Open question: are the routes provably equivalent in Lean?

A small constructive contribution: ship `Lean lemmas` proving the
implications among the named hypotheses (e.g.,
`DBarSolvabilityAtGenusZero X → UniformizationToRiemannSphere X`),
so the equivalence is not just informal. Currently the routes are
**parallel** (each plugged separately into the closure), not
**proven equivalent**. Closing the equivalences would consolidate
the open frontier into a single Prop with multiple equivalent
names.

This is a tractable Lean chip (~100-300 LOC, depending on how
mathlib-aware the chain is), and would clean up the open-frontier
story considerably.
