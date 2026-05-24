# RR-direct route audit (item 14 forward leg)

Audit date: 2026-05-24. Premise: previous handoff
(`HANDOFF_ITEM14.md` 🛑 STOP banner) instructed pivot from the
Forster §16.9 / `DBarSolvabilityAtGenusZero` route to a "direct RR"
route, hypothesizing a path to `RiemannRochGenusZero X` on arbitrary
X via "lifting from the RS unconditional case via divisor/linear-system
transport machinery, not via biholom equivalence." This audit reads
the actual scaffolding (the 4 Topology files cited in the handoff +
`HSP_AUDIT.md` §1, plus a sweep for any in-tree transport
infrastructure) and reports what is and is not possible without
introducing classical content of comparable size to the route the
pivot was meant to avoid.

This audit does NOT quote LOC estimates — per
`feedback_no_fabricated_loc_estimates.md`, estimates are only
quoted for work whose chain has been read to its leaves.

## TL;DR

* The Lean def of **`RiemannRochGenusZero X`**
  (`Topology/UniformizationFromRiemannRoch.lean:72`) is "for genus 0 X,
  there exists a degree-1 holomorphic map `X → RiemannSphere`."
* In tree, this is discharged on general X **only** via
  `riemannRochGenusZero_from_ExistsSimplePoleGerm` (which composes
  through `RR_StrictLt_of_existsSimplePoleGerm` and
  `liftToMeromorphicNonzero`), or via
  `riemannRochGenusZero_of_holomorphicEquiv_RS` (transport through a
  biholom with RS, which is the uniformization input itself).
* The only `LinearSystemGermDeltaP …` transport in tree is
  `LinearSystemGermDeltaPHolomorphicEquivTransport.lean` — it
  transports via `HolomorphicEquiv X Y`. No biholom-free transport
  exists.
* Therefore: **the "RR-direct route" reduces to discharging the same
  `hSP X` on arbitrary X that the DBar route was tracking**, unless
  new classical content is introduced. The pivot does not avoid the
  hard step; it relabels it.

## The chain

Reading the five scaffolding files cited in the handoff
(`HSP_AUDIT.md` §1, `Topology/LinearSystemDivisorSimplePoleRank.lean`,
`Topology/RRDimGE2FromUniformizationAndFiniteDim.lean`,
`Topology/RRStrictLtFromSimplePole.lean`,
`Topology/Item14FinalComposition.lean`):

```
Item14FinalComposition.genus_eq_zero_iff_homeo_from_all_conditionals
  ⇐ RiemannRochGenusZero X
  + 3 already-unconditional classical inputs
  + h_top (topological sphere ⇒ HolomorphicEquiv)

RRStrictLtFromSimplePole.riemannRochGenusZero_from_ExistsSimplePoleGerm
  ⇐ ExistsSimplePoleGermAtSomePoint X            ← OPEN on arbitrary X

LinearSystemDivisorSimplePoleRank.rr_DimGE2_GenusZero_Germ_of_existsSimplePoleGerm_finiteDim
  ⇐ hSP X + LinearSystemGermDeltaPFiniteDim X   ← second is unconditional on RS only

RRDimGE2FromUniformizationAndFiniteDim — all three theorems take
  Nonempty (HolomorphicEquiv X RS)              ← THE uniformization input itself
```

The four files form a closed system: every route to
`RiemannRochGenusZero X` on arbitrary X in tree consumes either
`hSP X` (open) or `HolomorphicEquiv X RS` (uniformization, open).
There is no third route.

## What in-tree "lift / transport" actually does

Grep'd for `transport` and `lift`. Two classes:

1. **Order-/germ-continuity lifting** (`LiftMeroOrderFromContinuity`,
   `LiftRegularContinuousAtPole`, `LiftDecomposition`,
   `GermLimitLiftSetup`, `LiftNonvanishingFromIdentityTheorem`,
   `LiftToMeromorphicNonzero`, etc.) — chart-side identity-theorem
   machinery that lifts a chart-pullback meromorphic / non-vanishing
   property to a manifold-side germ. Used inside
   `liftToMeromorphicNonzero` (one of the downstream consumers of
   `RR_StrictLt_GenusZero_Germ`). This is **not** "transport from RS
   to X"; it's "lift from punctured to non-punctured around a single
   pole on a single X".

2. **Biholom-mediated transport**
   (`LinearSystemGermDeltaPHolomorphicEquivTransport`,
   `LinearSystemGermDeltaPFiniteDimTransport`,
   `ExistsSimplePoleGermFromHolomorphicEquivRS`,
   `Item14ClassTransport`, `GenusEqZeroFromHolomorphicEquivRS`) — all
   require `HolomorphicEquiv X RS` (i.e., uniformization).

No file in tree provides a biholom-free transport of hSP, dim-finite,
or `linearSystemGermDeltaP` content from RS to arbitrary X.

## "At-pole-germ continuity" — what it is and what it discharges

`UniversalGermCoherentAtPole p` and friends
(`LiftRegularContinuousAtPole.lean`, `LiftRegularContinuousFromCoherence.lean`,
`UniversalGermCoherentFromContinuity.lean`) are identity-theorem
content that *supports* `liftToMeromorphicNonzero` — the step inside
`riemannRochGenusZero_from_RR_StrictLt_Germ` that turns a germ in
`linearSystemGermDeltaP \ constantsGerm` into a global meromorphic
nonzero function with degree 1. That step is **already in tree** and
already consumes hSP X via the strict-lt form.

So "at-pole-germ continuity" is not a separate missing piece; it is
the existing machinery downstream of hSP X, not a parallel route to
hSP X.

## So what was the handoff suggesting?

Three readings, increasingly speculative:

**(R1) `riemannRochGenusZero` constructed directly from RR-on-divisors
machinery** that bypasses the explicit hSP X / strict-lt /
liftToMeromorphicNonzero chain. This would mean formalizing
Riemann-Roch + Serre duality + `H^0(X, Ω) = 0` at genus 0 directly
(the proof sketch in `UniformizationFromRiemannRoch.lean`'s docstring,
lines 13–34). That **is** the textbook construction, but none of
Riemann-Roch / Serre duality / Hodge `H^1 = H^0(Ω)*` is in mathlib
at the pin (per `HSP_AUDIT.md` §2.7). It's not a shorter route than
DBar; it's an alternative classical-content gap of comparable size.

**(R2) Some symbolic shortcut** — e.g. constructing a meromorphic
germ on X by pulling back the RS witness through an intermediate
structure (a chart, a divisor identification, etc.) that doesn't
require a biholom X ≃ RS. I read `RiemannSphereSimplePole.lean`'s
construction: `RSSimplePole : RS → ℂ` is literally the function `z`
on the affine chart, `0` at `∞`. There is no way to push this through
a single chart of an arbitrary X to a globally meromorphic function
on X without classical content (you'd have to extend across all
other charts, which is exactly what Forster 16.9's cutoff + DBar
correction does).

**(R3) The handoff was overestimating what's available** in the tree
and the actual remaining gap is the same hSP X classical-content gap
that's been the open frontier since `HSP_AUDIT.md` was written
(2026-05-23).

I think (R3) is the honest reading. The HSP_AUDIT TL;DR is explicit:

> The actual hSP-side gap is one classical content statement —
> uniformization-at-genus-0 (or, equivalently, `∂̄`-solvability at
> genus 0), not multiple.

and §4.4 lists exactly two classical-content gaps, neither of which
"RR-direct route" eliminates.

## What WOULD work if classical content is introduced

For each interpretation:

* **(R1) Direct RR + Serre + Hodge route.** Would require formalizing
  enough of Riemann-Roch and Serre duality on a compact Riemann
  surface to derive `dim H^0(X, O(δp)) ≥ 2` from `H^0(X, Ω) = 0` at
  genus 0. This is the period-pairing / Hodge route. Size is
  comparable to the DBar route. Not in mathlib at the pin.

* **(R-uniform) Period-mapping uniformization.** Build a biholom
  `X ≃ RS` from `genus X = 0` via the period mapping, then route
  through the existing `_of_holomorphicEquiv_RS` transport. Forster
  §17 + Griffiths-Harris §2. Also heavy.

* **(R-DBar) `DBarSolvabilityAtGenusZero X` discharge.** The route
  the handoff's STOP banner rules out, citing multi-year content.

All three are textbook-classical content of comparable size. The
audit's honest conclusion is that **no shorter route exists in the
current tree** without introducing one of them.

## Recommendation

Before chipping anything, escalate to the user. The handoff banner
ruled out the DBar route on grounds of size, but the "RR-direct"
route as literally described requires the same or larger amount of
classical content that is also not in mathlib. The user may have
meant a specific construction I'm not seeing — or may want to
reconsider one of the routes.

Specific question to surface (already in this audit):

> "Lift `existsSimplePoleGermAtSomePoint_RiemannSphere` to arbitrary
> X via divisor/linear-system transport machinery, not via biholom
> equivalence" — could you point at the construction you had in mind?
> The only `linearSystemGermDeltaP` transport in tree
> (`LinearSystemGermDeltaPHolomorphicEquivTransport.lean`) goes
> through `HolomorphicEquiv X Y`. Without a biholom, there is no
> X-to-X transport of a function defined on RS.

If the answer is one of (R1)/(R-uniform)/(R-DBar), this audit has
the framing right and we pick the smallest of the three. If the
answer is something I missed in the tree, this audit needs to be
revised before chipping.

## Anti-paraphrase gate check

Per `feedback_lean_paraphrase_antipattern.md`: writing a chip that
"bridges named hypothesis A to named hypothesis B" without genuine
classical content is the exact anti-pattern. Any next-session chip
must discharge a named hypothesis by **classical proof** (Forster,
Griffiths-Harris, Miranda content) or by a `mathlib` lemma — not by
introducing a new def that "reduces hSP X to hSP'_with_lift X" or
similar.

Until classical content is on the table, there is nothing useful to
chip in this thread.
