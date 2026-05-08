/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RamificationIndex
import JacobianChallenge.Manifold.Degree
import JacobianChallenge.Manifold.FibresFiniteUnconditional

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Ramification sum equals degree (ZZ179d statement)

Names the load-bearing analytic identity for the multiplicity-weighted
pullback (`Divisor/FiberPullbackWeighted.lean`):

```
∀ y : Y, ∑ x ∈ fibre y, manifoldRamificationIndex f x = degreeFiber f hf
```

for non-constant `ContMDiff f`. This is the classical Riemann-Hurwitz
total-weight statement: at every point `y` (regular *or* branch), the
sum of local ramification indices over the fibre equals the topological
degree.

## What this file delivers

* `Owed.degree.ramificationSumEqualsDegree_statement` — the named
  obligation, in
  `∀ f, ContMDiff f → ¬ IsConstantMap f → ∀ y, ...` shape.

## What is owed (and not yet discharged)

The proof requires composing four ingredients, none of which is glued
together for compact connected complex 1-manifolds at this mathlib pin:

1. **Disjoint neighbourhoods around fibre points.** `f ⁻¹' {y}` is finite
   (ZZ48) and `X` is T2, so we get pairwise disjoint open neighbourhoods
   `U_i` of each `x_i ∈ fibre`.
2. **Planar k-fold on each chart-disk.** ZZ91 / ZZ92 supply the
   `localKFoldMultiplicity_preimage_card_fully_unconditional` content in
   chart coordinates: for `w` in a small punctured disk around `f(x_i)`,
   `|{z ∈ ball x_i ε_i | f z = w}| = manifoldRamificationIndex f x_i`.
3. **All preimages of nearby regular `w` lie in `⋃ U_i`.** Compactness
   of `X` plus continuity of `f` gives that for `w` close enough to
   `y`, every preimage lies in one of the `U_i`. (Otherwise a sequence
   of preimages of `w_n → y` outside `⋃ U_i` would limit to a fibre
   point not in `fibre`, contradiction.)
4. **Regular fibre cardinality equals degree.** ZZ176 gives constant
   card on regular witnesses; `degreeFiber f hf = (Classical.choice
   h_exist).card` plugs in.

Composing 1-4 gives the identity at *every* `y`, not just regular ones,
because the planar k-fold accounts for branch points by counting
multiplicity.

No `sorry`, no `axiom`. The statement is recorded as an `Owed.degree`
obligation; the proof body is a follow-up chip. -/

@[expose] public section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

namespace ContMDiff

namespace Owed.degree

universe u v

/-- (ramification-sum) **The Riemann-Hurwitz total-weight identity.**

For every non-constant `ContMDiff f : X → Y` between compact connected
complex 1-manifolds, the sum of local ramification indices over any
fibre equals the topological degree.

The fibre `(f ⁻¹' {y}).toFinset` is materialised via the unconditional
fibre-finiteness theorem `fibres_finite_statement_holds_unconditional`
(ZZ48), which requires the non-constancy hypothesis.

**Status:** statement only. The proof is a follow-up chip composing
four named ingredients (see file docstring). -/
def ramificationSumEqualsDegree_statement
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] : Prop :=
  ∀ (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (y : Y),
      (∑ x ∈ (fibres_finite_statement_holds_unconditional f hf hnc y).toFinset,
        JacobianChallenge.Manifold.manifoldRamificationIndex f x : ℕ)
        = JacobianChallenge.ContMDiff.degreeFiber f hf

end Owed.degree

end ContMDiff

end JacobianChallenge
