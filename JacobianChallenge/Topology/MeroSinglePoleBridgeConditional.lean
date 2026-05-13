/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.RiemannRochGenusZeroDecomposition
import JacobianChallenge.Manifold.DegreeOneFromSinglePole

set_option diagnostics.threshold 100

/-! # `MeroSinglePoleExtendsToDeg1Map X` conditional on a universal-regularity hypothesis

This file closes zz337's named analytic-bridge hypothesis
`MeroSinglePoleExtendsToDeg1Map X` conditional on a single named
classical input:

  `UniformSimplePoleRegularity X` :=
    ∀ (f : MeromorphicNonzero X) (p : X),
      mmeromorphicOrderAt _ f.toFun p = -1 →
      (∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt _ f.toFun x) →
      ChartPullback_Deriv_AtSimplePole_NeZero f p

This is precisely the classical "simple poles are regular for the
pole-extension to the Riemann sphere" statement. Forster §1.4 + §3.4:
near a simple pole `p`, `f ∼ c/(z - chart(p))` with `c ≠ 0`, hence
`1/f ∼ (z - chart(p))/c`, hence the south-chart-composition has
derivative `1/c ≠ 0` at `chart(p)`.

The composition theorem then chains through zz341 to give
`MeroSinglePoleExtendsToDeg1Map X` unconditionally on the named
universal-regularity hypothesis. Combined with zz337's
`riemannRochGenusZero_of_inputs`, this gives a closed-form route to
`RiemannRochGenusZero X`: just the two named classical inputs
`ExistsMeroSimplePole_GenusZero X` (Riemann-Roch + Serre duality at
genus 0) and `UniformSimplePoleRegularity X` (analytic local form
at a simple pole).

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Set OnePoint

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Named classical hypothesis: universal regularity of simple poles.**
For every `f : MeromorphicNonzero X` with a single simple pole at some
point `p`, the chart-pullback derivative of `f.toRiemannSphere` at `p`
(with the south chart of `RiemannSphere` as the target chart) is
non-zero.

This is the Forster §1.4 local-form statement: near a simple pole the
reciprocal extends analytically with non-vanishing derivative, which
is what the chart-pullback derivative literally is. -/
def UniformSimplePoleRegularity : Prop :=
  ∀ (f : MeromorphicNonzero X) (p : X),
    mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p = ((-1 : ℤ) : WithTop ℤ) →
    (∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) →
    JacobianChallenge.MeromorphicNonzero.ChartPullback_Deriv_AtSimplePole_NeZero f p

/-- **Closure of `MeroSinglePoleExtendsToDeg1Map X` conditional on
`UniformSimplePoleRegularity X`.** -/
theorem meroSinglePoleExtendsToDeg1Map_of_uniformSimplePoleRegularity
    (h_reg : UniformSimplePoleRegularity X) :
    MeroSinglePoleExtendsToDeg1Map X := by
  intro p f h_pole h_holo _h_nonconst
  exact MeromorphicNonzero.meroSinglePoleExtendsToDeg1Map_witness_of_single_simple_pole
    f h_pole h_holo (h_reg f p h_pole h_holo)

/-- **`RiemannRochGenusZero X` from the two named classical inputs.**
This is the maximally-compressed closure chain after zz337–zz341: two
named classical hypotheses suffice to discharge
`RiemannRochGenusZero X`. -/
theorem riemannRochGenusZero_of_existence_and_uniformRegularity
    (h_exists : ExistsMeroSimplePole_GenusZero X)
    (h_reg : UniformSimplePoleRegularity X) :
    RiemannRochGenusZero X :=
  riemannRochGenusZero_of_inputs X h_exists
    (meroSinglePoleExtendsToDeg1Map_of_uniformSimplePoleRegularity X h_reg)

end JacobianChallenge

end
