/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RegularValueWitnessAtInfty
import JacobianChallenge.Manifold.DegreeWellDefined
import JacobianChallenge.Manifold.MeromorphicExtension

set_option diagnostics.threshold 100

/-! # `degreeFiber f.toRiemannSphere = 1` under one simple pole + regularity

Composition chip: given the (named) regularity hypothesis
`ChartPullback_Deriv_AtSimplePole_NeZero f p` from zz340, this chip
chains zz339's non-constancy + zz340's `RegularValueWitnessReg` with
card = 1 through the unconditional `degreeFiber_eq_card_of_regular_witness`
(`DegreeWellDefined.lean`) to land

  `degreeFiber f.toRiemannSphere f.toRiemannSphere_contMDiff = 1`.

This closes the *degree-1 leg* of the analytic-bridge stack named in
zz337's `MeroSinglePoleExtendsToDeg1Map` conditional on the named
regularity hypothesis. Combined with the (open) discharge of
`ChartPullback_Deriv_AtSimplePole_NeZero` it gives unconditional
`MeroSinglePoleExtendsToDeg1Map`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Set OnePoint

namespace JacobianChallenge

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace MeromorphicNonzero

/-- **`degreeFiber f.toRiemannSphere = 1`** under one simple pole at `p`
+ the named regularity certificate at `p`.

Mechanical composition:
* `f.toRiemannSphere_contMDiff` (unconditional) provides the smoothness
  needed by `degreeFiber`.
* zz339's `toRiemannSphere_not_isConstantMap_of_single_simple_pole`
  rules out the constant branch.
* zz340's `regularValueWitnessReg_at_infty_of_single_simple_pole` builds
  a `RegularValueWitnessReg f.toRiemannSphere` (conditional on the
  named regularity hypothesis).
* `degreeFiber_eq_card_of_regular_witness` (from
  `DegreeWellDefined.lean`) equates `degreeFiber` with that witness's
  `card`.
* zz340's `regularValueWitnessReg_at_infty_card_eq_one` gives card = 1. -/
theorem degreeFiber_toRiemannSphere_eq_one_of_single_simple_pole
    (f : MeromorphicNonzero X) {p : X}
    (h_pole : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p = ((-1 : ℤ) : WithTop ℤ))
    (h_holo : ∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x)
    (h_reg_at_p : ChartPullback_Deriv_AtSimplePole_NeZero f p) :
    JacobianChallenge.ContMDiff.degreeFiber f.toRiemannSphere
        f.toRiemannSphere_contMDiff = 1 := by
  -- Non-constancy from zz339.
  have hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere :=
    toRiemannSphere_not_isConstantMap_of_single_simple_pole f h_pole h_holo
  -- Regular witness (with card 1) from zz340.
  set w : JacobianChallenge.ContMDiff.RegularValueWitnessReg f.toRiemannSphere :=
    regularValueWitnessReg_at_infty_of_single_simple_pole f h_pole h_holo h_reg_at_p
    with hw_def
  have hw_card : w.card = 1 :=
    regularValueWitnessReg_at_infty_card_eq_one f h_pole h_holo h_reg_at_p
  -- Apply degreeFiber-eq-card.
  have h_eq :
      JacobianChallenge.ContMDiff.degreeFiber f.toRiemannSphere
          f.toRiemannSphere_contMDiff
        = w.card :=
    JacobianChallenge.degreeFiber_eq_card_of_regular_witness
      (f := f.toRiemannSphere) f.toRiemannSphere_contMDiff hnc w
  rw [h_eq, hw_card]

/-- **Composition of degree-1 + non-constancy** into the existence
form expected by zz337's `MeroSinglePoleExtendsToDeg1Map`. Under the
single-simple-pole hypothesis at `p` and the named regularity
certificate, the pole-extension `f.toRiemannSphere` witnesses the
existence clause of `MeroSinglePoleExtendsToDeg1Map`. -/
theorem meroSinglePoleExtendsToDeg1Map_witness_of_single_simple_pole
    (f : MeromorphicNonzero X) {p : X}
    (h_pole : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p = ((-1 : ℤ) : WithTop ℤ))
    (h_holo : ∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x)
    (h_reg_at_p : ChartPullback_Deriv_AtSimplePole_NeZero f p) :
    ∃ (F : X → JacobianChallenge.RiemannSphere)
      (hF : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F),
      ¬ JacobianChallenge.IsConstantMap F ∧
        JacobianChallenge.ContMDiff.degreeFiber F hF = 1 := by
  refine ⟨f.toRiemannSphere, f.toRiemannSphere_contMDiff, ?_, ?_⟩
  · exact toRiemannSphere_not_isConstantMap_of_single_simple_pole f h_pole h_holo
  · exact degreeFiber_toRiemannSphere_eq_one_of_single_simple_pole
      f h_pole h_holo h_reg_at_p

end MeromorphicNonzero

end JacobianChallenge

end
