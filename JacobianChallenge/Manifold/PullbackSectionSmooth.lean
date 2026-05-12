/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicEquiv
import JacobianChallenge.Manifold.HolomorphicOneForm
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackPointwise
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackSmoothness
import JacobianChallenge.Manifold.HolomorphicOneFormLinear
import JacobianChallenge.Manifold.HolomorphicEquivPullbackObligationAnalysis
import JacobianChallenge.Manifold.HolomorphicEquivSubsingletonTransfer

set_option diagnostics.threshold 100

/-! # Pullback-obligation ↔ genus-zero (under FiniteDimensional)

Under `[FiniteDimensional ℂ (HolomorphicOneForm X)]`, the named
smoothness obligation
`IsHolomorphicOneFormPullback_for_all (e.symm : HolomorphicEquiv RS X)`
is equivalent to `JacobianChallenge.genus X = 0`.

For a compact connected Riemann surface, `FiniteDimensional ℂ
(HolomorphicOneForm X)` is the Hodge finite-dim input, which is a
separate open hypothesis. Once supplied, the smoothness obligation
collapses to the genus-zero conclusion, and either side is a
satisfactory discharge of item 14 reverse.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **Biconditional under finite-dimensionality.** Under the Hodge
finite-dim hypothesis, the pullback obligation is equivalent to
`genus X = 0`. -/
theorem pullback_obligation_iff_genus_zero
    [FiniteDimensional ℂ (HolomorphicOneForm X)]
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere) :
    IsHolomorphicOneFormPullback_for_all e.symm
      ↔ JacobianChallenge.genus X = 0 := by
  refine ⟨fun hOblig => ?_, fun hgen => ?_⟩
  · exact JacobianChallenge.genus_eq_zero_of_holomorphicEquiv_RiemannSphere
      e hOblig
  · -- From `genus X = 0` + FiniteDim, `HolomorphicOneForm X` is
    -- subsingleton (zz288's content). Then the obligation follows from
    -- the subsingleton via zz296.
    haveI : Subsingleton (HolomorphicOneForm X) :=
      holomorphicOneForm_subsingleton_of_genus_eq_zero X hgen
    exact (subsingleton_iff_pullback_obligation e).mp inferInstance

/-- **Genus consequence (under FiniteDim).** Under FiniteDim, `genus X
= 0` iff the named obligation holds. -/
theorem genus_zero_iff_pullback_obligation
    [FiniteDimensional ℂ (HolomorphicOneForm X)]
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere) :
    JacobianChallenge.genus X = 0
      ↔ IsHolomorphicOneFormPullback_for_all e.symm :=
  (pullback_obligation_iff_genus_zero e).symm

end JacobianChallenge

end
