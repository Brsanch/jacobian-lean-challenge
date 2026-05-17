/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.JacobianAnalyticPerCurveBundle
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackMatrix

set_option linter.unusedSectionVars false

/-! # `JacobianAnalyticPushforwardLift` from a curve map + lattice match

Convenience constructor that takes a smooth curve map `f : X → Y`, the
chosen bases `αX, αY`, and a *lattice-match certificate*, and produces
the per-curve pushforward lift bundle with `T := pushforwardLinearLift αX αY f hf`.

The pre-built `pushforwardLinearLift` is the canonical CLM lift derived
from the basis matrix of the pullback `f^* : HolomorphicOneForm Y → HolomorphicOneForm X`.
The lattice-match certificate is the genuinely-new analytic content:
it asserts that for every X-period vector `v ∈ data_X.lattice`,
`T v` (the period vector of `f_*γ` for `γ` with period `v`) lies in
`data_Y.lattice`. Classically this follows from the adjunction
`∫_{f_*γ} αY = ∫_γ f^* αY`, which requires period-pairing integration
infrastructure not yet built at the pin.

Once supplied, the bundle's `toQuotientMap_contMDiff` discharges item
18 at the AnalyticJacobian level (sister chip
`JacobianAnalyticBasicLeanReduction.lean`).

Pullback direction mirrors with the obvious swap.
-/

open scoped ContDiff Manifold
open Submodule Module

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **Convenience constructor for `JacobianAnalyticPushforwardLift`** from a
curve map + bases + lattice-match certificate. -/
noncomputable def JacobianAnalyticPushforwardLift.ofCurveMap
    (data_X : PeriodLatticeOfRankTwoG X)
    (data_Y : PeriodLatticeOfRankTwoG Y)
    [DiscreteTopology data_X.lattice.toIntSubmodule]
    [IsZLattice ℝ data_X.lattice.toIntSubmodule]
    [DiscreteTopology data_Y.lattice.toIntSubmodule]
    [IsZLattice ℝ data_Y.lattice.toIntSubmodule]
    (αX : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (αY : Basis (Fin (JacobianChallenge.genus Y)) ℂ (HolomorphicOneForm Y))
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (lattice_match : ∀ x ∈ data_X.lattice.toIntSubmodule,
      HolomorphicOneForm.pushforwardLinearLift αX αY f hf x
        ∈ data_Y.lattice.toIntSubmodule) :
    JacobianAnalyticPushforwardLift data_X data_Y where
  f := f
  contMDiff_f := hf
  T := HolomorphicOneForm.pushforwardLinearLift αX αY f hf
  lattice_match := lattice_match

/-- **Convenience constructor for `JacobianAnalyticPullbackLift`** from a
curve map + lattice-match certificate.

The pullback transform `T : ℂ^{gY} →L[ℂ] ℂ^{gX}` is taken as an explicit
argument (the natural construction is the matrix of
`pullbackLinearMap f hf` itself, but downstream callers may prefer a
different equivalent form; we leave the choice open). -/
noncomputable def JacobianAnalyticPullbackLift.ofCurveMap
    (data_X : PeriodLatticeOfRankTwoG X)
    (data_Y : PeriodLatticeOfRankTwoG Y)
    [DiscreteTopology data_X.lattice.toIntSubmodule]
    [IsZLattice ℝ data_X.lattice.toIntSubmodule]
    [DiscreteTopology data_Y.lattice.toIntSubmodule]
    [IsZLattice ℝ data_Y.lattice.toIntSubmodule]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (T : (Fin (JacobianChallenge.genus Y) → ℂ) →L[ℂ]
          (Fin (JacobianChallenge.genus X) → ℂ))
    (lattice_match : ∀ x ∈ data_Y.lattice.toIntSubmodule,
      T x ∈ data_X.lattice.toIntSubmodule) :
    JacobianAnalyticPullbackLift data_X data_Y where
  f := f
  contMDiff_f := hf
  T := T
  lattice_match := lattice_match

end JacobianChallenge

end
