/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothHomologyDataPackageFromHodgeChain
import JacobianChallenge.Manifold.CompleteHodgeRiemannViaStandardForm

set_option linter.unusedSectionVars false

/-! # `SmoothHomologyDataPackage` from via-standard-form Hodge chain (chip 14)

Ergonomic constructor that takes the simplified
`CompleteHodgeRiemannHypothesisViaStandardForm` (chip 11) instead of the
full `CompleteHodgeRiemannHypothesis`. The PD atom and the Hodge form
choice are absorbed by the standard form; the user supplies only
`(J, first relation, bridge identity)`.

Composes chip 11's `completeHodgeRiemannHypothesis_of_viaStandardForm`
with chip 4's `SmoothHomologyDataPackage.ofHodgeChain`.

## What this file ships

* `SmoothHomologyDataPackage.ofHodgeChainViaStandardForm` — constructor.
* `nonempty_smoothHomologyDataPackage_of_hodgeChainViaStandardForm` —
  `Nonempty` corollary.
* `nonempty_periodLatticeSymplecticBundle_of_hodgeChainViaStandardForm` —
  full headline composite.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`SmoothHomologyDataPackage.ofHodgeChainViaStandardForm`** — ergonomic
constructor: takes the via-standard-form Hodge chain hypothesis directly. -/
noncomputable def SmoothHomologyDataPackage.ofHodgeChainViaStandardForm
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    (basePoint : X)
    (symplecticBasis :
      SmoothSymplecticBasis 𝓘(ℝ, ℂ) X basePoint (JacobianChallenge.genus X))
    (hurewicz : SmoothHurewiczHypothesis symplecticBasis)
    (hHRStd : CompleteHodgeRiemannHypothesisViaStandardForm
      (PeriodPairingData.ofSmoothCycle X) basis_ω symplecticBasis.cycleGens) :
    SmoothHomologyDataPackage basis_ω :=
  SmoothHomologyDataPackage.ofHodgeChain basePoint symplecticBasis hurewicz
    (completeHodgeRiemannHypothesis_of_viaStandardForm hHRStd)

/-- **`Nonempty` corollary.** -/
theorem nonempty_smoothHomologyDataPackage_of_hodgeChainViaStandardForm
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    (basePoint : X)
    (symplecticBasis :
      SmoothSymplecticBasis 𝓘(ℝ, ℂ) X basePoint (JacobianChallenge.genus X))
    (hurewicz : SmoothHurewiczHypothesis symplecticBasis)
    (hHRStd : CompleteHodgeRiemannHypothesisViaStandardForm
      (PeriodPairingData.ofSmoothCycle X) basis_ω symplecticBasis.cycleGens) :
    Nonempty (SmoothHomologyDataPackage basis_ω) :=
  ⟨SmoothHomologyDataPackage.ofHodgeChainViaStandardForm basePoint
    symplecticBasis hurewicz hHRStd⟩

/-- **Full headline composite.** -/
theorem nonempty_periodLatticeSymplecticBundle_of_hodgeChainViaStandardForm
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    (basePoint : X)
    (symplecticBasis :
      SmoothSymplecticBasis 𝓘(ℝ, ℂ) X basePoint (JacobianChallenge.genus X))
    (hurewicz : SmoothHurewiczHypothesis symplecticBasis)
    (hHRStd : CompleteHodgeRiemannHypothesisViaStandardForm
      (PeriodPairingData.ofSmoothCycle X) basis_ω symplecticBasis.cycleGens) :
    Nonempty
      (PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X)
        basis_ω) :=
  nonempty_periodLatticeSymplecticBundle_of_smoothHomologyDataPackage
    (SmoothHomologyDataPackage.ofHodgeChainViaStandardForm basePoint
      symplecticBasis hurewicz hHRStd)

end JacobianChallenge

end
