/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.Pic0HolomorphicEquiv
import JacobianChallenge.Manifold.Pic0EquivComplexTorus

set_option linter.unusedSectionVars false

/-! # `Pic0 X ≃+ ℂ ⧸ L` from a biholomorphism `X ≃ω (ℂ ⧸ L)`

Composes the just-shipped `pic0_holomorphicEquivCongr` (Pic0 transport
along a biholomorphism) with the in-tree
`pic0EquivComplexTorus L h hTL hConverse : Pic0 (ℂ⧸L) ≃+ ℂ⧸L`
(conditional on the two T_L classical hypotheses).

For any `X` biholomorphic to `ℂ⧸L`, this gives the explicit
`Pic0 X ≃+ ℂ⧸L` isomorphism under the same two named hypotheses on L.

## What ships

* `pic0EquivComplexTorus_of_holomorphicEquiv` — the composed AddEquiv.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`Pic0 X ≃+ ℂ ⧸ L` from a biholomorphism `X ≃ω ℂ⧸L`** plus the two
T_L classical hypotheses (Abel + Abel's converse). -/
noncomputable def pic0EquivComplexTorus_of_holomorphicEquiv
    (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]
    (e : HolomorphicEquiv X (ℂ ⧸ L))
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (ComplexTorus.basis_g_dz L))
    (hTL : ComplexTorus.TLDivSumHypothesis L)
    (hConverse : ComplexTorus.TLAbelConverseHypothesis L) :
    Pic0 X ≃+ (ℂ ⧸ L) :=
  (pic0_holomorphicEquivCongr e).trans
    (ComplexTorus.pic0EquivComplexTorus L h hTL hConverse)

end JacobianChallenge

end
