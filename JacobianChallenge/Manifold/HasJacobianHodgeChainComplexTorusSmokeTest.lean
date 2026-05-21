/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianHodgeChainComplexTorusUnconditional
import JacobianChallenge.Manifold.CanonicalAnalyticJacobianComplexTorusSmokeTest

set_option linter.unusedSectionVars false

/-! # T_L smoke tests for the chip 19r `HasJacobianHodgeChain` instance

Verifies via `inferInstance` that the chip 19r unconditional
instance `instHasJacobianHodgeChain_complexTorus` fires correctly
and composes through the global bridge
`HasJacobianHodgeChain X ⟹ HasJacobianAnalyticStructure X`. All
downstream `CanonicalAnalyticJacobianAnonymous (ℂ ⧸ L)` instances
remain accessible.

The smoke tests are `example` statements with no surface output —
their value is in *compiling*. They serve as regression guards for
the typeclass synthesis chain.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Class-level instance synthesis -/

/-- **Chip 19r instance fires via `inferInstance`.** -/
example : HasJacobianHodgeChain (ℂ ⧸ L) := inferInstance

/-- **The global bridge `HasJacobianHodgeChain X ⟹ HasJacobianAnalyticStructure X`
fires via instance synthesis.** -/
example : HasJacobianAnalyticStructure (ℂ ⧸ L) := inferInstance

/-! ## Downstream canonical-Jacobian instances (re-validating the smoke tests) -/

/-- **Compact space.** -/
example : CompactSpace (CanonicalAnalyticJacobianAnonymous (ℂ ⧸ L)) :=
  inferInstance

/-- **Charted space.** -/
example : ChartedSpace (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ)
    (CanonicalAnalyticJacobianAnonymous (ℂ ⧸ L)) :=
  inferInstance

/-- **`ω`-smooth manifold.** -/
example : @IsManifold ℂ _
    (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) _ _
    (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) _
    (modelWithCornersSelf ℂ
      (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ)) ω
    (CanonicalAnalyticJacobianAnonymous (ℂ ⧸ L)) _ inferInstance :=
  inferInstance

/-- **Lie additive group.** -/
example : @LieAddGroup ℂ _
    (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) _
    (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) _ _
    (modelWithCornersSelf ℂ
      (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ)) ω
    (CanonicalAnalyticJacobianAnonymous (ℂ ⧸ L)) _ _ inferInstance :=
  inferInstance

/-! ## Self-vanishing of `canonicalOfCurve` -/

/-- **`canonicalOfCurve P P = 0` for any `P ∈ T_L`.** -/
example (P : ℂ ⧸ L) :
    canonicalOfCurve P P
      = (0 : CanonicalAnalyticJacobianAnonymous (ℂ ⧸ L)) :=
  canonicalOfCurve_self P

end ComplexTorus

end JacobianChallenge

end
