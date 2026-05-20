/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CanonicalOfCurve
import JacobianChallenge.Manifold.HasJacobianAnalyticStructure
import JacobianChallenge.Manifold.AnalyticJacobianSympComplexTorusEquiv

set_option linter.unusedSectionVars false

/-! # End-to-end T_L smoke test for the canonical analytic Jacobian chain

Parallel of `CanonicalAnalyticJacobianRiemannSphereSmokeTest`, but on
the complex torus `T_L = ℂ ⧸ L`. At genus 1, the canonical analytic
Jacobian is non-trivial (a complex 1-torus), so this validates the
plumbing in the genus ≥ 1 setting.

On `T_L = ℂ ⧸ L`:

* `[HasJacobianAnalyticStructure (ℂ ⧸ L)]` is unconditional (from
  the per-basis class instance at `basis_g_dz L` + existential
  introduction).
* `CanonicalAnalyticJacobianAnonymous (ℂ ⧸ L)` has all seven structural
  instances.
* `canonicalOfCurve P Q : CanonicalAnalyticJacobianAnonymous (ℂ ⧸ L)` is
  well-defined for any `P, Q`.
* `canonicalOfCurve P P = 0`.

The smoothness discharge `canonicalOfCurve_contMDiff_of_subsingleton_omega`
does NOT apply on T_L (since `HolomorphicOneForm T_L` is `≃ ℂ`, NOT
subsingleton). T_L smoothness requires the substantive
`AbelJacobiSmoothnessSymp` content (item 17 forward), which is closed
elsewhere via `AbelJacobiSmoothnessComplexTorus`.

This file confirms the genus ≥ 1 chain compiles end-to-end on T_L,
without requiring the smoothness route.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Submodule

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- **End-to-end T_L smoke test (self-vanishing).** -/
example (P : ℂ ⧸ L) :
    canonicalOfCurve P P
      = (0 : CanonicalAnalyticJacobianAnonymous (ℂ ⧸ L)) :=
  canonicalOfCurve_self P

/-- **End-to-end T_L smoke test (compactness of canonical analytic
Jacobian).** -/
example : CompactSpace (CanonicalAnalyticJacobianAnonymous (ℂ ⧸ L)) :=
  inferInstance

/-- **End-to-end T_L smoke test (charted-space structure).** -/
example : ChartedSpace (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ)
    (CanonicalAnalyticJacobianAnonymous (ℂ ⧸ L)) :=
  inferInstance

/-- **End-to-end T_L smoke test (complex-`ω` manifold structure).** -/
example : @IsManifold ℂ _
    (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) _ _
    (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) _
    (modelWithCornersSelf ℂ
      (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ)) ω
    (CanonicalAnalyticJacobianAnonymous (ℂ ⧸ L)) _ inferInstance :=
  inferInstance

/-- **End-to-end T_L smoke test (Lie additive group structure).** -/
example : @LieAddGroup ℂ _
    (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) _
    (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) _ _
    (modelWithCornersSelf ℂ
      (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ)) ω
    (CanonicalAnalyticJacobianAnonymous (ℂ ⧸ L)) _ _ inferInstance :=
  inferInstance

end ComplexTorus

end JacobianChallenge

end
