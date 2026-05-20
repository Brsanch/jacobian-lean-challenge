/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianAnalyticStructure
import JacobianChallenge.Manifold.DiskChartCoverFiniteDim

set_option linter.unusedSectionVars false

/-! # `Subsingleton (CanonicalAnalyticJacobianAnonymous X)` at genus 0

When `[Subsingleton (HolomorphicOneForm X)]` (i.e., `genus X = 0`), the
ambient `Fin (genus X) → ℂ = Fin 0 → ℂ` is a singleton, so the quotient
`CanonicalAnalyticJacobianAnonymous X` is also a singleton.

This is the genus-0 analogue of the structural triviality of the
analytic Jacobian — it reduces to a single point at genus 0.

Combined with the structural instances on
`CanonicalAnalyticJacobianAnonymous`, this gives the trivial-Jacobian
discharge of the analytic-level period-lattice items at genus 0.

## What this file ships

* `subsingleton_finGenusToComplex_of_subsingleton_omega` — auxiliary:
  `Subsingleton (Fin (genus X) → ℂ)` from `Subsingleton (HolomorphicOneForm X)`.
* `Subsingleton (CanonicalAnalyticJacobianAnonymous X)` — under both
  classes, the analytic Jacobian is a singleton.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`Fin (genus X) → ℂ` is subsingleton under `[Subsingleton
(HolomorphicOneForm X)]`.** At subsingleton ω, the genus is 0 (via
`Module.finrank_zero_of_subsingleton` + the unconditional finite-dim
instance), so the ambient `Fin 0 → ℂ` is a singleton. -/
theorem subsingleton_finGenusToComplex_of_subsingleton_omega
    [Subsingleton (HolomorphicOneForm X)] :
    Subsingleton (Fin (JacobianChallenge.genus X) → ℂ) := by
  haveI : FiniteDimensional ℂ (HolomorphicOneForm X) :=
    finiteDimensional_of_HolomorphicOneFormFiniteDim
      (DiskChartCover.holomorphicOneFormFiniteDim_holds (X := X))
  have hrank_zero : JacobianChallenge.genus X = 0 := by
    show Module.finrank ℂ (HolomorphicOneForm X) = 0
    exact Module.finrank_zero_of_subsingleton
  rw [hrank_zero]
  haveI : Unique (Fin 0 → ℂ) := Pi.uniqueOfIsEmpty _
  infer_instance

set_option maxHeartbeats 1600000 in
/-- **`Subsingleton (JacobianOfLattice X data)` from a subsingleton
ambient.** Auxiliary: any `JacobianOfLattice X data` with subsingleton
`Fin (genus X) → ℂ` is itself subsingleton. Direct construction via
surjectivity of the quotient map. -/
theorem subsingleton_jacobianOfLattice_of_subsingleton_ambient
    [hsub : Subsingleton (Fin (JacobianChallenge.genus X) → ℂ)]
    (data : PeriodLatticeOfRankTwoG X) :
    Subsingleton (JacobianOfLattice X data) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Subsingleton.elim a b]

/-- **`Subsingleton (CanonicalAnalyticJacobianAnonymous X)` at genus 0.**
Under both `[HasJacobianAnalyticStructure X]` (which gives the analytic
Jacobian Type) and `[Subsingleton (HolomorphicOneForm X)]` (which makes
the ambient `Fin 0 → ℂ` a singleton), the analytic Jacobian is a
singleton. -/
instance subsingleton_canonicalAnalyticJacobianAnonymous_of_subsingleton_omega
    [HasJacobianAnalyticStructure X]
    [Subsingleton (HolomorphicOneForm X)] :
    Subsingleton (CanonicalAnalyticJacobianAnonymous X) := by
  haveI := subsingleton_finGenusToComplex_of_subsingleton_omega (X := X)
  exact subsingleton_jacobianOfLattice_of_subsingleton_ambient
    (canonicalPeriodLatticeOfRankTwoG (canonicalBasisFromAnalyticStructure X))

end JacobianChallenge

end
