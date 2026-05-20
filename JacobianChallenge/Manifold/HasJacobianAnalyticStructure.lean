/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CanonicalAnalyticJacobianFromClass
import JacobianChallenge.Manifold.DefaultHolomorphicOneFormBasis

set_option linter.unusedSectionVars false

/-! # `HasJacobianAnalyticStructure X` — basis-agnostic class wrapper

A class on `X` alone (no `basis_ω` argument) that asserts the existence
of *some* `Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)` together
with a `SmoothHomologyDataPackage` over it. This is the natural form
for typeclass-driven downstream construction of the canonical analytic
Jacobian when the choice of basis is opaque (just an existence
hypothesis).

The X-only class instances cover the same X as
`HasSmoothHomologyDataPackage X basis_ω` for the canonical bases
already constructed (RS, T_L), via existential introduction.

## What this file ships

* `HasJacobianAnalyticStructure X` — basis-agnostic class wrapper.
* `HasJacobianAnalyticStructure.of_hasSmoothHomologyDataPackage` — bridge
  from the per-basis class.
* `instHasJacobianAnalyticStructure_RiemannSphere` — instance on `RS`.
* `instHasJacobianAnalyticStructure_complexTorus` — instance on `T_L`.
* `canonicalBasisFromAnalyticStructure` — Classical.choice of the basis.
* `canonicalSmoothHomologyDataPackageFromAnalyticStructure` —
  Classical.choice of the package.
* `CanonicalAnalyticJacobianAnonymous X` — Type with the seven
  structural instances, basis hidden behind the class.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Basis-agnostic class wrapper.** Asserts the existence of *some*
ℂ-basis `basis_ω` of `HolomorphicOneForm X` together with a non-empty
`SmoothHomologyDataPackage basis_ω`. -/
class HasJacobianAnalyticStructure (X : Type u) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X] : Prop where
  /-- The witness: some basis + non-empty package over it. -/
  out :
    ∃ (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
        (HolomorphicOneForm X)),
      Nonempty (SmoothHomologyDataPackage basis_ω)

/-- **Bridge from the per-basis class to the basis-agnostic class.** Any
`[HasSmoothHomologyDataPackage X basis_ω]` instance produces a
`HasJacobianAnalyticStructure X` instance by existential introduction. -/
theorem HasJacobianAnalyticStructure.of_hasSmoothHomologyDataPackage
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    [HasSmoothHomologyDataPackage (X := X) basis_ω] :
    HasJacobianAnalyticStructure X :=
  ⟨⟨basis_ω, nonempty_smoothHomologyDataPackage_of_class⟩⟩

/-! ## Instance: `RiemannSphere` -/

namespace RiemannSphere

/-- **Unconditional instance for `RiemannSphere`.** Discharges via the
per-basis class instance + existential introduction. The witness basis
is the default one, but any basis would do (genus 0). -/
instance instHasJacobianAnalyticStructure_RiemannSphere :
    HasJacobianAnalyticStructure RiemannSphere :=
  letI := JacobianChallenge.RiemannSphere.instHasSmoothHomologyDataPackage_RiemannSphere
    (defaultHolomorphicOneFormBasis RiemannSphere)
  HasJacobianAnalyticStructure.of_hasSmoothHomologyDataPackage
    (X := RiemannSphere) (defaultHolomorphicOneFormBasis RiemannSphere)

end RiemannSphere

/-! ## Instance: `T_L = ℂ ⧸ L` -/

namespace ComplexTorus

variable (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- **Unconditional instance for the complex torus `T_L`.** Discharges
via the per-basis class instance at `basis_g_dz L` + existential
introduction. -/
instance instHasJacobianAnalyticStructure_complexTorus :
    HasJacobianAnalyticStructure (ℂ ⧸ L) :=
  HasJacobianAnalyticStructure.of_hasSmoothHomologyDataPackage
    (X := ℂ ⧸ L) (JacobianChallenge.ComplexTorus.basis_g_dz L)

end ComplexTorus

/-! ## Canonical basis and package extraction (basis-agnostic) -/

/-- **Canonical basis from `[HasJacobianAnalyticStructure X]`.**
Classical.choice'd once; downstream constructions reference this exact
witness. -/
noncomputable def canonicalBasisFromAnalyticStructure
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    [HasJacobianAnalyticStructure X] :
    Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X) :=
  Classical.choose HasJacobianAnalyticStructure.out

/-- **Canonical package over the canonical basis.** -/
noncomputable def canonicalSmoothHomologyDataPackageFromAnalyticStructure
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    [HasJacobianAnalyticStructure X] :
    SmoothHomologyDataPackage
      (canonicalBasisFromAnalyticStructure X) :=
  Classical.choice
    (Classical.choose_spec HasJacobianAnalyticStructure.out)

/-! ## `HasSmoothHomologyDataPackage` instance over the canonical basis

To bridge `HasJacobianAnalyticStructure X` (basis-agnostic) back to
`HasSmoothHomologyDataPackage X (canonicalBasisFromAnalyticStructure X)`
(per-basis form, parameterised by the canonical basis). This makes the
canonical-basis package available as a typeclass for downstream
consumers (notably `CanonicalAnalyticJacobian`). -/

/-- **Per-basis class instance over the canonical basis.** This is the
inverse direction of `of_hasSmoothHomologyDataPackage`: from
`[HasJacobianAnalyticStructure X]`, the per-basis class fires on the
canonical basis. -/
instance instHasSmoothHomologyDataPackage_canonicalBasis
    [HasJacobianAnalyticStructure X] :
    HasSmoothHomologyDataPackage (X := X)
      (canonicalBasisFromAnalyticStructure X) where
  out := ⟨canonicalSmoothHomologyDataPackageFromAnalyticStructure X⟩

/-! ## The basis-anonymous canonical analytic Jacobian -/

/-- **Canonical analytic Jacobian (basis-anonymous).** Specialises
`CanonicalAnalyticJacobian` to `canonicalBasisFromAnalyticStructure X`,
so the basis argument is no longer exposed at the type level. -/
def CanonicalAnalyticJacobianAnonymous
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    [HasJacobianAnalyticStructure X] : Type :=
  CanonicalAnalyticJacobian (canonicalBasisFromAnalyticStructure X)

namespace CanonicalAnalyticJacobianAnonymous

variable [HasJacobianAnalyticStructure X]

instance instAddCommGroup :
    AddCommGroup (CanonicalAnalyticJacobianAnonymous X) :=
  inferInstanceAs (AddCommGroup
    (CanonicalAnalyticJacobian (canonicalBasisFromAnalyticStructure X)))

instance instTopologicalSpace :
    TopologicalSpace (CanonicalAnalyticJacobianAnonymous X) :=
  inferInstanceAs (TopologicalSpace
    (CanonicalAnalyticJacobian (canonicalBasisFromAnalyticStructure X)))

instance instT2Space :
    T2Space (CanonicalAnalyticJacobianAnonymous X) :=
  inferInstanceAs (T2Space
    (CanonicalAnalyticJacobian (canonicalBasisFromAnalyticStructure X)))

instance instCompactSpace :
    CompactSpace (CanonicalAnalyticJacobianAnonymous X) :=
  inferInstanceAs (CompactSpace
    (CanonicalAnalyticJacobian (canonicalBasisFromAnalyticStructure X)))

instance instChartedSpace :
    ChartedSpace (Fin (JacobianChallenge.genus X) → ℂ)
      (CanonicalAnalyticJacobianAnonymous X) :=
  inferInstanceAs (ChartedSpace (Fin (JacobianChallenge.genus X) → ℂ)
    (CanonicalAnalyticJacobian (canonicalBasisFromAnalyticStructure X)))

instance instIsManifold :
    @IsManifold ℂ _
      (Fin (JacobianChallenge.genus X) → ℂ) _ _
      (Fin (JacobianChallenge.genus X) → ℂ) _
      (modelWithCornersSelf ℂ (Fin (JacobianChallenge.genus X) → ℂ)) ω
      (CanonicalAnalyticJacobianAnonymous X) _ inferInstance :=
  inferInstanceAs (@IsManifold ℂ _
    (Fin (JacobianChallenge.genus X) → ℂ) _ _
    (Fin (JacobianChallenge.genus X) → ℂ) _
    (modelWithCornersSelf ℂ (Fin (JacobianChallenge.genus X) → ℂ)) ω
    (CanonicalAnalyticJacobian (canonicalBasisFromAnalyticStructure X))
    _ inferInstance)

instance instLieAddGroup :
    @LieAddGroup ℂ _
      (Fin (JacobianChallenge.genus X) → ℂ) _
      (Fin (JacobianChallenge.genus X) → ℂ) _ _
      (modelWithCornersSelf ℂ (Fin (JacobianChallenge.genus X) → ℂ)) ω
      (CanonicalAnalyticJacobianAnonymous X) _ _ inferInstance :=
  inferInstanceAs (@LieAddGroup ℂ _
    (Fin (JacobianChallenge.genus X) → ℂ) _
    (Fin (JacobianChallenge.genus X) → ℂ) _ _
    (modelWithCornersSelf ℂ (Fin (JacobianChallenge.genus X) → ℂ)) ω
    (CanonicalAnalyticJacobian (canonicalBasisFromAnalyticStructure X))
    _ _ inferInstance)

end CanonicalAnalyticJacobianAnonymous

end JacobianChallenge

end
