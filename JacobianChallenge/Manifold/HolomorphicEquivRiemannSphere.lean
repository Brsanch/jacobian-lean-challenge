/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicEquiv
import JacobianChallenge.Manifold.RiemannSphere
import JacobianChallenge.Topology.SurfaceClassificationGenus
import JacobianChallenge.Topology.Genus0ImpliesS2Reduction

set_option diagnostics.threshold 100

/-! # `HolomorphicEquiv` with the Riemann sphere

zz284 ships `HolomorphicEquiv X Y` as the analytic-Lean-convention
alias for `Diffeomorph 𝓘(ℂ) 𝓘(ℂ) X Y ω`. This file specialises the
API to the `Y = RiemannSphere` (or `X = RiemannSphere`) case and
records:

* `holomorphicEquiv_RiemannSphere_self` — the identity
  `HolomorphicEquiv RiemannSphere RiemannSphere`.
* `homeoStandardS2_of_holomorphicEquiv_RiemannSphere` — composition of
  a biholomorphism `X ≃ RS` with `RiemannSphere.toSphereHomeo` to
  produce `X ≃ₜ StandardS2`. Topological side only — does not require
  pullback-of-1-forms.
* `genus0ImpliesS2_of_nonemptyHolomorphicEquiv_RiemannSphere` —
  `Genus0ImpliesS2 X` from a biholomorphism with the Riemann sphere
  (the genus = 0 hypothesis is unused; the conclusion comes from the
  homeomorphism).

The reverse direction (`S2ImpliesGenus0 X` from
`HolomorphicEquiv X RiemannSphere`) requires the pullback-of-1-forms
construction, which is not in this file. (Once supplied, it would
combine with this file's forward direction to close item 14 for any
`X` biholomorphic to the Riemann sphere.)

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-- The identity biholomorphism on the Riemann sphere. -/
noncomputable def holomorphicEquiv_RiemannSphere_self :
    HolomorphicEquiv JacobianChallenge.RiemannSphere
                     JacobianChallenge.RiemannSphere :=
  HolomorphicEquiv.refl

/-- The corresponding `NonemptyHolomorphicEquiv` witness for the
Riemann sphere reflexivity. -/
theorem nonemptyHolomorphicEquiv_RiemannSphere_self :
    JacobianChallenge.NonemptyHolomorphicEquiv
      JacobianChallenge.RiemannSphere
      JacobianChallenge.RiemannSphere :=
  ⟨holomorphicEquiv_RiemannSphere_self⟩

end RiemannSphere

/-- A biholomorphism `X ≃ RiemannSphere` gives a homeomorphism
`X ≃ₜ StandardS2`. Pure topological composition — does not require
pullback-of-1-forms. -/
noncomputable def homeoStandardS2_of_holomorphicEquiv_RiemannSphere
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere) :
    X ≃ₜ StandardS2 :=
  (HolomorphicEquiv.toHomeomorph e).trans RiemannSphere.toSphereHomeo

/-- A biholomorphism with the Riemann sphere gives `X ≃ₜ StandardS2`
in `Nonempty` form. -/
theorem nonempty_homeo_standardS2_of_holomorphicEquiv_RiemannSphere
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere) :
    Nonempty (X ≃ₜ StandardS2) :=
  ⟨homeoStandardS2_of_holomorphicEquiv_RiemannSphere e⟩

/-- A `NonemptyHolomorphicEquiv X RiemannSphere` witness gives
`Nonempty (X ≃ₜ StandardS2)`. -/
theorem nonempty_homeo_standardS2_of_nonemptyHolomorphicEquiv_RiemannSphere
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h : JacobianChallenge.NonemptyHolomorphicEquiv X
          JacobianChallenge.RiemannSphere) :
    Nonempty (X ≃ₜ StandardS2) := by
  obtain ⟨e⟩ := h
  exact nonempty_homeo_standardS2_of_holomorphicEquiv_RiemannSphere e

variable {X : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **`Genus0ImpliesS2 X` from a biholomorphism with the Riemann sphere.**
The `genus X = 0` hypothesis is unused; the conclusion comes from the
biholomorphism via `homeoStandardS2_of_holomorphicEquiv_RiemannSphere`. -/
theorem genus0ImpliesS2_of_holomorphicEquiv_RiemannSphere
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere) :
    Genus0ImpliesS2 X :=
  fun _ => nonempty_homeo_standardS2_of_holomorphicEquiv_RiemannSphere e

/-- **`Genus0ImpliesS2 X` from `NonemptyHolomorphicEquiv X RiemannSphere`.** -/
theorem genus0ImpliesS2_of_nonemptyHolomorphicEquiv_RiemannSphere
    (h : JacobianChallenge.NonemptyHolomorphicEquiv X
          JacobianChallenge.RiemannSphere) :
    Genus0ImpliesS2 X :=
  fun _ => nonempty_homeo_standardS2_of_nonemptyHolomorphicEquiv_RiemannSphere h

/-! ### `UniformizationGenus0` from `NonemptyHolomorphicEquiv`

The named open hypothesis `UniformizationGenus0 X` from
`Topology/Genus0ImpliesS2Reduction.lean` is exactly
`genus X = 0 → Nonempty (X ≃ₜ RiemannSphere)`. A
`NonemptyHolomorphicEquiv X RiemannSphere` gives this directly, since
a biholomorphism is a homeomorphism. -/

/-- A `NonemptyHolomorphicEquiv X RiemannSphere` discharges
`UniformizationGenus0 X` — the `genus = 0` hypothesis is unused. -/
theorem uniformizationGenus0_of_nonemptyHolomorphicEquiv_RiemannSphere
    (h : JacobianChallenge.NonemptyHolomorphicEquiv X
          JacobianChallenge.RiemannSphere) :
    JacobianChallenge.UniformizationGenus0 X := by
  intro _
  obtain ⟨e⟩ := h
  exact ⟨HolomorphicEquiv.toHomeomorph e⟩

/-- A `HolomorphicEquiv X RiemannSphere` discharges
`UniformizationGenus0 X` directly. -/
theorem uniformizationGenus0_of_holomorphicEquiv_RiemannSphere
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere) :
    JacobianChallenge.UniformizationGenus0 X :=
  uniformizationGenus0_of_nonemptyHolomorphicEquiv_RiemannSphere ⟨e⟩

end JacobianChallenge
