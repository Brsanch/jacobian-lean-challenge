/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneForm
import JacobianChallenge.Manifold.RiemannSphereGenus
import JacobianChallenge.Topology.S2ImpliesGenus0Discharge
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option diagnostics.threshold 100

/-! # Linear-algebraic packaging of `HolomorphicOneForm` and `genus`

Glue lemmas turning the `Module.finrank ℂ (HolomorphicOneForm X)`
definition of `genus` into a tool fit for the item-14 chain:

* `Subsingleton (HolomorphicOneForm X) ↔ ∀ α, α = 0`
  (`DFunLike`-extensionality + `ContMDiffSection.coe_zero`).
* `Subsingleton → genus = 0` (wrapper around
  `Module.finrank_zero_of_subsingleton`).
* `genus = 0 → Subsingleton` under `[FiniteDimensional ℂ
  (HolomorphicOneForm X)]` (via `finrank_zero_iff_forall_zero`).
* `genus_le` under an injective `ℂ`-linear map of 1-form spaces.
* `Subsingleton` transfer along a linear injection, plus the
  `genus = 0` corollary.
* The Riemann-sphere specialisation
  `genus_eq_zero_of_injective_into_RiemannSphere`.
* `HolomorphicOneFormInjectsIntoRiemannSphere`: a one-sided variant
  (linear injection rather than `≃ₗ[ℂ]`) of the
  `HolomorphicOneFormEquivRiemannSphere` hypothesis from
  `S2ImpliesGenus0Discharge`, plus the conversion in the easy direction
  and the resulting `genus X = 0` discharge.

**Not** done in this file: the
`Subsingleton (HolomorphicOneForm RiemannSphere)` instance — the
chart-coefficient extraction chase explicitly named as "still owed" in
`RiemannSphereGenus.lean`.

No `sorry`, no `axiom`, no new bundles, no signature changes.
-/

open scoped Manifold ContDiff Topology Bundle

noncomputable section

namespace HolomorphicOneForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Restatement using the `HolomorphicOneForm`-internal `0`: a holomorphic-
1-form space is a subsingleton iff every form equals the zero form. -/
theorem subsingleton_iff_forall_eq_zero :
    Subsingleton (HolomorphicOneForm X)
      ↔ ∀ α : HolomorphicOneForm X, α = (0 : HolomorphicOneForm X) := by
  refine ⟨fun h α => Subsingleton.elim _ _, fun h => ⟨fun α β => ?_⟩⟩
  rw [h α, h β]

end HolomorphicOneForm

/-! ### `Subsingleton` / `genus = 0` -/

section GenusSubsingleton

variable (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Forward direction.** If `HolomorphicOneForm X` is a subsingleton,
then `genus X = 0`. Wraps `Module.finrank_zero_of_subsingleton`. -/
theorem genus_eq_zero_of_holomorphicOneForm_subsingleton
    (h : Subsingleton (HolomorphicOneForm X)) :
    JacobianChallenge.genus X = 0 := by
  unfold JacobianChallenge.genus
  haveI := h
  exact Module.finrank_zero_of_subsingleton

/-- **Reverse direction under finite-dimensionality.** If
`HolomorphicOneForm X` is finite-dimensional over `ℂ` and `genus X = 0`,
then `HolomorphicOneForm X` is a subsingleton. Uses
`finrank_zero_iff_forall_zero`. -/
theorem holomorphicOneForm_subsingleton_of_genus_eq_zero
    [FiniteDimensional ℂ (HolomorphicOneForm X)]
    (h : JacobianChallenge.genus X = 0) :
    Subsingleton (HolomorphicOneForm X) := by
  have hzero : ∀ α : HolomorphicOneForm X, α = 0 :=
    (finrank_zero_iff_forall_zero (K := ℂ) (V := HolomorphicOneForm X)).mp h
  exact HolomorphicOneForm.subsingleton_iff_forall_eq_zero.mpr hzero

/-- **Equivalence (under finite-dimensionality).** Over `ℂ`, if
`HolomorphicOneForm X` is finite-dimensional then `genus X = 0` iff
`HolomorphicOneForm X` is a subsingleton. -/
theorem genus_eq_zero_iff_holomorphicOneForm_subsingleton
    [FiniteDimensional ℂ (HolomorphicOneForm X)] :
    JacobianChallenge.genus X = 0 ↔ Subsingleton (HolomorphicOneForm X) := by
  refine ⟨fun h => holomorphicOneForm_subsingleton_of_genus_eq_zero X h, ?_⟩
  intro h
  exact genus_eq_zero_of_holomorphicOneForm_subsingleton X h

/-- Pointwise version: under finite-dimensionality, the genus is zero iff
every form is the zero form. -/
theorem genus_eq_zero_iff_forall_holomorphicOneForm_eq_zero
    [FiniteDimensional ℂ (HolomorphicOneForm X)] :
    JacobianChallenge.genus X = 0
      ↔ ∀ α : HolomorphicOneForm X, α = (0 : HolomorphicOneForm X) := by
  rw [genus_eq_zero_iff_holomorphicOneForm_subsingleton]
  exact HolomorphicOneForm.subsingleton_iff_forall_eq_zero

end GenusSubsingleton

/-! ### Transfer along `ℂ`-linear maps -/

section TransferAlongLinearMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **Genus bound under an injective linear map.** A `ℂ`-linear injection
`HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm Y` with `Y` of finite
holomorphic-1-form dimension gives `genus X ≤ genus Y`. Wraps
`LinearMap.finrank_le_finrank_of_injective`. -/
theorem genus_le_of_holomorphicOneForm_injective
    [FiniteDimensional ℂ (HolomorphicOneForm Y)]
    (f : HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm Y)
    (hf : Function.Injective f) :
    JacobianChallenge.genus X ≤ JacobianChallenge.genus Y := by
  unfold JacobianChallenge.genus
  exact f.finrank_le_finrank_of_injective hf

/-- **Subsingleton transfer.** A `ℂ`-linear injection from
`HolomorphicOneForm X` into a subsingleton holomorphic-1-form space
forces `HolomorphicOneForm X` itself to be a subsingleton. -/
theorem holomorphicOneForm_subsingleton_of_injective_into_subsingleton
    [Subsingleton (HolomorphicOneForm Y)]
    (f : HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm Y)
    (hf : Function.Injective f) :
    Subsingleton (HolomorphicOneForm X) := by
  refine ⟨fun α β => hf ?_⟩
  exact Subsingleton.elim _ _

/-- **Genus = 0 transfer.** A `ℂ`-linear injection from
`HolomorphicOneForm X` into a subsingleton holomorphic-1-form space
forces `genus X = 0`. -/
theorem genus_eq_zero_of_holomorphicOneForm_injective_into_subsingleton
    [Subsingleton (HolomorphicOneForm Y)]
    (f : HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm Y)
    (hf : Function.Injective f) :
    JacobianChallenge.genus X = 0 :=
  genus_eq_zero_of_holomorphicOneForm_subsingleton X
    (holomorphicOneForm_subsingleton_of_injective_into_subsingleton f hf)

/-- **Riemann-sphere specialisation.** If
`HolomorphicOneForm RiemannSphere` is a subsingleton, then a `ℂ`-linear
injection of `HolomorphicOneForm X` into it suffices for `genus X = 0`.

Compared with `S2ImpliesGenus0Discharge.s2ImpliesGenus0_of_linearEquiv`,
this version weakens the hypothesis from `≃ₗ[ℂ]` to `→ₗ[ℂ] + Injective`,
which matches how a biholomorphism's pullback would actually be obtained
in the wired-up proof (one-sided injectivity is easier than constructing
the full inverse). -/
theorem genus_eq_zero_of_injective_into_RiemannSphere
    [Subsingleton (HolomorphicOneForm JacobianChallenge.RiemannSphere)]
    (f : HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm JacobianChallenge.RiemannSphere)
    (hf : Function.Injective f) :
    JacobianChallenge.genus X = 0 :=
  genus_eq_zero_of_holomorphicOneForm_injective_into_subsingleton f hf

end TransferAlongLinearMap

/-! ### One-sided variant of the Riemann-sphere bridge hypothesis -/

namespace JacobianChallenge

/-- **Open hypothesis (one-sided variant).** A `ℂ`-linear injection — not
necessarily an equivalence — of `HolomorphicOneForm X` into
`HolomorphicOneForm RiemannSphere`.

Compare with `HolomorphicOneFormEquivRiemannSphere`
(`Topology/S2ImpliesGenus0Discharge.lean`), which uses `≃ₗ[ℂ]`. The
one-sided version is the minimal data needed to push `genus X = 0`
through once `Subsingleton (HolomorphicOneForm RiemannSphere)` is
supplied. -/
def HolomorphicOneFormInjectsIntoRiemannSphere
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Prop :=
  Nonempty
    { f : HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm JacobianChallenge.RiemannSphere //
        Function.Injective f }

/-- From a `≃ₗ[ℂ]` between holomorphic-1-form spaces (the `Equiv`
hypothesis in `S2ImpliesGenus0Discharge.lean`) one immediately recovers
the one-sided injection hypothesis. -/
theorem holomorphicOneFormInjectsIntoRiemannSphere_of_equiv
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    (h : HolomorphicOneFormEquivRiemannSphere X) :
    HolomorphicOneFormInjectsIntoRiemannSphere X := by
  obtain ⟨e⟩ := h
  exact ⟨⟨e.toLinearMap, e.injective⟩⟩

/-- **Discharge of `genus X = 0`** from the one-sided injection
hypothesis plus the open subsingleton statement for the Riemann sphere.
No `sorry`, no axiom. -/
theorem genus_eq_zero_of_injects_into_RiemannSphere
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    (hInj : HolomorphicOneFormInjectsIntoRiemannSphere X)
    (hSS : RiemannSphere.HolomorphicOneForm_RiemannSphere_subsingleton_statement) :
    JacobianChallenge.genus X = 0 := by
  obtain ⟨⟨f, hf⟩⟩ := hInj
  haveI : Subsingleton (HolomorphicOneForm JacobianChallenge.RiemannSphere) := hSS
  exact genus_eq_zero_of_injective_into_RiemannSphere f hf

end JacobianChallenge

end
