/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneForm
import Mathlib.Geometry.Manifold.MFDeriv.Basic

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Pointwise holomorphic cotangent pullback via a smooth map

Holomorphic-side analogue of `cotangentPullbackAt`
(`Manifold/CotangentPullbackAt.lean`). For a smooth map
`g : Y → X` between complex 1-manifolds, a holomorphic 1-form
`α : HolomorphicOneForm X`, and a point `y : Y`, the **pointwise
holomorphic pullback** of `α` at `y` is the `ℂ`-linear cotangent vector

  `(g^* α)(y) := α(g y) ∘L (mfderiv g y) : CotangentSpace 𝓘(ℂ, ℂ) y`.

This file ships:

* `holCotangentPullbackAt` — the definition (totally analogous to
  `cotangentPullbackAt` but with `𝓘(ℂ, ℂ)` instead of `𝓘(ℝ, ℂ)` and
  taking `α : HolomorphicOneForm X` directly).
* `holCotangentPullbackAt_apply` — unfolding.
* `holCotangentPullbackAt_zero`, `_add`, `_smul` — ℂ-linearity in α.
* `holCotangentPullbackAt_congr_of_eventuallyEq` — germ-determinism in
  `g`. Both `α.toFun (g y)` and `mfderiv g y` depend only on the germ
  of `g` at `y`.

These are the foundational primitives for the holomorphic-side trace
construction `f_*α` (a `HolomorphicOneFormOn RiemannSphere
f.regularValueSet` for `f : MeromorphicNonzero X`), parallel to the
realified construction `cotangentPullbackAt → traceAt → fStarOmega →
fStarOmegaOn`.

The germ-congruence proof reuses `Filter.EventuallyEq.mfderiv_eq` from
mathlib, which is model-generic and applies to the `𝓘(ℂ, ℂ)` bundle
without modification.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff Topology

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-- **Pointwise holomorphic cotangent pullback.** For a smooth map
`g : Y → X` between complex 1-manifolds, a holomorphic 1-form
`α : HolomorphicOneForm X`, and a point `y : Y`,
`holCotangentPullbackAt g y α : CotangentSpace 𝓘(ℂ, ℂ) y` is the
ℂ-linear cotangent vector `(α (g y)) ∘L (mfderiv g y)`. -/
noncomputable def holCotangentPullbackAt
    (g : Y → X) (y : Y) (α : HolomorphicOneForm X) :
    CotangentSpace 𝓘(ℂ, ℂ) y :=
  (α.toFun (g y)).comp (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g y)

/-- Definitional unfolding of `holCotangentPullbackAt`. -/
lemma holCotangentPullbackAt_apply
    (g : Y → X) (y : Y) (α : HolomorphicOneForm X) :
    holCotangentPullbackAt g y α
      = (α.toFun (g y)).comp (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g y) := rfl

/-! ## ℂ-linearity in the 1-form -/

@[simp] lemma holCotangentPullbackAt_zero (g : Y → X) (y : Y) :
    holCotangentPullbackAt g y (0 : HolomorphicOneForm X) = 0 := by
  unfold holCotangentPullbackAt
  show ((0 : HolomorphicOneForm X).toFun (g y)).comp _ = 0
  have h_zero : ((0 : HolomorphicOneForm X).toFun (g y) : ℂ →L[ℂ] ℂ) = 0 := rfl
  rw [h_zero]
  exact ContinuousLinearMap.zero_comp _

@[simp] lemma holCotangentPullbackAt_add (g : Y → X) (y : Y)
    (α₁ α₂ : HolomorphicOneForm X) :
    holCotangentPullbackAt g y (α₁ + α₂)
      = holCotangentPullbackAt g y α₁ + holCotangentPullbackAt g y α₂ := by
  unfold holCotangentPullbackAt
  show ((α₁ + α₂).toFun (g y)).comp _
      = (α₁.toFun (g y)).comp _ + (α₂.toFun (g y)).comp _
  have h_add : ((α₁ + α₂).toFun (g y) : ℂ →L[ℂ] ℂ)
      = α₁.toFun (g y) + α₂.toFun (g y) := rfl
  rw [h_add]
  exact ContinuousLinearMap.add_comp _ _ _

@[simp] lemma holCotangentPullbackAt_smul (g : Y → X) (y : Y)
    (c : ℂ) (α : HolomorphicOneForm X) :
    holCotangentPullbackAt g y (c • α) = c • holCotangentPullbackAt g y α := by
  unfold holCotangentPullbackAt
  show ((c • α).toFun (g y)).comp _ = c • (α.toFun (g y)).comp _
  have h_smul : ((c • α).toFun (g y) : ℂ →L[ℂ] ℂ) = c • α.toFun (g y) := rfl
  rw [h_smul]
  exact ContinuousLinearMap.smul_comp _ _ _

/-! ## Germ congruence in the map `g` -/

/-- **`holCotangentPullbackAt` respects germ-equality of `g`.** If
`g₁ =ᶠ[𝓝 y] g₂`, their holomorphic cotangent pullbacks at `y` coincide.

Both `α.toFun (g y)` (because `g₁ y = g₂ y` from the germ equality)
and `mfderiv g y` (via mathlib's model-generic
`Filter.EventuallyEq.mfderiv_eq`) depend only on the germ of `g`. -/
theorem holCotangentPullbackAt_congr_of_eventuallyEq
    {g₁ g₂ : Y → X} {y : Y} (h : g₁ =ᶠ[𝓝 y] g₂)
    (α : HolomorphicOneForm X) :
    holCotangentPullbackAt g₁ y α = holCotangentPullbackAt g₂ y α := by
  unfold holCotangentPullbackAt
  have h_pt : g₁ y = g₂ y := h.eq_of_nhds
  have h_mfd : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g₁ y
      = mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g₂ y :=
    Filter.EventuallyEq.mfderiv_eq h
  rw [h_pt, h_mfd]

/-- **EqOn-form of the germ-congruence lemma.** -/
theorem holCotangentPullbackAt_congr_of_eqOn_open
    {g₁ g₂ : Y → X} {y : Y} {U : Set Y}
    (h_open : IsOpen U) (h_mem : y ∈ U) (h_eq : Set.EqOn g₁ g₂ U)
    (α : HolomorphicOneForm X) :
    holCotangentPullbackAt g₁ y α = holCotangentPullbackAt g₂ y α :=
  holCotangentPullbackAt_congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (h_open.mem_nhds h_mem) h_eq) α

end JacobianChallenge

end
