/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothOneForm
import Mathlib.Geometry.Manifold.MFDeriv.Basic

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Pointwise cotangent pullback via a smooth map

For a smooth map `g : Y → X` between real C^∞ manifolds (modelled on
`(E, H)` and `(E', H')` over `ℝ`), a smooth 1-form `om : SmoothOneForm I X`
on `X`, and a point `y : Y` at which `g` is `ContMDiffAt`, the
**pointwise pullback** of `ω` at `y` is the cotangent vector

  `(g^* ω)(y) := ω(g y) ∘L (mfderiv g y) : CotangentSpace I' y`.

This file ships:

* `cotangentPullbackAt` — the definition.
* `cotangentPullbackAt_add` / `cotangentPullbackAt_smul` — ℝ-linearity
  of the pullback in the 1-form argument.
* `cotangentPullbackAt_zero` — zero 1-form pulls back to zero.

These are the foundational pointwise primitives for the trace
construction `f_*ω` on regular values of a meromorphic function. The
trace at a regular value `y` will be a `Finset`-sum of pullbacks
through each local-inverse sheet over the fiber.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff Topology

namespace JacobianChallenge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ⊤ Y]

/-- **Pointwise cotangent pullback.** For a smooth map `g : Y → X`,
a smooth 1-form `om : SmoothOneForm I X`, and a point `y : Y`,
`cotangentPullbackAt g y ω : CotangentSpace I' y` is the cotangent
vector `(om (g y)) ∘L (mfderiv g y)`. -/
noncomputable def cotangentPullbackAt
    (g : Y → X) (y : Y) (om : SmoothOneForm I X) :
    CotangentSpace I' y :=
  (om (g y)).comp (mfderiv I' I g y)

/-! ## Linearity in the 1-form -/

@[simp] lemma cotangentPullbackAt_zero (g : Y → X) (y : Y) :
    cotangentPullbackAt (I := I) (I' := I') g y (0 : SmoothOneForm I X) = 0 := by
  unfold cotangentPullbackAt
  show ((0 : SmoothOneForm I X) (g y)).comp _ = 0
  -- SmoothOneForm has AddCommGroup; 0 applied gives 0 in CotangentSpace.
  have h_zero : ((0 : SmoothOneForm I X) (g y) : E →L[ℝ] ℝ) = 0 := rfl
  rw [h_zero]
  exact ContinuousLinearMap.zero_comp _

@[simp] lemma cotangentPullbackAt_add (g : Y → X) (y : Y)
    (om₁ om₂ : SmoothOneForm I X) :
    cotangentPullbackAt (I := I) (I' := I') g y (om₁ + om₂)
      = cotangentPullbackAt (I := I) (I' := I') g y om₁
        + cotangentPullbackAt (I := I) (I' := I') g y om₂ := by
  unfold cotangentPullbackAt
  show ((om₁ + om₂) (g y)).comp _ = (om₁ (g y)).comp _ + (om₂ (g y)).comp _
  have h_add : ((om₁ + om₂) (g y) : E →L[ℝ] ℝ)
      = om₁ (g y) + om₂ (g y) := rfl
  rw [h_add]
  exact ContinuousLinearMap.add_comp _ _ _

@[simp] lemma cotangentPullbackAt_smul (g : Y → X) (y : Y)
    (c : ℝ) (om : SmoothOneForm I X) :
    cotangentPullbackAt (I := I) (I' := I') g y (c • om)
      = c • cotangentPullbackAt (I := I) (I' := I') g y om := by
  unfold cotangentPullbackAt
  show ((c • om) (g y)).comp _ = c • (om (g y)).comp _
  have h_smul : ((c • om) (g y) : E →L[ℝ] ℝ) = c • (om (g y)) := rfl
  rw [h_smul]
  exact ContinuousLinearMap.smul_comp _ _ _

end JacobianChallenge

end
