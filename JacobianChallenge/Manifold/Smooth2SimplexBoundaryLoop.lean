/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2Simplex
import JacobianChallenge.Manifold.SmoothPathConcat
import JacobianChallenge.Manifold.SmoothPathReverse
import JacobianChallenge.Manifold.SmoothPathIntegrateConcat
import JacobianChallenge.Manifold.SmoothPathIntegrateReverse
import JacobianChallenge.Manifold.SmoothChainIntegralLinearity

set_option linter.unusedSectionVars false

/-! # Boundary loop of a smooth 2-simplex

Given a smooth 2-simplex `σ : Smooth2Simplex I X`, its three faces form
a closed loop: `face2 ⋆ face0 ⋆ face1.reverse` traces the boundary
`v₀ → v₁ → v₂ → v₀`. This file constructs that loop and shows its
integral against any smooth 1-form equals the boundary chain integral
`∫_{∂σ} ω`.

This is the structural prerequisite for reducing
`HolomorphicStokesHypothesis X` to a CLOSED-LOOP hypothesis (every
smooth closed loop bounding a 2-simplex has zero integral against
closed real 1-forms). Combined with Cauchy's theorem (mathlib has it
on disks via `DifferentiableOn.isExactOn_ball`), this enables the
discharge of `HolomorphicCanonicalClosed X` for the chart-contained
case.

## What this file ships

* `Smooth2Simplex.boundaryLoop σ : SmoothPath I X` — the concatenated
  loop `face2 ⋆ face0 ⋆ face1.reverse`.
* `Smooth2Simplex.boundaryLoop_src`, `_tgt` — both endpoints equal `σ(v0)`.
* `Smooth2Simplex.boundaryLoop_integrate_eq` —
  `boundaryLoop.integrate ω = SmoothChain.integrate (∂σ) ω`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace Smooth2Simplex

/-! ## Endpoint compatibility for face concatenation -/

lemma face2_tgt_eq_face0_src (σ : Smooth2Simplex I X) :
    (face2 σ).tgt = (face0 σ).src := by
  show σ.toFun Smooth2Simplex.v1 = σ.toFun Smooth2Simplex.v1
  rfl

lemma face0_tgt_eq_face1_reverse_src (σ : Smooth2Simplex I X) :
    (face0 σ).tgt = (face1 σ).reverse.src := by
  show σ.toFun Smooth2Simplex.v2 = σ.toFun Smooth2Simplex.v2
  rfl

/-! ## The boundary loop -/

/-- The closed boundary loop of a smooth 2-simplex:
`face2 ⋆ face0 ⋆ face1.reverse` traces `v₀ → v₁ → v₂ → v₀`. -/
noncomputable def boundaryLoop (σ : Smooth2Simplex I X) : SmoothPath I X :=
  ((face2 σ).concat (face0 σ) (face2_tgt_eq_face0_src σ)).concat
    (face1 σ).reverse
    (by
      rw [SmoothPath.concat_tgt]
      exact face0_tgt_eq_face1_reverse_src σ)

@[simp] lemma boundaryLoop_src (σ : Smooth2Simplex I X) :
    (boundaryLoop σ).src = σ.toFun Smooth2Simplex.v0 := by
  unfold boundaryLoop
  rw [SmoothPath.concat_src, SmoothPath.concat_src]
  rfl

@[simp] lemma boundaryLoop_tgt (σ : Smooth2Simplex I X) :
    (boundaryLoop σ).tgt = σ.toFun Smooth2Simplex.v0 := by
  unfold boundaryLoop
  rw [SmoothPath.concat_tgt, SmoothPath.reverse_tgt]
  rfl

/-! ## Integral commutativity with the boundary chain -/

/-- The boundary loop integrates equally to the boundary chain
(via `integrate_concat`, `integrate_reverse`, and chain linearity). -/
theorem boundaryLoop_integrate_eq (σ : Smooth2Simplex I X)
    (om : SmoothOneForm I X) :
    (boundaryLoop σ).integrate om
      = SmoothChain.integrate (Smooth2Simplex.boundary σ) om := by
  -- boundaryLoop.integrate ω
  --   = (face2 ⋆ face0).integrate ω + face1.reverse.integrate ω    (concat)
  --   = face2.integrate ω + face0.integrate ω + face1.reverse.integrate ω (concat)
  --   = face2.integrate ω + face0.integrate ω - face1.integrate ω  (reverse)
  --   = (face0 - face1 + face2) integrated                          (chain linearity)
  --   = ∂σ integrated.
  unfold boundaryLoop
  rw [SmoothPath.integrate_concat, SmoothPath.integrate_concat,
      SmoothPath.integrate_reverse]
  -- Now we have: face2.integrate ω + face0.integrate ω - face1.integrate ω.
  -- And SmoothChain.integrate ∂σ om = (single face0 - single face1 + single face2).integrate om.
  unfold Smooth2Simplex.boundary
  rw [SmoothChain.integrate_add, SmoothChain.integrate_sub,
      SmoothChain.integrate_single, SmoothChain.integrate_single,
      SmoothChain.integrate_single]
  ring

end Smooth2Simplex

end
