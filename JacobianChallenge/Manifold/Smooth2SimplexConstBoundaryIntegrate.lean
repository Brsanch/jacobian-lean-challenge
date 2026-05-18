/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathIntegrateConstToPath
import JacobianChallenge.Manifold.SmoothChainIntegralLinearity

set_option linter.unusedSectionVars false

/-! # The constant 2-simplex's boundary integrates to zero against any form

For the constant 2-simplex `Smooth2Simplex.const I X P`, each face
`face₀ / face₁ / face₂` is a constant-toPath smooth path at `P`.
Hence each face integrates to zero against any smooth 1-form (by
`integrate_eq_zero_of_toPath_eq_const`). By linearity of
`SmoothChain.integrate` over the chain-side decomposition
`boundary (const P) = single (face₀) - single (face₁) + single (face₂)`,
the boundary integrates to zero against any smooth 1-form.

This is the cleanest non-trivial single-simplex Stokes statement
available unconditionally: the constant 2-simplex automatically
satisfies the integration-side Stokes vanishing against any form,
without any closedness assumption on the form.

## Significance

This is consistent with — and complementary to — the canonical
`stokesBoundaries` membership of `boundary_const_smoothCycle`:
both express the structural fact that constant 2-simplices contribute
trivially to the Stokes complex.

## What this file ships

* `Smooth2Simplex.integrate_boundary_const_eq_zero` —
  `SmoothChain.integrate (boundary (const P)) ω = 0` for any
  `ω : SmoothOneForm I X`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology Bundle ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-- **The constant 2-simplex's boundary integrates to zero against any
smooth 1-form.** Each face is a constant-toPath path at `P`, hence
integrates to zero; linearity of `SmoothChain.integrate` over
`boundary (const P) = single (face₀) - single (face₁) + single (face₂)`
gives `0 - 0 + 0 = 0`. -/
theorem Smooth2Simplex.integrate_boundary_const_eq_zero
    (P : X) (om : SmoothOneForm I X) :
    SmoothChain.integrate
      (Smooth2Simplex.boundary (Smooth2Simplex.const I X P)) om = 0 := by
  unfold Smooth2Simplex.boundary
  -- LHS = integrate (single face0 - single face1 + single face2) ω
  --     = integrate (single face0) ω - integrate (single face1) ω
  --       + integrate (single face2) ω
  rw [SmoothChain.integrate_add, SmoothChain.integrate_sub,
      SmoothChain.integrate_single, SmoothChain.integrate_single,
      SmoothChain.integrate_single,
      face0_const_integrate_eq_zero,
      face1_const_integrate_eq_zero,
      face2_const_integrate_eq_zero,
      sub_zero, add_zero]

end JacobianChallenge

end
