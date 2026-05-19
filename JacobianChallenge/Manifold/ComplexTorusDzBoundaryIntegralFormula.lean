/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusDzIntegrandFormula
import JacobianChallenge.Manifold.ComplexTorusDzComponentsClosed
import JacobianChallenge.Manifold.Smooth2Simplex

set_option linter.unusedSectionVars false

/-! # Boundary-integral formula for `dz` on a smooth 2-simplex of `T_L`

For any smooth 2-simplex `σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)`, the
boundary integral of `realComponent (dz L)` (resp. `imagComponent (dz L)`)
reduces to the real (resp. imaginary) part of a ℂ-valued integral of
the **alternating sum of face velocities**:

```
SmoothChain.integrate (boundary σ) (realComponent (dz L))
  = (∫ s in 0..1, (face0 σ).velocity s
      - (face1 σ).velocity s + (face2 σ).velocity s).re
```

and analogously for `imagComponent`.

This packages the two atomic Stokes inputs as a **single ℂ-valued
claim**: that the alternating velocity integral vanishes. Both
`realComponent` and `imagComponent` then close simultaneously.

## What this file ships

* `ComplexTorus.boundary_face_velocity_integral σ : ℂ` — the alternating
  velocity integral `∫₀¹ face0.vel - face1.vel + face2.vel ds`.
* `ComplexTorus.boundary_integrate_realComponent_dz` — the formula
  `SmoothChain.integrate (boundary σ) (realComponent (dz L)) =
   (boundary_face_velocity_integral σ).re`.
* `ComplexTorus.boundary_integrate_imagComponent_dz` — same for `Im`.

No `sorry`, no `axiom`. -/

open scoped Manifold ContDiff Topology
open MeasureTheory

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## ℂ-valued boundary-face velocity integral -/

/-- **The alternating ℂ-valued integral of face velocities** of a smooth
2-simplex. Equals the per-face velocity integrals combined with the
simplicial boundary signs `+face0 - face1 + face2`. -/
def boundary_face_velocity_integral (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)) : ℂ :=
  (∫ s in (0 : ℝ)..1, (Smooth2Simplex.face0 σ).velocity s)
    - (∫ s in (0 : ℝ)..1, (Smooth2Simplex.face1 σ).velocity s)
    + (∫ s in (0 : ℝ)..1, (Smooth2Simplex.face2 σ).velocity s)

/-! ## Chain-integral linearity unwrap -/

/-- Negation linearity: `integrate (-c) = -integrate c`. Derived via the
group identity `-c + c = 0`. -/
private lemma smoothChain_integrate_neg
    (c : SmoothChain 𝓘(ℝ, ℂ) (ℂ ⧸ L))
    (om : SmoothOneForm 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    SmoothChain.integrate (-c) om = -SmoothChain.integrate c om := by
  have h_add : SmoothChain.integrate (-c + c) om
      = SmoothChain.integrate (-c) om + SmoothChain.integrate c om :=
    SmoothChain.integrate_add _ _ _
  rw [neg_add_cancel, SmoothChain.integrate_zero] at h_add
  linarith

/-- Subtraction linearity: `integrate (c₁ - c₂) = integrate c₁ - integrate c₂`. -/
private lemma smoothChain_integrate_sub
    (c₁ c₂ : SmoothChain 𝓘(ℝ, ℂ) (ℂ ⧸ L))
    (om : SmoothOneForm 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    SmoothChain.integrate (c₁ - c₂) om
      = SmoothChain.integrate c₁ om - SmoothChain.integrate c₂ om := by
  rw [sub_eq_add_neg, SmoothChain.integrate_add, smoothChain_integrate_neg]
  ring

private lemma smoothChain_integrate_boundary_unfold
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L))
    (om : SmoothOneForm 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    SmoothChain.integrate (Smooth2Simplex.boundary σ) om
      = (Smooth2Simplex.face0 σ).integrate om
        - (Smooth2Simplex.face1 σ).integrate om
        + (Smooth2Simplex.face2 σ).integrate om := by
  -- boundary σ = single face0 - single face1 + single face2.
  unfold Smooth2Simplex.boundary
  rw [SmoothChain.integrate_add, smoothChain_integrate_sub,
      SmoothChain.integrate_single, SmoothChain.integrate_single,
      SmoothChain.integrate_single]

/-! ## `Re` / `Im` factor through the boundary integral -/

/-- **`SmoothChain.integrate (boundary σ) (realComponent (dz L)) =
Re(boundary_face_velocity_integral σ)`.** -/
theorem boundary_integrate_realComponent_dz
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    SmoothChain.integrate (Smooth2Simplex.boundary σ) (realComponent (dz L))
      = (boundary_face_velocity_integral L σ).re := by
  rw [smoothChain_integrate_boundary_unfold]
  -- Each face's path integral via integrate_realComponent_dz.
  rw [integrate_realComponent_dz, integrate_realComponent_dz,
      integrate_realComponent_dz]
  -- Now LHS = Re(V_0) - Re(V_1) + Re(V_2).
  -- RHS = (V_0 - V_1 + V_2).re.
  -- Re is ℝ-linear and respects + and -.
  unfold boundary_face_velocity_integral
  rw [Complex.add_re, Complex.sub_re]

/-- **`SmoothChain.integrate (boundary σ) (imagComponent (dz L)) =
Im(boundary_face_velocity_integral σ)`.** -/
theorem boundary_integrate_imagComponent_dz
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    SmoothChain.integrate (Smooth2Simplex.boundary σ) (imagComponent (dz L))
      = (boundary_face_velocity_integral L σ).im := by
  rw [smoothChain_integrate_boundary_unfold]
  rw [integrate_imagComponent_dz, integrate_imagComponent_dz,
      integrate_imagComponent_dz]
  unfold boundary_face_velocity_integral
  rw [Complex.add_im, Complex.sub_im]

/-! ## Closure of the named predicate via the ℂ-valued vanishing -/

/-- **From `boundary_face_velocity_integral σ = 0` to membership in
`canonicalClosedForms` for both `realComponent (dz L)` and
`imagComponent (dz L)`.**

If the ℂ-valued alternating face-velocity integral vanishes for every
smooth 2-simplex on `T_L`, then both `realComponent (dz L)` and
`imagComponent (dz L)` lie in `canonicalClosedForms 𝓘(ℝ, ℂ) (ℂ ⧸ L)`. -/
theorem realImagDzInCanonicalClosed_of_boundary_velocity_vanishing
    (h : ∀ σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L),
      boundary_face_velocity_integral L σ = 0) :
    RealImagDzInCanonicalClosed L := by
  refine ⟨?_, ?_⟩
  · intro σ
    rw [boundary_integrate_realComponent_dz, h σ]
    simp
  · intro σ
    rw [boundary_integrate_imagComponent_dz, h σ]
    simp

end ComplexTorus

end JacobianChallenge

end
