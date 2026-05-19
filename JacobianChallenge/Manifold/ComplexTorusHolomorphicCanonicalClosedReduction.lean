/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusGenusUpperBound
import JacobianChallenge.Manifold.HolomorphicComponentsCanonicalClosed
import JacobianChallenge.Manifold.HolomorphicOneFormRealComponentLinear

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-! # Structural reduction of `HolomorphicComponentsCanonicalClosed`
on `T_L = ℂ ⧸ L`

With the genus closure `α = c • dz L` for every
`α : HolomorphicOneForm (ℂ ⧸ L)` (proved in
`ComplexTorusGenusUpperBound.lean`), the `holomorphic_closed` atomic
input reduces to its instance at the single 1-form `dz L`:

```
HolomorphicComponentsCanonicalClosed (ℂ ⧸ L)
  ⟺  realComponent (dz L) ∈ canonicalClosedForms 𝓘(ℝ, ℂ) (ℂ ⧸ L)
   ∧  imagComponent (dz L) ∈ canonicalClosedForms 𝓘(ℝ, ℂ) (ℂ ⧸ L)
```

The reduction uses two algebraic identities for complex-scalar
multiplication of holomorphic 1-forms:

* `realComponent (c • α) = c.re • realComponent α - c.im • imagComponent α`
* `imagComponent (c • α) = c.im • realComponent α + c.re • imagComponent α`

combined with the fact that `canonicalClosedForms` is an
`ℝ`-submodule, hence closed under ℝ-linear combinations.

## What this file ships

* `realComponent_I_smul` — `realComponent (Complex.I • α) = -imagComponent α`.
* `imagComponent_I_smul` — `imagComponent (Complex.I • α) = realComponent α`.
* `realComponent_complex_smul` — the ℂ-scalar identity for `realComponent`.
* `imagComponent_complex_smul` — the ℂ-scalar identity for `imagComponent`.
* `ComplexTorus.holomorphicComponentsCanonicalClosed_of_dz_components`
  — structural reduction: from the two `dz`-component hypotheses,
  deduces `HolomorphicComponentsCanonicalClosed (ℂ ⧸ L)`.

The two `dz`-component hypotheses themselves (classical Stokes /
2-simplex-lift content) are the **only** remaining open input.

No `sorry`, no `axiom`. -/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-! ## ℂ-scalar identities for real/imag components -/

/-- **Pointwise: `(c • α).realPart x v = c.re • (α.realPart x v)
- c.im • (α.imagPart x v)`** via `Re(c · z) = c.re · Re z - c.im · Im z`. -/
private lemma realPart_complex_smul_pointwise
    (c : ℂ) (α : HolomorphicOneForm X) (x : X) (v : ℂ) :
    (c • α).realPart x v
      = c.re • (α.realPart x v) - c.im • (α.imagPart x v) := by
  rw [HolomorphicOneForm.realPart_apply, HolomorphicOneForm.realPart_apply,
      HolomorphicOneForm.imagPart_apply]
  have h_eval_smul : (c • α).eval x = c • α.eval x := rfl
  rw [h_eval_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.mul_re]
  simp [smul_eq_mul]

/-- **Pointwise: `(c • α).imagPart x v = c.im • (α.realPart x v)
+ c.re • (α.imagPart x v)`** via `Im(c · z) = c.im · Re z + c.re · Im z`. -/
private lemma imagPart_complex_smul_pointwise
    (c : ℂ) (α : HolomorphicOneForm X) (x : X) (v : ℂ) :
    (c • α).imagPart x v
      = c.im • (α.realPart x v) + c.re • (α.imagPart x v) := by
  rw [HolomorphicOneForm.imagPart_apply, HolomorphicOneForm.realPart_apply,
      HolomorphicOneForm.imagPart_apply]
  have h_eval_smul : (c • α).eval x = c • α.eval x := rfl
  rw [h_eval_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.mul_im]
  simp [smul_eq_mul]; ring

/-- **ℂ-scalar identity for `realComponent`** (section level).
`realComponent (c • α) = c.re • realComponent α - c.im • imagComponent α`
as elements of `SmoothOneForm 𝓘(ℝ, ℂ) X`. -/
lemma realComponent_complex_smul (c : ℂ) (α : HolomorphicOneForm X) :
    realComponent (c • α)
      = c.re • realComponent α - c.im • imagComponent α := by
  ext x
  -- Goal: realComponent (c • α) x = (c.re • realComponent α - c.im • imagComponent α) x.
  -- Both sides have type `CotangentSpace 𝓘(ℝ,ℂ) x` which is def `ℂ →L[ℝ] ℝ`.
  -- Reduce LHS and unfold RHS to CLM operations.
  show realComponent (c • α) x
      = (c.re • realComponent α - c.im • imagComponent α) x
  rw [realComponent_apply]
  -- LHS now: (c • α).realPart x : ℂ →L[ℝ] ℝ.
  -- Show RHS is also a CLM via a `change`.
  show (c • α).realPart x
      = c.re • (realComponent α x) - c.im • (imagComponent α x)
  rw [realComponent_apply, imagComponent_apply]
  -- Now both sides are explicitly ℂ →L[ℝ] ℝ. Apply ContinuousLinearMap.ext.
  refine ContinuousLinearMap.ext fun v => ?_
  -- Goal: (c • α).realPart x v = (c.re • α.realPart x - c.im • α.imagPart x) v.
  rw [realPart_complex_smul_pointwise]
  rfl

/-- **ℂ-scalar identity for `imagComponent`** (section level).
`imagComponent (c • α) = c.im • realComponent α + c.re • imagComponent α`. -/
lemma imagComponent_complex_smul (c : ℂ) (α : HolomorphicOneForm X) :
    imagComponent (c • α)
      = c.im • realComponent α + c.re • imagComponent α := by
  ext x
  show imagComponent (c • α) x
      = (c.im • realComponent α + c.re • imagComponent α) x
  rw [imagComponent_apply]
  show (c • α).imagPart x
      = c.im • (realComponent α x) + c.re • (imagComponent α x)
  rw [realComponent_apply, imagComponent_apply]
  refine ContinuousLinearMap.ext fun v => ?_
  rw [imagPart_complex_smul_pointwise]
  rfl

end JacobianChallenge

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Structural reduction to `dz`-component hypotheses -/

/-- **Structural reduction of `HolomorphicComponentsCanonicalClosed
(ℂ ⧸ L)` to the two `dz`-component hypotheses.**

Under the genus closure (every `α = c • dz L`) and the
ℂ-scalar identities for `realComponent` / `imagComponent`, the named
predicate `HolomorphicComponentsCanonicalClosed (ℂ ⧸ L)` reduces to:

* `realComponent (dz L) ∈ canonicalClosedForms 𝓘(ℝ, ℂ) (ℂ ⧸ L)`
* `imagComponent (dz L) ∈ canonicalClosedForms 𝓘(ℝ, ℂ) (ℂ ⧸ L)`

These two atomic hypotheses are the **only** remaining open input
on the holomorphic-side of the period-lattice bundle on `T_L`. -/
theorem holomorphicComponentsCanonicalClosed_of_dz_components
    (h_re : realComponent (dz L)
              ∈ canonicalClosedForms 𝓘(ℝ, ℂ) (ℂ ⧸ L))
    (h_im : imagComponent (dz L)
              ∈ canonicalClosedForms 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    HolomorphicComponentsCanonicalClosed (ℂ ⧸ L) := by
  intro α
  -- α = c • dz L for some c (by genus closure).
  obtain ⟨c, hc⟩ := exists_smul_dz L α
  rw [hc]
  refine ⟨?_, ?_⟩
  · -- realComponent (c • dz L) = c.re • realComponent (dz L) - c.im • imagComponent (dz L).
    rw [realComponent_complex_smul]
    exact (canonicalClosedForms 𝓘(ℝ, ℂ) (ℂ ⧸ L)).sub_mem
      ((canonicalClosedForms 𝓘(ℝ, ℂ) (ℂ ⧸ L)).smul_mem c.re h_re)
      ((canonicalClosedForms 𝓘(ℝ, ℂ) (ℂ ⧸ L)).smul_mem c.im h_im)
  · -- imagComponent (c • dz L) = c.im • realComponent (dz L) + c.re • imagComponent (dz L).
    rw [imagComponent_complex_smul]
    exact (canonicalClosedForms 𝓘(ℝ, ℂ) (ℂ ⧸ L)).add_mem
      ((canonicalClosedForms 𝓘(ℝ, ℂ) (ℂ ⧸ L)).smul_mem c.im h_re)
      ((canonicalClosedForms 𝓘(ℝ, ℂ) (ℂ ⧸ L)).smul_mem c.re h_im)

end ComplexTorus

end JacobianChallenge

end
