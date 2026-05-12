/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormRealification

/-! # Pointwise linearity of the real/imaginary decomposition

`HolomorphicOneFormRealification.lean` introduces, for every
`om : HolomorphicOneForm X` and `x : X`,

* `om.eval x : ℂ →L[ℂ] ℂ`,
* `om.realPart x : ℂ →L[ℝ] ℝ`,
* `om.imagPart x : ℂ →L[ℝ] ℝ`,

together with the pointwise reconstruction
`om.eval x v = om.realPart x v + I * om.imagPart x v`.

This file records the algebraic compatibilities of these three pointwise
operations with the `AddCommGroup` / `Module ℂ` structure that
`HolomorphicOneForm X` inherits from `ContMDiffSection`. Concretely, we
show that `eval`, `realPart`, and `imagPart` are *pointwise* additive
(and behave correctly under negation, subtraction, and the zero form),
and that `eval` is `ℂ`-linear in the form argument. These identities are
exactly the pointwise content downstream of which the holomorphic side of
the period-pairing chip can split a `∫_γ (om₁ + c · om₂)` integral as
`∫_γ om₁ + c · ∫_γ om₂` summand-by-summand, by composing with
`SmoothChainIntegralLinearity` (chip ZZP, real-side).

Everything below is purely the algebraic content of mathlib's
`ContMDiffSection.coe_add / coe_zero / coe_neg / coe_sub / coe_smul`
unfolded through the named projections `eval / realPart / imagPart`,
plus the fact that `Complex.reCLM` and `Complex.imCLM` are `ℝ`-linear
continuous maps and that `ContinuousLinearMap.restrictScalars ℝ` is an
additive group / module homomorphism in its argument.

No new definitions, no new axioms, no `sorry`. We keep the file
`om`-binders only (the Greek omega is reserved as a tactic-block token at
this Lean version).

## Main theorems

* `HolomorphicOneForm.eval_zero`,
* `HolomorphicOneForm.eval_add`,
* `HolomorphicOneForm.eval_neg`,
* `HolomorphicOneForm.eval_sub`,
* `HolomorphicOneForm.eval_smul`,
* `HolomorphicOneForm.realPart_zero`,
* `HolomorphicOneForm.realPart_add`,
* `HolomorphicOneForm.realPart_neg`,
* `HolomorphicOneForm.realPart_sub`,
* `HolomorphicOneForm.imagPart_zero`,
* `HolomorphicOneForm.imagPart_add`,
* `HolomorphicOneForm.imagPart_neg`,
* `HolomorphicOneForm.imagPart_sub`,
* `HolomorphicOneForm.eval_add_apply`,
* `HolomorphicOneForm.eval_smul_apply`,
* `HolomorphicOneForm.realPart_add_apply`,
* `HolomorphicOneForm.imagPart_add_apply`.

These are stated at the level of `om.eval x = …` (continuous-linear-map
equality at a point) and at the level of `om.eval x v = …` (the scalar
form, with `v : ℂ`). The two flavours are recorded separately because
downstream callers use both shapes.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

-- The `unusedSimpArgs` linter flags lemmas in `simp [...]` calls that are
-- not strictly necessary for the rewrite when run in isolation, but which
-- document the chain of simp facts and remain helpful for diagnosis when
-- upstream lemmas change. Suppressed locally rather than per-call to keep
-- the file readable.
set_option linter.unusedSimpArgs false

namespace HolomorphicOneForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Pointwise behaviour of `eval` -/

/-- Underlying `ContMDiffSection` view of a `HolomorphicOneForm`. -/
private abbrev asSection (om : HolomorphicOneForm X) :
    ContMDiffSection (𝕜 := ℂ) (E := ℂ) (H := ℂ) (M := X)
      𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω (CotangentSpace 𝓘(ℂ) : X → Type _) := om

private theorem eval_eq_section_apply (om : HolomorphicOneForm X) (x : X) :
    om.eval x = (asSection om) x := rfl

@[simp]
theorem eval_zero (x : X) :
    (0 : HolomorphicOneForm X).eval x = 0 := by
  rw [eval_eq_section_apply]
  show (0 : ContMDiffSection (𝕜 := ℂ) (E := ℂ) (H := ℂ) (M := X)
      𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω (CotangentSpace 𝓘(ℂ) : X → Type _)) x = 0
  rw [ContMDiffSection.coe_zero]
  rfl

@[simp]
theorem eval_add (om₁ om₂ : HolomorphicOneForm X) (x : X) :
    (om₁ + om₂).eval x = om₁.eval x + om₂.eval x := by
  rw [eval_eq_section_apply, eval_eq_section_apply, eval_eq_section_apply]
  show (asSection om₁ + asSection om₂) x = asSection om₁ x + asSection om₂ x
  rw [ContMDiffSection.coe_add]
  rfl

@[simp]
theorem eval_neg (om : HolomorphicOneForm X) (x : X) :
    (-om).eval x = -(om.eval x) := by
  rw [eval_eq_section_apply, eval_eq_section_apply]
  show (-(asSection om)) x = -(asSection om x)
  rw [ContMDiffSection.coe_neg]
  rfl

@[simp]
theorem eval_sub (om₁ om₂ : HolomorphicOneForm X) (x : X) :
    (om₁ - om₂).eval x = om₁.eval x - om₂.eval x := by
  rw [eval_eq_section_apply, eval_eq_section_apply, eval_eq_section_apply]
  show (asSection om₁ - asSection om₂) x = asSection om₁ x - asSection om₂ x
  rw [ContMDiffSection.coe_sub]
  rfl

@[simp]
theorem eval_smul (c : ℂ) (om : HolomorphicOneForm X) (x : X) :
    (c • om).eval x = c • om.eval x := by
  rw [eval_eq_section_apply, eval_eq_section_apply]
  show (c • asSection om) x = c • asSection om x
  rw [ContMDiffSection.coe_smul]
  rfl

/-! ### Scalar-applied versions of `eval` -/

theorem eval_add_apply (om₁ om₂ : HolomorphicOneForm X) (x : X) (v : ℂ) :
    (om₁ + om₂).eval x v = om₁.eval x v + om₂.eval x v := by
  rw [eval_add]
  rfl

theorem eval_smul_apply (c : ℂ) (om : HolomorphicOneForm X) (x : X) (v : ℂ) :
    (c • om).eval x v = c * om.eval x v := by
  rw [eval_smul]
  -- `(c • φ) v = c • (φ v)` for `φ : ℂ →L[ℂ] ℂ`; on `ℂ` scalar mult is mult.
  simp [smul_eq_mul]

theorem eval_neg_apply (om : HolomorphicOneForm X) (x : X) (v : ℂ) :
    (-om).eval x v = -(om.eval x v) := by
  rw [eval_neg]
  rfl

theorem eval_sub_apply (om₁ om₂ : HolomorphicOneForm X) (x : X) (v : ℂ) :
    (om₁ - om₂).eval x v = om₁.eval x v - om₂.eval x v := by
  rw [eval_sub]
  rfl

theorem eval_zero_apply (x : X) (v : ℂ) :
    (0 : HolomorphicOneForm X).eval x v = 0 := by
  rw [eval_zero]
  rfl

/-! ### Pointwise behaviour of `realPart` -/

@[simp]
theorem realPart_zero (x : X) :
    (0 : HolomorphicOneForm X).realPart x = 0 := by
  -- `realPart om x = reCLM ∘L (om.eval x).restrictScalars ℝ`. Both
  -- `restrictScalars` and post-composition with a CLM send `0 ↦ 0`.
  ext v
  simp [realPart_apply, eval_zero]

@[simp]
theorem realPart_add (om₁ om₂ : HolomorphicOneForm X) (x : X) :
    (om₁ + om₂).realPart x = om₁.realPart x + om₂.realPart x := by
  ext v
  -- Reduce to `Complex.add_re` after pushing `eval_add` through.
  simp [realPart_apply, eval_add_apply, Complex.add_re]

@[simp]
theorem realPart_neg (om : HolomorphicOneForm X) (x : X) :
    (-om).realPart x = -(om.realPart x) := by
  ext v
  simp [realPart_apply, eval_neg_apply, Complex.neg_re]

@[simp]
theorem realPart_sub (om₁ om₂ : HolomorphicOneForm X) (x : X) :
    (om₁ - om₂).realPart x = om₁.realPart x - om₂.realPart x := by
  ext v
  simp [realPart_apply, eval_sub_apply, Complex.sub_re]

theorem realPart_add_apply (om₁ om₂ : HolomorphicOneForm X) (x : X) (v : ℂ) :
    (om₁ + om₂).realPart x v = om₁.realPart x v + om₂.realPart x v := by
  simp [realPart_apply, eval_add_apply, Complex.add_re]

theorem realPart_neg_apply (om : HolomorphicOneForm X) (x : X) (v : ℂ) :
    (-om).realPart x v = -(om.realPart x v) := by
  simp [realPart_apply, eval_neg_apply, Complex.neg_re]

theorem realPart_sub_apply (om₁ om₂ : HolomorphicOneForm X) (x : X) (v : ℂ) :
    (om₁ - om₂).realPart x v = om₁.realPart x v - om₂.realPart x v := by
  simp [realPart_apply, eval_sub_apply, Complex.sub_re]

theorem realPart_zero_apply (x : X) (v : ℂ) :
    (0 : HolomorphicOneForm X).realPart x v = 0 := by
  simp [realPart_apply, eval_zero_apply]

/-! ### Pointwise behaviour of `imagPart` -/

@[simp]
theorem imagPart_zero (x : X) :
    (0 : HolomorphicOneForm X).imagPart x = 0 := by
  ext v
  simp [imagPart_apply, eval_zero]

@[simp]
theorem imagPart_add (om₁ om₂ : HolomorphicOneForm X) (x : X) :
    (om₁ + om₂).imagPart x = om₁.imagPart x + om₂.imagPart x := by
  ext v
  simp [imagPart_apply, eval_add_apply, Complex.add_im]

@[simp]
theorem imagPart_neg (om : HolomorphicOneForm X) (x : X) :
    (-om).imagPart x = -(om.imagPart x) := by
  ext v
  simp [imagPart_apply, eval_neg_apply, Complex.neg_im]

@[simp]
theorem imagPart_sub (om₁ om₂ : HolomorphicOneForm X) (x : X) :
    (om₁ - om₂).imagPart x = om₁.imagPart x - om₂.imagPart x := by
  ext v
  simp [imagPart_apply, eval_sub_apply, Complex.sub_im]

theorem imagPart_add_apply (om₁ om₂ : HolomorphicOneForm X) (x : X) (v : ℂ) :
    (om₁ + om₂).imagPart x v = om₁.imagPart x v + om₂.imagPart x v := by
  simp [imagPart_apply, eval_add_apply, Complex.add_im]

theorem imagPart_neg_apply (om : HolomorphicOneForm X) (x : X) (v : ℂ) :
    (-om).imagPart x v = -(om.imagPart x v) := by
  simp [imagPart_apply, eval_neg_apply, Complex.neg_im]

theorem imagPart_sub_apply (om₁ om₂ : HolomorphicOneForm X) (x : X) (v : ℂ) :
    (om₁ - om₂).imagPart x v = om₁.imagPart x v - om₂.imagPart x v := by
  simp [imagPart_apply, eval_sub_apply, Complex.sub_im]

theorem imagPart_zero_apply (x : X) (v : ℂ) :
    (0 : HolomorphicOneForm X).imagPart x v = 0 := by
  simp [imagPart_apply, eval_zero_apply]

/-! ### Reconstruction is additive

A direct consequence of the pointwise reconstruction `eval_eq` and
`eval_add_apply` / `realPart_add_apply` / `imagPart_add_apply`:
splitting `om₁ + om₂` form-wise commutes with assembling the complex
reconstruction `re + i · im` from the real/imag parts. This is the
identity that downstream chips will combine with chain-integral
linearity to reduce a holomorphic period to two real periods. -/

theorem eval_eq_add_realPart_imagPart (om : HolomorphicOneForm X) (x : X)
    (v : ℂ) :
    om.eval x v =
      (om.realPart x v : ℂ) + Complex.I * (om.imagPart x v : ℂ) :=
  om.eval_eq x v

theorem realPart_add_imagPart_add_eq
    (om₁ om₂ : HolomorphicOneForm X) (x : X) (v : ℂ) :
    ((om₁ + om₂).realPart x v : ℂ)
        + Complex.I * ((om₁ + om₂).imagPart x v : ℂ)
      =
        ((om₁.realPart x v : ℂ) + Complex.I * (om₁.imagPart x v : ℂ))
        + ((om₂.realPart x v : ℂ) + Complex.I * (om₂.imagPart x v : ℂ)) := by
  -- LHS = (om₁ + om₂).eval x v by reconstruction; RHS = om₁.eval x v + om₂.eval x v
  -- by reconstruction summand-wise. They agree by `eval_add_apply`.
  rw [← eval_eq_add_realPart_imagPart, ← eval_eq_add_realPart_imagPart,
    ← eval_eq_add_realPart_imagPart, eval_add_apply]

theorem realPart_imagPart_smul_eq
    (c : ℂ) (om : HolomorphicOneForm X) (x : X) (v : ℂ) :
    ((c • om).realPart x v : ℂ)
        + Complex.I * ((c • om).imagPart x v : ℂ)
      =
        c * ((om.realPart x v : ℂ) + Complex.I * (om.imagPart x v : ℂ)) := by
  rw [← eval_eq_add_realPart_imagPart, ← eval_eq_add_realPart_imagPart,
    eval_smul_apply]

end HolomorphicOneForm

end
