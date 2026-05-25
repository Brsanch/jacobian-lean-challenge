/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.PompeiuKernelSmoothness
import JacobianChallenge.Manifold.PartialZBar

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Cauchy-Pompeiu kernel — Chip 3b: `∂̄` and `pompeiuKernel` commute

This file proves the algebraic bridge identity

```
partialZBar (pompeiuKernel α) z = pompeiuKernel (partialZBar α) z
```

for `α : ℂ → ℂ` of class `C^1` with compact support. This is the key
algebraic step in the Cauchy-Pompeiu identity arc
(`∂̄(pompeiuKernel α) = α`).

The proof has two ingredients:

1. **Linearity of `pompeiuKernel`** — additivity and scalar
   multiplication, both proved in this file for continuous compactly-
   supported inputs (where integrability follows from Chip 1c).
2. **Chip 2d's `fderiv_pompeiuKernel_apply`** — the identity
   `(fderiv ℝ (pompeiuKernel α) z) v = pompeiuKernel (αDeriv α v) z`,
   specialized at `v = 1` and `v = I`.

Combining via the definitions of `partialZBar` and `αDeriv`, both sides
collapse to `(1/2) · (pompeiuKernel (αDeriv α 1) z + I · pompeiuKernel (αDeriv α I) z)`.

After this chip, the only remaining ingredient for the full Cauchy-
Pompeiu identity `∂̄(pompeiuKernel α) z = α z` is the classical
identity `pompeiuKernel (partialZBar α) z = α z` (Chip 3c, the heavy
piece using rectangle Stokes + Chip 3a's small-disc limit).

## Chip 3 arc context

* Chip 3a (`PompeiuKernelSmallDiscLimit.lean`) — small-disc limit
  `∮_{C(z,ε)} α(ζ)·(ζ-z)⁻¹ dζ → 2πI · α(z)`.
* **Chip 3b (this file)** — algebraic bridge
  `partialZBar (pompeiuKernel α) = pompeiuKernel (partialZBar α)`.
* Chip 3c (next) — classical Cauchy-Pompeiu identity
  `pompeiuKernel (partialZBar α) z = α z` via rectangle Stokes on
  `[−L, L]² \ closedBall z ε` + Chip 3a + compact support.

## Main results

* `pompeiuKernel_add` — additivity of `pompeiuKernel` in `α`.
* `pompeiuKernel_const_mul` — `pompeiuKernel (c · α) z = c · pompeiuKernel α z`.
* `partialZBar_pompeiuKernel_eq_pompeiuKernel_partialZBar` — the bridge.

No `sorry`, no `axiom`. -/

noncomputable section

open MeasureTheory Complex Filter Set Topology
open scoped Real Topology

namespace JacobianChallenge.PompeiuKernel

variable {α β : ℂ → ℂ} {z : ℂ}

/-! ## Linearity of `pompeiuKernel` -/

/-- Pointwise additivity of the Pompeiu integrand. -/
lemma pompeiuIntegrand_add (α β : ℂ → ℂ) (z : ℂ) (ζ : ℂ) :
    pompeiuIntegrand (α + β) z ζ
      = pompeiuIntegrand α z ζ + pompeiuIntegrand β z ζ := by
  unfold pompeiuIntegrand
  simp only [Pi.add_apply]
  ring

/-- Pointwise scalar-multiplication identity for the Pompeiu integrand. -/
lemma pompeiuIntegrand_const_mul (c : ℂ) (α : ℂ → ℂ) (z : ℂ) (ζ : ℂ) :
    pompeiuIntegrand (fun ζ' => c * α ζ') z ζ = c * pompeiuIntegrand α z ζ := by
  unfold pompeiuIntegrand
  ring

/-- **Additivity of `pompeiuKernel`** in `α`, for `α`, `β` continuous
and compactly supported. Both summand integrands are integrable
(Chip 1c), so Bochner-integral additivity applies. -/
theorem pompeiuKernel_add
    (h_cont_α : Continuous α) (h_supp_α : HasCompactSupport α)
    (h_cont_β : Continuous β) (h_supp_β : HasCompactSupport β) (z : ℂ) :
    pompeiuKernel (α + β) z = pompeiuKernel α z + pompeiuKernel β z := by
  unfold pompeiuKernel
  have h_pointwise :
      (fun ζ => pompeiuIntegrand (α + β) z ζ)
        = (fun ζ => pompeiuIntegrand α z ζ + pompeiuIntegrand β z ζ) := by
    funext ζ
    exact pompeiuIntegrand_add α β z ζ
  rw [h_pointwise]
  rw [integral_add
    (integrable_pompeiuIntegrand_of_continuous_hasCompactSupport h_cont_α h_supp_α z)
    (integrable_pompeiuIntegrand_of_continuous_hasCompactSupport h_cont_β h_supp_β z)]
  ring

/-- **Scalar-multiplication compatibility of `pompeiuKernel`** in `α`.
This is unconditional: Bochner's `integral_const_mul` does not require
integrability (when not integrable, both sides are `0`). -/
theorem pompeiuKernel_const_mul (c : ℂ) (α : ℂ → ℂ) (z : ℂ) :
    pompeiuKernel (fun ζ => c * α ζ) z = c * pompeiuKernel α z := by
  unfold pompeiuKernel
  have h_pointwise :
      (fun ζ => pompeiuIntegrand (fun ζ' => c * α ζ') z ζ)
        = (fun ζ => c * pompeiuIntegrand α z ζ) := by
    funext ζ
    exact pompeiuIntegrand_const_mul c α z ζ
  rw [h_pointwise]
  have h_pull : ∫ (ζ : ℂ), c * pompeiuIntegrand α z ζ
      = c * ∫ (ζ : ℂ), pompeiuIntegrand α z ζ :=
    integral_const_mul c (pompeiuIntegrand α z)
  rw [h_pull]
  ring

/-! ## The bridge identity -/

/-- **Algebraic bridge (Chip 3b).** The antiholomorphic Wirtinger
derivative of `pompeiuKernel α` at `z` equals the Pompeiu kernel of
`partialZBar α` at `z`, for `α ∈ C^1` with compact support.

This reduces the Cauchy-Pompeiu identity `∂̄(pompeiuKernel α) = α`
to the single classical statement `pompeiuKernel (∂̄α) z = α z`
(Chip 3c). -/
theorem partialZBar_pompeiuKernel_eq_pompeiuKernel_partialZBar
    (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α) (z : ℂ) :
    partialZBar (pompeiuKernel α) z = pompeiuKernel (partialZBar α) z := by
  -- LHS: expand via Chip 2d's fderiv identification.
  have h1 : (fderiv ℝ (pompeiuKernel α) z) 1 = pompeiuKernel (αDeriv α 1) z :=
    fderiv_pompeiuKernel_apply h_smooth h_supp z 1
  have hI : (fderiv ℝ (pompeiuKernel α) z) I = pompeiuKernel (αDeriv α I) z :=
    fderiv_pompeiuKernel_apply h_smooth h_supp z I
  have hLHS :
      partialZBar (pompeiuKernel α) z
        = (2 : ℂ)⁻¹ * (pompeiuKernel (αDeriv α 1) z
                        + I * pompeiuKernel (αDeriv α I) z) := by
    unfold partialZBar
    rw [h1, hI]
  -- RHS: expand `partialZBar α` as `(1/2) · αDeriv α 1 + ((1/2) · I) · αDeriv α I`
  -- and pull the constants through `pompeiuKernel` via linearity.
  have h_cont_α1 : Continuous (αDeriv α 1) := αDeriv_continuous h_smooth (1 : ℂ)
  have h_supp_α1 : HasCompactSupport (αDeriv α 1) :=
    αDeriv_hasCompactSupport h_supp (1 : ℂ)
  have h_cont_αI : Continuous (αDeriv α I) := αDeriv_continuous h_smooth (I : ℂ)
  have h_supp_αI : HasCompactSupport (αDeriv α I) :=
    αDeriv_hasCompactSupport h_supp (I : ℂ)
  have h_cont_f₁ : Continuous (fun ζ => (2 : ℂ)⁻¹ * αDeriv α 1 ζ) :=
    continuous_const.mul h_cont_α1
  have h_supp_f₁ : HasCompactSupport (fun ζ => (2 : ℂ)⁻¹ * αDeriv α 1 ζ) := by
    have h_eq : (fun ζ => (2 : ℂ)⁻¹ * αDeriv α 1 ζ)
        = (fun _ : ℂ => (2 : ℂ)⁻¹) * αDeriv α 1 := by
      funext ζ; rfl
    rw [h_eq]
    exact h_supp_α1.mul_left
  have h_cont_f₂ : Continuous (fun ζ => ((2 : ℂ)⁻¹ * I) * αDeriv α I ζ) :=
    continuous_const.mul h_cont_αI
  have h_supp_f₂ : HasCompactSupport (fun ζ => ((2 : ℂ)⁻¹ * I) * αDeriv α I ζ) := by
    have h_eq : (fun ζ => ((2 : ℂ)⁻¹ * I) * αDeriv α I ζ)
        = (fun _ : ℂ => (2 : ℂ)⁻¹ * I) * αDeriv α I := by
      funext ζ; rfl
    rw [h_eq]
    exact h_supp_αI.mul_left
  -- `partialZBar α ζ = (1/2) · αDeriv α 1 ζ + ((1/2) · I) · αDeriv α I ζ`.
  have h_pzb_decomp :
      (partialZBar α : ℂ → ℂ)
        = (fun ζ => (2 : ℂ)⁻¹ * αDeriv α 1 ζ)
          + (fun ζ => ((2 : ℂ)⁻¹ * I) * αDeriv α I ζ) := by
    funext ζ
    simp only [Pi.add_apply]
    unfold partialZBar αDeriv
    ring
  -- Combine.
  rw [hLHS, h_pzb_decomp,
      pompeiuKernel_add h_cont_f₁ h_supp_f₁ h_cont_f₂ h_supp_f₂,
      pompeiuKernel_const_mul (2 : ℂ)⁻¹ (αDeriv α 1),
      pompeiuKernel_const_mul ((2 : ℂ)⁻¹ * I) (αDeriv α I)]
  ring

end JacobianChallenge.PompeiuKernel
