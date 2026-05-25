/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.PompeiuKernelRadialIntegral
import JacobianChallenge.Analysis.PompeiuKernelSecondSummandIdentity

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Cauchy-Pompeiu kernel — Chip 3c-F-3d-2-prep: rescaling identities for the radial bump

The algebraic identities under the rescaling `η = z + ε·w`:

```
radialBump z ε (z + ε·w) = radialBump 0 1 w           = psiBump 1 ‖w‖,
radialBumpComplex z ε (z + ε·w) = unitRadialBumpC w,
radialCutoff z ε (z + ε·w) = radialCutoff 0 1 w,
radialCutoffComplex z ε (z + ε·w) = ((radialCutoff 0 1 w : ℝ) : ℂ).
```

These follow from `psiBump ε (ε·r) = psiBump 1 r` (a direct calculation
in `Real.smoothTransition`'s argument), combined with the norm identity
`‖z + ε·w - z‖ = ε · ‖w‖` for `ε ≥ 0`.

Used by Chip 3c-F-3d-2 (the substitution identity) and Chip 3c-F-3d-3
(the DCT on the substituted integral). All sorry- and axiom-free. -/

noncomputable section

open Complex Filter Set Topology Metric
open scoped Topology

namespace JacobianChallenge.PompeiuKernel

/-! ## Scalar identity: `psiBump ε (ε·r) = psiBump 1 r` -/

/-- The 1D profile `psiBump` is invariant under the rescaling
`(ε, r) ↦ (1, ε⁻¹·r)`: `psiBump ε (ε·r) = psiBump 1 r`. -/
lemma psiBump_rescale {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    psiBump ε (ε * r) = psiBump 1 r := by
  unfold psiBump
  -- psiBump ε (ε·r) = smoothTransition (2 - 2 · (ε·r) / ε)
  --                 = smoothTransition (2 - 2·r)
  --                 = smoothTransition (2 - 2·r / 1)
  --                 = psiBump 1 r.
  congr 1
  field_simp

/-! ## Norm identity for `z + ε·w - z` -/

/-- `‖(z + ε·w) - z‖ = ε · ‖w‖` for `ε ≥ 0`. -/
lemma norm_z_add_smul_sub {z w : ℂ} {ε : ℝ} (hε : 0 ≤ ε) :
    ‖(z + (ε : ℂ) * w) - z‖ = ε * ‖w‖ := by
  have h : (z + (ε : ℂ) * w) - z = (ε : ℂ) * w := by ring
  rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε]

/-! ## Rescaling of the radial bump -/

/-- `radialBump z ε (z + ε·w) = psiBump 1 ‖w‖` for `ε > 0`. -/
lemma radialBump_at_rescaled {z : ℂ} {ε : ℝ} (hε : 0 < ε) (w : ℂ) :
    radialBump z ε (z + (ε : ℂ) * w) = psiBump 1 ‖w‖ := by
  unfold radialBump
  rw [norm_z_add_smul_sub hε.le]
  exact psiBump_rescale hε ‖w‖

/-- `unitRadialBumpC w = ((psiBump 1 ‖w‖ : ℝ) : ℂ)`: the `ℂ`-valued
unit bump equals the lifted `psiBump 1 ‖w‖`. Restates
`unitRadialBumpC_eq_psi`. -/
lemma unitRadialBumpC_value (w : ℂ) :
    unitRadialBumpC w = ((psiBump 1 ‖w‖ : ℝ) : ℂ) :=
  unitRadialBumpC_eq_psi w

/-- **Rescaling identity for `radialBumpComplex`.** For `ε > 0`,
`radialBumpComplex z ε (z + ε·w) = unitRadialBumpC w`. -/
lemma radialBumpComplex_at_rescaled {z : ℂ} {ε : ℝ} (hε : 0 < ε) (w : ℂ) :
    ((radialBump z ε (z + (ε : ℂ) * w) : ℝ) : ℂ) = unitRadialBumpC w := by
  rw [radialBump_at_rescaled hε, unitRadialBumpC_value]

/-! ## Rescaling of the radial cutoff -/

/-- `radialCutoff z ε (z + ε·w) = 1 - psiBump 1 ‖w‖` for `ε > 0`. -/
lemma radialCutoff_at_rescaled {z : ℂ} {ε : ℝ} (hε : 0 < ε) (w : ℂ) :
    radialCutoff z ε (z + (ε : ℂ) * w) = 1 - psiBump 1 ‖w‖ := by
  unfold radialCutoff
  rw [radialBump_at_rescaled hε]

/-- The unit-scale radial cutoff `ℂ`-valued: `radialCutoffComplex 0 1 w`. -/
lemma radialCutoffComplex_at_rescaled {z : ℂ} {ε : ℝ} (hε : 0 < ε) (w : ℂ) :
    radialCutoffComplex z ε (z + (ε : ℂ) * w) = radialCutoffComplex 0 1 w := by
  unfold radialCutoffComplex
  rw [radialCutoff_at_rescaled hε]
  unfold radialCutoff radialBump
  congr 1
  rw [sub_zero]

end JacobianChallenge.PompeiuKernel
