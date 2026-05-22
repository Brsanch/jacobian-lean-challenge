/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MorseFunctionRiemannSphere

set_option linter.unusedSectionVars false

/-! # `heightLocalℂ` strict bounds at `z = 0` (classical-3)

Strict bounds: for `z ≠ 0`, `heightLocalℂ z < heightLocalℂ 0 = 1`.

These strict inequalities express that the max at `z = 0` is **strict
(no flat direction)**, a necessary precondition for the Hessian to be
non-degenerate (Morse).

## What this file ships

* `heightLocalℂ_lt_one_of_ne_zero` — `z ≠ 0 ⇒ heightLocalℂ z < 1`.
* `heightLocalℂ_lt_one_of_ne_zero_isMaxOn` — strict-max-on form:
  `heightLocalℂ z < heightLocalℂ 0` whenever `z ≠ 0`.
* `heightLocalℂ_S_pos_of_ne_zero` — `w ≠ 0 ⇒ 0 < heightLocalℂ_S w`.
* `heightLocalℂ_S_gt_zero_isMinOn` — strict-min form:
  `heightLocalℂ_S 0 < heightLocalℂ_S w` whenever `w ≠ 0`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-- **Strict bound:** `heightLocalℂ z < 1` for `z ≠ 0`. -/
lemma heightLocalℂ_lt_one_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    heightLocalℂ z < 1 := by
  unfold heightLocalℂ
  have h_pos : (0 : ℝ) < 1 + ‖z‖^2 := by positivity
  have h_norm_sq_pos : 0 < ‖z‖^2 := by
    have : 0 < ‖z‖ := norm_pos_iff.mpr hz
    positivity
  rw [div_lt_one h_pos]
  linarith

/-- **Strict-max-at-zero form**: `heightLocalℂ z < heightLocalℂ 0`
whenever `z ≠ 0`. -/
lemma heightLocalℂ_lt_one_of_ne_zero_isMaxOn {z : ℂ} (hz : z ≠ 0) :
    heightLocalℂ z < heightLocalℂ 0 := by
  rw [heightLocalℂ_zero]
  exact heightLocalℂ_lt_one_of_ne_zero hz

/-- **Strict bound:** `heightLocalℂ_S w > 0` for `w ≠ 0`. -/
lemma heightLocalℂ_S_pos_of_ne_zero {w : ℂ} (hw : w ≠ 0) :
    0 < heightLocalℂ_S w := by
  unfold heightLocalℂ_S
  have h_pos : (0 : ℝ) < 1 + ‖w‖^2 := by positivity
  have h_norm_sq_pos : 0 < ‖w‖^2 := by
    have : 0 < ‖w‖ := norm_pos_iff.mpr hw
    positivity
  exact div_pos h_norm_sq_pos h_pos

/-- **Strict-min-at-zero form**: `heightLocalℂ_S 0 < heightLocalℂ_S w`
whenever `w ≠ 0`. -/
lemma heightLocalℂ_S_gt_zero_isMinOn {w : ℂ} (hw : w ≠ 0) :
    heightLocalℂ_S 0 < heightLocalℂ_S w := by
  rw [heightLocalℂ_S_zero]
  exact heightLocalℂ_S_pos_of_ne_zero hw

end RiemannSphere

end JacobianChallenge

end
