/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RamificationIndex
import JacobianChallenge.Manifold.ContMDiffOmegaAnalytic
import Mathlib.Analysis.Analytic.Order

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Chart-shift invariance helper for `manifoldRamificationIndex`

A small invariance fact: precomposing the chart-pullback with translation
in `ℂ` does not change the analytic order, since translation has nonzero
derivative everywhere.

This is used to bridge between different chart parametrisations of the
same manifold neighbourhood.

No `sorry`, no `axiom`. -/

namespace JacobianChallenge

namespace Manifold

universe u v

/-- **Translations have nonzero derivative everywhere.** -/
lemma deriv_add_const (c : ℂ) (z : ℂ) :
    deriv (fun w : ℂ => w + c) z = 1 := by
  have h : (fun w : ℂ => w + c) = (fun w => w) + (fun _ => c) := rfl
  rw [h, deriv_add (differentiableAt_id) (differentiableAt_const c),
      deriv_id, deriv_const]
  ring

/-- **Translation is analytic.** -/
lemma analyticAt_add_const (c : ℂ) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => w + c) z :=
  (analyticAt_id).add (analyticAt_const)

/-- **Subtraction by a constant is analytic.** -/
lemma analyticAt_sub_const (c : ℂ) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => w - c) z :=
  (analyticAt_id).sub (analyticAt_const)

/-- **Derivative of subtraction by a constant.** -/
lemma deriv_sub_const (c : ℂ) (z : ℂ) :
    deriv (fun w : ℂ => w - c) z = 1 := by
  have h : (fun w : ℂ => w - c) = (fun w => w) - (fun _ => c) := rfl
  rw [h, deriv_sub (differentiableAt_id) (differentiableAt_const c),
      deriv_id, deriv_const, sub_zero]

end Manifold

end JacobianChallenge
