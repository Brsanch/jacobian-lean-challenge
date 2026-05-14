/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroRSAffineFactor
import JacobianChallenge.Manifold.Pic0SubsingletonBridge
import JacobianChallenge.Divisor.Single

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `Subsingleton (Pic0 RiemannSphere)` — Pic⁰(ℙ¹) = 0 (partial)

Divisor identity for `mnRSAffineFactor`, with the elementary divisor
`δ_{some a} - δ_∞` shown to lie in `PrincDiv RiemannSphere`. -/

noncomputable section

open scoped Classical Manifold ContDiff Topology
open Filter Set OnePoint

namespace JacobianChallenge

/-! ## Order computations -/

/-- The order of `(fun w => w - a)` at `a` is `1`. Uses the change-of-variable
formula `meromorphicOrderAt_comp_of_deriv_ne_zero` with `f = id` (order 1 at 0). -/
lemma meromorphicOrderAt_sub_const_at_a (a : ℂ) :
    meromorphicOrderAt (fun w : ℂ => w - a) a = ((1 : ℤ) : WithTop ℤ) := by
  have hg : AnalyticAt ℂ (fun w : ℂ => w - a) a := analyticAt_id.sub analyticAt_const
  have h_deriv : HasDerivAt (fun w : ℂ => w - a) 1 a := by
    have := (hasDerivAt_id a).sub_const a
    simpa using this
  have hg' : deriv (fun w : ℂ => w - a) a ≠ 0 := by
    rw [h_deriv.deriv]; exact one_ne_zero
  -- Apply `meromorphicOrderAt_comp_of_deriv_ne_zero` with `id ∘ g`.
  have h_eq : (fun w : ℂ => w - a) = (id ∘ (fun w : ℂ => w - a)) := by funext; rfl
  rw [h_eq, meromorphicOrderAt_comp_of_deriv_ne_zero hg hg']
  -- Now: meromorphicOrderAt id ((fun w => w - a) a) = 1. (fun w => w - a) a = 0.
  show meromorphicOrderAt id (a - a) = ((1 : ℤ) : WithTop ℤ)
  rw [sub_self]
  exact meromorphicOrderAt_id

/-- The order of `(fun w => w - a)` at `z ≠ a` is `0`. -/
lemma meromorphicOrderAt_sub_const_at_ne (a z : ℂ) (hza : z ≠ a) :
    meromorphicOrderAt (fun w : ℂ => w - a) z = 0 := by
  have hAn : AnalyticAt ℂ (fun w : ℂ => w - a) z :=
    analyticAt_id.sub analyticAt_const
  have h_val : (fun w : ℂ => w - a) z ≠ 0 := sub_ne_zero.mpr hza
  rw [hAn.meromorphicOrderAt_eq]
  have h_ord : analyticOrderAt (fun w : ℂ => w - a) z = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr h_val)
  rw [h_ord]
  rfl

/-- `mmeromorphicOrderAt` of `RSAffineFactor a` at `some z`. -/
lemma RSAffineFactor_orderAt_coe_eq_one (a : ℂ) :
    mmeromorphicOrderAt 𝓘(ℂ, ℂ) (RSAffineFactor a) (((a : ℂ) : RiemannSphere))
      = ((1 : ℤ) : WithTop ℤ) := by
  show meromorphicOrderAt
      ((RSAffineFactor a) ∘ (chartAt ℂ (((a : ℂ) : RiemannSphere))).symm)
      ((chartAt ℂ (((a : ℂ) : RiemannSphere))) (((a : ℂ) : RiemannSphere))) = _
  have h_chart : (chartAt ℂ (((a : ℂ) : RiemannSphere))
      : OpenPartialHomeomorph RiemannSphere ℂ)
        = RiemannSphere.chartN := rfl
  rw [h_chart, RSAffineFactor_comp_chartN_symm, RiemannSphere.chartN_apply_coe]
  exact meromorphicOrderAt_sub_const_at_a a

lemma RSAffineFactor_orderAt_coe_eq_zero (a z : ℂ) (hza : z ≠ a) :
    mmeromorphicOrderAt 𝓘(ℂ, ℂ) (RSAffineFactor a) ((z : RiemannSphere)) = 0 := by
  show meromorphicOrderAt
      ((RSAffineFactor a) ∘ (chartAt ℂ ((z : RiemannSphere))).symm)
      ((chartAt ℂ ((z : RiemannSphere))) ((z : RiemannSphere))) = _
  have h_chart : (chartAt ℂ ((z : RiemannSphere))
      : OpenPartialHomeomorph RiemannSphere ℂ)
        = RiemannSphere.chartN := rfl
  rw [h_chart, RSAffineFactor_comp_chartN_symm, RiemannSphere.chartN_apply_coe]
  exact meromorphicOrderAt_sub_const_at_ne a z hza

/-! ## The divisor of `mnRSAffineFactor` -/

/-- Pointwise value of the elementary-divisor difference. -/
lemma elementary_div_apply (a : ℂ) (x : RiemannSphere) :
    ((Div.single (((a : ℂ) : RiemannSphere)) : Div RiemannSphere)
        - Div.single (∞ : RiemannSphere)) x
      = (if x = ((a : ℂ) : RiemannSphere) then 1 else 0)
        - (if x = (∞ : RiemannSphere) then 1 else 0) := by
  exact Div.single_sub_single_apply _ _ _

/-- `principalDivisorMap (mnRSAffineFactor a) = Div.single (some a) - Div.single ∞`. -/
lemma principalDivisorMap_mnRSAffineFactor (a : ℂ) :
    principalDivisorMap (mnRSAffineFactor a)
      = (Div.single (((a : ℂ) : RiemannSphere)) : Div RiemannSphere)
        - Div.single (∞ : RiemannSphere) := by
  ext x
  show (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (RSAffineFactor a) x).untop₀
        = ((Div.single (((a : ℂ) : RiemannSphere)) : Div RiemannSphere)
            - Div.single (∞ : RiemannSphere)) x
  rw [elementary_div_apply]
  induction x using OnePoint.rec with
  | infty =>
    rw [RSAffineFactor_orderAt_infty]
    -- ((-1:ℤ) : WithTop ℤ).untop₀ = -1. RHS: (∞ = some a → False) - (∞ = ∞ → True) = 0 - 1 = -1.
    have h1 : (∞ : RiemannSphere) ≠ ((a : ℂ) : RiemannSphere) :=
      OnePoint.infty_ne_coe a
    have h2 : (∞ : RiemannSphere) = (∞ : RiemannSphere) := rfl
    rw [if_neg h1, if_pos h2]
    rfl
  | coe z =>
    by_cases hza : z = a
    · subst hza
      rw [RSAffineFactor_orderAt_coe_eq_one]
      -- (1 : WithTop ℤ).untop₀ = 1. RHS: 1 - 0 = 1.
      have h1 : (((z : ℂ) : RiemannSphere)) = (((z : ℂ) : RiemannSphere)) := rfl
      have h2 : (((z : ℂ) : RiemannSphere)) ≠ (∞ : RiemannSphere) :=
        (OnePoint.infty_ne_coe z).symm
      rw [if_pos h1, if_neg h2]
      rfl
    · rw [RSAffineFactor_orderAt_coe_eq_zero a z hza]
      -- (0 : WithTop ℤ).untop₀ = 0. RHS: 0 - 0 = 0.
      have h1 : (((z : ℂ) : RiemannSphere)) ≠ (((a : ℂ) : RiemannSphere)) := by
        intro h; exact hza (OnePoint.coe_injective h)
      have h2 : (((z : ℂ) : RiemannSphere)) ≠ (∞ : RiemannSphere) :=
        (OnePoint.infty_ne_coe z).symm
      rw [if_neg h1, if_neg h2]
      rfl

/-- The elementary divisor `δ_{some a} - δ_∞ ∈ PrincDiv RiemannSphere`. -/
lemma elementaryDivisor_mem_PrincDiv (a : ℂ) :
    ((Div.single (((a : ℂ) : RiemannSphere)) : Div RiemannSphere)
      - Div.single (∞ : RiemannSphere)) ∈ PrincDiv RiemannSphere := by
  rw [← principalDivisorMap_mnRSAffineFactor a]
  exact principalDivisorMap_mem_PrincDiv _

end JacobianChallenge

end
