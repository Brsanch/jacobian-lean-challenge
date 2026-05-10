/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import JacobianChallenge.Manifold.NormPushforwardChartPullbackTranslated
import JacobianChallenge.Manifold.NormPushforwardLocal
import JacobianChallenge.Manifold.NormPushforwardGlobal
import JacobianChallenge.Manifold.FibreDisjointChartRadiusDecomposition
import JacobianChallenge.Manifold.RegularValueExistsRegUnconditional
import JacobianChallenge.Manifold.CriticalValuesFiniteGeneral
import JacobianChallenge.Manifold.CriticalSetClosed
import JacobianChallenge.Manifold.RamificationIndex

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # `NormFM_mmeromorphicAt` unconditional (Phase 1, ZZ214 direct)

This file closes the headline open obligation of Phase 1's norm-pushforward
chain: for non-constant `C^ω` `f : X → Y` between compact connected complex
1-manifolds and `g : MeromorphicNonzero X`, the global norm pushforward
`NormFM f hf hf_nc g : Y → ℂ` is meromorphic at every `y₀ : Y`.

The proof composes:
* `fibre_disjoint_chart_radius_decomposition` (ZZ211) — at any `y₀`, gives a
  finite preimage `hF`, per-`x` chart-radii `ε_x`, an open `V ∋ y₀`,
  pairwise-disjoint chart-disks `D_x`, `f ⁻¹' V ⊆ ⋃ D_x`, and per-fibre
  count `(f ⁻¹' {y} ∩ D_x).ncard = manifoldRamificationIndex f x` for
  `y ∈ V \ {y₀}`.
* `criticalValues_finite_general` (CV-Gen) — finiteness of the critical-value
  set, used to restrict to a punctured neighbourhood of `y₀` consisting only
  of regular values (where every preimage has ramification index 1).
* `deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood` (RVE) — at a non-
  critical preimage, the chart-pullback's derivative is nonzero. Combined
  with `AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero` from mathlib,
  this gives `analyticOrderAt = 1`, hence `manifoldRamificationIndex = 1`.

No new `Prop` bundles. No `_of_X` wrappers over fresh predicates. -/

@[expose] public section

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace JacobianChallenge
namespace Manifold

universe u v

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable {Y : Type v}
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-! ## Step 1: ramification index is 1 at a regular preimage. -/

/-- At a non-critical preimage of a non-critical value, the manifold
ramification index is `1`.

Chain: `x ∉ criticalSetGeneral f` ⟺ `∃ U ∈ 𝓝 x, InjOn f U`, then via
`deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood` (RVE) we get
the chart-pullback's derivative at `chart x` nonzero, then mathlib's
`analyticOrderAt_sub_eq_one_of_deriv_ne_zero` gives analytic order 1,
and the `toNat` collapses to `1`. -/
theorem manifoldRamificationIndex_eq_one_of_inj_on_neighbourhood
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (x : X)
    (h_inj : ∃ U ∈ 𝓝 x, Set.InjOn f U) :
    manifoldRamificationIndex f x = 1 := by
  classical
  have hF_an :
      AnalyticAt ℂ ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) :=
    JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback
      hf x
  have h_deriv_ne :
      deriv ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) ≠ 0 :=
    JacobianChallenge.ContMDiff.Owed.degree.deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood
      hf hnc x h_inj
  have h_ord :
      analyticOrderAt
        (fun z =>
          ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z -
          ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
        ((chartAt ℂ x) x) = 1 :=
    hF_an.analyticOrderAt_sub_eq_one_of_deriv_ne_zero h_deriv_ne
  show (analyticOrderAt _ _).toNat = 1
  rw [h_ord]
  rfl

/-- At a regular value (not in `criticalValuesGeneral f`), every preimage
has manifold ramification index `1`. -/
theorem manifoldRamificationIndex_eq_one_at_regular_value_preimage
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f)
    {y : Y} (hy : y ∉ criticalValuesGeneral f)
    {x : X} (hx : x ∈ f ⁻¹' {y}) :
    manifoldRamificationIndex f x = 1 := by
  apply manifoldRamificationIndex_eq_one_of_inj_on_neighbourhood hf hnc x
  -- y not a critical value ⇒ x not in critical set ⇒ ∃ nbhd InjOn.
  have hfx_eq : f x = y := hx
  have hx_not_crit : x ∉ criticalSetGeneral f := by
    intro hx_crit
    apply hy
    exact ⟨x, hx_crit, hfx_eq⟩
  by_contra h
  apply hx_not_crit
  show ¬ ∃ U ∈ 𝓝 x, Set.InjOn f U
  exact h

end Manifold
end JacobianChallenge

end
