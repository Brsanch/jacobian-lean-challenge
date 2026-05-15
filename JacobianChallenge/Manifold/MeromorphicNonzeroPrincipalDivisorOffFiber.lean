/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicExtensionValue
import JacobianChallenge.Manifold.MeromorphicDivisor
import JacobianChallenge.Divisor.PrincipalDivisor

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Principal divisor vanishes at non-zero non-pole points

At a point `z` where `f.toRiemannSphere z ∉ {some 0, ∞}`,
`(principalDivisorMap f).toFun z = 0`.

This is **step 7d-a** of the C3 staircase: the off-fiber case of the
identification between `∂(levelSetChain f β)` and `−principalDivisorMap f`
modulo the `Div ↔ Finsupp` bridge.

## Argument

* `f.toRS z ≠ ∞` gives `0 ≤ mmeromorphicOrderAt f.toFun z` via
  `toRiemannSphere_eq_infty_iff_neg`'s contrapositive.
* `f.regular_continuousAt z` (a field of `MeromorphicNonzero`) gives
  `ContinuousAt f.toFun z`.
* `f.toRS z ≠ some 0` combined with non-pole and continuity forces
  `f.toFun z ≠ 0` via `toRiemannSphere_eq_some_zero_iff`.
* `mathlib.tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero` then forces
  `meromorphicOrderAt (chart-pullback) (chart z) = 0`, which is exactly
  `mmeromorphicOrderAt f.toFun z = 0`.

## What ships

* `MeromorphicNonzero.principalDivisorMap_toFun_eq_zero_off_fiber`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Off-fiber vanishing of the principal divisor.**

If `f.toRiemannSphere z` is neither `some 0` nor `∞`, then
`(principalDivisorMap f).toFun z = 0`. -/
theorem principalDivisorMap_toFun_eq_zero_off_fiber
    (f : MeromorphicNonzero X) (z : X)
    (h_not_zero : f.toRiemannSphere z ≠ (OnePoint.some (0 : ℂ) : RiemannSphere))
    (h_not_pole : f.toRiemannSphere z ≠ (OnePoint.infty : RiemannSphere)) :
    (principalDivisorMap f : X → ℤ) z = 0 := by
  classical
  -- Step 1: 0 ≤ mmeromorphicOrderAt (from h_not_pole).
  have h_nonneg : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun z := by
    by_contra h_neg
    push Not at h_neg
    exact h_not_pole (f.toRiemannSphere_apply_of_neg h_neg)
  -- Step 2: f.toFun z ≠ 0 (from h_not_zero + step 1).
  have h_value_ne : f.toFun z ≠ 0 := by
    intro h_zero
    apply h_not_zero
    exact (f.toRiemannSphere_eq_some_zero_iff z).mpr ⟨h_nonneg, h_zero⟩
  -- Step 3: f.toFun is continuous at z (from regular_continuousAt + h_nonneg).
  have h_cont : ContinuousAt f.toFun z := f.regular_continuousAt z h_nonneg
  -- Step 4: reduce to mmeromorphicOrderAt = 0 via orderFun_eq_zero_iff.
  rw [principalDivisorMap_apply]
  rw [JacobianChallenge.MMeromorphicOn.orderFun_eq_zero_iff (f.nonvanishing_germ z)]
  -- Step 5: chart-pullback level. Set g := f.toFun ∘ chart.symm.
  show meromorphicOrderAt (f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) = 0
  -- The chart-pullback at chart z equals f.toFun z.
  have h_chart_value : (f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) = f.toFun z := by
    show f.toFun ((chartAt ℂ z).symm ((chartAt ℂ z) z)) = f.toFun z
    rw [(chartAt ℂ z).left_inv (mem_chart_source ℂ z)]
  -- Chart-pullback is MeromorphicAt at chart z (from f.meromorphic).
  have hf_mer : MeromorphicAt (f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) :=
    f.meromorphic z (Set.mem_univ z)
  -- Chart-pullback is continuous at chart z (from h_cont composed with chart.continuous_symm).
  have h_g_cont : ContinuousAt (f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) := by
    apply ContinuousAt.comp
    · rw [(chartAt ℂ z).left_inv (mem_chart_source ℂ z)]; exact h_cont
    · exact ((chartAt ℂ z).continuousOn_symm).continuousAt
        ((chartAt ℂ z).open_target.mem_nhds (mem_chart_target ℂ z))
  -- Tendsto g at 𝓝[≠] chart z to g (chart z) = f.toFun z ≠ 0.
  have h_tendsto : Tendsto (f.toFun ∘ (chartAt ℂ z).symm) (𝓝[≠] ((chartAt ℂ z) z))
      (𝓝 ((f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z))) :=
    h_g_cont.tendsto.mono_left nhdsWithin_le_nhds
  have h_value_ne' :
      (f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) ≠ 0 := by
    rw [h_chart_value]; exact h_value_ne
  -- Apply the iff.
  exact (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hf_mer).mp
    ⟨_, h_value_ne', h_tendsto⟩

end MeromorphicNonzero

end JacobianChallenge

end
