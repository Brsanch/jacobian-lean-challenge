/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphereChartCoefficients

/-! # Vanishing of chart coefficients implies vanishing of the 1-form

Given `om : HolomorphicOneForm RiemannSphere`, the two chart coefficient
maps `chartNCoeff om, chartSCoeff om : ℂ → ℂ` (from
`RiemannSphereChartCoefficients.lean`) together capture the full content
of `om`. The cotangent fibre at each point of the Riemann sphere is
`ℂ →L[ℂ] ℂ`, which is determined by its value at `1 : ℂ` because a
continuous `ℂ`-linear map `L : ℂ →L[ℂ] ℂ` satisfies `L z = z * L 1`.

If both chart coefficients vanish identically, then `om = 0`.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

namespace RiemannSphere

/-! ### Algebraic preliminary -/

/-- A continuous `ℂ`-linear map from `ℂ` to `ℂ` vanishing at `1` is zero. -/
theorem cotangent_eq_zero_of_apply_one_zero (L : ℂ →L[ℂ] ℂ) (h : L 1 = 0) :
    L = 0 := by
  refine ContinuousLinearMap.ext (fun z => ?_)
  have hz : L z = z • L 1 := by
    have : L z = L (z • (1 : ℂ)) := by rw [smul_eq_mul, mul_one]
    rw [this, map_smul]
  rw [hz, h, smul_zero]
  rfl

/-- Pointwise form: the evaluation of a holomorphic 1-form at a point
vanishes iff its application to `1` vanishes. -/
theorem eval_eq_zero_iff_apply_one_zero
    (om : HolomorphicOneForm RiemannSphere) (x : RiemannSphere) :
    om.eval x = 0 ↔ om.eval x 1 = 0 :=
  ⟨fun h => by rw [h]; rfl,
   fun h => cotangent_eq_zero_of_apply_one_zero (om.eval x) h⟩

/-- A `HolomorphicOneForm RiemannSphere` is zero iff its underlying
`eval` is zero at every point. -/
theorem eq_zero_iff_eval_eq_zero (om : HolomorphicOneForm RiemannSphere) :
    om = 0 ↔ ∀ x : RiemannSphere, om.eval x = 0 := by
  refine ⟨fun h x => ?_, fun h => ?_⟩
  · rw [h]; exact HolomorphicOneForm.eval_zero x
  · -- Use DFunLike.ext on the underlying ContMDiffSection.
    let s :
        ContMDiffSection (𝕜 := ℂ) (E := ℂ) (H := ℂ) (M := RiemannSphere)
          𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω (CotangentSpace 𝓘(ℂ) : RiemannSphere → Type _) :=
      om
    show s = (0 :
        ContMDiffSection (𝕜 := ℂ) (E := ℂ) (H := ℂ) (M := RiemannSphere)
          𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω (CotangentSpace 𝓘(ℂ) : RiemannSphere → Type _))
    refine DFunLike.ext _ _ (fun x => ?_)
    have hx : s x = om.eval x := rfl
    have h0 :
        ((0 : ContMDiffSection (𝕜 := ℂ) (E := ℂ) (H := ℂ) (M := RiemannSphere)
            𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω
            (CotangentSpace 𝓘(ℂ) : RiemannSphere → Type _))) x = 0 := by
      rw [ContMDiffSection.coe_zero]
      rfl
    rw [hx, h0]
    exact h x

/-! ### Main vanishing theorem -/

/-- **Key bridge.** If both chart coefficients of a holomorphic 1-form
on the Riemann sphere vanish identically, then the form is zero. -/
theorem eq_zero_of_chartCoeff_vanishing
    {om : HolomorphicOneForm RiemannSphere}
    (hN : chartNCoeff om = 0) (hS : chartSCoeff om = 0) :
    om = 0 := by
  rw [eq_zero_iff_eval_eq_zero]
  intro x
  rw [eval_eq_zero_iff_apply_one_zero]
  -- Case split on whether `x = ∞` using `OnePoint.rec`.
  induction x using OnePoint.rec with
  | infty =>
    have := congrFun hS 0
    rw [chartSCoeff_zero_apply] at this
    simpa using this
  | coe z =>
    have := congrFun hN z
    rw [chartNCoeff_apply] at this
    simpa using this

end RiemannSphere

end JacobianChallenge

end
