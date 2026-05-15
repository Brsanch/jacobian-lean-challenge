/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneForm
import JacobianChallenge.Manifold.HolomorphicOneFormRealification
import JacobianChallenge.Manifold.HolomorphicOneFormRealificationLinearity
import JacobianChallenge.Manifold.CotangentBundleSmoothness
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.Analytic

set_option diagnostics.threshold 100

/-! # Local coefficient of a holomorphic 1-form at a base point

For a holomorphic 1-form `om : HolomorphicOneForm X` on a complex
1-manifold `X` and a *base point* `y : X`, the *local coefficient*
`HolomorphicOneForm.localCoeff om y : ℂ → ℂ` is the chart-`y` frame
coefficient of `dz` of `om`, expressed as a function `ℂ → ℂ` via the
chart inverse `(chartAt ℂ y).symm`.

Concretely, the value at `z ∈ ℂ` is obtained by:
1. transporting `om.toFun ((chartAt ℂ y).symm z)` from the canonical
   chart at `(chartAt ℂ y).symm z` to the chart at `y`
   (cotangent-bundle coordinate change),
2. then evaluating the resulting cotangent vector at the tangent basis
   vector `1 : ℂ` (the chart-`y` frame's `∂/∂z` viewed via the model
   tangent fibre).

At `z = (chartAt ℂ y) y` (the chart image of the base point itself),
both charts coincide and the coord-change is the identity, giving
`localCoeff om y ((chartAt ℂ y) y) = om.eval y 1`.

At `z ∉ (chartAt ℂ y).target`, the value is junk (driven by
`OpenPartialHomeomorph.symm`'s default).

This is the foundational object for the elementary
Forster/Montel/Riesz proof of finite-dimensionality of
`HolomorphicOneForm X` on a compact complex 1-manifold: a finite
cover by base-point charts produces a seminorm on
`HolomorphicOneForm X`, with bounded sets locally equicontinuous by
Cauchy estimates on the chart pullback.

## Main definitions

* `HolomorphicOneForm.localCoeff om y : ℂ → ℂ` — the chart-`y` local
  coefficient.

## Main results

* `HolomorphicOneForm.localCoeff_zero / _add / _neg / _sub / _smul` —
  pointwise linearity in `om`.
* `HolomorphicOneForm.localCoeffₗ y : HolomorphicOneForm X →ₗ[ℂ]
  (ℂ → ℂ)` — bundled ℂ-linear map.
* `HolomorphicOneForm.localCoeff_contMDiffAt_chart_image` — at the
  chart image `(chartAt ℂ y) y`, the local coefficient is
  `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω` (= complex analytic at that point).
* `HolomorphicOneForm.localCoeff_analyticAt_chart_image` — corollary.

## Implementation

The coord-change definition is mathematically more robust than the
naive `om.eval (chart.symm z) 1` (which would mix chart frames at
different points of the chart, breaking smoothness for general `X`).

The chart-image ContMDiffAt at the single point `(chartAt ℂ y) y`
follows from the repo's `cotangentSection_contMDiffAt_iff` bridge
at base point `y`, composed with chart-symm smoothness and the
continuous-linear evaluation at `1 : ℂ`. The composed function on
`ℂ` is identified with `localCoeff om y` pointwise.

Smoothness on the whole chart target — needed for Cauchy estimates
over a closed disk — requires a cocycle argument (transporting the
chart-coord representative at arbitrary `y'` back to chart-`y` frame
via the cotangent transition). That extension is a downstream chip;
the chart-image ContMDiffAt provided here is the foundational
single-point step.

The linearity proofs use the standard CLM linearity lemmas
(`ContinuousLinearMap.map_add`, `_neg`, `_sub`, `_smul` and
`ContinuousLinearMap.add_apply`, `_neg_apply`, `_sub_apply`,
`_smul_apply`), unfolded through helper lemmas to avoid
elaboration issues with the nested CLM application.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace HolomorphicOneForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-! ## Helper lemma for double CLM application -/

private lemma clm_apply_apply_add
    (f : (ℂ →L[ℂ] ℂ) →L[ℂ] (ℂ →L[ℂ] ℂ)) (v₁ v₂ : ℂ →L[ℂ] ℂ) (e : ℂ) :
    (f (v₁ + v₂)) e = (f v₁) e + (f v₂) e := by
  rw [ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply]

private lemma clm_apply_apply_neg
    (f : (ℂ →L[ℂ] ℂ) →L[ℂ] (ℂ →L[ℂ] ℂ)) (v : ℂ →L[ℂ] ℂ) (e : ℂ) :
    (f (-v)) e = -((f v) e) := by
  rw [ContinuousLinearMap.map_neg, ContinuousLinearMap.neg_apply]

private lemma clm_apply_apply_sub
    (f : (ℂ →L[ℂ] ℂ) →L[ℂ] (ℂ →L[ℂ] ℂ)) (v₁ v₂ : ℂ →L[ℂ] ℂ) (e : ℂ) :
    (f (v₁ - v₂)) e = (f v₁) e - (f v₂) e := by
  rw [ContinuousLinearMap.map_sub, ContinuousLinearMap.sub_apply]

private lemma clm_apply_apply_smul
    (f : (ℂ →L[ℂ] ℂ) →L[ℂ] (ℂ →L[ℂ] ℂ)) (c : ℂ) (v : ℂ →L[ℂ] ℂ) (e : ℂ) :
    (f (c • v)) e = c * (f v) e := by
  rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply]
  rfl

private lemma clm_apply_apply_zero
    (f : (ℂ →L[ℂ] ℂ) →L[ℂ] (ℂ →L[ℂ] ℂ)) (e : ℂ) :
    (f 0) e = 0 := by
  rw [map_zero, ContinuousLinearMap.zero_apply]

/-! ## Definition -/

/-- The chart-`y` local coefficient of a holomorphic 1-form `om` on a
complex 1-manifold `X`, expressed as a function `ℂ → ℂ`.

At `z ∈ (chartAt ℂ y).target`, this is the coefficient of `dz` of
`om` in chart `chartAt ℂ y` — formally, the cotangent bundle's
transport of `om.toFun ((chartAt ℂ y).symm z)` from the canonical
chart at that point to the chart at `y`, evaluated at the tangent
basis vector `1 : ℂ`.

At `z ∉ (chartAt ℂ y).target`, the value is junk. Downstream
regularity statements are over `(chartAt ℂ y).target`. -/
def localCoeff (om : HolomorphicOneForm X) (y : X) : ℂ → ℂ :=
  fun z =>
    ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ ((chartAt ℂ y).symm z)) (achart ℂ y)
        ((chartAt ℂ y).symm z) (om.toFun ((chartAt ℂ y).symm z))) 1

/-! ## Pointwise linearity in `om` -/

@[simp]
theorem localCoeff_zero (y : X) :
    localCoeff (0 : HolomorphicOneForm X) y = 0 := by
  funext z
  show ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
      (achart ℂ ((chartAt ℂ y).symm z)) (achart ℂ y)
      ((chartAt ℂ y).symm z)
      ((0 : HolomorphicOneForm X).toFun ((chartAt ℂ y).symm z))) 1 = 0
  have h_zero : (0 : HolomorphicOneForm X).toFun ((chartAt ℂ y).symm z)
      = (0 : ℂ →L[ℂ] ℂ) := eval_zero _
  rw [h_zero]
  exact clm_apply_apply_zero _ _

theorem localCoeff_add (om₁ om₂ : HolomorphicOneForm X) (y : X) :
    localCoeff (om₁ + om₂) y = localCoeff om₁ y + localCoeff om₂ y := by
  funext z
  show ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
      (achart ℂ ((chartAt ℂ y).symm z)) (achart ℂ y)
      ((chartAt ℂ y).symm z)
      ((om₁ + om₂).toFun ((chartAt ℂ y).symm z))) 1
      = ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ ((chartAt ℂ y).symm z)) (achart ℂ y)
          ((chartAt ℂ y).symm z)
          (om₁.toFun ((chartAt ℂ y).symm z))) 1
        + ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
            (achart ℂ ((chartAt ℂ y).symm z)) (achart ℂ y)
            ((chartAt ℂ y).symm z)
            (om₂.toFun ((chartAt ℂ y).symm z))) 1
  have h_add : (om₁ + om₂).toFun ((chartAt ℂ y).symm z)
      = om₁.toFun ((chartAt ℂ y).symm z) + om₂.toFun ((chartAt ℂ y).symm z) :=
    eval_add _ _ _
  rw [h_add]
  exact clm_apply_apply_add _ _ _ _

theorem localCoeff_neg (om : HolomorphicOneForm X) (y : X) :
    localCoeff (-om) y = -localCoeff om y := by
  funext z
  show ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
      (achart ℂ ((chartAt ℂ y).symm z)) (achart ℂ y)
      ((chartAt ℂ y).symm z)
      ((-om).toFun ((chartAt ℂ y).symm z))) 1
      = -((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ ((chartAt ℂ y).symm z)) (achart ℂ y)
          ((chartAt ℂ y).symm z)
          (om.toFun ((chartAt ℂ y).symm z))) 1
  have h_neg : (-om).toFun ((chartAt ℂ y).symm z)
      = -(om.toFun ((chartAt ℂ y).symm z)) := eval_neg _ _
  rw [h_neg]
  exact clm_apply_apply_neg _ _ _

theorem localCoeff_sub (om₁ om₂ : HolomorphicOneForm X) (y : X) :
    localCoeff (om₁ - om₂) y = localCoeff om₁ y - localCoeff om₂ y := by
  funext z
  show ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
      (achart ℂ ((chartAt ℂ y).symm z)) (achart ℂ y)
      ((chartAt ℂ y).symm z)
      ((om₁ - om₂).toFun ((chartAt ℂ y).symm z))) 1
      = ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ ((chartAt ℂ y).symm z)) (achart ℂ y)
          ((chartAt ℂ y).symm z)
          (om₁.toFun ((chartAt ℂ y).symm z))) 1
        - ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
            (achart ℂ ((chartAt ℂ y).symm z)) (achart ℂ y)
            ((chartAt ℂ y).symm z)
            (om₂.toFun ((chartAt ℂ y).symm z))) 1
  have h_sub : (om₁ - om₂).toFun ((chartAt ℂ y).symm z)
      = om₁.toFun ((chartAt ℂ y).symm z) - om₂.toFun ((chartAt ℂ y).symm z) :=
    eval_sub _ _ _
  rw [h_sub]
  exact clm_apply_apply_sub _ _ _ _

theorem localCoeff_smul (c : ℂ) (om : HolomorphicOneForm X) (y : X) :
    localCoeff (c • om) y = c • localCoeff om y := by
  funext z
  show ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
      (achart ℂ ((chartAt ℂ y).symm z)) (achart ℂ y)
      ((chartAt ℂ y).symm z)
      ((c • om).toFun ((chartAt ℂ y).symm z))) 1
      = c • ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ ((chartAt ℂ y).symm z)) (achart ℂ y)
          ((chartAt ℂ y).symm z)
          (om.toFun ((chartAt ℂ y).symm z))) 1
  have h_smul : (c • om).toFun ((chartAt ℂ y).symm z)
      = c • om.toFun ((chartAt ℂ y).symm z) := eval_smul _ _ _
  rw [h_smul]
  -- Use CLM linearity in two steps via named intermediate.
  have step1 : ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ ((chartAt ℂ y).symm z)) (achart ℂ y)
        ((chartAt ℂ y).symm z))
        (c • om.toFun ((chartAt ℂ y).symm z))
      = c • ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ ((chartAt ℂ y).symm z)) (achart ℂ y)
          ((chartAt ℂ y).symm z)) (om.toFun ((chartAt ℂ y).symm z)) :=
    ContinuousLinearMap.map_smul _ _ _
  rw [step1]
  exact ContinuousLinearMap.smul_apply _ _ _

/-! ### As a `ℂ`-linear map `HolomorphicOneForm X →ₗ[ℂ] (ℂ → ℂ)`. -/

/-- The local coefficient at base point `y` as a ℂ-linear map. -/
def localCoeffₗ (y : X) : HolomorphicOneForm X →ₗ[ℂ] (ℂ → ℂ) where
  toFun om := localCoeff om y
  map_add' om₁ om₂ := localCoeff_add om₁ om₂ y
  map_smul' c om := localCoeff_smul c om y

@[simp]
theorem localCoeffₗ_apply (y : X) (om : HolomorphicOneForm X) :
    localCoeffₗ y om = localCoeff om y := rfl

/-! ## Smoothness at the chart image of the base point -/

/-- Auxiliary: the *raw* chart-coordinate representative of a section
`om : HolomorphicOneForm X` in chart `achart ℂ y`, as a function
`X → ℂ →L[ℂ] ℂ`. -/
private noncomputable def chartFiberRepr
    (om : HolomorphicOneForm X) (y : X) : X → (ℂ →L[ℂ] ℂ) :=
  fun x =>
    (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
      (achart ℂ x) (achart ℂ y) x (om.toFun x)

/-- The raw chart-coordinate representative is `ContMDiffAt` at the
base point `y`, via the repo's existing cotangent-section bridge. -/
private lemma chartFiberRepr_contMDiffAt_basePoint
    (om : HolomorphicOneForm X) (y : X) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (chartFiberRepr om y) y := by
  have h_om : ContMDiffAt 𝓘(ℂ, ℂ) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun x : X => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) x (om.toFun x)) y :=
    om.contMDiff.contMDiffAt
  rw [cotangentSection_contMDiffAt_iff (om.toFun)] at h_om
  exact h_om

/-- Auxiliary: smoothness of `(· 1) : (ℂ →L[ℂ] ℂ) → ℂ` as a
self-modelled `ContMDiff` map. -/
private lemma contMDiff_apply_one :
    ContMDiff 𝓘(ℂ, ℂ →L[ℂ] ℂ) 𝓘(ℂ, ℂ) ω
      (fun T : ℂ →L[ℂ] ℂ => T 1) := by
  have h : ContMDiff 𝓘(ℂ, ℂ →L[ℂ] ℂ) 𝓘(ℂ, ℂ) ω
      (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)) :=
    (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).contMDiff
  have h_eq : (fun T : ℂ →L[ℂ] ℂ => T 1)
      = (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)) := by
    funext T
    simp [ContinuousLinearMap.apply_apply]
  rw [h_eq]
  exact h

/-- The local coefficient is `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω` at the chart
image `(chartAt ℂ y) y` of the base point. -/
theorem localCoeff_contMDiffAt_chart_image (om : HolomorphicOneForm X)
    (y : X) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (localCoeff om y) ((chartAt ℂ y) y) := by
  -- chart-symm smoothness at `(chartAt ℂ y) y`.
  have h_chart_y_in_target : (chartAt ℂ y) y ∈ (chartAt ℂ y).target :=
    (chartAt ℂ y).map_source (mem_chart_source _ y)
  have h_symm_on : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      ((chartAt ℂ y).symm : ℂ → X) (chartAt ℂ y).target :=
    contMDiffOn_chart_symm (I := 𝓘(ℂ, ℂ)) (n := ω) (x := y)
  have h_symm_at : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      ((chartAt ℂ y).symm : ℂ → X) ((chartAt ℂ y) y) :=
    h_symm_on.contMDiffAt ((chartAt ℂ y).open_target.mem_nhds h_chart_y_in_target)
  -- chart-fiber repr smooth at y.
  have h_repr_at : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (chartFiberRepr om y) y :=
    chartFiberRepr_contMDiffAt_basePoint om y
  -- (chartAt y).symm ((chartAt y) y) = y.
  have h_chart_inv : (chartAt ℂ y).symm ((chartAt ℂ y) y) = y :=
    (chartAt ℂ y).left_inv (mem_chart_source _ y)
  -- chart-fiber repr smooth at (chart.symm (chart y)).
  have h_repr_at' : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (chartFiberRepr om y) ((chartAt ℂ y).symm ((chartAt ℂ y) y)) := by
    rw [h_chart_inv]; exact h_repr_at
  -- Compose: chart-fiber repr ∘ chart-symm smooth at chart y.
  have h_comp_at : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun w : ℂ => chartFiberRepr om y ((chartAt ℂ y).symm w))
      ((chartAt ℂ y) y) := by
    have := h_repr_at'.comp ((chartAt ℂ y) y) h_symm_at
    simpa [Function.comp_def] using this
  -- Apply (· 1).
  have h_final_at : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun w : ℂ => (chartFiberRepr om y ((chartAt ℂ y).symm w)) 1)
      ((chartAt ℂ y) y) :=
    contMDiff_apply_one.contMDiffAt.comp ((chartAt ℂ y) y) h_comp_at
  -- Identify with `localCoeff om y` pointwise.
  have h_eq : (fun w : ℂ => (chartFiberRepr om y ((chartAt ℂ y).symm w)) 1)
      = localCoeff om y := by
    funext w
    rfl
  rw [h_eq] at h_final_at
  exact h_final_at

/-! ## Analytic corollary at the chart image -/

/-- The local coefficient is `AnalyticAt ℂ` at the chart image of
the base point. -/
theorem localCoeff_analyticAt_chart_image (om : HolomorphicOneForm X)
    (y : X) :
    AnalyticAt ℂ (localCoeff om y) ((chartAt ℂ y) y) := by
  have h_contMDiff := localCoeff_contMDiffAt_chart_image om y
  have h_contDiff : ContDiffAt ℂ ω (localCoeff om y) ((chartAt ℂ y) y) :=
    contMDiffAt_iff_contDiffAt.mp h_contMDiff
  rw [← contDiffWithinAt_univ] at h_contDiff
  rw [contDiffWithinAt_omega_iff_analyticWithinAt] at h_contDiff
  rwa [analyticWithinAt_univ] at h_contDiff

/-- The local coefficient is `DifferentiableAt ℂ` at the chart image of
the base point. -/
theorem localCoeff_differentiableAt_chart_image (om : HolomorphicOneForm X)
    (y : X) :
    DifferentiableAt ℂ (localCoeff om y) ((chartAt ℂ y) y) :=
  (localCoeff_analyticAt_chart_image om y).differentiableAt

end HolomorphicOneForm

end
