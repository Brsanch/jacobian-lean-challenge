/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.PompeiuKernelCauchyPompeiu
import JacobianChallenge.Analysis.PompeiuKernelSmoothness
import JacobianChallenge.Manifold.PartialZBarManifold
import JacobianChallenge.Manifold.PartialZBarChainRule
import JacobianChallenge.Manifold.MeromorphicAt

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Chip 4 — chart-pullback of the Pompeiu kernel

The Cauchy-Pompeiu identity on ℂ (Chip 3c-F-4,
`partialZBar_pompeiuKernel_eq_self`) is the analytic engine. Chip 4
lifts it to the manifold side: for a chart `chartAt ℂ x : X ⊃ U → V ⊆ ℂ`
and a function `α : X → ℂ` whose chart-pullback `α ∘ chart.symm`
is `C¹` with compact support inside the chart's target, define

```
pompeiuKernelChart x α : X → ℂ :=
  fun y => pompeiuKernel (α ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y).
```

The function lives on all of `X`, and inside `(chartAt ℂ x).source` it
satisfies the **chart-x view of the ∂̄ identity**:

```
partialZBar (pompeiuKernelChart x α ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)
  = α y    for every y ∈ (chartAt ℂ x).source.
```

At the basepoint `x` itself, this collapses to the manifold-level
identity `partialZBarManifold (pompeiuKernelChart x α) x = α x` (since
`extChartAt 𝓘(ℂ, ℂ) x = chartAt ℂ x` modulo the trivial model, and
the construction chart equals the canonical chart at `x`).

This is the local input for Chip 5 (genus-0 globalization). Chip 5
patches these local solutions via a partition of unity plus the
Behnke-Stein spreading-function correction, producing a global
∂̄-inverse on every genus-0 compact Riemann surface.

## What this file ships

* `pompeiuKernelChart x α : X → ℂ` — chart-pullback definition.
* `pompeiuKernelChart_smul`, `pompeiuKernelChart_add`,
  `pompeiuKernelChart_neg` — algebraic preservation.
* `pompeiuKernelChart_eq_on_chart_source` — restatement helper.
* `partialZBar_pompeiuKernelChart_eq_α_on_chart_source` —
  the **chart-x view local identity**: ∂̄ (chart-x pullback of u) at
  chart_x y equals α y, for y in chart_x.source.
* `partialZBarManifold_pompeiuKernelChart_at_basepoint` —
  the **manifold-level identity at the basepoint**: ∂̄_man u x = α x.

All sorry-free, axiom-free. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex Filter Set

namespace JacobianChallenge.PompeiuKernel

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ## Construction of the chart-pulled Pompeiu kernel -/

/-- The chart-pulled Pompeiu kernel at base point `x : X` applied to
`α : X → ℂ`. The result is a function `X → ℂ` computed by:

1. Pull `α` through `(chartAt ℂ x).symm` to get `α ∘ chart.symm : ℂ → ℂ`.
2. Apply the Pompeiu kernel `pompeiuKernel : (ℂ → ℂ) → ℂ → ℂ`.
3. Compose with `chartAt ℂ x : X → ℂ` to land back on `X`.

Equivalently, the value at `y : X` is
`pompeiuKernel (α ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)`. -/
def pompeiuKernelChart (x : X) (α : X → ℂ) : X → ℂ :=
  fun y => pompeiuKernel (α ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)

/-! ## Algebraic preservation lemmas -/

/-- `pompeiuKernelChart` is additive in `α` for `C¹` compactly-supported
chart-pullbacks (using `pompeiuKernel_add`). -/
lemma pompeiuKernelChart_add (x : X) {α β : X → ℂ}
    (h_α_cont : Continuous (α ∘ (chartAt ℂ x).symm))
    (h_α_cs : HasCompactSupport (α ∘ (chartAt ℂ x).symm))
    (h_β_cont : Continuous (β ∘ (chartAt ℂ x).symm))
    (h_β_cs : HasCompactSupport (β ∘ (chartAt ℂ x).symm)) :
    pompeiuKernelChart x (α + β) = pompeiuKernelChart x α + pompeiuKernelChart x β := by
  funext y
  unfold pompeiuKernelChart
  have h_chart_add :
      ((α + β) ∘ (chartAt ℂ x).symm)
        = ((α ∘ (chartAt ℂ x).symm)) + ((β ∘ (chartAt ℂ x).symm)) := by
    funext z; rfl
  rw [h_chart_add]
  rw [pompeiuKernel_add h_α_cont h_α_cs h_β_cont h_β_cs]
  rfl

/-- `pompeiuKernelChart` is linear in `α` under constant ℂ-scalar
multiplication. -/
lemma pompeiuKernelChart_const_mul (x : X) (c : ℂ) (α : X → ℂ) :
    pompeiuKernelChart x (fun y => c * α y)
      = fun y => c * pompeiuKernelChart x α y := by
  funext y
  unfold pompeiuKernelChart
  have h_chart_mul :
      ((fun y' : X => c * α y') ∘ (chartAt ℂ x).symm)
        = fun z => c * ((α ∘ (chartAt ℂ x).symm) z) := by
    funext z; rfl
  rw [h_chart_mul]
  exact pompeiuKernel_const_mul c (α ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)

/-- Pointwise restatement of `pompeiuKernelChart` for `y ∈ chart.source`. -/
lemma pompeiuKernelChart_apply (x : X) (α : X → ℂ) (y : X) :
    pompeiuKernelChart x α y
      = pompeiuKernel (α ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y) := rfl

/-! ## Chart-x view of `∂̄` of the chart-pulled Pompeiu kernel -/

/-- The chart-x pullback of `pompeiuKernelChart x α` along
`(chartAt ℂ x).symm`, restricted to `(chartAt ℂ x).target`, equals
`pompeiuKernel (α ∘ (chartAt ℂ x).symm)`.

This is the trivial composition identity that lets us drop the chart
wrappings when computing `∂̄` in chart-x view (no `extChartAt`-vs-`chartAt`
or model-`id` issues since the chart-x view is the "natural" frame). -/
lemma pompeiuKernelChart_comp_chart_symm_eq
    (x : X) (α : X → ℂ) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target) :
    (pompeiuKernelChart x α ∘ (chartAt ℂ x).symm) z
      = pompeiuKernel (α ∘ (chartAt ℂ x).symm) z := by
  unfold pompeiuKernelChart
  show pompeiuKernel (α ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) ((chartAt ℂ x).symm z)) = _
  rw [(chartAt ℂ x).right_inv hz]

/-- Stronger: the two compositions agree on the entire open neighborhood
`(chartAt ℂ x).target`. -/
lemma pompeiuKernelChart_eventuallyEq_pompeiuKernel
    (x : X) (α : X → ℂ) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target) :
    (pompeiuKernelChart x α ∘ (chartAt ℂ x).symm)
      =ᶠ[nhds z] pompeiuKernel (α ∘ (chartAt ℂ x).symm) := by
  refine Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨(chartAt ℂ x).target, (chartAt ℂ x).open_target.mem_nhds hz, ?_⟩
  intro w hw
  exact pompeiuKernelChart_comp_chart_symm_eq x α hw

/-! ## Chart-x view of the local `∂̄` identity -/

/-- **Chip 4 — chart-x view local identity.** For `y ∈ (chartAt ℂ x).source`,
the chart-x view of the antiholomorphic derivative of
`pompeiuKernelChart x α` at the chart-x image of `y` equals `α y`,
provided `α ∘ (chartAt ℂ x).symm` is `C¹` and compactly supported.

This is the direct chart-frame consequence of Chip 3c-F-4's
unconditional Cauchy-Pompeiu identity on ℂ:
`partialZBar (pompeiuKernel γ) z = γ z` at `z := (chartAt ℂ x) y`,
with `γ := α ∘ (chartAt ℂ x).symm` and using `chartAt ℂ x).left_inv` to
turn `γ ((chartAt ℂ x) y) = α (chart.symm (chart y))` into `α y`. -/
theorem partialZBar_pompeiuKernelChart_eq_α_on_chart_source
    (x : X) (α : X → ℂ)
    (h_α_smooth : ContDiff ℝ 1 (α ∘ (chartAt ℂ x).symm))
    (h_α_cs : HasCompactSupport (α ∘ (chartAt ℂ x).symm))
    {y : X} (h_y_in : y ∈ (chartAt ℂ x).source) :
    partialZBar (pompeiuKernelChart x α ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) y)
      = α y := by
  -- Eventual equality of `pompeiuKernelChart x α ∘ chart.symm` and
  -- `pompeiuKernel (α ∘ chart.symm)` on a neighborhood of `(chart) y`.
  have h_target : (chartAt ℂ x) y ∈ (chartAt ℂ x).target :=
    (chartAt ℂ x).map_source h_y_in
  have h_evEq := pompeiuKernelChart_eventuallyEq_pompeiuKernel x α h_target
  -- `partialZBar` only depends on local values (via `fderiv`), so transport.
  have h_pZ_eq :
      partialZBar (pompeiuKernelChart x α ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)
        = partialZBar (pompeiuKernel (α ∘ (chartAt ℂ x).symm)) ((chartAt ℂ x) y) := by
    unfold partialZBar
    rw [Filter.EventuallyEq.fderiv_eq h_evEq]
  rw [h_pZ_eq]
  -- Apply Chip 3c-F-4 (unconditional Cauchy-Pompeiu on ℂ).
  rw [partialZBar_pompeiuKernel_eq_self h_α_smooth h_α_cs ((chartAt ℂ x) y)]
  -- Goal: (α ∘ chart.symm) (chart y) = α y.
  show α ((chartAt ℂ x).symm ((chartAt ℂ x) y)) = α y
  rw [(chartAt ℂ x).left_inv h_y_in]

/-! ## Smoothness of the chart-pulled Pompeiu kernel -/

/-- **Chip 4 — smoothness of the chart-pullback of the Pompeiu kernel.**
For `α ∘ chart.symm ∈ C^∞` with compact support, the function
`pompeiuKernelChart x α ∘ (chartAt ℂ x).symm` is `C^∞` on a
neighborhood of every point of `(chartAt ℂ x).target` — in fact globally
`C^∞` on `ℂ` because the eventual equality with `pompeiuKernel _` holds
on the open set `(chartAt ℂ x).target`, and the smoothness of
`pompeiuKernel _` is global (Chip 2d's
`contDiff_pompeiuKernel_infty`). -/
theorem contDiffOn_pompeiuKernelChart_chart_symm
    (x : X) (α : X → ℂ)
    (h_α_smooth : ContDiff ℝ ∞ (α ∘ (chartAt ℂ x).symm))
    (h_α_cs : HasCompactSupport (α ∘ (chartAt ℂ x).symm)) :
    ContDiffOn ℝ ∞ (pompeiuKernelChart x α ∘ (chartAt ℂ x).symm)
      (chartAt ℂ x).target := by
  -- The two functions agree on `(chartAt ℂ x).target`, an open set.
  intro z hz
  -- Use ContDiffAt at `z`, then `.contDiffWithinAt`.
  have h_evEq := pompeiuKernelChart_eventuallyEq_pompeiuKernel x α hz
  have h_global :
      ContDiffAt ℝ ∞ (pompeiuKernel (α ∘ (chartAt ℂ x).symm)) z :=
    (contDiff_pompeiuKernel_infty h_α_smooth h_α_cs).contDiffAt
  have h_at : ContDiffAt ℝ ∞ (pompeiuKernelChart x α ∘ (chartAt ℂ x).symm) z :=
    h_global.congr_of_eventuallyEq h_evEq
  exact h_at.contDiffWithinAt

/-! ## Manifold-level identity at the basepoint -/

/-- **Chip 4 — manifold-level identity at the basepoint.** Because
`extChartAt 𝓘(ℂ, ℂ) x = chartAt ℂ x` (modulo the trivial model `𝓘(ℂ, ℂ)`),
the manifold-side `partialZBarManifold` evaluated at the basepoint `x`
coincides with the chart-x view; combined with
`partialZBar_pompeiuKernelChart_eq_α_on_chart_source` at `y := x`, this
gives the manifold identity at `x`. -/
theorem partialZBarManifold_pompeiuKernelChart_at_basepoint
    (x : X) (α : X → ℂ)
    (h_α_smooth : ContDiff ℝ 1 (α ∘ (chartAt ℂ x).symm))
    (h_α_cs : HasCompactSupport (α ∘ (chartAt ℂ x).symm)) :
    JacobianChallenge.partialZBarManifold (pompeiuKernelChart x α) x = α x := by
  -- Unfold partialZBarManifold via extChartAt.
  unfold JacobianChallenge.partialZBarManifold
  -- extChartAt 𝓘(ℂ, ℂ) x reduces to chartAt ℂ x via the trivial model.
  -- Use the chart-x view local identity at y := x (which is in chart.source).
  have h_x_in : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  -- Rewrite the goal in terms of (chartAt ℂ x).
  have h_ext_apply : (extChartAt 𝓘(ℂ, ℂ) x) x = (chartAt ℂ x) x := by
    rw [extChartAt_coe]; rfl
  have h_ext_symm :
      ((extChartAt 𝓘(ℂ, ℂ) x).symm : ℂ → X) = (chartAt ℂ x).symm := by
    funext z
    rw [extChartAt_coe_symm]; rfl
  rw [h_ext_symm, h_ext_apply]
  exact partialZBar_pompeiuKernelChart_eq_α_on_chart_source x α h_α_smooth h_α_cs h_x_in

/-! ## Manifold-level identity at any y in chart_x.source (with chart-transition factor)

For `y ∈ (chartAt ℂ x).source` but `y ≠ x` (in general), the manifold
`∂̄` uses the **canonical** chart `chartAt ℂ y`, which differs from the
construction chart `chartAt ℂ x` by a holomorphic chart transition
`Φ_yx := (chartAt ℂ y) ∘ (chartAt ℂ x).symm`. The chain rule for `∂̄`
(`partialZBar_comp_of_differentiableAt`) inserts a `conj (deriv Φ_yx)`
factor.

This is the "Jacobian correction" that the genus-0 globalization
(Chip 5) absorbs via partition-of-unity averaging plus the Behnke-Stein
spreading-function technique. -/

section ManifoldIdentityWithTransition
variable [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- Local scalar-tower workaround for restricting ℂ-differentiability to
ℝ-differentiability on `ℂ → ℂ` (dodges the `IsScalarTower ℝ ℂ ℂ`
synthesis diamond, mirroring the private wrapper in
`Manifold/PartialZBarChainRule.lean`). -/
@[reducible] private def isScalarTower_R_C_C_local : IsScalarTower ℝ ℂ ℂ :=
  ⟨fun (r : ℝ) (c c' : ℂ) => by
    show (r • c) • c' = r • c • c'
    rw [smul_assoc]⟩

/-- Wrapper for `DifferentiableAt.restrictScalars ℝ` with explicit
`IsScalarTower ℝ ℂ ℂ` instance. -/
private theorem differentiableAt_restrictScalars_R_C_C_local
    {f : ℂ → ℂ} {x : ℂ} (h : DifferentiableAt ℂ f x) :
    DifferentiableAt ℝ f x :=
  @DifferentiableAt.restrictScalars ℝ _ ℂ _ _ ℂ _ _ _ isScalarTower_R_C_C_local
    ℂ _ _ _ isScalarTower_R_C_C_local _ _ h

/-- **Chart-x view → manifold-side bridge (general y).** For any
`y ∈ (chartAt ℂ x).source` with `(chartAt ℂ x).symm`-pullback
`ℝ`-differentiable at `(chartAt ℂ x) y` (e.g. `C¹` from
`h_α_smooth`-style hypotheses), the chart-x view of `partialZBar` is
the chart-y `partialZBarManifold` times the chain-rule factor
`conj(deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y))`.

This is the unconditional bridge underlying the manifold-side analogue
of Chip 4's chart-x view identity. -/
lemma partialZBar_chart_x_eq_manifold_mul_transition
    {f : X → ℂ} {x y : X}
    (h_y_in : y ∈ (chartAt ℂ x).source)
    (h_f_diff_y : DifferentiableAt ℝ (f ∘ (chartAt ℂ y).symm)
                    ((chartAt ℂ y) y)) :
    partialZBar (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)
      = JacobianChallenge.partialZBarManifold f y *
          (starRingEnd ℂ)
            (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)) := by
  -- Atlas and source memberships.
  have h_x_atlas : chartAt ℂ x ∈ atlas ℂ X := chart_mem_atlas ℂ x
  have h_y_atlas : chartAt ℂ y ∈ atlas ℂ X := chart_mem_atlas ℂ y
  have h_y_in_ysrc : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  -- Chart transition `(chartAt ℂ y) ∘ (chartAt ℂ x).symm` is ℂ-analytic at `(chart_x y)`.
  have h_an_trans : AnalyticAt ℂ ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) y) :=
    JacobianChallenge.analyticAt_chart_transition_of_isManifold
      h_x_atlas h_y_atlas h_y_in h_y_in_ysrc
  have h_Φ_diff : DifferentiableAt ℂ ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) y) := h_an_trans.differentiableAt
  -- Transition's value at chart_x y equals chart_y y.
  have h_trans_apply : ((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)
      = (chartAt ℂ y) y := by
    change (chartAt ℂ y) ((chartAt ℂ x).symm ((chartAt ℂ x) y))
        = (chartAt ℂ y) y
    rw [(chartAt ℂ x).left_inv h_y_in]
  -- Eventual equality (same as in PartialZBarManifoldChartPullbackVanish).
  have h_pre_open : IsOpen ((chartAt ℂ x).target ∩
      (chartAt ℂ x).symm ⁻¹' (chartAt ℂ y).source) :=
    (chartAt ℂ x).isOpen_inter_preimage_symm (chartAt ℂ y).open_source
  have h_x_target_mem : (chartAt ℂ x) y ∈ (chartAt ℂ x).target :=
    (chartAt ℂ x).map_source h_y_in
  have h_y_in_pre : (chartAt ℂ x) y ∈ (chartAt ℂ x).target ∩
      (chartAt ℂ x).symm ⁻¹' (chartAt ℂ y).source := by
    refine ⟨h_x_target_mem, ?_⟩
    change (chartAt ℂ x).symm ((chartAt ℂ x) y) ∈ (chartAt ℂ y).source
    rw [(chartAt ℂ x).left_inv h_y_in]; exact h_y_in_ysrc
  have h_evEq :
      (f ∘ (chartAt ℂ x).symm)
        =ᶠ[nhds ((chartAt ℂ x) y)]
        ((f ∘ (chartAt ℂ y).symm) ∘ ((chartAt ℂ y) ∘ (chartAt ℂ x).symm)) := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, h_pre_open.mem_nhds h_y_in_pre, ?_⟩
    intro w hw
    obtain ⟨_hw_tgt, hw_pre⟩ := hw
    change f ((chartAt ℂ x).symm w)
        = f ((chartAt ℂ y).symm ((chartAt ℂ y) ((chartAt ℂ x).symm w)))
    rw [(chartAt ℂ y).left_inv hw_pre]
  -- `partialZBar` is local.
  have h_pZ_congr : partialZBar (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)
      = partialZBar ((f ∘ (chartAt ℂ y).symm) ∘ ((chartAt ℂ y) ∘ (chartAt ℂ x).symm))
          ((chartAt ℂ x) y) := by
    unfold partialZBar
    rw [Filter.EventuallyEq.fderiv_eq h_evEq]
  rw [h_pZ_congr]
  -- Apply the chain rule.
  have h_diff_at_trans :
      DifferentiableAt ℝ (f ∘ (chartAt ℂ y).symm)
        (((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)) := by
    rw [h_trans_apply]; exact h_f_diff_y
  rw [partialZBar_comp_of_differentiableAt h_diff_at_trans h_Φ_diff]
  -- Rewrite (chart-y ∘ chart-x.symm)(chart_x y) = chart_y y.
  rw [h_trans_apply]
  -- The first factor IS `partialZBarManifold f y` by definition.
  rfl

/-- **Chip 4 — manifold identity at any y ∈ chart_x.source** (with
chart-transition factor). For `y ∈ (chartAt ℂ x).source`,

```
partialZBarManifold (pompeiuKernelChart x α) y *
  conj(deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y))
  = α y.
```

The chart-transition factor encodes how `∂̄` transforms as a `(0,1)`-form
under holomorphic chart changes. At the basepoint `y = x` the factor is
`1` (`Φ = id`, `deriv id = 1`, `conj 1 = 1`), recovering
`partialZBarManifold_pompeiuKernelChart_at_basepoint`. -/
theorem partialZBarManifold_pompeiuKernelChart_eq_α_mul_transition
    (x : X) (α : X → ℂ)
    (h_α_smooth : ContDiff ℝ 1 (α ∘ (chartAt ℂ x).symm))
    (h_α_cs : HasCompactSupport (α ∘ (chartAt ℂ x).symm))
    {y : X} (h_y_in : y ∈ (chartAt ℂ x).source) :
    JacobianChallenge.partialZBarManifold (pompeiuKernelChart x α) y *
      (starRingEnd ℂ)
        (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y))
      = α y := by
  -- u_chart := pompeiuKernel (α ∘ chart_x.symm) is C^1 globally
  -- (Chip 2d's `contDiff_pompeiuKernel_of_nat` at n := 1, requiring only
  -- C^1 input).
  have h_pk_smooth :
      ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (pompeiuKernel (α ∘ (chartAt ℂ x).symm)) :=
    contDiff_pompeiuKernel_of_nat 1 h_α_smooth h_α_cs
  -- The manifold partialZBar of pompeiuKernelChart x α at y uses chart_y.
  -- We need ℝ-differentiability of `pompeiuKernelChart x α ∘ chart_y.symm`
  -- at `chart_y y`.
  -- Strategy: bridge via the chart-x view eventual equality, then use
  -- smoothness of `pompeiuKernel (α ∘ chart_x.symm)` directly.
  -- For the bridge lemma we want DifferentiableAt ℝ (u ∘ chart_y.symm) (chart_y y).
  -- Build it via the eventual equality
  --   u ∘ chart_y.symm =ᶠ (u_chart ∘ chart_x ∘ chart_y.symm) on a nbhd of chart_y y,
  -- then differentiability of u_chart at chart_x y composed with differentiability
  -- of chart_x ∘ chart_y.symm at chart_y y (smooth chart transition).
  set u : X → ℂ := pompeiuKernelChart x α with hu_def
  have h_u_chart_diff_at :
      DifferentiableAt ℝ (u ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) := by
    -- Build via the chart-transition route:
    --   u ∘ chart_y.symm = u_chart_x ∘ chart_x ∘ chart_y.symm  (on a nbhd).
    -- u_chart_x := pompeiuKernel (α ∘ chart_x.symm) is differentiable everywhere.
    -- chart_x ∘ chart_y.symm is holomorphic at chart_y y (chart transition).
    -- Compose.
    have h_x_atlas : chartAt ℂ x ∈ atlas ℂ X := chart_mem_atlas ℂ x
    have h_y_atlas : chartAt ℂ y ∈ atlas ℂ X := chart_mem_atlas ℂ y
    have h_y_in_ysrc : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
    -- chart_x ∘ chart_y.symm is ℂ-analytic at chart_y y.
    have h_an_inv : AnalyticAt ℂ ((chartAt ℂ x) ∘ (chartAt ℂ y).symm)
        ((chartAt ℂ y) y) :=
      JacobianChallenge.analyticAt_chart_transition_of_isManifold
        h_y_atlas h_x_atlas h_y_in_ysrc h_y_in
    have h_inv_diff_at_R :
        DifferentiableAt ℝ ((chartAt ℂ x) ∘ (chartAt ℂ y).symm)
          ((chartAt ℂ y) y) :=
      differentiableAt_restrictScalars_R_C_C_local h_an_inv.differentiableAt
    -- u_chart_x = pompeiuKernel (α ∘ chart_x.symm) is C^∞ at every point.
    have h_pk_diff_at : DifferentiableAt ℝ
        (pompeiuKernel (α ∘ (chartAt ℂ x).symm))
        (((chartAt ℂ x) ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y)) := by
      have h_one_ne_zero : ((1 : ℕ) : WithTop ℕ∞) ≠ 0 := by decide
      exact (h_pk_smooth.differentiable h_one_ne_zero).differentiableAt
    -- Composed: pompeiuKernel ∘ (chart_x ∘ chart_y.symm) differentiable at chart_y y.
    have h_comp_diff : DifferentiableAt ℝ
        (pompeiuKernel (α ∘ (chartAt ℂ x).symm) ∘
          ((chartAt ℂ x) ∘ (chartAt ℂ y).symm))
        ((chartAt ℂ y) y) :=
      h_pk_diff_at.comp ((chartAt ℂ y) y) h_inv_diff_at_R
    -- Eventually-equal: u ∘ chart_y.symm = pompeiuKernel (α ∘ chart_x.symm) ∘ chart_x ∘ chart_y.symm
    -- on the open neighborhood where chart_y.symm w ∈ chart_x.source.
    have h_pre_open : IsOpen ((chartAt ℂ y).target ∩
        (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source) :=
      (chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ x).open_source
    have h_y_target_mem : (chartAt ℂ y) y ∈ (chartAt ℂ y).target :=
      (chartAt ℂ y).map_source h_y_in_ysrc
    have h_y_in_pre : (chartAt ℂ y) y ∈ (chartAt ℂ y).target ∩
        (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source := by
      refine ⟨h_y_target_mem, ?_⟩
      change (chartAt ℂ y).symm ((chartAt ℂ y) y) ∈ (chartAt ℂ x).source
      rw [(chartAt ℂ y).left_inv h_y_in_ysrc]; exact h_y_in
    have h_evEq :
        (u ∘ (chartAt ℂ y).symm)
          =ᶠ[nhds ((chartAt ℂ y) y)]
          (pompeiuKernel (α ∘ (chartAt ℂ x).symm) ∘
            ((chartAt ℂ x) ∘ (chartAt ℂ y).symm)) := by
      refine Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨_, h_pre_open.mem_nhds h_y_in_pre, ?_⟩
      intro w hw
      obtain ⟨hw_tgt, hw_pre⟩ := hw
      -- u ((chartAt ℂ y).symm w) = pompeiuKernel (...) (chart_x ((chart_y).symm w))
      show pompeiuKernel (α ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) ((chartAt ℂ y).symm w))
          = pompeiuKernel (α ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) ((chartAt ℂ y).symm w))
      rfl
    exact h_comp_diff.congr_of_eventuallyEq h_evEq.symm
  -- Now combine via the bridge lemma.
  have h_bridge :=
    partialZBar_chart_x_eq_manifold_mul_transition (f := u) h_y_in h_u_chart_diff_at
  -- h_bridge: partialZBar (u ∘ chart_x.symm)(chart_x y) =
  --   partialZBarManifold u y * conj(deriv (chart_y ∘ chart_x.symm)(chart_x y))
  -- The LHS equals α y by Chip 4's chart-x view local identity.
  rw [partialZBar_pompeiuKernelChart_eq_α_on_chart_source x α h_α_smooth h_α_cs h_y_in]
    at h_bridge
  -- h_bridge: α y = partialZBarManifold u y * conj(deriv ...)
  exact h_bridge.symm

end ManifoldIdentityWithTransition

end JacobianChallenge.PompeiuKernel

end
