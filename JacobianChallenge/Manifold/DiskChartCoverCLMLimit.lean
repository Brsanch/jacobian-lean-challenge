/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverPointwiseLimit

set_option diagnostics.threshold 100

/-! # CLM-level pointwise limit at every `y ∈ X`

Lifts chip 5d's scalar limit to a CLM limit in the cotangent fibre.

For each `y ∈ X`, the chart-`x_y`-frame CLM
`coordChange (achart y) (achart x_y) y (om_n (ψ k).toFun y) ∈ ℂ →L[ℂ] ℂ`
has its value at `1` converging to `c_y` (chip 5d). Since a `ℂ →L[ℂ] ℂ`
CLM is determined by its value at `1` via `smulRight 1`, the CLMs
converge to `T_lim_xy := smulRight 1 c_y`. Then by continuity of the
inverse cocycle `coordChange (achart x_y) (achart y) y`, the section
values `om_n (ψ k).toFun y` converge to
`T_lim_y := (coordChange (achart x_y) (achart y) y) T_lim_xy` — the
pointwise CLM limit.

## Main result

* `DiskChartCover.section_value_tendsto` — at every `y ∈ X`, the
  CLM sequence `om_n (ψ k).toFun y` converges in `ℂ →L[ℂ] ℂ` to a
  specific CLM `T_lim_y`.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff Pointwise
open Set Metric HolomorphicOneForm Filter

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

omit [IsManifold 𝓘(ℂ) ω X] in
/-- A CLM `ℂ →L[ℂ] ℂ` is determined by its value at `1`: every such CLM
equals `smulRight 1 (T 1)`. -/
private lemma clm_eq_smulRight_value_at_one (T : ℂ →L[ℂ] ℂ) :
    T = ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (T 1) := by
  apply ContinuousLinearMap.ext
  intro z
  show T z = z * T 1
  rw [show z = z • (1 : ℂ) from by simp, T.map_smul]
  simp [smul_eq_mul]

omit [IsManifold 𝓘(ℂ) ω X] in
/-- The map `c ↦ smulRight 1 c : ℂ → (ℂ →L[ℂ] ℂ)` is continuous. -/
private lemma continuous_smulRight_one :
    Continuous (fun c : ℂ => ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c) :=
  (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (1 : ℂ →L[ℂ] ℂ)).continuous

/-- **CLM-level pointwise limit at any `y ∈ X`.** -/
theorem section_value_tendsto (cover : DiskChartCover X) [Nonempty X]
    (om_n : ℕ → HolomorphicOneForm X)
    {ψ : ℕ → ℕ}
    (h_diag : ∀ (x : X) (hx : x ∈ cover.basePoints),
      ∃ g_lim : BoundedContinuousFunction
            ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ,
        Tendsto (fun k => localCoeffBcf cover (om_n (ψ k)) hx) atTop (𝓝 g_lim))
    (y : X) :
    ∃ T_lim : ℂ →L[ℂ] ℂ,
      Tendsto (fun k => (om_n (ψ k)).toFun y) atTop (𝓝 T_lim) := by
  -- Step 1: scalar limit from chip 5d.
  obtain ⟨c_y, h_scalar⟩ := chartLimit_tendsto cover om_n h_diag y
  set x_y := chosenBasePoint cover y with hxy_def
  -- Step 2: chart-x_y-frame CLM limit = smulRight 1 c_y.
  let T_lim_xy : ℂ →L[ℂ] ℂ :=
    ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c_y
  -- Step 3: chart-x_y-frame CLM applied to om_n.toFun y is
  -- `coordChange (achart y) (achart x_y) y (om_n.toFun y)`.
  -- Its value at 1 = localCoeff (om_n) x_y ((chartAt ℂ x_y) y),
  -- which converges to c_y by chip 5d (after identification).
  have h_chart_value :
      Tendsto (fun k => (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y) (achart ℂ x_y) y) ((om_n (ψ k)).toFun y)) 1)
        atTop (𝓝 c_y) := by
    -- Identify with the scalar from chip 5d.
    have h_eq : ∀ k,
        (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ y) (achart ℂ x_y) y) ((om_n (ψ k)).toFun y)) 1
        = localCoeff (om_n (ψ k)) x_y ((chartAt ℂ x_y) y) := by
      intro k
      -- localCoeff om x w = ((coordChange (achart (chart.symm w)) (achart x)
      --   (chart.symm w)) (om.toFun (chart.symm w))) 1.
      -- At w = chartAt x y, chart.symm w = y (by chartAt y ∈ chart-source).
      have h_symm : (chartAt ℂ x_y).symm ((chartAt ℂ x_y) y) = y :=
        (chartAt ℂ x_y).left_inv (chosenBasePoint_source cover y)
      show (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y) (achart ℂ x_y) y) ((om_n (ψ k)).toFun y)) 1
        = (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
            (achart ℂ ((chartAt ℂ x_y).symm ((chartAt ℂ x_y) y)))
            (achart ℂ x_y)
            ((chartAt ℂ x_y).symm ((chartAt ℂ x_y) y)))
            ((om_n (ψ k)).toFun ((chartAt ℂ x_y).symm ((chartAt ℂ x_y) y)))) 1
      rw [h_symm]
    rw [show (fun k => (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y) (achart ℂ x_y) y) ((om_n (ψ k)).toFun y)) 1)
        = fun k => localCoeff (om_n (ψ k)) x_y ((chartAt ℂ x_y) y) from
      funext h_eq]
    exact h_scalar
  -- Step 4: chart-x_y-frame CLMs converge to T_lim_xy via smulRight 1.
  have h_chart_clm :
      Tendsto (fun k => ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y) (achart ℂ x_y) y) ((om_n (ψ k)).toFun y))
        atTop (𝓝 T_lim_xy) := by
    have h_clm_eq : ∀ k,
        ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ y) (achart ℂ x_y) y) ((om_n (ψ k)).toFun y)
        = ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
            ((((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
              (achart ℂ y) (achart ℂ x_y) y) ((om_n (ψ k)).toFun y)) 1) :=
      fun k => clm_eq_smulRight_value_at_one _
    rw [show (fun k => ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y) (achart ℂ x_y) y) ((om_n (ψ k)).toFun y))
        = fun k => ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
          ((((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
            (achart ℂ y) (achart ℂ x_y) y) ((om_n (ψ k)).toFun y)) 1) from
      funext h_clm_eq]
    show Tendsto _ atTop (𝓝 (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c_y))
    exact (continuous_smulRight_one.tendsto _).comp h_chart_value
  -- Step 5: transport back via cocycle.
  -- `coordChange (achart x_y) (achart y) y ∘ coordChange (achart y) (achart x_y) y = id`
  -- on the cotangent fibre at y.
  let T_lim : ℂ →L[ℂ] ℂ :=
    ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
      (achart ℂ x_y) (achart ℂ y) y) T_lim_xy
  refine ⟨T_lim, ?_⟩
  -- Identify `om_n (ψ k).toFun y` with `(coordChange (achart x_y) (achart y) y)
  -- ((coordChange (achart y) (achart x_y) y) (om_n.toFun y))` via cocycle.
  have h_y_inter : y ∈
      (cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ y) ∩
      (cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ x_y) ∩
      (cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ y) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show y ∈ (achart ℂ y).1.source
      rw [achart_val]
      exact mem_chart_source ℂ y
    · show y ∈ (achart ℂ x_y).1.source
      rw [achart_val]
      exact chosenBasePoint_source cover y
    · show y ∈ (achart ℂ y).1.source
      rw [achart_val]
      exact mem_chart_source ℂ y
  have h_self : ∀ v : ℂ →L[ℂ] ℂ,
      ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y) (achart ℂ y) y) v = v := by
    intro v
    apply cotangentBundleCore_coordChange_self
    show y ∈ (achart ℂ y).1.source
    rw [achart_val]
    exact mem_chart_source ℂ y
  have h_cocycle : ∀ v : ℂ →L[ℂ] ℂ,
      ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ x_y) (achart ℂ y) y)
        (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ y) (achart ℂ x_y) y) v) = v := by
    intro v
    have h_cc := (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange_comp
      (achart ℂ y) (achart ℂ x_y) (achart ℂ y) y h_y_inter v
    rw [h_self] at h_cc
    exact h_cc
  have h_om_eq : ∀ k, (om_n (ψ k)).toFun y
      = ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ x_y) (achart ℂ y) y)
          (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
            (achart ℂ y) (achart ℂ x_y) y) ((om_n (ψ k)).toFun y)) := by
    intro k
    rw [h_cocycle]
  rw [show (fun k => (om_n (ψ k)).toFun y) = fun k =>
      ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ x_y) (achart ℂ y) y)
        (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ y) (achart ℂ x_y) y) ((om_n (ψ k)).toFun y)) from
    funext h_om_eq]
  exact (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
    (achart ℂ x_y) (achart ℂ y) y).continuous.tendsto _).comp h_chart_clm

end DiskChartCover

end JacobianChallenge

end
