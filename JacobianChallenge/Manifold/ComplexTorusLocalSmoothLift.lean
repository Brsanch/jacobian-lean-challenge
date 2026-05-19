/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorus
import JacobianChallenge.Manifold.ComplexTorusBasicInstances
import JacobianChallenge.Manifold.SmoothChain
import JacobianChallenge.Manifold.SmoothPathIntegral

set_option linter.unusedSectionVars false

/-! # Chart-based local smooth lift on `ℂ ⧸ L`

For a smooth path `γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)` and a chosen
"anchor" lift `x₀ : ℂ` of `γ.ambient(t₀)` (i.e., `mkQ x₀ = γ.ambient
t₀`), define the **chart-based local smooth lift**

    localLift x₀ t := (localChart L (discRadius_separates L) x₀).symm
                          (γ.ambient t)

on a neighborhood of `t₀` where `γ.ambient t ∈ mkQ '' ball x₀ (r/2)`.

This is a smooth ℂ-valued function on the open set
`γ.ambient ⁻¹' (mkQ '' ball x₀ (r/2)) ⊆ ℝ`, and it lifts `γ.ambient`
locally: `mkQ ∘ localLift = γ.ambient` on the open set.

## What this file ships

* `ComplexTorus.localLift L γ x₀` — the chart-based local lift
  function `ℝ → ℂ` (defined on chart-domain via dependent-if; outside
  it falls back arbitrarily).

* `ComplexTorus.localLift_lifts` — `mkQ (localLift L γ x₀ t) =
  γ.ambient t` when `γ.ambient t ∈ mkQ '' ball x₀ (r/2)`.

This is a building block for the smoothness upgrade of `contLift`.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff Topology

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **Chart-based local lift.** For `x₀ : ℂ` (anchor), use the chart
`(localChart L _ x₀).symm : T² → ℂ` (centered at `x₀`, with chart-
target containing `x₀`). On the chart-source preimage
(`γ.ambient ⁻¹' (localChart _ x₀).target`), this composes with
`γ.ambient` to give a smooth `ℝ → ℂ` function whose value at the
basepoint `t₀` (where `γ.ambient t₀ = mkQ x₀`) is exactly `x₀`. -/
noncomputable def localLift
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (x₀ : ℂ) (t : ℝ) : ℂ := by
  classical
  exact if h : γ.ambient t ∈
      (localChart L (discRadius_separates L) x₀).symm.source then
    (localChart L (discRadius_separates L) x₀).symm (γ.ambient t)
  else 0

/-- **Inverse property of `(localChart L _ x₀).symm`.** For
`y = mkQ x` with `x ∈ ball x₀ (r/2)`, the chart .symm sends `y` back
to `x`. In particular, at the chart-source basepoint `mkQ x₀`, the
chart .symm returns `x₀`. -/
theorem chart_symm_mkQ_in_ball (x₀ : ℂ) {x : ℂ}
    (hx : x ∈ Metric.ball x₀ (discRadius L / 2)) :
    (localChart L (discRadius_separates L) x₀).symm (L.mkQ x) = x :=
  (localChart L (discRadius_separates L) x₀).left_inv hx

/-- The chart `(localChart L _ x₀).symm` is in the atlas of `ℂ ⧸ L`. -/
private lemma chart_x₀_mem_atlas (x₀ : ℂ) :
    (localChart L (discRadius_separates L) x₀).symm ∈ atlas ℂ (ℂ ⧸ L) :=
  ⟨x₀, rfl⟩

/-- The chart `(localChart L _ x₀).symm` is in the maximal atlas. -/
private lemma chart_x₀_mem_maximalAtlas (n : WithTop ℕ∞) (x₀ : ℂ) :
    (localChart L (discRadius_separates L) x₀).symm ∈
      IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) n (ℂ ⧸ L) :=
  IsManifold.subset_maximalAtlas (chart_x₀_mem_atlas L x₀)

/-! ## Local agreement of localLift with the chart-composition -/

/-- On the open set `γ.ambient ⁻¹' (localChart _ x₀).symm.source`, the
local lift coincides with the chart-composition
`(localChart _ x₀).symm ∘ γ.ambient` — without the dependent-if branch. -/
private lemma localLift_eqOn_chartComp
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (x₀ : ℂ) :
    Set.EqOn (localLift L γ x₀)
      (fun t : ℝ => (localChart L (discRadius_separates L) x₀).symm
          (γ.ambient t))
      (γ.ambient ⁻¹' (localChart L (discRadius_separates L) x₀).symm.source) := by
  intro t ht
  show localLift L γ x₀ t
      = (localChart L (discRadius_separates L) x₀).symm (γ.ambient t)
  have ht' : γ.ambient t ∈
      (localChart L (discRadius_separates L) x₀).symm.source := ht
  unfold localLift
  rw [dif_pos ht']

/-! ## `mkQ ∘ localLift = γ.ambient` on chart-source preimage -/

/-- **Local lift property.** On the chart-source preimage, the lift
satisfies `mkQ ∘ localLift = γ.ambient`. -/
theorem mkQ_localLift
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (x₀ : ℂ) {t : ℝ}
    (ht : γ.ambient t ∈
        (localChart L (discRadius_separates L) x₀).symm.source) :
    L.mkQ (localLift L γ x₀ t) = γ.ambient t := by
  have h_eq := localLift_eqOn_chartComp L γ x₀ ht
  rw [h_eq]
  -- mkQ ((localChart _ x₀).symm y) = y for y in chart source.
  -- (localChart _ x₀).symm.symm = localChart _ x₀, and right_inv property.
  exact (localChart L (discRadius_separates L) x₀).right_inv ht

/-! ## Smoothness of the chart-composition -/

/-- **The chart-composition `(localChart _ x₀).symm ∘ γ.ambient` is
`ContMDiffOn` on the chart-source preimage** at level `∞`. -/
theorem chartComp_contMDiffOn
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (x₀ : ℂ) :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
      (fun t : ℝ => (localChart L (discRadius_separates L) x₀).symm
          (γ.ambient t))
      (γ.ambient ⁻¹' (localChart L (discRadius_separates L) x₀).symm.source) := by
  have h_amb : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ γ.ambient :=
    γ.ambient_contMDiff
  have h_amb_on : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ γ.ambient
      (γ.ambient ⁻¹' (localChart L (discRadius_separates L) x₀).symm.source) :=
    h_amb.contMDiffOn
  -- The chart .symm.symm = .symm.symm.symm = .symm: that's the function ℂ⧸L → ℂ.
  -- Wait, we need ContMDiffOn of the .symm direction (T² → ℂ), which is
  -- the inverse of the atlas chart. Apply contMDiffOn_symm_of_mem_maximalAtlas
  -- to the .symm.symm form... actually the atlas chart IS (.symm), so its
  -- .symm gives back the localChart (ℂ → T² direction).
  -- We want ContMDiff of the ℂ⧸L → ℂ direction, which is .symm of the atlas chart.
  -- Specifically, our atlas chart is `(localChart _ x₀).symm`, an OPH ℂ⧸L → ℂ
  -- (T² → ℂ direction). Its source contains points like mkQ x₀.
  -- This chart, as a function (ℂ⧸L → ℂ), is smooth on its source.
  have h_chart_atlas : (localChart L (discRadius_separates L) x₀).symm ∈
      atlas ℂ (ℂ ⧸ L) := chart_x₀_mem_atlas L x₀
  have h_chart_max : (localChart L (discRadius_separates L) x₀).symm ∈
      IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ∞ (ℂ ⧸ L) :=
    chart_x₀_mem_maximalAtlas L ∞ x₀
  have h_chart : ContMDiffOn (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ∞
      (localChart L (discRadius_separates L) x₀).symm
      (localChart L (discRadius_separates L) x₀).symm.source :=
    contMDiffOn_of_mem_maximalAtlas h_chart_max
  exact h_chart.comp h_amb_on (fun _ ht => ht)

/-! ## Smoothness of `localLift` on the chart-source preimage -/

/-- **`localLift` is `ContMDiffOn` on the chart-source preimage.**
Follows from `chartComp_contMDiffOn` via the local agreement
`localLift_eqOn_chartComp`. -/
theorem localLift_contMDiffOn
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (x₀ : ℂ) :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
      (localLift L γ x₀)
      (γ.ambient ⁻¹' (localChart L (discRadius_separates L) x₀).symm.source) := by
  have h_chart := chartComp_contMDiffOn L γ x₀
  have h_eq := localLift_eqOn_chartComp L γ x₀
  exact h_chart.congr h_eq

/-! ## Anchor identity: `localLift L γ x₀ t₀ = x₀` when γ.ambient t₀ = mkQ x₀ -/

/-- **At an anchor point**: when `γ.ambient t₀ = mkQ x₀` (so x₀ is a
preimage of γ.ambient t₀ in ℂ AND the chart at x₀ has source
containing γ.ambient t₀), `localLift t₀ = x₀`. -/
theorem localLift_at_anchor
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (x₀ : ℂ) {t₀ : ℝ}
    (ht₀ : γ.ambient t₀ = L.mkQ x₀) :
    localLift L γ x₀ t₀ = x₀ := by
  -- We have x₀ ∈ ball x₀ (r/2) trivially, so mkQ x₀ ∈ chart-source.
  have hr_pos : 0 < discRadius L := discRadius_pos L
  have hr2_pos : 0 < discRadius L / 2 := by linarith
  have hx₀_in_ball : x₀ ∈ Metric.ball x₀ (discRadius L / 2) := by
    simp [Metric.mem_ball, dist_self, hr2_pos]
  -- (localChart _ x₀).symm.source = (localChart _ x₀).target = mkQ '' ball x₀ (r/2).
  have h_mkQ_x₀_in_source : L.mkQ x₀ ∈
      (localChart L (discRadius_separates L) x₀).symm.source := by
    show L.mkQ x₀ ∈ (localChart L (discRadius_separates L) x₀).target
    exact (localChart L (discRadius_separates L) x₀).map_source hx₀_in_ball
  have h_amb_in : γ.ambient t₀ ∈
      (localChart L (discRadius_separates L) x₀).symm.source := by
    rw [ht₀]
    exact h_mkQ_x₀_in_source
  -- Apply localLift_eqOn_chartComp at t₀.
  have h_eq : localLift L γ x₀ t₀
      = (localChart L (discRadius_separates L) x₀).symm (γ.ambient t₀) :=
    localLift_eqOn_chartComp L γ x₀ h_amb_in
  rw [h_eq, ht₀]
  -- (localChart _ x₀).symm (mkQ x₀) = x₀ by chart_symm_mkQ_in_ball.
  exact chart_symm_mkQ_in_ball L x₀ hx₀_in_ball

end ComplexTorus

end JacobianChallenge

end
