/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothBordantOfSmoothHomotopy

set_option linter.unusedSectionVars false

/-! # Chart-local straight-line smooth homotopy on a complex manifold

For a complex 1-manifold `X`, basepoint `p₀ : X`, chart `ψ := chartAt
ℂ p₀`, and two smooth based loops `γ₀, γ₁ : BasedLoopAt 𝓘(ℝ, ℂ) X p₀`
**both globally chart-source-contained** with **chart-straight-line
globally chart-target-contained**, the straight line *in chart
coordinates* gives a smooth homotopy on `X`:

```
H(s, t) := ψ.symm( (1 - s) · ψ(γ₀.ambient(t)) + s · ψ(γ₁.ambient(t)) )
```

This is a real chart-local-bordism construction. Compared to the `ℂ`-
specific straight-line chip, here `X` is an arbitrary complex 1-manifold
and the linear interpolation happens in the chart-target inside `ℂ`,
then is pulled back to `X` via the chart inverse.

## Strong hypotheses

To avoid bump-function infrastructure (smoothly extending the loops
outside `[0,1]` to stay in `ψ.source`), we package both
chart-containment conditions as **global** requirements:

1. `γᵢ.toPath.ambient t ∈ ψ.source` for all `t : ℝ` (not just
   `t ∈ [0,1]`).
2. The chart-image straight line `(1-s)·ψ(γ₀.ambient t) +
   s·ψ(γ₁.ambient t) ∈ ψ.target` for all `(s, t) ∈ ℝ²`.

These are restrictive but allow `ψ` and `ψ.symm` to be composed
without bump-extension. A follow-on chip will weaken (1) via a
smooth-bump-extension utility.

## What this file ships

* `ChartLocalHomotopyData p₀` — bundle of two based loops + the two
  hypotheses.
* `SmoothHomotopyBasedLoop.chartLocalStraightLine` — the homotopy
  constructor.
* `smoothBordant_of_chartLocal` — corollary: `SmoothBordant γ₀ γ₁`
  via `smoothBordant_of_smoothHomotopy`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-! ## Hypotheses bundle -/

/-- **Chart-local homotopy data**: two based loops + global
chart-containment + global chart-straight-line containment. -/
structure ChartLocalHomotopyData (p₀ : X) where
  γ₀ : BasedLoopAt 𝓘(ℝ, ℂ) X p₀
  γ₁ : BasedLoopAt 𝓘(ℝ, ℂ) X p₀
  /-- `γ₀.ambient` globally lands in `chart.source`. -/
  γ₀_amb_in_source : ∀ t : ℝ, γ₀.toPath.ambient t ∈ (chartAt ℂ p₀).source
  /-- `γ₁.ambient` globally lands in `chart.source`. -/
  γ₁_amb_in_source : ∀ t : ℝ, γ₁.toPath.ambient t ∈ (chartAt ℂ p₀).source
  /-- The chart-straight-line globally lands in `chart.target`. -/
  chart_straightLine_in_target :
    ∀ s t : ℝ,
      (1 - s) • (chartAt ℂ p₀) (γ₀.toPath.ambient t)
        + s • (chartAt ℂ p₀) (γ₁.toPath.ambient t)
      ∈ (chartAt ℂ p₀).target

namespace ChartLocalHomotopyData

variable {p₀ : X} (data : ChartLocalHomotopyData p₀)

/-! ## Smoothness helpers -/

/-- `(x : Fin 2 → ℝ) ↦ x i` is smooth `→ ℝ`. -/
private lemma contMDiff_proj_R (i : Fin 2) :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞ (fun x : Fin 2 → ℝ => x i) := by
  have h_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Fin 2 → ℝ => x i) :=
    (ContinuousLinearMap.proj i : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff
  exact h_cd.contMDiff

/-- `ψ ∘ γ.ambient : ℝ → ℂ` is smooth, given `γ.ambient` maps globally
into `chart.source`. -/
private lemma contMDiff_chart_of_amb_in_source
    {γ : BasedLoopAt 𝓘(ℝ, ℂ) X p₀}
    (h_in : ∀ t : ℝ, γ.toPath.ambient t ∈ (chartAt ℂ p₀).source) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
      (fun t : ℝ => (chartAt ℂ p₀) (γ.toPath.ambient t)) := by
  have h_chart : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (chartAt ℂ p₀)
      (chartAt ℂ p₀).source :=
    contMDiffOn_chart
  exact h_chart.comp_contMDiff γ.toPath.ambient_contMDiff h_in

/-- The inner chart-straight-line `L(x) := (1 - x 0) • ψ(γ₀.amb(x 1)) +
(x 0) • ψ(γ₁.amb(x 1))` is smooth `(Fin 2 → ℝ) → ℂ`. -/
private lemma contMDiff_innerStraightLine :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ =>
        (1 - x 0) • (chartAt ℂ p₀) (data.γ₀.toPath.ambient (x 1))
          + (x 0) • (chartAt ℂ p₀) (data.γ₁.toPath.ambient (x 1))) := by
  have h_proj0 := contMDiff_proj_R 0
  have h_proj1 := contMDiff_proj_R 1
  have h_one_sub : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun x : Fin 2 → ℝ => 1 - (x 0 : ℝ)) :=
    contMDiff_const.sub h_proj0
  have h_chart_γ₀ := contMDiff_chart_of_amb_in_source data.γ₀_amb_in_source
  have h_chart_γ₁ := contMDiff_chart_of_amb_in_source data.γ₁_amb_in_source
  -- Compose with x ↦ x 1.
  have h_chart_γ₀_x : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => (chartAt ℂ p₀) (data.γ₀.toPath.ambient (x 1))) :=
    h_chart_γ₀.comp h_proj1
  have h_chart_γ₁_x : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => (chartAt ℂ p₀) (data.γ₁.toPath.ambient (x 1))) :=
    h_chart_γ₁.comp h_proj1
  have h_lhs : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => (1 - x 0) • (chartAt ℂ p₀)
        (data.γ₀.toPath.ambient (x 1))) :=
    h_one_sub.smul h_chart_γ₀_x
  have h_rhs : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => (x 0) • (chartAt ℂ p₀)
        (data.γ₁.toPath.ambient (x 1))) :=
    h_proj0.smul h_chart_γ₁_x
  exact h_lhs.add h_rhs

/-! ## The chart-local straight-line homotopy -/

/-- **Chart-local straight-line smooth homotopy.** For two based loops
`γ₀, γ₁` at `p₀` with `ChartLocalHomotopyData`, the map

```
H(s, t) := ψ.symm( (1-s) · ψ(γ₀.ambient(t)) + s · ψ(γ₁.ambient(t)) )
```

defines a `SmoothHomotopyBasedLoop γ₀ γ₁`. -/
noncomputable def _root_.JacobianChallenge.SmoothHomotopyBasedLoop.chartLocalStraightLine
    {p₀ : X} (data : ChartLocalHomotopyData p₀) :
    SmoothHomotopyBasedLoop data.γ₀ data.γ₁ where
  toFun := fun x : Fin 2 → ℝ =>
    (chartAt ℂ p₀).symm
      ((1 - x 0) • (chartAt ℂ p₀) (data.γ₀.toPath.ambient (x 1))
        + (x 0) • (chartAt ℂ p₀) (data.γ₁.toPath.ambient (x 1)))
  smooth := by
    -- ψ.symm is ContMDiffOn ψ.target; the inner straight-line is smooth
    -- ℝ² → ℂ and globally lands in ψ.target by hypothesis.
    have h_symm : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (chartAt ℂ p₀).symm
        (chartAt ℂ p₀).target := contMDiffOn_chart_symm
    have h_inner := data.contMDiff_innerStraightLine
    have h_maps : ∀ x : Fin 2 → ℝ,
        ((1 - x 0) • (chartAt ℂ p₀) (data.γ₀.toPath.ambient (x 1))
            + (x 0) • (chartAt ℂ p₀) (data.γ₁.toPath.ambient (x 1)))
          ∈ (chartAt ℂ p₀).target :=
      fun x => data.chart_straightLine_in_target (x 0) (x 1)
    exact h_symm.comp_contMDiff h_inner h_maps
  left_edge := by
    intro t
    -- H(0, t) = ψ.symm(1 · ψ(γ₀.amb t) + 0 · ψ(γ₁.amb t)) = ψ.symm(ψ(γ₀.amb t))
    --        = γ₀.amb t  (by chart left_inv, since γ₀.amb t ∈ ψ.source).
    show (chartAt ℂ p₀).symm
          ((1 - (![0, t] : Fin 2 → ℝ) 0) •
              (chartAt ℂ p₀) (data.γ₀.toPath.ambient ((![0, t] : Fin 2 → ℝ) 1))
            + ((![0, t] : Fin 2 → ℝ) 0) •
              (chartAt ℂ p₀) (data.γ₁.toPath.ambient ((![0, t] : Fin 2 → ℝ) 1)))
        = data.γ₀.toPath.ambient t
    have h0 : (![0, t] : Fin 2 → ℝ) 0 = 0 := rfl
    have h1 : (![0, t] : Fin 2 → ℝ) 1 = t := rfl
    rw [h0, h1]
    -- Now: ψ.symm((1 - 0) ψ(γ₀.amb t) + 0 ψ(γ₁.amb t)) = ψ.symm(ψ(γ₀.amb t))
    have h_scalar : (1 - (0 : ℝ)) • (chartAt ℂ p₀) (data.γ₀.toPath.ambient t)
          + (0 : ℝ) • (chartAt ℂ p₀) (data.γ₁.toPath.ambient t)
        = (chartAt ℂ p₀) (data.γ₀.toPath.ambient t) := by module
    rw [h_scalar]
    exact (chartAt ℂ p₀).left_inv (data.γ₀_amb_in_source t)
  right_edge := by
    intro t
    show (chartAt ℂ p₀).symm
          ((1 - (![1, t] : Fin 2 → ℝ) 0) •
              (chartAt ℂ p₀) (data.γ₀.toPath.ambient ((![1, t] : Fin 2 → ℝ) 1))
            + ((![1, t] : Fin 2 → ℝ) 0) •
              (chartAt ℂ p₀) (data.γ₁.toPath.ambient ((![1, t] : Fin 2 → ℝ) 1)))
        = data.γ₁.toPath.ambient t
    have h0 : (![1, t] : Fin 2 → ℝ) 0 = 1 := rfl
    have h1 : (![1, t] : Fin 2 → ℝ) 1 = t := rfl
    rw [h0, h1]
    have h_scalar : (1 - (1 : ℝ)) • (chartAt ℂ p₀) (data.γ₀.toPath.ambient t)
          + (1 : ℝ) • (chartAt ℂ p₀) (data.γ₁.toPath.ambient t)
        = (chartAt ℂ p₀) (data.γ₁.toPath.ambient t) := by module
    rw [h_scalar]
    exact (chartAt ℂ p₀).left_inv (data.γ₁_amb_in_source t)
  bottom_edge := by
    intro s
    show (chartAt ℂ p₀).symm
          ((1 - (![s, (0 : ℝ)] : Fin 2 → ℝ) 0) •
              (chartAt ℂ p₀) (data.γ₀.toPath.ambient
                ((![s, (0 : ℝ)] : Fin 2 → ℝ) 1))
            + ((![s, (0 : ℝ)] : Fin 2 → ℝ) 0) •
              (chartAt ℂ p₀) (data.γ₁.toPath.ambient
                ((![s, (0 : ℝ)] : Fin 2 → ℝ) 1)))
        = p₀
    have h0 : (![s, (0 : ℝ)] : Fin 2 → ℝ) 0 = s := rfl
    have h1 : (![s, (0 : ℝ)] : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h0, h1]
    -- γᵢ.toPath.ambient 0 = γᵢ.toPath.toPath 0 = γᵢ.toPath.src = p₀.
    have h_γ₀_amb_0 : data.γ₀.toPath.ambient 0 = p₀ := by
      have h := data.γ₀.toPath.ambient_eq_on_unitInterval
        (⟨0, by constructor <;> norm_num⟩ : unitInterval)
      have hval : ((⟨0, by constructor <;> norm_num⟩ : unitInterval).val : ℝ) = 0
        := rfl
      rw [hval] at h
      rw [h]
      exact (data.γ₀.toPath.toPath.source).trans data.γ₀.toPath_src
    have h_γ₁_amb_0 : data.γ₁.toPath.ambient 0 = p₀ := by
      have h := data.γ₁.toPath.ambient_eq_on_unitInterval
        (⟨0, by constructor <;> norm_num⟩ : unitInterval)
      have hval : ((⟨0, by constructor <;> norm_num⟩ : unitInterval).val : ℝ) = 0
        := rfl
      rw [hval] at h
      rw [h]
      exact (data.γ₁.toPath.toPath.source).trans data.γ₁.toPath_src
    rw [h_γ₀_amb_0, h_γ₁_amb_0]
    -- (1-s) ψ(p₀) + s ψ(p₀) = ψ(p₀); ψ.symm(ψ(p₀)) = p₀ (since p₀ ∈ ψ.source).
    have h_combine : (1 - s) • (chartAt ℂ p₀) p₀ + s • (chartAt ℂ p₀) p₀
        = (chartAt ℂ p₀) p₀ := by module
    rw [h_combine]
    exact (chartAt ℂ p₀).left_inv (mem_chart_source ℂ p₀)
  top_edge := by
    intro s
    show (chartAt ℂ p₀).symm
          ((1 - (![s, (1 : ℝ)] : Fin 2 → ℝ) 0) •
              (chartAt ℂ p₀) (data.γ₀.toPath.ambient
                ((![s, (1 : ℝ)] : Fin 2 → ℝ) 1))
            + ((![s, (1 : ℝ)] : Fin 2 → ℝ) 0) •
              (chartAt ℂ p₀) (data.γ₁.toPath.ambient
                ((![s, (1 : ℝ)] : Fin 2 → ℝ) 1)))
        = p₀
    have h0 : (![s, (1 : ℝ)] : Fin 2 → ℝ) 0 = s := rfl
    have h1 : (![s, (1 : ℝ)] : Fin 2 → ℝ) 1 = 1 := rfl
    rw [h0, h1]
    have h_γ₀_amb_1 : data.γ₀.toPath.ambient 1 = p₀ := by
      have h := data.γ₀.toPath.ambient_eq_on_unitInterval
        (⟨1, by constructor <;> norm_num⟩ : unitInterval)
      have hval : ((⟨1, by constructor <;> norm_num⟩ : unitInterval).val : ℝ) = 1
        := rfl
      rw [hval] at h
      rw [h]
      exact (data.γ₀.toPath.toPath.target).trans data.γ₀.toPath_tgt
    have h_γ₁_amb_1 : data.γ₁.toPath.ambient 1 = p₀ := by
      have h := data.γ₁.toPath.ambient_eq_on_unitInterval
        (⟨1, by constructor <;> norm_num⟩ : unitInterval)
      have hval : ((⟨1, by constructor <;> norm_num⟩ : unitInterval).val : ℝ) = 1
        := rfl
      rw [hval] at h
      rw [h]
      exact (data.γ₁.toPath.toPath.target).trans data.γ₁.toPath_tgt
    rw [h_γ₀_amb_1, h_γ₁_amb_1]
    have h_combine : (1 - s) • (chartAt ℂ p₀) p₀ + s • (chartAt ℂ p₀) p₀
        = (chartAt ℂ p₀) p₀ := by module
    rw [h_combine]
    exact (chartAt ℂ p₀).left_inv (mem_chart_source ℂ p₀)

end ChartLocalHomotopyData

/-- **Corollary: chart-local smooth bordism.** `SmoothBordant γ₀ γ₁`
for any two based loops at `p₀` admitting a `ChartLocalHomotopyData`. -/
theorem smoothBordant_of_chartLocal
    {p₀ : X} (data : ChartLocalHomotopyData p₀) :
    SmoothBordant data.γ₀ data.γ₁ :=
  SmoothHomotopyBasedLoop.smoothBordant_of_smoothHomotopy
    (SmoothHomotopyBasedLoop.chartLocalStraightLine data)

end JacobianChallenge

end
