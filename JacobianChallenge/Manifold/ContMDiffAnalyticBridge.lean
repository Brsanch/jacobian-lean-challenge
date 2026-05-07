/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ContMDiffOmegaAnalytic
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Basic

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Iff bridge: `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω` ↔ `AnalyticAt ℂ` on chart pullbacks

The forward direction
`ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x → AnalyticAt ℂ (chart pullback) (chartAt x x)`
is supplied by `ContMDiffOmegaAnalytic.lean`
(`contMDiffAt_omega_analyticAt_chart_pullback`).

This file supplies the **reverse direction** — and hence the full iff —
under the additional natural hypothesis `ContinuousAt f x`. The continuity
hypothesis cannot be dropped: analyticity of the chart pullback as a function
`ℂ → ℂ` does not, on its own, force `f y` to land in `(chartAt ℂ (f x)).source`
for `y` near `x`.

This iff is the gating chip identified by ZZ123 for `Degree.lean` items
8 (`fibres_finite_statement`) and 9 (`regular_value_exists_statement`):
the chart-level identity theorem applies to the analytic chart pullback,
and translates back to discreteness of fibres of the manifold map via this
bridge.

No `sorry`, no `axiom`. -/

@[expose] public section

open Set Filter Topology
open scoped Manifold Topology ContDiff

namespace JacobianChallenge
namespace ContMDiff
namespace Owed.degree

universe u v

/-! ## Reverse direction: `AnalyticAt ℂ → ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω`

Under `ContinuousAt f x`, analyticity of the chart pullback at the chart
image gives `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x`. -/

/-- **Reverse bridge: `AnalyticAt ℂ` (chart pullback) ⇒ `ContMDiffAt … ω`.**
For `f : X → Y` between complex-analytic charted spaces (model `𝓘(ℂ)`),
if `f` is continuous at `x` and the chart pullback
`(chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm`
is `AnalyticAt ℂ` at `(chartAt ℂ x) x`, then `f` is `C^ω` at `x` in the
manifold sense.

The continuity hypothesis is needed: analyticity of the chart pullback as a
map `ℂ → ℂ` does not by itself imply that `f` lands in `chartAt(f x).source`
near `x`, which is required for the manifold-level smoothness statement. -/
theorem contMDiffAt_omega_of_analyticAt_chart_pullback
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y} {x : X}
    (hcont : ContinuousAt f x)
    (hA : AnalyticAt ℂ ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) x)) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x := by
  -- Strategy: rewrite in `extChartAt` form, then use `contMDiffAt_iff`.
  -- Step 1. Convert `chartAt`-pullback analyticity to `extChartAt`-pullback
  -- analyticity (they coincide as functions because `𝓘(ℂ) = id` on `ℂ`).
  have hbase : (chartAt ℂ x) x = extChartAt 𝓘(ℂ) x x := by
    simp [extChartAt_coe]
  have hfun :
      ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
        = (extChartAt 𝓘(ℂ) (f x) ∘ f ∘ (extChartAt 𝓘(ℂ) x).symm) := by
    funext z
    simp [extChartAt_coe, extChartAt_coe_symm]
  rw [hfun, hbase] at hA
  -- Step 2. `AnalyticAt ℂ → ContDiffAt ℂ ω` (mathlib, ℂ is complete).
  have hCD : ContDiffAt ℂ ω
      (extChartAt 𝓘(ℂ) (f x) ∘ f ∘ (extChartAt 𝓘(ℂ) x).symm)
      (extChartAt 𝓘(ℂ) x x) := hA.contDiffAt
  -- Step 3. `ContDiffAt → ContDiffWithinAt _ univ`, and `range 𝓘(ℂ) = univ`.
  have hCDW : ContDiffWithinAt ℂ ω
      (extChartAt 𝓘(ℂ) (f x) ∘ f ∘ (extChartAt 𝓘(ℂ) x).symm)
      (range (𝓘(ℂ) : ModelWithCorners ℂ ℂ ℂ))
      (extChartAt 𝓘(ℂ) x x) := by
    have hrange : range (𝓘(ℂ) : ModelWithCorners ℂ ℂ ℂ) = univ :=
      ModelWithCorners.Boundaryless.range_eq_univ
    rw [hrange]
    exact hCD.contDiffWithinAt
  -- Step 4. Repackage via `contMDiffAt_iff`.
  exact (contMDiffAt_iff (I := 𝓘(ℂ)) (I' := 𝓘(ℂ)) (f := f) (x := x) (n := ω)).mpr
    ⟨hcont, hCDW⟩

/-! ## Iff -/

/-- **Iff bridge** between `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω` and analyticity of the
chart pullback, under the natural continuity hypothesis.

The continuity assumption is needed only for the reverse direction; the
forward direction supplies it for free (a `C^ω` map is continuous). We bundle
it as a hypothesis on both sides so the iff is symmetric. -/
theorem contMDiffAt_omega_iff_analyticAt_chart_pullback
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y} {x : X} (hcont : ContinuousAt f x) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x ↔
      AnalyticAt ℂ ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) := by
  refine ⟨fun h => contMDiffAt_omega_analyticAt_chart_pullback h, fun h => ?_⟩
  exact contMDiffAt_omega_of_analyticAt_chart_pullback hcont h

end Owed.degree
end ContMDiff
end JacobianChallenge
