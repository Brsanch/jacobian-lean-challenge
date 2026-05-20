/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartLocalPrimitive
import JacobianChallenge.Manifold.PrimitiveOnSmoothPathConnected

set_option linter.unusedSectionVars false

/-! # Bridge `pathPrimitive` ↔ `chartLocalPrimitive` under `LoopPeriodVanishes`

Under the period-vanishing hypothesis `LoopPeriodVanishes om x₀`, the
global path-primitive `pathPrimitive h_conn x₀ om` is path-independent
(`pathPrimitive_eq_integral_of_loopPeriodVanishes`). For any point `y`
covered by a chart `φ` with convex target, this gives the local
decomposition

  `pathPrimitive om x = pathPrimitive om y + chartLocalPrimitive(φ, y) om x`

for `x ∈ φ.source`. The proof: concatenate any smooth path `α : x₀ ⇝ y`
(from `h_conn`) with the chart-linear segment `β : y ⇝ x` (from
`linearInChartSegment`) into a single smooth path `α ⋆ β : x₀ ⇝ x`, and
unwind via `complexChainPeriod_single_concat`.

The chartLocalPrimitive side is by definition `complexChainPeriod` of
the single chart-linear segment, so this is a clean rfl after the
concat-and-path-independence rewrites.

## Why this matters (item 14 reverse leg)

`pathPrimitive` is defined via `Classical.choose` on
`SmoothPathConnected`, so its smoothness and FTC in the endpoint are
hard to reason about directly. `chartLocalPrimitive` is defined via the
explicit `linearInChartSegment` — a `C^∞` segment whose ambient
extension is jointly smooth in `(z, t)`. Standard parametric-integral
machinery (mathlib's `ParametricIntervalIntegral`) gives smoothness of
`chartLocalPrimitive` in the endpoint.

This bridge transfers chart-local smoothness/FTC to global
`pathPrimitive`: locally on `φ.source`, `pathPrimitive om` differs from
`chartLocalPrimitive(φ, y) om` by the constant `pathPrimitive om y`, so
their `ContMDiff` regularity and `mfderiv` agree on `φ.source`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **Local decomposition of `pathPrimitive` via a chart-line segment.**

For a global basepoint `x₀ : X` and a holomorphic 1-form `om` with
vanishing loop periods at `x₀`, the global path-primitive at any
point `x` in a chart `φ` with convex target decomposes as the
path-primitive at the chart-basepoint `y` plus the chart-local primitive
from `y` to `x`:

  `pathPrimitive h_conn x₀ om x =
   pathPrimitive h_conn x₀ om y + chartLocalPrimitive(φ, y) om x`.

Proof: pick any smooth path `α : x₀ ⇝ y` from `h_conn`, concatenate with
the chart-line segment `β : y ⇝ x`, and apply
`pathPrimitive_eq_integral_of_loopPeriodVanishes` together with
`complexChainPeriod_single_concat`. -/
theorem pathPrimitive_eq_pathPrimitive_at_chartBase_add_chartLocal
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    (x : X) (hx : x ∈ φ.source) :
    pathPrimitive h_conn x₀ om x
      = pathPrimitive h_conn x₀ om y
        + chartLocalPrimitive φ h_atlas h_target_convex y hy om x hx := by
  -- α : x₀ ⇝ y via SmoothPathConnected (Classical.choose).
  set α : SmoothPath 𝓘(ℝ, ℂ) X := (h_conn x₀ y).choose with hα_def
  have hα_src : α.src = x₀ := (h_conn x₀ y).choose_spec.1
  have hα_tgt : α.tgt = y := (h_conn x₀ y).choose_spec.2
  -- β : y ⇝ x via linearInChartSegment (chart-line).
  set β : SmoothPath 𝓘(ℝ, ℂ) X :=
    SmoothPath.linearInChartSegment φ h_atlas y x hy hx
      (Convex.segment_subset h_target_convex
        (φ.map_source hy) (φ.map_source hx))
    with hβ_def
  have hβ_src : β.src = y :=
    SmoothPath.linearInChartSegment_src φ h_atlas y x hy hx _
  have hβ_tgt : β.tgt = x :=
    SmoothPath.linearInChartSegment_tgt φ h_atlas y x hy hx _
  -- Concatenation `γ := α ⋆ β : x₀ ⇝ x`.
  have h_concat_endpoint : α.tgt = β.src := hα_tgt.trans hβ_src.symm
  set γ : SmoothPath 𝓘(ℝ, ℂ) X := α.concat β h_concat_endpoint with hγ_def
  have hγ_src : γ.src = x₀ := by
    rw [hγ_def, SmoothPath.concat_src]; exact hα_src
  have hγ_tgt : γ.tgt = x := by
    rw [hγ_def, SmoothPath.concat_tgt]; exact hβ_tgt
  -- pathPrimitive om x = complexChainPeriod (single γ) om by path-independence.
  rw [pathPrimitive_eq_integral_of_loopPeriodVanishes
      h_conn x₀ om h_loop x γ hγ_src hγ_tgt]
  -- complexChainPeriod (single γ) om
  --   = complexChainPeriod (single α) om + complexChainPeriod (single β) om.
  rw [hγ_def, complexChainPeriod_single_concat α β h_concat_endpoint om]
  -- complexChainPeriod (single α) om = pathPrimitive om y by path-independence
  -- (α is a smooth path from x₀ to y).
  rw [← pathPrimitive_eq_integral_of_loopPeriodVanishes
      h_conn x₀ om h_loop y α hα_src hα_tgt]
  -- complexChainPeriod (single β) om = chartLocalPrimitive(φ, y) om x by
  -- definitional unfolding of chartLocalPrimitive.
  rfl

end JacobianChallenge

end
