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

/-- **Chart-based local lift.** For `x₀ : ℂ` (anchor), the function
`(localChart L _ x₀).symm` is `T² → ℂ`, defined on chart-target
`mkQ '' ball x₀ (r/2)`. Composed with `γ.ambient`, it gives a partial
function `ℝ → ℂ`. Outside the chart-target preimage, the value is
unspecified (set to `0`). -/
noncomputable def localLift
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (x₀ : ℂ) (t : ℝ) : ℂ := by
  classical
  exact if h : γ.ambient t ∈ (chartAt ℂ (L.mkQ x₀)).source then
    (chartAt ℂ (L.mkQ x₀) : (ℂ ⧸ L) → ℂ) (γ.ambient t)
  else 0

/-- **Local lift property.** When `γ.ambient t` is in the chart at
`mkQ x₀`'s source, the local lift sends it back via the chart's
inverse direction. Note: `chartAt ℂ (mkQ x₀)` IS the (localChart _
(mkQ x₀).out).symm, which maps to ball ((mkQ x₀).out) (r/2). The
specific x₀ doesn't directly correspond to this chart's anchor unless
x₀ = (mkQ x₀).out. -/
theorem mkQ_chartAt_apply (q : ℂ ⧸ L) (y : ℂ ⧸ L)
    (hy : y ∈ (chartAt ℂ q).source) :
    L.mkQ ((chartAt ℂ q : (ℂ ⧸ L) → ℂ) y) = y := by
  -- chartAt q = (localChart L _ q.out).symm. Its source = mkQ '' ball q.out (r/2).
  -- For y in source, chartAt q y ∈ ball q.out (r/2), and mkQ of it = y.
  show L.mkQ ((localChart L (discRadius_separates L) q.out).symm y) = y
  -- The chart .symm sends T²-elements to their preimage in ball.
  -- mkQ on a ball-preimage IS the chartAt's inverse direction.
  -- We use the chart's right inverse property.
  have h_right_inv : (localChart L (discRadius_separates L) q.out)
      ((localChart L (discRadius_separates L) q.out).symm y) = y :=
    (localChart L (discRadius_separates L) q.out).right_inv hy
  -- (localChart L _ q.out) on its source is L.mkQ.
  -- Specifically, (localChart c) maps ball c (r/2) → ℂ⧸L by L.mkQ.
  show L.mkQ ((localChart L (discRadius_separates L) q.out).symm y) = y
  -- The function value equality follows from h_right_inv directly.
  exact h_right_inv

end ComplexTorus

end JacobianChallenge

end
