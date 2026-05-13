/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzManifold
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Local analytic inverse of the chart pullback (zz385)

For an `ω`-smooth, globally injective `f : X → Y` between complex
1-manifolds, the chart pullback
`g := (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm : ℂ → ℂ`
is analytic at `z₀ := (chartAt ℂ x) x` with non-vanishing derivative
(zz384). Mathlib's `AnalyticAt.analyticAt_localInverse` therefore yields
an analytic local inverse `g.localInverse : ℂ → ℂ` with both
left-inverse and right-inverse properties holding eventually near `z₀`
and `g z₀`.

This chip packages those three facts (analyticity of the inverse,
local-left-inverse property, local-right-inverse property) in a single
existential. The package is the input shape expected by the gluing chip
that lifts to a manifold-level local inverse of `f`.

## Anti-cheat

* No `axiom`, no `sorry`.
* No signature changes to any pre-existing definition or theorem.
-/

noncomputable section

open scoped Topology Manifold ContDiff
open Set Filter Metric

namespace JacobianChallenge
namespace Manifold

universe u v

/-- **Chart-pullback local analytic inverse.**

For `f : X → Y` `ω`-smooth, globally injective, between complex
1-manifolds, the chart pullback at `x` admits a (mathlib-supplied)
analytic local inverse. The witness is `g.localInverse` from the
inverse function theorem; the conclusion records analyticity at
`g (φ x) = ψ (f x)` together with both eventual inverse properties. -/
theorem ContMDiff.chartPullback_localInverse_of_injective
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y}
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hinj : Function.Injective f) (x : X) :
    ∃ h : ℂ → ℂ,
      AnalyticAt ℂ h ((chartAt ℂ (f x)) (f x)) ∧
      (∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
          h (((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z) = z) ∧
      (∀ᶠ w in 𝓝 (((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
                      ((chartAt ℂ x) x)),
          ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) (h w) = w) := by
  -- Names.
  set φ : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hφ_def
  set ψ : OpenPartialHomeomorph Y ℂ := chartAt ℂ (f x) with hψ_def
  set g : ℂ → ℂ := ψ ∘ f ∘ φ.symm with hg_def
  set z₀ : ℂ := φ x with hz₀_def
  -- Analyticity of `g` at `z₀` and non-vanishing derivative.
  have h_an : AnalyticAt ℂ g z₀ :=
    JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback hf x
  have h_deriv_ne :
      deriv g z₀ ≠ 0 :=
    ContMDiff.deriv_chart_pullback_ne_zero_of_injective hf hinj x
  -- Mathlib's `HasStrictDerivAt` from analyticity.
  have h_strict : HasStrictDerivAt g (deriv g z₀) z₀ := h_an.hasStrictDerivAt
  -- The local inverse.
  set h : ℂ → ℂ := h_strict.localInverse g (deriv g z₀) z₀ h_deriv_ne with hh_def
  -- Analyticity of the local inverse at `g z₀ = ψ (f x)`.
  have h_inv_an_at_gz₀ : AnalyticAt ℂ h (g z₀) :=
    h_an.analyticAt_localInverse h_deriv_ne
  -- Identify `g z₀` with `ψ (f x)`. We have z₀ = φ x; φ.left_inv at mem_chart_source
  -- gives φ.symm (φ x) = x, so g z₀ = ψ (f (φ.symm (φ x))) = ψ (f x).
  have hφ_left : φ.symm z₀ = x := by
    rw [hz₀_def]; exact φ.left_inv (ChartedSpace.mem_chart_source x)
  have hgz₀ : g z₀ = ψ (f x) := by
    simp [hg_def, Function.comp_apply, hφ_left]
  -- Convert the analyticity to be at `ψ (f x)`.
  have h_inv_an : AnalyticAt ℂ h (ψ (f x)) := hgz₀ ▸ h_inv_an_at_gz₀
  refine ⟨h, h_inv_an, ?_, ?_⟩
  · -- Eventually-left-inverse: h (g z) = z for z near z₀.
    exact h_strict.eventually_left_inverse h_deriv_ne
  · -- Eventually-right-inverse: g (h w) = w for w near g z₀.
    exact h_strict.eventually_right_inverse h_deriv_ne

end Manifold
end JacobianChallenge

end
