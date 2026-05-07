/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import JacobianChallenge.Manifold.SmoothPathIntegral

/-! # Chart-coordinate compatibility for `SmoothPath.integrate`

This file develops the first chart-coordinate identities used by the
R5 partition-of-unity Stokes route. The eventual target of that route
is the boundary identity `∫_{∂c} ω = ∫_c dω`. Before we get to Stokes
proper, we need to know that the path integral

    `γ.integrate ω = ∫_{0}^{1} ω(γ t)(γ' t) dt`

(introduced in `SmoothPathIntegral.lean`, ZZ139) admits a clean
chart-coordinate representation: when the smooth path lies entirely
inside the source of a chart `φ`, its velocity push-forward through
`φ` equals the velocity of the chart-image curve `φ ∘ γ` against the
trivial-model derivative on `H` (regarded with its own tautological
manifold structure).

## Main results

* `SmoothPath.integrate_eq_intervalIntegral` — the unfolding lemma:
  `γ.integrate ω = ∫_{0}^{1} applyCotangent (ω (γ.ambient t)) (γ.velocity t) dt`.
  This is `rfl`-true and is exposed as a named lemma so downstream
  files can rewrite without unfolding `integrate`.

* `SmoothPath.mdifferentiableAt_chart_comp_ambient` — when the chosen
  ambient extension of `γ` lands inside a chart's source at parameter
  `t`, the composite curve `φ ∘ γ.ambient` is `MDifferentiableAt` at
  `t` (against `𝓘(ℝ, ℝ)` and the manifold model `I` on `H`).

* `SmoothPath.mfderiv_chart_comp_ambient_apply_one` — the chain-rule
  identity for the chart-image curve at `t`:
  `mfderiv 𝓘(ℝ,ℝ) I (φ ∘ γ.ambient) t (1 : ℝ)`
  `= (mfderiv I I φ (γ.ambient t)) (γ.velocity t)`.

This is exactly the "velocity in chart coordinates" identity that the
chart-pulled integrand will need: the right-hand side is the chart
push-forward of `γ.velocity t`, which is the tangent vector at the
chart point `φ (γ.ambient t)`.

## Scope notes

This chip deliberately stops short of constructing a `SmoothOneForm`-
valued chart-pullback (that requires building the cotangent-bundle
pullback, ZZ?? on the roadmap) and stops short of the global Stokes
identity. We provide only the velocity-side compatibility lemma; the
covector-side (chart-pull of `ω`) and the integral-side (a change-of-
variables in `t`) are subsequent chips.

The chart `φ : OpenPartialHomeomorph X H` is taken as an arbitrary
member of `atlas H X`, so the lemma applies uniformly to `chartAt H x`
and to charts obtained by composition with elements of the
`contDiffGroupoid`. The hypothesis `γ.ambient t ∈ φ.source` is the
familiar "the path stays in the chart at parameter `t`" condition.
-/

open scoped Manifold Topology
open MeasureTheory intervalIntegral

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace SmoothPath

/-- **Definitional unfolding of the path integral.** Stated as a named
lemma so downstream files can rewrite without exposing the
`integrand` / `applyCotangent` plumbing. -/
theorem integrate_eq_intervalIntegral (γ : SmoothPath I X)
    (ω : SmoothOneForm I X) :
    γ.integrate ω
      = ∫ t in (0 : ℝ)..1,
          applyCotangent (ω (γ.ambient t)) (γ.velocity t) := rfl

/-- Auxiliary: the ambient extension `γ.ambient : ℝ → X` is
`MDifferentiableAt` at every parameter `t`. This is just the
`MDifferentiable` projection of its `ContMDiff ⊤` smoothness. -/
lemma mdifferentiableAt_ambient (γ : SmoothPath I X) (t : ℝ) :
    MDifferentiableAt 𝓘(ℝ, ℝ) I γ.ambient t := by
  have h : ContMDiff 𝓘(ℝ, ℝ) I ⊤ γ.ambient := γ.ambient_contMDiff
  -- `ContMDiffAt ⊤ ⇒ MDifferentiableAt` (since `1 ≤ ⊤`).
  have hAt : ContMDiffAt 𝓘(ℝ, ℝ) I ⊤ γ.ambient t := h t
  -- `ContMDiffAt.mdifferentiableAt` needs `n ≠ 0`; here `n = ⊤ ≠ 0`.
  refine hAt.mdifferentiableAt ?_
  exact (lt_of_lt_of_le (zero_lt_one' (WithTop ℕ∞)) le_top).ne'

/-- Each chart of the manifold `X` is `MDifferentiableAt` every point
of its source, against the model `I` on both sides. This is the
mathlib lemma `mdifferentiableAt_atlas` specialised to the cotangent
bundle's regularity downcast (`IsManifold I 1 X`). -/
lemma mdifferentiableAt_chart {φ : OpenPartialHomeomorph X H}
    (h_atlas : φ ∈ atlas H X) {x : X} (hx : x ∈ φ.source) :
    MDifferentiableAt I I φ x :=
  mdifferentiableAt_atlas (I := I) h_atlas hx

/-- **Chart-image curve is `MDifferentiableAt`.** When the ambient
extension of `γ` lands inside `φ.source` at parameter `t`, the
composite `φ ∘ γ.ambient : ℝ → H` is `MDifferentiableAt` at `t`
(against `𝓘(ℝ, ℝ)` on the source and the manifold model `I` on the
target `H`). -/
theorem mdifferentiableAt_chart_comp_ambient (γ : SmoothPath I X)
    {φ : OpenPartialHomeomorph X H} (h_atlas : φ ∈ atlas H X)
    {t : ℝ} (h_in_source : γ.ambient t ∈ φ.source) :
    MDifferentiableAt 𝓘(ℝ, ℝ) I ((φ : X → H) ∘ γ.ambient) t :=
  (mdifferentiableAt_chart h_atlas h_in_source).comp t
    (γ.mdifferentiableAt_ambient t)

/-- **Chain rule for the chart-image curve.** The mfderiv of
`φ ∘ γ.ambient` at parameter `t`, applied to the canonical tangent
vector `(1 : ℝ)`, equals the chart push-forward of the velocity
`γ.velocity t`. This is the velocity-side of the chart-pullback
identity for the path integral. -/
theorem mfderiv_chart_comp_ambient_apply_one (γ : SmoothPath I X)
    {φ : OpenPartialHomeomorph X H} (h_atlas : φ ∈ atlas H X)
    {t : ℝ} (h_in_source : γ.ambient t ∈ φ.source) :
    (mfderiv 𝓘(ℝ, ℝ) I ((φ : X → H) ∘ γ.ambient) t : ℝ →L[ℝ] _) (1 : ℝ)
      = (mfderiv I I (φ : X → H) (γ.ambient t) : E →L[ℝ] _)
          (γ.velocity t) := by
  have hg : MDifferentiableAt I I (φ : X → H) (γ.ambient t) :=
    mdifferentiableAt_chart h_atlas h_in_source
  have hf : MDifferentiableAt 𝓘(ℝ, ℝ) I γ.ambient t :=
    γ.mdifferentiableAt_ambient t
  -- Apply the manifold chain rule pointwise.
  have hcomp :=
    mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := I)
      (f := γ.ambient) (g := (φ : X → H)) (x := t) hg hf (1 : ℝ)
  -- Unfold `velocity` on the right.
  change (mfderiv 𝓘(ℝ, ℝ) I ((φ : X → H) ∘ γ.ambient) t) (1 : ℝ) = _
  rw [hcomp]
  rfl

end SmoothPath

end
