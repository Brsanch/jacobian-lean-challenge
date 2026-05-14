/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalBiholomorphism
import JacobianChallenge.Manifold.HurwitzPatchingDataConstruction

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Planar `OpenPartialHomeomorph` of the chart pullback at every regular point

For `f : MeromorphicNonzero X` with non-constant `f.toRiemannSphere` and a
regular point `x₀ ∈ f.regularSet`, the chart pullback `f.chartPullback x₀ :
ℂ → ℂ` admits a packaged planar `OpenPartialHomeomorph ℂ ℂ` representing the
local biholomorphism at `(chartAt ℂ x₀) x₀`.  This is the "OPH form" of
chip 5's `exists_local_biholomorphism_chartPullback`.

The OPH form is the consumer-facing shape for downstream chips that need a
canonical planar inverse (rather than a `Classical.choose`-extracted
existential).  It is built via mathlib's
`HasStrictFDerivAt.toOpenPartialHomeomorph`.

## What ships

* `MeromorphicNonzero.chartPullback_oph` — the planar
  `OpenPartialHomeomorph ℂ ℂ` representing `f.chartPullback x₀` as a
  local biholomorphism at `(chartAt ℂ x₀) x₀`.

* `MeromorphicNonzero.mem_source_chartPullback_oph` — the base point
  lies in the source.

* `MeromorphicNonzero.coe_chartPullback_oph` — the underlying function
  of `chartPullback_oph` is `f.chartPullback x₀`.

The manifold-level `LocalSheetData` construction (chip 6+) consumes this
OPH plus chart bookkeeping.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter Function
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- The planar `OpenPartialHomeomorph ℂ ℂ` packaging the local
biholomorphism of `f.chartPullback x₀` at `(chartAt ℂ x₀) x₀`.

Built from `HasStrictFDerivAt.toOpenPartialHomeomorph` applied to the
non-zero-derivative analytic chart pullback. -/
noncomputable def chartPullback_oph
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {x₀ : X} (hx₀ : x₀ ∈ f.regularSet) :
    OpenPartialHomeomorph ℂ ℂ :=
  let h_an : AnalyticAt ℂ (f.chartPullback x₀) ((chartAt ℂ x₀) x₀) :=
    f.analyticAt_chartPullback x₀
  let h_dne : deriv (f.chartPullback x₀) ((chartAt ℂ x₀) x₀) ≠ 0 :=
    f.deriv_chartPullback_ne_zero_of_regular hnc hx₀
  let hsd : HasStrictDerivAt (f.chartPullback x₀)
      (deriv (f.chartPullback x₀) ((chartAt ℂ x₀) x₀)) ((chartAt ℂ x₀) x₀) :=
    h_an.hasStrictDerivAt
  let hsfd : HasStrictFDerivAt (f.chartPullback x₀)
      (ContinuousLinearEquiv.unitsEquivAut ℂ
          (Units.mk0 (deriv (f.chartPullback x₀) ((chartAt ℂ x₀) x₀)) h_dne) :
        ℂ →L[ℂ] ℂ) ((chartAt ℂ x₀) x₀) :=
    hsd.hasStrictFDerivAt_equiv h_dne
  hsfd.toOpenPartialHomeomorph (f.chartPullback x₀)

/-- The base point `(chartAt ℂ x₀) x₀` lies in the source of
`chartPullback_oph`. -/
lemma mem_source_chartPullback_oph
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {x₀ : X} (hx₀ : x₀ ∈ f.regularSet) :
    (chartAt ℂ x₀) x₀ ∈ (f.chartPullback_oph hnc hx₀).source := by
  have h_an : AnalyticAt ℂ (f.chartPullback x₀) ((chartAt ℂ x₀) x₀) :=
    f.analyticAt_chartPullback x₀
  have h_dne : deriv (f.chartPullback x₀) ((chartAt ℂ x₀) x₀) ≠ 0 :=
    f.deriv_chartPullback_ne_zero_of_regular hnc hx₀
  exact (h_an.hasStrictDerivAt.hasStrictFDerivAt_equiv h_dne).mem_toOpenPartialHomeomorph_source

/-- The underlying function of `chartPullback_oph` is the chart pullback. -/
lemma coe_chartPullback_oph
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {x₀ : X} (hx₀ : x₀ ∈ f.regularSet) :
    ((f.chartPullback_oph hnc hx₀) : ℂ → ℂ) = f.chartPullback x₀ := by
  have h_an : AnalyticAt ℂ (f.chartPullback x₀) ((chartAt ℂ x₀) x₀) :=
    f.analyticAt_chartPullback x₀
  have h_dne : deriv (f.chartPullback x₀) ((chartAt ℂ x₀) x₀) ≠ 0 :=
    f.deriv_chartPullback_ne_zero_of_regular hnc hx₀
  exact (h_an.hasStrictDerivAt.hasStrictFDerivAt_equiv h_dne).toOpenPartialHomeomorph_coe

/-- The source of `chartPullback_oph` is open. -/
lemma isOpen_source_chartPullback_oph
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {x₀ : X} (hx₀ : x₀ ∈ f.regularSet) :
    IsOpen (f.chartPullback_oph hnc hx₀).source :=
  (f.chartPullback_oph hnc hx₀).open_source

end MeromorphicNonzero

end JacobianChallenge

end
