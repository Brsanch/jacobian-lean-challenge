/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Cotangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

set_option diagnostics.threshold 100

/-! # Smoothness of cotangent-bundle sections in chart coordinates

Mirrors the tangent-bundle pattern: a section
`ω : (x : M) → CotangentSpace I x` is `ContMDiff` iff its representative in
chart coordinates is `ContMDiff` as a map into `E →L[𝕜] 𝕜`.

For a generic vector bundle, the iff between section smoothness and
trivialization-coordinate smoothness already exists in mathlib as
`Bundle.contMDiffAt_section` and `Bundle.contMDiffWithinAt_section`. The
content of this file is to specialize those iffs to the cotangent bundle
built in `JacobianChallenge.Manifold.Cotangent`, expressed in terms of
`(cotangentBundleCore I M).coordChange`.

The chart-coordinate representative of a section `ω` at `x₀` is
```
fun x => (trivializationAt (E →L[𝕜] 𝕜) (CotangentSpace I) x₀ ⟨x, ω x⟩).2
```
which equals `(cotangentBundleCore I M).coordChange (achart H x) (achart H x₀) x (ω x)`
by `localTrivAt_snd`.

## Main results

* `cotangentBundle_trivializationAt_snd_apply` — the snd of the
  trivialization at `x₀` of a cotangent section, in terms of the cotangent
  core's `coordChange`.
* `cotangentSection_contMDiffWithinAt_iff` — within-set, at a point.
* `cotangentSection_contMDiffAt_iff` — at a point. The global form is the
  pointwise quantification of this iff and is therefore not stated separately;
  any consumer can compose it with `contMDiff_iff_contMDiffAt`.

These are the cotangent analogues of the tangent-side `Bundle.contMDiff*_section`
applications used throughout `Mathlib.Geometry.Manifold.MFDeriv.*`.

## Design notes

The file is purely an `iff` packaging layer; no new vector-bundle smoothness
content is proved here. The substantive smoothness fact — that the cotangent
core has `C^n` coordinate changes when `M` is `C^{n+1}` — already lives in
`JacobianChallenge.Manifold.Cotangent` as `cotangentBundleCore.isContMDiff`
and yields the `ContMDiffVectorBundle` instance
`CotangentBundle.contMDiffVectorBundle`. The bundle's
`MemTrivializationAtlas` instance is supplied automatically by the
`FiberBundle` instance on `CotangentSpace I`, so the generic mathlib lemmas
apply.
-/

open Bundle Set FiberBundle
open scoped Manifold Topology Bundle

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- The snd of the canonical trivialization at `x₀` applied to a section
`⟨x, ω x⟩` of the cotangent bundle equals the cotangent core's coordinate
change applied to `ω x`. This is the cotangent analogue of
`TangentBundle.trivializationAt_apply` (snd component). -/
theorem cotangentBundle_trivializationAt_snd_apply
    (ω : ∀ x, CotangentSpace I x) (x₀ x : M) :
    (trivializationAt (E →L[𝕜] 𝕜) (CotangentSpace I) x₀ ⟨x, ω x⟩).2 =
      (cotangentBundleCore I M).coordChange (achart H x) (achart H x₀) x (ω x) := by
  -- The bundle structure on `CotangentSpace I` is `(cotangentBundleCore I M).fiberBundle`,
  -- whose `trivializationAt` is `localTrivAt`. Then `localTrivAt_snd` evaluates the
  -- snd to the core's coordinate change at `(indexAt p.1, indexAt b)`, and our core's
  -- `indexAt` is `achart H` by `cotangentBundleCore_indexAt`.
  change ((cotangentBundleCore I M).toFiberBundleCore.localTrivAt x₀
      (TotalSpace.mk x (ω x))).2 = _
  rw [FiberBundleCore.localTrivAt_snd]
  rfl

/-- Within-set, at-a-point characterisation: a section `ω` of the cotangent
bundle is `C^n` within `s` at `x₀` iff its chart-coordinate
representative — `x ↦ (cotangentBundleCore I M).coordChange (achart H x) (achart H x₀) x (ω x)`
— is `C^n` within `s` at `x₀`. -/
theorem cotangentSection_contMDiffWithinAt_iff
    {n : WithTop ℕ∞} (ω : ∀ x, CotangentSpace I x) {s : Set M} {x₀ : M} :
    ContMDiffWithinAt I (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) n
        (fun x => TotalSpace.mk' (E →L[𝕜] 𝕜) x (ω x)) s x₀ ↔
      ContMDiffWithinAt I 𝓘(𝕜, E →L[𝕜] 𝕜) n
        (fun x => (cotangentBundleCore I M).coordChange
          (achart H x) (achart H x₀) x (ω x)) s x₀ := by
  rw [Bundle.contMDiffWithinAt_section]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine h.congr_of_eventuallyEq ?_ ?_
    · refine Filter.Eventually.of_forall fun x => ?_
      exact cotangentBundle_trivializationAt_snd_apply ω x₀ x
    · exact cotangentBundle_trivializationAt_snd_apply ω x₀ x₀
  · refine h.congr_of_eventuallyEq ?_ ?_
    · refine Filter.Eventually.of_forall fun x => ?_
      exact (cotangentBundle_trivializationAt_snd_apply ω x₀ x).symm
    · exact (cotangentBundle_trivializationAt_snd_apply ω x₀ x₀).symm

/-- At-a-point characterisation: a section `ω` of the cotangent bundle is
`C^n` at `x₀` iff its chart-coordinate representative is `C^n` at `x₀`. -/
theorem cotangentSection_contMDiffAt_iff
    {n : WithTop ℕ∞} (ω : ∀ x, CotangentSpace I x) {x₀ : M} :
    ContMDiffAt I (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) n
        (fun x => TotalSpace.mk' (E →L[𝕜] 𝕜) x (ω x)) x₀ ↔
      ContMDiffAt I 𝓘(𝕜, E →L[𝕜] 𝕜) n
        (fun x => (cotangentBundleCore I M).coordChange
          (achart H x) (achart H x₀) x (ω x)) x₀ := by
  simp_rw [← contMDiffWithinAt_univ]
  exact cotangentSection_contMDiffWithinAt_iff ω

end
