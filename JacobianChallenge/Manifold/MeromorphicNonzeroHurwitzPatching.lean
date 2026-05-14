/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroFiberFinite
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalSheet

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `HurwitzPatchingData` at every regular value

For `f : MeromorphicNonzero X` with non-constant `f.toRiemannSphere`,
this file constructs a `HurwitzPatchingData f.toRiemannSphere v` at
every regular value `v ∈ f.regularValueSet`.

The construction is one line:

  `HurwitzPatchingData.ofLocalSheets hf_cont h_fib_finite sheets`

where:
* `hf_cont` is continuity of `f.toRiemannSphere`,
* `h_fib_finite` is fiber finiteness (chip 9,
  `fiber_finite_of_mem_regularValueSet`),
* `sheets` produces the per-fiber-point `LocalSheetData` (chip 7,
  `localSheetData_at_regular`).

The resulting `HurwitzPatchingData` package supplies:
* a finite enumeration of `f.toRiemannSphere ⁻¹' {v}`,
* pairwise-disjoint open neighbourhoods `U x` at each preimage,
* a common open neighbourhood `W` of `v` with `f.toRiemannSphere ⁻¹' W
  ⊆ ⋃ x ∈ xs, U x` and `f.toRiemannSphere` injective+surjective on
  each sheet.

This is the *evenly-covered nbhd* structure of a topological covering
map.  Combined with mathlib's `IsCoveringMapOn` and
`IsCoveringMap.liftPath`, it would yield continuous path lifting on
the regular-value set — the foundation of the level-set chain.

## What ships

* `MeromorphicNonzero.hurwitzPatchingData_at_regularValue` —
  `HurwitzPatchingData f.toRiemannSphere v` at every `v ∈ f.regularValueSet`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HurwitzPatchingData` at every regular value.** Constructed via
`HurwitzPatchingData.ofLocalSheets` from chip 7 (`localSheetData_at_regular`)
and chip 9 (`fiber_finite_of_mem_regularValueSet`). -/
noncomputable def hurwitzPatchingData_at_regularValue
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet) :
    JacobianChallenge.HurwitzPatchingData f.toRiemannSphere v := by
  classical
  refine JacobianChallenge.HurwitzPatchingData.ofLocalSheets
    (JacobianChallenge.MeromorphicNonzero.toRiemannSphere_contMDiff f).continuous
    (f.fiber_finite_of_mem_regularValueSet hv) ?_
  intro x hx
  -- `hx : x ∈ f.toRiemannSphere ⁻¹' {v}`.
  have hxv : f.toRiemannSphere x = v := hx
  have hxReg : x ∈ f.regularSet :=
    f.mem_regularSet_of_preimage_regularValue hv hxv
  -- `localSheetData_at_regular` gives `LocalSheetData f.toRiemannSphere
  -- (f.toRiemannSphere x) x`; rewrite via `hxv` to land at `v`.
  have h_sheet : JacobianChallenge.LocalSheetData f.toRiemannSphere
      (f.toRiemannSphere x) x := f.localSheetData_at_regular hnc hxReg
  rw [hxv] at h_sheet
  exact h_sheet

end MeromorphicNonzero

end JacobianChallenge

end
