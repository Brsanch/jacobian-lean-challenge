/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalSheet
import JacobianChallenge.Manifold.MeromorphicNonzeroRegularValueSet

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Fiber finiteness at every regular value

For `f : MeromorphicNonzero X` with non-constant `f.toRiemannSphere`,
the fiber `f.toRiemannSphere ⁻¹' {v}` is **finite** at every regular
value `v ∈ f.regularValueSet`.

## Argument

Each preimage `x ∈ f.toRiemannSphere ⁻¹' {v}` is a regular point
(because if `x` were in `f.criticalSet`, then `v = f.toRiemannSphere x`
would lie in `f.criticalValues`, contradicting `v ∈ f.regularValueSet`).
Being in `f.regularSet` means `x` admits an open neighbourhood `U_x`
on which `f.toRiemannSphere` is injective — so the fiber's intersection
with `U_x` is exactly `{x}`.  In other words, every fiber point is
*isolated in the fiber*.

The fiber is closed in `X` (preimage of a singleton under continuous
`f.toRiemannSphere`; `RiemannSphere` is T1), hence compact (closed in
compact `X`).  A locally-finite compact set is finite: cover by the
isolating neighbourhoods, extract a finite subcover, each cover element
meets the fiber in at most one point.

## What ships

* `MeromorphicNonzero.fiber_finite_of_mem_regularValueSet` —
  the headline.
* `MeromorphicNonzero.fiber_isClosed` — closedness of the fiber
  (preimage of singleton under continuous `f.toRiemannSphere`,
  any value, regular or not).

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- The fiber `f.toRiemannSphere ⁻¹' {v}` is closed in `X` (preimage of
a singleton in T1 `RiemannSphere` under continuous `f.toRiemannSphere`). -/
theorem fiber_isClosed (f : MeromorphicNonzero X) (v : RiemannSphere) :
    IsClosed (f.toRiemannSphere ⁻¹' {v}) :=
  (T1Space.t1 v).preimage
    (JacobianChallenge.MeromorphicNonzero.toRiemannSphere_contMDiff f).continuous

/-- Every preimage of a regular value is a regular point. If `v ∈
f.regularValueSet` and `x ∈ f.toRiemannSphere ⁻¹' {v}`, then
`x ∈ f.regularSet`. -/
lemma mem_regularSet_of_preimage_regularValue
    (f : MeromorphicNonzero X) {v : RiemannSphere}
    (hv : v ∈ f.regularValueSet) {x : X} (hx : f.toRiemannSphere x = v) :
    x ∈ f.regularSet := by
  -- Contrapositive: if x ∈ criticalSet, then v ∈ criticalValues.
  by_contra hxnc
  rw [regularSet_eq_compl_criticalSet, mem_compl_iff, not_not] at hxnc
  apply hv
  exact ⟨x, hxnc, hx⟩

/-- **Fiber finiteness at every regular value.**

For non-constant `f.toRiemannSphere` and `v ∈ f.regularValueSet`, the
fiber `f.toRiemannSphere ⁻¹' {v}` is finite. -/
theorem fiber_finite_of_mem_regularValueSet
    (f : MeromorphicNonzero X)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet) :
    (f.toRiemannSphere ⁻¹' {v}).Finite := by
  classical
  set F : Set X := f.toRiemannSphere ⁻¹' {v} with hF_def
  -- F is closed and hence compact (in compact X).
  have hF_closed : IsClosed F := f.fiber_isClosed v
  have hF_compact : IsCompact F := hF_closed.isCompact
  -- Per-fiber-point isolation hypothesis.
  have h_loc :
      ∀ x ∈ F, ∃ U : Set X, U ∈ 𝓝 x ∧ ∀ y ∈ F, y ∈ U → y = x := by
    intro x hxF
    have hxRS : f.toRiemannSphere x = v := hxF
    have hxReg : x ∈ f.regularSet :=
      f.mem_regularSet_of_preimage_regularValue hv hxRS
    obtain ⟨U, hU_nhds, hU_inj⟩ := hxReg
    refine ⟨U, hU_nhds, ?_⟩
    intro y hyF hyU
    have hx_mem : x ∈ U := mem_of_mem_nhds hU_nhds
    have h_eq : f.toRiemannSphere y = f.toRiemannSphere x := by
      have hyv : f.toRiemannSphere y = v := hyF
      rw [hyv, hxRS]
    exact hU_inj hyU hx_mem h_eq
  -- Convert the family into a function-valued isolation choice.
  choose! U_F hU_F_nhds hU_F_isol using h_loc
  -- Compactness gives a finite subcover.
  obtain ⟨t, ht_sub_F, ht_cover⟩ :=
    hF_compact.elim_nhds_subcover U_F hU_F_nhds
  -- `F ⊆ t` via isolation: each cover element meets `F` only at its
  -- center.
  have hF_sub_t : F ⊆ (t : Set X) := by
    intro y hyF
    obtain ⟨x, hxt, hyU⟩ := mem_iUnion₂.mp (ht_cover hyF)
    have hxF : x ∈ F := ht_sub_F x hxt
    have h_eq : y = x := hU_F_isol x hxF y hyF hyU
    rw [h_eq]; exact hxt
  exact t.finite_toSet.subset hF_sub_t

/-- **Corollary: fiber is `Set.Finite` as a subset of `X`** — restated
in the consumer-facing form (same content). -/
theorem fiber_setFinite_of_mem_regularValueSet
    (f : MeromorphicNonzero X)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet) :
    Set.Finite (f.toRiemannSphere ⁻¹' {v}) :=
  f.fiber_finite_of_mem_regularValueSet hv

end MeromorphicNonzero

end JacobianChallenge

end
