/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalBiholomorphism
import JacobianChallenge.Manifold.MeromorphicNonzeroTraceAt
import JacobianChallenge.Manifold.DegreeWellDefined

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `fiberFinset` cardinality is constant across regular values

For a non-constant `f : MeromorphicNonzero X` on a compact connected
complex 1-manifold `X`, the cardinality of the fibre `f⁻¹({v})` over a
regular value `v` does not depend on which regular value is chosen — it
equals the topological degree `degreeFiber f.toRiemannSphere`.

The bridge is `RegularValueWitnessReg`-valued: every regular value
`v ∈ f.regularValueSet` produces a `RegularValueWitnessReg
f.toRiemannSphere` whose `.card` equals `(f.fiberFinset hv).card`.
Composing with `degreeFiber_eq_card_of_regular_witness` gives the
constancy statement.

The chart-pullback-derivative-nonzero certificate inlined in
`RegularValueWitnessReg` is supplied by
`MeromorphicNonzero.deriv_chartPullback_ne_zero_of_regular`: a preimage
of a regular value lies in `f.regularSet`
(`mem_regularSet_of_preimage_regularValue`), and the chart pullback
based at any regular point has nonzero derivative.

This is the cardinality input for the "surjectivity at general `t`"
discharge of `RegularLevelSetLatticeClause` (the only remaining
substantive analytic input for `AbelHypothesis B` in general genus).

## What ships

* `MeromorphicNonzero.regularValueWitnessReg_of_mem_regularValueSet` —
  promotes a regular-value-set membership to a `RegularValueWitnessReg`.
* `MeromorphicNonzero.fiberFinset_card_eq_degreeFiber` — bridge to
  the topological degree.
* `MeromorphicNonzero.fiberFinset_card_const` — the constancy
  statement: `(fiberFinset hv₁).card = (fiberFinset hv₂).card` for
  any two regular values.

No `sorry`, no `axiom`. -/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Regular-value-set membership produces a `RegularValueWitnessReg`.**

Given `v ∈ f.regularValueSet`, package the regular value, fibre
finiteness, and chart-pullback-derivative-nonzero certificate into a
`JacobianChallenge.ContMDiff.RegularValueWitnessReg f.toRiemannSphere`. -/
def regularValueWitnessReg_of_mem_regularValueSet
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet) :
    JacobianChallenge.ContMDiff.RegularValueWitnessReg f.toRiemannSphere where
  toWitness :=
    { value := v
      fiber_finite := f.fiber_finite_of_mem_regularValueSet hv }
  is_regular := by
    intro x hx
    -- `hx : x ∈ f.toRiemannSphere ⁻¹' {v}`, i.e. `f.toRiemannSphere x = v`.
    have hxv : f.toRiemannSphere x = v := hx
    -- A preimage of a regular value lies in the regular set.
    have hxReg : x ∈ f.regularSet :=
      f.mem_regularSet_of_preimage_regularValue hv hxv
    -- Chart pullback has nonzero derivative at every regular point.
    have h_ne : deriv (f.chartPullback x) ((chartAt ℂ x) x) ≠ 0 :=
      f.deriv_chartPullback_ne_zero_of_regular hnc hxReg
    -- `f.chartPullback x = (chartAt ℂ (f.toRiemannSphere x)) ∘ f.toRiemannSphere ∘
    --   (chartAt ℂ x).symm`. Rewriting `f.toRiemannSphere x = v` gives the
    -- shape required by `RegularValueWitnessReg`.
    have h_eq : f.chartPullback x =
        (chartAt ℂ v) ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm := by
      unfold chartPullback
      rw [hxv]
    rw [← h_eq]
    exact h_ne

/-- **Card-coherence with the underlying witness.** The
`fiberFinset hv` and the `RegularValueWitnessReg`'s `card` are both
`(f.fiber_finite_of_mem_regularValueSet hv).toFinset.card`, so they are
definitionally equal. -/
@[simp] lemma card_regularValueWitnessReg_of_mem_regularValueSet
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet) :
    (regularValueWitnessReg_of_mem_regularValueSet f hnc hv).card
      = (f.fiberFinset hv).card := rfl

/-- **Bridge to the topological degree.** For any regular value `v`,
the cardinality of the fibre `f⁻¹({v})` equals
`degreeFiber f.toRiemannSphere`. -/
theorem fiberFinset_card_eq_degreeFiber
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet) :
    (f.fiberFinset hv).card
      = JacobianChallenge.ContMDiff.degreeFiber f.toRiemannSphere
          f.toRiemannSphere_contMDiff := by
  -- Chain: fiberFinset card = witness card = degreeFiber.
  rw [← card_regularValueWitnessReg_of_mem_regularValueSet f hnc hv]
  exact (degreeFiber_eq_card_of_regular_witness
    f.toRiemannSphere f.toRiemannSphere_contMDiff hnc
    (regularValueWitnessReg_of_mem_regularValueSet f hnc hv)).symm

/-- **Constancy of the fibre cardinality across regular values.** For
any two regular values, the fibres have the same cardinality. -/
theorem fiberFinset_card_const
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v₁ v₂ : RiemannSphere}
    (hv₁ : v₁ ∈ f.regularValueSet) (hv₂ : v₂ ∈ f.regularValueSet) :
    (f.fiberFinset hv₁).card = (f.fiberFinset hv₂).card := by
  rw [fiberFinset_card_eq_degreeFiber f hnc hv₁,
      fiberFinset_card_eq_degreeFiber f hnc hv₂]

end MeromorphicNonzero

end JacobianChallenge

end
