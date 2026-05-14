/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalBiholomorphism
import JacobianChallenge.Manifold.CriticalValuesFiniteUnconditional
import JacobianChallenge.Manifold.CriticalSetClosed

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Local biholomorphism of the chart pullback at every regular point

For `f : MeromorphicNonzero X` on a compact connected complex 1-manifold
`X` with non-constant `f.toRiemannSphere`, at every regular point
`x ∈ f.regularSet` the **chart pullback**

  `f.chartPullback x := (chartAt ℂ (f.toRiemannSphere x)) ∘
                         f.toRiemannSphere ∘ (chartAt ℂ x).symm`

is a planar holomorphic function with non-zero derivative at
`(chartAt ℂ x) x`, hence is a local biholomorphism there.

The non-zero-derivative claim is pulled directly from the
`DerivBridgeData` machinery that drives the unconditional finiteness
of the critical-value set
(`Manifold/CriticalValuesFiniteUnconditional.lean`): the `hCompat` field
of `derivBridgeData_unconditional f hnc x` gives the iff

  `x ∈ f.criticalSet ↔ deriv (f.chartPullback x) ((chartAt ℂ x) x) = 0`,

so `x ∈ f.regularSet` (i.e. `x ∉ f.criticalSet`) forces the derivative
to be non-zero.  Applying the planar
`AnalyticAt.exists_local_biholomorphism` yields the planar local inverse.

## What ships

* `MeromorphicNonzero.chartPullback f x` — the literal chart pullback.

* `MeromorphicNonzero.analyticAt_chartPullback` — analyticity at
  `(chartAt ℂ x) x` via `contMDiff_omega_analyticAt_chart_pullback`.

* `MeromorphicNonzero.deriv_chartPullback_ne_zero_of_regular` —
  non-zero derivative at regular points, under non-constancy.

* `MeromorphicNonzero.exists_local_biholomorphism_chartPullback` —
  planar local biholomorphism at every regular point.

This is the **planar** local-biholomorphism layer.  The manifold-level
lift to a local homeomorphism of `f.toRiemannSphere : X → RiemannSphere`
is consumed downstream by the path-lifting / level-set chain
construction.

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

/-- **Chart pullback of `f.toRiemannSphere` based at `x`.** The literal
expression `(chartAt ℂ (f.toRiemannSphere x)) ∘ f.toRiemannSphere ∘
(chartAt ℂ x).symm`, on which the analytic IFT operates. -/
def chartPullback (f : MeromorphicNonzero X) (x : X) : ℂ → ℂ :=
  (chartAt ℂ (f.toRiemannSphere x)) ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm

/-- **Analyticity of the chart pullback at `(chartAt ℂ x) x`.** Direct
consequence of ω-smoothness of `f.toRiemannSphere`
(`MeromorphicNonzero.toRiemannSphere_contMDiff`) and ZZ24's
`contMDiff_omega_analyticAt_chart_pullback`. -/
theorem analyticAt_chartPullback (f : MeromorphicNonzero X) (x : X) :
    _root_.AnalyticAt ℂ (f.chartPullback x) ((chartAt ℂ x) x) :=
  JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback
    (JacobianChallenge.MeromorphicNonzero.toRiemannSphere_contMDiff f) x

/-- **Non-zero derivative at every regular point.**

For non-constant `f.toRiemannSphere` and `x ∈ f.regularSet`,
`deriv (f.chartPullback x) ((chartAt ℂ x) x) ≠ 0`.

Proof. The `DerivBridgeData` consumed by `criticalSet_finite_unconditional`
provides `hCompat x D.hxV : x ∈ f.criticalSet ↔
deriv (f.chartPullback x) ((chartAt ℂ x) x) = 0`. The membership
`x ∈ f.regularSet` is exactly `x ∉ f.criticalSet` (via
`criticalSet_eq_compl_regularSet`), so the iff forces the derivative
to be non-zero. -/
theorem deriv_chartPullback_ne_zero_of_regular
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {x : X} (hx : x ∈ f.regularSet) :
    deriv (f.chartPullback x) ((chartAt ℂ x) x) ≠ 0 := by
  -- Recover `x ∉ criticalSet` from regular-set membership.
  have hncrit : x ∉ f.criticalSet := by
    rw [criticalSet_eq_compl_regularSet]
    intro hc
    exact hc hx
  -- Build the per-point `DerivBridgeData`.
  set D : JacobianChallenge.Manifold.DerivBridgeData f x :=
    JacobianChallenge.Manifold.derivBridgeData_unconditional f hnc x with hD_def
  -- Extract `hCompat` at the central point `x`.
  have h_iff : x ∈ f.criticalSet ↔
      deriv (f.chartPullback x) ((chartAt ℂ x) x) = 0 :=
    D.hCompat x D.hxV
  -- `D.F = f.chartPullback x` definitionally (literal chart pullback),
  -- so `h_iff` is the desired iff.
  intro h_zero
  exact hncrit (h_iff.mpr h_zero)

/-- **Planar local biholomorphism at every regular point.**

For non-constant `f.toRiemannSphere` and `x ∈ f.regularSet`, the chart
pullback `f.chartPullback x` admits a planar local inverse `φ_inv` on
neighbourhoods `U` of `(chartAt ℂ x) x` and `V` of
`f.chartPullback x ((chartAt ℂ x) x)`, with `φ_inv` analytic at the
base value.  Composition of `analyticAt_chartPullback` +
`deriv_chartPullback_ne_zero_of_regular` +
`AnalyticAt.exists_local_biholomorphism`. -/
theorem exists_local_biholomorphism_chartPullback
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {x : X} (hx : x ∈ f.regularSet) :
    ∃ (U : Set ℂ), U ∈ 𝓝 ((chartAt ℂ x) x) ∧
      ∃ (V : Set ℂ), V ∈ 𝓝 (f.chartPullback x ((chartAt ℂ x) x)) ∧
        ∃ (φ_inv : ℂ → ℂ),
          Set.MapsTo (f.chartPullback x) U V ∧
          Set.MapsTo φ_inv V U ∧
          Set.LeftInvOn φ_inv (f.chartPullback x) U ∧
          Set.RightInvOn φ_inv (f.chartPullback x) V ∧
          _root_.AnalyticAt ℂ φ_inv (f.chartPullback x ((chartAt ℂ x) x)) :=
  JacobianChallenge.Manifold.AnalyticAt.exists_local_biholomorphism
    (f.analyticAt_chartPullback x)
    (f.deriv_chartPullback_ne_zero_of_regular hnc hx)

end MeromorphicNonzero

end JacobianChallenge

end
