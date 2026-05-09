/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.JacobianPullbackWeighted
import JacobianChallenge.Manifold.HNTotalFromRamificationSum
import JacobianChallenge.Manifold.FibresFiniteUnconditional

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Honest `Jacobian.pullback` conditional on the named obligation (ZZ179g)

Final structural composer in the multiplicity-weighted pullback chain.
Given `Owed.degree.ramificationSumEqualsDegree_statement X Y` as a
hypothesis (the single named analytic obligation, owed at the mathlib
pin and discharged by the Riemann-Hurwitz argument in a follow-up
chip), produces the honest `Jacobian Y →ₜ+ Jacobian X` that
`Basic.lean.Jacobian.pullback` will swap its zero-stub body for.

## Cases

* **Constant `f`**: returns the zero `→ₜ+`. This matches the natural
  classical convention (constant maps have zero pullback on Pic⁰; the
  fibre cardinality formula degenerates).
* **Non-constant `f`**: derives `hf_finite_fibres` from ZZ48
  (`fibres_finite_statement_holds_unconditional`), derives `hN_total`
  from `h_rsum` via the ZZ179e bridge with `e :=
  manifoldRamificationIndex f` and `N := degreeFiber f hf`, and
  delegates to `Jacobian.pullbackWeighted` (ZZ179f).

## What is proved

The composer itself is purely structural — it is type-correct and
discharges by `Classical.byCases` on `IsConstantMap`. No analytic
content lives here. The single open obligation is `h_rsum`, owed in
`Manifold/RamificationSumEqualsDegree.lean`.

When `h_rsum` is discharged, the body swap in `Basic.lean` becomes a
one-line edit, and OPEN.md items 8, 13, 21, 22, 24 unblock together.

No `sorry`, no `axiom`. -/

@[expose] public section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace Jacobian

universe u v

/-- **Honest pullback conditional on the Riemann-Hurwitz total-weight
identity.** Cases on `IsConstantMap f`: constant ⇒ zero, non-constant ⇒
`Jacobian.pullbackWeighted` with the `e := manifoldRamificationIndex f`
weight and `N := degreeFiber f hf`. -/
noncomputable def pullbackHonest_of_rsum
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [DecidableEq X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_rsum : JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_statement X Y)
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian Y →ₜ+ Jacobian X := by
  classical
  by_cases hc : JacobianChallenge.IsConstantMap f
  · -- Constant case: zero hom.
    exact 0
  · -- Non-constant case: weighted pullback via the analytic hypothesis.
    have hf_fin :
        ∀ y : Y, (f ⁻¹' {y}).Finite :=
      JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional
        f hf hc
    have hN_total :
        ∀ y : Y,
          (∑ x ∈ (hf_fin y).toFinset,
            JacobianChallenge.Manifold.manifoldRamificationIndex f x : ℕ)
          = JacobianChallenge.ContMDiff.degreeFiber f hf := by
      intro y
      exact h_rsum f hf hc y
    exact Jacobian.pullbackWeighted f hf_fin
      (JacobianChallenge.Manifold.manifoldRamificationIndex f)
      (JacobianChallenge.ContMDiff.degreeFiber f hf)
      hN_total

end Jacobian

end JacobianChallenge
