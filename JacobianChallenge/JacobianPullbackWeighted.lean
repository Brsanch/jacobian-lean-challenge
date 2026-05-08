/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Jacobian
import JacobianChallenge.Divisor.FiberPullbackWeighted

/-! # `Jacobian`-side weighted pullback (ZZ179f)

Topological-hom version of `Pic0.pullbackWeighted`. With the current
discrete topology on `Jacobian X = Pic0 X` (placeholder until the
analytic-torus topology lands), every `Pic0 Y →+ Pic0 X` is
automatically continuous and lifts to `Jacobian Y →ₜ+ Jacobian X`.

This mirrors `Jacobian.pushforward` (`Jacobian.lean` line 608) which
is built the same way from `Pic0.pushforward`.

When `ramificationSumEqualsDegree_statement` is discharged
(`Manifold/RamificationSumEqualsDegree.lean`), this composer plugs
into `Basic.lean.Jacobian.pullback`'s body to swap out the zero stub.

No `sorry`, no `axiom`. -/

namespace JacobianChallenge

namespace Jacobian

variable {X Y : Type*}
variable [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
variable [DecidableEq X]

/-- The **weighted pullback** `Jacobian Y →ₜ+ Jacobian X` from
`Pic0.pullbackWeighted`. Continuity is automatic because `Jacobian X`
carries the discrete topology at this pin. -/
noncomputable def pullbackWeighted
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) (e : X → ℕ) (N : ℕ)
    (hN_total : ∀ y, (∑ x ∈ (hf y).toFinset, e x) = N) :
    Jacobian Y →ₜ+ Jacobian X where
  toAddMonoidHom := Pic0.pullbackWeighted f hf e N hN_total
  continuous_toFun := continuous_of_discreteTopology

end Jacobian

end JacobianChallenge
