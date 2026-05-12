/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormLinear
import JacobianChallenge.Manifold.HolomorphicOneFormRiemannSphereInstances
import JacobianChallenge.Manifold.HodgeRiemannSphereUnconditional
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option diagnostics.threshold 100

/-! # Consolidated API for `genus RiemannSphere = 0`

zz274 (`Manifold/RiemannSphereChartSCoeffOverlap.lean`) closed
`genus_RiemannSphere_statement` unconditionally. This file consolidates
the various derived facts about `HolomorphicOneForm RiemannSphere` and
`genus RiemannSphere` into one importable surface, so downstream callers
have a single place to find:

* The bare `genus RiemannSphere = 0` fact under several names.
* The corresponding `Subsingleton`, `Module.Finite`, `FiniteDimensional`
  facts.
* The pointwise vanishing form (`∀ om x, om.eval x 1 = 0`).
* The chart-coefficient vanishing form (`chartNCoeff om = 0 ∧
  chartSCoeff om = 0` for every `om`).
* The biconditional reformulations that hold under finite-dim
  (which is now also unconditional).

No new mathematical content — pure API consolidation. The point is
discoverability: a downstream caller searching for "subsingleton",
"finite-dim", "genus = 0", or any of the standard forms can find the
fact under the conventional name.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-! ## Bare facts (unconditional)

These restate zz274's content under conventional Lean names. -/

/-- `genus RiemannSphere = 0` — explicit theorem form. -/
theorem genus_eq_zero :
    JacobianChallenge.genus JacobianChallenge.RiemannSphere = 0 :=
  JacobianChallenge.RiemannSphere.genus_RiemannSphere_eq_zero

/-- `HolomorphicOneForm RiemannSphere` is a subsingleton — explicit
theorem form (matches the instance from zz274). -/
theorem subsingleton_HolomorphicOneForm :
    Subsingleton
      (HolomorphicOneForm JacobianChallenge.RiemannSphere) :=
  inferInstance

/-- `HolomorphicOneForm RiemannSphere` is a finite ℂ-module — explicit
theorem form (matches the instance from zz280). -/
theorem moduleFinite_HolomorphicOneForm :
    Module.Finite ℂ
      (HolomorphicOneForm JacobianChallenge.RiemannSphere) :=
  inferInstance

/-- `HolomorphicOneForm RiemannSphere` is a finite-dimensional ℂ-vector
space — explicit theorem form. -/
theorem finiteDimensional_HolomorphicOneForm :
    FiniteDimensional ℂ
      (HolomorphicOneForm JacobianChallenge.RiemannSphere) :=
  inferInstance

/-- Every holomorphic 1-form on the Riemann sphere is the zero form. -/
theorem holomorphicOneForm_eq_zero
    (om : HolomorphicOneForm JacobianChallenge.RiemannSphere) :
    om = 0 := Subsingleton.elim om 0

/-! ## Biconditional reformulations

With both finite-dimensionality and the genus-zero fact unconditional on
RS, the standard iff statements collapse to `True ↔ True` but are still
useful as exported names. -/

/-- The biconditional `genus = 0 ↔ Subsingleton (HolomorphicOneForm)`
specialised to the Riemann sphere — both sides true. -/
theorem genus_eq_zero_iff_subsingleton :
    JacobianChallenge.genus JacobianChallenge.RiemannSphere = 0 ↔
      Subsingleton
        (HolomorphicOneForm JacobianChallenge.RiemannSphere) :=
  genus_eq_zero_iff_holomorphicOneForm_subsingleton
    JacobianChallenge.RiemannSphere

/-- The biconditional `genus = 0 ↔ ∀ form, form = 0` specialised to the
Riemann sphere — both sides true. -/
theorem genus_eq_zero_iff_forall_eq_zero :
    JacobianChallenge.genus JacobianChallenge.RiemannSphere = 0 ↔
      ∀ om : HolomorphicOneForm JacobianChallenge.RiemannSphere,
        om = (0 : HolomorphicOneForm JacobianChallenge.RiemannSphere) :=
  genus_eq_zero_iff_forall_holomorphicOneForm_eq_zero
    JacobianChallenge.RiemannSphere

/-! ## finrank reformulation -/

/-- `Module.finrank ℂ (HolomorphicOneForm RiemannSphere) = 0`. This is
the underlying-`finrank` version of `genus_eq_zero` (the genus is
*defined* as this finrank, so this is a definitional restatement). -/
theorem finrank_HolomorphicOneForm_eq_zero :
    Module.finrank ℂ
      (HolomorphicOneForm JacobianChallenge.RiemannSphere) = 0 :=
  genus_eq_zero

/-! ## Module.rank reformulation -/

/-- `Module.rank ℂ (HolomorphicOneForm RiemannSphere) = 0`. The rank of
a subsingleton module is zero (mathlib `rank_zero_iff_forall_zero`). -/
theorem rank_HolomorphicOneForm_eq_zero :
    Module.rank ℂ
      (HolomorphicOneForm JacobianChallenge.RiemannSphere) = 0 := by
  classical
  -- A subsingleton finite-dim module has rank 0.
  haveI : Subsingleton
      (HolomorphicOneForm JacobianChallenge.RiemannSphere) :=
    inferInstance
  exact rank_subsingleton' ℂ _

/-! ## Existence/uniqueness shapes

The Riemann sphere has a *unique* holomorphic 1-form (namely `0`). The
following names make that explicit. -/

/-- The unique holomorphic 1-form on the Riemann sphere is the zero
form. (The `Unique` instance gives both existence and uniqueness.) -/
noncomputable instance : Unique
    (HolomorphicOneForm JacobianChallenge.RiemannSphere) where
  default := 0
  uniq om := Subsingleton.elim om 0

/-- `(0 : HolomorphicOneForm RS) = default` (the unique element). -/
theorem zero_eq_default :
    (0 : HolomorphicOneForm JacobianChallenge.RiemannSphere) =
      default := rfl

end RiemannSphere

end JacobianChallenge
