/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicEquivWitnessCardOne
import JacobianChallenge.Manifold.HolomorphicEquivIsConstantMap
import JacobianChallenge.Manifold.RegularValueExistsRegUnconditional

set_option diagnostics.threshold 100

/-! # `degreeFiber e = 1` for any biholomorphism `e` between non-subsingleton compact Riemann surfaces

This file closes the natural identity: any biholomorphism
`e : HolomorphicEquiv X Y` between compact connected Riemann surfaces
with `¬ Subsingleton Y` has fibre-cardinality degree equal to 1.

Composition of two existing pieces:

* zz322's `HolomorphicEquiv.RegularValueWitnessReg_card_eq_one` — any
  `RegularValueWitnessReg e` has cardinality 1.
* `regular_value_exists_reg_holds_unconditional` — non-constant
  analytic maps between compact connected complex 1-manifolds always
  admit such a witness.

Combined with zz320's `subsingleton_target_of_isConstantMap` (giving
`¬ IsConstantMap e` from `¬ Subsingleton Y`), this is the genuine
degree-1 result: biholomorphisms are degree 1.

This is the main analytic step toward "degree-1 holomorphic map ⇒
biholomorphism" — half of one of the classical uniformization
routes via Forster-style Riemann-Roch.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-- **`degreeFiber e = 1` for a biholomorphism on non-subsingleton
spaces.** Composes the unconditional regular-value existence
(`regular_value_exists_reg_holds_unconditional`) with zz322's
witness-card-1 result. -/
theorem HolomorphicEquiv.degreeFiber_eq_one
    [Nonempty X] (hY : ¬ Subsingleton Y)
    (e : HolomorphicEquiv X Y) :
    ContMDiff.degreeFiber (e : X → Y) e.contMDiff_forward = 1 := by
  unfold ContMDiff.degreeFiber
  -- The map `e` is not constant on a non-subsingleton target.
  have hnc : ¬ JacobianChallenge.IsConstantMap (e : X → Y) :=
    e.not_isConstantMap_of_not_subsingleton_target hY
  -- Hence the first branch (`if IsConstantMap`) is `else`.
  rw [if_neg hnc]
  -- Regular witness exists by the unconditional theorem.
  have hwit : Nonempty (ContMDiff.RegularValueWitnessReg (e : X → Y)) :=
    JacobianChallenge.ContMDiff.Owed.degree.regular_value_exists_reg_holds_unconditional
      (e : X → Y) e.contMDiff_forward hnc
  rw [dif_pos hwit]
  -- Any chosen witness has card 1 (zz322).
  exact HolomorphicEquiv.RegularValueWitnessReg_card_eq_one e _

end JacobianChallenge

end
