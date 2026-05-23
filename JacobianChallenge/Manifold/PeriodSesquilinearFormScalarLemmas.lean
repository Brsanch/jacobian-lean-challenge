/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodSesquilinearFormProperties

set_option linter.unusedSectionVars false

/-! # Scalar lemmas for `periodSesquilinearForm`

Routine corollaries of sesquilinearity:

* `smul_smul` — `Q_sq (c • ω₀) (d • ω₁) = c · star d · Q_sq ω₀ ω₁`.
* `neg_left` — `Q_sq (-ω₀) ω₁ = - Q_sq ω₀ ω₁`.
* `neg_right` — `Q_sq ω₀ (-ω₁) = - Q_sq ω₀ ω₁`.
* `sub_left` — bilinear sub.
* `sub_right` — bilinear sub.

No `sorry`, no `axiom`. -/

noncomputable section

open Matrix Complex

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

namespace periodSesquilinearForm

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]
  {data : PeriodPairingData X}
  (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
  (J : Matrix (Fin (2 * JacobianChallenge.genus X))
        (Fin (2 * JacobianChallenge.genus X)) ℤ)

/-- **Scaling on both sides.** -/
theorem smul_smul (c d : ℂ) (om₀ om₁ : HolomorphicOneForm X) :
    periodSesquilinearForm cycleGens J (c • om₀) (d • om₁)
      = c * star d * periodSesquilinearForm cycleGens J om₀ om₁ := by
  rw [smul_left, smul_right]; ring

/-- **Negation on the left argument.** -/
theorem neg_left (om₀ om₁ : HolomorphicOneForm X) :
    periodSesquilinearForm cycleGens J (-om₀) om₁
      = - periodSesquilinearForm cycleGens J om₀ om₁ := by
  rw [show (-om₀ : HolomorphicOneForm X) = (-1 : ℂ) • om₀ from by
        rw [neg_smul, one_smul], smul_left]; ring

/-- **Negation on the right argument.** -/
theorem neg_right (om₀ om₁ : HolomorphicOneForm X) :
    periodSesquilinearForm cycleGens J om₀ (-om₁)
      = - periodSesquilinearForm cycleGens J om₀ om₁ := by
  rw [show (-om₁ : HolomorphicOneForm X) = (-1 : ℂ) • om₁ from by
        rw [neg_smul, one_smul], smul_right]; simp

/-- **Subtraction on the left.** -/
theorem sub_left (om₀ om₀' om₁ : HolomorphicOneForm X) :
    periodSesquilinearForm cycleGens J (om₀ - om₀') om₁
      = periodSesquilinearForm cycleGens J om₀ om₁
        - periodSesquilinearForm cycleGens J om₀' om₁ := by
  rw [sub_eq_add_neg, add_left, neg_left, sub_eq_add_neg]

/-- **Subtraction on the right.** -/
theorem sub_right (om₀ om₁ om₁' : HolomorphicOneForm X) :
    periodSesquilinearForm cycleGens J om₀ (om₁ - om₁')
      = periodSesquilinearForm cycleGens J om₀ om₁
        - periodSesquilinearForm cycleGens J om₀ om₁' := by
  rw [sub_eq_add_neg, add_right, neg_right, sub_eq_add_neg]

end periodSesquilinearForm

end JacobianChallenge

end
