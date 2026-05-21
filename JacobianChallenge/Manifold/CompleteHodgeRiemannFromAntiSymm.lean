/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HodgeFormFromPeriodMatrixPD
import JacobianChallenge.Manifold.BilinearFromHodgeChain

set_option linter.unusedSectionVars false

/-! # `CompleteHodgeRiemannHypothesis` from (anti-sym J + first + matrix PD) (chip 19e)

The chip-19 chain (19a–d) shows that for any anti-symmetric integer
matrix `J`, the **canonical Hodge form**
`canonicalHodgeFormFromAntiSymm` makes both the bridge identity and the
Hermitian conjunct of `RiemannBilinearSecondRelation` automatic. The
remaining content is:

* the **first relation** `Πᵀ · J.map ↑ · Π = 0`, and
* the **positivity conjunct** of the second relation
  `(star x ⬝ᵥ (i • periodMatrixForm pm J *ᵥ x))` is a positive real
  for `x ≠ 0`.

This file bundles those into a single existence theorem for
`CompleteHodgeRiemannHypothesis`. Specifically, `CompleteHodgeRiemannHypothesis`
reduces to **(anti-sym J + first relation + matrix PD)** with no
mention of any Hodge form.

## What this file ships

* `completeHodgeRiemannHypothesis_of_antiSymm_first_matrixPos` —
  composes chips 19a (Hermitian), 19c (bridge identity automatic),
  and 19d (PD from matrix positivity) into a single discharge of
  `CompleteHodgeRiemannHypothesis` from three named inputs.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Matrix

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`CompleteHodgeRiemannHypothesis` from (anti-sym J + first relation
+ matrix positivity).** Given anti-symmetric `J`, the first relation
`Πᵀ · J · Π = 0`, and positivity of `i • periodMatrixForm pm J` on
non-zero vectors, the full Hodge–Riemann bundle holds with the
canonical Hodge form. -/
theorem completeHodgeRiemannHypothesis_of_antiSymm_first_matrixPos
    {data : PeriodPairingData X}
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    {cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1}
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    (hJ : Jᵀ = -J)
    (hFirst : RiemannBilinearFirstRelation data basis_ω cycleGens J)
    (hPos : ∀ x : Fin (JacobianChallenge.genus X) → ℂ, x ≠ 0 →
        (star x ⬝ᵥ
            (((Complex.I : ℂ) •
                periodMatrixForm (periodMatrix data basis_ω cycleGens) J)
              *ᵥ x)).im = 0 ∧
          0 < (star x ⬝ᵥ
            (((Complex.I : ℂ) •
                periodMatrixForm (periodMatrix data basis_ω cycleGens) J)
              *ᵥ x)).re) :
    CompleteHodgeRiemannHypothesis data basis_ω cycleGens := by
  refine ⟨J, canonicalHodgeFormFromAntiSymm data basis_ω cycleGens hJ,
    isPositiveDefinite_canonicalHodgeFormFromAntiSymm hJ hPos,
    hFirst,
    canonicalHodgeFormFromAntiSymm_bridgeIdentity data basis_ω cycleGens hJ⟩

end JacobianChallenge

end
