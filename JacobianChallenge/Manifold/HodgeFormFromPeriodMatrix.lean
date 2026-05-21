/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HodgeFormFromMatrix
import JacobianChallenge.Manifold.PeriodMatrixAntiHermitian
import JacobianChallenge.Manifold.HodgeRiemannBridge

set_option linter.unusedSectionVars false

/-! # Canonical Hodge form from anti-symmetric `J` — bridge identity automatic

For any anti-symmetric integer matrix `J : Matrix (Fin (2*g)) (Fin (2*g)) ℤ`
(`Jᵀ = -J`) on a compact connected complex 1-manifold `X` with chosen
basis `basis_ω` and cycle data `cycleGens`, we define the **canonical
Hodge form**

  `canonicalHodgeFormFromAntiSymm data basis_ω cycleGens hJ`

to be `hodgeFormFromMatrix basis_ω (i • periodMatrixForm pm J) _` where
`pm := periodMatrix data basis_ω cycleGens`. The Hermitian-ness of
`i • Πᵀ J Π̄` is automatic from `iPeriodMatrixForm_isHermitian`.

With this canonical choice, the `HodgeRiemannBridgeHypothesis` identity
`i Πᵀ J Π̄ = H.toMatrix basis_ω` is **definitional** via
`hodgeFormFromMatrix_toMatrix`. Hence the bridge atom in
`CompleteHodgeRiemannHypothesis` is **free** for any anti-symmetric `J`.

## What this file ships

* `canonicalHodgeFormFromAntiSymm` — the canonical Hodge form.
* `canonicalHodgeFormFromAntiSymm_bridgeIdentity` — the bridge identity
  holds automatically for the canonical form.

The remaining classical content of `CompleteHodgeRiemannHypothesis`
reduces to: (anti-symmetric `J`) + (first relation) + (PD of
`i • periodMatrixForm pm J`).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Matrix

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **The canonical Hodge form from anti-symmetric `J`.** Defined as the
realisation of the period-matrix bilinear form via
`hodgeFormFromMatrix`. -/
noncomputable def canonicalHodgeFormFromAntiSymm
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    (hJ : Jᵀ = -J) :
    HermitianOnHolomorphicOneForm X :=
  hodgeFormFromMatrix basis_ω
    ((Complex.I : ℂ) • periodMatrixForm (periodMatrix data basis_ω cycleGens) J)
    (iPeriodMatrixForm_isHermitian _ J hJ)

/-- **Bridge identity is automatic for the canonical Hodge form.** The
identity `i • Πᵀ J Π̄ = H.toMatrix basis_ω` holds by construction. -/
theorem canonicalHodgeFormFromAntiSymm_bridgeIdentity
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    (hJ : Jᵀ = -J) :
    HodgeRiemannBridgeHypothesis data basis_ω cycleGens J
      (canonicalHodgeFormFromAntiSymm data basis_ω cycleGens hJ) := by
  unfold HodgeRiemannBridgeHypothesis canonicalHodgeFormFromAntiSymm
  rw [hodgeFormFromMatrix_toMatrix]
  rfl

end JacobianChallenge

end
