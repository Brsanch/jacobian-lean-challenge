/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HodgeRiemannBridge

set_option linter.unusedSectionVars false

/-! # Bridge identity from `Subsingleton (HolomorphicOneForm X)`

When `HolomorphicOneForm X` is a subsingleton (equivalently `genus X
= 0`), every Hermitian form `H` is vacuously the constant-zero form,
and both sides of the bridge identity are `0 × 0` matrices. So the
bridge identity holds vacuously.

This is the most general unconditional discharge of the bridge
identity. Generalises `hodgeRiemannBridgeHypothesis_of_genus_zero`
(which needs `h_genus : genus X = 0`) to taking `[Subsingleton ω]`
directly.

## What ships

* `hodgeRiemannBridgeHypothesis_of_subsingleton_omega` — bridge from
  `Subsingleton ω` (vacuous).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Bridge identity from `[Subsingleton (HolomorphicOneForm X)]`.**

Under subsingleton holomorphic 1-forms, `genus X = 0`, so both sides
of the bridge are matrices over the empty `Fin 0` and vacuously
equal. -/
theorem hodgeRiemannBridgeHypothesis_of_subsingleton_omega
    [Subsingleton (HolomorphicOneForm X)]
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ)
    (H : HermitianOnHolomorphicOneForm X) :
    HodgeRiemannBridgeHypothesis data basis_ω cycleGens J H := by
  have h_genus : JacobianChallenge.genus X = 0 :=
    Module.finrank_zero_of_subsingleton
  unfold HodgeRiemannBridgeHypothesis
  haveI : IsEmpty (Fin (JacobianChallenge.genus X)) := by
    rw [h_genus]; exact Fin.isEmpty
  ext i j
  exact isEmptyElim i

end JacobianChallenge

end
