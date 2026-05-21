/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CompleteHodgeRiemannViaStandardForm

set_option linter.unusedSectionVars false

/-! # `CompleteHodgeRiemannHypothesisViaStandardForm` at genus 0 (chip 12)

Under `[Subsingleton (HolomorphicOneForm X)]`, `genus X = 0`, so the
period matrix `pmat : Matrix (Fin (2 * 0)) (Fin 0) ℂ` has empty row
and column index. The first relation `pmatᵀ * J * pmat = 0` and bridge
identity reduce to `(0 = 0 : Matrix (Fin 0) (Fin 0) ℂ)` after picking
any `J` (say the zero matrix). Hence
`CompleteHodgeRiemannHypothesisViaStandardForm` holds vacuously.

This complements chip 9's `instHasJacobianHodgeChain_of_subsingleton_and_HasBSLB`
on the Hodge side: at genus 0, the bridge atom is also free.

## What this file ships

* `completeHodgeRiemannHypothesisViaStandardForm_of_subsingleton` —
  unconditional discharge of the simplified form at genus 0.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Genus-0 vacuous discharge.** Under `[Subsingleton ω]`,
`CompleteHodgeRiemannHypothesisViaStandardForm` holds vacuously: pick
`J = 0` and observe that `Fin (genus X)`-indexed matrices are all `0`. -/
theorem completeHodgeRiemannHypothesisViaStandardForm_of_subsingleton
    [Subsingleton (HolomorphicOneForm X)]
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1) :
    CompleteHodgeRiemannHypothesisViaStandardForm data basis_ω cycleGens := by
  -- All matrices on Fin (genus X) are Subsingleton at genus 0 (IsEmpty).
  have hgenus : JacobianChallenge.genus X = 0 :=
    Module.finrank_zero_of_subsingleton
  haveI : IsEmpty (Fin (JacobianChallenge.genus X)) := by
    rw [hgenus]; infer_instance
  -- A `Matrix (Fin 0) (Fin 0) ℂ` has empty index, so all such matrices are equal.
  haveI : Subsingleton (Matrix (Fin (JacobianChallenge.genus X))
      (Fin (JacobianChallenge.genus X)) ℂ) := by
    apply Pi.instSubsingleton
  refine ⟨0, ?_, ?_⟩
  · -- First relation: 0 = 0 by Subsingleton on Fin (genus X)-indexed matrices.
    unfold RiemannBilinearFirstRelation
    apply Subsingleton.elim
  · -- Bridge identity: both sides Fin (genus X) × Fin (genus X) — Subsingleton.
    unfold HodgeRiemannBridgeHypothesis
    apply Subsingleton.elim

end JacobianChallenge

end
