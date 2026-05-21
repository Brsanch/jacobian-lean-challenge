/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CompleteHodgeRiemannGenusZero
import JacobianChallenge.Manifold.BilinearFromHodgeChain

set_option linter.unusedSectionVars false

/-! # ℝ-LI of period vectors UNCONDITIONAL at genus 0 (chip 20c)

For any compact connected complex 1-manifold `X` with
`JacobianChallenge.genus X = 0`, the period-vector family

  `fun i : Fin (2 * genus X) => periodVector data basis_ω (cycleGens i)`

is `LinearIndependent ℝ` *unconditionally* — the index type
`Fin (2 * 0) = Fin 0` is empty, so the family is trivially ℝ-LI by
`linearIndependent_empty_type`.

This is the SmoothHomologyDataPackage `bilinear` field at genus 0.
The chip composes the route via `realLI_periodVector_of_completeHodgeRiemann`
(applied to chip 20a) for a self-consistent derivation, plus a
direct empty-index proof.

## What this file ships

* `realLI_periodVector_of_genus_eq_zero` — direct empty-index proof.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **ℝ-LI of period vectors UNCONDITIONAL at `genus X = 0`** (direct
empty-index proof). -/
theorem realLI_periodVector_of_genus_eq_zero
    (h_genus : JacobianChallenge.genus X = 0)
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1) :
    LinearIndependent ℝ
      (fun i : Fin (2 * JacobianChallenge.genus X) =>
        periodVector data basis_ω (cycleGens i)) := by
  haveI : IsEmpty (Fin (2 * JacobianChallenge.genus X)) := by
    rw [h_genus, Nat.mul_zero]; infer_instance
  exact linearIndependent_empty_type

/-- **Alternative derivation via chip 20a.** Composes
`completeHodgeRiemannHypothesis_of_genus_eq_zero` with
`realLI_periodVector_of_completeHodgeRiemann` for an end-to-end
check that the chip 19 chain is consistent at genus 0. -/
theorem realLI_periodVector_of_genus_eq_zero_via_chrh
    (h_genus : JacobianChallenge.genus X = 0)
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1) :
    LinearIndependent ℝ
      (fun i : Fin (2 * JacobianChallenge.genus X) =>
        periodVector data basis_ω (cycleGens i)) :=
  realLI_periodVector_of_completeHodgeRiemann
    (completeHodgeRiemannHypothesis_of_genus_eq_zero h_genus
      data basis_ω cycleGens)

end JacobianChallenge

end
