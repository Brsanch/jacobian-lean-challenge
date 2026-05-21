/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodSigmaRealLI
import JacobianChallenge.Manifold.HodgeRiemannBridgeComposition

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # End-to-end `bilinear` discharge from the Hodge–Riemann chain (chip 3)

This file ships the named-hypothesis bundle that discharges the
`bilinear` field of `SmoothHomologyDataPackage` from concrete classical
inputs. The chain:

  (Hodge inner product PD)  +  (Hodge bridge identity)
       +  (Riemann first relation)
  ⟹  RiemannBilinearRelations          [chip 1]
  ⟹  ℝ-LI of period vectors            [chip 2C]
  =   the `bilinear` field of `SmoothHomologyDataPackage`.

The user-facing theorem `realLI_periodVector_of_completeHodgeRiemann`
takes a single bundled `CompleteHodgeRiemannHypothesis` (existence of
`J`, `H`, with the three conditions) and concludes ℝ-LI of period
vectors. The genus-0 discharge `completeHodgeRiemannHypothesis_of_subsingleton`
covers the trivial case via the empty bilinear form.

## What this file ships

* `CompleteHodgeRiemannHypothesis` — bundle of `(J, H, PD, first, bridge)`.
* `realLI_periodVector_of_completeHodgeRiemann` — the chip 3 theorem.
* `completeHodgeRiemannHypothesis_of_subsingleton` — genus-0 vacuous discharge.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Bundled classical hypotheses for the Hodge–Riemann chain.** Asserts
the existence of:

* `J` — an integer skew-symmetric `2g × 2g` matrix (the symplectic
  intersection form on the chosen `cycleGens`);
* `H` — a positive-definite Hermitian form on `H⁰(X, Ω)` (Hodge inner
  product);

with the conditions:

* `H.IsPositiveDefinite`;
* `RiemannBilinearFirstRelation data basis_ω cycleGens J` (i.e.,
  `Πᵀ · J · Π = 0`);
* `HodgeRiemannBridgeHypothesis data basis_ω cycleGens J H` (i.e.,
  `i · Πᵀ · J · Π̄ = H.toMatrix basis_ω`).

This is the *minimal classical content* required to discharge the
`bilinear` field of `SmoothHomologyDataPackage`. -/
def CompleteHodgeRiemannHypothesis
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1) : Prop :=
  ∃ (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ)
    (H : HermitianOnHolomorphicOneForm X),
    H.IsPositiveDefinite ∧
    RiemannBilinearFirstRelation data basis_ω cycleGens J ∧
    HodgeRiemannBridgeHypothesis data basis_ω cycleGens J H

/-- **Chip 3 main theorem: ℝ-LI of period vectors from
`CompleteHodgeRiemannHypothesis`.** Composes chips 1, 2A, 2B, 2C into a
single discharge of the `bilinear` field of `SmoothHomologyDataPackage`
from the bundled classical hypotheses. -/
theorem realLI_periodVector_of_completeHodgeRiemann
    {data : PeriodPairingData X}
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    {cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1}
    (h : CompleteHodgeRiemannHypothesis data basis_ω cycleGens) :
    LinearIndependent ℝ
      (fun i : Fin (2 * JacobianChallenge.genus X) =>
        periodVector data basis_ω (cycleGens i)) := by
  obtain ⟨J, H, hPD, hFirst, hBridge⟩ := h
  -- Compose: chip 1 (bridge ⟹ second relation) + chip 2C (relations ⟹ LI).
  have h_rel : RiemannBilinearRelations data basis_ω cycleGens :=
    RiemannBilinearRelations_of_HodgeBridge_and_first hPD hBridge hFirst
  exact RiemannBilinear2ImpliesRealLI_of_relations h_rel

/-! ## Genus-0 vacuous discharge -/

/-- **`CompleteHodgeRiemannHypothesis` holds vacuously at genus 0** under
`[Subsingleton (HolomorphicOneForm X)]`. The Hodge form is the zero
form (vacuously positive-definite on the singleton 0-form space), the
first relation is the zero-matrix identity (vacuous on `Fin g = Fin 0`),
and the bridge identity is the zero-matrix identity. -/
theorem completeHodgeRiemannHypothesis_of_subsingleton
    [Subsingleton (HolomorphicOneForm X)]
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1) :
    CompleteHodgeRiemannHypothesis data basis_ω cycleGens := by
  -- Use the zero matrix for J and the zero Hodge form.
  refine ⟨0, ?_, ?_, ?_, ?_⟩
  · -- The constant-zero Hodge form on the subsingleton ω space.
    exact {
      toFun := fun _ _ => 0
      map_zero_left := fun _ => rfl
      map_add_left := fun _ _ _ => by simp
      map_smul_left := fun _ _ _ => by simp
      conjSymm := fun _ _ => by simp
    }
  · -- Positive definite: vacuous on subsingleton (every value is 0).
    refine ⟨fun _ => ?_, fun om _ => ?_⟩
    · refine ⟨?_, ?_⟩ <;> simp
    · exact Subsingleton.elim om 0
  · -- First relation: 0 matrix.
    unfold RiemannBilinearFirstRelation
    simp [Matrix.map_zero]
  · -- Bridge identity: both sides are zero matrices (genus 0 ⟹ Fin g empty).
    unfold HodgeRiemannBridgeHypothesis
    -- LHS: i • (Πᵀ * J.map _ * Π̄). With J = 0, this is i • (Πᵀ * 0 * Π̄) = i • 0 = 0.
    -- RHS: HermitianOnHolomorphicOneForm.toMatrix basis_ω, which is fun i j => 0 = 0.
    ext i j
    simp [Matrix.map_zero, HermitianOnHolomorphicOneForm.toMatrix]

end JacobianChallenge

end
