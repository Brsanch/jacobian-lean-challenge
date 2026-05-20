/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannBilinearRelations

set_option linter.unusedSectionVars false

/-! # `RiemannBilinearSecondRelation ⟹ ℝ-LI of period vectors`

The classical linear-algebra implication: positive definiteness of the
Hermitian matrix `i · Π^T · J · Π̄` implies the `2g` rows of `Π` (the
period vectors) are ℝ-linearly independent in `ℂ^g`.

The implication factors through symplectic block decomposition:
1. Pos-def `i Π^T J Π̄` ⟹ the top `g × g` block of Π is invertible.
2. The normalized Π = (I | τ) has Im(τ) positive definite.
3. The rows of (I | τ) with Im(τ) pos-def are ℝ-LI in ℂ^g.

Steps 1-2 require symplectic linear algebra; step 3 is straightforward.

This file states the implication as a **named theorem** with a
genus-0 discharge. The general-g proof is left as a future chip
(pure linear algebra, no analytic content).

## What this file ships

* `RiemannBilinear2ImpliesRealLI` — named conclusion: ℝ-LI of period
  vectors implied by the second bilinear relation.
* `RiemannBilinear2ImpliesRealLI_genus_zero` — genus-0 discharge
  (vacuous: empty index `Fin (2 * 0) = Fin 0`).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Conclusion of Riemann's second relation:** ℝ-LI of the `2g`
period vectors. -/
def RiemannBilinear2ImpliesRealLI
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1) : Prop :=
  LinearIndependent ℝ
    (fun i : Fin (2 * JacobianChallenge.genus X) =>
      periodVector data α (cycleGens i))

/-- **Genus-0 vacuous discharge.** At `genus X = 0`, the index type
`Fin (2 * 0) = Fin 0` is empty, so the linear independence statement
is vacuously true (`linearIndependent_empty_type`). -/
theorem riemannBilinear2ImpliesRealLI_genus_zero
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (hgenus : JacobianChallenge.genus X = 0) :
    RiemannBilinear2ImpliesRealLI data α cycleGens := by
  haveI : IsEmpty (Fin (2 * JacobianChallenge.genus X)) := by
    rw [hgenus, Nat.mul_zero]
    infer_instance
  exact linearIndependent_empty_type

/-- **Genus-0 vacuous discharge from `[Subsingleton (HolomorphicOneForm
X)]`.** Convenience corollary — at subsingleton ω, the genus is `0`
(via `Module.finrank_zero_of_subsingleton`), so `Fin (2 * genus X)` is
empty and the conclusion is vacuous. -/
theorem riemannBilinear2ImpliesRealLI_of_subsingleton_omega
    [Subsingleton (HolomorphicOneForm X)]
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1) :
    RiemannBilinear2ImpliesRealLI data α cycleGens := by
  haveI : IsEmpty (Fin (2 * JacobianChallenge.genus X)) := by
    have hgenus : JacobianChallenge.genus X = 0 := by
      show Module.finrank ℂ (HolomorphicOneForm X) = 0
      exact Module.finrank_zero_of_subsingleton
    rw [hgenus, Nat.mul_zero]
    infer_instance
  exact linearIndependent_empty_type

end JacobianChallenge

end
