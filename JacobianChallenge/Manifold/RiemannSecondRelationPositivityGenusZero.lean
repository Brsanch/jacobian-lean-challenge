/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSecondRelationPositivityNamed
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option linter.unusedSectionVars false

/-! # `RiemannSecondRelationPositivity` UNCONDITIONAL at genus 0

At `JacobianChallenge.genus X = 0`, the input space
`Fin (genus X) → ℂ = Fin 0 → ℂ` is a subsingleton: there is only one
function (the zero function). The hypothesis `x ≠ 0` is then false,
and `RiemannSecondRelationPositivity` is vacuously satisfied.

Parallel to chip 11 for `RiemannFirstBilinearRelation`. Plus
unconditional RS instance via `RiemannSphere.genus_RiemannSphere_eq_zero`.

## What this file ships

* `riemannSecondRelationPositivity_of_genus_zero` — discharge from
  `genus X = 0`.
* `riemannSecondRelationPositivity_RiemannSphere` — unconditional RS
  instance.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`RiemannSecondRelationPositivity` UNCONDITIONAL at `genus X = 0`.**

At genus 0, every `x : Fin (genus X) → ℂ` equals `0` (subsingleton on
`Fin 0 → ℂ`), so the hypothesis `x ≠ 0` is false and the implication
holds vacuously. -/
theorem riemannSecondRelationPositivity_of_genus_zero
    (h_genus : JacobianChallenge.genus X = 0)
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1) :
    RiemannSecondRelationPositivity data basis_ω cycleGens := by
  haveI hEmpty : IsEmpty (Fin (JacobianChallenge.genus X)) := by
    rw [h_genus]; infer_instance
  intro x hx
  -- x : Fin (genus X) → ℂ with hEmpty means x is the unique 0 function.
  -- The hypothesis x ≠ 0 then yields False.
  exfalso
  apply hx
  funext i
  exact isEmptyElim i

/-- **Unconditional RS instance.** -/
theorem riemannSecondRelationPositivity_RiemannSphere
    (data : PeriodPairingData RiemannSphere)
    (basis_ω : Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
      (HolomorphicOneForm RiemannSphere))
    (cycleGens : Fin (2 * JacobianChallenge.genus RiemannSphere) → data.H1) :
    RiemannSecondRelationPositivity data basis_ω cycleGens :=
  riemannSecondRelationPositivity_of_genus_zero
    RiemannSphere.genus_RiemannSphere_eq_zero data basis_ω cycleGens

end JacobianChallenge

end
