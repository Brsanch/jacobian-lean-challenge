/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannFirstBilinearRelationNamed
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option linter.unusedSectionVars false

/-! # `RiemannFirstBilinearRelation` UNCONDITIONAL at genus 0

At `JacobianChallenge.genus X = 0`, the cycle-generator family
`cycleGens : Fin (2 * genus X) → data.H1 = Fin 0 → data.H1` is empty,
so the bilinear sum `Q J cycleGens ω₀ ω₁ = ∑ k l, ...` is empty and
identically `0`. The named hypothesis `RiemannFirstBilinearRelation`
(chip 9) is therefore vacuously discharged.

Validates that the chip 9 named-hypothesis setup composes correctly
with the genus-0 case, and provides an unconditional `RiemannSphere`
smoke test (`genus RiemannSphere = 0` in tree).

## What this file ships

* `riemannFirstBilinearRelation_of_genus_zero` — discharge from
  `genus X = 0`.
* `riemannFirstBilinearRelation_RiemannSphere` — unconditional
  RS instance via `genus_RiemannSphere_eq_zero`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`RiemannFirstBilinearRelation` UNCONDITIONAL at `genus X = 0`.**

The bilinear sum `Q J cycleGens ω₀ ω₁` ranges over `Fin (2 * 0) = Fin
0`, so every term is empty: the sum is identically `0`. -/
theorem riemannFirstBilinearRelation_of_genus_zero
    (h_genus : JacobianChallenge.genus X = 0)
    {data : PeriodPairingData X}
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ) :
    RiemannFirstBilinearRelation cycleGens J := by
  haveI hEmpty : IsEmpty (Fin (2 * JacobianChallenge.genus X)) := by
    rw [h_genus, Nat.mul_zero]; infer_instance
  intro ω₀ ω₁
  unfold riemannBilinearPeriodForm
  exact Finset.sum_of_isEmpty _

/-- **Unconditional `RiemannFirstBilinearRelation` on `RiemannSphere`.**

Composes `riemannFirstBilinearRelation_of_genus_zero` with
`genus_RiemannSphere_eq_zero`. -/
theorem riemannFirstBilinearRelation_RiemannSphere
    {data : PeriodPairingData RiemannSphere}
    (cycleGens : Fin (2 * JacobianChallenge.genus RiemannSphere) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus RiemannSphere))
          (Fin (2 * JacobianChallenge.genus RiemannSphere)) ℤ) :
    RiemannFirstBilinearRelation cycleGens J :=
  riemannFirstBilinearRelation_of_genus_zero
    RiemannSphere.genus_RiemannSphere_eq_zero cycleGens J

end JacobianChallenge

end
