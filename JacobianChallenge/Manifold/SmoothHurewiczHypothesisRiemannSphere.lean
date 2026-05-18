/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothHurewiczHypothesis
import JacobianChallenge.Manifold.BasedLoopHomologyFromBasedLoopsBound
import JacobianChallenge.Manifold.RiemannSphereGenus

set_option linter.unusedSectionVars false

/-! # `SmoothHurewiczHypothesis` on `RiemannSphere`, unconditional

At genus 0 (`X = RiemannSphere`), the symplectic basis tuple has
length `2 * 0 = 0`, so the data of a `SmoothSymplecticBasis 𝓘(ℝ, ℂ) RS
p₀ 0` is **vacuous** (the `Fin 0` basis-loop tuple is `Fin.elim0`).
The `SmoothHurewiczHypothesis` then collapses to: every based loop's
`single` lies in `stokesBoundaries` — exactly
`BasedSmoothLoopsBoundHypothesis`, which is unconditional on `RS` via
`basedSmoothLoopsBoundHypothesis_RS_holds`.

This file ships:

* `emptySymplecticBasis_RiemannSphere p₀` — the canonical empty
  symplectic basis on `RS` at genus 0.
* `smoothHurewiczHypothesis_RiemannSphere_holds p₀` — unconditional
  discharge of `SmoothHurewiczHypothesis emptySymplecticBasis`.

Together, these validate that the smooth-Hurewicz framework correctly
reproduces the genus-0 closure on `RS` end-to-end.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

namespace RiemannSphere

/-- **The canonical empty symplectic basis on `RiemannSphere` at
genus 0.** `Fin (2 * 0) = Fin 0`, so the basis tuple is `Fin.elim0`.
The endpoint hypotheses are discharged vacuously. -/
noncomputable def emptySymplecticBasis (p₀ : RiemannSphere) :
    SmoothSymplecticBasis 𝓘(ℝ, ℂ) RiemannSphere p₀ 0 where
  basis := by
    -- `Fin (2 * 0) = Fin 0`; `Fin.elim0` discharges via `IsEmpty`.
    intro i
    exact i.elim0
  basis_src := by
    intro i
    exact i.elim0
  basis_tgt := by
    intro i
    exact i.elim0

@[simp] lemma emptySymplecticBasis_cycleGens
    (p₀ : RiemannSphere) (i : Fin (2 * 0)) :
    (emptySymplecticBasis p₀).cycleGens i = i.elim0 := i.elim0

/-- **`SmoothHurewiczHypothesis` on `RiemannSphere` for the empty basis
at genus 0.** Reduces to `BasedSmoothLoopsBoundHypothesis`, which is
unconditional on `RS` via `basedSmoothLoopsBoundHypothesis_RS_holds`. -/
theorem smoothHurewiczHypothesis_RiemannSphere_holds (p₀ : RiemannSphere) :
    SmoothHurewiczHypothesis (emptySymplecticBasis p₀) := by
  intro γ h_src h_tgt
  -- The empty `Fin (2 * 0)` makes both the ℤ-tuple and the sum vacuous.
  refine ⟨Fin.elim0, ?_⟩
  -- `∑ i : Fin (2 * 0), (Fin.elim0 i) • cycleGens i = 0`.
  have h_sum_zero :
      (∑ i : Fin (2 * 0),
        (Fin.elim0 i : ℤ) • (emptySymplecticBasis p₀).cycleGens i)
        = (0 : SmoothCycle 𝓘(ℝ, ℂ) RiemannSphere) := by
    -- The Finset over `Fin (2*0)` is empty.
    haveI : IsEmpty (Fin (2 * 0)) := by
      rw [Nat.mul_zero]; infer_instance
    exact Finset.sum_of_isEmpty _
  rw [h_sum_zero, sub_zero]
  exact basedSmoothLoopsBoundHypothesis_RS_holds p₀ γ h_src h_tgt

end RiemannSphere

end JacobianChallenge

end
