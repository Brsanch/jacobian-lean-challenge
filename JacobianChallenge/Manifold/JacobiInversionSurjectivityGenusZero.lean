/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3FullInputSymp
import JacobianChallenge.Manifold.CanonicalAnalyticJacobianSubsingleton

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-! # Phase F (Jacobi inversion) surjectivity UNCONDITIONAL at genus 0

At `Subsingleton (HolomorphicOneForm X)` (= genus 0), the target
`AnalyticJacobianSymp` is subsingleton (period-lattice quotient of
`Fin 0 → ℂ`). So **every** `Pic⁰ X →+ AnalyticJacobianSymp` is
surjective: the only target is `0`, which is the image of `0`.

The injectivity half of Jacobi inversion is the genuine open content
(Abel's converse / `Subsingleton (Pic0 X)` ↔ RR genus 0). Surjectivity
at genus 0 is automatic.

## What ships

* `jacobiInversion_surjective_of_subsingleton_omega` — surjectivity
  half of Jacobi inversion at genus 0, unconditionally.

For Pic0 X subsingleton (= injectivity), see the existing in-tree
`Pic0SubsingletonBridge` infrastructure.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace AbelJacobiInputSymp

/-- **Surjectivity of `B.abelJacobi hAbel` at genus 0**, unconditional. -/
theorem abelJacobi_surjective_of_subsingleton_omega
    [Subsingleton (HolomorphicOneForm X)]
    {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
    {h : PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) α}
    (B : AbelJacobiInputSymp α h) (hAbel : AbelHypothesis B) :
    Function.Surjective (B.abelJacobi hAbel) := by
  -- AnalyticJacobianSymp is subsingleton at genus 0.
  haveI : Subsingleton (Fin (JacobianChallenge.genus X) → ℂ) := by
    have : JacobianChallenge.genus X = 0 := Module.finrank_zero_of_subsingleton
    rw [this]; exact Pi.uniqueOfIsEmpty _ |>.instSubsingleton
  haveI : Subsingleton (AnalyticJacobianSymp
      (PeriodPairingData.ofSmoothCycle X) α h) :=
    subsingleton_jacobianOfLattice_of_subsingleton_ambient _
  intro y
  exact ⟨0, Subsingleton.elim _ _⟩

end AbelJacobiInputSymp

end JacobianChallenge

end
