/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasPic0AnalyticEquivFromPhases

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-! # Phase G refactor: HasPic0AnalyticEquiv from E + F + SHDP

Modular variant of `hasPic0AnalyticEquiv_of_phases_DEFG` that takes
`[HasSmoothHomologyDataPackage basis_ω]` as a typeclass input rather
than constructing it from Phase D's Morse hypotheses. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- Phase G modulo SHDP. -/
theorem hasPic0AnalyticEquiv_of_phases_EF
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    [HasSmoothHomologyDataPackage (X := X) basis_ω]
    (h_abel : AbelGeneralXHypothesis X)
    (h_jacobi_inv : JacobiInversionGeneralXHypothesis X) :
    HasPic0AnalyticEquiv X := by
  let h_symp : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle X) basis_ω :=
    canonicalPeriodLatticeSymplecticBundle (X := X) basis_ω
  have hB_nonempty :
      Nonempty (AbelJacobiInputSymp (X := X) (α := basis_ω) (h := h_symp)) :=
    AbelJacobiInputSymp.nonempty_of_connected basis_ω h_symp
  let B : AbelJacobiInputSymp (X := X) (α := basis_ω) (h := h_symp) :=
    Classical.choice hB_nonempty
  have hAbel : AbelJacobiInputSymp.AbelHypothesis B :=
    h_abel basis_ω h_symp B
  have hJI : AbelJacobiInputSymp.JacobiInversion B hAbel :=
    h_jacobi_inv basis_ω h_symp B hAbel
  refine ⟨⟨{
    basis_ω := basis_ω
    shdp := inferInstance
    equiv := B.abelJacobiEquiv hAbel hJI }⟩⟩

end JacobianChallenge

end
