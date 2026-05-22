/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasPic0AnalyticEquiv
import JacobianChallenge.Manifold.MorseSmoothHurewicz
import JacobianChallenge.Manifold.AbelGeneralXHypotheses
import JacobianChallenge.Manifold.SmoothPathConnectedSymp

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-! # Phase G — Joint composition `D + E + F → HasPic0AnalyticEquiv X`

The final piece of the item-5 closure plan: given the four named
hypotheses of Phases D + E + F, construct `HasPic0AnalyticEquiv X`,
which (via Phase A's AddEquiv-transfer infrastructure) discharges
the cascade of items 5/11/12/13/17/18/21 in `Basic.lean`.

## The composition

1. **Phase D-3 bridge**: combines `MorsePerfectExistsHypothesis X
   (genus X)` + `MorseToSHDPHypothesis basis_ω` to produce
   `HasSmoothHomologyDataPackage X basis_ω`.

2. **Canonical bundle extraction**: the SHDP instance extracts a
   canonical `PeriodLatticeSymplecticBundle` via
   `canonicalPeriodLatticeSymplecticBundle basis_ω`.

3. **`AbelJacobiInputSymp` existence**: from `[ConnectedSpace X]` +
   `smoothPathConnected_of_preconnected` +
   `AbelJacobiInputSymp.nonempty_of_connected` we get
   `Nonempty (AbelJacobiInputSymp α canonicalBundle)`.

4. **Phase E**: `AbelGeneralXHypothesis X` discharges
   `AbelJacobiInputSymp.AbelHypothesis B` for any `B`.

5. **Phase F**: `JacobiInversionGeneralXHypothesis X` discharges
   `AbelJacobiInputSymp.JacobiInversion B hAbel`.

6. **AddEquiv composition**:
   `B.abelJacobiEquiv hAbel hJI : Pic⁰ X ≃+ AnalyticJacobianSymp _ α h`.
   And `AnalyticJacobianSymp _ basis_ω canonicalBundle =
        CanonicalAnalyticJacobian basis_ω` definitionally.

7. **Package** into `Pic0AnalyticEquivBundle X` → `HasPic0AnalyticEquiv X`.

When all four hypotheses are discharged unconditionally (Phases D / E /
F's open content), this gives an unconditional
`HasPic0AnalyticEquiv X` instance on any compact connected complex
1-manifold X — the keystone of the Basic.lean cascade flip.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Phase G — joint composition.** Given the four named hypotheses
of Phases D-E-F (plus a chosen `basis_ω`), produce
`HasPic0AnalyticEquiv X`. -/
theorem hasPic0AnalyticEquiv_of_phases_DEFG
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (h_morse_exists : MorsePerfectExistsHypothesis X (JacobianChallenge.genus X))
    (h_morse_bridge : MorseToSHDPHypothesis (X := X) basis_ω)
    (h_abel : AbelGeneralXHypothesis X)
    (h_jacobi_inv : JacobiInversionGeneralXHypothesis X) :
    HasPic0AnalyticEquiv X := by
  -- Step 1+2: Phase D bridge → `HasSmoothHomologyDataPackage X basis_ω`.
  haveI hSHDP : HasSmoothHomologyDataPackage (X := X) basis_ω :=
    hasSmoothHomologyDataPackage_of_morse_hypotheses h_morse_exists h_morse_bridge
  -- Step 2: extract the canonical symplectic bundle.
  let h_symp : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle X) basis_ω :=
    canonicalPeriodLatticeSymplecticBundle (X := X) basis_ω
  -- Step 3: get an `AbelJacobiInputSymp` from connectedness.
  have hB_nonempty :
      Nonempty (AbelJacobiInputSymp (X := X) (α := basis_ω) (h := h_symp)) :=
    AbelJacobiInputSymp.nonempty_of_connected basis_ω h_symp
  let B : AbelJacobiInputSymp (X := X) (α := basis_ω) (h := h_symp) :=
    Classical.choice hB_nonempty
  -- Step 4: Phase E discharges Abel for our `B`.
  have hAbel : AbelJacobiInputSymp.AbelHypothesis B :=
    h_abel basis_ω h_symp B
  -- Step 5: Phase F discharges Jacobi inversion.
  have hJI : AbelJacobiInputSymp.JacobiInversion B hAbel :=
    h_jacobi_inv basis_ω h_symp B hAbel
  -- Step 6+7: AddEquiv composition + package into the bundle.
  -- `B.abelJacobiEquiv hAbel hJI : Pic⁰ X ≃+ AnalyticJacobianSymp _ basis_ω h_symp`.
  -- `AnalyticJacobianSymp _ basis_ω canonicalBundle = CanonicalAnalyticJacobian basis_ω`
  -- definitionally (both unfold to `JacobianOfLattice X (ofSymplectic data basis_ω _)`
  -- with the canonical bundle).
  refine ⟨⟨{
    basis_ω := basis_ω
    shdp := hSHDP
    equiv := ?_ }⟩⟩
  -- The equiv: `Pic⁰ X ≃+ CanonicalAnalyticJacobian basis_ω`.
  -- `B.abelJacobiEquiv hAbel hJI` already lives at the right type
  -- via the definitional unfolding of `CanonicalAnalyticJacobian`.
  exact B.abelJacobiEquiv hAbel hJI

end JacobianChallenge

end
