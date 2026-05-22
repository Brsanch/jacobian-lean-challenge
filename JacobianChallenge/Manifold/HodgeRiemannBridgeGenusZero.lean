/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HodgeRiemannBridge
import JacobianChallenge.Manifold.HodgeRiemannBridgeComposition
import JacobianChallenge.Analysis.HodgeInnerProductDischarge

set_option linter.unusedSectionVars false

/-! # `HodgeRiemannBridgeHypothesis` discharged unconditionally at genus 0

The deep classical content of `HodgeRiemannBridgeHypothesis` (the matrix
identity `i Π^T J Π̄ = H.toMatrix basis_ω` bridging Hodge form ↔ period
matrix) collapses to a trivial 0×0 matrix equality whenever the genus
of `X` is 0: both sides are then matrices over `Fin (genus X) = Fin 0`,
which has the unique element-free function.

## What ships

* `hodgeRiemannBridgeHypothesis_of_genus_zero` — for every
  `data : PeriodPairingData X`, basis `basis_ω`, cycle generators,
  symplectic form `J`, and Hermitian form `H`, if `genus X = 0` the
  bridge identity holds.

* `riemannBilinearSecondRelation_of_genus_zero` — composing the bridge
  discharge with `RiemannBilinearSecondRelation_of_HodgeBridge` yields
  the Riemann second relation **unconditionally** at genus 0.

Combined with this session's unconditional `HodgeInnerProductHypothesis X`
discharge (via the global Petersson Hermitian form), the Riemann
bilinear second relation is now fully unconditional on every compact
connected complex 1-manifold of genus 0. This is concrete classical
content on the C3 path to flipping items 5/11/12/13 at the genus-0
specialization.

For genus ≥ 1, the bridge identity remains genuine open classical
content (wedge product + Stokes + cup-product; not in mathlib at the
pinned commit).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HodgeRiemannBridgeHypothesis` is unconditional at genus 0.**

At `genus X = 0`, both sides of the bridge identity are matrices over
the empty type `Fin 0`, hence equal by extensionality. -/
theorem hodgeRiemannBridgeHypothesis_of_genus_zero
    (h_g : JacobianChallenge.genus X = 0)
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ)
    (H : HermitianOnHolomorphicOneForm X) :
    HodgeRiemannBridgeHypothesis data basis_ω cycleGens J H := by
  unfold HodgeRiemannBridgeHypothesis
  have h_empty : IsEmpty (Fin (JacobianChallenge.genus X)) := by
    rw [h_g]; exact Fin.isEmpty
  ext i j
  exact h_empty.elim i

/-- **`RiemannBilinearSecondRelation` is unconditional at genus 0.**

Composes the genus-0 bridge discharge with
`RiemannBilinearSecondRelation_of_HodgeBridge`, taking any
`H.IsPositiveDefinite` witness (e.g. the global Petersson Hermitian
form's positive-definiteness shipped this session). -/
theorem riemannBilinearSecondRelation_of_genus_zero
    (h_g : JacobianChallenge.genus X = 0)
    {data : PeriodPairingData X}
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    {cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1}
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    {H : HermitianOnHolomorphicOneForm X}
    (hPD : H.IsPositiveDefinite) :
    RiemannBilinearSecondRelation data basis_ω cycleGens J :=
  RiemannBilinearSecondRelation_of_HodgeBridge hPD
    (hodgeRiemannBridgeHypothesis_of_genus_zero h_g data basis_ω cycleGens J H)

/-- **Fully unconditional `RiemannBilinearSecondRelation` at genus 0.**

Composes the genus-0 bridge discharge with this session's unconditional
`HodgeInnerProductHypothesis X` discharge (via the global Petersson
Hermitian form). On every compact connected complex 1-manifold of
genus 0, the Riemann bilinear second relation holds with **no remaining
named hypothesis**. -/
theorem riemannBilinearSecondRelation_of_genus_zero_unconditional
    (h_g : JacobianChallenge.genus X = 0)
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ) :
    RiemannBilinearSecondRelation data basis_ω cycleGens J := by
  obtain ⟨H, hPD⟩ := hodgeInnerProductHypothesis_holds X
  exact riemannBilinearSecondRelation_of_genus_zero (H := H) h_g hPD

end JacobianChallenge

end
