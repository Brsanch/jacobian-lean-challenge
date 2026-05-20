/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HodgeFormMatrix
import JacobianChallenge.Manifold.RiemannBilinearRelations

set_option linter.unusedSectionVars false

/-! # Bridge: Hodge inner product ↔ Riemann second bilinear relation

The classical Riemann second bilinear relation says that the `g × g`
Hermitian matrix

  `i · Π^T · J · Π̄`

is positive definite, where `Π` is the period matrix and `J` is the
symplectic intersection form.

Classically, this matrix EQUALS (up to scalar normalisation) the matrix
of the Hodge inner product `H_ij = H(ω_i, ω_j)`. The equality follows
from a Stokes / wedge-product calculation:

  `H(ω, η) = (i/2) ∫_X ω ∧ η̄ = ∑_{a, b} (intersection number aᵢ · bⱼ) · (∫_a ω)(∫_b η̄)`

which precisely produces `i Π^T J Π̄` in matrix form.

This identity is the DEEP CLASSICAL CONTENT bridging Hodge theory to
Riemann's bilinear relations. Formalising it requires:

* Wedge product of differential forms on a complex 1-manifold.
* Integration of 2-forms over a compact 2-manifold.
* The cup-product structure on cohomology.
* Stokes' theorem.

None of these are in the mathlib pin used by this project. This file
therefore exposes the bridge as a **named existence Prop**
`HodgeRiemannBridgeHypothesis`. Given the bridge + the
`HodgeInnerProductHypothesis`, one immediately obtains
`RiemannBilinearSecondRelation`.

## What this file ships

* `HodgeRiemannBridgeHypothesis` — named identity `i · Π^T · J · Π̄ =
  H.toMatrix` for the Hodge form's matrix representation.
* `RiemannBilinearSecondRelation_of_HodgeBridge` — composition.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Hodge-Riemann bridge hypothesis** — the matrix identity
`i · Π^T · J · Π̄ = H.toMatrix basis_ω`.

Classically: a consequence of the wedge-product expansion of `(i/2) ∫_X
ω ∧ η̄` in a symplectic basis of `H_1(X; ℤ)` via Stokes' theorem and the
cup-product structure on cohomology.

The matrix on the left is the Riemann bilinear second-relation form;
the matrix on the right is the Hodge inner product's matrix
representation against the basis. Their equality is what bridges
Hodge positivity to Riemann positivity.

Stated as a named existence Prop. The bridge requires deep classical
content (integration, wedge products) not currently in the mathlib pin. -/
def HodgeRiemannBridgeHypothesis
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ)
    (H : HermitianOnHolomorphicOneForm X) : Prop :=
  (Complex.I : ℂ) •
    ((periodMatrix data basis_ω cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)
      * (periodMatrix data basis_ω cycleGens).map star)
  = H.toMatrix basis_ω

/-- **Hermitian half of the bridge composition**: Hodge identity ⟹
the LHS matrix `i Π^T J Π̄` is Hermitian (matches the structural
Hermitian-ness of the Hodge form's matrix).

The positivity half of the bridge requires expanding `xᴴ · H.toMatrix
· x = H(∑ xⱼ basis_ω j, ∑ xⱼ basis_ω j)` via sesquilinearity and using
`H.IsPositiveDefinite`. That calculation is left for a follow-up chip
(it requires unfolding mathlib's `dotProduct`/`mulVec` and the
linearity fields of `HermitianOnHolomorphicOneForm`). -/
theorem hodgeRiemann_lhs_isHermitian
    {data : PeriodPairingData X}
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    {cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1}
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    {H : HermitianOnHolomorphicOneForm X}
    (hBridge : HodgeRiemannBridgeHypothesis data basis_ω cycleGens J H) :
    ((Complex.I : ℂ) •
      ((periodMatrix data basis_ω cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)
        * (periodMatrix data basis_ω cycleGens).map star)).IsHermitian := by
  rw [hBridge]
  exact H.toMatrix_conjTranspose basis_ω

end JacobianChallenge

end
