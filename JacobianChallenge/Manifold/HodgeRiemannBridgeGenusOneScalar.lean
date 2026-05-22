/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HodgeRiemannBridge
import JacobianChallenge.Manifold.PeriodMatrixFormStandardSymplecticOneSymbolic

set_option linter.unusedSectionVars false

/-! # Bridge identity at genus 1 reduces to a single scalar identity

The `HodgeRiemannBridgeHypothesis` matrix identity
`i · pmᵀ · J · pm.map star = H.toMatrix basis_ω` at `J =
standardSymplectic g` is a `g × g` matrix equality. At `genus X = 1`,
both sides are `1 × 1` matrices over `Fin 1`, so the bridge identity
collapses to a **single scalar equality** at the unique entry `(i₀, i₀)`
for any `i₀ : Fin g`.

Using chip 19j's closed form for the diagonal of `i • periodMatrixForm
pm (standardSymplectic g)` at `g = 1`, that scalar identity becomes

  `H(basis_ω i₀, basis_ω i₀) = (2 · Im(star (pm k₀ i₀) · pm k₁ i₀) : ℂ)`,

where `pm := periodMatrix data basis_ω cycleGens` and `k₀, k₁ : Fin (2 * g)`
are any two cycle indices with `k₀.val = 0` and `k₁.val = 1`.

The forward direction shows the matrix bridge implies the scalar form;
the backward direction (the substantive content) shows that the scalar
identity at the unique basis index forces the full matrix identity at
genus 1.

## What this file ships

* `hodgeRiemannBridgeHypothesis_of_genus_one_scalar` — backward: from
  the single scalar identity to the full matrix bridge at `g = 1`.

* `hodgeRiemannBridgeHypothesis_iff_genus_one_scalar` — biconditional
  packaging.

## Significance

At genus 1, the deep classical content of `HodgeRiemannBridgeHypothesis`
collapses to a **single scalar identity** between the Hodge inner
product on the unique basis form `ω₀` and the imaginary part of the
product of its two periods. On `T_L = ℂ ⧸ L` with explicit lattice
basis `{lam₁, lam₂}` and periods `(lam₁, lam₂)`, this scalar identity
is `H(dz, dz) = 2 · Im(star lam₁ · lam₂) = 2 · area(L)` — the
fundamental Riemann area identity at genus 1.

For general genus-1 `X`, this scalar identity is the substantive
analytic input (deep Stokes) that bridges the period matrix to the
Petersson L²-norm of the unique basis form.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Bridge identity at genus 1 from a single scalar identity.**

At `genus X = 1`, the full `1 × 1` matrix bridge follows from the
single scalar equality at the unique basis index `i₀ : Fin g`:

  `H(basis_ω i₀, basis_ω i₀) = (2 · Im(star (pm k₀ i₀) · pm k₁ i₀) : ℂ)`,

where `pm := periodMatrix data basis_ω cycleGens` and `k₀, k₁ :
Fin (2 * g)` are any two cycle indices with `.val = 0, 1`. -/
theorem hodgeRiemannBridgeHypothesis_of_genus_one_scalar
    (h_g : JacobianChallenge.genus X = 1)
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (H : HermitianOnHolomorphicOneForm X)
    (k₀ k₁ : Fin (2 * JacobianChallenge.genus X))
    (h_k₀ : k₀.val = 0) (h_k₁ : k₁.val = 1)
    (i₀ : Fin (JacobianChallenge.genus X))
    (h_scalar :
      H.toFun (basis_ω i₀) (basis_ω i₀)
        = ((2 *
            (star (periodMatrix data basis_ω cycleGens k₀ i₀)
              * periodMatrix data basis_ω cycleGens k₁ i₀).im : ℝ) : ℂ)) :
    HodgeRiemannBridgeHypothesis data basis_ω cycleGens
      (standardSymplectic (JacobianChallenge.genus X)) H := by
  -- The bridge identity is `(I • periodMatrixForm pm (standardSymplectic g))
  -- = H.toMatrix basis_ω`. Unfold to matrix-entry equality and use
  -- Subsingleton (Fin g) at g = 1 to reduce all entries to (i₀, i₀).
  unfold HodgeRiemannBridgeHypothesis
  haveI hSub : Subsingleton (Fin (JacobianChallenge.genus X)) := by
    rw [h_g]; infer_instance
  -- Matrix equality: pointwise.
  funext i j
  -- All indices collapse to `i₀`.
  have h_i : i = i₀ := Subsingleton.elim _ _
  have h_j : j = i₀ := Subsingleton.elim _ _
  rw [h_i, h_j]
  -- Identify with iPeriodMatrixForm via the periodMatrixForm def, then use chip 19j.
  rw [show ((Complex.I : ℂ) •
        ((periodMatrix data basis_ω cycleGens)ᵀ
          * (standardSymplectic (JacobianChallenge.genus X)).map
              ((↑) : ℤ → ℂ)
          * (periodMatrix data basis_ω cycleGens).map star)) i₀ i₀
      = ((Complex.I : ℂ) •
          periodMatrixForm (periodMatrix data basis_ω cycleGens)
            (standardSymplectic (JacobianChallenge.genus X))) i₀ i₀ from rfl,
      iPeriodMatrixForm_standardSymplectic_diagonal_genus_one h_g
        (periodMatrix data basis_ω cycleGens) i₀ k₀ k₁ h_k₀ h_k₁,
      HermitianOnHolomorphicOneForm.toMatrix_apply]
  exact h_scalar.symm

/-- **Biconditional packaging of the genus-1 bridge identity.** At
`genus X = 1`, the matrix `HodgeRiemannBridgeHypothesis` for
`J = standardSymplectic g` is equivalent to the single scalar identity
`H(basis_ω i₀, basis_ω i₀) = (2 · Im(...) : ℂ)`. -/
theorem hodgeRiemannBridgeHypothesis_iff_genus_one_scalar
    (h_g : JacobianChallenge.genus X = 1)
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (H : HermitianOnHolomorphicOneForm X)
    (k₀ k₁ : Fin (2 * JacobianChallenge.genus X))
    (h_k₀ : k₀.val = 0) (h_k₁ : k₁.val = 1)
    (i₀ : Fin (JacobianChallenge.genus X)) :
    HodgeRiemannBridgeHypothesis data basis_ω cycleGens
        (standardSymplectic (JacobianChallenge.genus X)) H ↔
      H.toFun (basis_ω i₀) (basis_ω i₀)
        = ((2 *
            (star (periodMatrix data basis_ω cycleGens k₀ i₀)
              * periodMatrix data basis_ω cycleGens k₁ i₀).im : ℝ) : ℂ) := by
  refine ⟨fun h_bridge => ?_,
          hodgeRiemannBridgeHypothesis_of_genus_one_scalar h_g data
            basis_ω cycleGens H k₀ k₁ h_k₀ h_k₁ i₀⟩
  -- Forward: from the full matrix bridge to the (i₀, i₀) entry.
  have h_entry := congrFun (congrFun h_bridge i₀) i₀
  -- LHS via chip 19j; RHS via toMatrix_apply.
  have h_lhs :
      ((Complex.I : ℂ) •
        ((periodMatrix data basis_ω cycleGens)ᵀ
          * (standardSymplectic (JacobianChallenge.genus X)).map
              ((↑) : ℤ → ℂ)
          * (periodMatrix data basis_ω cycleGens).map star)) i₀ i₀
        = ((2 *
            (star (periodMatrix data basis_ω cycleGens k₀ i₀)
              * periodMatrix data basis_ω cycleGens k₁ i₀).im : ℝ) : ℂ) := by
    show ((Complex.I : ℂ) •
        periodMatrixForm (periodMatrix data basis_ω cycleGens)
          (standardSymplectic (JacobianChallenge.genus X))) i₀ i₀ = _
    exact iPeriodMatrixForm_standardSymplectic_diagonal_genus_one h_g
      (periodMatrix data basis_ω cycleGens) i₀ k₀ k₁ h_k₀ h_k₁
  rw [h_lhs] at h_entry
  rw [HermitianOnHolomorphicOneForm.toMatrix_apply] at h_entry
  exact h_entry.symm

end JacobianChallenge

end
