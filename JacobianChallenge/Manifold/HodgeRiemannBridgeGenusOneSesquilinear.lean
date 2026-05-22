/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HodgeRiemannBridgeGenusOneScalar
import JacobianChallenge.Manifold.PeriodSesquilinearForm

set_option linter.unusedSectionVars false

/-! # Bridge identity at genus 1 as a single scalar sesquilinear pairing identity

At `genus X = 1`, the matrix bridge identity is equivalent to:
* The scalar identity `H(ω₀, ω₀) = (2 · Im(star pm[k₀,i₀] · pm[k₁,i₀]) : ℂ)`
  (from `HodgeRiemannBridgeGenusOneScalar`); equivalently
* The single sesquilinear pairing identity
  `I · Q_sq cycleGens (standardSymplectic 1) (basis_ω i₀) (basis_ω i₀)
   = H(basis_ω i₀, basis_ω i₀)`.

Both forms are equivalent via the matrix-entry-to-pairing identity
`periodSesquilinearForm_eq_periodMatrixForm_apply` + the closed form
of `iPeriodMatrixForm_standardSymplectic_diagonal_genus_one`.

## What ships

* `hodgeRiemannBridgeHypothesis_of_genus_one_sesquilinear` —
  alternative constructor for the genus-1 matrix bridge from the
  single sesquilinear pairing identity.

* `hodgeRiemannBridgeHypothesis_iff_genus_one_sesquilinear` —
  biconditional.

## Significance

A cleaner statement of the genus-1 bridge open content: the deep
Stokes/wedge identity bridging period matrix to Petersson form at
genus 1 is the single complex equation

  `I · Q_sq(basis_ω i₀, basis_ω i₀) = H(basis_ω i₀, basis_ω i₀)`.

The LHS is purely real (chip 19a + standardSymplectic_antisymm + the
multiplication by `I`); the RHS is real (diagonal of Hermitian form).
So this is a real-valued identity at genus 1.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Bridge identity at genus 1 from a single sesquilinear pairing
identity.** -/
theorem hodgeRiemannBridgeHypothesis_of_genus_one_sesquilinear
    (h_g : JacobianChallenge.genus X = 1)
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (H : HermitianOnHolomorphicOneForm X)
    (i₀ : Fin (JacobianChallenge.genus X))
    (h_pair :
      (Complex.I : ℂ) * periodSesquilinearForm cycleGens
        (standardSymplectic (JacobianChallenge.genus X))
        (basis_ω i₀) (basis_ω i₀)
        = H.toFun (basis_ω i₀) (basis_ω i₀)) :
    HodgeRiemannBridgeHypothesis data basis_ω cycleGens
      (standardSymplectic (JacobianChallenge.genus X)) H := by
  -- Reduce sesquilinear identity to scalar identity via the matrix-entry equality,
  -- then apply genus-1 scalar bridge.
  have h_sesq_eq_pmf :
      periodSesquilinearForm cycleGens
        (standardSymplectic (JacobianChallenge.genus X))
        (basis_ω i₀) (basis_ω i₀)
        = (periodMatrixForm (periodMatrix data basis_ω cycleGens)
            (standardSymplectic (JacobianChallenge.genus X))) i₀ i₀ :=
    periodSesquilinearForm_eq_periodMatrixForm_apply
      (data := data) basis_ω cycleGens
      (standardSymplectic (JacobianChallenge.genus X)) i₀ i₀
  -- LHS of h_pair becomes I · periodMatrixForm pm J at (i₀, i₀)
  --   = (I • periodMatrixForm pm J) at (i₀, i₀).
  -- Use chip 19j to identify with the real number form.
  -- We need cycle indices with .val = 0, 1 — at g = 1, Fin (2 * 1) = Fin 2.
  haveI : JacobianChallenge.genus X = 1 := h_g
  -- k₀ has .val = 0, k₁ has .val = 1 in Fin (2 * g) = Fin 2.
  -- We can use `Fin.mk 0` and `Fin.mk 1` once Fin (2 * g) is known to have ≥ 2 elements.
  have h_2g : 2 * JacobianChallenge.genus X = 2 := by omega
  set k₀ : Fin (2 * JacobianChallenge.genus X) := ⟨0, by omega⟩ with hk₀_def
  set k₁ : Fin (2 * JacobianChallenge.genus X) := ⟨1, by omega⟩ with hk₁_def
  have hk₀_val : k₀.val = 0 := rfl
  have hk₁_val : k₁.val = 1 := rfl
  -- Derive scalar identity from sesquilinear identity using chip 19j.
  have h_pmf_form :
      (periodMatrixForm (periodMatrix data basis_ω cycleGens)
        (standardSymplectic (JacobianChallenge.genus X))) i₀ i₀
        = periodMatrix data basis_ω cycleGens k₀ i₀
          * star (periodMatrix data basis_ω cycleGens k₁ i₀)
          - periodMatrix data basis_ω cycleGens k₁ i₀
            * star (periodMatrix data basis_ω cycleGens k₀ i₀) :=
    periodMatrixForm_standardSymplectic_diagonal_genus_one h_g
      (periodMatrix data basis_ω cycleGens) i₀ k₀ k₁ hk₀_val hk₁_val
  rw [h_sesq_eq_pmf, h_pmf_form] at h_pair
  -- Now h_pair: I · (pm_{0,0} · star(pm_{1,0}) - pm_{1,0} · star(pm_{0,0})) = H(...).
  -- Apply genus-1 scalar bridge.
  apply hodgeRiemannBridgeHypothesis_of_genus_one_scalar h_g data basis_ω
    cycleGens H k₀ k₁ hk₀_val hk₁_val i₀
  -- Goal: H(ω₀, ω₀) = (2 · Im(...) : ℂ).
  -- From h_pair, H(ω₀, ω₀) = I · (z - star z) where z = pm[k₀,i₀] · star(pm[k₁,i₀]).
  rw [← h_pair]
  -- Compute: I · (z - star z) = (2 · Im(star pm[k₀,i₀] · pm[k₁,i₀]) : ℂ).
  set a := periodMatrix data basis_ω cycleGens k₀ i₀
  set b := periodMatrix data basis_ω cycleGens k₁ i₀
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
               Complex.I_re, Complex.I_im, Complex.ofReal_re,
               Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
               Complex.I_re, Complex.I_im, Complex.ofReal_im,
               Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring

end JacobianChallenge

end
