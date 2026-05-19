/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusPeriodValue
import JacobianChallenge.Manifold.ComplexTorusSymplecticBasis
import JacobianChallenge.Manifold.ComplexTorusDz
import JacobianChallenge.Manifold.PeriodLatticeFromPairing

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Riemann bilinear on the complex torus

For a complex torus `T_L = ℂ ⧸ L` with a chosen pair of lattice
generators `(lam₁, lam₂)` that are ℝ-linearly independent in ℂ, the
period vectors of the symplectic basis cycles against `dz` are
ℝ-linearly independent in `Fin 1 → ℂ`.

Combines:
* `complexPeriod_torusBasisLoop_dz` (period of dz over γ_lam = lam).
* `LinearIndependent ℝ ![lam₁, lam₂]` → `LinearIndependent ℝ
  (fun i : Fin 2 => fun _ : Fin 1 => period(γ_lam_i))`.

## What this file ships

* `ComplexTorus.basis_one_dz : Basis (Fin 1) ℂ (HolomorphicOneForm
  (ℂ ⧸ L))` *conditional on* the upper bound `genus ≤ 1` (provided
  as an extensionality hypothesis: dz spans the space).

* `ComplexTorus.riemannBilinear_torus`: the ℝ-linear independence
  of the period vectors of the symplectic basis against `dz`.

The closure assumes:
- `(lam₁, lam₂)` are ℝ-linearly independent in ℂ (i.e., their
  ℝ-span is all of ℂ, hence they form a ℝ-basis of ℂ ≅ ℝ²). For
  a ℤ-basis of a full-rank lattice, this is automatic; we leave
  it as an explicit hypothesis to keep the chip narrowly scoped.

No `sorry`, no `axiom`. -/

open Module
open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Period vectors of the symplectic basis at `dz` -/

/-- For each `i : Fin 2`, the period vector of `symplecticBasis.cycleGens i`
against a one-element basis `{dz}` is `fun _ : Fin 1 => (if i = 0 then
lam₁ else lam₂)`. -/
private lemma periodVector_symplecticBasis
    (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L)
    (basis_one : Basis (Fin 1) ℂ (HolomorphicOneForm (ℂ ⧸ L)))
    (h_basis_zero : basis_one 0 = dz L)
    (i : Fin 2) :
    (fun j : Fin 1 =>
        PeriodPairing (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
          ((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens
            (Fin.cast (by decide) i : Fin (2 * 1)))
          (basis_one j))
      = fun _ : Fin 1 => if i.val = 0 then lam₁ else lam₂ := by
  funext j
  -- j : Fin 1, so j = 0.
  fin_cases j
  -- basis_one ⟨0, _⟩ = basis_one 0 by definitional unfolding.
  change PeriodPairing (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
      ((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens
        (Fin.cast (by decide) i)) (basis_one 0)
      = if i.val = 0 then lam₁ else lam₂
  -- PeriodPairing _ cycle dz = complexPeriod cycle dz (by PeriodPairing_ofSmoothCycle).
  rw [h_basis_zero, PeriodPairing_ofSmoothCycle]
  -- cycleGens (cast i) = single_smoothLoop_smoothCycle (symplecticBasis.basis (cast i))
  -- = single_smoothLoop_smoothCycle (if (cast i).val = 0 then torusBasisLoop lam₁ _
  --   else torusBasisLoop lam₂ _)
  by_cases h : i.val = 0
  · -- i = 0 case: basis 0 = torusBasisLoop lam₁.
    simp only [h, if_true]
    have h_i0 : i = ⟨0, by decide⟩ := Fin.ext h
    subst h_i0
    -- (symplecticBasis L lam₁ lam₂ _ _).cycleGens (Fin.cast _ ⟨0, _⟩) = ...
    show complexPeriod
      ((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens
        (Fin.cast (by decide) ⟨0, by decide⟩))
      (dz L) = lam₁
    -- cycleGens ⟨0, _⟩ for symplecticBasis = single_smoothLoop_smoothCycle (basis 0).
    have h_cg :
        (symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens
          (Fin.cast (by decide) (⟨0, by decide⟩ : Fin 2))
        = single_smoothLoop_smoothCycle (torusBasisLoop lam₁ hlam₁)
            ((torusBasisLoop_src lam₁ hlam₁).trans
              (torusBasisLoop_tgt lam₁ hlam₁).symm) := by
      apply Subtype.ext
      simp only [SmoothSymplecticBasis.cycleGens_coe]
      rw [single_smoothLoop_smoothCycle_coe]
      -- (symplecticBasis _ _ _ _ _).basis (Fin.cast _ ⟨0, _⟩) = torusBasisLoop lam₁ _.
      show SmoothChain.single
          ((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).basis
            (Fin.cast (by decide) (⟨0, by decide⟩ : Fin 2)))
        = SmoothChain.single (torusBasisLoop lam₁ hlam₁)
      rfl
    rw [h_cg]
    exact complexPeriod_torusBasisLoop_dz L lam₁ hlam₁
  · -- i = 1 case.
    simp only [h, if_false]
    have hi : i.val = 1 := by omega
    have h_i1 : i = ⟨1, by decide⟩ := Fin.ext hi
    subst h_i1
    show complexPeriod
      ((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens
        (Fin.cast (by decide) ⟨1, by decide⟩))
      (dz L) = lam₂
    have h_cg :
        (symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens
          (Fin.cast (by decide) (⟨1, by decide⟩ : Fin 2))
        = single_smoothLoop_smoothCycle (torusBasisLoop lam₂ hlam₂)
            ((torusBasisLoop_src lam₂ hlam₂).trans
              (torusBasisLoop_tgt lam₂ hlam₂).symm) := by
      apply Subtype.ext
      simp only [SmoothSymplecticBasis.cycleGens_coe]
      rw [single_smoothLoop_smoothCycle_coe]
      show SmoothChain.single
          ((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).basis
            (Fin.cast (by decide) (⟨1, by decide⟩ : Fin 2)))
        = SmoothChain.single (torusBasisLoop lam₂ hlam₂)
      rfl
    rw [h_cg]
    exact complexPeriod_torusBasisLoop_dz L lam₂ hlam₂

/-! ## ℝ-linear independence -/

/-- **Riemann bilinear on `T_L`.** Given:
- `(lam₁, lam₂)` lattice generators in L;
- a one-element basis `{dz}` of `HolomorphicOneForm (ℂ ⧸ L)`
  (caller's responsibility — uses the `genus = 1` hypothesis);
- ℝ-linear independence of `(lam₁, lam₂)` in ℂ (e.g., from being a
  ℤ-basis of a discrete rank-2 lattice);

the period vectors of the symplectic basis cycles `(γ_lam_1, γ_lam_2)`
against `{dz}` are ℝ-linearly independent in `Fin 1 → ℂ`. -/
theorem riemannBilinear_torus
    (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L)
    (basis_one : Basis (Fin 1) ℂ (HolomorphicOneForm (ℂ ⧸ L)))
    (h_basis_zero : basis_one 0 = dz L)
    (h_indep : LinearIndependent ℝ ![lam₁, lam₂]) :
    LinearIndependent ℝ
      (fun i : Fin 2 =>
        fun j : Fin 1 =>
          PeriodPairing (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
            ((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens
              (Fin.cast (by decide) i : Fin (2 * 1)))
            (basis_one j)) := by
  -- Pointwise simplification of each period vector.
  have h_eq : ∀ i : Fin 2,
      (fun j : Fin 1 =>
          PeriodPairing (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
            ((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens
              (Fin.cast (by decide) i : Fin (2 * 1)))
            (basis_one j))
        = fun _ : Fin 1 => if i.val = 0 then lam₁ else lam₂ :=
    periodVector_symplecticBasis L lam₁ lam₂ hlam₁ hlam₂ basis_one h_basis_zero
  -- Use `funext` to rewrite the family.
  have h_simp :
      (fun i : Fin 2 =>
        fun j : Fin 1 =>
          PeriodPairing (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
            ((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens
              (Fin.cast (by decide) i : Fin (2 * 1)))
            (basis_one j))
        = fun i : Fin 2 =>
          fun _ : Fin 1 => if i.val = 0 then lam₁ else lam₂ := by
    funext i
    exact h_eq i
  rw [h_simp]
  -- Goal: LinearIndependent ℝ (fun i : Fin 2 => fun _ : Fin 1 => if i.val = 0 then lam₁ else lam₂).
  -- ![lam₁, lam₂] = fun i : Fin 2 => if i.val = 0 then lam₁ else lam₂.
  have h_eq2 :
      (fun i : Fin 2 => if i.val = 0 then lam₁ else lam₂)
        = (![lam₁, lam₂] : Fin 2 → ℂ) := by
    funext i
    by_cases h : i.val = 0
    · have hi : i = 0 := Fin.ext h
      subst hi
      simp
    · have hi : i = 1 := Fin.ext (by omega)
      subst hi
      simp
  have h_funext :
      (fun i : Fin 2 => fun _ : Fin 1 => if i.val = 0 then lam₁ else lam₂)
        = (fun i : Fin 2 => fun _ : Fin 1 => (![lam₁, lam₂] : Fin 2 → ℂ) i) := by
    funext i j
    have := congrFun h_eq2 i
    exact this
  rw [h_funext]
  -- LinearIndependent ℝ (fun i => fun _ : Fin 1 => v i) where v = ![lam₁, lam₂].
  -- Use the equivalence (Fin 1 → ℂ) ≃ₗ[ℝ] ℂ inline.
  let h_equiv : (Fin 1 → ℂ) ≃ₗ[ℝ] ℂ :=
    LinearEquiv.funUnique (Fin 1) ℝ ℂ
  have h_factor :
      (fun i : Fin 2 => fun _ : Fin 1 => (![lam₁, lam₂] : Fin 2 → ℂ) i)
        = h_equiv.symm ∘ (![lam₁, lam₂] : Fin 2 → ℂ) := by
    funext i j
    simp [h_equiv, LinearEquiv.funUnique_symm_apply]
  rw [h_factor]
  -- LinearIndependent of a comp with injective ℝ-linear map.
  exact h_indep.map' h_equiv.symm.toLinearMap h_equiv.symm.ker

end ComplexTorus

end JacobianChallenge

end
