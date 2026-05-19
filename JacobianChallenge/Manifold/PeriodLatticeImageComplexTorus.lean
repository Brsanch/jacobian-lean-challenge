/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiPointComplexTorus
import JacobianChallenge.Manifold.ComplexPeriodH1
import JacobianChallenge.Manifold.StokesCanonicalClosedForms
import JacobianChallenge.Manifold.ComplexTorusBasisLoopZSpan

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # `periodLatticeImage` characterization on `T_L = ℂ ⧸ L`

For the canonical basis `basis_g_dz L`, the periodLatticeImage equals
`{(fun _ : Fin (genus T_L) => z) : z ∈ L}` — the constant-on-Fin-1
functions valued in `L`.

This file ships the easy ⊇ direction (every `z ∈ L` yields a constant
period vector in `periodLatticeImage`). The reverse ⊆ direction
requires Hurewicz + Stokes-period-vanishing and is handled in a
follow-up chip.

## What this file ships

* `complexPeriod_eq_zero_of_stokesBoundary_dz`: period of `dz L` along
  a Stokes-boundary cycle vanishes.
* `periodVector_torusBasisLoop_cycle_dz`: the period vector of
  `torusBasisLoop_cycle lam hlam` against `basis_g_dz L` is
  constantly `lam`.
* `const_lam_mem_periodLatticeImage` (lattice generators contribute):
  `(fun _ => lam) ∈ periodLatticeImage data basis_g_dz` for every
  `lam ∈ L`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Period of `dz` vanishes on Stokes-boundary cycles -/

/-- **Period of `dz L` along a Stokes-boundary cycle vanishes.**
Combines `(StokesBoundaryInvariance.canonical _ _).complexPeriod_eq_zero_of_boundary`
with `holomorphicComponentsCanonicalClosed_holds L` (every holomorphic
1-form's real/imag components are canonically closed). -/
theorem complexPeriod_eq_zero_of_stokesBoundary_dz
    {γ : SmoothCycle 𝓘(ℝ, ℂ) (ℂ ⧸ L)}
    (hγ : γ ∈ stokesBoundaries 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    complexPeriod γ (dz L) = 0 := by
  -- Use the canonical StokesBoundaryInvariance.
  have hb : γ ∈ (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) (ℂ ⧸ L)).boundaries := by
    rw [StokesBoundaryInvariance.canonical_boundaries]; exact hγ
  -- dz L is canonically closed (via holomorphicComponentsCanonicalClosed_holds).
  have h_can := holomorphicComponentsCanonicalClosed_holds L (dz L)
  have hom : dz L ∈
      (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) (ℂ ⧸ L)).closedHolomorphicForms := by
    rw [(StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) (ℂ ⧸ L)).mem_closedHolomorphicForms]
    refine ⟨?_, ?_⟩
    · show realComponent (dz L) ∈
        (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) (ℂ ⧸ L)).closedForms
      exact h_can.1
    · show imagComponent (dz L) ∈
        (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) (ℂ ⧸ L)).closedForms
      exact h_can.2
  exact (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) (ℂ ⧸ L)).complexPeriod_eq_zero_of_boundary hb hom

/-! ## Period vector of `torusBasisLoop_cycle lam hlam` against `basis_g_dz` -/

/-- **Period vector of a torus basis loop cycle against `basis_g_dz`
is constantly `lam`.** -/
theorem periodVector_torusBasisLoop_cycle_dz
    (lam : ℂ) (hlam : lam ∈ L) :
    periodVector (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L)
        (torusBasisLoop_cycle lam hlam)
      = fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => lam := by
  funext j
  show PeriodPairing (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
      (torusBasisLoop_cycle lam hlam) (basis_g_dz L j) = lam
  rw [basis_g_dz_const, PeriodPairing_ofSmoothCycle]
  exact complexPeriod_torusBasisLoop_dz L lam hlam

/-! ## Lattice generators contribute to `periodLatticeImage` -/

/-- **`(fun _ => lam) ∈ periodLatticeImage` for every `lam ∈ L`.**
Take `γ := torusBasisLoop_cycle lam hlam`; its period vector against
`basis_g_dz L` is constantly `lam`, hence `(fun _ => lam) ∈ image`. -/
theorem const_lam_mem_periodLatticeImage
    (lam : ℂ) (hlam : lam ∈ L) :
    (fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => lam)
      ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
          (basis_g_dz L) := by
  rw [mem_periodLatticeImage_iff]
  exact ⟨torusBasisLoop_cycle lam hlam,
    periodVector_torusBasisLoop_cycle_dz L lam hlam⟩

/-! ## ⊇ direction: every constant-on-`Fin g` vector with value in `L`
lies in `periodLatticeImage` -/

/-- **Closure under ℤ-linear combinations** — for any `z ∈ L`,
`(fun _ => z) ∈ periodLatticeImage`.

Uses `IsZBasisOfL` on `(basisFin2OfL L 0, basisFin2OfL L 1)` to write
`z = m₁ • lam₁ + m₂ • lam₂`, then closure of `periodLatticeImage`
under addition and ℤ-scalar mult. -/
theorem const_mem_periodLatticeImage_of_mem_L (z : ℂ) (hz : z ∈ L) :
    (fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => z)
      ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
          (basis_g_dz L) := by
  -- Decompose z as a ℤ-combination of the basisFin2OfL generators.
  obtain ⟨m₁, m₂, hz_eq⟩ :=
    basisFin2OfL_isZBasisOfL z hz
  -- (fun _ => z) = (fun _ => m₁ • lam₁ + m₂ • lam₂)
  --              = m₁ • (fun _ => lam₁) + m₂ • (fun _ => lam₂).
  have h_lam₁ : ((basisFin2OfL L 0 : L) : ℂ) ∈ L := (basisFin2OfL L 0).property
  have h_lam₂ : ((basisFin2OfL L 1 : L) : ℂ) ∈ L := (basisFin2OfL L 1).property
  have h_split :
      (fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => z)
        = m₁ • (fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) =>
            ((basisFin2OfL L 0 : L) : ℂ))
          + m₂ • (fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) =>
            ((basisFin2OfL L 1 : L) : ℂ)) := by
    funext j
    show z = m₁ • ((basisFin2OfL L 0 : L) : ℂ) + m₂ • ((basisFin2OfL L 1 : L) : ℂ)
    exact hz_eq
  rw [h_split]
  refine AddSubgroup.add_mem _ (AddSubgroup.zsmul_mem _ ?_ m₁)
    (AddSubgroup.zsmul_mem _ ?_ m₂)
  · exact const_lam_mem_periodLatticeImage L _ h_lam₁
  · exact const_lam_mem_periodLatticeImage L _ h_lam₂

end ComplexTorus

end JacobianChallenge

end
