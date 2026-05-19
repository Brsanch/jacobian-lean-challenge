/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.GenericGenusPeriodLatticeInputsComplexTorus
import JacobianChallenge.Manifold.PeriodLatticeImageComplexTorus

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # `periodLatticeImage ⊆ {fun _ => z : z ∈ L}` on `T_L`

Reverse direction of the period-lattice characterization on the
complex torus. Combines:

* **`complexPeriod_cycleGens_complexTorus_mem_L`**: each of the two
  symplectic-basis cycles has period in `L`.

* **`homologyGeneration_of_spans_top`** on
  `c3StokesSpanTopInputs_complexTorus L`: every cycle decomposes as a
  ℤ-combination of `cycleGens` plus a Stokes-boundary residual.

* **`complexPeriod_eq_zero_of_stokesBoundary_dz`** (from the prior
  chip): the boundary residual's period vanishes.

Together: for every cycle `γ`, `complexPeriod γ (dz L) ∈ L`.

Finally, this gives the ⊆ direction
`periodLatticeImage ⊆ {fun _ => z : z ∈ L}` and combined with the
prior ⊇ direction the full characterization.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Period of each `symplecticBasisG.cycleGens i` -/

/-- **The `i`-th cycle of `symplecticBasisG L` decomposes by case on
`(Fin.cast _ i).val`.** -/
private lemma symplecticBasisG_cycleGens_apply
    (i : Fin (2 * JacobianChallenge.genus (ℂ ⧸ L))) :
    (symplecticBasisG L).cycleGens i
      = if (Fin.cast (by rw [genus_eq_one L]) i : Fin (2 * 1)).val = 0
        then torusBasisLoop_cycle (lam₁_complexTorus L) (lam₁_complexTorus_mem L)
        else torusBasisLoop_cycle (lam₂_complexTorus L) (lam₂_complexTorus_mem L) := by
  -- Unfold symplecticBasisG = symplecticBasisOne.reindex.
  unfold symplecticBasisG
  rw [SmoothSymplecticBasis.reindex_cycleGens_apply]
  -- Now: symplecticBasisOne.cycleGens (Fin.cast ... i)
  --  = single_smoothLoop_smoothCycle (symplecticBasisOne.basis (Fin.cast ... i)) (...)
  -- Compute symplecticBasisOne.basis at this index: it's the if-then-else.
  unfold SmoothSymplecticBasis.cycleGens
  show single_smoothLoop_smoothCycle
      ((symplecticBasisOne L).basis (Fin.cast (by rw [genus_eq_one L]) i))
      ((symplecticBasisOne L).basis_is_loop _) = _
  -- Cases on (Fin.cast _ i).val
  by_cases h : (Fin.cast (by rw [genus_eq_one L]) i : Fin (2 * 1)).val = 0
  · rw [if_pos h]
    unfold torusBasisLoop_cycle
    congr 1
    show (if (Fin.cast (by rw [genus_eq_one L]) i : Fin (2 * 1)).val = 0
          then torusBasisLoop (lam₁_complexTorus L) (lam₁_complexTorus_mem L)
          else torusBasisLoop (lam₂_complexTorus L) (lam₂_complexTorus_mem L))
      = torusBasisLoop (lam₁_complexTorus L) (lam₁_complexTorus_mem L)
    exact if_pos h
  · rw [if_neg h]
    unfold torusBasisLoop_cycle
    congr 1
    show (if (Fin.cast (by rw [genus_eq_one L]) i : Fin (2 * 1)).val = 0
          then torusBasisLoop (lam₁_complexTorus L) (lam₁_complexTorus_mem L)
          else torusBasisLoop (lam₂_complexTorus L) (lam₂_complexTorus_mem L))
      = torusBasisLoop (lam₂_complexTorus L) (lam₂_complexTorus_mem L)
    exact if_neg h

/-- **Each symplectic-basis cycle has period in `L`.** -/
theorem complexPeriod_cycleGens_complexTorus_mem_L
    (i : Fin (2 * JacobianChallenge.genus (ℂ ⧸ L))) :
    complexPeriod (cycleGens_complexTorus L i) (dz L) ∈ L := by
  show complexPeriod ((symplecticBasisG L).cycleGens i) (dz L) ∈ L
  rw [symplecticBasisG_cycleGens_apply]
  split
  · unfold torusBasisLoop_cycle
    rw [complexPeriod_torusBasisLoop_dz]
    exact lam₁_complexTorus_mem L
  · unfold torusBasisLoop_cycle
    rw [complexPeriod_torusBasisLoop_dz]
    exact lam₂_complexTorus_mem L

/-! ## Per-cycle period membership in `L` -/

/-- **Every cycle's complex period against `dz L` is in `L`.**

Proof: apply `homologyGeneration_of_spans_top` from the explicit
`c3StokesSpanTopInputs_complexTorus L` to write
`γ = ∑ nᵢ • cycleGens i + b` with `b ∈ stokesBoundaries`. Then use
linearity of `complexPeriod` in the cycle argument, vanishing on the
Stokes boundary, and that each cycleGen's period is in `L`. -/
theorem complexPeriod_mem_L_of_cycle
    (γ : (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)).H1) :
    complexPeriod γ (dz L) ∈ L := by
  classical
  obtain ⟨n, b, hb, hγ⟩ :=
    (c3StokesSpanTopInputs_complexTorus L).homologyGeneration_of_spans_top γ
  -- hb : b ∈ stokes.boundaries; stokes = canonical, so b ∈ stokesBoundaries.
  have hb' : b ∈ stokesBoundaries 𝓘(ℝ, ℂ) (ℂ ⧸ L) := by
    have := hb
    rw [c3StokesSpanTopInputs_complexTorus_stokes,
        StokesBoundaryInvariance.canonical_boundaries] at this
    exact this
  -- γ = (∑ nᵢ • cycleGens i) + b. Convert complexPeriod to complexPeriodHom for linearity.
  show complexPeriodHom (dz L) γ ∈ L
  -- Force explicit parens via a set name for the sum.
  set S : (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)).H1 :=
    ∑ i, n i • (c3StokesSpanTopInputs_complexTorus L).cycleGens i with hS_def
  have hγ' : γ = S + b := hγ
  rw [hγ']
  rw [show (complexPeriodHom (dz L)) (S + b)
        = complexPeriodHom (dz L) S + complexPeriodHom (dz L) b
        from (complexPeriodHom (dz L)).map_add S b]
  -- Expand S and apply map_sum.
  have hSum :
      complexPeriodHom (dz L) S
        = ∑ i, complexPeriodHom (dz L)
            (n i • (c3StokesSpanTopInputs_complexTorus L).cycleGens i) := by
    show (complexPeriodHom (dz L))
        (∑ i, n i • (c3StokesSpanTopInputs_complexTorus L).cycleGens i)
      = ∑ i, complexPeriodHom (dz L)
          (n i • (c3StokesSpanTopInputs_complexTorus L).cycleGens i)
    exact map_sum _ _ _
  rw [hSum]
  -- Each summand: complexPeriodHom (dz L) (n i • cycleGens i) = n i • complexPeriod (cg i) (dz L).
  -- b term vanishes.
  have hb_period : complexPeriodHom (dz L) b = 0 := by
    show complexPeriod b (dz L) = 0
    exact complexPeriod_eq_zero_of_stokesBoundary_dz L hb'
  rw [hb_period, add_zero]
  -- Sum over Fin (2 * genus T_L) of n i • complexPeriod (cycleGens i) (dz L), each ∈ L.
  apply Submodule.sum_mem
  intro i _
  -- (complexPeriodHom (dz L)) (n i • cycleGens i) = n i • complexPeriod (cycleGens i) (dz L)
  have h_zsmul :
      (complexPeriodHom (dz L)) (n i • (c3StokesSpanTopInputs_complexTorus L).cycleGens i)
        = n i • (complexPeriodHom (dz L))
            ((c3StokesSpanTopInputs_complexTorus L).cycleGens i) :=
    (complexPeriodHom (dz L)).map_zsmul _ _
  rw [h_zsmul]
  -- (c3StokesSpanTopInputs_complexTorus L).cycleGens = cycleGens_complexTorus L
  rw [c3StokesSpanTopInputs_complexTorus_cycleGens]
  show n i • complexPeriod (cycleGens_complexTorus L i) (dz L) ∈ L
  exact Submodule.smul_mem L (n i)
    (complexPeriod_cycleGens_complexTorus_mem_L L i)

/-! ## ⊆ direction: every element of `periodLatticeImage` is a constant
function with value in `L` -/

/-- **`periodLatticeImage` is contained in the constants over `L`.**
For any `v ∈ periodLatticeImage data basis_g_dz`, there exists `z ∈ L`
with `v = fun _ => z`. -/
theorem exists_const_of_mem_periodLatticeImage
    {v : Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ}
    (hv : v ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
            (basis_g_dz L)) :
    ∃ z ∈ L, v = fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => z := by
  rcases (mem_periodLatticeImage_iff _ _ _).mp hv with ⟨γ, hγ⟩
  -- v = periodVector data basis_g_dz γ = fun j => PeriodPairing data γ (basis_g_dz L j)
  --   = fun _ => complexPeriod γ (dz L)
  refine ⟨complexPeriod γ (dz L), complexPeriod_mem_L_of_cycle L γ, ?_⟩
  rw [← hγ]
  funext j
  show PeriodPairing (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) γ (basis_g_dz L j)
    = complexPeriod γ (dz L)
  rw [basis_g_dz_const, PeriodPairing_ofSmoothCycle]

/-! ## The full characterization -/

/-- **Full characterization of `periodLatticeImage` on `T_L`.**

`v ∈ periodLatticeImage data basis_g_dz ↔ ∃ z ∈ L, v = fun _ => z`. -/
theorem mem_periodLatticeImage_complexTorus_iff
    (v : Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) :
    v ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
          (basis_g_dz L)
      ↔ ∃ z ∈ L, v = fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => z := by
  refine ⟨exists_const_of_mem_periodLatticeImage L, ?_⟩
  rintro ⟨z, hz, rfl⟩
  exact const_mem_periodLatticeImage_of_mem_L L z hz

end ComplexTorus

end JacobianChallenge

end
