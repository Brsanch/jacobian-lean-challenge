/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import JacobianChallenge.Manifold.ComplexTorusGlobalSimplexLiftFTC
import JacobianChallenge.Manifold.ComplexTorusPathConnected
import JacobianChallenge.Manifold.ComplexTorusRiemannBilinear
import JacobianChallenge.Manifold.ComplexTorusZBasisExistence
import JacobianChallenge.Manifold.SmoothSymplecticBasisReindex
import JacobianChallenge.Manifold.GenericGenusPeriodLatticeInputsFromBasedLoopHomology

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # `Nonempty (PeriodLatticeSymplecticBundle … (ℂ ⧸ L))` unconditional

Assembles the seven atomic torus closures from prior chips into a
`PeriodLatticeSymplecticBundle` witness on the complex torus, via
`nonempty_periodLatticeSymplecticBundle_ofBasedLoopHomology`. Transports
along `genus_eq_one` use `SmoothSymplecticBasis.reindex` (from
`SmoothSymplecticBasisReindex.lean`) and `Basis.reindex`. The
ℝ-linear-independence transport from dim 1 (`riemannBilinear_torus`)
to dim `genus (ℂ⧸L)` factors through `LinearEquiv.piCongrLeft'`
applied to the inner index family.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## ℝ-linear independence of the lattice basis -/

/-- **The two coercions of a `Fin 2` ℤ-basis of `L` are ℝ-linearly
independent in `ℂ`.** Follows from `Basis.ofZLatticeBasis ℝ L
(basisFin2OfL L)` being a `Basis (Fin 2) ℝ ℂ`. -/
theorem basisFin2OfL_realLinearIndependent :
    LinearIndependent ℝ
      (![((basisFin2OfL L 0 : L) : ℂ), ((basisFin2OfL L 1 : L) : ℂ)] :
        Fin 2 → ℂ) := by
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let b_R : Basis (Fin 2) ℝ ℂ := (basisFin2OfL L).ofZLatticeBasis ℝ L
  have h_eq : ∀ i, b_R i = ((basisFin2OfL L i : L) : ℂ) := fun i =>
    (basisFin2OfL L).ofZLatticeBasis_apply ℝ L i
  have h_funext :
      (![((basisFin2OfL L 0 : L) : ℂ), ((basisFin2OfL L 1 : L) : ℂ)] :
        Fin 2 → ℂ) = b_R := by
    funext i
    fin_cases i
    · simp [h_eq 0]
    · simp [h_eq 1]
  rw [h_funext]
  exact b_R.linearIndependent

/-! ## The canonical `Fin 1` Hodge basis and its dim-`genus` lift -/

/-- **`basis_one_dz L`** — the canonical `Basis (Fin 1) ℂ
(HolomorphicOneForm (ℂ⧸L))` with `basis_one_dz L 0 = dz L`. -/
noncomputable def basis_one_dz : Basis (Fin 1) ℂ (HolomorphicOneForm (ℂ ⧸ L)) :=
  FiniteDimensional.basisSingleton (Fin 1) (genus_eq_one L) (dz L)
    (dz_ne_zero L)

@[simp] lemma basis_one_dz_apply :
    basis_one_dz L 0 = dz L :=
  FiniteDimensional.basisSingleton_apply (Fin 1) (genus_eq_one L) (dz L)
    (dz_ne_zero L) 0

/-- **`basis_g_dz L`** — the dim-`genus (ℂ⧸L)` basis obtained by
reindexing `basis_one_dz L` along `(genus_eq_one L).symm`. -/
noncomputable def basis_g_dz :
    Basis (Fin (JacobianChallenge.genus (ℂ ⧸ L))) ℂ
      (HolomorphicOneForm (ℂ ⧸ L)) :=
  (basis_one_dz L).reindex (finCongr (genus_eq_one L).symm)

lemma basis_g_dz_apply (j : Fin (JacobianChallenge.genus (ℂ ⧸ L))) :
    basis_g_dz L j = basis_one_dz L (finCongr (genus_eq_one L) j) := by
  unfold basis_g_dz
  rw [Basis.reindex_apply]
  congr 1

/-! ## The Riemann-bilinear transport, dim 1 → dim `genus (ℂ⧸L)` -/

/-- **Riemann bilinear at dim `genus (ℂ⧸L)`** — period vectors of the
reindexed symplectic basis against `basis_g_dz` are ℝ-linearly
independent. The proof transports `riemannBilinear_torus` (dim 1) along
`genus_eq_one.symm` via:

* `finCongr` on the outer `Fin (2 * genus (ℂ⧸L)) ≃ Fin (2 * 1)` index;
* `LinearEquiv.piCongrLeft'` on the inner `Fin (genus (ℂ⧸L)) ≃ Fin 1`
  index (an ℝ-linear isomorphism between the two ℂ-valued function
  spaces). -/
theorem riemannBilinear_transport
    (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L)
    (h_indep : LinearIndependent ℝ ![lam₁, lam₂]) :
    LinearIndependent ℝ
      (fun i : Fin (2 * JacobianChallenge.genus (ℂ ⧸ L)) =>
        periodVector (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
          (basis_g_dz L)
          (((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).reindex
            (genus_eq_one L)).cycleGens i)) := by
  have hg : JacobianChallenge.genus (ℂ ⧸ L) = 1 := genus_eq_one L
  have h2g : 2 * JacobianChallenge.genus (ℂ ⧸ L) = 2 * 1 := by rw [hg]
  -- Outer index equiv.
  let e_outer : Fin (2 * JacobianChallenge.genus (ℂ ⧸ L)) ≃ Fin (2 * 1) :=
    finCongr h2g
  -- Inner ℝ-linear iso `(Fin (genus T_L) → ℂ) ≃ₗ[ℝ] (Fin 1 → ℂ)`.
  let e_inner : (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) ≃ₗ[ℝ]
      (Fin 1 → ℂ) :=
    LinearEquiv.piCongrLeft' ℝ
      (fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => ℂ)
      (finCongr hg)
  -- After applying `e_inner.symm.toLinearMap` to a `Fin 1 → ℂ` family,
  -- LinearIndependent transports.
  -- Step 1: rewrite the goal so the outer index goes through `e_outer`.
  rw [show (fun i : Fin (2 * JacobianChallenge.genus (ℂ ⧸ L)) =>
        periodVector (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
          (basis_g_dz L)
          (((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).reindex
            (genus_eq_one L)).cycleGens i))
      = (fun i : Fin (2 * 1) =>
          periodVector (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
            (basis_g_dz L)
            ((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens i))
          ∘ e_outer from ?_]
  · rw [linearIndependent_equiv]
    -- Now goal: LinearIndependent ℝ
    --   (fun i : Fin (2 * 1) =>
    --     periodVector data (basis_g_dz L) (sb_one.cycleGens i))
    -- Step 2: factor periodVector through e_inner.symm.toLinearMap.
    have h_inner :
        (fun i : Fin (2 * 1) =>
            periodVector (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
              (basis_g_dz L)
              ((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens i))
          = e_inner.symm.toLinearMap ∘
            (fun i : Fin (2 * 1) =>
              fun j : Fin 1 =>
                PeriodPairing (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
                  ((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens i)
                  (basis_one_dz L j)) := by
      funext i j
      -- LHS j : periodVector data basis_g (sb_one.cycleGens i) j
      --      = PeriodPairing data (sb_one.cycleGens i) (basis_g j)
      --      = PeriodPairing data (sb_one.cycleGens i) (basis_one (finCongr hg j))
      -- RHS j : e_inner.symm (fun j' : Fin 1 => …) j
      --      = (fun j' : Fin 1 => …) (e_inner.symm.symm-side index of j)
      show PeriodPairing (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        ((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens i)
        (basis_g_dz L j) = _
      rw [basis_g_dz_apply]
      -- The RHS is e_inner.symm applied to (fun j' : Fin 1 => PeriodPairing ... (basis_one_dz L j')) at j.
      -- e_inner = piCongrLeft' ℝ (constant ℂ) (finCongr hg : Fin (genus T_L) ≃ Fin 1)
      -- e_inner f i' = f (e.symm i') = f ((finCongr hg).symm i') = f (finCongr hg.symm i')
      -- e_inner.symm g j = ???. The inverse: piCongrLeft'.symm (g)(j) = g (e j).
      -- So e_inner.symm g j = g (finCongr hg j).
      -- Then e_inner.symm (fun j' => PeriodPairing ... (basis_one j')) j
      --    = PeriodPairing ... (basis_one (finCongr hg j))
      change _ =
        (LinearEquiv.piCongrLeft' ℝ
          (fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => ℂ)
          (finCongr hg)).symm
            (fun j' : Fin 1 =>
              PeriodPairing (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
                ((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens i)
                (basis_one_dz L j')) j
      simp [LinearEquiv.piCongrLeft'_symm_apply]
    rw [h_inner]
    -- Now we want LinearIndependent ℝ (e_inner.symm.toLinearMap ∘ f).
    -- Use LinearIndependent.map' from h_rb (the dim-1 LinearIndependent).
    refine LinearIndependent.map' ?_ _ ?_
    · -- Dim-1 LinearIndependent.
      have h_basis_zero : basis_one_dz L 0 = dz L := basis_one_dz_apply L
      have h_rb :=
        riemannBilinear_torus L lam₁ lam₂ hlam₁ hlam₂ (basis_one_dz L)
          h_basis_zero h_indep
      -- h_rb is on Fin 2; reindex to Fin (2*1) via finCongr (decide : 2*1 = 2).
      rw [show (fun i : Fin (2 * 1) =>
            fun j : Fin 1 =>
              PeriodPairing (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
                ((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens i)
                (basis_one_dz L j))
          = (fun i : Fin 2 =>
              fun j : Fin 1 =>
                PeriodPairing (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
                  ((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens
                    (Fin.cast (by decide) i : Fin (2 * 1)))
                  (basis_one_dz L j))
              ∘ (finCongr (by decide : (2 * 1 : ℕ) = 2)) from ?_]
      · rw [linearIndependent_equiv]; exact h_rb
      · funext i j; rfl
    · exact LinearEquiv.ker _
  · funext i
    show periodVector (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L)
        (((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).reindex
          (genus_eq_one L)).cycleGens i)
      = periodVector (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
          (basis_g_dz L)
          ((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens (e_outer i))
    rfl

/-! ## Headline: unconditional `Nonempty (PLSB …)` on `T_L` -/

/-- **`Nonempty (PeriodLatticeSymplecticBundle … T_L) basis_g_dz`,
unconditional.**

Composes seven atomic torus closures via
`nonempty_periodLatticeSymplecticBundle_ofBasedLoopHomology`. -/
theorem nonempty_periodLatticeSymplecticBundle_complexTorus :
    Nonempty
      (PeriodLatticeSymplecticBundle
        (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L)) := by
  -- Extract the lam₁/lam₂ pair + Hurewicz hypothesis unconditionally.
  let b₂ := basisFin2OfL L
  set lam₁ : ℂ := ((b₂ 0 : L) : ℂ) with hlam₁_def
  set lam₂ : ℂ := ((b₂ 1 : L) : ℂ) with hlam₂_def
  have hlam₁ : lam₁ ∈ L := (b₂ 0).property
  have hlam₂ : lam₂ ∈ L := (b₂ 1).property
  have h_indep : LinearIndependent ℝ ![lam₁, lam₂] :=
    basisFin2OfL_realLinearIndependent L
  have hSH : SmoothHurewiczHypothesisTorus L lam₁ lam₂ hlam₁ hlam₂ :=
    smoothHurewiczHypothesisTorus_holds_of_basis _ _ _ _
      (basisFin2OfL_isZBasisOfL)
  -- The dim-1 symplectic basis and its reindex up to dim `genus T_L`.
  let sb_one : SmoothSymplecticBasis 𝓘(ℝ, ℂ) (ℂ ⧸ L) 0 1 :=
    symplecticBasis L lam₁ lam₂ hlam₁ hlam₂
  let sb_g : SmoothSymplecticBasis 𝓘(ℝ, ℂ) (ℂ ⧸ L) 0
      (JacobianChallenge.genus (ℂ ⧸ L)) :=
    sb_one.reindex (genus_eq_one L)
  -- Transport SmoothHurewicz across the reindex.
  have hSH_g : SmoothHurewiczHypothesis sb_g :=
    SmoothHurewiczHypothesis.reindex sb_one (genus_eq_one L) hSH
  -- Apply the BasedLoopHomology headline.
  exact nonempty_periodLatticeSymplecticBundle_ofBasedLoopHomology
    (basis := basis_g_dz L)
    (cycleGens := sb_g.cycleGens)
    (riemannBilinear :=
      riemannBilinear_transport L lam₁ lam₂ hlam₁ hlam₂ h_indep)
    (holomorphicCanonicalClosed := holomorphicComponentsCanonicalClosed_holds L)
    (p₀ := (0 : ℂ ⧸ L))
    (α := α L)
    (h_α_src := α_src L)
    (h_α_tgt := α_tgt L)
    (basedLoopHomology :=
      SmoothHurewiczHypothesis.basedLoopHomology_of_smoothHurewicz hSH_g)

end ComplexTorus

end JacobianChallenge

end
