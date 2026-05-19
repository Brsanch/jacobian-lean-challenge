/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodLatticeImageComplexTorusReverse

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # `AnalyticJacobianSymp ≃+ T_L` AddEquiv on the complex torus

The canonical additive iso between the analytic Jacobian and `T_L = ℂ ⧸ L`,
derived from:

* `Unique (Fin (genus (ℂ⧸L)))` (from `genus_eq_one`).
* `LinearEquiv.funUnique` giving `(Fin g → ℂ) ≃ₗ[ℝ] ℂ`.
* `periodLatticeImage ↔ L` under this iso (from the lattice
  characterization `mem_periodLatticeImage_complexTorus_iff`).
* `QuotientAddGroup.congr` lifting the iso to the quotients.

Headline lemmas:
* `analyticJacobianSympEquiv_complexTorus L h`: the AddEquiv.
* `analyticJacobianSympEquiv_complexTorus_abelJacobiPoint`: the AJ
  point map becomes the identity under this iso.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## `Unique (Fin (genus (ℂ⧸L)))` -/

/-- **`Fin (genus (ℂ⧸L))` is `Unique`** (transported from `Fin 1`
along `genus_eq_one`). -/
@[reducible] noncomputable def uniqueFinGenus :
    Unique (Fin (JacobianChallenge.genus (ℂ ⧸ L))) :=
  (genus_eq_one L).symm ▸ (Fin.instUnique)

/-! ## The underlying `(Fin g → ℂ) ≃+ ℂ` -/

/-- **`(Fin (genus (ℂ⧸L)) → ℂ) ≃+ ℂ`** via `LinearEquiv.funUnique`. -/
noncomputable def funUniqueAddEquivComplexTorus :
    (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) ≃+ ℂ :=
  letI : Unique (Fin (JacobianChallenge.genus (ℂ ⧸ L))) := uniqueFinGenus L
  (LinearEquiv.funUnique (Fin (JacobianChallenge.genus (ℂ ⧸ L))) ℝ ℂ).toAddEquiv

/-- `funUniqueAddEquivComplexTorus` maps `f` to `f default`. -/
lemma funUniqueAddEquivComplexTorus_apply
    (f : Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) :
    letI : Unique (Fin (JacobianChallenge.genus (ℂ ⧸ L))) := uniqueFinGenus L
    funUniqueAddEquivComplexTorus L f = f default :=
  rfl

/-- The inverse maps `z` to the constant function `fun _ => z`. -/
lemma funUniqueAddEquivComplexTorus_symm_apply (z : ℂ) :
    (funUniqueAddEquivComplexTorus L).symm z
      = (fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => z) :=
  rfl

/-! ## The image of `periodLatticeImage` under the equiv is `L` -/

/-- **The image of `periodLatticeImage` under `funUniqueAddEquivComplexTorus`
equals `L.toAddSubgroup`.**

Forward: `f ∈ periodLatticeImage ↔ ∃ z ∈ L, f = fun _ => z`, then
`eval default f = z ∈ L`. Reverse: any `z ∈ L` is `(fun _ => z) default`
where `fun _ => z ∈ periodLatticeImage`. -/
theorem map_periodLatticeImage_eq_L :
    AddSubgroup.map (funUniqueAddEquivComplexTorus L : _ →+ ℂ)
        (periodLatticeImage (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
          (basis_g_dz L))
      = L.toAddSubgroup := by
  ext z
  constructor
  · rintro ⟨v, hv_mem, hv_eq⟩
    -- v ∈ periodLatticeImage, image is z = v default.
    rw [Submodule.mem_toAddSubgroup]
    rcases (mem_periodLatticeImage_complexTorus_iff L v).mp hv_mem with ⟨w, hwL, rfl⟩
    -- v = fun _ => w, image of fun _ => w is w (the value at default).
    show z ∈ L
    have : z = w := by
      rw [← hv_eq]
      rfl
    rw [this]
    exact hwL
  · intro hz
    rw [Submodule.mem_toAddSubgroup] at hz
    refine ⟨fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => z, ?_, ?_⟩
    · exact const_mem_periodLatticeImage_of_mem_L L z hz
    · rfl

/-! ## The headline iso `AnalyticJacobianSymp ≃+ T_L` -/

/-- **`AnalyticJacobianSymp ≃+ ℂ ⧸ L`** via `QuotientAddGroup.congr`. -/
noncomputable def analyticJacobianSympEquiv_complexTorus
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L)) :
    AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L) h
      ≃+ (ℂ ⧸ L) := by
  -- Bridge: AnalyticJacobianSymp = (Fin g → ℂ) ⧸ (ofSymplectic ...).lattice
  --                              = (Fin g → ℂ) ⧸ periodLatticeImage.
  -- After congr through funUniqueAddEquivComplexTorus,
  --       this becomes ℂ ⧸ L.toAddSubgroup = ℂ ⧸ L.
  refine (AddEquiv.refl _).trans ?_
  -- Apply QuotientAddGroup.congr with the AddEquiv and the subgroup-image equality.
  have h_lattice :
      (PeriodLatticeOfRankTwoG.ofSymplectic
        (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L) h).lattice
        = periodLatticeImage (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
            (basis_g_dz L) := rfl
  -- Reduce the source quotient.
  refine (QuotientAddGroup.quotientAddEquivOfEq h_lattice).trans ?_
  -- Now quotient is by periodLatticeImage; transport via funUniqueAddEquivComplexTorus.
  exact QuotientAddGroup.congr _ L.toAddSubgroup
    (funUniqueAddEquivComplexTorus L)
    (map_periodLatticeImage_eq_L L)

/-! ## The AJ point map becomes the identity under the iso -/

/-- **Under the iso, the AJ point map is the identity on T_L.**
`analyticJacobianSympEquiv_complexTorus (abelJacobiPoint Q) = Q`. -/
theorem analyticJacobianSympEquiv_complexTorus_abelJacobiPoint
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L))
    (Q : ℂ ⧸ L) :
    analyticJacobianSympEquiv_complexTorus L h
        ((canonicalAbelJacobiInputSymp L h).abelJacobiPoint Q)
      = Q := by
  rw [canonicalAbelJacobiInputSymp_abelJacobiPoint]
  -- abelJacobiPoint Q = QuotientAddGroup.mk (fun _ => Q.out).
  -- Under the iso, this should become QuotientAddGroup.mk Q.out = Q.
  show (Quotient.mk'' Q.out : ℂ ⧸ L) = Q
  exact Quotient.out_eq Q

end ComplexTorus

end JacobianChallenge

end
