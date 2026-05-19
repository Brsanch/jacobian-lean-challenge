/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiPointSymp
import JacobianChallenge.Manifold.C3FullInputExtSymp
import JacobianChallenge.Manifold.ComplexTorusPathConnected
import JacobianChallenge.Manifold.PeriodLatticeSymplecticBundleComplexTorus

set_option linter.unusedSectionVars false

/-! # `Nonempty (AbelJacobiInputSymp …)` on the complex torus

`AbelJacobiInputSymp α h` packages:
* a chosen base point of `X`;
* a smooth path family `pathFromBase : X → SmoothPath 𝓘(ℝ, ℂ) X` with
  `src = basePoint` and `tgt = Q`.

For the complex torus `T_L = ℂ ⧸ L`, the basepoint-0 smooth-path family
`α L : T_L → SmoothPath` (constructed in
`ComplexTorusPathConnected.lean`) directly fills these slots with
`(α L Q).src = 0` and `(α L Q).tgt = Q`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **`AbelJacobiInputSymp` on `ℂ ⧸ L`, parameterised by any basis +
PLSB.** Uses `α L` (basepoint-0 smooth-path family) as
`pathFromBase`. -/
noncomputable def abelJacobiInputSymp
    (β : Basis (Fin (JacobianChallenge.genus (ℂ ⧸ L))) ℂ
      (HolomorphicOneForm (ℂ ⧸ L)))
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) β) :
    AbelJacobiInputSymp β h where
  basePoint := (0 : ℂ ⧸ L)
  pathFromBase := α L
  src_eq := α_src L
  tgt_eq := α_tgt L

/-- **`Nonempty (AbelJacobiInputSymp …)` on the torus, unconditional.** -/
theorem nonempty_abelJacobiInputSymp_complexTorus
    (β : Basis (Fin (JacobianChallenge.genus (ℂ ⧸ L))) ℂ
      (HolomorphicOneForm (ℂ ⧸ L)))
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) β) :
    Nonempty (AbelJacobiInputSymp β h) :=
  ⟨abelJacobiInputSymp L β h⟩

/-! ## Hypothesis-driven `Nonempty (C3FullInputSymp T_L)` and
`Nonempty (C3FullInputExtSymp T_L)`

The two remaining classical inputs at genus ≥ 1 (Abel's theorem on
elliptic curves + Jacobi inversion) are not yet in tree. We surface
constructors taking the four open classical hypotheses
(`AbelHypothesis` / `JacobiInversion` / `AbelJacobiSmoothnessSymp` /
`AbelJacobiInjectiveSymp`) as named inputs, packaging the seven prior
torus closures + `abelJacobiInputSymp` into a `C3FullInputExtSymp`
bundle.

Downstream chips closing Abel + Jacobi + smoothness + injectivity on
`T_L` instantiate these constructors to land
`Nonempty (C3FullInputExtSymp (ℂ ⧸ L))` unconditional. -/

/-- **The canonical `AbelJacobiInputSymp` on `T_L`** at the canonical
basis `basis_g_dz L` and PLSB `periodLatticeSymplecticBundle_complexTorus L`. -/
noncomputable def canonicalAbelJacobiInputSymp
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L)) :
    AbelJacobiInputSymp (basis_g_dz L) h :=
  abelJacobiInputSymp L (basis_g_dz L) h

/-- **`Nonempty (C3FullInputSymp (ℂ ⧸ L))` from Abel + Jacobi
hypotheses.** Wraps the canonical basis + PLSB + AJ-input chain. -/
theorem nonempty_C3FullInputSymp_complexTorus
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L))
    (hAbel : AbelJacobiInputSymp.AbelHypothesis (canonicalAbelJacobiInputSymp L h))
    (hJacobi : AbelJacobiInputSymp.JacobiInversion
      (canonicalAbelJacobiInputSymp L h) hAbel) :
    Nonempty (JacobianChallenge.C3FullInputSymp (ℂ ⧸ L)) :=
  ⟨{ basis := basis_g_dz L
     discreteness := h
     ajInput := canonicalAbelJacobiInputSymp L h
     abel := hAbel
     jacobi := hJacobi }⟩

/-- **`Nonempty (C3FullInputExtSymp (ℂ ⧸ L))` from Abel + Jacobi +
smoothness + injectivity hypotheses.** -/
theorem nonempty_C3FullInputExtSymp_complexTorus
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L))
    (hAbel : AbelJacobiInputSymp.AbelHypothesis (canonicalAbelJacobiInputSymp L h))
    (hJacobi : AbelJacobiInputSymp.JacobiInversion
      (canonicalAbelJacobiInputSymp L h) hAbel)
    (hSmooth :
      haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle h
      haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle h
      haveI : DiscreteTopology
          (PeriodLatticeOfRankTwoG.ofSymplectic
            (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
            (basis_g_dz L) h).lattice.toIntSubmodule :=
        PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle h
      haveI : IsZLattice ℝ
          (PeriodLatticeOfRankTwoG.ofSymplectic
            (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
            (basis_g_dz L) h).lattice.toIntSubmodule :=
        PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle h
      AbelJacobiSmoothnessSymp (canonicalAbelJacobiInputSymp L h))
    (hInj : AbelJacobiInjectiveSymp (canonicalAbelJacobiInputSymp L h)) :
    Nonempty (C3FullInputExtSymp (ℂ ⧸ L)) :=
  ⟨{ base :=
      { basis := basis_g_dz L
        discreteness := h
        ajInput := canonicalAbelJacobiInputSymp L h
        abel := hAbel
        jacobi := hJacobi }
     smoothness := hSmooth
     injective := hInj }⟩

end ComplexTorus

end JacobianChallenge

end
