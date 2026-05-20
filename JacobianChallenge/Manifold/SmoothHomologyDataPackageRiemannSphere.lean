/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothHomologyDataPackage
import JacobianChallenge.Manifold.SmoothHurewiczHypothesisRiemannSphere
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option linter.unusedSectionVars false

/-! # `SmoothHomologyDataPackage` on `RiemannSphere`, unconditional

At genus 0 on `RiemannSphere`:

* The `2g`-tuple of basis loops is **empty** (`Fin (2 * 0) = Fin 0`),
  so the `SmoothSymplecticBasis 𝓘(ℝ, ℂ) RS p₀ 0` data uses
  `Fin.elim0`.
* `SmoothHurewiczHypothesis` reduces to
  `BasedSmoothLoopsBoundHypothesis`, unconditional on `RS` via
  `smoothHurewiczHypothesis_RiemannSphere_holds`.
* The bilinear-non-degeneracy on the empty tuple is `linearIndependent_empty_type`.

This file ships the unconditional discharge of
`SmoothHomologyDataPackage basis_ω` on `X = RiemannSphere`, validating
the bundled-three-named-atoms structure end-to-end at genus 0.

## What this file ships

* `emptySymplecticBasis_RS` — typed empty symplectic basis at
  `JacobianChallenge.genus RiemannSphere` (not the literal `0`).
* `smoothHomologyDataPackage_RiemannSphere p₀ basis_ω` — concrete
  unconditional `SmoothHomologyDataPackage` on `RS`.
* `nonempty_smoothHomologyDataPackage_RiemannSphere` — `Nonempty`
  packaging (with `p₀` chosen via `Classical.arbitrary RS`).
* `nonempty_periodLatticeSymplecticBundle_RiemannSphere_of_package`
  — composition through to `Nonempty
  (PeriodLatticeSymplecticBundle ... basis_ω)`. Confirms that the
  single-input headline composite reproduces the known RS closure.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Module Submodule

namespace JacobianChallenge

namespace RiemannSphere

/-- **An `IsEmpty (Fin (2 * genus RS))` instance**, derived from the
unconditional `genus_RiemannSphere_eq_zero`. -/
private instance isEmpty_fin_two_genus_RS :
    IsEmpty (Fin (2 * JacobianChallenge.genus RiemannSphere)) := by
  rw [genus_RiemannSphere_eq_zero, Nat.mul_zero]; infer_instance

/-- **The canonical empty symplectic basis at `genus RiemannSphere`.**
Companion to `RiemannSphere.emptySymplecticBasis` which is typed at the
literal `0`; this version is typed at `JacobianChallenge.genus
RiemannSphere`, matching the indexing used by `SmoothHomologyDataPackage`. -/
noncomputable def emptySymplecticBasis_RS (p₀ : RiemannSphere) :
    SmoothSymplecticBasis 𝓘(ℝ, ℂ) RiemannSphere p₀
      (JacobianChallenge.genus RiemannSphere) where
  basis := IsEmpty.elim isEmpty_fin_two_genus_RS
  basis_src := IsEmpty.elim isEmpty_fin_two_genus_RS
  basis_tgt := IsEmpty.elim isEmpty_fin_two_genus_RS

/-- **Smooth-Hurewicz on the empty basis at `genus RiemannSphere`.**
Companion to `smoothHurewiczHypothesis_RiemannSphere_holds` (typed at
the literal `0`), but at the `genus RiemannSphere`-indexed empty basis. -/
theorem smoothHurewiczHypothesis_emptySymplecticBasis_RS
    (p₀ : RiemannSphere) :
    SmoothHurewiczHypothesis (emptySymplecticBasis_RS p₀) := by
  intro γ h_src h_tgt
  refine ⟨IsEmpty.elim isEmpty_fin_two_genus_RS, ?_⟩
  have h_sum_zero :
      (∑ i : Fin (2 * JacobianChallenge.genus RiemannSphere),
        (IsEmpty.elim isEmpty_fin_two_genus_RS i : ℤ) •
          (emptySymplecticBasis_RS p₀).cycleGens i)
        = (0 : SmoothCycle 𝓘(ℝ, ℂ) RiemannSphere) :=
    Finset.sum_of_isEmpty _
  rw [h_sum_zero, sub_zero]
  exact basedSmoothLoopsBoundHypothesis_RS_holds p₀ γ h_src h_tgt

/-- **Unconditional `SmoothHomologyDataPackage basis_ω` on `RS`.**

At genus 0 every field is discharged trivially:
* `symplecticBasis` — `emptySymplecticBasis_RS p₀`.
* `hurewicz` — `smoothHurewiczHypothesis_emptySymplecticBasis_RS p₀`.
* `bilinear` — `linearIndependent_empty_type` on the empty index set. -/
noncomputable def smoothHomologyDataPackage_RiemannSphere
    (p₀ : RiemannSphere)
    (basis_ω : Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
      (HolomorphicOneForm RiemannSphere)) :
    SmoothHomologyDataPackage (X := RiemannSphere) basis_ω where
  basePoint := p₀
  symplecticBasis := emptySymplecticBasis_RS p₀
  hurewicz := smoothHurewiczHypothesis_emptySymplecticBasis_RS p₀
  bilinear := linearIndependent_empty_type

/-- **`Nonempty` packaging of the unconditional `SmoothHomologyDataPackage`
on `RS`.** Base point chosen via `Classical.arbitrary`. -/
theorem nonempty_smoothHomologyDataPackage_RiemannSphere
    (basis_ω : Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
      (HolomorphicOneForm RiemannSphere)) :
    Nonempty (SmoothHomologyDataPackage (X := RiemannSphere) basis_ω) :=
  ⟨smoothHomologyDataPackage_RiemannSphere (Classical.arbitrary _) basis_ω⟩

/-- **End-to-end validation: `Nonempty (PeriodLatticeSymplecticBundle ...)`
on `RS` via the single-input package.**

Confirms the headline composite `nonempty_periodLatticeSymplecticBundle_
of_smoothHomologyDataPackage` reproduces the known unconditional RS
closure (cf. `nonempty_genericGenusPeriodLatticeInputs_RiemannSphere`). -/
theorem nonempty_periodLatticeSymplecticBundle_RiemannSphere_of_package
    (basis_ω : Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
      (HolomorphicOneForm RiemannSphere)) :
    Nonempty
      (PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle RiemannSphere)
        basis_ω) :=
  nonempty_periodLatticeSymplecticBundle_of_nonempty_smoothHomologyDataPackage
    (nonempty_smoothHomologyDataPackage_RiemannSphere basis_ω)

end RiemannSphere

end JacobianChallenge

end
