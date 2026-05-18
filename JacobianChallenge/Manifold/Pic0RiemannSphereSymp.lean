/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.JacobianAnalyticChoiceSymp
import JacobianChallenge.Manifold.AbelHypothesisGenusZero
import JacobianChallenge.Manifold.JacobiInversionGenusZero
import JacobianChallenge.Manifold.AbelJacobiEquivRiemannSphere
import JacobianChallenge.Manifold.Pic0RiemannSphereSubsingleton

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Symplectic genus-0 / RiemannSphere discharges

Migration target file: lifts the legacy genus-0 + RS chain
(`Subsingleton.analyticJacobian_of_genus_zero`,
`AbelJacobiInput.abelHypothesis_of_genus_zero`,
`AbelJacobiInput.jacobiInversion_of_genus_zero_and_subsingleton_pic0`,
`AbelJacobiInput.abelJacobiEquiv_of_genus_zero`,
`AbelJacobiInput.abelJacobiEquiv_of_RiemannSphere`,
`AbelJacobiInput.abelJacobiEquiv_of_RiemannSphere_unconditional`) to
the symplectic bundle.

The symplectic versions make `C3FullInputExtSymp X` /
`JacobianAnalyticChoiceSymp X` inhabitable at genus 0 and unconditional
on `RiemannSphere` — the migration target for downstream code that
previously routed through the legacy `PeriodLatticeDiscretenessBundle`
(whose `h1Basis : Basis (Fin 2g) ℤ data.H1` is dead code at every
genus for `data = ofSmoothCycle X`).

The proofs reuse the legacy ones via per-point / per-divisor `rfl`
between `AnalyticJacobian` and `AnalyticJacobianSymp` (both are
`(Fin g → ℂ) ⧸ (periodLatticeImage data α).toIntSubmodule`).

## What ships

* `Subsingleton.analyticJacobianSymp_of_genus_zero`.
* `AbelJacobiInputSymp.abelHypothesis_of_genus_zero`.
* `AbelJacobiInputSymp.jacobiInversion_of_genus_zero_and_subsingleton_pic0`.
* `AbelJacobiInputSymp.abelJacobiEquiv_of_genus_zero`.
* `AbelJacobiInputSymp.abelJacobiEquiv_of_RiemannSphere`.
* `AbelJacobiInputSymp.abelJacobiEquiv_of_RiemannSphere_unconditional`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Submodule Module

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-! ## Subsingleton of `AnalyticJacobianSymp` at genus 0 -/

/-- **`AnalyticJacobianSymp` is subsingleton at genus 0.** Mirror of
`Subsingleton.analyticJacobian_of_genus_zero` for the symplectic bundle.
Same proof — the underlying type
`(Fin (genus X) → ℂ) ⧸ (periodLatticeImage …).toIntSubmodule` is
identical in both cases. -/
theorem Subsingleton.analyticJacobianSymp_of_genus_zero
    {data : PeriodPairingData X}
    {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
    {h : PeriodLatticeSymplecticBundle data α}
    (hgenus : JacobianChallenge.genus X = 0) :
    Subsingleton (AnalyticJacobianSymp data α h) := by
  unfold AnalyticJacobianSymp JacobianOfLattice
  haveI : Subsingleton (Fin (JacobianChallenge.genus X) → ℂ) :=
    subsingleton_pi_fin_genus_zero hgenus
  refine ⟨fun x y => ?_⟩
  induction x using QuotientAddGroup.induction_on with
  | H xRep =>
    induction y using QuotientAddGroup.induction_on with
    | H yRep =>
      have heq : xRep = yRep := Subsingleton.elim xRep yRep
      rw [heq]

/-! ## Genus-zero discharges (symplectic) -/

namespace AbelJacobiInputSymp

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) α}

/-- **Genus-zero discharge of `AbelHypothesis` (symplectic).** Mirror
of `AbelJacobiInput.abelHypothesis_of_genus_zero`. -/
theorem abelHypothesis_of_genus_zero
    (B : AbelJacobiInputSymp α h)
    (hgenus : JacobianChallenge.genus X = 0) :
    AbelHypothesis B := by
  intro D _hPrinc
  haveI := Subsingleton.analyticJacobianSymp_of_genus_zero
    (data := PeriodPairingData.ofSmoothCycle X) (α := α) (h := h) hgenus
  exact Subsingleton.elim _ _

/-- **Genus-zero discharge of `JacobiInversion` (symplectic).** Mirror
of `AbelJacobiInput.jacobiInversion_of_genus_zero_and_subsingleton_pic0`. -/
theorem jacobiInversion_of_genus_zero_and_subsingleton_pic0
    (B : AbelJacobiInputSymp α h)
    (hAbel : AbelHypothesis B)
    (hgenus : JacobianChallenge.genus X = 0)
    (hPic0 : Subsingleton (Pic0 X)) :
    JacobiInversion B hAbel := by
  haveI : Subsingleton
      (AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle X) α h) :=
    Subsingleton.analyticJacobianSymp_of_genus_zero
      (data := PeriodPairingData.ofSmoothCycle X) (α := α) (h := h) hgenus
  refine ⟨?_, ?_⟩
  · intro a b _
    exact hPic0.elim a b
  · intro v
    refine ⟨0, ?_⟩
    exact Subsingleton.elim _ _

/-- **Genus-zero composite — closed `abelJacobiEquiv` (symplectic).**
Mirror of `AbelJacobiInput.abelJacobiEquiv_of_genus_zero`. -/
noncomputable def abelJacobiEquiv_of_genus_zero
    (B : AbelJacobiInputSymp α h)
    (hgenus : JacobianChallenge.genus X = 0)
    (hPic0 : Subsingleton (Pic0 X)) :
    Pic0 X ≃+ AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle X) α h :=
  B.abelJacobiEquiv
    (B.abelHypothesis_of_genus_zero hgenus)
    (jacobiInversion_of_genus_zero_and_subsingleton_pic0 B
      (B.abelHypothesis_of_genus_zero hgenus) hgenus hPic0)

end AbelJacobiInputSymp

/-! ## RiemannSphere discharges (symplectic) -/

namespace AbelJacobiInputSymp

variable {α : Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
          (HolomorphicOneForm RiemannSphere)}
  {h : PeriodLatticeSymplecticBundle
    (PeriodPairingData.ofSmoothCycle RiemannSphere) α}

/-- **Abel-Jacobi isomorphism on the Riemann sphere (symplectic).**
Mirror of `AbelJacobiInput.abelJacobiEquiv_of_RiemannSphere`. -/
noncomputable def abelJacobiEquiv_of_RiemannSphere
    (B : AbelJacobiInputSymp α h)
    (hPic0 : Subsingleton (Pic0 RiemannSphere)) :
    Pic0 RiemannSphere ≃+
      AnalyticJacobianSymp
        (PeriodPairingData.ofSmoothCycle RiemannSphere) α h :=
  B.abelJacobiEquiv_of_genus_zero
    JacobianChallenge.RiemannSphere.genus_RiemannSphere_eq_zero hPic0

/-- **Abel-Jacobi iso on RS, unconditional (symplectic).** Mirror of
`AbelJacobiInput.abelJacobiEquiv_of_RiemannSphere_unconditional`. -/
noncomputable def abelJacobiEquiv_of_RiemannSphere_unconditional
    (B : AbelJacobiInputSymp α h) :
    Pic0 RiemannSphere ≃+
      AnalyticJacobianSymp
        (PeriodPairingData.ofSmoothCycle RiemannSphere) α h :=
  B.abelJacobiEquiv_of_RiemannSphere subsingleton_pic0_RiemannSphere

end AbelJacobiInputSymp

end JacobianChallenge

end
