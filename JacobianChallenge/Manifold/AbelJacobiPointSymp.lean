/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiPoint
import JacobianChallenge.Manifold.PeriodLatticeSymplecticBundle

set_option linter.unusedSectionVars false

/-! # Symplectic-bundle parallel of `AbelJacobiPath` + `AbelJacobiPoint`

Following the 2026-05-17 late-night `PeriodLatticeSymplecticBundle`
refactor (`Manifold/PeriodLatticeSymplecticBundle.lean`), this file
provides the parallel pathwise / pointwise Abel-Jacobi machinery
parametrised over the new symplectic bundle instead of the legacy
`PeriodLatticeDiscretenessBundle`.

The underlying mathematics is identical — `abelJacobiPath α h γ` is the
class `[complexChainPeriodVector α (single γ)] mod periodLatticeImage` —
but the bundle hypothesis is now the corrected one
(`PeriodLatticeSymplecticBundle`), so downstream consumers no longer
have to traffic in the dead-code legacy bundle.

The lattice equality
`(PeriodLatticeOfRankTwoG.ofSymplectic …).lattice = periodLatticeImage data α`
(`PeriodLatticeOfRankTwoG.ofSymplectic_lattice`, `@[simp]`) makes the
membership rewrites mechanical — identical in shape to the legacy
versions in `AbelJacobiPath.lean`.

## What this file ships

* `abelJacobiPathSymp` — pathwise AJ class against a symplectic bundle.
* `abelJacobiPathSymp_eq_of_shared_endpoints` — path independence.
* `abelJacobiChainSymp` — chain-level `AddMonoidHom`.
* `abelJacobiChainSymp_single` / `_cycle_eq_zero` — apply lemmas.
* `AbelJacobiInputSymp` — base-point + path-from-base bundle.
* `abelJacobiPointSymp` / `relAbelJacobiSymp` — pointwise + relative AJ.
* `relAbelJacobiSymp_self` / `_swap` — basic identities.
* `AbelJacobiInput.toSymp` — legacy → symplectic conversion.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Submodule Module

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ⊤ X]

/-! ## Pathwise AJ class against the symplectic bundle -/

/-- **Pathwise Abel-Jacobi class (symplectic).** Same construction as
`abelJacobiPath` but parametrised over a `PeriodLatticeSymplecticBundle`. -/
def abelJacobiPathSymp
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) α)
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) :
    AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle X) α h :=
  QuotientAddGroup.mk
    (complexChainPeriodVector α (SmoothChain.single γ))

/-- **Path-independence (symplectic).** Two smooth paths with shared
endpoints determine the same class in `AnalyticJacobianSymp`. -/
theorem abelJacobiPathSymp_eq_of_shared_endpoints
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) α)
    {γ γ' : SmoothPath 𝓘(ℝ, ℂ) X}
    (hsrc : γ.src = γ'.src) (htgt : γ.tgt = γ'.tgt) :
    abelJacobiPathSymp α h γ = abelJacobiPathSymp α h γ' := by
  change (QuotientAddGroup.mk (complexChainPeriodVector α (SmoothChain.single γ))
        : AnalyticJacobianSymp _ α h)
      = QuotientAddGroup.mk (complexChainPeriodVector α (SmoothChain.single γ'))
  rw [QuotientAddGroup.eq]
  rw [PeriodLatticeOfRankTwoG.ofSymplectic_lattice]
  rw [neg_add_eq_sub]
  exact complexChainPeriodVector_single_diff_mem_periodLatticeImage
    (γ := γ') (γ' := γ) hsrc.symm htgt.symm α

/-! ## Chain-level AJ as `AddMonoidHom` (symplectic) -/

/-- **Chain-level Abel-Jacobi map (symplectic).** Mirrors
`abelJacobiChain` against the symplectic bundle. -/
def abelJacobiChainSymp
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) α) :
    SmoothChain 𝓘(ℝ, ℂ) X
      →+ AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle X) α h :=
  (QuotientAddGroup.mk' (PeriodLatticeOfRankTwoG.ofSymplectic
    (PeriodPairingData.ofSmoothCycle X) α h).lattice).comp
      (complexChainPeriodVectorHom α)

@[simp] lemma abelJacobiChainSymp_apply
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) α)
    (c : SmoothChain 𝓘(ℝ, ℂ) X) :
    abelJacobiChainSymp α h c
      = QuotientAddGroup.mk (complexChainPeriodVector α c) := rfl

@[simp] lemma abelJacobiChainSymp_single
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) α)
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) :
    abelJacobiChainSymp α h (SmoothChain.single γ) = abelJacobiPathSymp α h γ := rfl

/-- **`abelJacobiChainSymp` vanishes on cycles.** -/
lemma abelJacobiChainSymp_cycle_eq_zero
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) α)
    (c : SmoothCycle 𝓘(ℝ, ℂ) X) :
    abelJacobiChainSymp α h (c : SmoothChain 𝓘(ℝ, ℂ) X) = 0 := by
  change (QuotientAddGroup.mk
            (complexChainPeriodVector α (c : SmoothChain 𝓘(ℝ, ℂ) X)) :
          AnalyticJacobianSymp _ α h) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  rw [PeriodLatticeOfRankTwoG.ofSymplectic_lattice]
  rw [complexChainPeriodVector_of_cycle_eq_periodVector]
  exact ⟨c, rfl⟩

/-! ## Pointwise AJ + base-point bundle (symplectic) -/

/-- **Abel-Jacobi base-point bundle (symplectic).** Parallel of
`AbelJacobiInput` against `PeriodLatticeSymplecticBundle`. -/
structure AbelJacobiInputSymp
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) α) where
  /-- A chosen base point on `X`. -/
  basePoint : X
  /-- For each target `Q : X`, a smooth path from `basePoint` to `Q`. -/
  pathFromBase : (Q : X) → SmoothPath 𝓘(ℝ, ℂ) X
  /-- The source of each `pathFromBase Q` is `basePoint`. -/
  src_eq : ∀ Q : X, (pathFromBase Q).src = basePoint
  /-- The target of each `pathFromBase Q` is `Q`. -/
  tgt_eq : ∀ Q : X, (pathFromBase Q).tgt = Q

namespace AbelJacobiInputSymp

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) α}

/-- **Pointwise Abel-Jacobi map (symplectic).** -/
def abelJacobiPoint (B : AbelJacobiInputSymp α h) (Q : X) :
    AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle X) α h :=
  abelJacobiPathSymp α h (B.pathFromBase Q)

@[simp] lemma abelJacobiPoint_def (B : AbelJacobiInputSymp α h) (Q : X) :
    B.abelJacobiPoint Q = abelJacobiPathSymp α h (B.pathFromBase Q) := rfl

/-- **Relative Abel-Jacobi (symplectic).** -/
def relAbelJacobi (B : AbelJacobiInputSymp α h) (P Q : X) :
    AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle X) α h :=
  B.abelJacobiPoint Q - B.abelJacobiPoint P

@[simp] lemma relAbelJacobi_def (B : AbelJacobiInputSymp α h) (P Q : X) :
    B.relAbelJacobi P Q = B.abelJacobiPoint Q - B.abelJacobiPoint P := rfl

/-- **Self-relative AJ is zero.** -/
@[simp] lemma relAbelJacobi_self (B : AbelJacobiInputSymp α h) (P : X) :
    B.relAbelJacobi P P = 0 := by
  show B.abelJacobiPoint P - B.abelJacobiPoint P = 0
  exact sub_self _

/-- **Antisymmetry of `relAbelJacobi` (symplectic).** -/
lemma relAbelJacobi_swap (B : AbelJacobiInputSymp α h) (P Q : X) :
    B.relAbelJacobi P Q = -(B.relAbelJacobi Q P) := by
  change B.abelJacobiPoint Q - B.abelJacobiPoint P
      = -(B.abelJacobiPoint P - B.abelJacobiPoint Q)
  abel

end AbelJacobiInputSymp

/-! ## Legacy → symplectic conversion -/

/-- **Convert a legacy `AbelJacobiInput` to a symplectic one.** The
base-point + path-from-base data is bundle-independent; the conversion
just rewires the type parameter through `PeriodLatticeDiscretenessBundle.toSymplectic`. -/
noncomputable def AbelJacobiInput.toSymp
    {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
    {h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α}
    (B : AbelJacobiInput α h) :
    AbelJacobiInputSymp α h.toSymplectic where
  basePoint := B.basePoint
  pathFromBase := B.pathFromBase
  src_eq := B.src_eq
  tgt_eq := B.tgt_eq

end JacobianChallenge

end
