/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiPointSymp
import JacobianChallenge.Manifold.AbelJacobiDiv
import JacobianChallenge.Manifold.AbelJacobiPic0
import JacobianChallenge.Manifold.AbelJacobiIso
import JacobianChallenge.Manifold.C3FullInput
import JacobianChallenge.Manifold.PeriodLatticeOfRankTwoG_LieGroupWiring

set_option linter.unusedSectionVars false

/-! # `C3FullInputSymp X` — C3 full input parametrised over the symplectic bundle

Mechanical replication of the legacy `C3FullInput` chain
(`AbelJacobiPoint` → `AbelJacobiDiv` → `AbelJacobiPic0` → `AbelJacobiIso`
→ `C3FullInput`) but with the `discreteness` slot taking the corrected
`PeriodLatticeSymplecticBundle` instead of the dead-code
`PeriodLatticeDiscretenessBundle`.

The underlying analytic-Jacobian target
`AnalyticJacobianSymp data α h_symp` and the legacy
`AnalyticJacobian data α h_legacy` are **both** definitionally
`(Fin g → ℂ) ⧸ (periodLatticeImage data α).toIntSubmodule`, so the
chain definitions translate by mechanical type-swap.

## What this file ships

The full symplectic AJ chain:

1. `AbelJacobiInputSymp.abelJacobiDiv` / `_DivHom` / `_Div0Hom` —
   divisor-level AJ.
2. `AbelJacobiInputSymp.AbelHypothesis` / `.abelJacobi` —
   descent through `Pic⁰ X`.
3. `AbelJacobiInputSymp.JacobiInversion` + `.abelJacobiEquiv`.
4. `C3FullInputSymp` — the 5-field bundle.
5. `C3FullInputSymp.abelJacobiEquiv` — the headline `AddEquiv`.
6. Instance-discharge helpers mirroring `C3FullInputInstances.lean`.
7. `C3FullInput.toSymp` — legacy → symplectic conversion.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Submodule Module

namespace JacobianChallenge

universe u

namespace AbelJacobiInputSymp

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) α}

/-! ## Divisor-level Abel-Jacobi (symplectic) -/

/-- **Divisor-level Abel-Jacobi (symplectic).** -/
noncomputable def abelJacobiDiv (B : AbelJacobiInputSymp α h) (D : Div X) :
    AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle X) α h :=
  ∑ x ∈ D.supportFinset, ((D : X → ℤ) x) • B.abelJacobiPoint x

lemma abelJacobiDiv_eq_sum_of_supportFinset_subset
    (B : AbelJacobiInputSymp α h) {D : Div X} {S : Finset X}
    (hS : D.supportFinset ⊆ S) :
    B.abelJacobiDiv D
      = ∑ x ∈ S, ((D : X → ℤ) x) • B.abelJacobiPoint x := by
  classical
  unfold abelJacobiDiv
  refine Finset.sum_subset hS ?_
  intro x _ hxS
  rw [Div.apply_eq_zero_of_notMem_supportFinset hxS, zero_smul]

@[simp] lemma abelJacobiDiv_zero (B : AbelJacobiInputSymp α h) :
    B.abelJacobiDiv (0 : Div X) = 0 := by
  classical
  unfold abelJacobiDiv
  have hsupp : ((0 : Div X) : X → ℤ).support = (∅ : Set X) := by
    ext x; simp
  have hempty : (0 : Div X).supportFinset = (∅ : Finset X) := by
    unfold Div.supportFinset
    apply Finset.eq_empty_iff_forall_notMem.2
    intro x hx
    have hx' : x ∈ ((0 : Div X) : X → ℤ).support :=
      (Set.Finite.mem_toFinset _).1 hx
    rw [hsupp] at hx'
    exact hx'.elim
  rw [hempty]
  exact Finset.sum_empty

lemma abelJacobiDiv_add (B : AbelJacobiInputSymp α h) (D₁ D₂ : Div X) :
    B.abelJacobiDiv (D₁ + D₂) = B.abelJacobiDiv D₁ + B.abelJacobiDiv D₂ := by
  classical
  set S : Finset X :=
    (D₁ + D₂).supportFinset ∪ D₁.supportFinset ∪ D₂.supportFinset with hS_def
  have h12 : (D₁ + D₂).supportFinset ⊆ S := by
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have h1 : D₁.supportFinset ⊆ S := by
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have h2 : D₂.supportFinset ⊆ S := by
    intro x hx
    exact Finset.mem_union_right _ hx
  rw [B.abelJacobiDiv_eq_sum_of_supportFinset_subset h12,
      B.abelJacobiDiv_eq_sum_of_supportFinset_subset h1,
      B.abelJacobiDiv_eq_sum_of_supportFinset_subset h2]
  have hpt : ∀ x : X, ((D₁ + D₂ : Div X) : X → ℤ) x
      = (D₁ : X → ℤ) x + (D₂ : X → ℤ) x := by
    intro x
    simp [Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
  rw [show (∑ x ∈ S, ((D₁ + D₂ : Div X) : X → ℤ) x • B.abelJacobiPoint x)
        = ∑ x ∈ S, ((D₁ : X → ℤ) x + (D₂ : X → ℤ) x) • B.abelJacobiPoint x from by
        refine Finset.sum_congr rfl ?_
        intro x _; rw [hpt]]
  rw [show (∑ x ∈ S, ((D₁ : X → ℤ) x + (D₂ : X → ℤ) x) • B.abelJacobiPoint x)
        = ∑ x ∈ S, ((D₁ : X → ℤ) x • B.abelJacobiPoint x
          + (D₂ : X → ℤ) x • B.abelJacobiPoint x) from by
        refine Finset.sum_congr rfl ?_
        intro x _; rw [add_smul]]
  exact Finset.sum_add_distrib

/-- **Bundled divisor-level AJ (symplectic).** -/
noncomputable def abelJacobiDivHom (B : AbelJacobiInputSymp α h) :
    Div X →+ AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle X) α h where
  toFun := B.abelJacobiDiv
  map_zero' := B.abelJacobiDiv_zero
  map_add' := B.abelJacobiDiv_add

@[simp] lemma abelJacobiDivHom_apply (B : AbelJacobiInputSymp α h) (D : Div X) :
    B.abelJacobiDivHom D = B.abelJacobiDiv D := rfl

/-- **Restriction to degree-0 divisors (symplectic).** -/
noncomputable def abelJacobiDiv0Hom (B : AbelJacobiInputSymp α h) :
    Div0 X →+ AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle X) α h :=
  B.abelJacobiDivHom.comp (Div0 X).subtype

@[simp] lemma abelJacobiDiv0Hom_apply (B : AbelJacobiInputSymp α h) (D : Div0 X) :
    B.abelJacobiDiv0Hom D = B.abelJacobiDiv (D : Div X) := rfl

end AbelJacobiInputSymp

/-! ## Abel's theorem + descent to `Pic⁰ X` (symplectic) -/

namespace AbelJacobiInputSymp

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]
  {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) α}

/-- **Abel's theorem (symplectic, named-hypothesis form).** -/
def AbelHypothesis (B : AbelJacobiInputSymp α h) : Prop :=
  ∀ D : Div0 X, (D : Div X) ∈ PrincDiv X → B.abelJacobiDiv0Hom D = 0

lemma abelHypothesis_iff_subgroup_le_ker (B : AbelJacobiInputSymp α h) :
    AbelHypothesis B ↔
      (PrincDiv X).addSubgroupOf (Div0 X) ≤ B.abelJacobiDiv0Hom.ker := by
  constructor
  · intro hAbel D hD
    rw [AddMonoidHom.mem_ker]
    exact hAbel D hD
  · intro hSub D hD
    have : D ∈ B.abelJacobiDiv0Hom.ker := hSub hD
    rwa [AddMonoidHom.mem_ker] at this

/-- **The Abel-Jacobi map on `Pic⁰ X` (symplectic).** -/
noncomputable def abelJacobi (B : AbelJacobiInputSymp α h)
    (hAbel : AbelHypothesis B) :
    Pic0 X →+ AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle X) α h :=
  QuotientAddGroup.lift ((PrincDiv X).addSubgroupOf (Div0 X))
    B.abelJacobiDiv0Hom
    ((B.abelHypothesis_iff_subgroup_le_ker).mp hAbel)

@[simp] lemma abelJacobi_mk (B : AbelJacobiInputSymp α h)
    (hAbel : AbelHypothesis B) (D : Div0 X) :
    B.abelJacobi hAbel (QuotientAddGroup.mk D : Pic0 X)
      = B.abelJacobiDiv0Hom D := rfl

lemma abelJacobi_mk_eq_abelJacobiDiv
    (B : AbelJacobiInputSymp α h) (hAbel : AbelHypothesis B) (D : Div0 X) :
    B.abelJacobi hAbel (QuotientAddGroup.mk D : Pic0 X)
      = B.abelJacobiDiv (D : Div X) := by
  rw [abelJacobi_mk]
  rfl

/-! ## Jacobi inversion + AddEquiv (symplectic) -/

/-- **Jacobi inversion (symplectic).** -/
structure JacobiInversion (B : AbelJacobiInputSymp α h)
    (hAbel : AbelHypothesis B) : Prop where
  injective : Function.Injective (B.abelJacobi hAbel)
  surjective : Function.Surjective (B.abelJacobi hAbel)

lemma JacobiInversion.bijective
    {B : AbelJacobiInputSymp α h} {hAbel : AbelHypothesis B}
    (hJI : JacobiInversion B hAbel) :
    Function.Bijective (B.abelJacobi hAbel) :=
  ⟨hJI.injective, hJI.surjective⟩

/-- **The Abel-Jacobi isomorphism (symplectic):
`Pic⁰ X ≃+ AnalyticJacobianSymp`.** -/
noncomputable def abelJacobiEquiv (B : AbelJacobiInputSymp α h)
    (hAbel : AbelHypothesis B) (hJI : JacobiInversion B hAbel) :
    Pic0 X ≃+ AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle X) α h :=
  AddEquiv.ofBijective (B.abelJacobi hAbel) hJI.bijective

@[simp] lemma abelJacobiEquiv_apply
    (B : AbelJacobiInputSymp α h) (hAbel : AbelHypothesis B)
    (hJI : JacobiInversion B hAbel) (c : Pic0 X) :
    B.abelJacobiEquiv hAbel hJI c = B.abelJacobi hAbel c := rfl

end AbelJacobiInputSymp

/-! ## `C3FullInputSymp` bundle + headline `abelJacobiEquiv` -/

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **C3 full input bundle (symplectic).** -/
structure C3FullInputSymp where
  basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)
  discreteness : PeriodLatticeSymplecticBundle
    (PeriodPairingData.ofSmoothCycle X) basis
  ajInput : AbelJacobiInputSymp basis discreteness
  abel : AbelJacobiInputSymp.AbelHypothesis ajInput
  jacobi : AbelJacobiInputSymp.JacobiInversion ajInput abel

namespace C3FullInputSymp

variable {X}

/-- **The Abel-Jacobi `AddEquiv` (symplectic).** -/
noncomputable def abelJacobiEquiv (B : JacobianChallenge.C3FullInputSymp X) :
    Pic0 X ≃+ AnalyticJacobianSymp
      (PeriodPairingData.ofSmoothCycle X) B.basis B.discreteness :=
  B.ajInput.abelJacobiEquiv B.abel B.jacobi

end C3FullInputSymp

/-! ## Per-point + per-divisor identity between legacy and symplectic AJ

The underlying types `AnalyticJacobian` and `AnalyticJacobianSymp` are
definitionally equal (both reduce to
`(Fin g → ℂ) ⧸ (periodLatticeImage data α).toIntSubmodule`), and the
constructor `QuotientAddGroup.mk` is the same. Hence per-point and
per-divisor AJ values agree by `rfl`. -/

namespace AbelJacobiInput

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]
  {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α}

/-- **Per-point: symplectic vs legacy AJ values agree.** -/
lemma toSymp_abelJacobiPoint_eq (B : AbelJacobiInput α h) (Q : X) :
    (B.toSymp.abelJacobiPoint Q
        : AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle X) α h.toSymplectic)
      = (B.abelJacobiPoint Q
        : AnalyticJacobian (PeriodPairingData.ofSmoothCycle X) α h) := rfl

/-- **Per-divisor: symplectic vs legacy AJ values agree.** -/
lemma toSymp_abelJacobiDiv_eq (B : AbelJacobiInput α h) (D : Div X) :
    (B.toSymp.abelJacobiDiv D
        : AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle X) α h.toSymplectic)
      = (B.abelJacobiDiv D
        : AnalyticJacobian (PeriodPairingData.ofSmoothCycle X) α h) := by
  classical
  show (∑ x ∈ D.supportFinset, ((D : X → ℤ) x) • B.toSymp.abelJacobiPoint x
          : AnalyticJacobianSymp _ _ _)
      = ∑ x ∈ D.supportFinset, ((D : X → ℤ) x) • B.abelJacobiPoint x
  refine Finset.sum_congr rfl ?_
  intro x _
  rfl

end AbelJacobiInput

/-! ## Legacy → symplectic for `C3FullInput`

The Abel + Jacobi hypotheses transport via the per-divisor equality
above. -/

namespace C3FullInput

variable {X}

/-- **Abel hypothesis transports along `toSymp`.** -/
lemma abel_of_toSymp
    (B : JacobianChallenge.C3FullInput X)
    (hAbel : AbelJacobiInput.AbelHypothesis B.ajInput) :
    AbelJacobiInputSymp.AbelHypothesis (B.ajInput.toSymp) := by
  intro D hD
  -- symp side: B.ajInput.toSymp.abelJacobiDiv0Hom D = B.ajInput.toSymp.abelJacobiDiv (D : Div X)
  show B.ajInput.toSymp.abelJacobiDiv (D : Div X) = 0
  rw [B.ajInput.toSymp_abelJacobiDiv_eq]
  -- legacy side equals 0 by hAbel.
  have h_legacy : B.ajInput.abelJacobiDiv0Hom D = 0 := hAbel D hD
  -- Unfold legacy abelJacobiDiv0Hom to abelJacobiDiv.
  have : B.ajInput.abelJacobiDiv (D : Div X) = 0 := h_legacy
  exact this

/-- **Per-Pic⁰: symplectic vs legacy `abelJacobi` agree.** -/
private lemma toSymp_abelJacobi_eq
    (B : JacobianChallenge.C3FullInput X)
    (hAbel : AbelJacobiInput.AbelHypothesis B.ajInput) (c : Pic0 X) :
    (B.ajInput.toSymp.abelJacobi (B.abel_of_toSymp hAbel) c
        : AnalyticJacobianSymp _ _ _)
      = (B.ajInput.abelJacobi hAbel c
        : AnalyticJacobian _ _ _) := by
  refine QuotientAddGroup.induction_on c ?_
  intro D
  rw [AbelJacobiInputSymp.abelJacobi_mk_eq_abelJacobiDiv,
      AbelJacobiInput.abelJacobi_mk_eq_abelJacobiDiv]
  exact B.ajInput.toSymp_abelJacobiDiv_eq (D : Div X)

/-- **Jacobi inversion transports along `toSymp`.** -/
lemma jacobi_of_toSymp
    (B : JacobianChallenge.C3FullInput X)
    (hAbel : AbelJacobiInput.AbelHypothesis B.ajInput)
    (hJI : AbelJacobiInput.JacobiInversion B.ajInput hAbel) :
    AbelJacobiInputSymp.JacobiInversion (B.ajInput.toSymp)
      (B.abel_of_toSymp hAbel) := by
  refine ⟨?_, ?_⟩
  · -- Injectivity via per-class identity.
    intro x y hxy
    have h_eq : B.ajInput.abelJacobi hAbel x
        = B.ajInput.abelJacobi hAbel y := by
      have hx := B.toSymp_abelJacobi_eq hAbel x
      have hy := B.toSymp_abelJacobi_eq hAbel y
      -- hx : symp.abelJacobi x = legacy.abelJacobi x
      -- hy : symp.abelJacobi y = legacy.abelJacobi y
      -- hxy : symp.abelJacobi x = symp.abelJacobi y
      -- Rewrite: legacy.abelJacobi x = symp.abelJacobi x = symp.abelJacobi y = legacy.abelJacobi y
      rw [← hx, ← hy]; exact hxy
    exact hJI.injective h_eq
  · -- Surjectivity via per-class identity.
    intro v
    obtain ⟨c, hc⟩ := hJI.surjective v
    refine ⟨c, ?_⟩
    rw [B.toSymp_abelJacobi_eq hAbel]
    exact hc

/-- **Legacy → symplectic for `C3FullInput`.** -/
noncomputable def toSymp (B : JacobianChallenge.C3FullInput X) :
    JacobianChallenge.C3FullInputSymp X where
  basis := B.basis
  discreteness := B.discreteness.toSymplectic
  ajInput := B.ajInput.toSymp
  abel := B.abel_of_toSymp B.abel
  jacobi := B.jacobi_of_toSymp B.abel B.jacobi

end C3FullInput

/-! ## Instance discharges from `C3FullInputSymp`

Mirrors `C3FullInputInstances.lean`: items 11, 5+12, 13 on
`JacobianOfLattice X (PeriodLatticeOfRankTwoG.ofSymplectic …)`. -/

namespace C3FullInputSymp

variable {X}

/-- **Item 11 content (symplectic).** -/
theorem compactSpaceHypothesis (B : JacobianChallenge.C3FullInputSymp X) :
    haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle
      B.discreteness
    haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle
      B.discreteness
    JacobianOfLattice.CompactSpaceHypothesis
      (PeriodLatticeOfRankTwoG.ofSymplectic (PeriodPairingData.ofSmoothCycle X)
        B.basis B.discreteness) :=
  PeriodLatticeOfRankTwoG.ofSymplectic_compactSpace
    (PeriodPairingData.ofSmoothCycle X) B.basis B.discreteness

/-- **Items 5 + 12 content (symplectic).** -/
noncomputable def chartedSpaceHypothesis (B : JacobianChallenge.C3FullInputSymp X) :
    haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle
      B.discreteness
    haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle
      B.discreteness
    JacobianOfLattice.ChartedSpaceHypothesis
      (PeriodLatticeOfRankTwoG.ofSymplectic (PeriodPairingData.ofSmoothCycle X)
        B.basis B.discreteness) :=
  PeriodLatticeOfRankTwoG.ofSymplectic_chartedSpace
    (PeriodPairingData.ofSmoothCycle X) B.basis B.discreteness

/-- **Item 13 content (symplectic).** -/
theorem lieAddGroupHypothesis (B : JacobianChallenge.C3FullInputSymp X) :
    haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle
      B.discreteness
    haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle
      B.discreteness
    haveI : DiscreteTopology
        (PeriodLatticeOfRankTwoG.ofSymplectic (PeriodPairingData.ofSmoothCycle X)
          B.basis B.discreteness).lattice.toIntSubmodule :=
      PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle
        B.discreteness
    haveI : IsZLattice ℝ
        (PeriodLatticeOfRankTwoG.ofSymplectic (PeriodPairingData.ofSmoothCycle X)
          B.basis B.discreteness).lattice.toIntSubmodule :=
      PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle
        B.discreteness
    JacobianOfLattice.LieAddGroupHypothesis
      (PeriodLatticeOfRankTwoG.ofSymplectic (PeriodPairingData.ofSmoothCycle X)
        B.basis B.discreteness)
      (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds
        (PeriodLatticeOfRankTwoG.ofSymplectic
          (PeriodPairingData.ofSmoothCycle X) B.basis B.discreteness)) := by
  haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle
    B.discreteness
  haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle
    B.discreteness
  haveI : DiscreteTopology
      (PeriodLatticeOfRankTwoG.ofSymplectic (PeriodPairingData.ofSmoothCycle X)
        B.basis B.discreteness).lattice.toIntSubmodule :=
    PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle
      B.discreteness
  haveI : IsZLattice ℝ
      (PeriodLatticeOfRankTwoG.ofSymplectic (PeriodPairingData.ofSmoothCycle X)
        B.basis B.discreteness).lattice.toIntSubmodule :=
    PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle
      B.discreteness
  exact PeriodLatticeOfRankTwoG.lieAddGroupHypothesis_holds _

end C3FullInputSymp

end JacobianChallenge

end
