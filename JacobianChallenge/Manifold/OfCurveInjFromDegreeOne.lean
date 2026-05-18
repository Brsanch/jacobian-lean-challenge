/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PrincDivWitnessExtraction
import JacobianChallenge.Manifold.BijectiveAnalyticToBiholomorphismDischarge
import JacobianChallenge.Manifold.PullbackLinearEquiv
import JacobianChallenge.Manifold.DegreeOneBijective
import JacobianChallenge.Manifold.SurjectiveOfNonConstantDischarge
import JacobianChallenge.Manifold.NearbyRegularWitnessUnconditional
import JacobianChallenge.Topology.OnePointHomeoSphere
import JacobianChallenge.Jacobian
import Mathlib

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Conditional item-16 closure: `ofCurve_inj` from a degree-1 hypothesis

`Jacobian.lean`'s `ofCurve_inj` (item 16 of `Basic.lean`) currently has
`sorry`. Under honest `PrincDiv X` it requires Abel's theorem at
genus ≥ 1.

This file ships a **conditional closure**: given the **single named
classical hypothesis** that a meromorphic function with a simple zero
at `Q₁ ≠ Q₂` and a simple pole at `Q₂` (and no other zeros/poles)
extends to a degree-1 ω-smooth map `X → RiemannSphere`, `ofCurve_inj`
holds. The remaining classical content (the named hypothesis) is the
local pole-extension construction (Forster §1.4), reduced to a single
chip.

## Proof chain

1. Suppose `ofCurve P Q₁ = ofCurve P Q₂` with `Q₁ ≠ Q₂`.
2. Then `single Q₁ - single Q₂ ∈ PrincDiv X` (quotient-equality unfolding).
3. Extract witness `f : MeromorphicNonzero X` with
   `principalDivisorMap f = single Q₁ - single Q₂` via
   `exists_meromorphicNonzero_principalDivisorMap_of_mem_PrincDiv`.
4. By the **named hypothesis** `DegreeOneFromSimpleZeroSimplePole`,
   `degreeFiber f.toRiemannSphere = 1`.
5. By `bijective_of_degreeFiber_eq_one` (with unconditional
   `ramificationSumEqualsDegree_holds_unconditional` +
   `surjective_of_NonConstant_Analytic_Manifold_holds`),
   `f.toRiemannSphere` is bijective.
6. By `bijectiveAnalyticIsBiholomorphism_holds X` (discharged in
   `Manifold/BijectiveAnalyticToBiholomorphismDischarge.lean`),
   there exists `e : HolomorphicEquiv X RiemannSphere`.
7. By `genus_eq_zero_iff_homeo_of_HolomorphicEquiv_RiemannSphere`
   (`Manifold/PullbackLinearEquiv.lean`), `genus X = 0`.
8. Contradicts `0 < genus X`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Named classical hypothesis: simple-zero/simple-pole meromorphic
function extends to a degree-1 map to the Riemann sphere.**

If `principalDivisorMap f = single Q₁ - single Q₂` for distinct
`Q₁, Q₂ : X`, then `f.toRiemannSphere : X → ℙ¹` is a non-constant
ω-smooth map of degree 1.

Classical content: local pole-extension construction (Forster §1.4) +
degree counting on a regular fibre (the simple zero gives a single
preimage of `0 ∈ ℙ¹` with ramification 1). Not in mathlib at this pin;
exposed as a named hypothesis. -/
def DegreeOneFromSimpleZeroSimplePole (X : Type u) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X] : Prop :=
  letI : DecidableEq X := Classical.decEq X
  ∀ (f : MeromorphicNonzero X) (Q₁ Q₂ : X), Q₁ ≠ Q₂ →
    principalDivisorMap f = Div.single Q₁ - Div.single Q₂ →
      JacobianChallenge.ContMDiff.degreeFiber f.toRiemannSphere
        f.toRiemannSphere_contMDiff = 1 ∧
      ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere

/-- **Item 16 conditional closure**: under `0 < genus X` and the named
classical hypothesis `DegreeOneFromSimpleZeroSimplePole X`,
`Function.Injective (Jacobian.ofCurve P)` holds. -/
theorem ofCurve_inj_under_genus_pos
    (h_deg1 : DegreeOneFromSimpleZeroSimplePole (X := X))
    (P : X) (h_pos : 0 < JacobianChallenge.genus X) :
    Function.Injective (Jacobian.ofCurve (X := X) P) := by
  classical
  letI : DecidableEq X := Classical.decEq X
  intro Q₁ Q₂ hQ
  by_contra h_ne
  -- hQ : ofCurve P Q₁ = ofCurve P Q₂, h_ne : Q₁ ≠ Q₂.
  let D₁ : Div0 X := ⟨Div.single Q₁ - Div.single P, Div.single_sub_single_mem_Div0 P Q₁⟩
  let D₂ : Div0 X := ⟨Div.single Q₂ - Div.single P, Div.single_sub_single_mem_Div0 P Q₂⟩
  -- From the equality of quotient classes, the difference is in the subgroup.
  have hQ' : (QuotientAddGroup.mk D₁ : Jacobian X) = QuotientAddGroup.mk D₂ := hQ
  rw [QuotientAddGroup.eq] at hQ'
  -- hQ' : -D₁ + D₂ ∈ (PrincDiv X).addSubgroupOf (Div0 X)
  -- Unfold via AddSubgroup.mem_addSubgroupOf — yields membership of
  -- coercion `↑(-D₁ + D₂)` (a `Div X`) in `PrincDiv X`.
  simp only [AddSubgroup.mem_addSubgroupOf] at hQ'
  -- hQ' : ↑(-D₁ + D₂) ∈ PrincDiv X, where ↑(-D₁ + D₂) : Div X.
  have hPrinc : (Div.single Q₂ - Div.single Q₁ : Div X) ∈ PrincDiv X := by
    have h_val : ((-D₁ + D₂ : Div0 X) : Div X) = Div.single Q₂ - Div.single Q₁ := by
      show (-(Div.single Q₁ - Div.single P) + (Div.single Q₂ - Div.single P) : Div X)
        = Div.single Q₂ - Div.single Q₁
      abel
    rw [h_val] at hQ'
    exact hQ'
  -- Step 3: Extract witness f.
  obtain ⟨f, hf⟩ :=
    exists_meromorphicNonzero_principalDivisorMap_of_mem_PrincDiv hPrinc
  -- hf : principalDivisorMap f = Div.single Q₂ - Div.single Q₁
  have h_ne_sym : Q₂ ≠ Q₁ := fun h => h_ne h.symm
  -- Step 4: degreeFiber f.toRiemannSphere = 1 via named hypothesis.
  obtain ⟨h_deg, h_nonconst⟩ := h_deg1 f Q₂ Q₁ h_ne_sym hf
  -- Step 5: Bijective f.toRiemannSphere.
  have hf_smooth := f.toRiemannSphere_contMDiff
  have h_RS : JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_statement X
                JacobianChallenge.RiemannSphere :=
    JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_holds_unconditional
      (X := X) (Y := JacobianChallenge.RiemannSphere)
  have h_surj : Surjective_of_NonConstant_Analytic_Manifold X
                  JacobianChallenge.RiemannSphere :=
    surjective_of_NonConstant_Analytic_Manifold_holds
  have hbij : Function.Bijective f.toRiemannSphere :=
    bijective_of_degreeFiber_eq_one h_RS h_surj hf_smooth h_nonconst h_deg
  -- Step 6: HolomorphicEquiv X RS.
  obtain ⟨e⟩ : Nonempty (HolomorphicEquiv X JacobianChallenge.RiemannSphere) :=
    bijectiveAnalyticIsBiholomorphism_holds X
      (Y := JacobianChallenge.RiemannSphere)
      f.toRiemannSphere hf_smooth hbij
  -- Step 7: genus X = 0 from biholomorphism.
  have h_genus_zero : JacobianChallenge.genus X = 0 := by
    apply (JacobianChallenge.genus_eq_zero_iff_homeo_of_HolomorphicEquiv_RiemannSphere
            (X := X) e).mpr
    -- Need: Nonempty (X ≃ₜ StandardS2). Compose e.toHomeomorph with
    -- RiemannSphere.toSphereHomeo.
    exact ⟨e.toHomeomorph.trans RiemannSphere.toSphereHomeo⟩
  -- Step 8: Contradicts 0 < genus X.
  omega

end JacobianChallenge

end
