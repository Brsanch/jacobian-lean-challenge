/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AnalyticJacobianSympComplexTorusEquiv
import JacobianChallenge.Manifold.AbelHypothesisFromPrincipal

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # `AbelHypothesis` on `T_L` reduces to the T_L-divisor-sum hypothesis

Using `analyticJacobianSympEquiv_complexTorus` (the iso
`AnalyticJacobianSymp ≃+ ℂ ⧸ L`) under which the AJ point map
becomes the identity on `T_L`, the `AbelHypothesis` reduces to a
purely T_L-level statement:

  **`∀ f : MeromorphicNonzero (ℂ⧸L), ∑ x, ord_x(f) • x = 0 in T_L`**

This is **Abel's theorem on elliptic functions** (classical residue
theorem applied to `d log f` on a fundamental domain of L in ℂ).

Once this T_L-level statement is discharged classically, the
`AbelHypothesis` on the canonical AJ input on T_L follows
unconditionally.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## The named T_L-level divisor-sum hypothesis -/

/-- **Abel's theorem on `T_L`, as a named hypothesis at the T_L level.**

States: for every meromorphic-nonvanishing-germ function `f` on
`T_L = ℂ ⧸ L`, the formal sum `∑ x ∈ supp(div f), ord_x(f) • x`
vanishes in `T_L`.

Classically: this is the elliptic-function version of Abel's theorem,
equivalent to `∮_∂R d log f = 0` on a fundamental domain
`R ⊂ ℂ` of the lattice `L`. -/
def TLDivSumHypothesis : Prop :=
  ∀ f : MeromorphicNonzero (ℂ ⧸ L),
    ∑ x ∈ (principalDivisorMap f).supportFinset,
        ((principalDivisorMap f : Div (ℂ ⧸ L)) : ℂ ⧸ L → ℤ) x • x = (0 : ℂ ⧸ L)

/-! ## The reduction: TLDivSumHypothesis ⟹ AbelHypothesis -/

/-- **`AbelHypothesis (canonicalAbelJacobiInputSymp L h)` from
`TLDivSumHypothesis`.**

The AJ point map under the iso `analyticJacobianSympEquiv_complexTorus`
is the identity on T_L. Hence for a divisor `D`:

  `analyticJacobianSympEquiv (B.abelJacobiDivHom D) = ∑ x, (D x) • x`

The RHS vanishes for `D = principalDivisorMap f` by
`TLDivSumHypothesis`; applying the iso's `(equiv).symm 0 = 0` gives the
AnalyticJacobianSymp-level vanishing, and hence `AbelHypothesis`. -/
theorem abelHypothesis_complexTorus_of_TLDivSum
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L))
    (hTL : TLDivSumHypothesis L) :
    AbelJacobiInputSymp.AbelHypothesis (canonicalAbelJacobiInputSymp L h) := by
  apply AbelJacobiInputSymp.abelHypothesis_of_abelJacobiDivHom_principal_zero
  intro f
  -- Goal: B.abelJacobiDivHom (principalDivisorMap f) = 0.
  -- The iso analyticJacobianSympEquiv sends abelJacobiPoint x to x, so
  -- analyticJacobianSympEquiv (B.abelJacobiDivHom (principalDivisorMap f))
  --   = ∑ x, (div f x) • analyticJacobianSympEquiv (B.abelJacobiPoint x)
  --   = ∑ x, (div f x) • x = 0   (by TLDivSumHypothesis).
  -- Then apply (equiv).symm to get the original = 0.
  apply (analyticJacobianSympEquiv_complexTorus L h).injective
  rw [(analyticJacobianSympEquiv_complexTorus L h).map_zero]
  -- LHS: analyticJacobianSympEquiv (∑ x, (div f x) • B.abelJacobiPoint x).
  show analyticJacobianSympEquiv_complexTorus L h
      (∑ x ∈ (principalDivisorMap f).supportFinset,
        ((principalDivisorMap f : Div (ℂ ⧸ L)) : ℂ ⧸ L → ℤ) x •
          (canonicalAbelJacobiInputSymp L h).abelJacobiPoint x) = 0
  rw [map_sum]
  -- Each summand: equiv (n • abelJacobiPoint x) = n • equiv (abelJacobiPoint x) = n • x.
  have h_eq :
      ∀ x ∈ (principalDivisorMap f).supportFinset,
        analyticJacobianSympEquiv_complexTorus L h
            (((principalDivisorMap f : Div (ℂ ⧸ L)) : ℂ ⧸ L → ℤ) x •
              (canonicalAbelJacobiInputSymp L h).abelJacobiPoint x)
          = ((principalDivisorMap f : Div (ℂ ⧸ L)) : ℂ ⧸ L → ℤ) x • x := by
    intro x _
    rw [map_zsmul,
      analyticJacobianSympEquiv_complexTorus_abelJacobiPoint]
  rw [Finset.sum_congr rfl h_eq]
  exact hTL f

end ComplexTorus

end JacobianChallenge

end
