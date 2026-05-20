/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.TLDivSumEvalSumBridge
import JacobianChallenge.Manifold.Pic0EquivComplexTorus

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # The Abel–Jacobi map on `Pic⁰ T_L` as `evalSum`

Under `TLDivSumHypothesis L`, the homomorphism
`Div.evalSumHom : Div (ℂ ⧸ L) →+ ℂ ⧸ L` vanishes on **all** of
`PrincDiv (ℂ ⧸ L)` (`evalSumHom_eq_zero_on_PrincDiv_of_TLDivSum` in
`TLDivSumEvalSumBridge.lean`). Restricted to `Div0 (ℂ ⧸ L)`, it descends
through the quotient by `(PrincDiv).addSubgroupOf (Div0)` to give the
**closed-form Abel–Jacobi map on `Pic⁰ T_L`**:

`evalSumPic0 : Pic⁰ (ℂ ⧸ L) →+ ℂ ⧸ L`,
sending the class of a degree-zero divisor `D = ∑ nᵢ (xᵢ)` to
`∑ nᵢ • xᵢ` in `ℂ ⧸ L`.

We also show `evalSumPic0` is **surjective** (every point of `ℂ ⧸ L` is
hit by `[ (Q) − (0) ]`), and that on `[Q − 0]` it returns `Q` — matching
the formula already proved for the abstract `pic0EquivComplexTorus`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## `Div0 (ℂ⧸L) →+ ℂ⧸L` from `evalSumHom` -/

/-- Restriction of `evalSumHom` to `Div0 (ℂ ⧸ L)`. -/
noncomputable def evalSumDiv0Hom : Div0 (ℂ ⧸ L) →+ (ℂ ⧸ L) :=
  Div.evalSumHom.comp (Div0 (ℂ ⧸ L)).subtype

@[simp] lemma evalSumDiv0Hom_apply (D : Div0 (ℂ ⧸ L)) :
    evalSumDiv0Hom L D = Div.evalSum (D : Div (ℂ ⧸ L)) := rfl

/-! ## Descent to `Pic⁰ T_L` -/

/-- **`Pic⁰ T_L`-valued Abel–Jacobi map via `evalSum`.**

Definitionally: the quotient of `Div.evalSumHom : Div (ℂ ⧸ L) →+ ℂ ⧸ L`
restricted to `Div0` by `(PrincDiv).addSubgroupOf (Div0)`. The descent
is allowed by `evalSumHom_eq_zero_on_PrincDiv_of_TLDivSum`
(`TLDivSumHypothesis L`), which makes `PrincDiv ⊆ ker evalSumHom`. -/
noncomputable def evalSumPic0
    (hTL : TLDivSumHypothesis L) : Pic0 (ℂ ⧸ L) →+ (ℂ ⧸ L) :=
  QuotientAddGroup.lift _ (evalSumDiv0Hom L) <| by
    intro D hD
    -- hD : D ∈ (PrincDiv (ℂ⧸L)).addSubgroupOf (Div0 (ℂ⧸L))
    -- Unfold to membership in PrincDiv at the Div level.
    have h_princ : (D : Div (ℂ ⧸ L)) ∈ PrincDiv (ℂ ⧸ L) := hD
    -- Apply the closure-induction result.
    exact evalSumHom_eq_zero_on_PrincDiv_of_TLDivSum L hTL _ h_princ

@[simp] lemma evalSumPic0_mk
    (hTL : TLDivSumHypothesis L) (D : Div0 (ℂ ⧸ L)) :
    evalSumPic0 L hTL (QuotientAddGroup.mk D)
      = Div.evalSum (D : Div (ℂ ⧸ L)) := rfl

/-! ## Surjectivity: every point of `T_L` is hit by `[(Q) − (0)]` -/

/-- **Image of `[ (Q) − (0) ]` under `evalSumPic0` equals `Q`.**

Concretely: `D = single Q − single 0` is degree zero, and
`evalSum D = Q • 1 − 0 • 1 = Q` in `ℂ ⧸ L`. -/
theorem evalSumPic0_single_sub_single
    (hTL : TLDivSumHypothesis L) (Q : ℂ ⧸ L) :
    haveI : DecidableEq (ℂ ⧸ L) := Classical.decEq _
    evalSumPic0 L hTL
        (QuotientAddGroup.mk
          (⟨Div.single Q - Div.single (0 : ℂ ⧸ L),
            Div.single_sub_single_mem_Div0 (0 : ℂ ⧸ L) Q⟩ : Div0 (ℂ ⧸ L)))
      = Q := by
  classical
  rw [evalSumPic0_mk]
  show Div.evalSum (Div.single Q - Div.single (0 : ℂ ⧸ L)) = Q
  -- evalSum (single Q - single 0) = evalSum (single Q) - evalSum (single 0)
  rw [Div.evalSum_sub]
  -- evalSum (single Q) = Q, evalSum (single 0) = 0.
  rw [Div.evalSum_single, Div.evalSum_single]
  simp

/-- **`evalSumPic0` is surjective.** Every `Q ∈ ℂ ⧸ L` is the image of
`[ (Q) − (0) ]`. -/
theorem evalSumPic0_surjective
    (hTL : TLDivSumHypothesis L) :
    Function.Surjective (evalSumPic0 L hTL) := by
  classical
  intro Q
  refine ⟨QuotientAddGroup.mk
    ⟨Div.single Q - Div.single (0 : ℂ ⧸ L),
      Div.single_sub_single_mem_Div0 (0 : ℂ ⧸ L) Q⟩, ?_⟩
  exact evalSumPic0_single_sub_single L hTL Q

/-! ## Identification: `pic0EquivComplexTorus = evalSumPic0` -/

/-- **The abstract Abel–Jacobi iso `pic0EquivComplexTorus` agrees, as a
function, with the concrete `evalSumPic0`.**

Both maps send `[D]` (for `D : Div0 (ℂ ⧸ L)`) to
`∑ x ∈ supp D, D x • x` in `ℂ ⧸ L`. For the LHS this is the content of
`analyticJacobianSympEquiv_abelJacobiDivHom` followed by the unfolding
of `abelJacobiDiv = abelJacobiDivHom` on the underlying divisor. For
the RHS it is the definition of `evalSum`. -/
theorem pic0EquivComplexTorus_eq_evalSumPic0
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L))
    (hTL : TLDivSumHypothesis L)
    (hConverse : TLAbelConverseHypothesis L) :
    (pic0EquivComplexTorus L h hTL hConverse : Pic0 (ℂ ⧸ L) → (ℂ ⧸ L))
      = evalSumPic0 L hTL := by
  classical
  ext c
  induction c using QuotientAddGroup.induction_on with
  | H D =>
  -- RHS: evalSumPic0 [D] = evalSum D.
  show (pic0EquivComplexTorus L h hTL hConverse)
      (QuotientAddGroup.mk D) = evalSumPic0 L hTL (QuotientAddGroup.mk D)
  rw [evalSumPic0_mk]
  -- LHS unfolds through pic0EquivComplexTorus = abelJacobiEquiv.trans iso.
  unfold pic0EquivComplexTorus
  show analyticJacobianSympEquiv_complexTorus L h
      ((canonicalAbelJacobiInputSymp L h).abelJacobiEquiv _ _ _)
    = Div.evalSum (D : Div (ℂ ⧸ L))
  rw [AbelJacobiInputSymp.abelJacobiEquiv_apply,
    AbelJacobiInputSymp.abelJacobi_mk_eq_abelJacobiDiv]
  -- iso (abelJacobiDiv D) = iso (abelJacobiDivHom D) (defeq) = evalSum D.
  show analyticJacobianSympEquiv_complexTorus L h
      ((canonicalAbelJacobiInputSymp L h).abelJacobiDivHom
        (D : Div (ℂ ⧸ L))) = Div.evalSum (D : Div (ℂ ⧸ L))
  rw [analyticJacobianSympEquiv_abelJacobiDivHom]
  rfl

/-- **Injectivity of `evalSumPic0` from `TLAbelConverseHypothesis`.**

If `[D] = [D']` in `Pic⁰ (ℂ ⧸ L)` is *forced* by `evalSum D = evalSum D'`,
then `D − D'` is a degree-zero divisor with `evalSum (D − D') = 0`, which
by `TLAbelConverseHypothesis L` lands in `PrincDiv`, i.e. `[D] = [D']`. -/
theorem evalSumPic0_injective
    (hTL : TLDivSumHypothesis L)
    (hConverse : TLAbelConverseHypothesis L) :
    Function.Injective (evalSumPic0 L hTL) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro c hc
  induction c using QuotientAddGroup.induction_on with
  | H D =>
  rw [evalSumPic0_mk] at hc
  -- hc : evalSum (D : Div) = 0.
  -- Unfold evalSum to the support-sum statement that `hConverse` expects.
  have h_sum : (∑ x ∈ ((D : Div (ℂ ⧸ L))).supportFinset,
        ((D : Div (ℂ ⧸ L)) : (ℂ ⧸ L) → ℤ) x • x : ℂ ⧸ L) = 0 := hc
  have h_princ : (D : Div (ℂ ⧸ L)) ∈ PrincDiv (ℂ ⧸ L) := hConverse D h_sum
  -- [D] = 0 iff D ∈ (PrincDiv).addSubgroupOf (Div0).
  show (QuotientAddGroup.mk D : Pic0 (ℂ ⧸ L)) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact h_princ

/-! ## Bundled closed-form Abel–Jacobi `AddEquiv` -/

/-- **Closed-form Abel–Jacobi isomorphism `Pic⁰ (ℂ ⧸ L) ≃+ ℂ ⧸ L`** via
`evalSumPic0`. Conditional on `TLDivSumHypothesis L` and
`TLAbelConverseHypothesis L`. Equal as a function to
`pic0EquivComplexTorus` (by `pic0EquivComplexTorus_eq_evalSumPic0`). -/
noncomputable def evalSumPic0Equiv
    (hTL : TLDivSumHypothesis L)
    (hConverse : TLAbelConverseHypothesis L) :
    Pic0 (ℂ ⧸ L) ≃+ (ℂ ⧸ L) :=
  AddEquiv.ofBijective (evalSumPic0 L hTL)
    ⟨evalSumPic0_injective L hTL hConverse,
     evalSumPic0_surjective L hTL⟩

@[simp] lemma evalSumPic0Equiv_apply
    (hTL : TLDivSumHypothesis L)
    (hConverse : TLAbelConverseHypothesis L)
    (c : Pic0 (ℂ ⧸ L)) :
    evalSumPic0Equiv L hTL hConverse c = evalSumPic0 L hTL c := rfl

/-! ## `TLAbelConverseHypothesis` ↔ `EvalSumAbelConverseHypothesis (ℂ⧸L)` -/

/-- **`TLAbelConverseHypothesis L` is the T_L specialization of
`EvalSumAbelConverseHypothesis (ℂ ⧸ L)`.** -/
theorem TLAbelConverseHypothesis_iff_evalSumAbelConverseHypothesis :
    TLAbelConverseHypothesis L ↔ EvalSumAbelConverseHypothesis (ℂ ⧸ L) := Iff.rfl

/-! ## Identification of the general `Pic0.evalSumLiftEquiv` with `evalSumPic0Equiv` on T_L -/

/-- **`Pic0.evalSumLift (ℂ⧸L)` agrees with `evalSumPic0` on T_L.** -/
theorem Pic0_evalSumLift_eq_evalSumPic0
    (hTL : TLDivSumHypothesis L) :
    (Pic0.evalSumLift (ℂ ⧸ L) hTL : Pic0 (ℂ ⧸ L) → (ℂ ⧸ L))
      = evalSumPic0 L hTL := by
  ext c
  induction c using QuotientAddGroup.induction_on with
  | H D =>
  show Pic0.evalSumLift (ℂ ⧸ L) hTL (QuotientAddGroup.mk D)
    = evalSumPic0 L hTL (QuotientAddGroup.mk D)
  rw [Pic0.evalSumLift_mk, evalSumPic0_mk]

/-- **The general `Pic0.evalSumLiftEquiv` and T_L `evalSumPic0Equiv`
agree as functions on T_L.** -/
theorem Pic0_evalSumLiftEquiv_eq_evalSumPic0Equiv
    (hTL : TLDivSumHypothesis L)
    (hConverse : TLAbelConverseHypothesis L) :
    (Pic0.evalSumLiftEquiv (ℂ ⧸ L) hTL hConverse : Pic0 (ℂ ⧸ L) → (ℂ ⧸ L))
      = evalSumPic0Equiv L hTL hConverse := by
  ext c
  show Pic0.evalSumLift (ℂ ⧸ L) hTL c = evalSumPic0 L hTL c
  exact congrFun (Pic0_evalSumLift_eq_evalSumPic0 L hTL) c

end ComplexTorus

end JacobianChallenge

end
