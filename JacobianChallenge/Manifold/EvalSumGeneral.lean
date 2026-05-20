/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.EvalSum
import JacobianChallenge.Divisor.PrincipalDivisorRange

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # General `EvalSumAbelHypothesis` and `Pic0.evalSumLift`

This file generalizes the T_L-specific
`TLDivSumHypothesis`/`evalSumPic0` API to **any** compact complex
1-manifold `X` that carries an `AddCommGroup` structure (a complex Lie
group — `T_L` is the canonical example, but everything below applies to
any such `X`).

* `EvalSumAbelHypothesis X` — `∀ f : MeromorphicNonzero X,
  Div.evalSum (principalDivisorMap f) = 0` in `X`.
* `evalSumHom_eq_zero_on_PrincDiv_of_evalSumAbelHypothesis` — free upgrade
  to vanishing on the full closure `PrincDiv X`, via
  `AddSubgroup.closure_induction`.
* `EvalSumAbelHypothesis_iff_PrincDiv_le_ker_evalSumHom` — `Iff` form.
* `Pic0.evalSumLift` — the quotient
  `Pic0 X = Div0 X ⧸ (PrincDiv).addSubgroupOf (Div0)` mapped to `X` by
  `Div.evalSumHom` restricted to `Div0` and descended through the
  quotient. Conditional on `EvalSumAbelHypothesis X`.

These constructions are PLSB-independent — the analytic-period-lattice
infrastructure is hidden, and only the named Abel-type hypothesis on
`EvalSumAbelHypothesis X` is required.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable (X : Type u)
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [AddCommGroup X]

/-- **General `EvalSumAbelHypothesis`** for any compact complex Lie group
manifold `X`: every principal divisor has vanishing support-weighted sum
in `X`. The T_L specialization is `TLDivSumHypothesis L`. -/
def EvalSumAbelHypothesis : Prop :=
  ∀ f : MeromorphicNonzero X,
    Div.evalSum (principalDivisorMap f) = (0 : X)

/-- **Free upgrade to vanishing on the full `PrincDiv X` closure.** -/
theorem evalSumHom_eq_zero_on_PrincDiv_of_evalSumAbelHypothesis
    (h : EvalSumAbelHypothesis X) :
    ∀ D ∈ PrincDiv X, Div.evalSumHom D = (0 : X) := by
  intro D hD
  unfold PrincDiv PrincDivHonestCandidate at hD
  refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ hD
  · rintro x ⟨f, rfl⟩
    exact h f
  · exact map_zero _
  · intro x y _ _ hx hy
    rw [map_add, hx, hy, zero_add]
  · intro x _ hx
    rw [map_neg, hx, neg_zero]

/-- **Kernel-containment Iff form.** -/
theorem evalSumAbelHypothesis_iff_PrincDiv_le_ker_evalSumHom :
    EvalSumAbelHypothesis X ↔
      PrincDiv X ≤ (Div.evalSumHom (X := X)).ker := by
  constructor
  · intro h D hD
    rw [AddMonoidHom.mem_ker]
    exact evalSumHom_eq_zero_on_PrincDiv_of_evalSumAbelHypothesis X h D hD
  · intro h_ker f
    have h_mem : principalDivisorMap f ∈ PrincDiv X :=
      principalDivisorMap_mem_PrincDiv f
    have h_in_ker := h_ker h_mem
    rw [AddMonoidHom.mem_ker] at h_in_ker
    exact h_in_ker

/-! ## Restriction to `Div0 X` and descent to `Pic⁰ X` -/

/-- Restriction of `Div.evalSumHom` to `Div0 X`. -/
noncomputable def Div0.evalSumHom : Div0 X →+ X :=
  Div.evalSumHom.comp (Div0 X).subtype

@[simp] lemma Div0.evalSumHom_apply (D : Div0 X) :
    Div0.evalSumHom X D = Div.evalSum (D : Div X) := rfl

/-- **Closed-form Abel–Jacobi `Pic⁰ X →+ X`** via `evalSum`,
conditional on `EvalSumAbelHypothesis X`. Wraps the quotient of
`Div0.evalSumHom` by `(PrincDiv).addSubgroupOf (Div0)`.

The descent is allowed by
`evalSumHom_eq_zero_on_PrincDiv_of_evalSumAbelHypothesis`. -/
noncomputable def Pic0.evalSumLift
    (h : EvalSumAbelHypothesis X) : Pic0 X →+ X :=
  QuotientAddGroup.lift _ (Div0.evalSumHom X) <| by
    intro D hD
    -- hD : D ∈ (PrincDiv X).addSubgroupOf (Div0 X), i.e. (D : Div X) ∈ PrincDiv X.
    have h_princ : (D : Div X) ∈ PrincDiv X := hD
    exact evalSumHom_eq_zero_on_PrincDiv_of_evalSumAbelHypothesis X h _ h_princ

@[simp] lemma Pic0.evalSumLift_mk
    (h : EvalSumAbelHypothesis X) (D : Div0 X) :
    Pic0.evalSumLift X h (QuotientAddGroup.mk D)
      = Div.evalSum (D : Div X) := rfl

end JacobianChallenge

end
