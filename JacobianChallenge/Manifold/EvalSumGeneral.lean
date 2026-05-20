/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.EvalSum
import JacobianChallenge.Divisor.PrincipalDivisorRange
import JacobianChallenge.Manifold.ResidueTheoremUnconditional

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

/-! ## Surjectivity (free on any AddCommGroup `X`)

For any `X` carrying an `AddCommGroup` structure, the map
`Pic0.evalSumLift` is surjective: every `Q ∈ X` is the image of the
class of `single Q − single 0`. -/

/-- **`Pic0.evalSumLift` is surjective** on any compact AddCommGroup
manifold. Every `Q ∈ X` is the image of the class of
`single Q − single (0 : X)`. -/
theorem Pic0.evalSumLift_surjective
    (h : EvalSumAbelHypothesis X) :
    Function.Surjective (Pic0.evalSumLift X h) := by
  classical
  intro Q
  refine ⟨QuotientAddGroup.mk
    ⟨Div.single Q - Div.single (0 : X),
      Div.single_sub_single_mem_Div0 (0 : X) Q⟩, ?_⟩
  rw [Pic0.evalSumLift_mk]
  show Div.evalSum ((Div.single Q - Div.single (0 : X)) : Div X) = Q
  rw [Div.evalSum_single_sub_single, sub_zero]

/-! ## Converse hypothesis + bundled `Pic0 X ≃+ X` -/

/-- **Abel converse hypothesis on `X`**: every degree-zero divisor
whose support-weighted sum vanishes in `X` is principal. T_L
specialization is `TLAbelConverseHypothesis L`. -/
def EvalSumAbelConverseHypothesis : Prop :=
  ∀ D : Div0 X,
    Div.evalSum (D : Div X) = (0 : X) → (D : Div X) ∈ PrincDiv X

/-- **`Pic0.evalSumLift` is injective from the converse hypothesis.** -/
theorem Pic0.evalSumLift_injective
    (h : EvalSumAbelHypothesis X)
    (hConv : EvalSumAbelConverseHypothesis X) :
    Function.Injective (Pic0.evalSumLift X h) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro c hc
  induction c using QuotientAddGroup.induction_on with
  | H D =>
  rw [Pic0.evalSumLift_mk] at hc
  -- hc : Div.evalSum (D : Div X) = 0
  have h_princ : (D : Div X) ∈ PrincDiv X := hConv D hc
  show (QuotientAddGroup.mk D : Pic0 X) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact h_princ

/-- **Closed-form Abel–Jacobi `AddEquiv` `Pic⁰ X ≃+ X`** on any
compact AddCommGroup manifold, conditional on the two named
hypotheses. -/
noncomputable def Pic0.evalSumLiftEquiv
    (h : EvalSumAbelHypothesis X)
    (hConv : EvalSumAbelConverseHypothesis X) :
    Pic0 X ≃+ X :=
  AddEquiv.ofBijective (Pic0.evalSumLift X h)
    ⟨Pic0.evalSumLift_injective X h hConv,
     Pic0.evalSumLift_surjective X h⟩

@[simp] lemma Pic0.evalSumLiftEquiv_apply
    (h : EvalSumAbelHypothesis X)
    (hConv : EvalSumAbelConverseHypothesis X)
    (c : Pic0 X) :
    Pic0.evalSumLiftEquiv X h hConv c = Pic0.evalSumLift X h c := rfl

/-! ## Clean joint characterization

The two named hypotheses together are equivalent to saying that the
divisor-class quotient `Pic0 X` *is* the kernel of `evalSumDiv0Hom`,
i.e. `(PrincDiv X).addSubgroupOf (Div0 X) = ker (Div0.evalSumHom X)`. -/

/-- **Joint characterization.** `EvalSumAbelHypothesis X` and
`EvalSumAbelConverseHypothesis X` together are equivalent to
`(PrincDiv X).addSubgroupOf (Div0 X) = ker (Div0.evalSumHom X)`. -/
theorem PrincDiv_addSubgroupOf_Div0_eq_ker_evalSumDiv0Hom_iff
    [ConnectedSpace X] :
    (PrincDiv X).addSubgroupOf (Div0 X) = (Div0.evalSumHom X).ker ↔
      EvalSumAbelHypothesis X ∧ EvalSumAbelConverseHypothesis X := by
  constructor
  · intro h_eq
    constructor
    · -- Forward direction (Abel): show every principal divisor has evalSum 0.
      intro f
      -- The Div0-element with underlying divisor (f).
      have h_deg : (principalDivisorMap f).degree = 0 := residue_theorem f
      let D : Div0 X := ⟨principalDivisorMap f,
        AddMonoidHom.mem_ker.mpr h_deg⟩
      -- D ∈ (PrincDiv X).addSubgroupOf (Div0 X) since (D : Div X) = (f) ∈ PrincDiv.
      have hD_mem : D ∈ (PrincDiv X).addSubgroupOf (Div0 X) :=
        principalDivisorMap_mem_PrincDiv f
      -- Apply h_eq: D ∈ ker (Div0.evalSumHom X), so evalSum ((D : Div X)) = 0.
      have hD_ker : D ∈ (Div0.evalSumHom X).ker := h_eq ▸ hD_mem
      rw [AddMonoidHom.mem_ker, Div0.evalSumHom_apply] at hD_ker
      exact hD_ker
    · -- Reverse direction (converse): for D ∈ Div0 with evalSum = 0, D is principal.
      intro D hD_sum
      -- D ∈ ker (Div0.evalSumHom X).
      have hD_ker : D ∈ (Div0.evalSumHom X).ker := by
        rw [AddMonoidHom.mem_ker]
        show Div.evalSum (D : Div X) = 0
        exact hD_sum
      -- Apply h_eq.symm: D ∈ (PrincDiv X).addSubgroupOf (Div0 X).
      have hD_princ : D ∈ (PrincDiv X).addSubgroupOf (Div0 X) := h_eq.symm ▸ hD_ker
      exact hD_princ
  · rintro ⟨hAbel, hConv⟩
    apply le_antisymm
    · -- (PrincDiv).addSubgroupOf (Div0) ≤ ker (Div0.evalSumHom).
      intro D hD
      rw [AddMonoidHom.mem_ker, Div0.evalSumHom_apply]
      have h_princ : (D : Div X) ∈ PrincDiv X := hD
      exact evalSumHom_eq_zero_on_PrincDiv_of_evalSumAbelHypothesis X hAbel _ h_princ
    · -- ker (Div0.evalSumHom) ≤ (PrincDiv).addSubgroupOf (Div0).
      intro D hD
      rw [AddMonoidHom.mem_ker, Div0.evalSumHom_apply] at hD
      exact hConv D hD

end JacobianChallenge

end
