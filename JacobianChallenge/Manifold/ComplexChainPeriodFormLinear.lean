/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiPath
import JacobianChallenge.Manifold.SmoothPathIntegrability
import JacobianChallenge.Manifold.HolomorphicOneFormRealComponentLinear
import JacobianChallenge.Manifold.SmoothPathIntegrateReverse
import JacobianChallenge.Manifold.SmoothPathIntegrateConcat

/-! # Form-side linearity for `complexChainPeriod`

`complexChainPeriod c om : ℂ` (from
`Manifold/AbelJacobiPath.lean`) is the complex period of a holomorphic
1-form `om` along a smooth 1-chain `c`. The chain-argument linearity
(zero / add / neg / sub) is already in `AbelJacobiPath.lean`; this file
provides the **form-argument** linearity:

* `complexChainPeriod_zero_right : complexChainPeriod c 0 = 0`
* `complexChainPeriod_add_right :
    complexChainPeriod c (om₁ + om₂)
      = complexChainPeriod c om₁ + complexChainPeriod c om₂`
* `complexChainPeriod_neg_right :
    complexChainPeriod c (-om) = -complexChainPeriod c om`
* `complexChainPeriod_sub_right :
    complexChainPeriod c (om₁ - om₂)
      = complexChainPeriod c om₁ - complexChainPeriod c om₂`

These are the chain-level analogs of `complexPeriod_add_right` etc. in
`Manifold/ComplexPeriodPairing.lean` (which restrict to cycles). The
proofs follow the same template: unfold `complexChainPeriod`, push the
form-side linearity through `realComponent` / `imagComponent` (via the
PL-3d lemmas in `HolomorphicOneFormRealComponentLinear.lean`), then
through `SmoothChain.integrate_add_form` (PL-3e, in
`SmoothPathIntegrability.lean`), and finally `push_cast; ring`.

These linearity lemmas underpin downstream identities of the form
`complexChainPeriod c (linear combination of om_i) =
  sum of complexChainPeriod c om_i`,  needed for any algebraic
manipulation of holomorphic 1-form periods at the chain level.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology Bundle ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Form-side zero of `complexChainPeriod`.** -/
@[simp] lemma complexChainPeriod_zero_right
    (c : SmoothChain 𝓘(ℝ, ℂ) X) :
    complexChainPeriod c (0 : HolomorphicOneForm X) = 0 := by
  unfold complexChainPeriod
  -- realComponent 0 = 0 and imagComponent 0 = 0 (PL-3d).
  have h_re_zero : realComponent (0 : HolomorphicOneForm X)
      = (0 : SmoothOneForm 𝓘(ℝ, ℂ) X) := realComponent_zero
  have h_im_zero : imagComponent (0 : HolomorphicOneForm X)
      = (0 : SmoothOneForm 𝓘(ℝ, ℂ) X) := imagComponent_zero
  rw [h_re_zero, h_im_zero]
  -- `SmoothChain.integrate c (0 : SmoothOneForm _ _) = 0` via the pairing API.
  have h_chain_zero :
      SmoothChain.integrate c (0 : SmoothOneForm 𝓘(ℝ, ℂ) X) = 0 :=
    smoothChain_realOneForm_pairing_zero_right c
  rw [h_chain_zero]
  push_cast
  ring

/-- **Form-side additivity of `complexChainPeriod`.** -/
lemma complexChainPeriod_add_right
    (c : SmoothChain 𝓘(ℝ, ℂ) X) (om₁ om₂ : HolomorphicOneForm X) :
    complexChainPeriod c (om₁ + om₂)
      = complexChainPeriod c om₁ + complexChainPeriod c om₂ := by
  unfold complexChainPeriod
  rw [realComponent_add, imagComponent_add,
      SmoothChain.integrate_add_form, SmoothChain.integrate_add_form]
  push_cast
  ring

/-- **Form-side negation of `complexChainPeriod`.** -/
lemma complexChainPeriod_neg_right
    (c : SmoothChain 𝓘(ℝ, ℂ) X) (om : HolomorphicOneForm X) :
    complexChainPeriod c (-om) = -complexChainPeriod c om := by
  -- From (-om) + om = 0, deduce complexChainPeriod c (-om) + complexChainPeriod c om = 0
  -- and hence complexChainPeriod c (-om) = -(complexChainPeriod c om).
  have h_sum_zero : complexChainPeriod c (-om + om) = 0 := by
    rw [neg_add_cancel]; exact complexChainPeriod_zero_right c
  have h_split : complexChainPeriod c (-om + om)
      = complexChainPeriod c (-om) + complexChainPeriod c om :=
    complexChainPeriod_add_right c (-om) om
  have h_add_zero :
      complexChainPeriod c (-om) + complexChainPeriod c om = 0 := by
    rw [← h_split]; exact h_sum_zero
  exact eq_neg_of_add_eq_zero_left h_add_zero

/-- **Form-side subtraction of `complexChainPeriod`.** -/
lemma complexChainPeriod_sub_right
    (c : SmoothChain 𝓘(ℝ, ℂ) X) (om₁ om₂ : HolomorphicOneForm X) :
    complexChainPeriod c (om₁ - om₂)
      = complexChainPeriod c om₁ - complexChainPeriod c om₂ := by
  rw [sub_eq_add_neg, complexChainPeriod_add_right,
      complexChainPeriod_neg_right]
  ring

/-- **Form-side `ℝ`-scalar of `complexChainPeriod`.** -/
lemma complexChainPeriod_smul_real_right
    (c : SmoothChain 𝓘(ℝ, ℂ) X) (a : ℝ) (om : HolomorphicOneForm X) :
    complexChainPeriod c (a • om) = (a : ℂ) * complexChainPeriod c om := by
  unfold complexChainPeriod
  rw [realComponent_smul_real, imagComponent_smul_real,
      SmoothChain.integrate_smul_form, SmoothChain.integrate_smul_form]
  push_cast
  ring

/-- **Form-side as an `AddMonoidHom`.** With the chain held fixed,
`complexChainPeriod c · : HolomorphicOneForm X →+ ℂ` is an additive
group homomorphism. (Full ℂ-linearity is not in scope here — that
mixes `realComponent` and `imagComponent` via the
`realPart (z • _) = Re z · realPart _ - Im z · imagPart _` identity,
which is a separate `ℝ ↔ ℂ` mixing chip.) -/
def complexChainPeriodHomRight
    (c : SmoothChain 𝓘(ℝ, ℂ) X) :
    HolomorphicOneForm X →+ ℂ where
  toFun om := complexChainPeriod c om
  map_zero' := complexChainPeriod_zero_right c
  map_add' om₁ om₂ := complexChainPeriod_add_right c om₁ om₂

@[simp] lemma complexChainPeriodHomRight_apply
    (c : SmoothChain 𝓘(ℝ, ℂ) X) (om : HolomorphicOneForm X) :
    complexChainPeriodHomRight c om = complexChainPeriod c om := rfl

/-! ## Single-path operations on `complexChainPeriod` -/

/-- **Reverse-path negates `complexChainPeriod` of a single-path chain.**
The complex period of a holomorphic 1-form along a reversed smooth path
is the negative of the period along the original path. -/
lemma complexChainPeriod_single_reverse
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) (om : HolomorphicOneForm X) :
    complexChainPeriod (SmoothChain.single γ.reverse) om
      = -complexChainPeriod (SmoothChain.single γ) om := by
  unfold complexChainPeriod
  simp only [SmoothChain.integrate_single,
    SmoothPath.integrate_reverse]
  push_cast
  ring

/-- **Concatenation-path is additive in `complexChainPeriod` of single chains.**
The complex period along the concatenation `γ.concat δ h` decomposes as
the sum of the periods along `γ` and `δ`. -/
lemma complexChainPeriod_single_concat
    (γ δ : SmoothPath 𝓘(ℝ, ℂ) X) (h : γ.tgt = δ.src)
    (om : HolomorphicOneForm X) :
    complexChainPeriod (SmoothChain.single (γ.concat δ h)) om
      = complexChainPeriod (SmoothChain.single γ) om
        + complexChainPeriod (SmoothChain.single δ) om := by
  unfold complexChainPeriod
  simp only [SmoothChain.integrate_single,
    SmoothPath.integrate_concat]
  push_cast
  ring

end JacobianChallenge

end
