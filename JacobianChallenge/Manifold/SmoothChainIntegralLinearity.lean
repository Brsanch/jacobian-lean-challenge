/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import JacobianChallenge.Manifold.SmoothChain
import JacobianChallenge.Manifold.SmoothOneForm
import JacobianChallenge.Manifold.SmoothPathIntegral

/-! # Full ℤ-linearity of the smooth-chain path integral (chain side)

`SmoothPathIntegral.lean` (ZZ139) defines

  `SmoothChain.integrate : SmoothChain I X → SmoothOneForm I X → ℝ`

with the basic identities `integrate_zero`, `integrate_single`,
`integrate_add` (all chain-side). What is *not* yet on tree is the
remaining algebraic structure on the chain argument — negation,
subtraction, integer scalar action — and the packaging as an honest
`SmoothChain I X →ₗ[ℤ] ℝ` for each fixed smooth 1-form `oneForm`. This
file closes that gap.

On the form side, we additionally derive the unconditional
*scalar-multiplication* identity

  `integrate c (a • oneForm) = a * integrate c oneForm`,

which follows directly from `SmoothPath.integrate_smul` (ZZ139, no
integrability hypothesis) summed over the finite chain support. The
*addition* identity in the form argument still requires per-summand
`IntervalIntegrable` hypotheses (it factors through
`SmoothPath.integrate_add`), so we do **not** ship a
`SmoothOneForm-side` `→ₗ[ℝ]` here — that would silently demand
integrability the API does not yet expose.

## Main definitions

* `SmoothChain.integrateLinearMap oneForm : SmoothChain I X →ₗ[ℤ] ℝ` —
  the chain-side ℤ-linear map sending `c ↦ SmoothChain.integrate c oneForm`,
  for a fixed smooth 1-form `oneForm`.

## Main lemmas

Chain-side identities (no integrability hypotheses):

* `SmoothChain.integrate_neg` — `integrate (-c) ω = - integrate c ω`.
* `SmoothChain.integrate_sub` — `integrate (c₁ - c₂) ω = integrate c₁ ω - integrate c₂ ω`.
* `SmoothChain.integrate_zsmul` — `integrate (n • c) ω = n • integrate c ω`
  for `n : ℤ`.

Form-side scalar identity (no integrability hypothesis):

* `SmoothChain.integrate_smul_form` — `integrate c (a • ω) = a * integrate c ω`
  for `a : ℝ`.

API on the bundled `integrateLinearMap`:

* `SmoothChain.integrateLinearMap_apply` — definitional unfolding.
* `SmoothChain.integrateLinearMap_single` — single-path evaluation.

## Design notes

The chain-side ℤ-linearity is *automatic* in the abstract sense
(`AddCommGroup → ℤ-module` always) once we have the additive-hom
structure provided by `integrate_add` and `integrate_zero` (already on
tree). The point of the explicit lemmas below is to give downstream
files stable `@[simp]` names instead of forcing them to rebuild
negation/subtraction/zsmul from `Finsupp` each time.

The form-side scalar lemma is the second of the four ingredients that a
period-lattice construction will need; the missing pieces (form
additivity unconditionally, complex-linear pairing on
`HolomorphicOneForm`, Stokes for closed forms) all require strictly
more analytic infrastructure than is on tree at the current pin and are
deliberately deferred. See `PeriodPairingFromSmoothChain.lean` for the
companion chain-fixed `AddMonoidHom` shape; this file delivers the
dual ℤ-linear-map shape and the form-scalar identity.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

set_option diagnostics.threshold 100

namespace SmoothChain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

/-- Negation in the chain argument: `∫_{-c} ω = -∫_c ω`. -/
@[simp] theorem integrate_neg (c : SmoothChain I X) (oneForm : SmoothOneForm I X) :
    integrate (-c) oneForm = - integrate c oneForm := by
  -- `-c = (-1) • c` plus `integrate_add` on `c + (-c) = 0`.
  have h := integrate_add c (-c) oneForm
  rw [add_neg_cancel, integrate_zero] at h
  linarith

/-- Subtraction in the chain argument:
`∫_{c₁ - c₂} ω = ∫_{c₁} ω - ∫_{c₂} ω`. -/
@[simp] theorem integrate_sub (c₁ c₂ : SmoothChain I X)
    (oneForm : SmoothOneForm I X) :
    integrate (c₁ - c₂) oneForm = integrate c₁ oneForm - integrate c₂ oneForm := by
  rw [sub_eq_add_neg, integrate_add, integrate_neg, sub_eq_add_neg]

/-- Integer scalar action in the chain argument on a natural number `m`:
follows by induction on `m` from `integrate_add`. Helper lemma for
`integrate_zsmul`. -/
private theorem integrate_natCast_zsmul (m : ℕ) (c : SmoothChain I X)
    (oneForm : SmoothOneForm I X) :
    integrate (((m : ℤ)) • c) oneForm = ((m : ℤ)) • integrate c oneForm := by
  induction m with
  | zero =>
    -- Both sides reduce to `0` after `Nat.cast_zero` and `zero_smul`.
    show integrate ((((0 : ℕ) : ℤ)) • c) oneForm
        = (((0 : ℕ) : ℤ)) • integrate c oneForm
    rw [show (((0 : ℕ) : ℤ)) • c = (0 : SmoothChain I X) by
          push_cast; exact zero_smul _ _,
        show (((0 : ℕ) : ℤ)) • integrate c oneForm = (0 : ℝ) by
          push_cast; exact zero_smul _ _,
        integrate_zero]
  | succ k ih =>
    have hsucc : ((k.succ : ℕ) : ℤ) • c = ((k : ℕ) : ℤ) • c + c := by
      show ((k + 1 : ℕ) : ℤ) • c = _
      push_cast
      module
    have hRHS : ((k.succ : ℕ) : ℤ) • integrate c oneForm
        = ((k : ℕ) : ℤ) • integrate c oneForm + integrate c oneForm := by
      show ((k + 1 : ℕ) : ℤ) • _ = _
      push_cast
      module
    rw [hsucc, integrate_add, ih, hRHS]

/-- Integer scalar action in the chain argument:
`∫_{n • c} ω = n • ∫_c ω` for `n : ℤ`. -/
@[simp] theorem integrate_zsmul (n : ℤ) (c : SmoothChain I X)
    (oneForm : SmoothOneForm I X) :
    integrate (n • c) oneForm = n • integrate c oneForm := by
  rcases n with m | m
  · -- `n = (m : ℕ)` as a non-negative integer.
    exact integrate_natCast_zsmul m c oneForm
  · -- `n = Int.negSucc m`. Both sides reduce via `Int.negSucc_eq` and `neg_smul`.
    have hLHS : (Int.negSucc m) • c = -(((m + 1 : ℕ) : ℤ) • c) := by
      rw [Int.negSucc_eq]
      rw [show -(((m : ℤ)) + 1) = -(((m + 1 : ℕ) : ℤ)) by push_cast; ring]
      exact neg_smul _ _
    have hRHS : (Int.negSucc m) • integrate c oneForm
        = -(((m + 1 : ℕ) : ℤ) • integrate c oneForm) := by
      rw [Int.negSucc_eq]
      rw [show -(((m : ℤ)) + 1) = -(((m + 1 : ℕ) : ℤ)) by push_cast; ring]
      exact neg_smul _ _
    rw [hLHS, integrate_neg, integrate_natCast_zsmul, hRHS]

/-- The chain-side ℤ-linear map: for fixed smooth 1-form `oneForm`, the map
`c ↦ ∫_c oneForm` is an honest `SmoothChain I X →ₗ[ℤ] ℝ`. -/
def integrateLinearMap (oneForm : SmoothOneForm I X) :
    SmoothChain I X →ₗ[ℤ] ℝ where
  toFun c := integrate c oneForm
  map_add' c₁ c₂ := integrate_add c₁ c₂ oneForm
  map_smul' n c := by
    show integrate (n • c) oneForm = n • integrate c oneForm
    exact integrate_zsmul n c oneForm

@[simp] theorem integrateLinearMap_apply (oneForm : SmoothOneForm I X)
    (c : SmoothChain I X) :
    integrateLinearMap oneForm c = integrate c oneForm := rfl

@[simp] theorem integrateLinearMap_single (oneForm : SmoothOneForm I X)
    (γ : SmoothPath I X) :
    integrateLinearMap oneForm (SmoothChain.single γ) = γ.integrate oneForm := by
  rw [integrateLinearMap_apply, integrate_single]

@[simp] theorem integrateLinearMap_zero_left (oneForm : SmoothOneForm I X) :
    integrateLinearMap oneForm (0 : SmoothChain I X) = 0 := by
  rw [integrateLinearMap_apply, integrate_zero]

@[simp] theorem integrateLinearMap_zero_right (c : SmoothChain I X) :
    integrateLinearMap (0 : SmoothOneForm I X) c = 0 := by
  classical
  rw [integrateLinearMap_apply]
  -- Unfold the chain integral and use `SmoothPath.integrate_zero` on each summand.
  unfold integrate asFinsupp
  refine Finset.sum_eq_zero ?_
  intro γ _
  rw [SmoothPath.integrate_zero]
  ring

/-- Form-side scalar identity (no integrability hypothesis):
`∫_c (a • oneForm) = a * ∫_c oneForm`. The proof uses `SmoothPath.integrate_smul`
summand-by-summand on the finite chain support — no path integrability
hypotheses needed because scalar multiplication factors out of `intervalIntegral`
unconditionally. -/
theorem integrate_smul_form (c : SmoothChain I X) (a : ℝ)
    (oneForm : SmoothOneForm I X) :
    integrate c (a • oneForm) = a * integrate c oneForm := by
  classical
  unfold integrate asFinsupp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro γ _
  rw [SmoothPath.integrate_smul]
  ring

/-- The companion form-side identity at the level of the bundled linear map:
scaling the form scales the linear map's value. -/
@[simp] theorem integrateLinearMap_smul_form (c : SmoothChain I X) (a : ℝ)
    (oneForm : SmoothOneForm I X) :
    integrateLinearMap (a • oneForm) c = a * integrateLinearMap oneForm c := by
  simp [integrate_smul_form]

/-- Negation in the form argument is unconditional (no integrability needed):
`∫_c (- oneForm) = - ∫_c oneForm`. -/
@[simp] theorem integrate_neg_form (c : SmoothChain I X)
    (oneForm : SmoothOneForm I X) :
    integrate c (- oneForm) = - integrate c oneForm := by
  have h := integrate_smul_form c (-1 : ℝ) oneForm
  simp [neg_smul, one_smul] at h
  linarith

end SmoothChain

namespace SmoothPath

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

/-- Negation in the form argument for a single smooth path:
`∫_γ (- oneForm) = - ∫_γ oneForm`. Follows from `SmoothPath.integrate_smul`
at scalar `-1`. -/
@[simp] theorem integrate_neg_form (γ : SmoothPath I X)
    (oneForm : SmoothOneForm I X) :
    γ.integrate (- oneForm) = - γ.integrate oneForm := by
  have h := γ.integrate_smul (-1 : ℝ) oneForm
  simp [neg_smul, one_smul] at h
  linarith

end SmoothPath

end
