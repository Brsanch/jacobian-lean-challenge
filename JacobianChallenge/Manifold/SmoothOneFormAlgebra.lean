/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothOneForm

/-! # Pointwise algebraic identities for `SmoothOneForm`

This file collects the pointwise evaluation lemmas that pin the
`AddCommGroup` / `Module ℝ` structure on `SmoothOneForm I X` (inherited
from `ContMDiffSection`) to the fibrewise operations on
`CotangentSpace I x`. These are the analogue, for smooth real
1-forms, of the standard `Pi.add_apply`, `Pi.zero_apply`, `Pi.smul_apply`
lemmas that every linear-algebra pipeline relies on.

These lemmas already appear *inline* — as anonymous `rfl` rewrites — in
`SmoothPathIntegral.lean` (e.g. lines 146, 153, 160). Lifting them to
named `@[simp]` lemmas eliminates those inline rewrites in downstream
chips (`PeriodPairingFromSmoothChain`, the period-lattice closure of
item 5, etc.) and is the algebraic backbone of the
period-integral / period-lattice / Jacobian item-5 chain.

## Main lemmas

* `SmoothOneForm.zero_eval` — `(0 : SmoothOneForm I X) x = 0`.
* `SmoothOneForm.add_eval` — `(ω₁ + ω₂) x = ω₁ x + ω₂ x`.
* `SmoothOneForm.neg_eval` — `(-ω) x = -(ω x)`.
* `SmoothOneForm.sub_eval` — `(ω₁ - ω₂) x = ω₁ x - ω₂ x`.
* `SmoothOneForm.smul_eval` — `(c • ω) x = c • (ω x)`.
* `SmoothOneForm.nsmul_eval` — `(n • ω) x = n • (ω x)` for `n : ℕ`.
* `SmoothOneForm.zsmul_eval` — `(n • ω) x = n • (ω x)` for `n : ℤ`.

All are by `rfl`: the `AddCommGroup` / `Module ℝ` instances on
`SmoothOneForm I X` are `inferInstanceAs` copies of those on the
underlying `ContMDiffSection`, whose group / module operations are
defined pointwise. The coercion to `(x : X) → CotangentSpace I x` is
likewise the underlying `ContMDiffSection` coercion. Hence the right-
hand side of each identity reduces to the left-hand side definitionally.

## Design notes

We deliberately do *not* state an `ext`-style extensionality lemma
here: the underlying `ContMDiffSection` is *not* a function type
quotient (it is a structure carrying a smoothness witness), so two
sections that agree pointwise need not be propositionally equal at the
structure level. Extensionality is therefore deferred to a later chip
that exposes a constructor / projection API on `ContMDiffSection`.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

namespace SmoothOneForm

@[simp] lemma zero_eval (x : X) :
    (0 : SmoothOneForm I X) x = (0 : CotangentSpace I x) := rfl

@[simp] lemma add_eval (ω₁ ω₂ : SmoothOneForm I X) (x : X) :
    (ω₁ + ω₂) x = ω₁ x + ω₂ x := rfl

@[simp] lemma neg_eval (ω₁ : SmoothOneForm I X) (x : X) :
    (-ω₁) x = -(ω₁ x) := rfl

@[simp] lemma sub_eval (ω₁ ω₂ : SmoothOneForm I X) (x : X) :
    (ω₁ - ω₂) x = ω₁ x - ω₂ x := rfl

@[simp] lemma smul_eval (c : ℝ) (ω₁ : SmoothOneForm I X) (x : X) :
    (c • ω₁) x = c • (ω₁ x) := rfl

@[simp] lemma nsmul_eval (n : ℕ) (ω₁ : SmoothOneForm I X) (x : X) :
    (n • ω₁) x = n • (ω₁ x) := rfl

@[simp] lemma zsmul_eval (n : ℤ) (ω₁ : SmoothOneForm I X) (x : X) :
    (n • ω₁) x = n • (ω₁ x) := rfl

/-- Doubling a smooth 1-form: `(2 • ω) x = ω x + ω x`. A convenience
restatement of `nsmul_eval` at `n = 2`, useful when downstream rewrites
expect the `+` form rather than the `•` form. -/
lemma two_nsmul_eval (ω₁ : SmoothOneForm I X) (x : X) :
    ((2 : ℕ) • ω₁) x = ω₁ x + ω₁ x := by
  rw [nsmul_eval]; exact two_nsmul _

/-- Compatibility: scalar multiplication by `0 : ℝ` evaluates to
`0 : CotangentSpace I x`. Follows from `smul_eval` and `zero_smul`. -/
@[simp] lemma zero_smul_eval (ω₁ : SmoothOneForm I X) (x : X) :
    ((0 : ℝ) • ω₁) x = (0 : CotangentSpace I x) := by
  rw [smul_eval, zero_smul]

/-- Compatibility: scalar multiplication by `1 : ℝ` is the identity at
each point. Follows from `smul_eval` and `one_smul`. -/
@[simp] lemma one_smul_eval (ω₁ : SmoothOneForm I X) (x : X) :
    ((1 : ℝ) • ω₁) x = ω₁ x := by
  rw [smul_eval, one_smul]

/-- Associativity of scalar multiplication at a point. -/
lemma smul_smul_eval (a b : ℝ) (ω₁ : SmoothOneForm I X) (x : X) :
    ((a * b) • ω₁) x = a • ((b • ω₁) x) := by
  rw [smul_eval, smul_eval, mul_smul]

/-- Distributivity of scalar multiplication over a sum at a point. -/
lemma smul_add_eval (c : ℝ) (ω₁ ω₂ : SmoothOneForm I X) (x : X) :
    (c • (ω₁ + ω₂)) x = c • (ω₁ x) + c • (ω₂ x) := by
  rw [smul_eval, add_eval, smul_add]

/-- Distributivity of scalar multiplication over a real-scalar sum at
a point. -/
lemma add_smul_eval (a b : ℝ) (ω₁ : SmoothOneForm I X) (x : X) :
    ((a + b) • ω₁) x = a • (ω₁ x) + b • (ω₁ x) := by
  rw [smul_eval, add_smul]

/-- Subtraction expressed via addition and negation at a point. -/
lemma sub_eq_add_neg_eval (ω₁ ω₂ : SmoothOneForm I X) (x : X) :
    (ω₁ - ω₂) x = ω₁ x + -(ω₂ x) := by
  rw [sub_eval, sub_eq_add_neg]

/-- Self-cancellation: `ω - ω = 0` at every point. -/
@[simp] lemma sub_self_eval (ω₁ : SmoothOneForm I X) (x : X) :
    (ω₁ - ω₁) x = (0 : CotangentSpace I x) := by
  rw [sub_eval, sub_self]

/-- Negation of negation at a point. -/
@[simp] lemma neg_neg_eval (ω₁ : SmoothOneForm I X) (x : X) :
    (- -ω₁) x = ω₁ x := by
  rw [neg_eval, neg_eval, neg_neg]

/-- The zero one-form is its own negation at every point. -/
@[simp] lemma neg_zero_eval (x : X) :
    (-(0 : SmoothOneForm I X)) x = (0 : CotangentSpace I x) := by
  rw [neg_eval, zero_eval, neg_zero]

end SmoothOneForm

end
