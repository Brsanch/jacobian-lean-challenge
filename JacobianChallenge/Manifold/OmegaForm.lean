/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PartialZBarManifoldAtChart
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-! # `(0,1)`-forms on a complex 1-manifold (Sub-chip 5.5c-I-a, Route I Option b)

A `(0,1)`-form on a complex 1-manifold `X` is, classically, a smooth
section of the antiholomorphic cotangent bundle `T*^{0,1} X`. The
mathlib pin at this repo does not provide an antiholomorphic cotangent
bundle (mathlib's `Cotangent` encodes the `(1,0)` part, ℂ-linear
cotangent vectors). Per `ROUTE_5_5C_AUDIT.md`'s addendum
recommendation, this file uses **Option (b)**: an in-repo record
encoding without a full bundle.

A value `f : OmegaForm X` carries a chart-coefficient family:

* `f.coeff x : ℂ → ℂ` — the chart-`x` view of `f` as a function on `ℂ`,
  meaningful on `(chartAt ℂ x).target` and junk elsewhere.
* `f.coeff_contDiffOn x` — smoothness of `f.coeff x` on the chart
  target.
* `f.transition hpx hpy` — the `(0,1)`-form chart-change cocycle:
  for `p ∈ chart_x.source ∩ chart_y.source`,
  ```
  f.coeff y ((chartAt ℂ y) p) ·
    conj(deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p))
    = f.coeff x ((chartAt ℂ x) p).
  ```

This is the standard `(0,1)`-form transformation `f^y = f^x /
conj(Φ')` (equivalently `f^x = f^y · conj(Φ')`) where `Φ = chart_y ∘
chart_x.symm`. The conjugate appears because a `(0,1)`-form `f dz̄`
transforms as `dz̄_y = conj(Φ'(z_x)) dz̄_x`, so the coefficient
transforms inversely (and conjugately).

The strategic role this object plays in Chip 5: see the
`ROUTE_5_5C_AUDIT.md` addendum. This file ships only the **record +
algebra + smoothness** scaffold; the function-lift, partition
operation, and ∂̄-inversion land in subsequent sub-chips.

## Naming note

The single-character variable `ω` would collide with the analytic
regularity literal `ω` opened via the `Manifold` scope. Throughout
this file we use `f`, `g`, `h` for `OmegaForm` values.

## What this file ships

* `OmegaForm X` — the record.
* `OmegaForm.transition_at_basepoint` — consistency: at `y = x` the
  transition cocycle is `conj(deriv id) = 1`, trivializing.
* Algebra: `Zero`, `Add`, `Neg`, `Sub` (defined as `add ∘ neg`),
  `SMul ℂ`, `AddCommGroup`, `Module ℂ`.
* `OmegaForm.ext` — extensionality via pointwise coeff equality.

No `sorry`, no `axiom`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff
open Complex

noncomputable section

namespace JacobianChallenge

variable (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- A `(0,1)`-form on a complex 1-manifold `X`, represented as a
chart-coefficient family with smoothness and the `(0,1)` chart-change
cocycle. See file docstring for design notes (Route I, Option b). -/
structure OmegaForm where
  /-- chart-`x` view of the form as a function `ℂ → ℂ`, meaningful on
  `(chartAt ℂ x).target` and junk elsewhere. -/
  coeff : X → (ℂ → ℂ)
  /-- smoothness of each chart-`x` view on the chart target. -/
  coeff_contDiffOn : ∀ x : X, ContDiffOn ℝ ∞ (coeff x) ((chartAt ℂ x).target)
  /-- `(0,1)`-form chart-change cocycle. -/
  transition : ∀ {x y : X} {p : X},
    p ∈ (chartAt ℂ x).source → p ∈ (chartAt ℂ y).source →
    coeff y ((chartAt ℂ y) p) *
      (starRingEnd ℂ)
        (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p))
      = coeff x ((chartAt ℂ x) p)

namespace OmegaForm

variable {X}

/-! ## Extensionality -/

/-- Two `OmegaForm`s are equal iff their `coeff` data agree pointwise. -/
@[ext] theorem ext {f g : OmegaForm X}
    (h : ∀ (x : X) (z : ℂ), f.coeff x z = g.coeff x z) :
    f = g := by
  cases f with
  | mk c₁ _ _ =>
    cases g with
    | mk c₂ _ _ =>
      congr 1
      funext x z
      exact h x z

/-! ## Sanity check: transition at the basepoint -/

/-- At `y = x` the transition cocycle is trivial: `conj(deriv (chart_x
∘ chart_x.symm))(chart_x p) = conj 1 = 1`. -/
lemma transition_at_basepoint
    (f : OmegaForm X) {x p : X} (hp : p ∈ (chartAt ℂ x).source) :
    f.coeff x ((chartAt ℂ x) p) *
      (starRingEnd ℂ)
        (deriv ((chartAt ℂ x) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p))
      = f.coeff x ((chartAt ℂ x) p) :=
  f.transition hp hp

/-! ## Algebra -/

/-- The zero `(0,1)`-form: every chart-coefficient is the constant `0`. -/
instance : Zero (OmegaForm X) where
  zero :=
    { coeff := fun _ _ => 0
      coeff_contDiffOn := fun _ => contDiffOn_const
      transition := by intros; simp }

@[simp] lemma coeff_zero (x : X) (z : ℂ) :
    (0 : OmegaForm X).coeff x z = 0 := rfl

/-- Pointwise sum of two `(0,1)`-forms. The transition cocycle is
preserved by additivity of the coefficient functions. -/
instance : Add (OmegaForm X) where
  add f g :=
    { coeff := fun x z => f.coeff x z + g.coeff x z
      coeff_contDiffOn := fun x =>
        (f.coeff_contDiffOn x).add (g.coeff_contDiffOn x)
      transition := by
        intro x y p hpx hpy
        have h₁ := f.transition hpx hpy
        have h₂ := g.transition hpx hpy
        show (f.coeff y ((chartAt ℂ y) p) + g.coeff y ((chartAt ℂ y) p)) *
              (starRingEnd ℂ)
                (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p))
            = f.coeff x ((chartAt ℂ x) p) + g.coeff x ((chartAt ℂ x) p)
        rw [add_mul, h₁, h₂] }

@[simp] lemma coeff_add (f g : OmegaForm X) (x : X) (z : ℂ) :
    (f + g).coeff x z = f.coeff x z + g.coeff x z := rfl

/-- Pointwise negation of a `(0,1)`-form. -/
instance : Neg (OmegaForm X) where
  neg f :=
    { coeff := fun x z => -f.coeff x z
      coeff_contDiffOn := fun x => (f.coeff_contDiffOn x).neg
      transition := by
        intro x y p hpx hpy
        have h := f.transition hpx hpy
        show -f.coeff y ((chartAt ℂ y) p) *
              (starRingEnd ℂ)
                (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p))
            = -f.coeff x ((chartAt ℂ x) p)
        rw [neg_mul, h] }

@[simp] lemma coeff_neg (f : OmegaForm X) (x : X) (z : ℂ) :
    (-f).coeff x z = -f.coeff x z := rfl

/-- Pointwise difference, defined as `f + (-g)` so that `sub_eq_add_neg`
holds definitionally. -/
instance : Sub (OmegaForm X) where
  sub f g := f + (-g)

@[simp] lemma coeff_sub (f g : OmegaForm X) (x : X) (z : ℂ) :
    (f - g).coeff x z = f.coeff x z - g.coeff x z := by
  show (f + (-g)).coeff x z = f.coeff x z - g.coeff x z
  simp [sub_eq_add_neg]

/-- Scalar multiplication of a `(0,1)`-form by a constant `c : ℂ`. The
transition cocycle is preserved by `(c · a) · t = c · (a · t)`. -/
instance : SMul ℂ (OmegaForm X) where
  smul c f :=
    { coeff := fun x z => c * f.coeff x z
      coeff_contDiffOn := fun x => (f.coeff_contDiffOn x).const_smul c
      transition := by
        intro x y p hpx hpy
        have h := f.transition hpx hpy
        show c * f.coeff y ((chartAt ℂ y) p) *
              (starRingEnd ℂ)
                (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) p))
            = c * f.coeff x ((chartAt ℂ x) p)
        rw [mul_assoc, h] }

@[simp] lemma coeff_smul (c : ℂ) (f : OmegaForm X) (x : X) (z : ℂ) :
    (c • f).coeff x z = c * f.coeff x z := rfl

/-! ## `AddCommGroup` and `Module ℂ` instances

Built up by `ext` + `simp` on the coeff data, which carries the
algebraic structure of `X → (ℂ → ℂ)`. -/

instance : AddCommGroup (OmegaForm X) where
  add_assoc f g h := by ext x z; simp [add_assoc]
  zero_add f := by ext x z; simp
  add_zero f := by ext x z; simp
  add_comm f g := by ext x z; simp [add_comm]
  neg_add_cancel f := by ext x z; simp
  sub_eq_add_neg f g := rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module ℂ (OmegaForm X) where
  one_smul f := by ext x z; show (1 : ℂ) * f.coeff x z = f.coeff x z; ring
  mul_smul a b f := by
    ext x z
    show (a * b) * f.coeff x z = a * (b * f.coeff x z)
    ring
  smul_zero c := by ext x z; show c * 0 = 0; ring
  smul_add c f g := by
    ext x z
    show c * (f.coeff x z + g.coeff x z) = c * f.coeff x z + c * g.coeff x z
    ring
  add_smul a b f := by
    ext x z
    show (a + b) * f.coeff x z = a * f.coeff x z + b * f.coeff x z
    ring
  zero_smul f := by ext x z; show (0 : ℂ) * f.coeff x z = 0; ring

end OmegaForm

end JacobianChallenge

end
