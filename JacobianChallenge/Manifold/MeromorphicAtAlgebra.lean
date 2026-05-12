/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicAt

set_option diagnostics.threshold 100

/-! # Order arithmetic for `MMeromorphicAt`

Companion to `JacobianChallenge.Manifold.MeromorphicAt`. The base file
defines `mmeromorphicOrderAt` as a chart-pullback of mathlib's
`meromorphicOrderAt`, and supplies algebraic closure of `MMeromorphicAt`
under add / sub / neg / mul / inv / div / pow / zpow / scalar mul.

This file collects the **order-level identities and inequalities** that
downstream consumers (zero/pole counting, divisor algebra, residue
arithmetic) need. Each result is a chart-pullback of an existing mathlib
`meromorphicOrderAt_*` lemma; no new mathematical content is introduced.

## Main results

* `mmeromorphicOrderAt_zero`     — order of the constant `0` is `⊤`.
* `mmeromorphicOrderAt_one`      — order of the constant `1` is `0`.
* `mmeromorphicOrderAt_const`    — order of a constant function: `⊤` or `0`.
* `mmeromorphicOrderAt_neg`      — `mmeromorphicOrderAt I (-f) x = mmeromorphicOrderAt I f x`.
* `mmeromorphicOrderAt_mul`      — `mmeromorphicOrderAt I (f * g) x = · + ·`.
* `mmeromorphicOrderAt_inv`      — `mmeromorphicOrderAt I f⁻¹ x = - mmeromorphicOrderAt I f x`.
* `mmeromorphicOrderAt_div`      — order of a quotient is the difference of orders.
* `mmeromorphicOrderAt_add_ge`   — `min ≤ mmeromorphicOrderAt I (f + g) x`.
* `mmeromorphicOrderAt_sub_ge`   — `min ≤ mmeromorphicOrderAt I (f - g) x`.

All hypotheses are `MMeromorphicAt I _ x` of the relevant factors, mirroring
the mathlib pattern.
-/

noncomputable section

open scoped Manifold Topology

namespace JacobianChallenge

universe u

variable {M : Type u}
variable [TopologicalSpace M] [ChartedSpace ℂ M]
variable {I : ModelWithCorners ℂ ℂ ℂ}
variable {f g : M → ℂ} {x : M}

/-! ## Order at constants -/

/-- The order of the constant-zero function at any point is `⊤`. -/
@[simp] lemma mmeromorphicOrderAt_zero :
    mmeromorphicOrderAt I (0 : M → ℂ) x = ⊤ := by
  -- Reduce to `meromorphicOrderAt (fun _ => 0) ((chartAt ℂ x) x) = ⊤`.
  show meromorphicOrderAt ((0 : M → ℂ) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = ⊤
  have h : (0 : M → ℂ) ∘ (chartAt ℂ x).symm = (fun _ : ℂ => (0 : ℂ)) := rfl
  rw [h]
  classical
  have := meromorphicOrderAt_const (𝕜 := ℂ) (E := ℂ) ((chartAt ℂ x) x) (0 : ℂ)
  simpa using this

/-- The order of the constant function `c` at any point is `⊤` if `c = 0`
and `0` otherwise. -/
lemma mmeromorphicOrderAt_const (c : ℂ) :
    mmeromorphicOrderAt I (fun _ : M => c) x =
      if c = 0 then (⊤ : WithTop ℤ) else (0 : WithTop ℤ) := by
  show meromorphicOrderAt ((fun _ : M => c) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = _
  have h : (fun _ : M => c) ∘ (chartAt ℂ x).symm = (fun _ : ℂ => c) := rfl
  rw [h]
  classical
  exact meromorphicOrderAt_const (𝕜 := ℂ) (E := ℂ) ((chartAt ℂ x) x) c

/-- The order of the constant function `1` is `0`. -/
@[simp] lemma mmeromorphicOrderAt_one_const :
    mmeromorphicOrderAt I (fun _ : M => (1 : ℂ)) x = 0 := by
  rw [mmeromorphicOrderAt_const]
  simp

/-! ## Order under ring operations

  `mmeromorphicOrderAt_one`, `_mul`, `_inv` already live in
  `Divisor/PrincipalDivisor.lean` (lines 166/185/220). This file no longer
  duplicates them. -/

/-- The order of a quotient equals the difference of the orders. -/
lemma mmeromorphicOrderAt_div
    (hf : MMeromorphicAt I f x) (hg : MMeromorphicAt I g x) :
    mmeromorphicOrderAt I (f / g) x =
      mmeromorphicOrderAt I f x - mmeromorphicOrderAt I g x := by
  have hf' : MeromorphicAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hf
  have hg' : MeromorphicAt (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hg
  show meromorphicOrderAt ((f / g) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = _
  have h : (f / g) ∘ (chartAt ℂ x).symm
      = (f ∘ (chartAt ℂ x).symm) / (g ∘ (chartAt ℂ x).symm) := rfl
  rw [h]
  exact meromorphicOrderAt_div hf' hg'

/-- The order of `-f` equals the order of `f`. Derived from
`meromorphicOrderAt_smul_of_ne_zero` with the nonzero constant `-1`,
which is unconditional in `f`. -/
lemma mmeromorphicOrderAt_neg :
    mmeromorphicOrderAt I (-f) x = mmeromorphicOrderAt I f x := by
  show meromorphicOrderAt ((-f) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
        = meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  have h_comp : (-f) ∘ (chartAt ℂ x).symm = -(f ∘ (chartAt ℂ x).symm) := rfl
  rw [h_comp]
  set F : ℂ → ℂ := f ∘ (chartAt ℂ x).symm
  -- Rewrite `-F` as the scalar action of the constant function `-1`.
  have h_smul : (-F) = ((fun _ : ℂ => (-1 : ℂ)) • F) := by
    funext z
    simp [Pi.smul_apply', smul_eq_mul, neg_one_mul]
  rw [h_smul]
  -- Apply the unit-constant smul-order identity; this is unconditional (mathlib handles
  -- the non-meromorphic branch internally via `meromorphicOrderAt_of_not_meromorphicAt`).
  have h_const_an : AnalyticAt ℂ (fun _ : ℂ => (-1 : ℂ)) ((chartAt ℂ x) x) :=
    analyticAt_const
  have h_const_ne : (fun _ : ℂ => (-1 : ℂ)) ((chartAt ℂ x) x) ≠ 0 := by
    simp
  exact meromorphicOrderAt_smul_of_ne_zero (g := fun _ : ℂ => (-1 : ℂ))
    (f := F) (x := (chartAt ℂ x) x) h_const_an h_const_ne

/-! ## Order under addition / subtraction -/

/-- The order of a sum is at least the minimum of the orders of the summands. -/
lemma mmeromorphicOrderAt_add_ge
    (hf : MMeromorphicAt I f x) (hg : MMeromorphicAt I g x) :
    min (mmeromorphicOrderAt I f x) (mmeromorphicOrderAt I g x)
      ≤ mmeromorphicOrderAt I (f + g) x := by
  have hf' : MeromorphicAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hf
  have hg' : MeromorphicAt (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hg
  show min (meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
           (meromorphicOrderAt (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
        ≤ meromorphicOrderAt ((f + g) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  have h : (f + g) ∘ (chartAt ℂ x).symm
      = (f ∘ (chartAt ℂ x).symm) + (g ∘ (chartAt ℂ x).symm) := rfl
  rw [h]
  exact meromorphicOrderAt_add hf' hg'

/-- The order of a difference is at least the minimum of the orders. Follows
from `mmeromorphicOrderAt_add_ge` and `mmeromorphicOrderAt_neg`. -/
lemma mmeromorphicOrderAt_sub_ge
    (hf : MMeromorphicAt I f x) (hg : MMeromorphicAt I g x) :
    min (mmeromorphicOrderAt I f x) (mmeromorphicOrderAt I g x)
      ≤ mmeromorphicOrderAt I (f - g) x := by
  have h_sub_add : (f - g) = f + (-g) := sub_eq_add_neg f g
  rw [h_sub_add]
  have h_neg_order : mmeromorphicOrderAt I (-g) x = mmeromorphicOrderAt I g x :=
    mmeromorphicOrderAt_neg
  have h := mmeromorphicOrderAt_add_ge (I := I) (x := x) hf hg.neg
  rw [h_neg_order] at h
  exact h

/-! ## Order under powers

  `mmeromorphicOrderAt_pow` and `mmeromorphicOrderAt_zpow` already live in
  `Divisor/PrincipalDivisor.lean` (lines 236 / 251) and are not duplicated
  here. -/

/-! ## Order under finset products -/

/-- The order of a finset product of meromorphic functions equals the
sum of the orders of the factors. Chart-pullback of
`Mathlib.Analysis.Meromorphic.Order.meromorphicOrderAt_fun_prod`. -/
lemma mmeromorphicOrderAt_finprod
    {ι : Type*} {s : Finset ι} {h : ι → M → ℂ}
    (hh : ∀ i ∈ s, MMeromorphicAt I (h i) x) :
    mmeromorphicOrderAt I (fun y => ∏ i ∈ s, h i y) x
      = ∑ i ∈ s, mmeromorphicOrderAt I (h i) x := by
  classical
  have hh' : ∀ i ∈ s, MeromorphicAt
      (fun z => h i ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x) :=
    fun i hi => by exact hh i hi
  show meromorphicOrderAt
      ((fun y => ∏ i ∈ s, h i y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = _
  have h_comp :
      (fun y => ∏ i ∈ s, h i y) ∘ (chartAt ℂ x).symm
        = (fun z => ∏ i ∈ s, h i ((chartAt ℂ x).symm z)) := by
    funext z
    rfl
  rw [h_comp]
  exact meromorphicOrderAt_fun_prod hh'

/-! ## Order under scalar multiplication by a nonzero constant -/

/-- The order of `c • f` (for `c : ℂ` nonzero) equals the order of `f`.
Derived from `meromorphicOrderAt_smul_of_ne_zero` with the constant function
`fun _ : ℂ => c`. -/
lemma mmeromorphicOrderAt_const_smul {c : ℂ} (hc : c ≠ 0) :
    mmeromorphicOrderAt I (c • f) x = mmeromorphicOrderAt I f x := by
  show meromorphicOrderAt ((c • f) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
        = meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  have h_comp : (c • f) ∘ (chartAt ℂ x).symm
      = ((fun _ : ℂ => c) • (f ∘ (chartAt ℂ x).symm)) := by
    funext z
    simp [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
  rw [h_comp]
  have h_const_an : AnalyticAt ℂ (fun _ : ℂ => c) ((chartAt ℂ x) x) :=
    analyticAt_const
  have h_const_ne : (fun _ : ℂ => c) ((chartAt ℂ x) x) ≠ 0 := hc
  exact meromorphicOrderAt_smul_of_ne_zero (g := fun _ : ℂ => c)
    (f := f ∘ (chartAt ℂ x).symm) (x := (chartAt ℂ x) x) h_const_an h_const_ne

end JacobianChallenge
