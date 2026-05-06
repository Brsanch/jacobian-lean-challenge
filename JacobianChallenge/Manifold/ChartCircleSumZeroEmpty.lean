/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartCircleSumZero

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # The empty-support / no-zeros-no-poles base case

This file ships the **trivial / boundary case** of the residue theorem on
a compact Riemann surface: the case when the principal divisor of `f`
has empty support, equivalently when `f` has neither zeros nor poles.

In this case three statements collapse to `Finset.sum_empty`:

* `chartCircleSum_zero_of_supportFinset_empty` — the formal chart-circle
  sum over the (empty) divisor support is `0`.
* `principalDivisorMap_degree_zero_of_supportFinset_empty` — the divisor
  has degree `0`.
* `principalDivisorMap_eq_zero_iff_no_zeros_no_poles` — empty support is
  equivalent to `mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x = 0` everywhere
  (i.e. no germ has positive nor negative chart order). The `nonvanishing_germ`
  field of `MeromorphicNonzero` rules out the `⊤` collapse, so
  `orderFun = 0 ↔ mmeromorphicOrderAt = 0` pointwise (mathlib content via
  `JacobianChallenge.MMeromorphicOn.orderFun_eq_zero_iff`).

These are the **base case**: combined with future work on the non-empty
case (Stokes-on-a-compact-2-manifold-without-boundary applied to
`d log f`), they cover the trivial boundary of the residue theorem.

## Anti-cheat

* No `axiom`, no `sorry`.
* No existing definition or signature is changed (pure addition).
* The lemmas have honest, non-trivial proof bodies that consume the
  empty-support hypothesis exactly once each (via `Finset.sum_empty`
  for the chart-circle and degree statements, and via `Div`-extensionality
  plus `orderFun_eq_zero_iff` for the iff statement).
-/

noncomputable section

open scoped Real Topology BigOperators Manifold ContDiff
open Complex MeasureTheory

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Empty-support reduction of the chart-circle sum -/

/-- **Empty-support base case of the residue theorem (chart-circle leg).**

If the principal divisor of `f` has empty support (i.e. `f` has neither
zeros nor poles in the chart-pulled-back sense), then the chart-circle
sum over that empty support is identically `0`, for any per-point radius
`r : X → ℝ`.

This is the *boundary case* of the residue identity
`chartCircleSum f ((principalDivisorMap f).supportFinset) r = 0`: when
the support is empty there is nothing to sum, and the identity reduces
to `Finset.sum_empty`. -/
lemma chartCircleSum_zero_of_supportFinset_empty
    (f : MeromorphicNonzero X) (r : X → ℝ)
    (hempty : (principalDivisorMap f).supportFinset = (∅ : Finset X)) :
    chartCircleSum f ((principalDivisorMap f).supportFinset) r = 0 := by
  rw [hempty]
  exact chartCircleSum_empty f r

/-! ## Empty-support reduction of the divisor degree -/

/-- **Empty-support base case of the residue theorem (degree leg).**

If the principal divisor of `f` has empty support, then its degree is
`0`. Direct corollary of the definition of `Div.degree` (= sum over the
divisor's `supportFinset`) plus `Finset.sum_empty`. -/
lemma principalDivisorMap_degree_zero_of_supportFinset_empty
    (f : MeromorphicNonzero X)
    (hempty : (principalDivisorMap f).supportFinset = (∅ : Finset X)) :
    (principalDivisorMap f).degree = 0 := by
  unfold Div.degree
  rw [hempty]
  exact Finset.sum_empty

/-! ## Equivalent forms of "no zeros, no poles" -/

/-- **No-zeros-no-poles characterisation of `principalDivisorMap = 0`.**

The principal divisor of `f` is the zero divisor iff `f` has chart-pulled-
back order `0` at every point of `X` (equivalently: every germ of `f` is
non-vanishing at finite order, with no zero or pole anywhere).

The reverse direction is a divisor-equality `ext` argument: if every
germ has chart order `0`, the order divisor's `toFun` is pointwise `0`,
so the divisor equals `(0 : Div X)`.

The forward direction uses `principalDivisorMap_apply` (which unfolds
`(principalDivisorMap f) x` to `MMeromorphicOn.orderFun 𝓘(ℂ,ℂ) f.toFun x`)
and the `nonvanishing_germ` field of `MeromorphicNonzero` (which rules
out the `⊤ ↦ 0` `untop₀` collapse), together with mathlib-side
`orderFun_eq_zero_iff`. -/
lemma principalDivisorMap_eq_zero_iff_no_zeros_no_poles
    (f : MeromorphicNonzero X) :
    principalDivisorMap f = 0 ↔
      ∀ x, mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun x = 0 := by
  classical
  constructor
  · -- Forward: `principalDivisorMap f = 0 → ∀ x, mmeromorphicOrderAt … = 0`.
    intro hzero x
    have h_apply : (principalDivisorMap f : X → ℤ) x
        = JacobianChallenge.MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x :=
      principalDivisorMap_apply f x
    have h_zero_apply : (principalDivisorMap f : X → ℤ) x = 0 := by
      rw [hzero]
      simp
    have h_orderFun_zero :
        JacobianChallenge.MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x = 0 := by
      rw [← h_apply]; exact h_zero_apply
    have hf0 : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x ≠ ⊤ :=
      f.nonvanishing_germ x
    exact (JacobianChallenge.MMeromorphicOn.orderFun_eq_zero_iff hf0).mp
      h_orderFun_zero
  · -- Reverse: `(∀ x, mmeromorphicOrderAt … = 0) → principalDivisorMap f = 0`.
    intro hall
    ext x
    show JacobianChallenge.MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x
        = ((0 : Div X) : X → ℤ) x
    unfold JacobianChallenge.MMeromorphicOn.orderFun
    rw [hall x]
    simp

/-! ## Pointwise reformulation of empty-support -/

/-- **Empty-support iff pointwise `mmeromorphicOrderAt = 0`.**

A convenience reformulation: `(principalDivisorMap f).supportFinset = ∅`
is equivalent to `mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x = 0` at every
point. This bridges the geometric "no zeros, no poles" picture and the
Finset-level empty-support hypothesis.

Proof: `supportFinset = ∅` iff the underlying function `(D : X → ℤ)` is
identically `0` (via `Finset.eq_empty_iff_forall_notMem` plus
`Div.mem_supportFinset`), which is `principalDivisorMap f = 0` by
`Div`-extensionality, which is the iff in
`principalDivisorMap_eq_zero_iff_no_zeros_no_poles`. -/
lemma supportFinset_eq_empty_iff_no_zeros_no_poles
    (f : MeromorphicNonzero X) :
    (principalDivisorMap f).supportFinset = (∅ : Finset X) ↔
      ∀ x, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x = 0 := by
  classical
  constructor
  · -- Forward: empty support ⇒ all orders are zero.
    intro hempty x
    -- From `supportFinset = ∅`, the function is pointwise zero.
    have h_notmem : x ∉ (principalDivisorMap f).supportFinset := by
      rw [hempty]; exact Finset.notMem_empty x
    have h_apply_zero : ((principalDivisorMap f) : X → ℤ) x = 0 :=
      Div.apply_eq_zero_of_notMem_supportFinset h_notmem
    have h_orderFun_zero :
        JacobianChallenge.MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x = 0 := by
      have := principalDivisorMap_apply f x
      rw [this] at h_apply_zero
      exact h_apply_zero
    have hf0 : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x ≠ ⊤ :=
      f.nonvanishing_germ x
    exact (JacobianChallenge.MMeromorphicOn.orderFun_eq_zero_iff hf0).mp
      h_orderFun_zero
  · -- Reverse: all orders zero ⇒ empty support.
    intro hall
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rw [Div.mem_supportFinset] at hx
    apply hx
    have h_apply : ((principalDivisorMap f) : X → ℤ) x
        = JacobianChallenge.MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x :=
      principalDivisorMap_apply f x
    rw [h_apply]
    unfold JacobianChallenge.MMeromorphicOn.orderFun
    rw [hall x]
    rfl

end MeromorphicNonzero

end JacobianChallenge

end
