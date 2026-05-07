/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import JacobianChallenge.Manifold.NonConcentricCauchyDeformationDischarge

/-! # Multi-hole Cauchy deformation for finite-Laurent meromorphic integrands (ZZ64)

This file builds on ZZ63's
`NonConcentricCauchyDeformationDischarge.nonConcentric_circleIntegral_zpow_eq`
to prove the *multi-hole* non-concentric Cauchy deformation identity for
integrands that admit a **finite-principal-part Laurent decomposition**
at each hole.

The headline statement (informally):

> Let `c : ℂ`, `R > 0`, `S` a finite set of pairwise-distinct points in
> `ball c R` with disjoint `closedBall x (ε x) ⊆ ball c R`. If
>   `g z = h z + ∑_{x ∈ S} ∑_{k = 1}^{N x} a x k · (z - x) ^ (-k : ℤ)`
> on every relevant circle, where `h` is differentiable on
> a neighbourhood of `closedBall c R`, then
>   `∮_{|z-c|=R} g(z) dz = ∑_{x ∈ S} ∮_{|z-x|=ε x} g(z) dz`.

The hypothesis is bundled: rather than asking the caller to prove that
their concrete `g` admits such a decomposition (the existence question
is itself a piece of complex analysis we do not discharge here), the
caller supplies the `h`, the principal coefficients `a`, the
truncation `N`, and the pointwise identity on the circles.

## What is proved

* `circleIntegral_finite_principal_part_eq` — the headline identity,
  unconditional in mathlib at this pin given the bundled hypotheses.
* `circleIntegral_zpow_neg_off_pole_vanishes` — for `closedBall y r`
  not containing `x`, the inner circle integral
  `∮_{|z-y|=r} (z - x) ^ (-(k : ℕ) : ℤ)` is zero. This is the
  off-pole-vanishing chip used inside the headline proof.

## Strategy

Linearity of `circleIntegral` over finite sums (`circleIntegral.integral_fun_sum`)
distributes both sides over the finitely many `(z - x)^(-k)` terms.

* The **`h` (analytic) term**: vanishes on every circle inside
  `closedBall c R` by `DiffContOnCl.circleIntegral_eq_zero`.

* The **`(z - x)^(-k)` term on the outer circle** `C(c, R)`: equals
  the integral over `C(x, ε x)` by ZZ63
  (`nonConcentric_circleIntegral_zpow_eq` with `n = -k`).

* The **`(z - x)^(-k)` term on inner circle `C(y, ε y)` with `y ≠ x`**:
  vanishes because `(z - x)^(-k)` is differentiable on a neighbourhood
  of `closedBall y (ε y)` (its only singularity is at `x`, which lies
  outside `closedBall y (ε y)` by disjointness).

The two-sided sum then collapses by re-indexing.

## Anti-cheat

* No `axiom`, no `sorry`.
* No existing definition or signature is changed.
* All proof routes through ZZ63's discharged monomial deformation plus
  mathlib's `circleIntegral.integral_fun_sum`, `integral_const_mul`,
  `integral_sub_zpow_of_ne`, `circleIntegrable_sub_zpow_iff`, and
  `DiffContOnCl.circleIntegral_eq_zero`.

## Residual hypotheses (named, concrete)

The caller must supply, alongside the geometry:

1. An "analytic part" `h : ℂ → ℂ` and an open `U ⊇ closedBall c R` with
   `DifferentiableOn ℂ h U`. (Owed externally: in applications,
   producing this `h` is the content of "g extends across the analytic
   part of the disc"; mathlib at this pin does not ship a removable-
   singularities theorem in this packaged form.)

2. Principal-coefficient data `a : ℂ → ℕ → ℂ` and bound `N : ℂ → ℕ`,
   with
       `g z = h z + ∑_{x ∈ S} ∑_{k = 1}^{N x} a x k · (z - x)^(-k : ℤ)`
   pointwise on every relevant circle.

Given (1) and (2) plus the disjoint-closed-ball geometry, the multi-hole
deformation identity holds.
-/

noncomputable section

open Complex MeasureTheory Set Metric Real Finset

namespace JacobianChallenge

namespace MultiHoleCauchyMeromorphic

/-- **Off-pole vanishing.** If `closedBall y r ⊆ {z : ℂ | z ≠ x}`
(equivalently, `x ∉ closedBall y r`), and `0 ≤ r`, then for every
positive integer `k`, the function `z ↦ (z - x) ^ (-(k : ℤ))` is
differentiable on a neighbourhood of `closedBall y r`, and its circle
integral vanishes:
`∮_{|z-y|=r} (z - x) ^ (-(k : ℤ)) dz = 0`. -/
lemma circleIntegral_zpow_neg_off_pole_vanishes
    {x y : ℂ} {r : ℝ} (hr : 0 ≤ r) (k : ℕ)
    (hxout : x ∉ closedBall y r) :
    (∮ z in C(y, r), (z - x) ^ (-(k : ℤ))) = 0 := by
  set f : ℂ → ℂ := fun z => (z - x) ^ (-(k : ℤ))
  have hf_diff_on : DifferentiableOn ℂ f {z : ℂ | z ≠ x} := by
    intro z hz
    have hz_ne : z - x ≠ 0 := sub_ne_zero.mpr hz
    have : DifferentiableAt ℂ f z := by
      have h1 : DifferentiableAt ℂ (fun z : ℂ => z - x) z :=
        (differentiableAt_id).sub_const x
      have h2 : DifferentiableAt ℂ (fun w : ℂ => w ^ (-(k : ℤ))) (z - x) :=
        differentiableAt_zpow.mpr (Or.inl hz_ne)
      exact h2.comp z h1
    exact this.differentiableWithinAt
  have hball_sub : Metric.ball y r ⊆ {z : ℂ | z ≠ x} := by
    intro z hz hzx
    apply hxout
    rw [show x = z from hzx.symm]
    exact Metric.ball_subset_closedBall hz
  have hclosed_sub : closedBall y r ⊆ {z : ℂ | z ≠ x} := by
    intro z hz hzx
    apply hxout
    rw [show x = z from hzx.symm]
    exact hz
  have hf_diff_open : DifferentiableOn ℂ f (Metric.ball y r) :=
    hf_diff_on.mono hball_sub
  have hf_cont_closed : ContinuousOn f (closedBall y r) :=
    (hf_diff_on.continuousOn).mono hclosed_sub
  have hf_cont_clos : ContinuousOn f (closure (Metric.ball y r)) :=
    hf_cont_closed.mono Metric.closure_ball_subset_closedBall
  have hdcoc : DiffContOnCl ℂ f (Metric.ball y r) := ⟨hf_diff_open, hf_cont_clos⟩
  exact hdcoc.circleIntegral_eq_zero hr

/-- **Per-monomial circle-integrability:** if `0 < r` and `x ∉ sphere y r`,
then `z ↦ coef * (z - x) ^ (-(k : ℤ))` is `CircleIntegrable` on `C(y, r)`. -/
private lemma const_mul_zpow_neg_circleIntegrable
    (y x : ℂ) (r : ℝ) (k : ℕ) (coef : ℂ)
    (hxnot : x ∉ Metric.sphere y |r|) :
    CircleIntegrable (fun z => coef * (z - x) ^ (-(k : ℤ))) y r := by
  have hbase : CircleIntegrable (fun z : ℂ => (z - x) ^ (-(k : ℤ))) y r := by
    rw [circleIntegrable_sub_zpow_iff]
    exact Or.inr (Or.inr hxnot)
  have := hbase.const_fun_smul (a := coef)
  simpa [smul_eq_mul] using this

/-- **Off-pole vanishing — `Finset.sum` of constant-multiples form.**

If `closedBall y r` does not contain `x` and `0 ≤ r`, then the
circle integral of the principal-part sum
`∑_{k ∈ Finset.Icc 1 (N : ℕ)} a k * (z - x) ^ (-(k : ℤ))` over
`C(y, r)` vanishes. -/
lemma circleIntegral_principal_part_off_pole_vanishes
    {x y : ℂ} {r : ℝ} (hr : 0 ≤ r) (N : ℕ) (a : ℕ → ℂ)
    (hxout : x ∉ closedBall y r) :
    (∮ z in C(y, r), ∑ k ∈ Finset.Icc 1 N, a k * (z - x) ^ (-(k : ℤ))) = 0 := by
  have hxnot_sphere : x ∉ Metric.sphere y |r| := by
    intro hx
    apply hxout
    have hxsphere : x ∈ Metric.sphere y r := by
      rw [Metric.mem_sphere] at hx ⊢
      rw [abs_of_nonneg hr] at hx; exact hx
    exact Metric.sphere_subset_closedBall hxsphere
  have hint :
      ∀ k ∈ Finset.Icc 1 N,
        CircleIntegrable (fun z => a k * (z - x) ^ (-(k : ℤ))) y r := by
    intro k _
    exact const_mul_zpow_neg_circleIntegrable y x r k (a k) hxnot_sphere
  rw [circleIntegral.integral_fun_sum hint]
  apply Finset.sum_eq_zero
  intro k _
  rw [circleIntegral.integral_const_mul]
  rw [circleIntegral_zpow_neg_off_pole_vanishes hr k hxout]
  simp

/-- **Headline:** multi-hole non-concentric Cauchy deformation identity for
finite-principal-part meromorphic integrands.

Given:
* a centre `c` and radius `R > 0`,
* a finite set `S : Finset ℂ` of poles inside `ball c R`,
* a radius assignment `ε : ℂ → ℝ` with `0 < ε x` and
  `closedBall x (ε x) ⊆ ball c R` for each `x ∈ S`,
* pairwise disjointness: for distinct `x y ∈ S`, `x ∉ closedBall y (ε y)`,
* an "analytic part" `h : ℂ → ℂ` differentiable on an open `U ⊇ closedBall c R`,
* finite principal coefficients `a : ℂ → ℕ → ℂ` and bound `N : ℂ → ℕ`,
* a pointwise decomposition: on every relevant circle (the outer
  `sphere c R` and each inner `sphere y (ε y)`),
  `g z = h z + ∑_{x ∈ S} ∑_{k = 1}^{N x} a x k · (z - x)^(-k : ℤ)`,

then  `∮_{|z-c|=R} g = ∑_{y ∈ S} ∮_{|z-y|=ε y} g`. -/
theorem circleIntegral_finite_principal_part_eq
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (S : Finset ℂ) (ε : ℂ → ℝ)
    (hε_pos : ∀ x ∈ S, 0 < ε x)
    (hε_sub : ∀ x ∈ S, closedBall x (ε x) ⊆ ball c R)
    (hε_disj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x ∉ closedBall y (ε y))
    {h : ℂ → ℂ} {U : Set ℂ}
    (hUopen : IsOpen U) (hUsub : closedBall c R ⊆ U)
    (hh : DifferentiableOn ℂ h U)
    (a : ℂ → ℕ → ℂ) (N : ℂ → ℕ)
    {g : ℂ → ℂ}
    (hg_outer : ∀ z ∈ sphere c R,
      g z = h z + ∑ x ∈ S, ∑ k ∈ Finset.Icc 1 (N x),
              a x k * (z - x) ^ (-(k : ℤ)))
    (hg_inner : ∀ y ∈ S, ∀ z ∈ sphere y (ε y),
      g z = h z + ∑ x ∈ S, ∑ k ∈ Finset.Icc 1 (N x),
              a x k * (z - x) ^ (-(k : ℤ))) :
    (∮ z in C(c, R), g z)
      = ∑ y ∈ S, ∮ z in C(y, ε y), g z := by
  -- Abbreviation for the principal-part big-sum.
  set Pg : ℂ → ℂ :=
    fun z => ∑ x ∈ S, ∑ k ∈ Finset.Icc 1 (N x), a x k * (z - x) ^ (-(k : ℤ)) with hPg
  -- Rewrite both sides via the bundled identity.
  have hLHS : (∮ z in C(c, R), g z) = (∮ z in C(c, R), (h z + Pg z)) := by
    refine circleIntegral.integral_congr (R := R) hR.le ?_
    intro z hz; exact hg_outer z hz
  have hRHS_each : ∀ y ∈ S,
      (∮ z in C(y, ε y), g z) = (∮ z in C(y, ε y), (h z + Pg z)) := by
    intro y hyS
    refine circleIntegral.integral_congr (R := ε y) (hε_pos y hyS).le ?_
    intro z hz; exact hg_inner y hyS z hz
  -- Step A: analytic-part vanishing on every circle.
  have hh_outer_zero : (∮ z in C(c, R), h z) = 0 := by
    have hball_sub : Metric.ball c R ⊆ Metric.closedBall c R := Metric.ball_subset_closedBall
    have hh_open : DifferentiableOn ℂ h (Metric.ball c R) :=
      hh.mono (fun z hz => hUsub (hball_sub hz))
    have hh_cont_closed : ContinuousOn h (closedBall c R) :=
      (hh.continuousOn).mono hUsub
    have hh_cont_clos : ContinuousOn h (closure (Metric.ball c R)) :=
      hh_cont_closed.mono Metric.closure_ball_subset_closedBall
    have hh_dcoc : DiffContOnCl ℂ h (Metric.ball c R) := ⟨hh_open, hh_cont_clos⟩
    exact hh_dcoc.circleIntegral_eq_zero hR.le
  have hh_inner_zero : ∀ y ∈ S, (∮ z in C(y, ε y), h z) = 0 := by
    intro y hyS
    have hyR : closedBall y (ε y) ⊆ closedBall c R := by
      intro z hz
      exact (Metric.ball_subset_closedBall (hε_sub y hyS hz))
    have hball_sub : Metric.ball y (ε y) ⊆ Metric.closedBall y (ε y) :=
      Metric.ball_subset_closedBall
    have hh_open : DifferentiableOn ℂ h (Metric.ball y (ε y)) :=
      hh.mono (fun z hz => hUsub (hyR (hball_sub hz)))
    have hh_cont_closed : ContinuousOn h (closedBall y (ε y)) :=
      (hh.continuousOn).mono (fun z hz => hUsub (hyR hz))
    have hh_cont_clos : ContinuousOn h (closure (Metric.ball y (ε y))) :=
      hh_cont_closed.mono Metric.closure_ball_subset_closedBall
    have hh_dcoc : DiffContOnCl ℂ h (Metric.ball y (ε y)) := ⟨hh_open, hh_cont_clos⟩
    exact hh_dcoc.circleIntegral_eq_zero (hε_pos y hyS).le
  -- Geometric facts on poles vs spheres.
  have hx_not_outer_sphere : ∀ x ∈ S, x ∉ Metric.sphere c |R| := by
    intro x hxS hxsph
    have hx_in_ball : x ∈ ball c R :=
      hε_sub x hxS (Metric.mem_closedBall_self (hε_pos x hxS).le)
    rw [Metric.mem_sphere, abs_of_pos hR] at hxsph
    rw [Metric.mem_ball] at hx_in_ball
    rw [hxsph] at hx_in_ball
    exact lt_irrefl R hx_in_ball
  -- For inner circle centered at y with x ≠ y: x ∉ sphere y (ε y).
  have hx_not_inner_sphere_off : ∀ y ∈ S, ∀ x ∈ S, x ≠ y →
      x ∉ Metric.sphere y |ε y| := by
    intro y hyS x hxS hxy hxsph
    rw [Metric.mem_sphere, abs_of_pos (hε_pos y hyS)] at hxsph
    have hx_in_cb : x ∈ closedBall y (ε y) := by
      rw [Metric.mem_closedBall]; exact le_of_eq hxsph
    exact hε_disj x hxS y hyS hxy hx_in_cb
  -- For inner circle centered at y with x = y: y ∉ sphere y (ε y) (positive radius).
  have hy_not_self_sphere : ∀ y ∈ S, y ∉ Metric.sphere y |ε y| := by
    intro y hyS hy
    rw [Metric.mem_sphere, dist_self, abs_of_pos (hε_pos y hyS)] at hy
    have := hε_pos y hyS
    linarith
  -- Step B: Integrability of `h` on each circle.
  have hh_integrable_outer : CircleIntegrable h c R := by
    have hh_cont_closed : ContinuousOn h (closedBall c R) :=
      (hh.continuousOn).mono hUsub
    have hcs : ContinuousOn h (sphere c R) :=
      hh_cont_closed.mono Metric.sphere_subset_closedBall
    exact ContinuousOn.circleIntegrable hR.le hcs
  have hh_integrable_inner : ∀ y ∈ S, CircleIntegrable h y (ε y) := by
    intro y hyS
    have hyR : closedBall y (ε y) ⊆ closedBall c R := by
      intro z hz
      exact (Metric.ball_subset_closedBall (hε_sub y hyS hz))
    have hh_cont_closed : ContinuousOn h (closedBall y (ε y)) :=
      (hh.continuousOn).mono (fun z hz => hUsub (hyR hz))
    have hcs : ContinuousOn h (sphere y (ε y)) :=
      hh_cont_closed.mono Metric.sphere_subset_closedBall
    exact ContinuousOn.circleIntegrable (hε_pos y hyS).le hcs
  -- Step C: Integrability of `Pg` on each circle. Use `CircleIntegrable.fun_sum`.
  have hPg_integrable_outer : CircleIntegrable Pg c R := by
    show CircleIntegrable
        (fun z => ∑ x ∈ S, ∑ k ∈ Finset.Icc 1 (N x),
            a x k * (z - x) ^ (-(k : ℤ))) c R
    refine CircleIntegrable.fun_sum S (fun x hxS => ?_)
    refine CircleIntegrable.fun_sum (Finset.Icc 1 (N x)) (fun k _ => ?_)
    exact const_mul_zpow_neg_circleIntegrable c x R k (a x k)
      (hx_not_outer_sphere x hxS)
  have hPg_integrable_inner : ∀ y ∈ S, CircleIntegrable Pg y (ε y) := by
    intro y hyS
    show CircleIntegrable
        (fun z => ∑ x ∈ S, ∑ k ∈ Finset.Icc 1 (N x),
            a x k * (z - x) ^ (-(k : ℤ))) y (ε y)
    refine CircleIntegrable.fun_sum S (fun x hxS => ?_)
    refine CircleIntegrable.fun_sum (Finset.Icc 1 (N x)) (fun k _ => ?_)
    by_cases hxy : x = y
    · -- x = y case: the only "pole" on the integration disc is x = y itself, and
      -- `y ∉ sphere y (ε y)` since `0 < ε y`.
      have hxnot : x ∉ Metric.sphere y |ε y| := by
        rw [hxy]; exact hy_not_self_sphere y hyS
      exact const_mul_zpow_neg_circleIntegrable y x (ε y) k (a x k) hxnot
    · exact const_mul_zpow_neg_circleIntegrable y x (ε y) k (a x k)
        (hx_not_inner_sphere_off y hyS x hxS hxy)
  -- Step D: Linearise both sides via `circleIntegral.integral_add`.
  have hLHS_split :
      (∮ z in C(c, R), (h z + Pg z))
        = (∮ z in C(c, R), h z) + (∮ z in C(c, R), Pg z) :=
    circleIntegral.integral_add hh_integrable_outer hPg_integrable_outer
  have hRHS_split : ∀ y ∈ S,
      (∮ z in C(y, ε y), (h z + Pg z))
        = (∮ z in C(y, ε y), h z) + (∮ z in C(y, ε y), Pg z) := by
    intro y hyS
    exact circleIntegral.integral_add (hh_integrable_inner y hyS)
      (hPg_integrable_inner y hyS)
  -- Step E: Distribute Pg over the outer double sum.
  have hPg_outer_double :
      (∮ z in C(c, R), Pg z)
        = ∑ x ∈ S, ∮ z in C(c, R),
            ∑ k ∈ Finset.Icc 1 (N x), a x k * (z - x) ^ (-(k : ℤ)) := by
    show (∮ z in C(c, R), ∑ x ∈ S, ∑ k ∈ Finset.Icc 1 (N x),
            a x k * (z - x) ^ (-(k : ℤ)))
        = ∑ x ∈ S, ∮ z in C(c, R), ∑ k ∈ Finset.Icc 1 (N x),
            a x k * (z - x) ^ (-(k : ℤ))
    rw [circleIntegral.integral_fun_sum]
    intro x hxS
    refine CircleIntegrable.fun_sum (Finset.Icc 1 (N x)) (fun k _ => ?_)
    exact const_mul_zpow_neg_circleIntegrable c x R k (a x k)
      (hx_not_outer_sphere x hxS)
  -- Distribute Pg over inner double sums.
  have hPg_inner_double : ∀ y ∈ S,
      (∮ z in C(y, ε y), Pg z)
        = ∑ x ∈ S, ∮ z in C(y, ε y),
            ∑ k ∈ Finset.Icc 1 (N x), a x k * (z - x) ^ (-(k : ℤ)) := by
    intro y hyS
    show (∮ z in C(y, ε y), ∑ x ∈ S, ∑ k ∈ Finset.Icc 1 (N x),
            a x k * (z - x) ^ (-(k : ℤ)))
        = ∑ x ∈ S, ∮ z in C(y, ε y), ∑ k ∈ Finset.Icc 1 (N x),
            a x k * (z - x) ^ (-(k : ℤ))
    rw [circleIntegral.integral_fun_sum]
    intro x hxS
    refine CircleIntegrable.fun_sum (Finset.Icc 1 (N x)) (fun k _ => ?_)
    by_cases hxy : x = y
    · have hxnot : x ∉ Metric.sphere y |ε y| := by
        rw [hxy]; exact hy_not_self_sphere y hyS
      exact const_mul_zpow_neg_circleIntegrable y x (ε y) k (a x k) hxnot
    · exact const_mul_zpow_neg_circleIntegrable y x (ε y) k (a x k)
        (hx_not_inner_sphere_off y hyS x hxS hxy)
  -- Step F: Per-x outer-to-inner identity (uses ZZ63).
  have h_outer_per_x : ∀ x ∈ S,
      (∮ z in C(c, R), ∑ k ∈ Finset.Icc 1 (N x), a x k * (z - x) ^ (-(k : ℤ)))
        = ∮ z in C(x, ε x), ∑ k ∈ Finset.Icc 1 (N x), a x k * (z - x) ^ (-(k : ℤ)) := by
    intro x hxS
    have hxnot_outer : x ∉ Metric.sphere c |R| := hx_not_outer_sphere x hxS
    have hxnot_self : x ∉ Metric.sphere x |ε x| := hy_not_self_sphere x hxS
    have hLsum :
        (∮ z in C(c, R), ∑ k ∈ Finset.Icc 1 (N x), a x k * (z - x) ^ (-(k : ℤ)))
          = ∑ k ∈ Finset.Icc 1 (N x), ∮ z in C(c, R), a x k * (z - x) ^ (-(k : ℤ)) := by
      rw [circleIntegral.integral_fun_sum]
      intro k _
      exact const_mul_zpow_neg_circleIntegrable c x R k (a x k) hxnot_outer
    have hRsum :
        (∮ z in C(x, ε x), ∑ k ∈ Finset.Icc 1 (N x), a x k * (z - x) ^ (-(k : ℤ)))
          = ∑ k ∈ Finset.Icc 1 (N x), ∮ z in C(x, ε x), a x k * (z - x) ^ (-(k : ℤ)) := by
      rw [circleIntegral.integral_fun_sum]
      intro k _
      exact const_mul_zpow_neg_circleIntegrable x x (ε x) k (a x k) hxnot_self
    rw [hLsum, hRsum]
    apply Finset.sum_congr rfl
    intro k _
    rw [circleIntegral.integral_const_mul, circleIntegral.integral_const_mul]
    congr 1
    -- ZZ63 with n = -(k : ℤ).
    exact NonConcentricCauchy.nonConcentric_circleIntegral_zpow_eq
      (-(k : ℤ)) hR (hε_pos x hxS) (hε_sub x hxS)
  -- Step G: Off-pole inner integrals vanish.
  have h_inner_per_x_off : ∀ y ∈ S, ∀ x ∈ S, x ≠ y →
      (∮ z in C(y, ε y), ∑ k ∈ Finset.Icc 1 (N x), a x k * (z - x) ^ (-(k : ℤ))) = 0 := by
    intro y hyS x hxS hxy
    have hxnot : x ∉ closedBall y (ε y) := hε_disj x hxS y hyS hxy
    exact circleIntegral_principal_part_off_pole_vanishes
      (hε_pos y hyS).le (N x) (a x) hxnot
  -- Step H: Final assembly.
  rw [hLHS, hLHS_split, hh_outer_zero, zero_add, hPg_outer_double]
  rw [Finset.sum_congr rfl h_outer_per_x]
  symm
  -- Rewrite RHS via `hRHS_each`, `hRHS_split`, kill `h` parts, distribute `Pg`.
  have hRHS_eq :
      (∑ y ∈ S, ∮ z in C(y, ε y), g z)
        = ∑ y ∈ S, ((∮ z in C(y, ε y), h z) + (∮ z in C(y, ε y), Pg z)) := by
    apply Finset.sum_congr rfl
    intro y hyS
    rw [hRHS_each y hyS, hRHS_split y hyS]
  rw [hRHS_eq]
  have hRHS_h_zero :
      (∑ y ∈ S, ((∮ z in C(y, ε y), h z) + (∮ z in C(y, ε y), Pg z)))
        = ∑ y ∈ S, (∮ z in C(y, ε y), Pg z) := by
    apply Finset.sum_congr rfl
    intro y hyS
    rw [hh_inner_zero y hyS, zero_add]
  rw [hRHS_h_zero]
  have hRHS_double :
      (∑ y ∈ S, ∮ z in C(y, ε y), Pg z)
        = ∑ y ∈ S, ∑ x ∈ S, ∮ z in C(y, ε y),
            ∑ k ∈ Finset.Icc 1 (N x), a x k * (z - x) ^ (-(k : ℤ)) := by
    apply Finset.sum_congr rfl
    intro y hyS
    exact hPg_inner_double y hyS
  rw [hRHS_double, Finset.sum_comm]
  -- Now: ∑_x ∑_y ∮(at y) ∑_k = ∑_x [∮(at x) ∑_k + ∑_{y ∈ erase x} 0].
  apply Finset.sum_congr rfl
  intro x hxS
  rw [show (∑ y ∈ S, ∮ z in C(y, ε y),
              ∑ k ∈ Finset.Icc 1 (N x), a x k * (z - x) ^ (-(k : ℤ)))
          = (∮ z in C(x, ε x),
                ∑ k ∈ Finset.Icc 1 (N x), a x k * (z - x) ^ (-(k : ℤ)))
            + ∑ y ∈ S.erase x, ∮ z in C(y, ε y),
                ∑ k ∈ Finset.Icc 1 (N x), a x k * (z - x) ^ (-(k : ℤ)) from ?_]
  · have herase_zero :
        (∑ y ∈ S.erase x, ∮ z in C(y, ε y),
            ∑ k ∈ Finset.Icc 1 (N x), a x k * (z - x) ^ (-(k : ℤ))) = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      rw [Finset.mem_erase] at hy
      obtain ⟨hyx, hyS⟩ := hy
      exact h_inner_per_x_off y hyS x hxS (Ne.symm hyx)
    rw [herase_zero, add_zero]
  · rw [← Finset.sum_erase_add S _ hxS, add_comm]

end MultiHoleCauchyMeromorphic

end JacobianChallenge

end
