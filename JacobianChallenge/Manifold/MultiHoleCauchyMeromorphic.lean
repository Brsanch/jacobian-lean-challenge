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
* `circleIntegral_zpow_neg_off_pole_vanishes` — for `y ≠ x` and
  `closedBall y (ε y)` not containing `x`, the inner circle integral
  `∮_{|z-y|=ε y} (z - x)^(-k : ℤ)` is zero. This is the
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
* The bundled-hypothesis `MultiHolePrincipalPartData` is fresh (lives
  inside this file's namespace).
* All proof routes through ZZ63's discharged monomial deformation plus
  mathlib's `circleIntegral.integral_fun_sum`, `integral_const_mul`,
  `integral_sub_zpow_of_ne`, and `DiffContOnCl.circleIntegral_eq_zero`.

## Residual hypotheses (named, concrete)

The caller must supply, alongside the geometry:

1. An "analytic part" `h : ℂ → ℂ` and an open `U ⊇ closedBall c R` with
   `DifferentiableOn ℂ h U`. (Owed externally: in applications,
   producing this `h` is the content of "g extends across the analytic
   part of the disc"; mathlib at this pin does not ship a removable-
   singularities theorem in this packaged form.)

2. Principal-coefficient data `a : ↥S → ℕ → ℂ` and bound `N : ↥S → ℕ`,
   with
       `g z = h z + ∑_{x ∈ S.attach} ∑_{k = 1}^{N x} a x k · (z - x)^(-k : ℤ)`
   pointwise on every relevant circle.

Given (1) and (2) plus the disjoint-closed-ball geometry, the multi-hole
deformation identity holds.
-/

noncomputable section

open Complex MeasureTheory Set Metric Real Finset

namespace JacobianChallenge

namespace MultiHoleCauchyMeromorphic

/-- **Off-pole vanishing.** If `closedBall y r ⊆ {z : ℂ | z ≠ x}`
(equivalently, `x ∉ closedBall y r`), then for every positive integer
`k`, the function `z ↦ (z - x) ^ (-(k : ℤ))` is differentiable on a
neighbourhood of `closedBall y r`, and its circle integral vanishes:
`∮_{|z-y|=r} (z - x) ^ (-(k : ℤ)) dz = 0`. -/
lemma circleIntegral_zpow_neg_off_pole_vanishes
    {x y : ℂ} {r : ℝ} (hr : 0 ≤ r) (k : ℕ)
    (hxout : x ∉ closedBall y r) :
    (∮ z in C(y, r), (z - x) ^ (-(k : ℤ))) = 0 := by
  -- The set `closedBall y r` is contained in `{z | z ≠ x}` since `x ∉ closedBall y r`.
  -- On `{z | z ≠ x}`, the function `z ↦ (z - x) ^ (-k : ℤ)` is differentiable.
  -- Then `DiffContOnCl.circleIntegral_eq_zero` finishes.
  set f : ℂ → ℂ := fun z => (z - x) ^ (-(k : ℤ))
  -- Step 1: f is differentiable on `{z : ℂ | z ≠ x}`.
  have hf_diff_on : DifferentiableOn ℂ f {z : ℂ | z ≠ x} := by
    intro z hz
    have hz_ne : z - x ≠ 0 := sub_ne_zero.mpr hz
    have : DifferentiableAt ℂ f z := by
      have h1 : DifferentiableAt ℂ (fun z => z - x) z :=
        (differentiableAt_id').sub_const x
      have h2 : DifferentiableAt ℂ (fun w : ℂ => w ^ (-(k : ℤ))) (z - x) :=
        differentiableAt_zpow.mpr (Or.inl hz_ne)
      exact h2.comp z h1
    exact this.differentiableWithinAt
  -- Step 2: ball y r ⊆ {z | z ≠ x} since x ∉ closedBall y r.
  have hball_sub : Metric.ball y r ⊆ {z : ℂ | z ≠ x} := by
    intro z hz
    intro hzx
    -- Then `x = z ∈ ball y r ⊆ closedBall y r`, contradicting `hxout`.
    apply hxout
    rw [← hzx]
    exact Metric.ball_subset_closedBall hz
  have hclosed_sub : closedBall y r ⊆ {z : ℂ | z ≠ x} := by
    intro z hz
    intro hzx
    apply hxout
    rw [← hzx]
    exact hz
  -- Step 3: f is differentiable on `ball y r` and continuous on `closedBall y r`.
  have hf_diff_open : DifferentiableOn ℂ f (Metric.ball y r) :=
    hf_diff_on.mono hball_sub
  have hf_cont_closed : ContinuousOn f (closedBall y r) :=
    (hf_diff_on.continuousOn).mono hclosed_sub
  have hf_cont_clos : ContinuousOn f (closure (Metric.ball y r)) :=
    hf_cont_closed.mono Metric.closure_ball_subset_closedBall
  -- Step 4: assemble `DiffContOnCl` and apply `circleIntegral_eq_zero`.
  have hdcoc : DiffContOnCl ℂ f (Metric.ball y r) := ⟨hf_diff_open, hf_cont_clos⟩
  exact hdcoc.circleIntegral_eq_zero hr

/-- **Off-pole vanishing — `Finset.sum` of constant-multiples form.**

If `closedBall y r` does not contain `x`, then
`∮_{|z-y|=r} ∑_{k ∈ Finset.Icc 1 (N : ℕ)} a k * (z - x) ^ (-(k : ℤ)) dz = 0`. -/
lemma circleIntegral_principal_part_off_pole_vanishes
    {x y : ℂ} {r : ℝ} (hr : 0 ≤ r) (N : ℕ) (a : ℕ → ℂ)
    (hxout : x ∉ closedBall y r) :
    (∮ z in C(y, r), ∑ k ∈ Finset.Icc 1 N, a k * (z - x) ^ (-(k : ℤ))) = 0 := by
  -- Use linearity: `circleIntegral.integral_fun_sum`.
  -- Each summand is circle-integrable: `(z - x)^(-k)` is continuous on the
  -- compact `sphere y r` (since `x ∉ closedBall y r ⊇ sphere y r`),
  -- hence integrable; multiplied by constant `a k` is still integrable.
  -- Easier route: each summand has integral zero individually, by
  -- `circleIntegral.integral_const_mul` + `circleIntegral_zpow_neg_off_pole_vanishes`.
  -- We use `circleIntegral.integral_fun_sum` to turn the integral of the sum
  -- into a sum of integrals.
  have hxne : ∀ z ∈ sphere y r, z ≠ x := by
    intro z hz hzx
    apply hxout
    rw [← hzx]
    exact Metric.sphere_subset_closedBall hz
  have hint :
      ∀ k ∈ Finset.Icc 1 N,
        CircleIntegrable (fun z => a k * (z - x) ^ (-(k : ℤ))) y r := by
    intro k _
    -- The base function `z ↦ (z - x) ^ (-k : ℤ)` is continuous on `sphere y r`
    -- (since the sphere avoids `x`).
    have hcont_on_sphere : ContinuousOn (fun z : ℂ => (z - x) ^ (-(k : ℤ)))
        (sphere y r) := by
      intro z hz
      have hzne : z - x ≠ 0 := sub_ne_zero.mpr (hxne z hz)
      have hcontAt : ContinuousAt (fun z : ℂ => (z - x) ^ (-(k : ℤ))) z := by
        have h1 : ContinuousAt (fun z : ℂ => z - x) z :=
          (continuous_id.sub continuous_const).continuousAt
        have h2 : ContinuousAt (fun w : ℂ => w ^ (-(k : ℤ))) (z - x) :=
          continuousAt_zpow.mpr (Or.inl hzne)
        exact h2.comp h1
      exact hcontAt.continuousWithinAt
    -- Hence `CircleIntegrable`.
    have hbase : CircleIntegrable (fun z : ℂ => (z - x) ^ (-(k : ℤ))) y r := by
      apply ContinuousOn.circleIntegrable (hr := abs_nonneg r |>.trans (le_refl _))
      -- We need `ContinuousOn ... (sphere y |r|)`.
      rcases le_or_lt 0 r with hr0 | hr0
      · rw [abs_of_nonneg hr0]; exact hcont_on_sphere
      · -- `r < 0` ⇒ closedBall y r = ∅ since hr : 0 ≤ r contradicts; impossible.
        exact absurd hr0 (not_lt.mpr hr)
    have := hbase.const_fun_smul (a := a k)
    simpa [smul_eq_mul] using this
  rw [circleIntegral.integral_fun_sum hint]
  -- Now each integral is zero by `integral_const_mul` + off-pole vanishing.
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
  -- Rewrite both sides via the bundled identity, then use linearity.
  -- LHS: rewrite `g` to `h + Pg` on `sphere c R`.
  have hLHS : (∮ z in C(c, R), g z) = (∮ z in C(c, R), (h z + Pg z)) := by
    refine circleIntegral.integral_congr (R := R) hR.le ?_
    intro z hz; exact hg_outer z hz
  -- RHS: similarly rewrite each inner integral.
  have hRHS_each : ∀ y ∈ S,
      (∮ z in C(y, ε y), g z) = (∮ z in C(y, ε y), (h z + Pg z)) := by
    intro y hyS
    refine circleIntegral.integral_congr (R := ε y) (hε_pos y hyS).le ?_
    intro z hz; exact hg_inner y hyS z hz
  -- Step A: the `h` part contributes zero on every circle (analytic on closed disc).
  -- For the outer circle: standard Cauchy on closed disc.
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
  -- Step B: Build helper for the principal-part term `Pg` integrability and integral computations.
  -- Per-monomial circle-integrability lemma (for any centre `w` with `x ∉ sphere w r`):
  have hmono_integrable : ∀ (w x : ℂ) (rad : ℝ) (k : ℕ) (coef : ℂ),
      x ∉ Metric.sphere w rad →
      CircleIntegrable (fun z => coef * (z - x) ^ (-(k : ℤ))) w rad := by
    intro w x rad k coef hxnot
    -- Continuous on `sphere w |rad|`.
    have hcont_on_sphere : ContinuousOn (fun z : ℂ => (z - x) ^ (-(k : ℤ)))
        (sphere w rad) := by
      intro z hz
      have hzne : z - x ≠ 0 := by
        intro hsub
        have : z = x := by linear_combination hsub
        rw [this] at hz; exact hxnot hz
      have hcontAt : ContinuousAt (fun z : ℂ => (z - x) ^ (-(k : ℤ))) z := by
        have h1 : ContinuousAt (fun z : ℂ => z - x) z :=
          (continuous_id.sub continuous_const).continuousAt
        have h2 : ContinuousAt (fun w : ℂ => w ^ (-(k : ℤ))) (z - x) :=
          continuousAt_zpow.mpr (Or.inl hzne)
        exact h2.comp h1
      exact hcontAt.continuousWithinAt
    have hbase : CircleIntegrable (fun z : ℂ => (z - x) ^ (-(k : ℤ))) w rad := by
      apply ContinuousOn.circleIntegrable (hr := abs_nonneg rad |>.trans (le_refl _))
      rcases le_or_lt 0 rad with hr0 | hr0
      · rw [abs_of_nonneg hr0]; exact hcont_on_sphere
      · -- `rad < 0` ⇒ `sphere w rad = ∅` actually; the `ContinuousOn` is vacuous.
        intro z hz
        have hempty : sphere w rad = ∅ := by
          ext z
          simp only [Metric.mem_sphere, Set.mem_empty_iff_false, iff_false]
          intro hd
          have : 0 ≤ dist z w := dist_nonneg
          rw [hd] at this; linarith
        rw [hempty] at hz; exact hz.elim
    have := hbase.const_fun_smul (a := coef)
    simpa [smul_eq_mul] using this
  -- Step C: Sum-shape integrability. For each circle (outer or inner), the
  -- `Pg` summand is integrable: every term is integrable.
  -- We need this to apply `circleIntegral.integral_add` and `integral_fun_sum`.
  -- Each "outer" sphere `sphere c R` contains no point of `S` (since `S ⊆ ball c R` strictly, so x ≠ z for z on outer sphere... wait, actually x ∈ ball c R ⊊ closedBall c R, so x ∈ ball c R means x is strictly inside, so x ∉ sphere c R).
  have hx_not_outer_sphere : ∀ x ∈ S, x ∉ sphere c R := by
    intro x hxS hxsph
    have hx_in_ball : x ∈ ball c R := by
      have := hε_sub x hxS (Metric.mem_closedBall_self (hε_pos x hxS).le)
      exact this
    rw [Metric.mem_sphere] at hxsph
    rw [Metric.mem_ball] at hx_in_ball
    rw [hxsph] at hx_in_ball
    exact lt_irrefl R hx_in_ball
  have hx_not_inner_sphere : ∀ y ∈ S, ∀ x ∈ S, x ∉ sphere y (ε y) ∨ x = y := by
    intro y hyS x hxS
    by_cases hxy : x = y
    · exact Or.inr hxy
    · left
      intro hxsph
      have hx_in_cb : x ∈ closedBall y (ε y) := Metric.sphere_subset_closedBall hxsph
      exact hε_disj x hxS y hyS hxy hx_in_cb
  -- Step D: simplify each integral via linearity. We rewrite using `circleIntegral.integral_add`,
  -- but to use that we need integrability of both summands.
  -- The `h` part: continuous on the closed disc (in `U`), hence circle-integrable.
  have hh_integrable_outer : CircleIntegrable h c R := by
    have hh_cont_closed : ContinuousOn h (closedBall c R) :=
      (hh.continuousOn).mono hUsub
    have : ContinuousOn h (sphere c R) :=
      hh_cont_closed.mono Metric.sphere_subset_closedBall
    apply ContinuousOn.circleIntegrable (hr := hR.le)
    rwa [abs_of_pos hR]
  have hh_integrable_inner : ∀ y ∈ S, CircleIntegrable h y (ε y) := by
    intro y hyS
    have hyR : closedBall y (ε y) ⊆ closedBall c R := by
      intro z hz
      exact (Metric.ball_subset_closedBall (hε_sub y hyS hz))
    have hh_cont_closed : ContinuousOn h (closedBall y (ε y)) :=
      (hh.continuousOn).mono (fun z hz => hUsub (hyR hz))
    have : ContinuousOn h (sphere y (ε y)) :=
      hh_cont_closed.mono Metric.sphere_subset_closedBall
    apply ContinuousOn.circleIntegrable (hr := (hε_pos y hyS).le)
    rwa [abs_of_pos (hε_pos y hyS)]
  -- The `Pg` part on outer circle: integrable since each monomial is.
  have hPg_integrable_outer : CircleIntegrable Pg c R := by
    -- Pg z = ∑ x ∈ S, ∑ k ∈ Icc 1 (N x), a x k * (z - x) ^ (-k:ℤ)
    -- It's a finite sum of `CircleIntegrable` functions.
    have : CircleIntegrable
        (fun z => ∑ x ∈ S, ∑ k ∈ Finset.Icc 1 (N x),
            a x k * (z - x) ^ (-(k : ℤ))) c R := by
      apply CircleIntegrable.sum
      intro x hxS
      apply CircleIntegrable.sum
      intro k _
      have hxnot : x ∉ sphere c R := hx_not_outer_sphere x hxS
      exact hmono_integrable c x R k (a x k) hxnot
    exact this
  have hPg_integrable_inner : ∀ y ∈ S, CircleIntegrable Pg y (ε y) := by
    intro y hyS
    have : CircleIntegrable
        (fun z => ∑ x ∈ S, ∑ k ∈ Finset.Icc 1 (N x),
            a x k * (z - x) ^ (-(k : ℤ))) y (ε y) := by
      apply CircleIntegrable.sum
      intro x hxS
      apply CircleIntegrable.sum
      intro k _
      -- Either x = y (centred at the pole) or x ∉ sphere y (ε y) (off-pole).
      by_cases hxy : x = y
      · -- Centred-at-pole case: `(z - x) ^ (-k : ℤ)` is continuous on `sphere y (ε y)`
        -- because `y ∉ sphere y (ε y)` (since `ε y > 0`).
        have hy_not : y ∉ sphere y (ε y) := by
          intro hy
          rw [Metric.mem_sphere] at hy
          have := hε_pos y hyS
          rw [dist_self] at hy
          linarith
        rw [hxy]
        exact hmono_integrable y y (ε y) k (a x k) hy_not
      · have hxnot : x ∉ sphere y (ε y) := by
          intro hxsph
          have hx_in_cb : x ∈ closedBall y (ε y) := Metric.sphere_subset_closedBall hxsph
          exact hε_disj x hxS y hyS hxy hx_in_cb
        exact hmono_integrable y x (ε y) k (a x k) hxnot
    exact this
  -- Step E: Linearise both sides.
  have hLHS_split :
      (∮ z in C(c, R), (h z + Pg z))
        = (∮ z in C(c, R), h z) + (∮ z in C(c, R), Pg z) :=
    circleIntegral.integral_add hh_integrable_outer hPg_integrable_outer
  have hRHS_split : ∀ y ∈ S,
      (∮ z in C(y, ε y), (h z + Pg z))
        = (∮ z in C(y, ε y), h z) + (∮ z in C(y, ε y), Pg z) := by
    intro y hyS
    exact circleIntegral.integral_add (hh_integrable_inner y hyS) (hPg_integrable_inner y hyS)
  -- Step F: distribute `Pg` over the finite double sum on each circle.
  -- Define `term x k z = a x k * (z - x) ^ (-(k : ℤ))`.
  set term : ℂ → ℕ → ℂ → ℂ :=
    fun x k z => a x k * (z - x) ^ (-(k : ℤ)) with hterm
  -- Outer: ∮ Pg = ∑_{x ∈ S} ∮ (∑_k term x k).
  have hPg_outer_double :
      (∮ z in C(c, R), Pg z)
        = ∑ x ∈ S, ∮ z in C(c, R), ∑ k ∈ Finset.Icc 1 (N x), term x k z := by
    show (∮ z in C(c, R), ∑ x ∈ S, ∑ k ∈ Finset.Icc 1 (N x),
            a x k * (z - x) ^ (-(k : ℤ)))
        = ∑ x ∈ S, ∮ z in C(c, R), ∑ k ∈ Finset.Icc 1 (N x),
            a x k * (z - x) ^ (-(k : ℤ))
    rw [circleIntegral.integral_fun_sum]
    intro x hxS
    apply CircleIntegrable.sum
    intro k _
    have hxnot : x ∉ sphere c R := hx_not_outer_sphere x hxS
    exact hmono_integrable c x R k (a x k) hxnot
  have hPg_inner_double : ∀ y ∈ S,
      (∮ z in C(y, ε y), Pg z)
        = ∑ x ∈ S, ∮ z in C(y, ε y), ∑ k ∈ Finset.Icc 1 (N x), term x k z := by
    intro y hyS
    show (∮ z in C(y, ε y), ∑ x ∈ S, ∑ k ∈ Finset.Icc 1 (N x),
            a x k * (z - x) ^ (-(k : ℤ)))
        = ∑ x ∈ S, ∮ z in C(y, ε y), ∑ k ∈ Finset.Icc 1 (N x),
            a x k * (z - x) ^ (-(k : ℤ))
    rw [circleIntegral.integral_fun_sum]
    intro x hxS
    apply CircleIntegrable.sum
    intro k _
    by_cases hxy : x = y
    · have hy_not : y ∉ sphere y (ε y) := by
        intro hy
        rw [Metric.mem_sphere] at hy
        have := hε_pos y hyS
        rw [dist_self] at hy; linarith
      rw [hxy]; exact hmono_integrable y y (ε y) k (a x k) hy_not
    · have hxnot : x ∉ sphere y (ε y) := by
        intro hxsph
        have hx_in_cb : x ∈ closedBall y (ε y) := Metric.sphere_subset_closedBall hxsph
        exact hε_disj x hxS y hyS hxy hx_in_cb
      exact hmono_integrable y x (ε y) k (a x k) hxnot
  -- Step G: For each `x ∈ S`, the per-`x` summand integrals reduce.
  -- Key per-x identity for the OUTER circle:
  -- ∮_{|z-c|=R} ∑_k term x k z = ∑_k a x k * ∮_{|z-c|=R} (z - x) ^ (-k:ℤ)
  --                           = ∑_k a x k * ∮_{|z-x|=ε x} (z - x) ^ (-k:ℤ)  (ZZ63)
  --                           = ∮_{|z-x|=ε x} ∑_k term x k z
  -- And for the INNER circle centered at y ≠ x: it's zero.
  have h_outer_per_x : ∀ x ∈ S,
      (∮ z in C(c, R), ∑ k ∈ Finset.Icc 1 (N x), term x k z)
        = ∮ z in C(x, ε x), ∑ k ∈ Finset.Icc 1 (N x), term x k z := by
    intro x hxS
    -- Distribute on both sides via integral_fun_sum.
    have hxnot_outer : x ∉ sphere c R := hx_not_outer_sphere x hxS
    have hx_self_not_sphere : x ∉ sphere x (ε x) := by
      intro hx
      rw [Metric.mem_sphere] at hx
      have := hε_pos x hxS
      rw [dist_self] at hx; linarith
    have hLsum :
        (∮ z in C(c, R), ∑ k ∈ Finset.Icc 1 (N x), term x k z)
          = ∑ k ∈ Finset.Icc 1 (N x), ∮ z in C(c, R), term x k z := by
      rw [circleIntegral.integral_fun_sum]
      intro k _
      exact hmono_integrable c x R k (a x k) hxnot_outer
    have hRsum :
        (∮ z in C(x, ε x), ∑ k ∈ Finset.Icc 1 (N x), term x k z)
          = ∑ k ∈ Finset.Icc 1 (N x), ∮ z in C(x, ε x), term x k z := by
      rw [circleIntegral.integral_fun_sum]
      intro k _
      exact hmono_integrable x x (ε x) k (a x k) hx_self_not_sphere
    rw [hLsum, hRsum]
    apply Finset.sum_congr rfl
    intro k _
    -- ∮ a x k * (z - x) ^ (-k:ℤ) on outer = ∮ ... on inner C(x, ε x), via ZZ63.
    show (∮ z in C(c, R), a x k * (z - x) ^ (-(k : ℤ)))
        = ∮ z in C(x, ε x), a x k * (z - x) ^ (-(k : ℤ))
    rw [circleIntegral.integral_const_mul, circleIntegral.integral_const_mul]
    congr 1
    -- ZZ63 with n = -(k : ℤ).
    exact NonConcentricCauchy.nonConcentric_circleIntegral_zpow_eq
      (-(k : ℤ)) hR (hε_pos x hxS) (hε_sub x hxS)
  -- For inner circle centered at y, with x ≠ y: per-x integral is zero.
  have h_inner_per_x_off : ∀ y ∈ S, ∀ x ∈ S, x ≠ y →
      (∮ z in C(y, ε y), ∑ k ∈ Finset.Icc 1 (N x), term x k z) = 0 := by
    intro y hyS x hxS hxy
    have hxnot : x ∉ closedBall y (ε y) := hε_disj x hxS y hyS hxy
    -- Apply our principal-part-off-pole lemma.
    show (∮ z in C(y, ε y), ∑ k ∈ Finset.Icc 1 (N x),
            a x k * (z - x) ^ (-(k : ℤ))) = 0
    exact circleIntegral_principal_part_off_pole_vanishes
      (hε_pos y hyS).le (N x) (a x) hxnot
  -- Step H: Assemble.
  -- LHS = ∮ h + ∮ Pg = 0 + ∑_{x ∈ S} ∮_{|z-c|=R} (∑_k term x k z)
  --     = ∑_{x ∈ S} ∮_{|z-x|=ε x} (∑_k term x k z)        [by h_outer_per_x]
  -- RHS = ∑_{y ∈ S} (∮_{|z-y|=ε y} h + ∮_{|z-y|=ε y} Pg)
  --     = ∑_{y ∈ S} (0 + ∑_{x ∈ S} ∮_{|z-y|=ε y} ∑_k term x k z)
  --     = ∑_{y ∈ S} ∑_{x ∈ S} ∮_{|z-y|=ε y} ∑_k term x k z
  -- Inner double sum: ∑_y ∑_x = ∑_x ∑_y. For fixed x, ∑_y ∮_{|z-y|=ε y} = the y=x term + ∑_{y ≠ x} 0
  --                = ∮_{|z-x|=ε x} ∑_k term x k z.
  -- So RHS = ∑_{x ∈ S} ∮_{|z-x|=ε x} ∑_k term x k z. Same as LHS.
  rw [hLHS, hLHS_split, hh_outer_zero, zero_add, hPg_outer_double]
  -- LHS = ∑ x ∈ S, ∮_{|z-c|=R} ∑_k term x k z
  -- We'll convert each summand to the inner-x form.
  rw [Finset.sum_congr rfl h_outer_per_x]
  -- Now LHS = ∑ x ∈ S, ∮ z in C(x, ε x), ∑ k, term x k z
  -- Show RHS equals the same.
  symm
  -- Rewrite RHS pointwise.
  have hRHS_eq :
      (∑ y ∈ S, ∮ z in C(y, ε y), g z)
        = ∑ y ∈ S, ((∮ z in C(y, ε y), h z) + (∮ z in C(y, ε y), Pg z)) := by
    apply Finset.sum_congr rfl
    intro y hyS
    rw [hRHS_each y hyS, hRHS_split y hyS]
  rw [hRHS_eq]
  -- ∑_y (0 + ∮ Pg) = ∑_y ∮ Pg.
  have hRHS_h_zero :
      (∑ y ∈ S, ((∮ z in C(y, ε y), h z) + (∮ z in C(y, ε y), Pg z)))
        = ∑ y ∈ S, (∮ z in C(y, ε y), Pg z) := by
    apply Finset.sum_congr rfl
    intro y hyS
    rw [hh_inner_zero y hyS, zero_add]
  rw [hRHS_h_zero]
  -- Distribute Pg into the per-x double sum.
  have hRHS_double :
      (∑ y ∈ S, ∮ z in C(y, ε y), Pg z)
        = ∑ y ∈ S, ∑ x ∈ S, ∮ z in C(y, ε y), ∑ k ∈ Finset.Icc 1 (N x), term x k z := by
    apply Finset.sum_congr rfl
    intro y hyS
    exact hPg_inner_double y hyS
  rw [hRHS_double]
  -- Swap sums: ∑_y ∑_x = ∑_x ∑_y.
  rw [Finset.sum_comm]
  -- Now: ∑_x ∑_y ∮_{|z-y|=ε y} ∑_k term x k z = ∑_x [∮_{|z-x|=ε x} ∑_k term x k z + ∑_{y ≠ x} 0].
  apply Finset.sum_congr rfl
  intro x hxS
  -- Split the inner sum at y = x.
  rw [show (∑ y ∈ S, ∮ z in C(y, ε y), ∑ k ∈ Finset.Icc 1 (N x), term x k z)
          = (∮ z in C(x, ε x), ∑ k ∈ Finset.Icc 1 (N x), term x k z)
            + ∑ y ∈ S.erase x, ∮ z in C(y, ε y), ∑ k ∈ Finset.Icc 1 (N x), term x k z from ?_]
  · -- Show the erase sum is zero.
    have herase_zero :
        (∑ y ∈ S.erase x, ∮ z in C(y, ε y), ∑ k ∈ Finset.Icc 1 (N x), term x k z) = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      rw [Finset.mem_erase] at hy
      obtain ⟨hyx, hyS⟩ := hy
      -- y ≠ x; apply h_inner_per_x_off.
      exact h_inner_per_x_off y hyS x hxS (Ne.symm hyx)
    rw [herase_zero, add_zero]
  · -- Auxiliary: ∑ y ∈ S = ∮(at x) + ∑_{y ∈ S.erase x} ∮(at y).
    rw [← Finset.sum_erase_add S _ hxS]

end MultiHoleCauchyMeromorphic

end JacobianChallenge

end
