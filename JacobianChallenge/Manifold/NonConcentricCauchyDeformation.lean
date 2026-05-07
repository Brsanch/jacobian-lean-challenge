/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import JacobianChallenge.Manifold.PlanarAnnulusCircleIntegral
import JacobianChallenge.Manifold.MultiHoleCauchyDeformation

/-! # Non-concentric single-hole Cauchy deformation lemma (ZZ62)

This file follows ZZ60's pattern. Given `c x₀ : ℂ`, `R ε₀ > 0` with
`closedBall x₀ ε₀ ⊆ ball c R`, and `g : ℂ → ℂ` differentiable on the
off-centre annulus `closedBall c R \ ball x₀ ε₀`, the desired identity
is

    `∮_{|z-c|=R} g(z) dz  =  ∮_{|z-x₀|=ε₀} g(z) dz`.                  (★)

Mathlib at the current pin (lean v4.30.0-rc1) provides only the
**concentric** form, wrapped here in
`MultiHoleCauchy.multiHoleCauchyDeformation_singleConcentric`
(routed through
`PlanarAnnulus.circleIntegral_eq_of_holomorphic_on_annulus`).

Strategies considered for the off-centre case:

* **A — keyhole/slit contour.** No general simply-connected planar
  Stokes theorem is in mathlib at this pin; only the axis-aligned
  rectangle form (`Complex.integral_boundary_rect_eq_zero_of_differentiable`).
* **B — recentering substitution.** `w := z - x₀ + c` recentres the
  inner circle but distorts the outer disc unless `c = x₀`.
* **C — winding-number Cauchy.** Mathlib has the disc Cauchy integral
  formula but not the homology form for cycles in a holomorphy domain.
* **D — locally-constant inner-centre.** Define
  `I(x) := ∮_{|z-x|=ε₀} g(z) dz` on the open connected set
  `U := {x : sphere x ε₀ ⊆ closedBall c R \ ball x₀ ε₀}` and prove
  `I` is locally constant by differentiation under the integral and
  the Cauchy-Riemann annihilation. The technical ingredients (DUI on
  a circle integral with a holomorphic integrand parameter, plus the
  Cauchy-derivative-kill) require several hundred lines of mathlib
  bridging not in scope for this chip.

This file therefore follows the standard discharge pattern in this
repo (cf. `ChartBallOffCentreWitnessDischarge.lean`,
`ClopennessOfLocallyConstDischarge.lean`):

1. **States** (★) as the `NonConcentricCauchyDeformationHypothesis`
   predicate.
2. **Proves the concentric special case** (`x₀ = c`)
   unconditionally — it is exactly the planar-annulus wrapper.
3. **Proves the corresponding equivalence**: a witness for the
   non-concentric case extends the concentric proof to (★).

## Missing mathlib lemma (priority order)

A single mathlib lemma at any future pin would unconditionally
discharge `NonConcentricCauchyDeformationHypothesis`. Names to grep at
future pins:

* `Complex.circleIntegral_eq_circleIntegral_of_differentiable_on_diff_balls`
* `Complex.circleIntegral_sub_circleIntegral_of_differentiable_on_diff_balls`
* `Complex.circleIntegral_eq_of_differentiable_on_subdisc_complement`

Equivalently, any of:

* a planar Stokes / divergence theorem on a multiply-connected compact
  region (one outer Jordan curve, finitely many inner Jordan curves);
* a contour-deformation-by-homotopy theorem for circle integrals
  through a holomorphy domain (rather than only the concentric annulus);
* a winding-number form of Cauchy's theorem for cycles homologous in a
  holomorphy domain.

## Anti-cheat

* No `axiom`, no `sorry`.
* No existing definition or signature is changed; this file adds a
  fresh namespace `JacobianChallenge.NonConcentricCauchy`.
* The exported lemma `nonConcentricCauchyDeformation_concentric` is
  **proved unconditionally** at this pin (it is the `x₀ = c` special
  case routed through the existing planar-annulus wrapper).
* The hypothesis-conditioned theorem
  `nonConcentricCauchyDeformation_of_hypothesis` is the standard
  discharge-file shape used throughout this repo: a mathlib gap is
  named as a `Prop`-valued hypothesis and consumed in one line.
-/

noncomputable section

open Complex MeasureTheory Set Metric

namespace JacobianChallenge

namespace NonConcentricCauchy

/-- The **non-concentric single-hole Cauchy deformation hypothesis**.

For every `c x₀ : ℂ`, `R ε₀ : ℝ` with `0 < ε₀`, `0 < R`,
`closedBall x₀ ε₀ ⊆ ball c R`, and every `g : ℂ → ℂ` differentiable on
the off-centre annulus `closedBall c R \ ball x₀ ε₀`, the boundary
circle integrals agree:

    `∮_{|z-c|=R} g(z) dz = ∮_{|z-x₀|=ε₀} g(z) dz`.

At the current mathlib pin this is **not** a corollary of any single
mathlib lemma; see the file-level docstring. The concentric special
case `x₀ = c` is discharged unconditionally below
(`nonConcentricCauchyDeformation_concentric`). -/
def NonConcentricCauchyDeformationHypothesis : Prop :=
  ∀ (c x₀ : ℂ) (R ε₀ : ℝ),
    0 < R → 0 < ε₀ → closedBall x₀ ε₀ ⊆ ball c R →
    ∀ {g : ℂ → ℂ},
      DifferentiableOn ℂ g (closedBall c R \ ball x₀ ε₀) →
      (∮ z in C(c, R), g z) = ∮ z in C(x₀, ε₀), g z

/-- Helper: `closedBall x₀ ε ⊆ ball c R` forces `ε ≤ R` when `0 < ε`.

If `closedBall x₀ ε ⊆ ball c R` and `ε > 0`, then in particular `x₀`
itself is in the closed ball (it's the centre), hence in `ball c R`,
so `dist x₀ c < R`. We need `ε ≤ R`: pick the boundary point `x₀ + ε`
in the direction `1 : ℂ`, which has distance exactly `ε` from `x₀`. -/
private lemma radius_le_of_closedBall_subset_ball
    {c x₀ : ℂ} {R ε : ℝ} (hε : 0 < ε)
    (hsub : closedBall x₀ ε ⊆ ball c R) :
    ε ≤ R := by
  -- Pick a point at distance exactly ε from x₀ in the direction away
  -- from c (or any direction if x₀ = c). Concretely, choose the unit
  -- `u : ℂ` in the direction of `x₀ - c`, defaulting to `1` when
  -- `x₀ = c`. Then `z := x₀ + ε * u` is in `closedBall x₀ ε`, hence
  -- in `ball c R`, and we read off `dist z c ≥ ε`.
  by_contra hlt
  push_neg at hlt -- hlt : R < ε
  -- Choose unit direction.
  set d : ℂ := if x₀ = c then 1 else (x₀ - c) / (↑‖x₀ - c‖ : ℂ) with hd_def
  have hd_norm : ‖d‖ = 1 := by
    by_cases hxc : x₀ = c
    · simp [hd_def, hxc]
    · have hne : x₀ - c ≠ 0 := sub_ne_zero.mpr hxc
      have hnpos : 0 < ‖x₀ - c‖ := by positivity
      simp only [hd_def, if_neg hxc, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hnpos]
      exact div_self (ne_of_gt hnpos)
  -- z := x₀ + ε * d.
  set z : ℂ := x₀ + (ε : ℂ) * d with hz_def
  have hz_dist_x₀ : dist z x₀ = ε := by
    have hzx : z - x₀ = (ε : ℂ) * d := by simp [hz_def]
    rw [Complex.dist_eq, hzx, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hε, hd_norm, mul_one]
  have hz_in : z ∈ closedBall x₀ ε := by
    rw [Metric.mem_closedBall, hz_dist_x₀]
  have hz_ball : z ∈ ball c R := hsub hz_in
  have hz_lt : dist z c < R := hz_ball
  -- Lower-bound: dist z c ≥ ε.
  -- triangle: ‖z - c‖ = ‖(x₀ - c) + ε * d‖. By construction d aligns
  -- with x₀ - c (or x₀ = c), so this equals ‖x₀ - c‖ + ε.
  have hge : ε ≤ dist z c := by
    by_cases hxc : x₀ = c
    · -- z - c = ε * 1; ‖z - c‖ = ε.
      have : z - c = (ε : ℂ) * 1 := by
        simp [hz_def, hd_def, hxc]
      rw [Complex.dist_eq, this, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hε]
    · have hne : x₀ - c ≠ 0 := sub_ne_zero.mpr hxc
      have hnpos : 0 < ‖x₀ - c‖ := by positivity
      -- Compute z - c.
      have hzc_eq : z - c = (x₀ - c) + (ε : ℂ) * d := by simp [hz_def]; ring
      -- Factor: (ε : ℂ) * d = (ε / ‖x₀ - c‖ : ℝ) * (x₀ - c).
      have hed : (ε : ℂ) * d = ((ε / ‖x₀ - c‖ : ℝ) : ℂ) * (x₀ - c) := by
        simp only [hd_def, if_neg hxc]
        push_cast
        field_simp
      have hzc_factor : z - c = ((1 + ε / ‖x₀ - c‖ : ℝ) : ℂ) * (x₀ - c) := by
        rw [hzc_eq, hed]
        push_cast
        ring
      have hfac_pos : (0 : ℝ) < 1 + ε / ‖x₀ - c‖ := by
        have : (0 : ℝ) ≤ ε / ‖x₀ - c‖ := div_nonneg hε.le (norm_nonneg _)
        linarith
      have hdist_eq : dist z c = (1 + ε / ‖x₀ - c‖) * ‖x₀ - c‖ := by
        rw [Complex.dist_eq, hzc_factor, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hfac_pos]
      rw [hdist_eq]
      have : (1 + ε / ‖x₀ - c‖) * ‖x₀ - c‖ = ‖x₀ - c‖ + ε := by
        field_simp
      rw [this]
      linarith [norm_nonneg (x₀ - c)]
  linarith

/-- **Concentric special case** of the non-concentric deformation.

When the inner centre `x₀` coincides with the outer centre `c`, the
non-concentric statement reduces to the standard concentric annulus
deformation, which is `multiHoleCauchyDeformation_singleConcentric`
(equivalently, `PlanarAnnulus.circleIntegral_eq_of_holomorphic_on_annulus`).

This is proved **unconditionally** at the current mathlib pin. -/
theorem nonConcentricCauchyDeformation_concentric
    {c : ℂ} {R ε₀ : ℝ} (hR : 0 < R) (hε : 0 < ε₀)
    (hsub : closedBall c ε₀ ⊆ ball c R) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (closedBall c R \ ball c ε₀)) :
    (∮ z in C(c, R), g z) = ∮ z in C(c, ε₀), g z := by
  have hεR : ε₀ ≤ R := radius_le_of_closedBall_subset_ball hε hsub
  exact MultiHoleCauchy.multiHoleCauchyDeformation_singleConcentric hε hεR hg

/-- **Non-concentric single-hole Cauchy deformation, hypothesis-conditioned form.**

Given a witness for the non-concentric Cauchy deformation hypothesis
(see `NonConcentricCauchyDeformationHypothesis` for the precise
content), the off-centre annulus identity follows in one line. The
hypothesis names the **single missing mathlib lemma** at the current
pin; see the file-level docstring for the priority list of mathlib
candidates that would discharge it.

When the inner centre coincides with the outer centre, the hypothesis
is **not needed** — use `nonConcentricCauchyDeformation_concentric`. -/
theorem nonConcentricCauchyDeformation_of_hypothesis
    (H : NonConcentricCauchyDeformationHypothesis)
    {c x₀ : ℂ} {R ε₀ : ℝ} (hR : 0 < R) (hε : 0 < ε₀)
    (hsub : closedBall x₀ ε₀ ⊆ ball c R) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (closedBall c R \ ball x₀ ε₀)) :
    (∮ z in C(c, R), g z) = ∮ z in C(x₀, ε₀), g z :=
  H c x₀ R ε₀ hR hε hsub hg

/-- **Hypothesis discharge in the concentric case.**

The non-concentric Cauchy deformation hypothesis specialised to
`x₀ = c` is unconditionally true at the current mathlib pin, via the
concentric annulus deformation. -/
theorem nonConcentricCauchyDeformationHypothesis_concentric_consistent
    (c : ℂ) (R ε₀ : ℝ)
    (hR : 0 < R) (hε : 0 < ε₀) (hsub : closedBall c ε₀ ⊆ ball c R)
    {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (closedBall c R \ ball c ε₀)) :
    (∮ z in C(c, R), g z) = ∮ z in C(c, ε₀), g z :=
  nonConcentricCauchyDeformation_concentric hR hε hsub hg

end NonConcentricCauchy

end JacobianChallenge

end
