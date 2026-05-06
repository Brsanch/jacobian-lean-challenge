/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartCircleHomotopyAnnulus
import JacobianChallenge.Manifold.ChartCircleVanishingRegular
import JacobianChallenge.Manifold.LogDiffAnchoredWitness

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Regular chart-disks around a meromorphic point

For `f : MeromorphicNonzero X` and `x : X`, this file packages a
"good" chart-disk around `x`: a positive radius `r` together with a
*planar Laurent factorisation* of `f̃ := f.toFun ∘ (chartAt ℂ x).symm`
on the closed disk of radius `r`.

The predicate `IsRegularChartDiskAround f x r` carries:

* chart containment: `closedBall z₀ r ⊆ (chartAt ℂ x).target`,
  where `z₀ := (chartAt ℂ x) x`;
* an analytic, non-vanishing planar factor `g : ℂ → ℂ` on the closed
  disk of radius `r`;
* the Laurent factorisation
  `f̃(z) = (z - z₀)^k · g(z)` on the punctured open disk
  `ball z₀ r \ {z₀}`, where `k := orderFun 𝓘(ℂ,ℂ) f.toFun x` is the
  integer order of `f` at `x`.

The non-vanishing of `g` on the closed disk is *exactly* the
isolation property "`x` is the only zero/pole of `f` in the
chart-disk": away from `z₀`, `f̃(z) = (z-z₀)^k · g(z)` is the product
of a non-vanishing factor and a power of `(z-z₀)`, neither of which
vanishes for `z ≠ z₀`. So `IsRegularChartDiskAround` *is* the
zero/pole-isolation predicate, in a form that simultaneously delivers
the analytic-remainder witness needed by the residue calculus.

The existence theorem `exists_regular_chartDisk` is **unconditional**:
the witness is supplied by the planar Laurent factorisation
infrastructure of `Manifold/LogDiffAnchoredWitness.lean` applied to
the non-vanishing-germ field `f.nonvanishing_germ x`.

The bridge `isRegularOnAnnulus_of_isRegularChartDiskAround` shows
that a regular chart-disk of radius `r` automatically supplies a
regular annulus (in the sense of
`Manifold.ChartCircleHomotopyAnnulus`) for every pair of inner/outer
radii `0 < r₁ < r₂ ≤ r`. The annular witness is

  `H(z) := k · (z - z₀)⁻¹ + (deriv g / g)(z)`,

continuous on the closed annulus (the simple pole at `z₀` is
excluded by the strictly positive inner radius) and differentiable
on the open annulus.

Together with the all-radii residue identity from
`Manifold.ChartCircleAnchoredAllRadii` (ZZ6), this makes the
chart-anchored circle integral identity universally applicable on
regular chart-disks.

## Anti-cheat

* No `axiom`, no `sorry`.
* No existing definition or signature is changed; this is a pure addition.
* The existence proof routes through `planar_laurent_factorization`
  and `extract_common_radius`
  (`Manifold/LogDiffAnchoredWitness.lean`), both unconditional.
* The annular bridge invokes only mathlib differentiability/continuity
  lemmas for the planar simple pole `z ↦ (z - z₀)⁻¹` on a region
  excluding `z₀`, plus analyticity of `deriv g / g` from the witness.
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

/-! ## Regular chart-disk predicate

`IsRegularChartDiskAround f x r` packages the data of a good
chart-disk of radius `r` around `x`: chart containment, a planar
analytic non-vanishing factor `g`, and the Laurent factorisation of
`f̃ := f.toFun ∘ (chartAt ℂ x).symm` on the punctured disk.

Stated as a `Prop`-valued `def` (not `axiom`). -/
def IsRegularChartDiskAround
    (f : MeromorphicNonzero X) (x : X) (r : ℝ) : Prop :=
  ∃ (R : ℝ) (g : ℂ → ℂ),
    r < R ∧
    Metric.closedBall ((chartAt ℂ x) x) r ⊆ (chartAt ℂ x).target ∧
    AnalyticOnNhd ℂ g (Metric.closedBall ((chartAt ℂ x) x) r) ∧
    (∀ z ∈ Metric.closedBall ((chartAt ℂ x) x) r, g z ≠ 0) ∧
    ∀ z ∈ Metric.ball ((chartAt ℂ x) x) R, z ≠ (chartAt ℂ x) x →
      (f.toFun ∘ (chartAt ℂ x).symm) z =
        (z - (chartAt ℂ x) x) ^
          ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ)) • g z

/-! ## Existence of a regular chart-disk

For every `f : MeromorphicNonzero X` and every `x : X`, there exists
`r > 0` such that `IsRegularChartDiskAround f x r` holds. The proof
threads the unconditional planar Laurent factorisation chain through
`extract_common_radius` and shrinks to the closed disk produced
there. -/
theorem exists_regular_chartDisk
    (f : MeromorphicNonzero X) (x : X) :
    ∃ r > 0, IsRegularChartDiskAround f x r := by
  have hf0 : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x ≠ ⊤ :=
    f.nonvanishing_germ x
  obtain ⟨g, hg_an, hg_ne, h_fact⟩ := planar_laurent_factorization f x hf0
  set k : ℤ := (MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) with hk_def
  obtain ⟨r, R, hr_pos, hrR, h_target_sub, hg_ne_disk, hg_an_on,
         h_closed_sub_R, h_fact_R⟩ :=
    extract_common_radius f x k g hg_an hg_ne h_fact
  exact ⟨r, hr_pos, R, g, hrR, h_target_sub, hg_an_on, hg_ne_disk, h_fact_R⟩

/-! ## Bridge to the annular regularity predicate

Given a regular chart-disk of radius `r` around `x`, every pair of
radii `0 < r₁ < r₂ ≤ r` is a regular annulus in the sense of
`Manifold.ChartCircleHomotopyAnnulus`. The annular witness is

  `H(z) := k · (z - z₀)⁻¹ + (deriv g / g)(z)`,

with `k := orderFun 𝓘(ℂ,ℂ) f.toFun x` and `z₀ := (chartAt ℂ x) x`.
-/

private lemma simplePole_continuousOn_annulus
    (z₀ : ℂ) (k : ℂ) (r₁ r₂ : ℝ) (hr₁ : 0 < r₁) :
    ContinuousOn (fun z : ℂ => k * (z - z₀)⁻¹)
      (Metric.closedBall z₀ r₂ \ Metric.ball z₀ r₁) := by
  intro z hz
  have hz_not_inner : z ∉ Metric.ball z₀ r₁ := hz.2
  rw [Metric.mem_ball, not_lt] at hz_not_inner
  have hz_ne : z ≠ z₀ := by
    intro heq
    rw [heq] at hz_not_inner
    simp at hz_not_inner
    linarith
  have hsub_ne : z - z₀ ≠ 0 := sub_ne_zero.mpr hz_ne
  refine ContinuousAt.continuousWithinAt ?_
  have h1 : ContinuousAt (fun z : ℂ => z - z₀) z :=
    (continuous_id.sub continuous_const).continuousAt
  have h2 : ContinuousAt (fun z : ℂ => (z - z₀)⁻¹) z := h1.inv₀ hsub_ne
  exact (continuousAt_const.mul h2)

private lemma simplePole_differentiableOn_annulus
    (z₀ : ℂ) (k : ℂ) (r₁ r₂ : ℝ) (hr₁ : 0 < r₁) :
    DifferentiableOn ℂ (fun z : ℂ => k * (z - z₀)⁻¹)
      (Metric.ball z₀ r₂ \ Metric.closedBall z₀ r₁) := by
  intro z hz
  have hz_not_inner : z ∉ Metric.closedBall z₀ r₁ := hz.2
  rw [Metric.mem_closedBall, not_le] at hz_not_inner
  have hz_ne : z ≠ z₀ := by
    intro heq
    rw [heq] at hz_not_inner
    simp at hz_not_inner
    linarith
  have hsub_ne : z - z₀ ≠ 0 := sub_ne_zero.mpr hz_ne
  refine DifferentiableAt.differentiableWithinAt ?_
  refine DifferentiableAt.const_mul ?_ k
  have h1 : DifferentiableAt ℂ (fun z : ℂ => z - z₀) z :=
    differentiableAt_id.sub_const z₀
  exact h1.inv hsub_ne

/-- **General bridge.** A regular chart-disk of radius `r` supplies a
regular annulus for every pair of radii `0 < r₁ ≤ r₂ ≤ r`. -/
theorem isRegularOnAnnulus_of_isRegularChartDiskAround
    (f : MeromorphicNonzero X) (x : X) (r r₁ r₂ : ℝ)
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂) (hr₂ : r₂ ≤ r)
    (hreg : IsRegularChartDiskAround f x r) :
    IsRegularOnAnnulus f x r₁ r₂ := by
  obtain ⟨R, g, hrR, h_target, hg_an, hg_ne, h_fact⟩ := hreg
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀
  -- closedBall r ⊆ ball R because r < R.
  have h_closed_r_sub_ball_R : Metric.closedBall z₀ r ⊆ Metric.ball z₀ R := by
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    linarith
  set k : ℂ :=
    ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ) with hk
  set kZ : ℤ := (MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) with hkZ
  -- Inclusions between the annulus and the disk-of-radius-r.
  have h_outer_sub : Metric.closedBall z₀ r₂ ⊆ Metric.closedBall z₀ r := by
    intro z hz
    rw [Metric.mem_closedBall] at hz ⊢
    linarith
  have h_outer_open_sub :
      Metric.ball z₀ r₂ ⊆ Metric.ball z₀ r := fun z hz => by
    rw [Metric.mem_ball] at hz ⊢
    linarith
  -- The analytic quotient `deriv g / g` on the closed ball.
  have hg_deriv : AnalyticOnNhd ℂ (deriv g) (Metric.closedBall z₀ r) :=
    hg_an.deriv
  have hquot : AnalyticOnNhd ℂ (fun z => deriv g z / g z)
      (Metric.closedBall z₀ r) := by
    intro z hz
    exact (hg_deriv z hz).div (hg_an z hz) (hg_ne z hz)
  refine ⟨fun z => k * (z - z₀)⁻¹ + deriv g z / g z, ?_, ?_, ?_, ?_⟩
  · -- ContinuousOn on closedBall z₀ r₂ \ ball z₀ r₁.
    have hpole := simplePole_continuousOn_annulus z₀ k r₁ r₂ hr₁
    have hquot_cont : ContinuousOn (fun z => deriv g z / g z)
        (Metric.closedBall z₀ r₂ \ Metric.ball z₀ r₁) := by
      refine (hquot.continuousOn).mono ?_
      intro z hz
      exact h_outer_sub hz.1
    exact hpole.add hquot_cont
  · -- DifferentiableOn on ball z₀ r₂ \ closedBall z₀ r₁.
    have hpole := simplePole_differentiableOn_annulus z₀ k r₁ r₂ hr₁
    have hquot_diff : DifferentiableOn ℂ (fun z => deriv g z / g z)
        (Metric.ball z₀ r₂ \ Metric.closedBall z₀ r₁) := by
      intro z hz
      have hzr : z ∈ Metric.closedBall z₀ r := by
        have := h_outer_open_sub hz.1
        exact Metric.ball_subset_closedBall this
      exact ((hquot z hzr).differentiableAt).differentiableWithinAt
    exact hpole.add hquot_diff
  · -- Inner-radius Laurent identity at radius r₁.
    intro θ
    set z : ℂ := z₀ + (r₁ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) with hz_def
    have hsub : z - z₀ = (r₁ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
      rw [hz_def]; ring
    have hexp_ne : Complex.exp (Complex.I * (θ : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    have hr1_complex_ne : (r₁ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr₁)
    have hsub_ne : z - z₀ ≠ 0 := by
      rw [hsub]; exact mul_ne_zero hr1_complex_ne hexp_ne
    have hz_ne : z ≠ z₀ := fun heq => hsub_ne (by rw [heq, sub_self])
    have hz_dist : dist z z₀ = r₁ := by
      rw [dist_eq_norm, hsub]
      have hcomm : Complex.exp (Complex.I * (θ : ℂ))
          = Complex.exp ((θ : ℂ) * Complex.I) := by rw [mul_comm]
      rw [hcomm, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      simp [abs_of_pos hr₁]
    -- z lies in closedBall z₀ r (via r₁ ≤ r₂ ≤ r).
    have hz_in_closed_r : z ∈ Metric.closedBall z₀ r := by
      rw [Metric.mem_closedBall, hz_dist]; linarith
    have hz_in_ball_R : z ∈ Metric.ball z₀ R :=
      h_closed_r_sub_ball_R hz_in_closed_r
    have hf := h_fact z hz_in_ball_R hz_ne
    -- Factor: f̃(z) = (z - z₀)^k · g z.
    have hg_at_z : AnalyticAt ℂ g z := hg_an z hz_in_closed_r
    have hg_diff_z : DifferentiableAt ℂ g z := hg_at_z.differentiableAt
    have hgz_ne : g z ≠ 0 := hg_ne z hz_in_closed_r
    have hz_target : z ∈ (chartAt ℂ x).target := h_target hz_in_closed_r
    -- chart-circleParameter equals symm of z.
    have hcp : (chartAt ℂ x).symm z = circleParameter (X := X) x r₁ θ := by
      unfold circleParameter
      rfl
    -- Compute logDiffCoeffAt at the chart-circle point.
    rw [hcp]
    rw [logDiffCoeffAt_circleParameter f x r₁ θ hz_target]
    have h_chart_inv : (chartAt ℂ x) (circleParameter (X := X) x r₁ θ) = z := by
      unfold circleParameter
      rw [(chartAt ℂ x).right_inv hz_target]
    -- f.toFun ∘ chart.symm at z equals (z-z₀)^k * g z.
    have h_F_at_z : (f.toFun ∘ (chartAt ℂ x).symm) z =
        (z - z₀) ^ kZ * g z := by
      have := hf
      simpa [smul_eq_mul] using this
    -- f.toFun (circleParameter x r₁ θ) = (f̃)(z).
    have h_f_eq : f.toFun (circleParameter (X := X) x r₁ θ) =
        (f.toFun ∘ (chartAt ℂ x).symm) z := by
      unfold circleParameter
      rfl
    -- Build EqOn neighborhood for deriv equality.
    have h_compl_open : IsOpen ({z₀}ᶜ : Set ℂ) := isOpen_compl_singleton
    have hz_in_compl : z ∈ ({z₀}ᶜ : Set ℂ) := hz_ne
    have hU_open : IsOpen (Metric.ball z₀ R ∩ ({z₀}ᶜ : Set ℂ)) :=
      Metric.isOpen_ball.inter h_compl_open
    have hz_in_U : z ∈ Metric.ball z₀ R ∩ ({z₀}ᶜ : Set ℂ) :=
      ⟨hz_in_ball_R, hz_in_compl⟩
    have h_eqOn :
        Set.EqOn (f.toFun ∘ (chartAt ℂ x).symm)
          (fun w : ℂ => (w - z₀) ^ kZ * g w)
          (Metric.ball z₀ R ∩ ({z₀}ᶜ : Set ℂ)) := by
      intro w hw
      have := h_fact w hw.1 hw.2
      simpa [smul_eq_mul] using this
    have h_evEq : (f.toFun ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 z]
        (fun w => (w - z₀) ^ kZ * g w) :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, hU_open.mem_nhds hz_in_U, h_eqOn⟩
    have h_deriv_eq :
        deriv (f.toFun ∘ (chartAt ℂ x).symm) z =
          deriv (fun w : ℂ => (w - z₀) ^ kZ * g w) z := h_evEq.deriv_eq
    rw [h_f_eq, h_F_at_z, h_deriv_eq]
    have hZB := logDeriv_zpow_smul_pointwise kZ z₀ g hz_ne hg_diff_z hgz_ne
    rw [hZB, div_eq_mul_inv]
  · -- Outer-radius Laurent identity at radius r₂.
    intro θ
    set z : ℂ := z₀ + (r₂ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) with hz_def
    have hsub : z - z₀ = (r₂ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
      rw [hz_def]; ring
    have hr₂_pos : 0 < r₂ := lt_of_lt_of_le hr₁ hr₁₂
    have hexp_ne : Complex.exp (Complex.I * (θ : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    have hr2_complex_ne : (r₂ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr₂_pos)
    have hsub_ne : z - z₀ ≠ 0 := by
      rw [hsub]; exact mul_ne_zero hr2_complex_ne hexp_ne
    have hz_ne : z ≠ z₀ := fun heq => hsub_ne (by rw [heq, sub_self])
    have hz_dist : dist z z₀ = r₂ := by
      rw [dist_eq_norm, hsub]
      have hcomm : Complex.exp (Complex.I * (θ : ℂ))
          = Complex.exp ((θ : ℂ) * Complex.I) := by rw [mul_comm]
      rw [hcomm, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      simp [abs_of_pos hr₂_pos]
    have hz_in_closed_r : z ∈ Metric.closedBall z₀ r := by
      rw [Metric.mem_closedBall, hz_dist]; linarith
    have hz_in_ball_R : z ∈ Metric.ball z₀ R :=
      h_closed_r_sub_ball_R hz_in_closed_r
    have hf := h_fact z hz_in_ball_R hz_ne
    have hg_at_z : AnalyticAt ℂ g z := hg_an z hz_in_closed_r
    have hg_diff_z : DifferentiableAt ℂ g z := hg_at_z.differentiableAt
    have hgz_ne : g z ≠ 0 := hg_ne z hz_in_closed_r
    have hz_target : z ∈ (chartAt ℂ x).target := h_target hz_in_closed_r
    have hcp : (chartAt ℂ x).symm z = circleParameter (X := X) x r₂ θ := by
      unfold circleParameter
      rfl
    rw [hcp]
    rw [logDiffCoeffAt_circleParameter f x r₂ θ hz_target]
    have h_F_at_z : (f.toFun ∘ (chartAt ℂ x).symm) z =
        (z - z₀) ^ kZ * g z := by
      simpa [smul_eq_mul] using hf
    have h_f_eq : f.toFun (circleParameter (X := X) x r₂ θ) =
        (f.toFun ∘ (chartAt ℂ x).symm) z := by
      unfold circleParameter
      rfl
    have h_compl_open : IsOpen ({z₀}ᶜ : Set ℂ) := isOpen_compl_singleton
    have hz_in_compl : z ∈ ({z₀}ᶜ : Set ℂ) := hz_ne
    have hU_open : IsOpen (Metric.ball z₀ R ∩ ({z₀}ᶜ : Set ℂ)) :=
      Metric.isOpen_ball.inter h_compl_open
    have hz_in_U : z ∈ Metric.ball z₀ R ∩ ({z₀}ᶜ : Set ℂ) :=
      ⟨hz_in_ball_R, hz_in_compl⟩
    have h_eqOn :
        Set.EqOn (f.toFun ∘ (chartAt ℂ x).symm)
          (fun w : ℂ => (w - z₀) ^ kZ * g w)
          (Metric.ball z₀ R ∩ ({z₀}ᶜ : Set ℂ)) := by
      intro w hw
      simpa [smul_eq_mul] using h_fact w hw.1 hw.2
    have h_evEq : (f.toFun ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 z]
        (fun w => (w - z₀) ^ kZ * g w) :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, hU_open.mem_nhds hz_in_U, h_eqOn⟩
    have h_deriv_eq :
        deriv (f.toFun ∘ (chartAt ℂ x).symm) z =
          deriv (fun w : ℂ => (w - z₀) ^ kZ * g w) z := h_evEq.deriv_eq
    rw [h_f_eq, h_F_at_z, h_deriv_eq]
    have hZB := logDeriv_zpow_smul_pointwise kZ z₀ g hz_ne hg_diff_z hgz_ne
    rw [hZB, div_eq_mul_inv]

end MeromorphicNonzero

end JacobianChallenge

end
