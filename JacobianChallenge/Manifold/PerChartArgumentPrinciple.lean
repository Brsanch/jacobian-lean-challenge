/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MultiHoleCauchyMeromorphic
import JacobianChallenge.Manifold.AnalyticPartExtraction
import JacobianChallenge.Manifold.MultiPoleLaurentExistence
import JacobianChallenge.Manifold.SinglePoleLaurentExtractionDischarge

/-! # Hypothesis-free per-chart argument principle (ZZ69)

This file composes ZZ64 (multi-hole Cauchy identity for finite-Laurent
meromorphic integrands), ZZ65 (analytic-part extraction), ZZ66 (multi-pole
Laurent assembly), and ZZ68 (single-pole Laurent discharge) into a
**hypothesis-free per-chart argument principle** on a complex disc:
the only assumptions are about `g` itself (meromorphic with finite-order
poles only at points of `S`, differentiable elsewhere), the geometry, and
no `a, N, h` are required from the caller.

## Headline statement

`circleIntegral_perChart_argumentPrinciple`:

> Let `c : ℂ`, `R > 0`, `S : Finset ℂ`, `ε : ℂ → ℝ` with `0 < ε x` and
> pairwise-disjoint `closedBall x (ε x) ⊆ ball c R` for `x ∈ S`. Let
> `g : ℂ → ℂ`, and let `U₀ ⊇ closedBall c R` be open with
> `DifferentiableOn ℂ g (U₀ \ S)`. Suppose at each `x ∈ S`, `g` is
> meromorphic at `x` with finite order. Then
>   `∮_{|z-c|=R} g(z) dz = ∑_{x ∈ S} ∮_{|z-x|=ε x} g(z) dz`.

The principal-coefficient data, the truncation bound, and the analytic
part are produced internally via ZZ65/ZZ66/ZZ68.

## Anti-cheat

* No `axiom`, no `sorry`.
* No existing definition or signature is changed.
* All bridges go through the four cited files plus mathlib.
-/

noncomputable section

open Complex MeasureTheory Set Metric Real Finset Filter Topology

namespace JacobianChallenge

namespace PerChartArgumentPrinciple

open AnalyticPartExtraction MultiPoleLaurentExistence MultiHoleCauchyMeromorphic

/-- **Headline.** Hypothesis-free per-chart argument principle on a disc.

Let `c : ℂ`, `R > 0`, `S : Finset ℂ`, and `ε : ℂ → ℝ` with `0 < ε x` and
pairwise-disjoint `closedBall x (ε x) ⊆ ball c R` for each `x ∈ S`.
Let `g : ℂ → ℂ` and `U₀ ⊇ closedBall c R` open such that `g` is
differentiable on `U₀ \ S` and meromorphic with finite order at each
`x ∈ S`. Then
`∮_{|z-c|=R} g = ∑_{y ∈ S} ∮_{|z-y|=ε y} g`. -/
theorem circleIntegral_perChart_argumentPrinciple
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (S : Finset ℂ) (ε : ℂ → ℝ)
    (hε_pos : ∀ x ∈ S, 0 < ε x)
    (hε_sub : ∀ x ∈ S, closedBall x (ε x) ⊆ ball c R)
    (hε_disj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x ∉ closedBall y (ε y))
    {g : ℂ → ℂ}
    {U₀ : Set ℂ} (hU₀_open : IsOpen U₀) (hU₀_sub : closedBall c R ⊆ U₀)
    (hg_diff : DifferentiableOn ℂ g (U₀ \ S))
    (hg_mero : ∀ x ∈ S, MeromorphicAt g x)
    (hg_finite : ∀ x ∈ S, meromorphicOrderAt g x ≠ ⊤) :
    (∮ z in C(c, R), g z)
      = ∑ y ∈ S, ∮ z in C(y, ε y), g z := by
  classical
  -- Step 1. Per-pole, discharge `SinglePoleLaurentExtraction` via ZZ68.
  have hExtract : ∀ x ∈ S, ∃ ε' : ℝ, 0 < ε' ∧ SinglePoleLaurentExtraction g x ε' :=
    fun x hxS => singlePole_laurent_extraction_of_meromorphicAt
      (hg_mero x hxS) (hg_finite x hxS)
  choose ε' hε'_pos hExtr using hExtract
  -- Unpack the per-pole witnesses: for x ∈ S, get Nx, ax, h_x, U_x.
  choose Nx ax h_x U_x hU_x_open hU_x_sub hh_x_diff hdec_x using hExtr
  -- Step 2. Define global principal-part data.
  let a' : ℂ → ℕ → ℂ := fun x =>
    if hx : x ∈ S then ax x hx else fun _ => 0
  let N' : ℂ → ℕ := fun x =>
    if hx : x ∈ S then Nx x hx else 0
  -- Step 3. Boundedness of `g − principalPartAt a' N' x` near each `x ∈ S`.
  -- On `U_x x hxS \ {x}`, `g z − principalPartAt a' N' x z = h_x x hxS z`,
  -- which is continuous on `U_x x hxS`. Choose a small closed ball of radius
  -- `ρ/2 ⊆ U_x x hxS` and use compactness.
  have hg_bdd : ∀ x ∈ S, ∃ V ∈ 𝓝 x,
      BddAbove (norm ∘ (fun z => g z - principalPartAt a' N' x z) '' (V \ {x})) := by
    intro x hxS
    -- A small open ball around `x` inside `U_x x hxS`.
    have hx_in_Ux : x ∈ U_x x hxS :=
      hU_x_sub x hxS (Metric.mem_closedBall_self (hε'_pos x hxS).le)
    obtain ⟨ρ, hρ_pos, hρ_sub⟩ :=
      Metric.isOpen_iff.mp (hU_x_open x hxS) x hx_in_Ux
    -- Use V := ball x (ρ/2). Then closedBall x (ρ/2) ⊆ ball x ρ ⊆ U_x x hxS.
    have hρ2_pos : 0 < ρ / 2 := by linarith
    have hclosed_sub : Metric.closedBall x (ρ / 2) ⊆ U_x x hxS := by
      intro z hz
      apply hρ_sub
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      linarith
    have hball_sub_closed : Metric.ball x (ρ / 2) ⊆ Metric.closedBall x (ρ / 2) :=
      Metric.ball_subset_closedBall
    have hball_sub_Ux : Metric.ball x (ρ / 2) ⊆ U_x x hxS :=
      fun z hz => hclosed_sub (hball_sub_closed hz)
    have hVnhd : Metric.ball x (ρ / 2) ∈ 𝓝 x :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ2_pos)
    refine ⟨Metric.ball x (ρ / 2), hVnhd, ?_⟩
    -- Bound `‖h_x x hxS‖` on the closed ball.
    have h_cont_on_Ux : ContinuousOn (h_x x hxS) (U_x x hxS) :=
      (hh_x_diff x hxS).continuousOn
    have h_cont_closed : ContinuousOn (h_x x hxS) (Metric.closedBall x (ρ / 2)) :=
      h_cont_on_Ux.mono hclosed_sub
    have h_compact : IsCompact (Metric.closedBall x (ρ / 2)) := isCompact_closedBall _ _
    obtain ⟨M, hM⟩ :=
      (h_compact.image_of_continuousOn (h_cont_closed.norm)).bddAbove
    refine ⟨M, ?_⟩
    rintro v ⟨z, ⟨hzV, hzx⟩, rfl⟩
    -- z ∈ ball x (ρ/2) \ {x}, so z ∈ U_x x hxS and z ≠ x.
    have hz_ne_x : z ≠ x := fun h => hzx (by simp [h])
    have hz_in_Ux : z ∈ U_x x hxS := hball_sub_Ux hzV
    -- Apply the witness decomposition.
    have hg_eq := hdec_x x hxS z hz_in_Ux hz_ne_x
    -- principalPartAt a' N' x z matches the witness sum because a', N' agree on S.
    have hPP_eq : principalPartAt a' N' x z =
        ∑ k ∈ Finset.Icc 1 (Nx x hxS), ax x hxS k * (z - x) ^ (-(k : ℤ)) := by
      unfold principalPartAt
      have hN_eq : N' x = Nx x hxS := by
        show (if hx : x ∈ S then Nx x hx else 0) = Nx x hxS
        simp [hxS]
      rw [hN_eq]
      apply Finset.sum_congr rfl
      intro k _
      have ha_eq : a' x k = ax x hxS k := by
        show (if hx : x ∈ S then ax x hx else fun _ => 0) k = ax x hxS k
        simp [hxS]
      rw [ha_eq]
    -- Now (g z - principalPartAt a' N' x z) = h_x x hxS z.
    have hdiff_eq : g z - principalPartAt a' N' x z = h_x x hxS z := by
      rw [hPP_eq, hg_eq]; ring
    show ‖g z - principalPartAt a' N' x z‖ ≤ M
    rw [hdiff_eq]
    have hz_closed : z ∈ Metric.closedBall x (ρ / 2) := hball_sub_closed hzV
    exact hM ⟨z, hz_closed, rfl⟩
  -- Step 4. ZZ65: extract the analytic part `h` on an open `U ⊇ closedBall c R`.
  have hSsubBall : (S : Set ℂ) ⊆ Metric.ball c R := by
    intro x hxS
    exact hε_sub x hxS (Metric.mem_closedBall_self (hε_pos x hxS).le)
  obtain ⟨U, hU_open, hU_sub, h, hh_diff, hh_eq⟩ :=
    exists_analytic_part_of_finite_pole_meromorphic
      hR S hSsubBall a' N' hU₀_open hU₀_sub hg_diff hg_bdd
  -- Step 5. Derive the pointwise circle decomposition: on `sphere c R` and on
  -- each `sphere y (ε y)`, points lie in `U \ S`, so `g z = h z + P_S z`.
  -- Outer sphere: sphere c R ⊆ closedBall c R ⊆ U, and avoids S since S ⊆ ball c R.
  have h_sphere_c_subU : Metric.sphere c R ⊆ U :=
    fun z hz => hU_sub (Metric.sphere_subset_closedBall hz)
  have h_sphere_c_avoidsS : ∀ z ∈ Metric.sphere c R, z ∉ (S : Set ℂ) := by
    intro z hz hzS
    have hzball : z ∈ Metric.ball c R := hSsubBall hzS
    rw [Metric.mem_sphere] at hz
    rw [Metric.mem_ball, hz] at hzball
    exact lt_irrefl R hzball
  have hg_outer : ∀ z ∈ Metric.sphere c R,
      g z = h z + ∑ x ∈ S, ∑ k ∈ Finset.Icc 1 (N' x),
              a' x k * (z - x) ^ (-(k : ℤ)) := by
    intro z hz
    have hzU : z ∈ U := h_sphere_c_subU hz
    have hzNotS : z ∉ (S : Set ℂ) := h_sphere_c_avoidsS z hz
    have := hh_eq z ⟨hzU, hzNotS⟩
    show g z = h z + fullPrincipalPart S a' N' z
    exact this
  -- Inner sphere centered at y ∈ S of radius ε y. Points lie in
  -- closedBall y (ε y) ⊆ ball c R ⊆ U₀ — and we need them in `U`.
  -- ZZ65 uses U := U₀, so closedBall c R ⊆ U₀ = U, and ball c R ⊆ closedBall c R ⊆ U.
  -- Each sphere y (ε y) ⊆ closedBall y (ε y) ⊆ ball c R ⊆ U.
  -- Each sphere y (ε y) avoids S: for x ≠ y, x ∉ closedBall y (ε y) by hε_disj;
  -- for x = y, y itself is the centre so y ∉ sphere y (ε y) (positive radius).
  have h_inner_subU : ∀ y ∈ S, Metric.sphere y (ε y) ⊆ U := by
    intro y hyS z hz
    have hz_cb : z ∈ Metric.closedBall y (ε y) := Metric.sphere_subset_closedBall hz
    have hz_ball : z ∈ Metric.ball c R := hε_sub y hyS hz_cb
    exact hU_sub (Metric.ball_subset_closedBall hz_ball)
  have h_inner_avoidsS : ∀ y ∈ S, ∀ z ∈ Metric.sphere y (ε y), z ∉ (S : Set ℂ) := by
    intro y hyS z hz hzS
    -- Either z = y or z ≠ y. If z = y, then y ∈ sphere y (ε y) means dist y y = ε y,
    -- but dist y y = 0 and ε y > 0 — contradiction.
    by_cases hzy : z = y
    · subst hzy
      rw [Metric.mem_sphere, dist_self] at hz
      exact (lt_irrefl 0) (hz ▸ hε_pos y hyS)
    · -- z ≠ y. z ∈ S so z ∈ closedBall z (ε z), and we have z ∈ closedBall y (ε y).
      have hzS' : z ∈ S := by exact_mod_cast hzS
      have hz_cb : z ∈ Metric.closedBall y (ε y) := Metric.sphere_subset_closedBall hz
      exact hε_disj z hzS' y hyS hzy hz_cb
  have hg_inner : ∀ y ∈ S, ∀ z ∈ Metric.sphere y (ε y),
      g z = h z + ∑ x ∈ S, ∑ k ∈ Finset.Icc 1 (N' x),
              a' x k * (z - x) ^ (-(k : ℤ)) := by
    intro y hyS z hz
    have hzU : z ∈ U := h_inner_subU y hyS hz
    have hzNotS : z ∉ (S : Set ℂ) := h_inner_avoidsS y hyS z hz
    have := hh_eq z ⟨hzU, hzNotS⟩
    show g z = h z + fullPrincipalPart S a' N' z
    exact this
  -- Step 6. ZZ64: assemble the multi-hole Cauchy identity.
  exact circleIntegral_finite_principal_part_eq
    hR S ε hε_pos hε_sub hε_disj hU_open hU_sub hh_diff a' N' hg_outer hg_inner

end PerChartArgumentPrinciple

end JacobianChallenge

end
