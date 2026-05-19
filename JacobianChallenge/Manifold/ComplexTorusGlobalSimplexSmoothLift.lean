/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusGlobalSimplexContLift
import JacobianChallenge.Manifold.ComplexTorus
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Smoothness of the global continuous lift

The continuous lift `globalSimplexContLift L σ : C((Fin 2 → ℝ), ℂ)`
is actually **smooth**, because `mkQ : ℂ → ℂ ⧸ L` is a local
diffeomorphism (the chart inverses on `ℂ ⧸ L` are smooth sections of
`mkQ`).

Locally near any `p₀ : (Fin 2 → ℝ)`:

* The chart `φ := chartAt ℂ (σ.toFun p₀)` is `ContMDiffOn` on its
  source, mapping `ℂ ⧸ L` to a small ball in `ℂ`.
* On `U := σ.toFun ⁻¹' φ.source` (an open nbhd of `p₀`), the
  composition `φ ∘ σ.toFun : U → ℂ` is smooth.
* The difference `F p - φ (σ.toFun p) ∈ L` is continuous in `p` on
  `U` (both summands are continuous and they lift the same quotient
  class). By discreteness of `L`, this difference is locally constant.
* Hence `F` agrees with `φ ∘ σ.toFun + lam₀` (where `lam₀ ∈ L` is the
  local constant) on an open nbhd of `p₀`, so `F` is `ContMDiff` there.

## What this file ships

* `ComplexTorus.globalSimplexContLift_contMDiff` — `F` is `ContMDiff` of
  any regularity `n`.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff Topology

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## A small ball around `lam₀ ∈ L` contains only `lam₀` from `L`. -/

private lemma exists_isolated_ball_L (lam₀ : ℂ) (hlam₀ : lam₀ ∈ L) :
    ∃ ε > 0, ∀ lam ∈ (L : Set ℂ), dist lam lam₀ < ε → lam = lam₀ := by
  -- L is discrete; shift to 0 via lam - lam₀ ∈ L.
  refine ⟨discRadius L, discRadius_pos L, fun lam hlam hd => ?_⟩
  have h_sub : lam - lam₀ ∈ L := L.sub_mem hlam hlam₀
  have h_norm : ‖lam - lam₀‖ < discRadius L := by
    have : dist lam lam₀ = ‖lam - lam₀‖ := dist_eq_norm _ _
    rw [← this]; exact hd
  have h_zero := discRadius_separates L (lam - lam₀) h_sub h_norm
  exact sub_eq_zero.mp h_zero

/-! ## Local smooth representation of `F` near a point -/

private lemma globalSimplexContLift_eventuallyEq_local
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (p₀ : Fin 2 → ℝ) :
    let φ := chartAt ℂ (σ.toFun p₀)
    let F := globalSimplexContLift L σ
    let lam₀ : ℂ := F p₀ - φ (σ.toFun p₀)
    (fun p : Fin 2 → ℝ => (F p : ℂ))
      =ᶠ[nhds p₀] (fun p => (φ : (ℂ ⧸ L) → ℂ) (σ.toFun p) + lam₀) := by
  intro φ F lam₀
  -- Helper: `L.mkQ ∘ chartAt q = id` on chart source.
  -- `chartAt q = (localChart _ q.out).symm`. Its `.symm` is `localChart _ q.out`,
  -- whose `.toFun` is `mkQ` (restricted to ball). Combined with chart.left_inv:
  -- for `q' ∈ chart.source`, `chart.symm (chart q') = q'`, hence `mkQ (chart q') = q'`.
  have h_mkQ_chart_id : ∀ {q' : ℂ ⧸ L}, q' ∈ (chartAt ℂ (σ.toFun p₀)).source →
      L.mkQ ((chartAt ℂ (σ.toFun p₀)) q') = q' := by
    intro q' hq'
    -- chart.symm at chart(q') equals q' (left_inv).
    have h_left : (chartAt ℂ (σ.toFun p₀)).symm ((chartAt ℂ (σ.toFun p₀)) q') = q' :=
      (chartAt ℂ (σ.toFun p₀)).left_inv hq'
    -- The symm of chartAt q is `localChart _ q.out`, which on ball acts as mkQ.
    -- chart q' ∈ chart.target = ball, so (localChart).toFun (chart q') = mkQ (chart q').
    -- This is rfl by definition of localChart via InjOn.toPartialEquiv L.mkQ s.
    have h_target : (chartAt ℂ (σ.toFun p₀)) q'
        ∈ (chartAt ℂ (σ.toFun p₀)).target :=
      (chartAt ℂ (σ.toFun p₀)).map_source hq'
    have h_apply : (chartAt ℂ (σ.toFun p₀)).symm ((chartAt ℂ (σ.toFun p₀)) q')
        = L.mkQ ((chartAt ℂ (σ.toFun p₀)) q') := by
      -- chartAt.symm = localChart. Its toFun on ball = mkQ.
      -- The definitional path: localChart is built via InjOn.toPartialEquiv L.mkQ s,
      -- so localChart.toFun = (Set.restrict s L.mkQ) which is L.mkQ for x ∈ s.
      rfl
    rw [h_apply] at h_left
    exact h_left
  -- Apply to φ at σ.toFun p₀.
  have h_φ_lifts : L.mkQ (φ (σ.toFun p₀)) = σ.toFun p₀ :=
    h_mkQ_chart_id (mem_chart_source ℂ (σ.toFun p₀))
  have h_F_lifts : L.mkQ (F p₀) = σ.toFun p₀ :=
    globalSimplexContLift_lifts L σ p₀
  have hlam₀_mem : lam₀ ∈ L := by
    show F p₀ - φ (σ.toFun p₀) ∈ L
    have h_mkQ : L.mkQ (F p₀ - φ (σ.toFun p₀)) = 0 := by
      rw [map_sub]; rw [h_F_lifts, h_φ_lifts, sub_self]
    exact (Submodule.Quotient.mk_eq_zero L).mp h_mkQ
  -- Now use discreteness of L to show `(F p - φ (σ.toFun p)) ∈ L` is locally constant.
  -- The function `g(p) := F p - φ (σ.toFun p)` is continuous on a nbhd of `p₀`
  -- where `σ.toFun p ∈ φ.source`. Its value at `p₀` is `lam₀`. By discreteness of L,
  -- it equals `lam₀` on a small enough nbhd.
  obtain ⟨ε, hε_pos, h_iso⟩ := exists_isolated_ball_L L lam₀ hlam₀_mem
  -- Define the continuity domain: σ.toFun⁻¹(φ.source).
  let U : Set (Fin 2 → ℝ) := σ.toFun ⁻¹' (φ.source : Set (ℂ ⧸ L))
  have hU_open : IsOpen U := φ.open_source.preimage σ.smooth.continuous
  have hU_p₀ : p₀ ∈ U := by
    show σ.toFun p₀ ∈ φ.source
    exact mem_chart_source ℂ (σ.toFun p₀)
  -- The function g(p) := F p - φ (σ.toFun p) is continuous on U.
  have h_g_cont : ContinuousOn (fun p => F p - φ (σ.toFun p)) U := by
    apply ContinuousOn.sub
    · exact (globalSimplexContLift_continuous L σ).continuousOn
    · -- φ ∘ σ.toFun : U → ℂ continuous on U.
      have h_φ_on : ContinuousOn (φ : (ℂ ⧸ L) → ℂ) φ.source :=
        φ.continuousOn
      have h_σ_cont : Continuous σ.toFun := σ.smooth.continuous
      exact h_φ_on.comp h_σ_cont.continuousOn (fun p hp => hp)
  -- Apply continuity at p₀ to get a nbhd on which g is close to lam₀.
  have h_g_p₀ : (fun p => F p - φ (σ.toFun p)) p₀ = lam₀ := rfl
  -- g is continuous at p₀ within U; combine with hU_open.mem_nhds.
  have h_cont_p₀ : ContinuousAt (fun p => F p - φ (σ.toFun p)) p₀ :=
    (h_g_cont.continuousAt (hU_open.mem_nhds hU_p₀))
  -- For our ε, we get a nbhd V of p₀ where g(p) is within ε of lam₀.
  have h_ev_close := h_cont_p₀.tendsto (Metric.ball_mem_nhds lam₀ hε_pos)
  -- h_ev_close says: ∀ᶠ p in 𝓝 p₀, g p ∈ Metric.ball lam₀ ε.
  -- We need: ∀ᶠ p in 𝓝 p₀, p ∈ U ∧ g p = lam₀.
  -- For p in U, mkQ(g p) = 0 (both summands lift σ.toFun p), so g p ∈ L.
  -- Combined with closeness to lam₀ and isolation, g p = lam₀.
  -- Final eventually statement.
  refine Filter.Eventually.mp
    (Filter.eventually_and.mpr ⟨hU_open.mem_nhds hU_p₀, h_ev_close⟩) ?_
  filter_upwards with p ⟨hpU, hp_close⟩
  -- Goal: F p = φ (σ.toFun p) + lam₀.
  -- g p = F p - φ (σ.toFun p) ∈ L (both lift σ.toFun p).
  have h_g_p_lifts : L.mkQ (F p - φ (σ.toFun p)) = 0 := by
    rw [map_sub]
    have h_F_p : L.mkQ (F p) = σ.toFun p :=
      globalSimplexContLift_lifts L σ p
    have h_φ_p : L.mkQ (φ (σ.toFun p)) = σ.toFun p :=
      h_mkQ_chart_id hpU
    rw [h_F_p, h_φ_p, sub_self]
  have h_g_p_in_L : F p - φ (σ.toFun p) ∈ L :=
    (Submodule.Quotient.mk_eq_zero L).mp h_g_p_lifts
  -- Now apply isolation.
  have h_g_eq_lam₀ : F p - φ (σ.toFun p) = lam₀ :=
    h_iso _ h_g_p_in_L (by
      have : dist (F p - φ (σ.toFun p)) lam₀ < ε := hp_close
      exact this)
  -- Rearrange.
  linear_combination h_g_eq_lam₀

/-! ## Smoothness of the global continuous lift -/

/-- **The global continuous lift is `ContMDiff` at C^∞ regularity.** -/
theorem globalSimplexContLift_contMDiff
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun p : Fin 2 → ℝ => (globalSimplexContLift L σ p : ℂ)) := by
  intro p₀
  -- Use local representation.
  have h_eq := globalSimplexContLift_eventuallyEq_local L σ p₀
  -- Show ContMDiffAt of the RHS at p₀, then transport via eventuallyEq.
  have h_RHS : ContMDiffAt 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun p : Fin 2 → ℝ =>
        ((chartAt ℂ (σ.toFun p₀)) : (ℂ ⧸ L) → ℂ) (σ.toFun p)
          + (globalSimplexContLift L σ p₀ - (chartAt ℂ (σ.toFun p₀)) (σ.toFun p₀)))
      p₀ := by
    have h_const : ContMDiffAt 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
        (fun _ : Fin 2 → ℝ =>
          globalSimplexContLift L σ p₀
            - (chartAt ℂ (σ.toFun p₀)) (σ.toFun p₀)) p₀ := contMDiffAt_const
    have h_σAt : ContMDiffAt 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞ σ.toFun p₀ := σ.smooth p₀
    have h_φ_on : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        ((chartAt ℂ (σ.toFun p₀)) : (ℂ ⧸ L) → ℂ)
        (chartAt ℂ (σ.toFun p₀)).source := contMDiffOn_chart
    have h_σ_in_source : σ.toFun p₀ ∈ (chartAt ℂ (σ.toFun p₀)).source :=
      mem_chart_source ℂ (σ.toFun p₀)
    have h_φAt : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        ((chartAt ℂ (σ.toFun p₀)) : (ℂ ⧸ L) → ℂ) (σ.toFun p₀) :=
      h_φ_on.contMDiffAt
        ((chartAt ℂ (σ.toFun p₀)).open_source.mem_nhds h_σ_in_source)
    have h_comp : ContMDiffAt 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
        (fun p : Fin 2 → ℝ =>
          ((chartAt ℂ (σ.toFun p₀)) : (ℂ ⧸ L) → ℂ) (σ.toFun p)) p₀ :=
      h_φAt.comp p₀ h_σAt
    exact h_comp.add h_const
  -- The eventuallyEq goes from F to the RHS expression; congr direction is `f =ᶠ g`
  -- with `f` being the original (here F).
  exact h_RHS.congr_of_eventuallyEq h_eq

end ComplexTorus

end JacobianChallenge

end
