/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormNormedInner
import JacobianChallenge.Manifold.DiskChartCoverSeminormInnerBcf

set_option diagnostics.threshold 100

/-! # Per-chart BCF convergence implies inner-norm convergence

Given a sequence of holomorphic 1-forms `om_n : ℕ → HolomorphicOneForm X`
and a target `om_lim : HolomorphicOneForm X`, if for every base point
`x ∈ basePoints` the BCF restriction `localCoeffBcf cover (om_n k) hx`
converges to `localCoeffBcf cover om_lim hx` in BCF metric, then the
sequence `HolomorphicOneFormCoveredInner.ofForm cover (om_n k)`
converges to `ofForm cover om_lim` in the
`HolomorphicOneFormCoveredInner X cover` norm.

Proof: the inner cover norm equals
`basePoints.sup' (fun x => localCoeffMaxInner cover x (om_n k - om_lim))`,
each component equals the BCF norm of the difference (by the prior
`norm_localCoeffBcf_sub` bridge), and a Finset `sup'` of sequences
tending to `0` tends to `0`.

This is the key BW-readiness step: combined with `extract_diagonal_subseq`
+ `limitHolomorphicOneForm` (which provide the BCF-convergent
subsequence and its limit form), it produces norm-convergence in the
inner-cover-normed space, hence sequential compactness of the unit ball,
hence (via Riesz) finite-dimensionality.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff
open Set Metric HolomorphicOneForm Filter BoundedContinuousFunction

noncomputable section

namespace JacobianChallenge

namespace HolomorphicOneFormCoveredInner

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- The norm of the difference of two `ofForm`-views equals the
inner-cover seminorm of the underlying form difference. -/
theorem norm_sub_ofForm (cover : DiskChartCover X) [Nonempty X]
    (om₁ om₂ : HolomorphicOneForm X) :
    ‖ofForm cover om₁ - ofForm cover om₂‖
      = DiskChartCover.seminormValInner cover (om₁ - om₂) := by
  rw [norm_eq]
  -- `toForm (ofForm om₁ - ofForm om₂) = om₁ - om₂` definitionally.
  show DiskChartCover.seminormValInner cover
      (toForm cover (ofForm cover om₁ - ofForm cover om₂))
    = DiskChartCover.seminormValInner cover (om₁ - om₂)
  -- `toForm` is the identity on the underlying type.
  rfl

/-! ## Filter convergence transfer -/

/-- If for every base point `x ∈ basePoints` the per-chart BCF restriction
sequence `localCoeffBcf cover (om_n k) hx` converges to
`localCoeffBcf cover om_lim hx` in BCF metric, then the lifted sequence
converges to the lifted target in the inner-cover norm. -/
theorem tendsto_ofForm_of_tendsto_localCoeffBcf
    (cover : DiskChartCover X) [Nonempty X]
    (om_n : ℕ → HolomorphicOneForm X) (om_lim : HolomorphicOneForm X)
    (h_bcf : ∀ (x : X) (hx : x ∈ cover.basePoints),
      Tendsto (fun k => DiskChartCover.localCoeffBcf cover (om_n k) hx)
        atTop (𝓝 (DiskChartCover.localCoeffBcf cover om_lim hx))) :
    Tendsto (fun k => ofForm cover (om_n k)) atTop
      (𝓝 (ofForm cover om_lim)) := by
  -- Reduce to: `∀ ε > 0, ∃ N, ∀ k ≥ N, dist ... < ε`.
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Per-base-point BCF convergence: choose `N_x` such that
  -- `‖localCoeffBcf cover (om_n k) hx - localCoeffBcf cover om_lim hx‖ < ε`
  -- for all `k ≥ N_x`. Then `N := max_x N_x` (finite Finset).
  have h_pt : ∀ (x : X) (hx : x ∈ cover.basePoints), ∃ N, ∀ k ≥ N,
      ‖DiskChartCover.localCoeffBcf cover (om_n k) hx
        - DiskChartCover.localCoeffBcf cover om_lim hx‖ < ε := by
    intro x hx
    have h_tend := (h_bcf x hx)
    rw [Metric.tendsto_atTop] at h_tend
    obtain ⟨N, hN⟩ := h_tend ε hε
    refine ⟨N, fun k hk => ?_⟩
    have := hN k hk
    rw [dist_eq_norm] at this
    exact this
  -- Convert the per-base-point thresholds to a uniform `N`.
  classical
  let N_of : (x : X) → x ∈ cover.basePoints → ℕ := fun x hx => (h_pt x hx).choose
  have N_of_spec : ∀ (x : X) (hx : x ∈ cover.basePoints), ∀ k ≥ N_of x hx,
      ‖DiskChartCover.localCoeffBcf cover (om_n k) hx
        - DiskChartCover.localCoeffBcf cover om_lim hx‖ < ε := fun x hx =>
    (h_pt x hx).choose_spec
  -- Aggregate via `Finset.sup'` over `basePoints.attach`.
  have h_attach_nonempty := cover.basePoints_nonempty.attach
  set N : ℕ := cover.basePoints.attach.sup'
    h_attach_nonempty (fun x => N_of x.val x.property) with hN_def
  refine ⟨N, fun k hk => ?_⟩
  -- For each base point `x ∈ basePoints`, `k ≥ N ≥ N_of x hx`.
  have hk_each : ∀ (x : X) (hx : x ∈ cover.basePoints), k ≥ N_of x hx := by
    intro x hx
    have h_le : N_of x hx ≤ N := by
      rw [hN_def]
      exact Finset.le_sup' (fun y : {y // y ∈ cover.basePoints} =>
        N_of y.val y.property) (Finset.mem_attach _ ⟨x, hx⟩)
    exact h_le.trans hk
  -- Bound `dist` by the inner-cover seminorm.
  rw [dist_eq_norm, norm_sub_ofForm cover (om_n k) om_lim]
  -- `seminormValInner cover (om_n k - om_lim)
  --   = basePoints.sup' (fun x => localCoeffMaxInner cover x (om_n k - om_lim))`
  -- and `localCoeffMaxInner cover x (om_n k - om_lim)
  --   = ‖localCoeffBcf cover (om_n k - om_lim) hx‖
  --   = ‖localCoeffBcf cover (om_n k) hx - localCoeffBcf cover om_lim hx‖`.
  unfold DiskChartCover.seminormValInner
  refine Finset.sup'_lt_iff (cover.basePoints_nonempty) (a := ε) |>.mpr ?_
  intro x hx
  rw [← DiskChartCover.norm_localCoeffBcf cover (om_n k - om_lim) hx,
      DiskChartCover.localCoeff_sub_bcf_eq]
  exact N_of_spec x hx k (hk_each x hx)

end HolomorphicOneFormCoveredInner

end JacobianChallenge

end
