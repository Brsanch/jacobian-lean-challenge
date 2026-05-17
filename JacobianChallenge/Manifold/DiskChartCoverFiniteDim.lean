/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverRiesz
import JacobianChallenge.Manifold.DiskChartCoverDensityAggregate
import JacobianChallenge.Manifold.DiskChartCoverDiagonal
import JacobianChallenge.Manifold.HolomorphicOneFormNormedInnerTendsto
import JacobianChallenge.Manifold.HolomorphicOneFormNormedCovered
import JacobianChallenge.Manifold.HodgeFiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Sequences

set_option linter.unusedSectionVars false

/-! # Finite-dimensionality of `HolomorphicOneForm X` (Forster Riesz)

End-to-end composition giving `FiniteDimensional ℂ (HolomorphicOneForm X)`
unconditionally on a compact connected complex 1-manifold `X`:

* outer-norm closed ball is sequentially compact (extract subseq + limit
  form + inner convergence + density bound → outer convergence);
* in a metric space, seq-compact ⇒ compact;
* Riesz gives `FiniteDimensional` of the wrapper;
* transport to `HolomorphicOneForm X` (defeq).

No `sorry`, no `axiom`.
-/

open Set Metric Filter Topology

open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **Closed outer-norm ball is sequentially compact.** -/
theorem isSeqCompact_closedBall_outer
    (cover : DiskChartCover X) [Nonempty X] (r : ℝ) :
    IsSeqCompact (Metric.closedBall
      (0 : HolomorphicOneFormCovered X cover) r) := by
  -- Density bound.
  obtain ⟨M, hM_nn, hM⟩ := cover.exists_density_bound
  intro om_seq h_in
  -- Bound r ≥ 0 from any sequence element.
  have h_r_nn : 0 ≤ r := by
    have h0 := h_in 0
    rw [mem_closedBall, dist_zero_right] at h0
    exact le_trans (norm_nonneg _) h0
  -- Per-k outer bound on toForm.
  have h_bound : ∀ k, seminormVal cover
      (HolomorphicOneFormCovered.toForm cover (om_seq k)) ≤ r := fun k => by
    have hk := h_in k
    rw [mem_closedBall, dist_zero_right] at hk
    exact hk
  -- Extract diagonal subseq.
  obtain ⟨ψ, hψ_mono, h_per_y⟩ := extract_diagonal_subseq cover r h_r_nn
    (fun k => HolomorphicOneFormCovered.toForm cover (om_seq k)) h_bound
  -- Build limit form.
  let om_seq_form : ℕ → HolomorphicOneForm X := fun k =>
    HolomorphicOneFormCovered.toForm cover (om_seq k)
  let om_lim : HolomorphicOneForm X :=
    cover.limitHolomorphicOneForm om_seq_form h_per_y
  -- Per-base-point BCF tendsto into the right form via the compatibility lemma.
  have h_bcf_full : ∀ (x : X) (hx : x ∈ cover.basePoints),
      Tendsto (fun k => localCoeffBcf cover (om_seq_form (ψ k)) hx)
        atTop (𝓝 (localCoeffBcf cover om_lim hx)) := fun x hx => by
    have h_chosen := (h_per_y x hx).choose_spec
    rw [cover.localCoeffBcf_limitHolomorphicOneForm om_seq_form h_per_y hx]
    exact h_chosen
  -- Apply inner-norm tendsto.
  have h_inner : Tendsto
      (fun k => HolomorphicOneFormCoveredInner.ofForm cover
        (om_seq_form (ψ k)))
      atTop (𝓝 (HolomorphicOneFormCoveredInner.ofForm cover om_lim)) :=
    HolomorphicOneFormCoveredInner.tendsto_ofForm_of_tendsto_localCoeffBcf
      cover (fun k => om_seq_form (ψ k)) om_lim h_bcf_full
  -- Upgrade to outer-norm tendsto via density bound.
  -- We need: `dist (ofForm cover (om_seq_form (ψ k))) (ofForm cover om_lim) → 0`
  -- in OUTER norm.
  have h_outer_tendsto :
      Tendsto (fun k => HolomorphicOneFormCovered.ofForm cover
        (om_seq_form (ψ k)))
        atTop (𝓝 (HolomorphicOneFormCovered.ofForm cover om_lim)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- From inner tendsto extract N s.t. inner dist < ε / max M 1 for k ≥ N.
    rw [Metric.tendsto_atTop] at h_inner
    set Md : ℝ := max M 1 with hMd_def
    have hMd_pos : 0 < Md := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hMd_nn : 0 ≤ Md := hMd_pos.le
    obtain ⟨N, hN⟩ := h_inner (ε / Md) (div_pos hε hMd_pos)
    refine ⟨N, fun k hk => ?_⟩
    have h_inner_k := hN k hk
    -- h_inner_k : dist (ofForm_inner (om_seq_form (ψ k))) (ofForm_inner om_lim) < ε / Md.
    -- Inner-norm dist = seminormValInner of the difference.
    rw [dist_eq_norm] at h_inner_k
    rw [HolomorphicOneFormCoveredInner.norm_sub_ofForm] at h_inner_k
    -- Outer-norm dist:
    rw [dist_eq_norm]
    -- ‖ofForm cover (om_seq_form (ψ k)) - ofForm cover om_lim‖_outer
    --   = seminormVal cover (om_seq_form (ψ k) - om_lim).
    -- Density: seminormVal ≤ M · seminormValInner.
    have h_norm_outer :
        ‖HolomorphicOneFormCovered.ofForm cover (om_seq_form (ψ k))
          - HolomorphicOneFormCovered.ofForm cover om_lim‖
          = seminormVal cover (om_seq_form (ψ k) - om_lim) := by
      rw [HolomorphicOneFormCovered.norm_eq]
      rfl
    rw [h_norm_outer]
    -- Density: ≤ M · seminormValInner (om_seq_form (ψ k) - om_lim) = M · inner-dist.
    have h_density := hM (om_seq_form (ψ k) - om_lim)
    -- M · inner-dist ≤ M · (ε/Md). Need < ε.
    have h_M_le_Md : M ≤ Md := le_max_left _ _
    calc seminormVal cover (om_seq_form (ψ k) - om_lim)
        ≤ M * seminormValInner cover (om_seq_form (ψ k) - om_lim) := h_density
      _ ≤ Md * seminormValInner cover (om_seq_form (ψ k) - om_lim) := by
          exact mul_le_mul_of_nonneg_right h_M_le_Md
            (seminormValInner_nonneg cover _)
      _ < Md * (ε / Md) := by
          refine mul_lt_mul_of_pos_left ?_ hMd_pos
          exact h_inner_k
      _ = ε := by field_simp
  -- Conclude: limit ∈ closed ball.
  refine ⟨HolomorphicOneFormCovered.ofForm cover om_lim, ?_, ψ, hψ_mono, ?_⟩
  · -- ‖ofForm om_lim‖ ≤ r.
    rw [mem_closedBall, dist_zero_right]
    -- Norm continuous, sequence bounded by r.
    have h_norm_cont := h_outer_tendsto.norm
    have h_bound_seq : ∀ k, ‖HolomorphicOneFormCovered.ofForm cover
        (om_seq_form (ψ k))‖ ≤ r := fun k => by
      -- = seminormVal cover (om_seq_form (ψ k)) ≤ r.
      rw [HolomorphicOneFormCovered.norm_ofForm]
      exact h_bound (ψ k)
    exact le_of_tendsto_of_tendsto' h_norm_cont tendsto_const_nhds
      h_bound_seq
  · -- om_seq ∘ ψ → ofForm cover om_lim.
    -- om_seq (ψ k) = ofForm cover (toForm cover (om_seq (ψ k)))
    --             = ofForm cover (om_seq_form (ψ k))
    -- via ofForm_toForm (defeq on the type alias).
    exact h_outer_tendsto

/-- **Closed outer-norm ball is compact** (metric ⇒ seq-compact ⇒ compact). -/
theorem isCompact_closedBall_outer
    (cover : DiskChartCover X) [Nonempty X] (r : ℝ) :
    IsCompact (Metric.closedBall
      (0 : HolomorphicOneFormCovered X cover) r) :=
  (cover.isSeqCompact_closedBall_outer r).isCompact

/-- **FiniteDimensional via Riesz** on the cover-indexed wrapper. -/
theorem finiteDimensional_holomorphicOneFormCovered
    (cover : DiskChartCover X) [Nonempty X] :
    FiniteDimensional ℂ (HolomorphicOneFormCovered X cover) :=
  FiniteDimensional.of_isCompact_closedBall₀ (𝕜 := ℂ) (V := _)
    (r := 1) one_pos (cover.isCompact_closedBall_outer 1)

/-- **FiniteDimensional of `HolomorphicOneForm X`**, unconditional on a
compact connected complex 1-manifold (given a `DiskChartCover`).

The `HolomorphicOneFormCovered` wrapper is definitionally equal to
`HolomorphicOneForm X`, so the `FiniteDimensional` instance transfers
through `Module.Finite.equiv` (or directly via defeq). -/
theorem finiteDimensional_holomorphicOneForm
    (cover : DiskChartCover X) [Nonempty X] :
    FiniteDimensional ℂ (HolomorphicOneForm X) := by
  -- Use the wrapper instance + the linear equivalence `toForm`.
  haveI : FiniteDimensional ℂ (HolomorphicOneFormCovered X cover) :=
    cover.finiteDimensional_holomorphicOneFormCovered
  -- The two are defeq; transfer FiniteDimensional via the identity LinearEquiv.
  exact this

/-- **`HolomorphicOneFormFiniteDim X`** holds unconditionally on a
compact connected complex 1-manifold (using `DiskChartCover.exists_of_compact`). -/
theorem holomorphicOneFormFiniteDim_holds
    [CompactSpace X] [Nonempty X] :
    HolomorphicOneFormFiniteDim X := by
  -- Get a cover via `exists_of_compact`.
  obtain ⟨cover⟩ := DiskChartCover.exists_of_compact (X := X)
  -- Apply finite-dim through the cover.
  unfold HolomorphicOneFormFiniteDim
  exact cover.finiteDimensional_holomorphicOneForm

end DiskChartCover

end JacobianChallenge

end
