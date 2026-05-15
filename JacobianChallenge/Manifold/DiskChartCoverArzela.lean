/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverLipschitz
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

set_option diagnostics.threshold 100

/-! # Arzelà-Ascoli for `localCoeff` on the inner disk

For each base point `x ∈ basePoints` and any bounded sequence
`om_n : ℕ → HolomorphicOneForm X` with `seminormVal cover (om_n n) ≤ M`,
the family of `localCoeff (om_n n) x` restricted to the inner closed
disk is bounded and equicontinuous (chip 5a). By Arzelà-Ascoli,
there is a subsequence convergent uniformly on the inner closed disk
to a continuous limit function (packaged as a bounded continuous
function on the subtype).

## Main result

* `DiskChartCover.arzela_localCoeff_innerDisk` — produces a strictly
  monotone subsequence and a limit `g_lim : C(↥closedBall, ℂ)` such
  that the restricted `localCoeff` sequence tends to `g_lim` in the
  uniform metric on the closed disk.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff Pointwise
open Set Metric HolomorphicOneForm Filter

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

omit [IsManifold 𝓘(ℂ) ω X] in
/-- The inner closed disk's subtype is a compact space. -/
private lemma innerDisk_compactSpace (cover : DiskChartCover X) (x : X) :
    CompactSpace ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)

/-- For a base point and any `om : HolomorphicOneForm X`, `localCoeff om x`
is continuous on the inner closed disk. -/
private lemma localCoeff_continuousOn_innerDisk (cover : DiskChartCover X)
    (om : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints) :
    ContinuousOn (localCoeff om x)
      (closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) := by
  have h_inner_le_outer :
      cover.innerRadius x ≤ cover.outerRadius x :=
    le_of_lt (cover.innerRadius_lt_outerRadius x hx)
  have h_subset :
      closedBall ((chartAt ℂ x) x) (cover.innerRadius x)
        ⊆ (chartAt ℂ x).target :=
    (closedBall_subset_closedBall h_inner_le_outer).trans
      (cover.closedDisk_in_target x hx)
  exact (localCoeff_differentiableOn om x).continuousOn.mono h_subset

/-- The norm of `localCoeff om x w` is bounded by `seminormVal cover om`
for `w` in the inner closed disk. -/
private lemma norm_localCoeff_le_seminormVal_innerDisk
    (cover : DiskChartCover X) [Nonempty X] (om : HolomorphicOneForm X)
    {x : X} (hx : x ∈ cover.basePoints) {w : ℂ}
    (hw : w ∈ closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :
    ‖localCoeff om x w‖ ≤ seminormVal cover om := by
  have h_inner_le_outer :
      cover.innerRadius x ≤ cover.outerRadius x :=
    le_of_lt (cover.innerRadius_lt_outerRadius x hx)
  have hw_outer : w ∈ closedBall ((chartAt ℂ x) x) (cover.outerRadius x) :=
    (closedBall_subset_closedBall h_inner_le_outer) hw
  have h_bound := norm_localCoeff_le_localCoeffMax cover om hx hw_outer
  have h_le : localCoeffMax cover x om ≤ seminormVal cover om :=
    Finset.le_sup' (fun y => localCoeffMax cover y om) hx
  exact h_bound.trans h_le

/-- Bundle `localCoeff om x` restricted to the inner closed disk as a
`BoundedContinuousFunction`. -/
noncomputable def localCoeffBcf
    (cover : DiskChartCover X) [Nonempty X] (om : HolomorphicOneForm X)
    {x : X} (hx : x ∈ cover.basePoints) :
    BoundedContinuousFunction
      ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ where
  toFun := fun w => localCoeff om x w.1
  continuous_toFun :=
    (localCoeff_continuousOn_innerDisk cover om hx).restrict
  map_bounded' := by
    refine ⟨2 * seminormVal cover om, fun u v => ?_⟩
    have h_u := norm_localCoeff_le_seminormVal_innerDisk cover om hx u.2
    have h_v := norm_localCoeff_le_seminormVal_innerDisk cover om hx v.2
    calc dist (localCoeff om x u.1) (localCoeff om x v.1)
        ≤ ‖localCoeff om x u.1‖ + ‖localCoeff om x v.1‖ :=
          dist_le_norm_add_norm _ _
      _ ≤ seminormVal cover om + seminormVal cover om := add_le_add h_u h_v
      _ = 2 * seminormVal cover om := by ring

/-- Evaluation: `localCoeffBcf cover om hx ⟨w, hw⟩ = localCoeff om x w`. -/
@[simp]
lemma localCoeffBcf_apply (cover : DiskChartCover X) [Nonempty X]
    (om : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints)
    (w : ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x))) :
    localCoeffBcf cover om hx w = localCoeff om x w.1 := rfl

/-- **Per-chart Arzelà-Ascoli for `localCoeff`.** Given a sequence of
holomorphic 1-forms with uniformly bounded seminorm and a base point
`x`, the bundled `localCoeffBcf` sequence has a subsequence convergent
in the BoundedContinuousFunction metric on the inner closed disk
to some limit. -/
theorem arzela_localCoeff_innerDisk (cover : DiskChartCover X) [Nonempty X]
    (M : ℝ) (hM : 0 ≤ M)
    (om_n : ℕ → HolomorphicOneForm X)
    (h_bound : ∀ n, seminormVal cover (om_n n) ≤ M)
    {x : X} (hx : x ∈ cover.basePoints) :
    ∃ (φ : ℕ → ℕ) (g_lim : BoundedContinuousFunction
        ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ),
      StrictMono φ ∧
      Tendsto (fun k => localCoeffBcf cover (om_n (φ k)) hx) atTop (𝓝 g_lim) := by
  haveI : CompactSpace
      ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :=
    innerDisk_compactSpace cover x
  let g : ℕ → BoundedContinuousFunction
      ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ :=
    fun n => localCoeffBcf cover (om_n n) hx
  -- Values lie in closedBall 0 M.
  have h_values : ∀ (f : BoundedContinuousFunction _ ℂ) (u : _),
      f ∈ Set.range g → f u ∈ closedBall (0 : ℂ) M := by
    rintro f u ⟨n, rfl⟩
    rw [mem_closedBall_zero_iff]
    show ‖localCoeff (om_n n) x u.1‖ ≤ M
    exact (norm_localCoeff_le_seminormVal_innerDisk cover (om_n n) hx u.2).trans
      (h_bound n)
  -- Equicontinuity via the chip 5a Lipschitz bound.
  have h_inner_lt :=
    cover.innerRadius_lt_outerRadius x hx
  have h_gap_pos : 0 < cover.outerRadius x - cover.innerRadius x := by linarith
  let L : ℝ := M / (cover.outerRadius x - cover.innerRadius x)
  have hL_nonneg : 0 ≤ L := div_nonneg hM h_gap_pos.le
  have h_equicont : Equicontinuous
      ((↑) : Set.range g → ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x))
        → ℂ) := by
    intro u
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    refine ⟨ε / (L + 1), div_pos hε (by linarith), ?_⟩
    rintro v hv ⟨_, n, rfl⟩
    show dist (localCoeff (om_n n) x u.1) (localCoeff (om_n n) x v.1) < ε
    have h_lip := localCoeff_lipschitz_innerDisk_of_seminorm_le cover
      (om_n n) M (h_bound n) hx v.2 u.2
    have h_dist_eq : dist (localCoeff (om_n n) x u.1) (localCoeff (om_n n) x v.1)
        = ‖localCoeff (om_n n) x v.1 - localCoeff (om_n n) x u.1‖ := by
      rw [dist_eq_norm, ← norm_neg, neg_sub]
    rw [h_dist_eq]
    have hLp1 : 0 < L + 1 := by linarith
    have h_dist_subtype : ‖v.1 - u.1‖ = dist v u := by
      rw [Subtype.dist_eq, dist_eq_norm]
    calc ‖localCoeff (om_n n) x v.1 - localCoeff (om_n n) x u.1‖
        ≤ L * ‖v.1 - u.1‖ := h_lip
      _ = L * dist v u := by rw [h_dist_subtype]
      _ ≤ L * (ε / (L + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hL_nonneg
          exact le_of_lt hv
      _ < ε := by
          rw [mul_div_assoc']
          apply (div_lt_iff₀ hLp1).mpr
          have : L * ε < (L + 1) * ε := by
            apply mul_lt_mul_of_pos_right _ hε
            linarith
          linarith
  -- Apply Arzela.
  have h_compact :=
    BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) M)
      (isCompact_closedBall _ _) (Set.range g) h_values h_equicont
  have h_seq : ∀ n, g n ∈ closure (Set.range g) :=
    fun n => subset_closure (Set.mem_range_self n)
  obtain ⟨g_lim, _, φ, hφ_mono, h_tendsto⟩ :=
    h_compact.tendsto_subseq h_seq
  exact ⟨φ, g_lim, hφ_mono, h_tendsto⟩

end DiskChartCover

end JacobianChallenge

end
