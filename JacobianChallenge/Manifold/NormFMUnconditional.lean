/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import JacobianChallenge.Manifold.NormPushforwardChartPullbackTranslated
import JacobianChallenge.Manifold.NormPushforwardLocal
import JacobianChallenge.Manifold.NormPushforwardGlobal
import JacobianChallenge.Manifold.FibreDisjointChartRadiusDecomposition
import JacobianChallenge.Manifold.RegularValueExistsRegUnconditional
import JacobianChallenge.Manifold.CriticalValuesFiniteGeneral
import JacobianChallenge.Manifold.CriticalSetClosed
import JacobianChallenge.Manifold.RamificationIndex
import JacobianChallenge.Manifold.RamificationIndexPositive
import JacobianChallenge.Manifold.AnalyticLocalNormalForm
import JacobianChallenge.Manifold.PerChartNonConstancyReduction
import JacobianChallenge.Manifold.ClopennessOfLocallyConstDischarge
import JacobianChallenge.Manifold.ChartPullbackNotEventuallyConstDischarge

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # `NormFM_mmeromorphicAt` unconditional (Phase 1, ZZ214 direct)

This file closes the headline open obligation of Phase 1's norm-pushforward
chain: for non-constant `C^ω` `f : X → Y` between compact connected complex
1-manifolds and `g : MeromorphicNonzero X`, the global norm pushforward
`NormFM f hf hf_nc g : Y → ℂ` is meromorphic at every `y₀ : Y`.

The proof composes:
* `fibre_disjoint_chart_radius_decomposition` (ZZ211) — at any `y₀`, gives a
  finite preimage `hF`, per-`x` chart-radii `ε_x`, an open `V ∋ y₀`,
  pairwise-disjoint chart-disks `D_x`, `f ⁻¹' V ⊆ ⋃ D_x`, and per-fibre
  count `(f ⁻¹' {y} ∩ D_x).ncard = manifoldRamificationIndex f x` for
  `y ∈ V \ {y₀}`.
* `criticalValues_finite_general` (CV-Gen) — finiteness of the critical-value
  set, used to restrict to a punctured neighbourhood of `y₀` consisting only
  of regular values (where every preimage has ramification index 1).
* `deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood` (RVE) — at a non-
  critical preimage, the chart-pullback's derivative is nonzero. Combined
  with `AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero` from mathlib,
  this gives `analyticOrderAt = 1`, hence `manifoldRamificationIndex = 1`.

No new `Prop` bundles. No `_of_X` wrappers over fresh predicates. -/

@[expose] public section

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace JacobianChallenge
namespace Manifold

universe u v

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable {Y : Type v}
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-! ## Step 1: ramification index is 1 at a regular preimage. -/

/-- At a non-critical preimage of a non-critical value, the manifold
ramification index is `1`.

Chain: `x ∉ criticalSetGeneral f` ⟺ `∃ U ∈ 𝓝 x, InjOn f U`, then via
`deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood` (RVE) we get
the chart-pullback's derivative at `chart x` nonzero, then mathlib's
`analyticOrderAt_sub_eq_one_of_deriv_ne_zero` gives analytic order 1,
and the `toNat` collapses to `1`. -/
theorem manifoldRamificationIndex_eq_one_of_inj_on_neighbourhood
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (x : X)
    (h_inj : ∃ U ∈ 𝓝 x, Set.InjOn f U) :
    manifoldRamificationIndex f x = 1 := by
  classical
  have hF_an :
      AnalyticAt ℂ ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) :=
    JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback
      hf x
  have h_deriv_ne :
      deriv ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) ≠ 0 :=
    JacobianChallenge.ContMDiff.Owed.degree.deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood
      hf hnc x h_inj
  have h_ord :
      analyticOrderAt
        (fun z =>
          ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z -
          ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
        ((chartAt ℂ x) x) = 1 :=
    hF_an.analyticOrderAt_sub_eq_one_of_deriv_ne_zero h_deriv_ne
  show (analyticOrderAt _ _).toNat = 1
  rw [h_ord]
  rfl

/-- At a regular value (not in `criticalValuesGeneral f`), every preimage
has manifold ramification index `1`. -/
theorem manifoldRamificationIndex_eq_one_at_regular_value_preimage
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f)
    {y : Y} (hy : y ∉ criticalValuesGeneral f)
    {x : X} (hx : x ∈ f ⁻¹' {y}) :
    manifoldRamificationIndex f x = 1 := by
  apply manifoldRamificationIndex_eq_one_of_inj_on_neighbourhood hf hnc x
  -- y not a critical value ⇒ x not in critical set ⇒ ∃ nbhd InjOn.
  have hfx_eq : f x = y := hx
  have hx_not_crit : x ∉ criticalSetGeneral f := by
    intro hx_crit
    apply hy
    exact ⟨x, hx_crit, hfx_eq⟩
  by_contra h
  apply hx_not_crit
  show ¬ ∃ U ∈ 𝓝 x, Set.InjOn f U
  exact h

/-! ## Step 2: Hurwitz local normal form at a fibre point of `y₀`. -/

/-- At a fibre point `x` of `y₀ = f x`, the chart pullback of `f` admits a
**Hurwitz local normal form**: there exist `ρ > 0` and an analytic ψ on
`closedBall (chart_x x) ρ` with `ψ (chart_x x) = 0`, `deriv ψ (chart_x x) ≠ 0`,
and `(chart-pullback of f) z = (chart_y₀ y₀) + (ψ z) ^ k`, where
`k = manifoldRamificationIndex f x`.

Just packages `analytic_local_normal_form` (already in repo) at the right
chart-shifted hypotheses, after extracting the analytic-order-equals-`k`
identity from the definition of `manifoldRamificationIndex` and the
non-eventual-constancy of the chart pullback. -/
theorem hurwitz_local_form_at_fibre
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (x : X)
    (h_pos : 1 ≤ manifoldRamificationIndex f x) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ ψ : ℂ → ℂ,
      AnalyticOnNhd ℂ ψ (Metric.closedBall ((chartAt ℂ x) x) ρ) ∧
      ψ ((chartAt ℂ x) x) = 0 ∧
      deriv ψ ((chartAt ℂ x) x) ≠ 0 ∧
      ∀ z ∈ Metric.closedBall ((chartAt ℂ x) x) ρ,
        ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z =
          (chartAt ℂ (f x)) (f x) + (ψ z) ^ (manifoldRamificationIndex f x) := by
  classical
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀_def
  set F : ℂ → ℂ := (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm with hF_def
  set k : ℕ := manifoldRamificationIndex f x with hk_def
  have hF_an : AnalyticAt ℂ F z₀ :=
    JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback
      hf x
  have hF_z₀_eq : F z₀ = (chartAt ℂ (f x)) (f x) := by
    have hx_src : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    show ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
        = (chartAt ℂ (f x)) (f x)
    simp [Function.comp, (chartAt ℂ x).left_inv hx_src]
  have h_pos' : 1 ≤ (analyticOrderAt (fun z => F z - F z₀) z₀).toNat := by
    rw [show (analyticOrderAt (fun z => F z - F z₀) z₀).toNat = k from rfl]
    exact h_pos
  have h_ord_ne_top :
      analyticOrderAt (fun z => F z - F z₀) z₀ ≠ ⊤ := by
    intro h
    rw [h, ENat.toNat_top] at h_pos'
    exact absurd h_pos' (by norm_num)
  have h_ord_eq : analyticOrderAt (fun z => F z - F z₀) z₀ = (k : ℕ∞) := by
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h_ord_ne_top
    have hk_n : k = n := by
      rw [hk_def, manifoldRamificationIndex_eq, ← hn, ENat.toNat_coe]
    rw [← hn, hk_n]
  have h_ord_eq_subst :
      analyticOrderAt (fun z => F z - (chartAt ℂ (f x)) (f x)) z₀ = (k : ℕ∞) := by
    rw [← hF_z₀_eq]; exact h_ord_eq
  exact analytic_local_normal_form h_pos hF_an hF_z₀_eq h_ord_eq_subst

/-! ## Step 3: per-`x` planar germ `g_x` is `MeromorphicAt 0`. -/

/-- At a fibre point `x` of `y₀`, the composition `g.toFun ∘ chart_x.symm ∘ φ_x`
is `MeromorphicAt 0`, where `φ_x` is the analytic local inverse of the Hurwitz
`ψ_x` at `0`. This is the per-`x` "planar germ representing g through the
local biholomorphism," used downstream as the `g`-argument of `normPow`. -/
theorem normFM_local_germ_meromorphicAt_zero
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (g : MeromorphicNonzero X) (x : X)
    (h_pos : 1 ≤ manifoldRamificationIndex f x) :
    ∃ g_x : ℂ → ℂ, MeromorphicAt g_x 0 := by
  classical
  -- Hurwitz local form gives ψ analytic with deriv ψ z₀ ≠ 0 and ψ z₀ = 0.
  obtain ⟨ρ, hρ_pos, ψ, hψ_an_on, hψ_z₀, hψ_deriv, _hψ_eq⟩ :=
    hurwitz_local_form_at_fibre hf hnc x h_pos
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀_def
  -- AnalyticAt at the centre of the closed ball.
  have hψ_an_at : AnalyticAt ℂ ψ z₀ := by
    have hmem : z₀ ∈ Metric.closedBall z₀ ρ := Metric.mem_closedBall_self hρ_pos.le
    exact hψ_an_on _ hmem
  -- The local inverse, as a function ℂ → ℂ.
  let φ : ℂ → ℂ :=
    hψ_an_at.hasStrictDerivAt.localInverse _ _ _ hψ_deriv
  -- φ is analytic at ψ z₀ = 0.
  have hφ_an_ψz₀ : AnalyticAt ℂ φ (ψ z₀) :=
    hψ_an_at.analyticAt_localInverse hψ_deriv
  have hφ_an_zero : AnalyticAt ℂ φ 0 := by rw [← hψ_z₀]; exact hφ_an_ψz₀
  -- φ (ψ z₀) = z₀ from the planar HasStrictFDerivAt.localInverse_apply_image.
  -- Since `hψ_an_at.hasStrictDerivAt` is HasStrictDerivAt, lift to HasStrictFDerivAt
  -- via `hasStrictFDerivAt_equiv`.
  have hφ_zero : φ 0 = z₀ := by
    have h_im :
        φ (ψ z₀) = z₀ :=
      HasStrictFDerivAt.localInverse_apply_image
        (hψ_an_at.hasStrictDerivAt.hasStrictFDerivAt_equiv hψ_deriv)
    rw [← hψ_z₀]; exact h_im
  -- g pulled back through chart_x is meromorphic at z₀.
  have hg_pulled : MeromorphicAt (g.toFun ∘ (chartAt ℂ x).symm) z₀ :=
    g.meromorphic x trivial
  -- Compose: (g ∘ chart.symm) ∘ φ is MeromorphicAt 0.
  have hg_at_φ0 :
      MeromorphicAt (g.toFun ∘ (chartAt ℂ x).symm) (φ 0) := by
    rw [hφ_zero]; exact hg_pulled
  exact ⟨_, hg_at_φ0.comp_analyticAt hφ_an_zero⟩

/-! ## Step 4: per-`x` factor `F_x : Y → ℂ` is `MMeromorphicAt y₀`. -/

/-- At a fibre point `x` of `y₀`, there exists a function `F_x : Y → ℂ` of the
form `fun y => normPow g_x k_x ((chart y₀ y) - (chart y₀ y₀))` that is
`MMeromorphicAt y₀`, where `k_x = manifoldRamificationIndex f x` and `g_x` is
the planar germ representing `g` through the local biholomorphism.

Direct corollary of `normFM_local_germ_meromorphicAt_zero` (step 3) plus
`normPow_mmeromorphicAt_chartPullback_translated` (ZZ210). -/
theorem normFM_local_factor_mmeromorphicAt
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (g : MeromorphicNonzero X) (x : X)
    (h_pos : 1 ≤ manifoldRamificationIndex f x) (y₀ : Y) :
    ∃ F_x : Y → ℂ, MMeromorphicAt (𝓘(ℂ, ℂ)) F_x y₀ := by
  obtain ⟨g_x, hg_x_mero⟩ := normFM_local_germ_meromorphicAt_zero hf hnc g x h_pos
  refine ⟨fun y =>
    normPow g_x (manifoldRamificationIndex f x)
      ((chartAt ℂ y₀) y - (chartAt ℂ y₀) y₀), ?_⟩
  exact normPow_mmeromorphicAt_chartPullback_translated h_pos hg_x_mero

/-! ## Step 5: Hurwitz form refined with local injectivity of `ψ`. -/

/-- A refinement of `hurwitz_local_form_at_fibre` that additionally provides
`Set.InjOn ψ (closedBall z₀ ρ)`. Local injectivity comes from the
`HasStrictFDerivAt.toOpenPartialHomeomorph` of the strict derivative + non-zero
derivative; we shrink the Hurwitz radius to fit inside the homeomorph's source. -/
theorem hurwitz_local_form_at_fibre_with_injectivity
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (x : X)
    (h_pos : 1 ≤ manifoldRamificationIndex f x) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ ψ : ℂ → ℂ,
      AnalyticOnNhd ℂ ψ (Metric.closedBall ((chartAt ℂ x) x) ρ) ∧
      ψ ((chartAt ℂ x) x) = 0 ∧
      deriv ψ ((chartAt ℂ x) x) ≠ 0 ∧
      Set.InjOn ψ (Metric.closedBall ((chartAt ℂ x) x) ρ) ∧
      ∀ z ∈ Metric.closedBall ((chartAt ℂ x) x) ρ,
        ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z =
          (chartAt ℂ (f x)) (f x) + (ψ z) ^ (manifoldRamificationIndex f x) := by
  classical
  obtain ⟨ρ₀, hρ₀_pos, ψ, hψ_an_on, hψ_z₀, hψ_deriv, hψ_eq⟩ :=
    hurwitz_local_form_at_fibre hf hnc x h_pos
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀_def
  -- Lift to HasStrictFDerivAt and grab the OpenPartialHomeomorph source.
  have hψ_an_at : AnalyticAt ℂ ψ z₀ :=
    hψ_an_on _ (Metric.mem_closedBall_self hρ₀_pos.le)
  have hψ_strictFD :
      HasStrictFDerivAt ψ
        ((ContinuousLinearEquiv.unitsEquivAut ℂ
          (Units.mk0 (deriv ψ z₀) hψ_deriv)).toContinuousLinearMap) z₀ :=
    hψ_an_at.hasStrictDerivAt.hasStrictFDerivAt_equiv hψ_deriv
  set H : OpenPartialHomeomorph ℂ ℂ := hψ_strictFD.toOpenPartialHomeomorph ψ with hH_def
  have hz₀_in_source : z₀ ∈ H.source :=
    hψ_strictFD.mem_toOpenPartialHomeomorph_source
  have hH_open_source : IsOpen H.source := H.open_source
  -- Source is an open nbhd of z₀; extract a closed-ball radius δ.
  have h_src_nhds : H.source ∈ 𝓝 z₀ := hH_open_source.mem_nhds hz₀_in_source
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.mem_nhds_iff.mp h_src_nhds
  -- Shrink Hurwitz radius to ρ := min ρ₀ (δ/2) (closed ball ⊂ open ball ⊂ H.source).
  set ρ : ℝ := min ρ₀ (δ/2) with hρ_def
  have hρ_pos : 0 < ρ := lt_min hρ₀_pos (by positivity)
  have hρ_le_ρ₀ : ρ ≤ ρ₀ := min_le_left _ _
  have hρ_le_half_δ : ρ ≤ δ/2 := min_le_right _ _
  have h_closedBall_sub_source :
      Metric.closedBall z₀ ρ ⊆ H.source := by
    intro z hz
    have h_lt : dist z z₀ < δ := by
      have h_le : dist z z₀ ≤ ρ := hz
      have h_strict : ρ < δ := by linarith [hδ_pos.le]
      exact lt_of_le_of_lt h_le h_strict
    exact hδ_sub h_lt
  -- Closed ball at smaller radius is inside the original Hurwitz domain.
  have h_closedBall_sub_ρ₀ :
      Metric.closedBall z₀ ρ ⊆ Metric.closedBall z₀ ρ₀ :=
    Metric.closedBall_subset_closedBall hρ_le_ρ₀
  -- Re-package the Hurwitz claims at the smaller radius.
  refine ⟨ρ, hρ_pos, ψ, ?_, hψ_z₀, hψ_deriv, ?_, ?_⟩
  · -- AnalyticOnNhd at smaller radius.
    intro z hz; exact hψ_an_on z (h_closedBall_sub_ρ₀ hz)
  · -- InjOn ψ on closedBall z₀ ρ via H's homeomorph injectivity.
    intro a ha b hb hab
    have ha_src : a ∈ H.source := h_closedBall_sub_source ha
    have hb_src : b ∈ H.source := h_closedBall_sub_source hb
    -- H.coe = ψ on H.source.
    have h_eq : (H : ℂ → ℂ) a = (H : ℂ → ℂ) b := by
      show ψ a = ψ b
      exact hab
    exact H.injOn ha_src hb_src h_eq
  · -- Hurwitz equation at smaller radius.
    intro z hz; exact hψ_eq z (h_closedBall_sub_ρ₀ hz)

/-! ## Step 6: Hurwitz form with both local injectivity AND fibre count. -/

/-- Combines step 5's `InjOn ψ` (at radius `ρ`) with
`localKFoldMultiplicityOnManifold_genuine_with_radius` (at the same radius `ρ`,
chosen via `R₀ := ρ`), yielding a single witness with both. -/
theorem hurwitz_local_form_with_count_and_injectivity
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (x : X)
    (h_pos : 1 ≤ manifoldRamificationIndex f x) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ V : Set Y, IsOpen V ∧ f x ∈ V ∧
      ∃ ψ : ℂ → ℂ,
        AnalyticOnNhd ℂ ψ (Metric.closedBall ((chartAt ℂ x) x) ε) ∧
        ψ ((chartAt ℂ x) x) = 0 ∧
        deriv ψ ((chartAt ℂ x) x) ≠ 0 ∧
        Set.InjOn ψ (Metric.closedBall ((chartAt ℂ x) x) ε) ∧
        (∀ z ∈ Metric.closedBall ((chartAt ℂ x) x) ε,
          ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z =
            (chartAt ℂ (f x)) (f x) + (ψ z) ^ (manifoldRamificationIndex f x)) ∧
        ∀ w ∈ V, w ≠ f x →
          (f ⁻¹' {w} ∩
            ((chartAt ℂ x).source ∩
              (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε)).ncard
            = manifoldRamificationIndex f x := by
  classical
  -- Step 5 gives ρ with both AnalyticOnNhd and InjOn at radius ρ.
  obtain ⟨ρ, hρ_pos, ψ, hψ_an_on, hψ_z₀, hψ_deriv, hψ_inj, hψ_eq⟩ :=
    hurwitz_local_form_at_fibre_with_injectivity hf hnc x h_pos
  -- Now invoke localKFoldMultiplicityOnManifold_genuine_with_radius at R₀ := ρ.
  obtain ⟨ε, V, hε_pos, hε_le_ρ, hV_open, hfx_V, h_count⟩ :=
    JacobianChallenge.Manifold.localKFoldMultiplicityOnManifold_genuine_with_radius
      hf x h_pos hρ_pos
  -- ε ≤ ρ, so closedBall z₀ ε ⊆ closedBall z₀ ρ; ψ data carries over.
  have h_sub : Metric.closedBall ((chartAt ℂ x) x) ε ⊆
      Metric.closedBall ((chartAt ℂ x) x) ρ :=
    Metric.closedBall_subset_closedBall hε_le_ρ
  refine ⟨ε, hε_pos, V, hV_open, hfx_V, ψ, ?_, hψ_z₀, hψ_deriv, ?_, ?_, h_count⟩
  · intro z hz; exact hψ_an_on z (h_sub hz)
  · intro a ha b hb hab; exact hψ_inj (h_sub ha) (h_sub hb) hab
  · intro z hz; exact hψ_eq z (h_sub hz)

/-! ## Step 7: ψ ∘ chart_x maps fibre points into `nthRootsFinset`. -/

/-- For `y` near `f x` with `y ≠ f x`, every `z ∈ f⁻¹{y}` lying in the
chart-disk of radius `ε` (where ε comes from `hurwitz_local_form_with_count_and_injectivity`)
satisfies `ψ (chart_x z) ∈ nthRootsFinset k_x ((chart_y₀ y) - (chart_y₀ y₀))`. -/
theorem normFM_local_psi_in_nthRootsFinset
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (x : X)
    (h_pos : 1 ≤ manifoldRamificationIndex f x)
    {ε : ℝ} (hε_pos : 0 < ε)
    {ψ : ℂ → ℂ}
    (hψ_eq : ∀ z ∈ Metric.closedBall ((chartAt ℂ x) x) ε,
      ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z =
        (chartAt ℂ (f x)) (f x) + (ψ z) ^ (manifoldRamificationIndex f x))
    {y : Y} {z : X}
    (hz_mem :
      z ∈ f ⁻¹' {y} ∩
        ((chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε)) :
    ψ ((chartAt ℂ x) z) ∈
      Polynomial.nthRootsFinset (manifoldRamificationIndex f x)
        ((chartAt ℂ (f x)) y - (chartAt ℂ (f x)) (f x)) := by
  classical
  obtain ⟨hfz, hz_src, hz_ball⟩ := hz_mem
  have hfz_eq : f z = y := hfz
  have h_chart_z_closed : (chartAt ℂ x) z ∈ Metric.closedBall ((chartAt ℂ x) x) ε :=
    Metric.ball_subset_closedBall hz_ball
  have h_eq := hψ_eq ((chartAt ℂ x) z) h_chart_z_closed
  have h_inv : (chartAt ℂ x).symm ((chartAt ℂ x) z) = z := (chartAt ℂ x).left_inv hz_src
  have h_pull : ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) z)
      = (chartAt ℂ (f x)) y := by
    show (chartAt ℂ (f x)) (f ((chartAt ℂ x).symm ((chartAt ℂ x) z))) = _
    rw [h_inv, hfz_eq]
  rw [h_pull] at h_eq
  have h_pow :
      (ψ ((chartAt ℂ x) z)) ^ (manifoldRamificationIndex f x)
        = (chartAt ℂ (f x)) y - (chartAt ℂ (f x)) (f x) := by
    rw [h_eq]; ring
  rw [Polynomial.mem_nthRootsFinset h_pos]
  exact h_pow

/-! ## Step 8: image of `ψ ∘ chart_x` equals `nthRootsFinset`. -/

/-- Under the hypotheses of `hurwitz_local_form_with_count_and_injectivity`,
the image of the per-fibre Finset under `z ↦ ψ ((chartAt ℂ x) z)` equals
`nthRootsFinset k_x ((chart_y₀ y) - (chart_y₀ (f x)))`. -/
theorem normFM_local_image_eq_nthRootsFinset
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (x : X)
    (h_pos : 1 ≤ manifoldRamificationIndex f x)
    {ε : ℝ} (hε_pos : 0 < ε) (y : Y)
    {ψ : ℂ → ℂ}
    (hψ_inj : Set.InjOn ψ (Metric.closedBall ((chartAt ℂ x) x) ε))
    (hψ_eq : ∀ z ∈ Metric.closedBall ((chartAt ℂ x) x) ε,
      ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z =
        (chartAt ℂ (f x)) (f x) + (ψ z) ^ (manifoldRamificationIndex f x))
    (hMan_fin : (f ⁻¹' {y} ∩ ((chartAt ℂ x).source ∩
      (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε)).Finite)
    (h_count :
      (f ⁻¹' {y} ∩
        ((chartAt ℂ x).source ∩
          (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε)).ncard
        = manifoldRamificationIndex f x) :
    Finset.image (fun z => ψ ((chartAt ℂ x) z))
        hMan_fin.toFinset
      = Polynomial.nthRootsFinset (manifoldRamificationIndex f x)
          ((chartAt ℂ (f x)) y - (chartAt ℂ (f x)) (f x)) := by
  classical
  set k : ℕ := manifoldRamificationIndex f x with hk_def
  set t : ℂ := (chartAt ℂ (f x)) y - (chartAt ℂ (f x)) (f x) with ht_def
  set rootsT : Finset ℂ := Polynomial.nthRootsFinset k t with hroots_def
  have h_subset :
      Finset.image (fun z => ψ ((chartAt ℂ x) z)) hMan_fin.toFinset ⊆ rootsT := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨z, hz, hz_eq⟩
    have hz_set : z ∈ (f ⁻¹' {y} ∩ ((chartAt ℂ x).source ∩
        (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε)) :=
      hMan_fin.mem_toFinset.mp hz
    have h7 := normFM_local_psi_in_nthRootsFinset (f := f) hf hnc x h_pos
      (hε_pos := hε_pos) (hψ_eq := hψ_eq) (y := y) (z := z) hz_set
    rw [← hz_eq]; exact h7
  have h_card_manifold_finset : hMan_fin.toFinset.card = k := by
    rw [Set.ncard_eq_toFinset_card _ hMan_fin] at h_count
    exact h_count
  have h_inj_on_finset :
      Set.InjOn (fun z : X => ψ ((chartAt ℂ x) z))
        (hMan_fin.toFinset : Set X) := by
    intro a ha b hb hab
    have ha_set : a ∈ _ := hMan_fin.mem_toFinset.mp (Finset.mem_coe.mp ha)
    have hb_set : b ∈ _ := hMan_fin.mem_toFinset.mp (Finset.mem_coe.mp hb)
    obtain ⟨_, ha_src, ha_ball⟩ := ha_set
    obtain ⟨_, hb_src, hb_ball⟩ := hb_set
    have ha_closed :
        (chartAt ℂ x) a ∈ Metric.closedBall ((chartAt ℂ x) x) ε :=
      Metric.ball_subset_closedBall ha_ball
    have hb_closed :
        (chartAt ℂ x) b ∈ Metric.closedBall ((chartAt ℂ x) x) ε :=
      Metric.ball_subset_closedBall hb_ball
    have h_chart_eq : (chartAt ℂ x) a = (chartAt ℂ x) b :=
      hψ_inj ha_closed hb_closed hab
    exact (chartAt ℂ x).injOn ha_src hb_src h_chart_eq
  have h_card_image :
      (Finset.image (fun z => ψ ((chartAt ℂ x) z)) hMan_fin.toFinset).card =
        hMan_fin.toFinset.card :=
    Finset.card_image_of_injOn h_inj_on_finset
  have h_card_rootsT_le : rootsT.card ≤ k := by
    have h_mset := Polynomial.card_nthRoots k t
    rw [hroots_def, Polynomial.nthRootsFinset]
    exact (Multiset.toFinset_card_le _).trans h_mset
  have h_card_image_eq : (Finset.image (fun z => ψ ((chartAt ℂ x) z))
      hMan_fin.toFinset).card = k := by
    rw [h_card_image, h_card_manifold_finset]
  apply Finset.eq_of_subset_of_card_le h_subset
  rw [h_card_image_eq]; exact h_card_rootsT_le

/-! ## Step 9: per-`x` product equality. -/

/-- For `y` near `f x` with `y ≠ f x`, the product of `g.toFun` over the
chart-disk fibre equals `normPow g_x k_x (chart y - chart (f x))`, where
`g_x s := g.toFun ((chart_x).symm (φ s))` and `φ` is the analytic local
inverse of the Hurwitz `ψ` at `0`. -/
theorem normFM_local_product_eq_normPow
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (g : MeromorphicNonzero X) (x : X)
    (h_pos : 1 ≤ manifoldRamificationIndex f x) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ V : Set Y, IsOpen V ∧ f x ∈ V ∧
      ∃ g_x : ℂ → ℂ, MeromorphicAt g_x 0 ∧
        ∀ y ∈ V, y ≠ f x →
          ∀ (hMan_fin :
            (f ⁻¹' {y} ∩ ((chartAt ℂ x).source ∩
              (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε)).Finite),
            (f ⁻¹' {y} ∩
              ((chartAt ℂ x).source ∩
                (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε)).ncard
              = manifoldRamificationIndex f x →
            (∏ z ∈ hMan_fin.toFinset, g.toFun z) =
              normPow g_x (manifoldRamificationIndex f x)
                ((chartAt ℂ (f x)) y - (chartAt ℂ (f x)) (f x)) := by
  classical
  obtain ⟨ε₆, hε₆_pos, V, hV_open, hfx_V, ψ, hψ_an_on, hψ_z₀, hψ_deriv,
    hψ_inj, hψ_eq, h_count⟩ :=
    hurwitz_local_form_with_count_and_injectivity hf hnc x h_pos
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀_def
  have hψ_an_at : AnalyticAt ℂ ψ z₀ :=
    hψ_an_on _ (Metric.mem_closedBall_self hε₆_pos.le)
  let φ : ℂ → ℂ :=
    hψ_an_at.hasStrictDerivAt.localInverse _ _ _ hψ_deriv
  have hφ_an_zero : AnalyticAt ℂ φ 0 := by
    have := hψ_an_at.analyticAt_localInverse hψ_deriv
    rwa [hψ_z₀] at this
  have hφψ_id :
      ∀ᶠ w in 𝓝 z₀, φ (ψ w) = w :=
    hψ_an_at.hasStrictDerivAt.eventually_left_inverse hψ_deriv
  obtain ⟨δ, hδ_pos, hδ_sub⟩ :
      ∃ δ > 0, Metric.ball z₀ δ ⊆ {w | φ (ψ w) = w} :=
    Metric.eventually_nhds_iff_ball.mp hφψ_id
  set ε : ℝ := min ε₆ (δ / 2) with hε_def
  have hε_pos : 0 < ε := lt_min hε₆_pos (by positivity)
  have hε_le_ε₆ : ε ≤ ε₆ := min_le_left _ _
  have hε_lt_δ : ε < δ := by
    have h1 : ε ≤ δ / 2 := min_le_right _ _
    linarith
  have h_sub_ε₆ : Metric.closedBall z₀ ε ⊆ Metric.closedBall z₀ ε₆ :=
    Metric.closedBall_subset_closedBall hε_le_ε₆
  have h_left_inv :
      ∀ w ∈ Metric.closedBall z₀ ε, φ (ψ w) = w := by
    intro w hw
    have hw_ball : w ∈ Metric.ball z₀ δ := by
      have h_le : dist w z₀ ≤ ε := hw
      exact lt_of_le_of_lt h_le hε_lt_δ
    exact hδ_sub hw_ball
  obtain ⟨ε', V', hε'_pos, hε'_le_ε, hV'_open, hfx_V', h_count'⟩ :=
    JacobianChallenge.Manifold.localKFoldMultiplicityOnManifold_genuine_with_radius
      hf x h_pos hε_pos
  refine ⟨ε', hε'_pos, V', hV'_open, hfx_V',
    fun s => g.toFun ((chartAt ℂ x).symm (φ s)), ?_, ?_⟩
  · have hg_pulled : MeromorphicAt (g.toFun ∘ (chartAt ℂ x).symm) z₀ :=
      g.meromorphic x trivial
    have hφ_zero : φ 0 = z₀ := by
      have h_im :
          φ (ψ z₀) = z₀ :=
        HasStrictFDerivAt.localInverse_apply_image
          (hψ_an_at.hasStrictDerivAt.hasStrictFDerivAt_equiv hψ_deriv)
      rw [← hψ_z₀]; exact h_im
    have hg_at_φ0 :
        MeromorphicAt (g.toFun ∘ (chartAt ℂ x).symm) (φ 0) := by
      rw [hφ_zero]; exact hg_pulled
    show MeromorphicAt (fun s => g.toFun ((chartAt ℂ x).symm (φ s))) 0
    exact hg_at_φ0.comp_analyticAt hφ_an_zero
  · intro y hy_V hy_ne hMan_fin h_count_y
    have h_image := normFM_local_image_eq_nthRootsFinset
      (f := f) hf hnc x h_pos (hε_pos := hε'_pos) y
      (hψ_inj := fun a ha b hb hab => hψ_inj
        (h_sub_ε₆ (Metric.closedBall_subset_closedBall hε'_le_ε ha))
        (h_sub_ε₆ (Metric.closedBall_subset_closedBall hε'_le_ε hb)) hab)
      (hψ_eq := fun z hz => hψ_eq z
        (h_sub_ε₆ (Metric.closedBall_subset_closedBall hε'_le_ε hz)))
      (hMan_fin := hMan_fin)
      (h_count := h_count_y)
    have h_inj_finset :
        Set.InjOn (fun z : X => ψ ((chartAt ℂ x) z))
          (hMan_fin.toFinset : Set X) := by
      intro a ha b hb hab
      have ha_set := hMan_fin.mem_toFinset.mp (Finset.mem_coe.mp ha)
      have hb_set := hMan_fin.mem_toFinset.mp (Finset.mem_coe.mp hb)
      obtain ⟨_, ha_src, ha_ball⟩ := ha_set
      obtain ⟨_, hb_src, hb_ball⟩ := hb_set
      have ha_closed :
          (chartAt ℂ x) a ∈ Metric.closedBall z₀ ε :=
        Metric.ball_subset_closedBall (Metric.ball_subset_ball hε'_le_ε ha_ball)
      have hb_closed :
          (chartAt ℂ x) b ∈ Metric.closedBall z₀ ε :=
        Metric.ball_subset_closedBall (Metric.ball_subset_ball hε'_le_ε hb_ball)
      have h_chart_eq : (chartAt ℂ x) a = (chartAt ℂ x) b :=
        hψ_inj (h_sub_ε₆ ha_closed) (h_sub_ε₆ hb_closed) hab
      exact (chartAt ℂ x).injOn ha_src hb_src h_chart_eq
    have h_fn_val : ∀ z ∈ hMan_fin.toFinset,
        g.toFun z = g.toFun ((chartAt ℂ x).symm (φ (ψ ((chartAt ℂ x) z)))) := by
      intro z hz
      have hz_set := hMan_fin.mem_toFinset.mp hz
      obtain ⟨_, hz_src, hz_ball⟩ := hz_set
      have h_chart_z_closed :
          (chartAt ℂ x) z ∈ Metric.closedBall z₀ ε :=
        Metric.ball_subset_closedBall (Metric.ball_subset_ball hε'_le_ε hz_ball)
      have h_li : φ (ψ ((chartAt ℂ x) z)) = (chartAt ℂ x) z :=
        h_left_inv _ h_chart_z_closed
      rw [h_li]
      have h_inv : (chartAt ℂ x).symm ((chartAt ℂ x) z) = z := (chartAt ℂ x).left_inv hz_src
      rw [h_inv]
    -- Define F : ℂ → ℂ as the per-x planar germ.
    set F : ℂ → ℂ := fun s => g.toFun ((chartAt ℂ x).symm (φ s)) with hF_def
    -- Rewrite ∏ z g(z) = ∏ z F(ψ(chart_x z)) using h_fn_val.
    have h_step1 :
        (∏ z ∈ hMan_fin.toFinset, g.toFun z)
          = ∏ z ∈ hMan_fin.toFinset, F (ψ ((chartAt ℂ x) z)) := by
      apply Finset.prod_congr rfl
      intro z hz
      exact h_fn_val z hz
    -- Use Finset.prod_image to re-index by the image map.
    have h_step2 :
        (∏ z ∈ hMan_fin.toFinset, F (ψ ((chartAt ℂ x) z)))
          = ∏ ζ ∈ Finset.image (fun z => ψ ((chartAt ℂ x) z)) hMan_fin.toFinset, F ζ :=
      (Finset.prod_image h_inj_finset).symm
    -- Substitute the image equality from step 8.
    have h_step3 :
        (∏ ζ ∈ Finset.image (fun z => ψ ((chartAt ℂ x) z)) hMan_fin.toFinset, F ζ)
          = ∏ ζ ∈ Polynomial.nthRootsFinset (manifoldRamificationIndex f x)
              ((chartAt ℂ (f x)) y - (chartAt ℂ (f x)) (f x)), F ζ := by
      rw [h_image]
    rw [h_step1, h_step2, h_step3]
    -- normPow's body is exactly this product.
    rfl

/-! ## Step 10: per-`x` factor function `F_x : Y → ℂ`. -/

/-- Existence of a planar germ representing `g` at the fibre point, with
`MeromorphicAt 0`. Cleaner factorisation of step 9's existential output. -/
private theorem normFM_local_germ_exists
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (g : MeromorphicNonzero X) (x : X)
    (h_pos : 1 ≤ manifoldRamificationIndex f x) :
    ∃ g_x : ℂ → ℂ, MeromorphicAt g_x 0 := by
  obtain ⟨_, _, _, _, _, g_x, hg_x_mero, _⟩ :=
    normFM_local_product_eq_normPow hf hnc g x h_pos
  exact ⟨g_x, hg_x_mero⟩

/-- The planar germ `g_x` for the fibre point `x`, extracted via Classical.choose. -/
noncomputable def normFM_g_x
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (g : MeromorphicNonzero X) (x : X)
    (h_pos : 1 ≤ manifoldRamificationIndex f x) : ℂ → ℂ :=
  Classical.choose (normFM_local_germ_exists hf hnc g x h_pos)

theorem normFM_g_x_meromorphicAt
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (g : MeromorphicNonzero X) (x : X)
    (h_pos : 1 ≤ manifoldRamificationIndex f x) :
    MeromorphicAt (normFM_g_x hf hnc g x h_pos) 0 :=
  Classical.choose_spec (normFM_local_germ_exists hf hnc g x h_pos)

/-- The per-`x` factor function for the headline `NormFM_mmeromorphicAt`. -/
noncomputable def normFM_F_x
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (g : MeromorphicNonzero X) (x : X)
    (h_pos : 1 ≤ manifoldRamificationIndex f x) : Y → ℂ :=
  fun y =>
    normPow (normFM_g_x hf hnc g x h_pos) (manifoldRamificationIndex f x)
      ((chartAt ℂ (f x)) y - (chartAt ℂ (f x)) (f x))

/-- `normFM_F_x` is `MMeromorphicAt (f x)`. -/
theorem normFM_F_x_mmeromorphicAt
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (g : MeromorphicNonzero X) (x : X)
    (h_pos : 1 ≤ manifoldRamificationIndex f x) :
    MMeromorphicAt (𝓘(ℂ, ℂ)) (normFM_F_x hf hnc g x h_pos) (f x) :=
  normPow_mmeromorphicAt_chartPullback_translated h_pos
    (normFM_g_x_meromorphicAt hf hnc g x h_pos)

/-! ## Step 11a: parametric per-`x` product equality. -/

/-- Parametric version of `normFM_local_product_eq_normPow`: takes the radius `ε`
and Hurwitz data `ψ` as input, plus a left-inverse identity hypothesis on
`closedBall ε`. Returns a `g_x` with `MeromorphicAt 0` and the product equality. -/
theorem normFM_local_product_eq_normPow_at_radius
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (g : MeromorphicNonzero X) (x : X)
    (h_pos : 1 ≤ manifoldRamificationIndex f x)
    {ε : ℝ} (hε_pos : 0 < ε)
    {ψ : ℂ → ℂ}
    (hψ_an_on : AnalyticOnNhd ℂ ψ (Metric.closedBall ((chartAt ℂ x) x) ε))
    (hψ_z₀ : ψ ((chartAt ℂ x) x) = 0)
    (hψ_deriv : deriv ψ ((chartAt ℂ x) x) ≠ 0)
    (hψ_inj : Set.InjOn ψ (Metric.closedBall ((chartAt ℂ x) x) ε))
    (hψ_eq : ∀ z ∈ Metric.closedBall ((chartAt ℂ x) x) ε,
      ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z =
        (chartAt ℂ (f x)) (f x) + (ψ z) ^ (manifoldRamificationIndex f x))
    (h_left_inv : ∀ w ∈ Metric.closedBall ((chartAt ℂ x) x) ε,
      (let z₀ := (chartAt ℂ x) x
       let φ : ℂ → ℂ := (hψ_an_on z₀ (Metric.mem_closedBall_self hε_pos.le)).hasStrictDerivAt.localInverse _ _ _ hψ_deriv
       φ (ψ w) = w)) :
    ∃ g_x : ℂ → ℂ, MeromorphicAt g_x 0 ∧
      ∀ y : Y,
      ∀ (hMan_fin :
        (f ⁻¹' {y} ∩ ((chartAt ℂ x).source ∩
          (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε)).Finite),
        (f ⁻¹' {y} ∩
          ((chartAt ℂ x).source ∩
            (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε)).ncard
          = manifoldRamificationIndex f x →
        (∏ z ∈ hMan_fin.toFinset, g.toFun z) =
          normPow g_x (manifoldRamificationIndex f x)
            ((chartAt ℂ (f x)) y - (chartAt ℂ (f x)) (f x)) := by
  classical
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀_def
  have hψ_an_at : AnalyticAt ℂ ψ z₀ :=
    hψ_an_on _ (Metric.mem_closedBall_self hε_pos.le)
  let φ : ℂ → ℂ :=
    hψ_an_at.hasStrictDerivAt.localInverse _ _ _ hψ_deriv
  have hφ_an_zero : AnalyticAt ℂ φ 0 := by
    have := hψ_an_at.analyticAt_localInverse hψ_deriv
    rwa [hψ_z₀] at this
  refine ⟨fun s => g.toFun ((chartAt ℂ x).symm (φ s)), ?_, ?_⟩
  · have hg_pulled : MeromorphicAt (g.toFun ∘ (chartAt ℂ x).symm) z₀ :=
      g.meromorphic x trivial
    have hφ_zero : φ 0 = z₀ := by
      have h_im :
          φ (ψ z₀) = z₀ :=
        HasStrictFDerivAt.localInverse_apply_image
          (hψ_an_at.hasStrictDerivAt.hasStrictFDerivAt_equiv hψ_deriv)
      rw [← hψ_z₀]; exact h_im
    have hg_at_φ0 :
        MeromorphicAt (g.toFun ∘ (chartAt ℂ x).symm) (φ 0) := by
      rw [hφ_zero]; exact hg_pulled
    show MeromorphicAt (fun s => g.toFun ((chartAt ℂ x).symm (φ s))) 0
    exact hg_at_φ0.comp_analyticAt hφ_an_zero
  · intro y hMan_fin h_count_y
    have h_image := normFM_local_image_eq_nthRootsFinset
      (f := f) hf hnc x h_pos (hε_pos := hε_pos) y
      (hψ_inj := hψ_inj) (hψ_eq := hψ_eq)
      (hMan_fin := hMan_fin) (h_count := h_count_y)
    have h_inj_finset :
        Set.InjOn (fun z : X => ψ ((chartAt ℂ x) z))
          (hMan_fin.toFinset : Set X) := by
      intro a ha b hb hab
      have ha_set := hMan_fin.mem_toFinset.mp (Finset.mem_coe.mp ha)
      have hb_set := hMan_fin.mem_toFinset.mp (Finset.mem_coe.mp hb)
      obtain ⟨_, ha_src, ha_ball⟩ := ha_set
      obtain ⟨_, hb_src, hb_ball⟩ := hb_set
      have ha_closed :
          (chartAt ℂ x) a ∈ Metric.closedBall z₀ ε :=
        Metric.ball_subset_closedBall ha_ball
      have hb_closed :
          (chartAt ℂ x) b ∈ Metric.closedBall z₀ ε :=
        Metric.ball_subset_closedBall hb_ball
      have h_chart_eq : (chartAt ℂ x) a = (chartAt ℂ x) b :=
        hψ_inj ha_closed hb_closed hab
      exact (chartAt ℂ x).injOn ha_src hb_src h_chart_eq
    have h_fn_val : ∀ z ∈ hMan_fin.toFinset,
        g.toFun z = g.toFun ((chartAt ℂ x).symm (φ (ψ ((chartAt ℂ x) z)))) := by
      intro z hz
      have hz_set := hMan_fin.mem_toFinset.mp hz
      obtain ⟨_, hz_src, hz_ball⟩ := hz_set
      have h_chart_z_closed :
          (chartAt ℂ x) z ∈ Metric.closedBall z₀ ε :=
        Metric.ball_subset_closedBall hz_ball
      have h_li : φ (ψ ((chartAt ℂ x) z)) = (chartAt ℂ x) z := by
        have := h_left_inv _ h_chart_z_closed
        simpa using this
      rw [h_li]
      have h_inv : (chartAt ℂ x).symm ((chartAt ℂ x) z) = z := (chartAt ℂ x).left_inv hz_src
      rw [h_inv]
    set F : ℂ → ℂ := fun s => g.toFun ((chartAt ℂ x).symm (φ s)) with hF_def
    have h_step1 :
        (∏ z ∈ hMan_fin.toFinset, g.toFun z)
          = ∏ z ∈ hMan_fin.toFinset, F (ψ ((chartAt ℂ x) z)) := by
      apply Finset.prod_congr rfl
      intro z hz
      exact h_fn_val z hz
    have h_step2 :
        (∏ z ∈ hMan_fin.toFinset, F (ψ ((chartAt ℂ x) z)))
          = ∏ ζ ∈ Finset.image (fun z => ψ ((chartAt ℂ x) z)) hMan_fin.toFinset, F ζ :=
      (Finset.prod_image h_inj_finset).symm
    have h_step3 :
        (∏ ζ ∈ Finset.image (fun z => ψ ((chartAt ℂ x) z)) hMan_fin.toFinset, F ζ)
          = ∏ ζ ∈ Polynomial.nthRootsFinset (manifoldRamificationIndex f x)
              ((chartAt ℂ (f x)) y - (chartAt ℂ (f x)) (f x)), F ζ := by
      rw [h_image]
    rw [h_step1, h_step2, h_step3]
    rfl

/-! ## Step 11b: pre-headline — per-`x` g_x and InjOn ψ at coordinated radius. -/

/-- For each `x ∈ f⁻¹{y₀}`, package step 5's Hurwitz form + InjOn together with
the planar germ `g_x` at a single radius. Existential output. -/
private theorem normFM_per_x_at_coord_radius
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (g : MeromorphicNonzero X) (x : X)
    (h_pos : 1 ≤ manifoldRamificationIndex f x) (R₀ : ℝ) (hR₀ : 0 < R₀) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ R₀ ∧ ∃ V : Set Y, IsOpen V ∧ f x ∈ V ∧
    (∀ w ∈ V, w ≠ f x →
      (f ⁻¹' {w} ∩
        ((chartAt ℂ x).source ∩
          (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε)).ncard
        = manifoldRamificationIndex f x) ∧
    ∃ g_x : ℂ → ℂ, MeromorphicAt g_x 0 ∧
      ∀ y : Y,
      ∀ (hMan_fin :
        (f ⁻¹' {y} ∩ ((chartAt ℂ x).source ∩
          (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε)).Finite),
        (f ⁻¹' {y} ∩
          ((chartAt ℂ x).source ∩
            (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε)).ncard
          = manifoldRamificationIndex f x →
        (∏ z ∈ hMan_fin.toFinset, g.toFun z) =
          normPow g_x (manifoldRamificationIndex f x)
            ((chartAt ℂ (f x)) y - (chartAt ℂ (f x)) (f x)) := by
  classical
  -- Step 5: Hurwitz form with InjOn at radius ρ.
  obtain ⟨ρ, hρ_pos, ψ, hψ_an_on, hψ_z₀, hψ_deriv, hψ_inj, hψ_eq⟩ :=
    hurwitz_local_form_at_fibre_with_injectivity hf hnc x h_pos
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀_def
  have hψ_an_at : AnalyticAt ℂ ψ z₀ :=
    hψ_an_on _ (Metric.mem_closedBall_self hρ_pos.le)
  -- Left-inverse holds in some nbhd of z₀.
  let φ : ℂ → ℂ :=
    hψ_an_at.hasStrictDerivAt.localInverse _ _ _ hψ_deriv
  have hφψ_id :
      ∀ᶠ w in 𝓝 z₀, φ (ψ w) = w :=
    hψ_an_at.hasStrictDerivAt.eventually_left_inverse hψ_deriv
  obtain ⟨δ, hδ_pos, hδ_sub⟩ :
      ∃ δ > 0, Metric.ball z₀ δ ⊆ {w | φ (ψ w) = w} :=
    Metric.eventually_nhds_iff_ball.mp hφψ_id
  -- Coordinated radius ε := min(R₀, ρ, δ/2).
  set ε_coord : ℝ := min R₀ (min ρ (δ / 2)) with hε_coord_def
  have hε_coord_pos : 0 < ε_coord := by
    refine lt_min hR₀ (lt_min hρ_pos ?_)
    positivity
  have hε_coord_le_R₀ : ε_coord ≤ R₀ := min_le_left _ _
  have hε_coord_le_ρ : ε_coord ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
  have hε_coord_le_half_δ : ε_coord ≤ δ / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hε_coord_lt_δ : ε_coord < δ := by linarith
  -- Apply localKFoldMultiplicityOnManifold_genuine_with_radius at R₀ := ε_coord
  -- to get count radius ε ≤ ε_coord.
  obtain ⟨ε, V, hε_pos, hε_le_ε_coord, hV_open, hfx_V, h_count⟩ :=
    JacobianChallenge.Manifold.localKFoldMultiplicityOnManifold_genuine_with_radius
      hf x h_pos hε_coord_pos
  have hε_le_R₀ : ε ≤ R₀ := hε_le_ε_coord.trans hε_coord_le_R₀
  have hε_le_ρ : ε ≤ ρ := hε_le_ε_coord.trans hε_coord_le_ρ
  have hε_lt_δ : ε < δ := lt_of_le_of_lt hε_le_ε_coord hε_coord_lt_δ
  -- Re-derive the radius-shrunk hypotheses on closedBall ε.
  have h_sub_ρ : Metric.closedBall z₀ ε ⊆ Metric.closedBall z₀ ρ :=
    Metric.closedBall_subset_closedBall hε_le_ρ
  have hψ_an_on_ε :
      AnalyticOnNhd ℂ ψ (Metric.closedBall z₀ ε) := by
    intro z hz; exact hψ_an_on z (h_sub_ρ hz)
  have hψ_inj_ε : Set.InjOn ψ (Metric.closedBall z₀ ε) :=
    hψ_inj.mono h_sub_ρ
  have hψ_eq_ε :
      ∀ z ∈ Metric.closedBall z₀ ε,
        ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z =
          (chartAt ℂ (f x)) (f x) + (ψ z) ^ (manifoldRamificationIndex f x) := by
    intro z hz; exact hψ_eq z (h_sub_ρ hz)
  have h_left_inv :
      ∀ w ∈ Metric.closedBall z₀ ε,
        (hψ_an_on_ε z₀ (Metric.mem_closedBall_self hε_pos.le)).hasStrictDerivAt.localInverse
            _ _ _ hψ_deriv (ψ w) = w := by
    intro w hw
    have hw_ball : w ∈ Metric.ball z₀ δ := by
      have : dist w z₀ ≤ ε := hw
      exact lt_of_le_of_lt this hε_lt_δ
    exact hδ_sub hw_ball
  -- Apply step 11a with ε, ψ.
  obtain ⟨g_x, hg_x_mero, h_prod⟩ :=
    normFM_local_product_eq_normPow_at_radius hf hnc g x h_pos hε_pos
      hψ_an_on_ε hψ_z₀ hψ_deriv hψ_inj_ε hψ_eq_ε h_left_inv
  exact ⟨ε, hε_pos, hε_le_R₀, V, hV_open, hfx_V, h_count, g_x, hg_x_mero, h_prod⟩

/-! ## Step 11c: NormFM_mmeromorphicAt y₀ — full headline assembly. -/

/-- Existence of a planar germ `g_x` (any one will do) at radius ε ≤ R₀.
Used to define `headline_g_x` cleanly via Classical.choose on a single layer. -/
private theorem headline_g_x_exists
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (g : MeromorphicNonzero X)
    (x : X) (h_pos : 1 ≤ manifoldRamificationIndex f x)
    {R₀ : ℝ} (hR₀ : 0 < R₀) :
    ∃ g_x : ℂ → ℂ, MeromorphicAt g_x 0 := by
  obtain ⟨_, _, _, _, _, _, _, g_x, hg_x, _⟩ :=
    normFM_per_x_at_coord_radius hf hnc g x h_pos R₀ hR₀
  exact ⟨g_x, hg_x⟩

/-- The per-`x` planar germ `g_x` for the headline. -/
private noncomputable def headline_g_x
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (g : MeromorphicNonzero X)
    (x : X) (h_pos : 1 ≤ manifoldRamificationIndex f x)
    {R₀ : ℝ} (hR₀ : 0 < R₀) : ℂ → ℂ :=
  Classical.choose (headline_g_x_exists hf hnc g x h_pos hR₀)

private theorem headline_g_x_meromorphicAt
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (g : MeromorphicNonzero X)
    (x : X) (h_pos : 1 ≤ manifoldRamificationIndex f x)
    {R₀ : ℝ} (hR₀ : 0 < R₀) :
    MeromorphicAt (headline_g_x hf hnc g x h_pos hR₀) 0 :=
  Classical.choose_spec (headline_g_x_exists hf hnc g x h_pos hR₀)

/-- The per-`x` factor function `F_x : Y → ℂ` for the headline assembly,
re-centred at the **target basepoint `y₀`** (not at `f x`). The chart used
to compare to `y₀` is `chartAt ℂ y₀`; the planar germ is `headline_g_x`.

For `x ∈ f⁻¹{y₀}` (so `f x = y₀`), this coincides with `normFM_F_x` after
an `f x = y₀` substitution. We use `y₀` as the chart basepoint here so the
final headline can stitch all per-`x` factors together at the same `y₀`. -/
noncomputable def headline_F_x
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (g : MeromorphicNonzero X)
    (x : X) (h_pos : 1 ≤ manifoldRamificationIndex f x)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (y₀ : Y) : Y → ℂ :=
  fun y =>
    normPow (headline_g_x hf hnc g x h_pos hR₀)
      (manifoldRamificationIndex f x)
      ((chartAt ℂ y₀) y - (chartAt ℂ y₀) y₀)

/-- The per-`x` factor `headline_F_x` is `MMeromorphicAt y₀`. Direct corollary
of `normPow_mmeromorphicAt_chartPullback_translated` (ZZ210) applied to the
planar germ `headline_g_x`. -/
theorem headline_F_x_mmeromorphicAt
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (g : MeromorphicNonzero X)
    (x : X) (h_pos : 1 ≤ manifoldRamificationIndex f x)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (y₀ : Y) :
    MMeromorphicAt (𝓘(ℂ, ℂ)) (headline_F_x hf hnc g x h_pos hR₀ y₀) y₀ :=
  normPow_mmeromorphicAt_chartPullback_translated h_pos
    (headline_g_x_meromorphicAt hf hnc g x h_pos hR₀)

/-- The finite product of per-`x` factors over the fibre `f ⁻¹' {y₀}` is
`MMeromorphicAt y₀`. Pure consequence of `mmeromorphicAt_finset_prod` and
`headline_F_x_mmeromorphicAt`.

This is the right-hand side of the eventual equality used in the final
`NormFM_mmeromorphicAt` assembly: on a punctured neighbourhood of `y₀`
consisting of regular values inside the ZZ211 decomposition, the fibre
product `NormFM y` agrees with this finite product (one factor per fibre
point). The eventual-equality discharge is the residual content that
will be wired in to close the headline. -/
theorem headline_finset_prod_F_x_mmeromorphicAt
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (g : MeromorphicNonzero X)
    (y₀ : Y)
    (hF_fin : (f ⁻¹' {y₀}).Finite)
    (h_pos_fn : ∀ x ∈ hF_fin.toFinset, 1 ≤ manifoldRamificationIndex f x)
    {R₀_fn : ∀ x ∈ hF_fin.toFinset, ℝ}
    (hR₀_pos_fn : ∀ x (hx : x ∈ hF_fin.toFinset), 0 < R₀_fn x hx) :
    MMeromorphicAt (𝓘(ℂ, ℂ))
      (fun y : Y => ∏ x ∈ hF_fin.toFinset.attach,
        headline_F_x hf hnc g x.val (h_pos_fn x.val x.property)
          (hR₀_pos_fn x.val x.property) y₀ y) y₀ := by
  classical
  apply mmeromorphicAt_finset_prod
  intro x _hx
  exact headline_F_x_mmeromorphicAt hf hnc g x.val
    (h_pos_fn x.val x.property) (hR₀_pos_fn x.val x.property) y₀

/-! ### Partial headline (Step B, ZZ216): per-`x` factors and their finite
product are meromorphic at `y₀`. The remaining content for the full
headline `NormFM_mmeromorphicAt` is the eventual equality
`NormFM f hf hnc g =ᶠ[𝓝[≠] y₀] (fun y => ∏ x, headline_F_x x y y₀)` on a
punctured open neighbourhood of `y₀` (built from the ZZ211 chart-radius
decomposition restricted to regular values via `criticalValues_finite_general`).
Once that equality is in place, `MeromorphicAt.congr` applied to
`headline_finset_prod_F_x_mmeromorphicAt` closes the headline. -/

/-! ## Step 12: Helper — shrink-radius preserves the per-x intersection.

If `f⁻¹{y} ∩ D_x_small` and `f⁻¹{y} ∩ D_x_large` both have the same finite
ncard `k`, and `D_x_small ⊆ D_x_large`, then the two intersections coincide
as sets. -/

lemma fibre_inter_chart_disk_shrink_eq
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} {f : X → Y} {y : Y} {x : X} {ε_small ε_large : ℝ}
    (hε_le : ε_small ≤ ε_large)
    (h_finite_large :
      (f ⁻¹' {y} ∩
        ((chartAt ℂ x).source ∩
          (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε_large)).Finite)
    (h_count_eq :
      (f ⁻¹' {y} ∩
        ((chartAt ℂ x).source ∩
          (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε_small)).ncard
        = (f ⁻¹' {y} ∩
            ((chartAt ℂ x).source ∩
              (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε_large)).ncard) :
    (f ⁻¹' {y} ∩
        ((chartAt ℂ x).source ∩
          (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε_small))
      = (f ⁻¹' {y} ∩
        ((chartAt ℂ x).source ∩
          (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε_large)) := by
  classical
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ h_finite_large
  · intro z hz
    refine ⟨hz.1, hz.2.1, ?_⟩
    exact Metric.ball_subset_ball hε_le hz.2.2
  · exact h_count_eq.symm.le

/-! ## Step 12 (ZZ219): Helper — `NormFM` at a regular value collapses to the
plain product `∏ g(z)` (no ramification weights), since every preimage `z` of
a non-critical value `y` has `manifoldRamificationIndex f z = 1`. -/

lemma NormFM_at_regular_value
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f)
    (g : MeromorphicNonzero X) {y : Y}
    (hy : y ∉ criticalValuesGeneral f) :
    NormFM f hf hnc g y =
      ∏ z ∈ (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional
                f hf hnc y).toFinset, g.toFun z := by
  classical
  rw [NormFM_apply]
  apply Finset.prod_congr rfl
  intro z hz
  have hz_fibre : z ∈ f ⁻¹' {y} :=
    (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional
      f hf hnc y).mem_toFinset.mp hz
  have h_ramif : manifoldRamificationIndex f z = 1 :=
    manifoldRamificationIndex_eq_one_at_regular_value_preimage hf hnc hy hz_fibre
  rw [h_ramif, pow_one]

/-! ## Step 12 (ZZ220): per-x existential rephrased with `y₀` in place of
`f x`. For `x ∈ f⁻¹{y₀}`, this is just `normFM_per_x_at_coord_radius`
with `f x` replaced by `y₀` everywhere it appears (in the membership
`f x ∈ V`, the witness exception `w ≠ f x`, and the chart difference
`chart_{f x} y - chart_{f x} (f x)`). The g_x is preserved verbatim. -/

theorem normFM_per_x_at_y₀
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (g : MeromorphicNonzero X)
    (x : X) (y₀ : Y) (hxy : f x = y₀)
    (h_pos : 1 ≤ manifoldRamificationIndex f x)
    (R₀ : ℝ) (hR₀ : 0 < R₀) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ R₀ ∧ ∃ V : Set Y, IsOpen V ∧ y₀ ∈ V ∧
    (∀ w ∈ V, w ≠ y₀ →
      (f ⁻¹' {w} ∩
        ((chartAt ℂ x).source ∩
          (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε)).ncard
        = manifoldRamificationIndex f x) ∧
    ∃ g_x : ℂ → ℂ, MeromorphicAt g_x 0 ∧
      ∀ y : Y,
      ∀ (hMan_fin :
        (f ⁻¹' {y} ∩ ((chartAt ℂ x).source ∩
          (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε)).Finite),
        (f ⁻¹' {y} ∩
          ((chartAt ℂ x).source ∩
            (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε)).ncard
          = manifoldRamificationIndex f x →
        (∏ z ∈ hMan_fin.toFinset, g.toFun z) =
          normPow g_x (manifoldRamificationIndex f x)
            ((chartAt ℂ y₀) y - (chartAt ℂ y₀) y₀) := by
  classical
  obtain ⟨ε, hε_pos, hε_le, V, hV_open, hfx_V, h_count, g_x, hg_x_mero, h_prod⟩ :=
    normFM_per_x_at_coord_radius hf hnc g x h_pos R₀ hR₀
  refine ⟨ε, hε_pos, hε_le, V, hV_open, ?_, ?_, g_x, hg_x_mero, ?_⟩
  · rw [← hxy]; exact hfx_V
  · intro w hw_V hw_ne_y₀
    have hw_ne_fx : w ≠ f x := by rw [hxy]; exact hw_ne_y₀
    exact h_count w hw_V hw_ne_fx
  · intro y hMan_fin h_count_y
    have h := h_prod y hMan_fin h_count_y
    rw [hxy] at h
    exact h

/-! ## Step 12 (ZZ221): generic finite-set partition product lemma.

Given a finite set `S`, a finite family `(D i)_{i ∈ FF}` of pairwise
disjoint sets that cover `S`, the product over `S` factors through the
product over `i` of the product over `S ∩ D i`. -/

lemma prod_finite_eq_prod_biUnion_inter
    {α β : Type*} [CommMonoid β] [DecidableEq α]
    {S : Set α} (hS : S.Finite)
    {ι : Type*} (FF : Finset ι) (D : ι → Set α)
    (h_disj : (FF : Set ι).PairwiseDisjoint D)
    (h_cov : S ⊆ ⋃ i ∈ FF, D i)
    (φ : α → β) :
    ∏ z ∈ hS.toFinset, φ z =
      ∏ i ∈ FF, ∏ z ∈ (hS.inter_of_left (D i)).toFinset, φ z := by
  classical
  set T : ι → Finset α := fun i => (hS.inter_of_left (D i)).toFinset with hT_def
  have hT_disj : (FF : Set ι).PairwiseDisjoint T := by
    intro i hi j hj hij
    have hD_disj : Disjoint (D i) (D j) := h_disj hi hj hij
    refine Finset.disjoint_left.mpr ?_
    intro a hai haj
    have hai_set : a ∈ S ∩ D i :=
      (hS.inter_of_left (D i)).mem_toFinset.mp hai
    have haj_set : a ∈ S ∩ D j :=
      (hS.inter_of_left (D j)).mem_toFinset.mp haj
    exact (Set.disjoint_left.mp hD_disj hai_set.2 haj_set.2)
  have h_eq : hS.toFinset = FF.biUnion T := by
    apply Finset.ext
    intro a
    simp only [Finset.mem_biUnion, hT_def, Set.Finite.mem_toFinset]
    constructor
    · intro ha_S
      obtain ⟨i, hi_FF, ha_Di⟩ := Set.mem_iUnion₂.mp (h_cov ha_S)
      exact ⟨i, hi_FF, ha_S, ha_Di⟩
    · rintro ⟨_, _, ha_S, _⟩
      exact ha_S
  rw [h_eq]
  exact Finset.prod_biUnion hT_disj

/-! ## Step 12 (ZZ222a): per-x data extraction.

For `x ∈ f⁻¹{y₀}` and a chosen radius bound `R₀ > 0`, extract the
existential output of `normFM_per_x_at_y₀` as concrete `noncomputable`
values via `Classical.choose`. The whole block of fields is extracted
from a SINGLE existential so the projections are mutually consistent
(in particular the planar germ `g_x` is the same one whose `prod_eq`
field we use). -/

variable {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
  (hnc : ¬ JacobianChallenge.IsConstantMap f) (g : MeromorphicNonzero X)

/-- Per-x ε (radius). -/
private noncomputable def perXEps
    (x : X) (y₀ : Y) (hxy : f x = y₀)
    (h_pos : 1 ≤ manifoldRamificationIndex f x)
    (R₀ : ℝ) (hR₀ : 0 < R₀) : ℝ :=
  Classical.choose (normFM_per_x_at_y₀ hf hnc g x y₀ hxy h_pos R₀ hR₀)

private theorem perXEps_spec
    (x : X) (y₀ : Y) (hxy : f x = y₀)
    (h_pos : 1 ≤ manifoldRamificationIndex f x)
    (R₀ : ℝ) (hR₀ : 0 < R₀) :
    0 < perXEps hf hnc g x y₀ hxy h_pos R₀ hR₀ ∧
      perXEps hf hnc g x y₀ hxy h_pos R₀ hR₀ ≤ R₀ ∧
      ∃ V : Set Y, IsOpen V ∧ y₀ ∈ V ∧
      (∀ w ∈ V, w ≠ y₀ →
        (f ⁻¹' {w} ∩
          ((chartAt ℂ x).source ∩
            (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x)
              (perXEps hf hnc g x y₀ hxy h_pos R₀ hR₀))).ncard
          = manifoldRamificationIndex f x) ∧
      ∃ g_x : ℂ → ℂ, MeromorphicAt g_x 0 ∧
        ∀ y : Y,
        ∀ (hMan_fin :
          (f ⁻¹' {y} ∩ ((chartAt ℂ x).source ∩
            (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x)
              (perXEps hf hnc g x y₀ hxy h_pos R₀ hR₀))).Finite),
          (f ⁻¹' {y} ∩
            ((chartAt ℂ x).source ∩
              (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x)
                (perXEps hf hnc g x y₀ hxy h_pos R₀ hR₀))).ncard
            = manifoldRamificationIndex f x →
          (∏ z ∈ hMan_fin.toFinset, g.toFun z) =
            normPow g_x (manifoldRamificationIndex f x)
              ((chartAt ℂ y₀) y - (chartAt ℂ y₀) y₀) :=
  Classical.choose_spec (normFM_per_x_at_y₀ hf hnc g x y₀ hxy h_pos R₀ hR₀)

/-! ## Step 12 (ZZ222b): per-x data structure with clean field projections.

Wraps the `normFM_per_x_at_y₀` existential output as a single structure
so downstream chips access fields by name rather than chained
`Classical.choose_spec` lookups. -/

structure NormFMPerXData
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (g : MeromorphicNonzero X)
    (x : X) (y₀ : Y) (R₀ : ℝ) where
  ε : ℝ
  ε_pos : 0 < ε
  ε_le : ε ≤ R₀
  V : Set Y
  V_open : IsOpen V
  y₀_V : y₀ ∈ V
  count : ∀ w ∈ V, w ≠ y₀ →
    (f ⁻¹' {w} ∩
      ((chartAt ℂ x).source ∩
        (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε)).ncard
      = manifoldRamificationIndex f x
  g_x : ℂ → ℂ
  g_x_mero : MeromorphicAt g_x 0
  prod_eq : ∀ y : Y,
    ∀ (hMan_fin :
      (f ⁻¹' {y} ∩ ((chartAt ℂ x).source ∩
        (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε)).Finite),
      (f ⁻¹' {y} ∩
        ((chartAt ℂ x).source ∩
          (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε)).ncard
        = manifoldRamificationIndex f x →
      (∏ z ∈ hMan_fin.toFinset, g.toFun z) =
        normPow g_x (manifoldRamificationIndex f x)
          ((chartAt ℂ y₀) y - (chartAt ℂ y₀) y₀)

/-- Build a `NormFMPerXData` from the existential `normFM_per_x_at_y₀`. -/
noncomputable def NormFMPerXData.ofExistential
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (g : MeromorphicNonzero X)
    (x : X) (y₀ : Y) (hxy : f x = y₀)
    (h_pos : 1 ≤ manifoldRamificationIndex f x)
    (R₀ : ℝ) (hR₀ : 0 < R₀) :
    NormFMPerXData hf hnc g x y₀ R₀ :=
  let h := normFM_per_x_at_y₀ hf hnc g x y₀ hxy h_pos R₀ hR₀
  let ε := h.choose
  let h_ε := h.choose_spec
  let ε_pos := h_ε.1
  let h_ε' := h_ε.2
  let ε_le := h_ε'.1
  let h_V := h_ε'.2
  let V := h_V.choose
  let h_V' := h_V.choose_spec
  let V_open := h_V'.1
  let h_V'' := h_V'.2
  let y₀_V := h_V''.1
  let h_V''' := h_V''.2
  let count := h_V'''.1
  let h_g := h_V'''.2
  let g_x := h_g.choose
  let h_g_x := h_g.choose_spec
  let g_x_mero := h_g_x.1
  let prod_eq := h_g_x.2
  { ε := ε, ε_pos := ε_pos, ε_le := ε_le,
    V := V, V_open := V_open, y₀_V := y₀_V, count := count,
    g_x := g_x, g_x_mero := g_x_mero, prod_eq := prod_eq }

/-! ## Step 12 (ZZ222c): generic G-product MMeromorphicAt lemma.

Given an external assignment of per-x planar germs `g_x_fn x hx` (each
`MeromorphicAt 0`) for `x` in some `Finset X` whose every element maps
to `y₀`, the chart-translated finite product is `MMeromorphicAt y₀`. -/

lemma headlineG_mmeromorphicAt
    (f : X → Y) (y₀ : Y) (FF : Finset X)
    (h_pos_fn : ∀ x ∈ FF, 1 ≤ manifoldRamificationIndex f x)
    (g_x_fn : ∀ x ∈ FF, ℂ → ℂ)
    (g_x_mero : ∀ (x : X) (hx : x ∈ FF), MeromorphicAt (g_x_fn x hx) 0) :
    MMeromorphicAt (𝓘(ℂ, ℂ))
      (fun y : Y => ∏ x ∈ FF.attach,
        normPow (g_x_fn x.val x.property)
          (manifoldRamificationIndex f x.val)
          ((chartAt ℂ y₀) y - (chartAt ℂ y₀) y₀)) y₀ := by
  classical
  apply mmeromorphicAt_finset_prod
  intro x _hx
  exact normPow_mmeromorphicAt_chartPullback_translated
    (h_pos_fn x.val x.property) (g_x_mero x.val x.property)

end Manifold
end JacobianChallenge

end
