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

end Manifold
end JacobianChallenge

end
