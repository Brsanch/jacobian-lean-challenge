/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DegreeOneFromSimpleZeroSimplePoleDischarge
import JacobianChallenge.Manifold.MeromorphicNonzeroPrincipalDivisorAtZero

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Discharge of `ChartDerivNeZeroImpliesNonCritical f`

For `f : MeromorphicNonzero X` and `x : X`: if `f.toFun(x) = 0` and the
chart-pullback `f.toFun ∘ (chartAt ℂ x).symm` has non-zero derivative
at `(chartAt ℂ x) x`, then `x ∉ f.criticalSet`.

**Proof strategy.**

1. The chart-pullback `g := f.toFun ∘ (chartAt ℂ x).symm` is analytic
   at `(chartAt ℂ x) x` with non-zero derivative (chart-pullback
   continuity from `f.regular_continuousAt` + meromorphicAt → analyticAt
   bridge; for `f.toFun(x) = 0`, the order is `≥ 0` so the chart-pullback
   is analytic).

2. By `HasStrictDerivAt.eventually_left_inverse`, `g` has a local
   left-inverse `h` on a nbhd of `(chartAt ℂ x) x`. This gives a
   nbhd `V` of `(chartAt ℂ x) x` where `g` is injective.

3. Find an open nbhd `U' ⊆ X` of `x` with:
   * `U' ⊆ (chartAt ℂ x).source`
   * `chart x' ∈ V` for `x' ∈ U'` (pullback of `V`).
   * No pole of `f` in `U'` (poles are finite by `poles_finite`).

4. On `U'`, `f.toRiemannSphere` is injective: for `x₁, x₂ ∈ U'` with
   `f.toRiemannSphere x₁ = f.toRiemannSphere x₂`, both are finite
   (since `U'` avoids poles), so `f.toFun x₁ = f.toFun x₂` by
   `OnePoint.coe_injective`. Then `g (chart x₁) = g (chart x₂)`; by
   `g` injective on `V` and `chart xᵢ ∈ V`, `chart x₁ = chart x₂`;
   by chart injectivity on source, `x₁ = x₂`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff Topology Classical
open Set OnePoint Filter

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`ChartDerivNeZeroImpliesNonCritical f` is unconditional** for every
`f : MeromorphicNonzero X`. -/
theorem chartDerivNeZeroImpliesNonCritical_holds (f : MeromorphicNonzero X) :
    ChartDerivNeZeroImpliesNonCritical f := by
  intro x h_val_zero h_deriv_ne h_crit
  -- Critical = no nbhd has InjOn f.toRiemannSphere. Exhibit a witness nbhd.
  apply h_crit
  -- Setup.
  set g : ℂ → ℂ := f.toFun ∘ (chartAt ℂ x).symm with hg_def
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀_def
  -- AnalyticAt g z₀.
  -- Continuity of f.toFun at x (need order ≥ 0).
  -- We have f.toFun x = 0, but that alone doesn't give order ≥ 0.
  -- However, mmeromorphicOrderAt < 0 ↔ pole. At a pole, f.toFun → ∞, not 0.
  -- So f.toFun x = 0 → not a pole → order ≥ 0.
  -- Subtle: `MeromorphicNonzero` doesn't directly give order ≥ 0 from value = 0.
  -- We need the contrapositive: order < 0 → x is a pole → f.toRiemannSphere x = ∞ ≠ some 0.
  -- But we don't even know `f.toRiemannSphere x = some 0` yet; just `f.toFun x = 0`.
  -- For continuity: regular_continuousAt requires order ≥ 0.
  -- Approach: directly use f.meromorphic + f.regular_continuousAt with a case split.
  -- If order < 0 (pole), the hypothesis `f.toFun x = 0` contradicts pole behavior.
  -- Easier: argue by contradiction on the deriv hypothesis.
  -- Actually: we can just use `f.meromorphic` for `MeromorphicAt`. AnalyticAt requires
  -- continuity, which requires order ≥ 0. Let's establish order ≥ 0 first via the deriv hyp.
  -- A function with non-zero derivative at z₀ is continuous at z₀ (deriv ⇒ continuous).
  -- But `deriv g z₀ ≠ 0` doesn't itself imply g is continuous at z₀; it just says the
  -- function has a non-zero derivative IF it has one. Hmm.
  -- However we DO know g is meromorphic at z₀ (from f.meromorphic). So g is either
  -- analytic at z₀ (order ≥ 0) or has a pole (order < 0).
  -- If g has a pole at z₀, then g(z) → ∞ as z → z₀ in ℂ. Then deriv g z₀ might be undefined
  -- or 0 (depending on convention). At a pole, mathlib's `deriv` returns 0 (junk value).
  -- So `deriv g z₀ ≠ 0` implies g is NOT a pole at z₀, hence analytic at z₀.
  have h_mer : MeromorphicAt g z₀ := f.meromorphic x (Set.mem_univ _)
  -- Order ≥ 0 from deriv ≠ 0 + meromorphicAt.
  have h_ord_nonneg : 0 ≤ meromorphicOrderAt g z₀ := by
    by_contra h_neg
    push_neg at h_neg
    -- order < 0 means pole. We'll derive deriv g z₀ = 0, contradicting h_deriv_ne.
    -- At a pole, `f * (z - z₀)^k` is analytic near z₀ with non-zero value for k = -order.
    -- The function f near z₀ behaves like `(z - z₀)^{-k} · h(z)` with h(z₀) ≠ 0, k ≥ 1.
    -- deriv f at z₀... well, f is NOT differentiable at z₀ (pole), so mathlib's deriv
    -- returns 0 there.
    -- The cleanest argument: AnalyticAt at z₀ implies continuous + differentiable.
    -- Conversely, not analytic + meromorphic + deriv ≠ 0 — hmm, the relationship is subtle.
    -- Direct: meromorphic + deriv defined non-zero → continuous → analytic.
    -- But this isn't a standard mathlib lemma I can easily cite. Let me use a different tactic.
    -- Direct: at a meromorphic pole, the function is unbounded near z₀; so it's not
    -- continuous; so `deriv` is undefined and returns 0.
    -- Concretely: `MeromorphicAt.deriv_eq_zero_of_not_analyticAt` or similar.
    -- Let me search for the right lemma; for now, use `MeromorphicAt.analyticAt` reverse:
    -- if NOT analytic at z₀ (and meromorphic), then deriv = 0.
    -- The lemma we want: `MeromorphicAt + ¬ AnalyticAt → deriv = 0` (since
    -- mathlib's deriv requires differentiability which requires analyticity here).
    -- Let me just use: `meromorphicOrderAt < 0 → ¬ AnalyticAt → ¬ DifferentiableAt → deriv = 0`.
    have h_not_an : ¬ AnalyticAt ℂ g z₀ := by
      intro h_an
      exact absurd h_an.meromorphicOrderAt_nonneg (not_le.mpr h_neg)
    -- ¬ AnalyticAt at z₀ + MeromorphicAt → ¬ DifferentiableAt at z₀.
    -- (Because for a meromorphic function, differentiable at z₀ → analytic at z₀.)
    -- Actually `differentiableAt → analyticAt` is the famous Goursat theorem.
    -- mathlib has `DifferentiableAt.analyticAt` (well, `DifferentiableOn.analyticOn`).
    -- For a function on ℂ, differentiable at z₀ implies analytic at z₀ (with the right
    -- assumptions about complete codomain).
    have h_not_diff : ¬ DifferentiableAt ℂ g z₀ := by
      intro h_diff
      -- A function differentiable on an open nbhd is analytic.
      -- Actually `DifferentiableAt → AnalyticAt` directly isn't true; we need on a nbhd.
      -- But if f is meromorphic + differentiable at z₀ + bounded near z₀, it's analytic.
      -- This is subtle. Let me use a different approach.
      -- For meromorphic functions, we have:
      -- "meromorphic + continuous = analytic" (MeromorphicAt.analyticAt).
      -- DifferentiableAt → ContinuousAt → ... so meromorphic + diff → cont → analytic.
      exact h_not_an (h_mer.analyticAt h_diff.continuousAt)
    -- deriv at non-differentiable point is 0.
    exact h_deriv_ne (deriv_zero_of_not_differentiableAt h_not_diff)
  -- Continuity of f.toFun at x.
  have h_cont_at_x : ContinuousAt f.toFun x := by
    apply f.regular_continuousAt
    unfold mmeromorphicOrderAt
    exact h_ord_nonneg
  -- AnalyticAt g z₀.
  have h_chart_symm_cont : ContinuousAt (chartAt ℂ x).symm z₀ :=
    (chartAt ℂ x).continuousAt_symm
      ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
  have h_chart_left : (chartAt ℂ x).symm z₀ = x :=
    (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have h_g_cont : ContinuousAt g z₀ :=
    h_cont_at_x.comp_of_eq h_chart_symm_cont h_chart_left
  have h_an : AnalyticAt ℂ g z₀ := h_mer.analyticAt h_g_cont
  -- HasStrictDerivAt g (deriv g z₀) z₀.
  have h_strict : HasStrictDerivAt g (deriv g z₀) z₀ := h_an.hasStrictDerivAt
  -- Eventually-left-inverse on a nbhd of z₀ in ℂ.
  have h_left_inv : ∀ᶠ z in 𝓝 z₀,
      h_strict.localInverse g (deriv g z₀) z₀ h_deriv_ne (g z) = z :=
    h_strict.eventually_left_inverse h_deriv_ne
  -- Extract a nbhd V ∈ 𝓝 z₀ on which g is InjOn.
  rcases Filter.eventually_iff_exists_mem.mp h_left_inv with ⟨V_set, hV_nhds, hV_inv⟩
  -- V_set ∈ 𝓝 z₀: extract an open ball / open nbhd inside.
  rcases _root_.mem_nhds_iff.mp hV_nhds with ⟨V_open, hV_sub, hV_open_open, hV_mem⟩
  -- V_open : Set ℂ open, V_open ⊆ V_set, z₀ ∈ V_open.
  -- g is InjOn V_open: for w₁, w₂ ∈ V_open with g w₁ = g w₂, apply localInverse:
  -- localInverse (g w_i) = w_i. So w₁ = localInverse (g w₁) = localInverse (g w₂) = w₂.
  have h_g_injOn : Set.InjOn g V_open := by
    intro w₁ hw₁ w₂ hw₂ hgw
    have h₁ := hV_inv w₁ (hV_sub hw₁)
    have h₂ := hV_inv w₂ (hV_sub hw₂)
    -- h₁ : localInverse (g w₁) = w₁; h₂ : localInverse (g w₂) = w₂.
    rw [← h₁, ← h₂, hgw]
  -- Now find the manifold-level nbhd U' of x.
  -- U₁ := chart.source ∩ chart ⁻¹ V_open. This is open + contains x.
  have h_chart_cont : ContinuousAt (chartAt ℂ x : X → ℂ) x :=
    (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
  have h_chart_pre_V_nhds : (chartAt ℂ x) ⁻¹' V_open ∈ 𝓝 x := by
    apply h_chart_cont.preimage_mem_nhds
    rw [show (chartAt ℂ x : X → ℂ) x = z₀ from rfl]
    exact hV_open_open.mem_nhds hV_mem
  have h_chart_src_nhds : (chartAt ℂ x).source ∈ 𝓝 x :=
    (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
  -- Pole avoidance: pole set is finite, find a nbhd avoiding it.
  have h_poles_fin :
      {y : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun y < (0 : WithTop ℤ)}.Finite := by
    apply MMeromorphicOn.poles_finite (𝓘(ℂ, ℂ)) f.toFun f.meromorphic f.nonvanishing_germ
  -- x is not a pole (order at x ≥ 0).
  have h_x_not_pole :
      x ∉ {y : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun y < (0 : WithTop ℤ)} := by
    simp only [Set.mem_setOf_eq]
    unfold mmeromorphicOrderAt
    push_neg
    exact h_ord_nonneg
  -- Pole set without x is closed (finite is closed in T1).
  have h_pole_minus_x_closed :
      IsClosed ({y : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun y < 0} \ {x}) :=
    (h_poles_fin.subset diff_subset).isClosed
  -- Complement is open and contains x.
  have h_no_pole_open : IsOpen
      (({y : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun y < 0} \ {x})ᶜ) :=
    h_pole_minus_x_closed.isOpen_compl
  have h_x_in_no_pole :
      x ∈ (({y : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun y < 0} \ {x})ᶜ) := by
    intro h_mem
    exact h_mem.2 rfl
  have h_no_pole_nhds :
      (({y : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun y < 0} \ {x})ᶜ) ∈ 𝓝 x :=
    h_no_pole_open.mem_nhds h_x_in_no_pole
  -- Combined nbhd: U' := chart.source ∩ chart ⁻¹ V_open ∩ no-pole-except-x.
  set U' : Set X := (chartAt ℂ x).source ∩ ((chartAt ℂ x) ⁻¹' V_open) ∩
                    ({y : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun y < 0} \ {x})ᶜ
                    with hU'_def
  have h_U'_nhds : U' ∈ 𝓝 x :=
    Filter.inter_mem (Filter.inter_mem h_chart_src_nhds h_chart_pre_V_nhds)
      h_no_pole_nhds
  refine ⟨U', h_U'_nhds, ?_⟩
  -- InjOn f.toRiemannSphere U'.
  intro x₁ hx₁ x₂ hx₂ h_eq
  obtain ⟨⟨hx₁_src, hx₁_pre⟩, hx₁_nopole⟩ := hx₁
  obtain ⟨⟨hx₂_src, hx₂_pre⟩, hx₂_nopole⟩ := hx₂
  -- xᵢ are not poles (or are = x). Actually we need them not to be poles.
  have h_x₁_nonpole : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x₁ := by
    -- hx₁_nopole : ¬ (order < 0 ∧ ≠ x). So either order ≥ 0 or = x.
    by_cases hx₁_eq : x₁ = x
    · rw [hx₁_eq]; exact h_ord_nonneg
    · -- x₁ ≠ x, so by hx₁_nopole, order x₁ ≥ 0 (not in pole set excluding x).
      by_contra h_neg
      push_neg at h_neg
      apply hx₁_nopole
      exact ⟨h_neg, hx₁_eq⟩
  have h_x₂_nonpole : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x₂ := by
    by_cases hx₂_eq : x₂ = x
    · rw [hx₂_eq]; exact h_ord_nonneg
    · by_contra h_neg
      push_neg at h_neg
      apply hx₂_nopole
      exact ⟨h_neg, hx₂_eq⟩
  -- f.toRiemannSphere xᵢ = some(f.toFun xᵢ).
  have h_apply_x₁ : f.toRiemannSphere x₁ = (((f.toFun x₁) : ℂ) : RiemannSphere) :=
    MeromorphicNonzero.toRiemannSphere_eq_some_of_order_nonneg f h_x₁_nonpole
  have h_apply_x₂ : f.toRiemannSphere x₂ = (((f.toFun x₂) : ℂ) : RiemannSphere) :=
    MeromorphicNonzero.toRiemannSphere_eq_some_of_order_nonneg f h_x₂_nonpole
  -- h_eq : f.toRiemannSphere x₁ = f.toRiemannSphere x₂ → some (f.toFun x₁) = some (f.toFun x₂).
  rw [h_apply_x₁, h_apply_x₂] at h_eq
  -- OnePoint.coe_injective : some-injective.
  have h_toFun_eq : f.toFun x₁ = f.toFun x₂ := OnePoint.coe_injective h_eq
  -- Now g (chart x₁) = g (chart x₂).
  have h_g_eq : g ((chartAt ℂ x) x₁) = g ((chartAt ℂ x) x₂) := by
    show (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x₁)
        = (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x₂)
    rw [Function.comp_apply, Function.comp_apply,
        (chartAt ℂ x).left_inv hx₁_src,
        (chartAt ℂ x).left_inv hx₂_src]
    exact h_toFun_eq
  -- chart xᵢ ∈ V_open (from hxᵢ_pre).
  have h_chart_x₁_V : (chartAt ℂ x) x₁ ∈ V_open := hx₁_pre
  have h_chart_x₂_V : (chartAt ℂ x) x₂ ∈ V_open := hx₂_pre
  -- g InjOn V_open → chart x₁ = chart x₂.
  have h_chart_eq : (chartAt ℂ x) x₁ = (chartAt ℂ x) x₂ :=
    h_g_injOn h_chart_x₁_V h_chart_x₂_V h_g_eq
  -- chart InjOn chart.source → x₁ = x₂.
  exact (chartAt ℂ x).injOn hx₁_src hx₂_src h_chart_eq

/-! ## Final unconditional closure of `DegreeOneFromSimpleZeroSimplePole` -/

/-- **`DegreeOneFromSimpleZeroSimplePole X` is unconditional.** -/
theorem degreeOneFromSimpleZeroSimplePole_holds (X : Type u)
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] :
    DegreeOneFromSimpleZeroSimplePole X := by
  apply degreeOneFromSimpleZeroSimplePole_holds_of_ChartDerivSub
  intro f
  exact chartDerivNeZeroImpliesNonCritical_holds f

/-! ## Item 16 fully closed (modulo placement in `Jacobian.lean`) -/

/-- **Item 16 closure: `Jacobian.ofCurve_inj` unconditional under
`0 < genus X`.** Composes the discharge above with
`ofCurve_inj_under_genus_pos` from
`Manifold/OfCurveInjFromDegreeOne.lean`. -/
theorem ofCurve_inj_holds {X : Type u}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (P : X) (h_pos : 0 < JacobianChallenge.genus X) :
    Function.Injective (Jacobian.ofCurve (X := X) P) :=
  ofCurve_inj_under_genus_pos (degreeOneFromSimpleZeroSimplePole_holds X) P h_pos

end JacobianChallenge

end
