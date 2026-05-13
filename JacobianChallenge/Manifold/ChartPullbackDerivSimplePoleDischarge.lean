/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SimplePoleAnalyticReciprocal
import JacobianChallenge.Manifold.RegularValueWitnessAtInfty
import JacobianChallenge.Manifold.MeromorphicExtension
import JacobianChallenge.Manifold.MeromorphicAt
import JacobianChallenge.Manifold.RiemannSphere
import JacobianChallenge.Topology.MeroSinglePoleBridgeConditional

set_option diagnostics.threshold 100

/-! # Discharge of `ChartPullback_Deriv_AtSimplePole_NeZero` and
`UniformSimplePoleRegularity`

This chip wires the complex-analytic core from zz343
(`SimplePoleAnalyticReciprocal.lean`) through the chart pullback +
south-chart of `RiemannSphere` to discharge the named regularity
hypothesis on simple poles.

Specifically, we prove unconditionally:

* `MeromorphicNonzero.chartPullback_deriv_AtSimplePole_neZero` —
  for any `f : MeromorphicNonzero X` with a single simple pole at
  `p` and holomorphic elsewhere,
  `deriv (chartAt ℂ ∞ ∘ f.toRiemannSphere ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) ≠ 0`,
  i.e. `ChartPullback_Deriv_AtSimplePole_NeZero f p` (zz340).

* `uniformSimplePoleRegularity_holds` —
  `UniformSimplePoleRegularity X` (zz342) holds unconditionally on
  any compact connected complex 1-manifold.

Combined with zz342's
`riemannRochGenusZero_of_existence_and_uniformRegularity`, this
reduces `RiemannRochGenusZero X` to a *single* remaining named
classical input: `ExistsMeroSimplePole_GenusZero X` (zz337). The
analytic bridge half of the Forster route is now fully closed.

## Proof outline

1. `MMeromorphicAt I f.toFun p` + `mmeromorphicOrderAt I f.toFun p = -1`
   ⇒ (mathlib) ∃ analytic `g` at `chart p` with `g (chart p) ≠ 0` and
   `(f.toFun ∘ chart.symm) z = g z / (z - chart p)` for `z ∈ 𝓝[≠] (chart p)`.

2. Show `chartAt ℂ ∞ ∘ f.toRiemannSphere ∘ chart.symm
       =ᶠ[𝓝 (chart p)] candidate (chart p) g`,
   where `candidate (chart p) g z := (z - chart p) / g z` (zz343).

   * Punctured part: 1/((f.toFun ∘ chart.symm) z) = candidate ... z
     (zz343's `one_div_f_eventuallyEq_candidate`), aligning with
     `chartS (some w) = w⁻¹` at non-pole points.
   * Value at `chart p`: chartS ∞ = 0 = candidate (chart p) g (chart p).

3. `Filter.EventuallyEq.deriv_eq` ⇒ derivs match at `chart p`.

4. zz343's `deriv_candidate_ne_zero` ⇒ derivative is `1/g(chart p) ≠ 0`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Set OnePoint Filter

namespace JacobianChallenge

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace MeromorphicNonzero

/-- **Helper.** `chartS ∘ f.toRiemannSphere = z⁻¹` evaluated through
`some z` at non-pole points (regular branch). -/
private lemma chartS_toRiemannSphere_of_order_nonneg
    (f : MeromorphicNonzero X) {x : X}
    (h_nonneg : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    (chartAt ℂ (∞ : RiemannSphere)) (f.toRiemannSphere x) = (f.toFun x)⁻¹ := by
  -- f.toRiemannSphere x = some (f.toFun x) in the non-pole branch.
  have h_eq : f.toRiemannSphere x
      = (OnePoint.some (f.toFun x) : RiemannSphere) :=
    f.toRiemannSphere_apply_of_nonneg h_nonneg
  rw [h_eq]
  -- chartAt ℂ ∞ = chartS by ChartedSpace instance; chartS (some w) = w⁻¹.
  exact RiemannSphere.chartS_apply_coe (f.toFun x)

/-- **Helper.** `chartS ∘ f.toRiemannSphere = 0` evaluated through `∞`
at pole points. -/
private lemma chartS_toRiemannSphere_of_order_neg
    (f : MeromorphicNonzero X) {x : X}
    (h_neg : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0) :
    (chartAt ℂ (∞ : RiemannSphere)) (f.toRiemannSphere x) = 0 := by
  have h_eq : f.toRiemannSphere x = (∞ : RiemannSphere) :=
    f.toRiemannSphere_apply_of_neg h_neg
  rw [h_eq]
  exact RiemannSphere.chartS_apply_infty

/-- **The chart-pullback derivative is non-zero at a simple pole.**
This is precisely `ChartPullback_Deriv_AtSimplePole_NeZero f p`
(zz340). -/
theorem chartPullback_deriv_AtSimplePole_neZero
    (f : MeromorphicNonzero X) {p : X}
    (h_pole : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p = ((-1 : ℤ) : WithTop ℤ))
    (h_holo : ∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    ChartPullback_Deriv_AtSimplePole_NeZero f p := by
  unfold ChartPullback_Deriv_AtSimplePole_NeZero
  -- Setup: chart at p, image of p, chart at ∞ = chartS.
  set ch : OpenPartialHomeomorph X ℂ := chartAt ℂ p with hch
  set zp : ℂ := ch p with hzp
  -- The chart-pullback function f.toFun ∘ ch.symm is MeromorphicAt zp,
  -- with meromorphicOrderAt = -1.
  have h_mero_chart : MeromorphicAt (f.toFun ∘ ch.symm) zp := by
    have := f.meromorphic p (Set.mem_univ p)
    -- MMeromorphicAt unfolds to MeromorphicAt (f.toFun ∘ chart.symm) (chart p).
    exact this
  have h_ord_chart : meromorphicOrderAt (f.toFun ∘ ch.symm) zp
      = ((-1 : ℤ) : WithTop ℤ) := h_pole
  -- Extract analytic witness g from zz343.
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ :=
    SimplePole.exists_analytic_witness_at_simple_pole h_mero_chart h_ord_chart
  -- Define the candidate (zz343).
  set candidate : ℂ → ℂ := SimplePole.candidate zp g with hcand
  -- Goal: deriv (chartS ∘ f.toRiemannSphere ∘ ch.symm) zp ≠ 0.
  -- Step 1: punctured-neighbourhood equality.
  have h_punctured : (fun z => (chartAt ℂ (∞ : RiemannSphere))
      (f.toRiemannSphere (ch.symm z))) =ᶠ[𝓝[≠] zp] candidate := by
    -- Build EventuallyEq on 𝓝[≠] zp.
    -- We need: for z ≠ zp near zp, LHS = candidate z.
    have h_src : ch.source ∈ 𝓝 p := by
      apply (ch.open_source).mem_nhds
      exact mem_chart_source ℂ p
    have h_tgt : ch.target ∈ 𝓝 zp := by
      apply (ch.open_target).mem_nhds
      exact ch.map_source (mem_chart_source ℂ p)
    have h_tgt' : ch.target ∈ 𝓝[≠] zp := nhdsWithin_le_nhds h_tgt
    -- Apply ZZ343's one_div_f_eventuallyEq_candidate.
    have h_1f : (fun z => 1 / (f.toFun ∘ ch.symm) z)
        =ᶠ[𝓝[≠] zp] candidate :=
      SimplePole.one_div_f_eventuallyEq_candidate hg_an hg_ne hg_eq
    -- Combine with chart-symm-z ≠ p, holomorphic-elsewhere, and
    -- chartS (some w) = w⁻¹.
    filter_upwards [h_1f, h_tgt', self_mem_nhdsWithin]
      with z h_1f_z h_z_tgt h_z_ne
    -- h_z_ne : z ∈ ({zp}ᶜ : Set ℂ), i.e. z ≠ zp.
    -- Derive chart.symm z ≠ p from chart injectivity.
    have h_symm_ne : ch.symm z ≠ p := by
      intro h_eq
      apply h_z_ne
      -- Goal: z ∈ ({zp}ᶜ : Set ℂ), i.e. z ≠ zp. We need z = zp.
      show z = zp
      -- Have: ch.symm z = p, i.e. ch (ch.symm z) = ch p = zp.
      have h := ch.right_inv h_z_tgt
      -- h : ch (ch.symm z) = z; want z = zp.
      rw [h_eq] at h
      -- h : ch p = z; goal is z = zp = ch p.
      exact h.symm
    -- Apply h_holo at ch.symm z.
    have h_nonneg : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun (ch.symm z) :=
      h_holo (ch.symm z) h_symm_ne
    -- Conclude LHS = (f.toFun (ch.symm z))⁻¹ = candidate z.
    have h_lhs := chartS_toRiemannSphere_of_order_nonneg f h_nonneg
    -- h_lhs : chartS (f.toRiemannSphere (ch.symm z)) = (f.toFun (ch.symm z))⁻¹
    -- Rewrite the goal.
    show (chartAt ℂ (∞ : RiemannSphere)) (f.toRiemannSphere (ch.symm z))
        = candidate z
    rw [h_lhs]
    -- Goal: (f.toFun (ch.symm z))⁻¹ = candidate z.
    -- Have h_1f_z : 1 / (f.toFun ∘ ch.symm) z = candidate z.
    have : (f.toFun (ch.symm z))⁻¹ = 1 / (f.toFun ∘ ch.symm) z := by
      simp [Function.comp, one_div]
    rw [this]
    exact h_1f_z
  -- Step 2: equality at zp.
  have h_at_zp : (chartAt ℂ (∞ : RiemannSphere))
      (f.toRiemannSphere (ch.symm zp)) = candidate zp := by
    -- ch.symm zp = p (left inverse since p ∈ ch.source).
    have hp_src : p ∈ ch.source := mem_chart_source ℂ p
    have h_inv : ch.symm zp = p := by
      rw [hzp]; exact ch.left_inv hp_src
    rw [h_inv]
    -- f.toRiemannSphere p = ∞ (since order at p is -1 < 0).
    have h_p_neg : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p < 0 := by
      rw [h_pole]
      exact_mod_cast (show (-1 : ℤ) < 0 from by decide)
    have h_lhs := chartS_toRiemannSphere_of_order_neg f h_p_neg
    rw [h_lhs]
    -- candidate zp = (zp - zp) / g zp = 0.
    simp [hcand, SimplePole.candidate_at_zero]
  -- Step 3: combine into EventuallyEq on 𝓝 zp.
  have h_eq_full :
      (fun z => (chartAt ℂ (∞ : RiemannSphere))
        (f.toRiemannSphere (ch.symm z)))
        =ᶠ[𝓝 zp] candidate :=
    eventuallyEq_nhds_of_eventuallyEq_nhdsNE h_punctured h_at_zp
  -- Step 4: derivs equal.
  have h_derivs_eq :
      deriv (fun z => (chartAt ℂ (∞ : RiemannSphere))
        (f.toRiemannSphere (ch.symm z))) zp = deriv candidate zp :=
    Filter.EventuallyEq.deriv_eq h_eq_full
  -- The goal uses ∘ instead of explicit lambda; align.
  show deriv ((chartAt ℂ (∞ : RiemannSphere))
      ∘ f.toRiemannSphere ∘ ch.symm) zp ≠ 0
  -- The composition is definitionally equal to the explicit lambda.
  have h_align :
      ((chartAt ℂ (∞ : RiemannSphere)) ∘ f.toRiemannSphere ∘ ch.symm)
      = (fun z => (chartAt ℂ (∞ : RiemannSphere))
          (f.toRiemannSphere (ch.symm z))) := rfl
  rw [h_align, h_derivs_eq]
  -- Step 5: candidate derivative is non-zero.
  exact SimplePole.deriv_candidate_ne_zero hg_an hg_ne

end MeromorphicNonzero

/-- **`UniformSimplePoleRegularity X` holds unconditionally** on any
compact connected complex 1-manifold. -/
theorem uniformSimplePoleRegularity_holds
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    UniformSimplePoleRegularity X := by
  intro f p h_pole h_holo
  exact MeromorphicNonzero.chartPullback_deriv_AtSimplePole_neZero
    f h_pole h_holo

end JacobianChallenge

end
