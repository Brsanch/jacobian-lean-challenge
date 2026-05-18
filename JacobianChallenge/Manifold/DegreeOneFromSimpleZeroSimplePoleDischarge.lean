/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.OfCurveInjFromDegreeOne
import JacobianChallenge.Manifold.MeromorphicNonzeroFiberFinsetCard
import JacobianChallenge.Manifold.MeromorphicExtensionValue
import JacobianChallenge.Manifold.MeromorphicNonzeroRegularValueSet
import JacobianChallenge.Manifold.CriticalSetDefinition

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Discharge of `DegreeOneFromSimpleZeroSimplePole X`

For `f : MeromorphicNonzero X` with `principalDivisorMap f = single Q₁ - single Q₂`
and `Q₁ ≠ Q₂`, the pole extension `f.toRiemannSphere` is non-constant
with `degreeFiber = 1`.

## Proof structure

The proof picks `(some 0 : RiemannSphere)` (the "zero point" of `ℙ¹`) as
a regular value and shows the fibre is `{Q₁}` (cardinality 1). Combined
with `MeromorphicNonzero.fiberFinset_card_eq_degreeFiber`, this gives
`degreeFiber = 1`.

The substantive content:

* **Order at Q₁ is 1** — from `principalDivisorMap_apply` + the value of
  `single Q₁ - single Q₂` at Q₁ being `1 - 0 = 1`.
* **f.toFun(Q₁) = 0** — from order 1 + chart-pullback analyticity
  (`AnalyticAt.analyticOrderAt_ne_zero`) + chart `left_inv`.
* **f.toFun(x) ≠ 0 for x ≠ Q₁** under `ord = 0` — same chain in reverse.
* **f.toRiemannSphere maps Q₂ to `∞`** — `toRiemannSphere_eq_infty_of_order_neg`
  at the simple pole.
* **`(some 0 : RS) ∈ regularValueSet`** — Q₁ is the unique preimage and
  is locally injective (order 1 → simple zero, no ramification).

## Hypothesis status

This file uses one named sub-hypothesis `OrderOneSingleFibreRegular f Q₁`
for the analytic content "fibre at 0 has cardinality 1 + 0 is regular".
The non-constancy is fully discharged. The pointwise content (order
values + value of `f.toRiemannSphere` at Q₁ and Q₂) is fully discharged.
The remaining locally-injective content (manifold-level translation of
the chart-pullback's `deriv ≠ 0` from order 1) requires significant
chart bookkeeping; deferred to a sister chip.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff Topology Classical
open Set OnePoint

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Pointwise order from `principalDivisorMap = single Q₁ - single Q₂` -/

/-- **Order at `Q₁` is `1`** when `principalDivisorMap f = single Q₁ - single Q₂`
and `Q₁ ≠ Q₂`. -/
private lemma order_eq_one_at_Q1
    {f : MeromorphicNonzero X} {Q₁ Q₂ : X} (hne : Q₁ ≠ Q₂)
    (hdiv : principalDivisorMap f = Div.single Q₁ - Div.single Q₂) :
    mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun Q₁ = ((1 : ℤ) : WithTop ℤ) := by
  classical
  letI : DecidableEq X := Classical.decEq X
  have h_apply : ((principalDivisorMap f : Div X) : X → ℤ) Q₁ = 1 := by
    rw [hdiv]
    show (Div.single Q₁ - Div.single Q₂ : Div X) Q₁ = 1
    rw [Div.single_sub_single_apply]
    simp [hne]
  rw [principalDivisorMap_apply] at h_apply
  have h_ne_top : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun Q₁ ≠ ⊤ :=
    f.nonvanishing_germ Q₁
  unfold MMeromorphicOn.orderFun at h_apply
  cases h : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun Q₁
  · exact absurd h h_ne_top
  · rename_i n
    rw [h] at h_apply
    show ((n : ℤ) : WithTop ℤ) = ((1 : ℤ) : WithTop ℤ)
    have hn : n = 1 := by simpa [WithTop.untop₀] using h_apply
    rw [hn]

/-- **Order at `Q₂` is `-1`** (simple pole). -/
private lemma order_eq_neg_one_at_Q2
    {f : MeromorphicNonzero X} {Q₁ Q₂ : X} (hne : Q₁ ≠ Q₂)
    (hdiv : principalDivisorMap f = Div.single Q₁ - Div.single Q₂) :
    mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun Q₂ = ((-1 : ℤ) : WithTop ℤ) := by
  classical
  letI : DecidableEq X := Classical.decEq X
  have h_apply : ((principalDivisorMap f : Div X) : X → ℤ) Q₂ = -1 := by
    rw [hdiv]
    show (Div.single Q₁ - Div.single Q₂ : Div X) Q₂ = -1
    rw [Div.single_sub_single_apply]
    have h_sym : Q₂ ≠ Q₁ := fun h => hne h.symm
    simp [h_sym]
  rw [principalDivisorMap_apply] at h_apply
  have h_ne_top : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun Q₂ ≠ ⊤ :=
    f.nonvanishing_germ Q₂
  unfold MMeromorphicOn.orderFun at h_apply
  cases h : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun Q₂
  · exact absurd h h_ne_top
  · rename_i n
    rw [h] at h_apply
    show ((n : ℤ) : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ)
    have hn : n = -1 := by simpa [WithTop.untop₀] using h_apply
    rw [hn]

/-- **Order at `x ∉ {Q₁, Q₂}` is `0`**. -/
private lemma order_eq_zero_off
    {f : MeromorphicNonzero X} {Q₁ Q₂ x : X}
    (hx₁ : x ≠ Q₁) (hx₂ : x ≠ Q₂)
    (hdiv : principalDivisorMap f = Div.single Q₁ - Div.single Q₂) :
    mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x = 0 := by
  classical
  letI : DecidableEq X := Classical.decEq X
  have h_apply : ((principalDivisorMap f : Div X) : X → ℤ) x = 0 := by
    rw [hdiv]
    show (Div.single Q₁ - Div.single Q₂ : Div X) x = 0
    rw [Div.single_sub_single_apply]
    simp [hx₁, hx₂]
  rw [principalDivisorMap_apply] at h_apply
  have h_ne_top : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x ≠ ⊤ :=
    f.nonvanishing_germ x
  rw [(MMeromorphicOn.orderFun_eq_zero_iff h_ne_top).mp h_apply]

/-! ## Pointwise values: `f.toFun` is 0 at Q₁, nonzero off divisor support -/

/-- **`f.toFun` vanishes at a point of strictly positive order.** -/
private lemma toFun_eq_zero_of_order_pos
    {f : MeromorphicNonzero X} {x : X}
    (h : ((1 : ℤ) : WithTop ℤ) ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    f.toFun x = 0 := by
  unfold mmeromorphicOrderAt at h
  have h_nonneg : 0 ≤ meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm)
                        ((chartAt ℂ x) x) :=
    le_trans (by decide : (0 : WithTop ℤ) ≤ ((1 : ℤ) : WithTop ℤ)) h
  have h_cont_at_x : ContinuousAt f.toFun x :=
    f.regular_continuousAt x (by unfold mmeromorphicOrderAt; exact h_nonneg)
  have h_chart_symm_cont : ContinuousAt (chartAt ℂ x).symm ((chartAt ℂ x) x) :=
    (chartAt ℂ x).continuousAt_symm
      ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
  have h_chart_left : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x :=
    (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have h_comp_cont : ContinuousAt (f.toFun ∘ (chartAt ℂ x).symm)
                       ((chartAt ℂ x) x) :=
    h_cont_at_x.comp_of_eq h_chart_symm_cont h_chart_left
  have h_mer : MeromorphicAt (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    f.meromorphic x (Set.mem_univ _)
  have h_an : AnalyticAt ℂ (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    h_mer.analyticAt h_comp_cont
  have h_eq : meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm)
                ((chartAt ℂ x) x)
              = (analyticOrderAt (f.toFun ∘ (chartAt ℂ x).symm)
                  ((chartAt ℂ x) x)).map (↑) := h_an.meromorphicOrderAt_eq
  rw [h_eq] at h
  have h_an_ne_zero : analyticOrderAt (f.toFun ∘ (chartAt ℂ x).symm)
                        ((chartAt ℂ x) x) ≠ 0 := by
    intro h_zero
    rw [h_zero] at h
    -- h : ((1 : ℤ) : WithTop ℤ) ≤ (0:ℕ∞).map ↑ = ((0:ℤ):WithTop ℤ).
    -- That gives 1 ≤ 0 in WithTop ℤ, false.
    simp only [ENat.map_zero] at h
    exact absurd h (by decide)
  have h_val_zero : (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0 :=
    apply_eq_zero_of_analyticOrderAt_ne_zero h_an_ne_zero
  show f.toFun x = 0
  rw [← h_chart_left]
  exact h_val_zero

/-- **`f.toFun` is non-zero at a point of zero order.** -/
private lemma toFun_ne_zero_of_order_zero
    {f : MeromorphicNonzero X} {x : X}
    (h : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x = 0) :
    f.toFun x ≠ 0 := by
  unfold mmeromorphicOrderAt at h
  have h_cont_at_x : ContinuousAt f.toFun x :=
    f.regular_continuousAt x (by unfold mmeromorphicOrderAt; rw [h])
  have h_chart_symm_cont : ContinuousAt (chartAt ℂ x).symm ((chartAt ℂ x) x) :=
    (chartAt ℂ x).continuousAt_symm
      ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
  have h_chart_left : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x :=
    (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have h_comp_cont : ContinuousAt (f.toFun ∘ (chartAt ℂ x).symm)
                       ((chartAt ℂ x) x) :=
    h_cont_at_x.comp_of_eq h_chart_symm_cont h_chart_left
  have h_mer : MeromorphicAt (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    f.meromorphic x (Set.mem_univ _)
  have h_an : AnalyticAt ℂ (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    h_mer.analyticAt h_comp_cont
  have h_eq : meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm)
                ((chartAt ℂ x) x)
              = (analyticOrderAt (f.toFun ∘ (chartAt ℂ x).symm)
                  ((chartAt ℂ x) x)).map (↑) := h_an.meromorphicOrderAt_eq
  rw [h_eq] at h
  have h_an_zero : analyticOrderAt (f.toFun ∘ (chartAt ℂ x).symm)
                    ((chartAt ℂ x) x) = 0 := by
    cases hn : analyticOrderAt (f.toFun ∘ (chartAt ℂ x).symm)
                ((chartAt ℂ x) x) with
    | top => rw [hn] at h; simp at h
    | coe n =>
      rw [hn] at h
      simp at h
      simpa [hn] using h
  have h_val_ne_zero : (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0 :=
    h_an.analyticOrderAt_eq_zero.mp h_an_zero
  show f.toFun x ≠ 0
  rw [← h_chart_left]
  exact h_val_ne_zero

/-! ## Non-constancy of `f.toRiemannSphere` -/

/-- **`f.toRiemannSphere` is non-constant** under the principal-divisor
hypothesis: `f.toRiemannSphere Q₁ = (some 0 : RS)` is finite while
`f.toRiemannSphere Q₂ = (∞ : RS)`. -/
private lemma toRiemannSphere_nonconst
    {f : MeromorphicNonzero X} {Q₁ Q₂ : X} (hne : Q₁ ≠ Q₂)
    (hdiv : principalDivisorMap f = Div.single Q₁ - Div.single Q₂) :
    ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere := by
  have h_Q2_infty : f.toRiemannSphere Q₂ = (∞ : RiemannSphere) := by
    apply MeromorphicNonzero.toRiemannSphere_eq_infty_of_order_neg
    rw [order_eq_neg_one_at_Q2 hne hdiv]
    decide
  rintro ⟨c, hc⟩
  have h_eq : f.toRiemannSphere Q₁ = f.toRiemannSphere Q₂ := by
    rw [hc Q₁, hc Q₂]
  rw [h_Q2_infty] at h_eq
  have h_infty := (MeromorphicNonzero.toRiemannSphere_eq_infty_iff f Q₁).mp h_eq
  rw [order_eq_one_at_Q1 hne hdiv] at h_infty
  exact absurd h_infty (by decide)

/-! ## `f.toRiemannSphere` values + preimage of `(some 0 : RS)` -/

/-- **`f.toRiemannSphere Q₁ = (some 0 : RS)`**. -/
private lemma toRiemannSphere_Q1_eq_zero
    {f : MeromorphicNonzero X} {Q₁ Q₂ : X} (hne : Q₁ ≠ Q₂)
    (hdiv : principalDivisorMap f = Div.single Q₁ - Div.single Q₂) :
    f.toRiemannSphere Q₁ = (((0 : ℂ) : RiemannSphere)) := by
  apply (MeromorphicNonzero.toRiemannSphere_eq_some_zero_iff f Q₁).mpr
  have h_ord : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun Q₁ = ((1 : ℤ) : WithTop ℤ) :=
    order_eq_one_at_Q1 hne hdiv
  refine ⟨?_, ?_⟩
  · rw [h_ord]; decide
  · apply toFun_eq_zero_of_order_pos
    rw [h_ord]

/-- **`f.toRiemannSphere x ≠ (some 0 : RS)`** for `x ∉ {Q₁, Q₂}`. -/
private lemma toRiemannSphere_off_ne_zero
    {f : MeromorphicNonzero X} {Q₁ Q₂ x : X}
    (hx₁ : x ≠ Q₁) (hx₂ : x ≠ Q₂)
    (hdiv : principalDivisorMap f = Div.single Q₁ - Div.single Q₂) :
    f.toRiemannSphere x ≠ (((0 : ℂ) : RiemannSphere)) := by
  intro h_eq
  have ⟨_, h_val⟩ :=
    (MeromorphicNonzero.toRiemannSphere_eq_some_zero_iff f x).mp h_eq
  exact toFun_ne_zero_of_order_zero (order_eq_zero_off hx₁ hx₂ hdiv) h_val

/-- **`f.toRiemannSphere Q₂ = ∞ ≠ (some 0 : RS)`**. -/
private lemma toRiemannSphere_Q2_ne_zero
    {f : MeromorphicNonzero X} {Q₁ Q₂ : X} (hne : Q₁ ≠ Q₂)
    (hdiv : principalDivisorMap f = Div.single Q₁ - Div.single Q₂) :
    f.toRiemannSphere Q₂ ≠ (((0 : ℂ) : RiemannSphere)) := by
  rw [MeromorphicNonzero.toRiemannSphere_eq_infty_of_order_neg f
        (by rw [order_eq_neg_one_at_Q2 hne hdiv]; decide)]
  exact OnePoint.infty_ne_coe (0 : ℂ)

/-- **The preimage of `(some 0 : RS)` is exactly `{Q₁}`.** -/
private lemma preimage_zero_eq_singleton
    {f : MeromorphicNonzero X} {Q₁ Q₂ : X} (hne : Q₁ ≠ Q₂)
    (hdiv : principalDivisorMap f = Div.single Q₁ - Div.single Q₂) :
    f.toRiemannSphere ⁻¹' {(((0 : ℂ) : RiemannSphere))} = {Q₁} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h_eq
    by_cases hx₁ : x = Q₁
    · exact hx₁
    by_cases hx₂ : x = Q₂
    · subst hx₂
      exact absurd h_eq (toRiemannSphere_Q2_ne_zero hne hdiv)
    · exact absurd h_eq (toRiemannSphere_off_ne_zero hx₁ hx₂ hdiv)
  · intro hx
    subst hx
    exact toRiemannSphere_Q1_eq_zero hne hdiv

/-! ## The full discharge

`OrderOneSingleFibreRegular` consists of two parts: (a) the preimage
is the singleton `{Q₁}` (fully discharged above as
`preimage_zero_eq_singleton`); (b) `(some 0 : RS)` is a regular value
(= not a critical value of `f`).

Part (b) reduces to "`Q₁` is locally injective at value `(some 0)`",
since `Q₁` is the unique preimage. Local injectivity at Q₁ follows
from order-1 at Q₁ via the inverse function theorem; we surface this
as one named sub-hypothesis. -/

/-- **Named sub-hypothesis** (carried forward from the earlier
attempted closure): there exists a regular-value witness at
`(some 0 : RS)` whose fibre is the singleton `{Q₁}`. -/
def OrderOneSingleFibreRegular (f : MeromorphicNonzero X) (Q₁ : X) : Prop :=
  ∃ hv : (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet,
    f.fiberFinset hv = {Q₁}

/-- **Conditional discharge of `DegreeOneFromSimpleZeroSimplePole X`
under `OrderOneSingleFibreRegular`** (composes the non-constancy
discharge with the named sub-hypothesis). -/
theorem degreeOneFromSimpleZeroSimplePole_holds_of_OrderOneSingleFibreRegular
    (h_sub : ∀ (f : MeromorphicNonzero X) (Q₁ Q₂ : X), Q₁ ≠ Q₂ →
      principalDivisorMap f = Div.single Q₁ - Div.single Q₂ →
        OrderOneSingleFibreRegular f Q₁) :
    DegreeOneFromSimpleZeroSimplePole X := by
  classical
  intro f Q₁ Q₂ hne hdiv
  have h_nonconst : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere :=
    toRiemannSphere_nonconst hne hdiv
  refine ⟨?_, h_nonconst⟩
  obtain ⟨hv, h_fiber⟩ := h_sub f Q₁ Q₂ hne hdiv
  have h_card_1 : (f.fiberFinset hv).card = 1 := by
    rw [h_fiber]; simp
  have h_eq := MeromorphicNonzero.fiberFinset_card_eq_degreeFiber f h_nonconst hv
  rw [h_card_1] at h_eq
  exact h_eq.symm

/-- **Named sub-hypothesis: `f.toRiemannSphere` is locally injective at
points with finite value where the chart-pullback of `f.toFun` has
nonzero derivative.**

For `f : MeromorphicNonzero X` and `x : X`: if `f.toFun(x) = 0` (so
the natural `RS`-chart at `f.toRiemannSphere x` is the north chart
acting as identity on finite values) and the chart-pullback
`f.toFun ∘ (chartAt ℂ x).symm` has non-zero derivative at
`(chartAt ℂ x) x`, then `x ∉ f.criticalSet`.

Classical content: inverse function theorem applied to the
chart-pullback (`HasStrictDerivAt.eventually_left_inverse`) composed
with chart translations. The discharge is `~150` LOC of chart
bookkeeping; surfaced as a named sub-hypothesis for clarity. -/
def ChartDerivNeZeroImpliesNonCritical (f : MeromorphicNonzero X) : Prop :=
  ∀ x : X, f.toFun x = 0 →
    deriv (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0 →
      x ∉ f.criticalSet

/-! ### Bonus discharge: chart-pullback derivative non-zero from order 1

The "deriv ≠ 0" half of the sub-hypothesis is pure complex-analytic
content (no chart bookkeeping); we discharge it inline as a private
lemma. The remaining content of the sub-hypothesis is the chart
translation of local injectivity, which is the deferred work. -/

/-- **Order 1 → chart-pullback derivative non-zero.** Pure
complex-analytic content. -/
private lemma chart_pullback_deriv_ne_zero_of_order_one
    {f : MeromorphicNonzero X} {x : X}
    (h_ord : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x = ((1 : ℤ) : WithTop ℤ)) :
    deriv (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0 := by
  unfold mmeromorphicOrderAt at h_ord
  -- Analytic at chart x.
  have h_cont_at_x : ContinuousAt f.toFun x := by
    apply f.regular_continuousAt
    unfold mmeromorphicOrderAt
    rw [h_ord]; decide
  have h_chart_symm_cont : ContinuousAt (chartAt ℂ x).symm ((chartAt ℂ x) x) :=
    (chartAt ℂ x).continuousAt_symm
      ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
  have h_chart_left : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x :=
    (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have h_comp_cont : ContinuousAt (f.toFun ∘ (chartAt ℂ x).symm)
                       ((chartAt ℂ x) x) :=
    h_cont_at_x.comp_of_eq h_chart_symm_cont h_chart_left
  have h_mer : MeromorphicAt (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    f.meromorphic x (Set.mem_univ _)
  have h_an : AnalyticAt ℂ (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    h_mer.analyticAt h_comp_cont
  -- Use `meromorphicOrderAt = analyticOrderAt.map ↑` to get analyticOrderAt info.
  have h_eq : meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm)
                ((chartAt ℂ x) x)
              = (analyticOrderAt (f.toFun ∘ (chartAt ℂ x).symm)
                  ((chartAt ℂ x) x)).map (↑) := h_an.meromorphicOrderAt_eq
  rw [h_ord] at h_eq
  -- (1:ℤ):WithTop ℤ = (analyticOrderAt _ _).map ↑.
  -- Use the iff for analyticOrderAt = 1: f differs from value by (z-x)·G with G ≠ 0.
  -- Apply `AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero`'s contrapositive.
  intro h_deriv_zero
  -- contrapositive: deriv = 0 → order ≠ 1.
  -- Use `AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero` to get
  -- analyticOrderAt (f - f x) x = 1 (under deriv ≠ 0). Contrapositive:
  -- analyticOrderAt (f - f x) x ≠ 1 if deriv = 0.
  -- But we have analyticOrderAt f x = 1 (since f x = 0, f - 0 = f).
  -- Need: f x = 0 + analyticOrderAt f x = 1 + deriv = 0 → contradiction.
  -- Get f x = 0 from analyticOrderAt = 1 (positive).
  -- From h_eq, the analyticOrderAt's cast equals (1:ℤ). Extract analyticOrderAt = 1.
  -- The cast `ENat.map ↑ : WithTop ℤ → WithTop ℤ` of `(↑n : ENat)` is `((n:ℤ):WithTop ℤ)`.
  -- So `((1:ℤ):WithTop ℤ) = (n : ℕ).cast.cast` would force n = 1.
  have h_an_ord_eq_one : analyticOrderAt (f.toFun ∘ (chartAt ℂ x).symm)
                          ((chartAt ℂ x) x) = (1 : ℕ∞) := by
    have h_cast_eq := h_eq
    -- Solve: ((1:ℤ):WithTop ℤ) = (analyticOrderAt).map ↑.
    cases hn : analyticOrderAt (f.toFun ∘ (chartAt ℂ x).symm)
                ((chartAt ℂ x) x) with
    | top =>
      rw [hn] at h_cast_eq
      simp at h_cast_eq
    | coe n =>
      rw [hn] at h_cast_eq
      -- h_cast_eq : ((1:ℤ):WithTop ℤ) = ((n:ℕ):ℕ∞).map ↑ = (((n:ℕ):ℤ):WithTop ℤ).
      -- Conclude n = 1.
      simp [ENat.map_coe] at h_cast_eq
      -- h_cast_eq : (n : ℤ) = 1 (after simp).
      have : n = 1 := by exact_mod_cast h_cast_eq.symm
      rw [this]
      rfl
  -- analyticOrderAt = 1, value = 0 (apply_eq_zero), deriv = 0. Use sub_eq_one's contrapositive.
  have h_val_zero : (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0 :=
    apply_eq_zero_of_analyticOrderAt_ne_zero (by rw [h_an_ord_eq_one]; decide)
  -- Apply `AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero`'s contrapositive.
  -- This lemma states: deriv ≠ 0 → analyticOrderAt (f - f x) x = 1.
  -- Contrapositive: analyticOrderAt (f - f x) x ≠ 1 → deriv = 0.
  -- We want: deriv = 0 → analyticOrderAt (f - f x) x ≠ 1.
  -- But we have analyticOrderAt f x = 1 and f x = 0, so f = f - f x (= f - 0 = f) and order = 1.
  -- Then `analyticOrderAt (f - f x) x = analyticOrderAt f x = 1` ≠ 1 contradiction... wait it IS 1.
  -- Hmm. Let me reverse: use the lemma directly to get a contradiction.
  -- The lemma gives: deriv ≠ 0 → order (f - fx) x = 1. So if deriv = 0, the hypothesis fails.
  -- BUT the lemma is one-directional. We need the converse direction.
  -- Look at the proof of `analyticOrderAt_sub_eq_one_of_deriv_ne_zero`:
  -- it has a `· contrapose! hf'` part showing if order > 1 then deriv = 0.
  -- So we actually have: order = 1 + deriv = 0 → ??? Not directly false.
  -- Let me use `iff` if available. Actually `analyticOrderAt_eq_one_of_zero_deriv_ne_zero`:
  --   AnalyticAt + f x = 0 + deriv ≠ 0 → analyticOrderAt = 1.
  -- Converse: AnalyticAt + f x = 0 + analyticOrderAt = 1 → deriv ≠ 0.
  -- We have all hypotheses. Use direct order 1 → deriv ≠ 0 lemma if exists. If not, derive.
  -- From analyticOrderAt = 1, by `analyticOrderAt_eq_natCast` (n=1):
  --   ∃ G analyticAt, G x ≠ 0, f =ᶠ (z - x)^1 · G.
  -- Then deriv f at x = G x ≠ 0.
  -- mathlib: rewrite analyticOrderAt = (n:ℕ∞) via `analyticOrderAt_eq_natCast`.
  have h_natCast : ∃ G : ℂ → ℂ, AnalyticAt ℂ G ((chartAt ℂ x) x) ∧
                    G ((chartAt ℂ x) x) ≠ 0 ∧
                    (f.toFun ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 ((chartAt ℂ x) x)]
                      fun z => (z - (chartAt ℂ x) x)^(1:ℕ) • G z := by
    have h_rw := h_an.analyticOrderAt_eq_natCast.mp
      (show analyticOrderAt _ _ = ((1 : ℕ) : ℕ∞) from by
        rw [h_an_ord_eq_one]; rfl)
    exact h_rw
  obtain ⟨G, hG_an, hG_ne, hG_eq⟩ := h_natCast
  -- deriv of f.toFun ∘ chart.symm at chart x = G (chart x).
  have h_deriv_eq : deriv (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
                    = G ((chartAt ℂ x) x) := by
    have h_eventually : (f.toFun ∘ (chartAt ℂ x).symm)
                          =ᶠ[𝓝 ((chartAt ℂ x) x)]
                          (fun z => (z - (chartAt ℂ x) x) • G z) := by
      have := hG_eq
      simpa [pow_one] using this
    rw [Filter.EventuallyEq.deriv_eq h_eventually]
    have hd_id : DifferentiableAt ℂ (fun z : ℂ => z - (chartAt ℂ x) x)
                  ((chartAt ℂ x) x) :=
      differentiableAt_id.sub_const _
    have hd_G : DifferentiableAt ℂ G ((chartAt ℂ x) x) :=
      hG_an.differentiableAt
    rw [deriv_fun_smul hd_id hd_G]
    simp
  rw [h_deriv_eq] at h_deriv_zero
  exact hG_ne h_deriv_zero

/-! ### Final discharge using both sub-hypotheses combined into one -/

/-- **`(some 0 : RS) ∈ f.regularValueSet`** under the named sub-hypothesis. -/
private lemma zero_mem_regularValueSet
    {f : MeromorphicNonzero X} {Q₁ Q₂ : X} (hne : Q₁ ≠ Q₂)
    (hdiv : principalDivisorMap f = Div.single Q₁ - Div.single Q₂)
    (h_sub : ChartDerivNeZeroImpliesNonCritical f) :
    (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet := by
  rw [MeromorphicNonzero.mem_regularValueSet]
  intro h_in
  obtain ⟨x, hx_crit, hx_eq⟩ := h_in
  have h_x_Q1 : x = Q₁ := by
    have : x ∈ f.toRiemannSphere ⁻¹' {(((0 : ℂ) : RiemannSphere))} := hx_eq
    rw [preimage_zero_eq_singleton hne hdiv] at this
    exact this
  rw [h_x_Q1] at hx_crit
  -- Use the sub-hypothesis.
  have h_Q1_zero : f.toFun Q₁ = 0 := by
    apply toFun_eq_zero_of_order_pos
    rw [order_eq_one_at_Q1 hne hdiv]
  have h_deriv_ne : deriv (f.toFun ∘ (chartAt ℂ Q₁).symm) ((chartAt ℂ Q₁) Q₁) ≠ 0 :=
    chart_pullback_deriv_ne_zero_of_order_one (order_eq_one_at_Q1 hne hdiv)
  exact h_sub Q₁ h_Q1_zero h_deriv_ne hx_crit

/-- **`OrderOneSingleFibreRegular f Q₁` holds** under the chart-deriv
sub-hypothesis. -/
private lemma orderOneSingleFibreRegular_holds_of_sub
    {f : MeromorphicNonzero X} {Q₁ Q₂ : X} (hne : Q₁ ≠ Q₂)
    (hdiv : principalDivisorMap f = Div.single Q₁ - Div.single Q₂)
    (h_sub : ChartDerivNeZeroImpliesNonCritical f) :
    OrderOneSingleFibreRegular f Q₁ := by
  refine ⟨zero_mem_regularValueSet hne hdiv h_sub, ?_⟩
  unfold MeromorphicNonzero.fiberFinset
  apply Finset.ext
  intro x
  simp only [Set.Finite.mem_toFinset]
  show x ∈ f.toRiemannSphere ⁻¹' {(((0 : ℂ) : RiemannSphere))}
        ↔ x ∈ ({Q₁} : Finset X)
  rw [preimage_zero_eq_singleton hne hdiv]
  simp

/-- **`DegreeOneFromSimpleZeroSimplePole X` holds modulo the chart-deriv
sub-hypothesis.** -/
theorem degreeOneFromSimpleZeroSimplePole_holds_of_ChartDerivSub
    (h_sub : ∀ f : MeromorphicNonzero X,
              ChartDerivNeZeroImpliesNonCritical f) :
    DegreeOneFromSimpleZeroSimplePole X := by
  apply degreeOneFromSimpleZeroSimplePole_holds_of_OrderOneSingleFibreRegular
  intro f Q₁ Q₂ hne hdiv
  exact orderOneSingleFibreRegular_holds_of_sub hne hdiv (h_sub f)

/-! ## Item 16 conditional closure (final)

Composing the chart-deriv sub-hypothesis with the existing
`ofCurve_inj_under_genus_pos`, we get a clean **conditional closure
of item 16 modulo a single classical sub-hypothesis** about manifold
local injectivity.

This is the cleanest end-state for item 16 at this mathlib pin: the
classical content (inverse function theorem chart-translation) is the
only remaining gap. -/

/-- **Item 16 conditional closure under chart-deriv sub-hypothesis.** -/
theorem ofCurve_inj_under_genus_pos_of_ChartDerivSub
    (h_sub : ∀ f : MeromorphicNonzero X,
              ChartDerivNeZeroImpliesNonCritical f)
    (P : X) (h_pos : 0 < JacobianChallenge.genus X) :
    Function.Injective (Jacobian.ofCurve (X := X) P) :=
  ofCurve_inj_under_genus_pos
    (degreeOneFromSimpleZeroSimplePole_holds_of_ChartDerivSub h_sub)
    P h_pos

end JacobianChallenge

end
