/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicOrderEqRamificationAtPole
import JacobianChallenge.Manifold.MeromorphicOrderEqRamificationAtZero
import JacobianChallenge.Manifold.NearbyRegularWitnessUnconditional
import JacobianChallenge.Manifold.ResidueTheorem
import JacobianChallenge.Manifold.ResidueTheoremFromRsum

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Unconditional discharge of `R4_fibreSum_balance_statement`

This file (the **R4composer** chip) closes
`R4_fibreSum_balance_statement X` (the last open ingredient of the
residue-theorem skeleton) by composing:

* `mmeromorphicOrderAt_eq_ramificationIndex_at_zero` (R4a, chartN side),
* `mmeromorphicOrderAt_eq_ramificationIndex_at_pole` (R4b, chartS side),
* `ramificationSumEqualsDegree_holds_unconditional` (the unconditional
  ramification-sum-equals-degree theorem).

The two applications of `ramificationSumEqualsDegree_holds_unconditional`
are at the values `((0 : ℂ) : RiemannSphere)` and `(∞ : RiemannSphere)`;
both right-hand sides equal the same `degreeFiber`, hence the LHS sums
of `manifoldRamificationIndex` are equal. Convert via R4a / R4b and
sign-cancel.

The constant case is handled inline. Inputs from in-tree:
`MeromorphicNonzero.nonvanishing_germ`, `R2_fibres_finite_statement_holds`,
`untop₀_*` bridges from `ResidueTheoremFromRsum`. -/

@[expose] public section

noncomputable section

open scoped Manifold Topology ContDiff BigOperators
open Filter Set OnePoint

namespace JacobianChallenge

namespace R4FibreSumBalance

universe u

variable (X : Type u)
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Setup notation: shorthand for the unconditional fibres-finite witness -/

/-- Shorthand: the unconditional fibre-finite witness for `f.toRiemannSphere`
applied at `y`. Re-exposed at this name so we don't have to break long
qualified names across lines. -/
private def fibresFinUncond
    (f : JacobianChallenge.MeromorphicNonzero X)
    (hf_RS : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f.toRiemannSphere)
    (hnc_RS : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (y : RiemannSphere) :
    (f.toRiemannSphere ⁻¹' {y}).Finite :=
  JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional
    f.toRiemannSphere hf_RS hnc_RS y

/-- Shorthand: the unconditional ramification-sum-equals-degree statement. -/
private theorem ramSumEqDeg
    (f : JacobianChallenge.MeromorphicNonzero X)
    (hf_RS : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f.toRiemannSphere)
    (hnc_RS : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (y : RiemannSphere) :
    (∑ x ∈ (fibresFinUncond X f hf_RS hnc_RS y).toFinset,
        JacobianChallenge.Manifold.manifoldRamificationIndex
          f.toRiemannSphere x : ℕ)
      = JacobianChallenge.ContMDiff.degreeFiber f.toRiemannSphere hf_RS := by
  have h := JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_holds_unconditional
    X RiemannSphere f.toRiemannSphere hf_RS hnc_RS y
  exact h

/-! ## Order at constant `f.toFun = w ≠ 0` -/

/-- If `f.toFun` is the constant function `(fun _ => w)` with `w ≠ 0`,
then every meromorphic order is zero. -/
private lemma mmeromorphicOrderAt_const
    (f : JacobianChallenge.MeromorphicNonzero X) {w : ℂ}
    (hconst : ∀ x, f.toFun x = w) (hw : w ≠ 0) (x : X) :
    mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x = 0 := by
  have h_const_pullback :
      (f.toFun ∘ (chartAt ℂ x).symm) = (fun _ : ℂ => w) := by
    funext z
    show f.toFun ((chartAt ℂ x).symm z) = w
    exact hconst _
  have h_eq :
      meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0 := by
    rw [h_const_pullback]
    have h_an : AnalyticAt ℂ (fun _ : ℂ => w) ((chartAt ℂ x) x) := analyticAt_const
    rw [h_an.meromorphicOrderAt_eq]
    rw [(h_an.analyticOrderAt_eq_zero).mpr hw]
    rfl
  exact h_eq

/-! ## R4 in the constant-`f.toFun` case -/

/-- If `f.toFun` is constant, R4 trivially holds (both summed sets are empty). -/
private lemma R4_balance_of_const_toFun
    (f : JacobianChallenge.MeromorphicNonzero X)
    (hconst : JacobianChallenge.IsConstantMap f.toFun)
    (hZ : {x : X | (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ > 0}.Finite)
    (hP : {x : X | (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ < 0}.Finite) :
    (∑ x ∈ hZ.toFinset, (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀) +
      (∑ x ∈ hP.toFinset,
          (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀) = 0 := by
  classical
  obtain ⟨w, hw_const⟩ := hconst
  -- `w ≠ 0` (else `nonvanishing_germ` violated).
  have hw_ne : w ≠ 0 := by
    intro h_w_zero
    have hx0 : X := Classical.arbitrary X
    have h_pullback_zero :
        (f.toFun ∘ (chartAt ℂ hx0).symm) = (fun _ : ℂ => (0 : ℂ)) := by
      funext z
      show f.toFun ((chartAt ℂ hx0).symm z) = 0
      rw [hw_const, h_w_zero]
    have h_top : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun hx0 = ⊤ := by
      show meromorphicOrderAt (f.toFun ∘ (chartAt ℂ hx0).symm)
          ((chartAt ℂ hx0) hx0) = ⊤
      rw [h_pullback_zero]
      have h_an : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) ((chartAt ℂ hx0) hx0) :=
        analyticAt_const
      rw [h_an.meromorphicOrderAt_eq]
      have h_zero_ev : (fun _ : ℂ => (0 : ℂ)) =ᶠ[𝓝 ((chartAt ℂ hx0) hx0)]
          (fun _ => 0) := Filter.EventuallyEq.refl _ _
      rw [analyticOrderAt_eq_top.mpr h_zero_ev]
      rfl
    exact f.nonvanishing_germ hx0 h_top
  -- All orders are 0.
  have h_all_zero : ∀ x, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x = 0 :=
    mmeromorphicOrderAt_const X f hw_const hw_ne
  -- Both summed sets are empty.
  have hZ_empty : hZ.toFinset = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro x hx
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx
    rw [h_all_zero x] at hx
    -- hx : 0 < ((0 : WithTop ℤ).untop₀ : ℤ) = 0; contradiction.
    have : (((0 : WithTop ℤ)).untop₀ : ℤ) = 0 := by simp
    rw [this] at hx
    exact lt_irrefl 0 hx
  have hP_empty : hP.toFinset = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro x hx
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx
    rw [h_all_zero x] at hx
    have : (((0 : WithTop ℤ)).untop₀ : ℤ) = 0 := by simp
    rw [this] at hx
    exact lt_irrefl 0 hx
  rw [hZ_empty, hP_empty]
  simp

/-! ## `IsConstantMap f.toRS → IsConstantMap f.toFun`

We rule out the `c = ∞` case by deriving `Set.univ.Finite` from R2 and
contradicting it via the *positive*-order set being infinite — which it
isn't here either, but the simpler route is: if all points are poles,
then in particular `nonvanishing_germ` plus R2 finiteness lets us get a
contradiction with the existence of a chart-source-open neighborhood.

We formalize this contradiction by selecting an arbitrary point `x₀ ∈ X`
(from `ConnectedSpace.toNonempty`), using its chart to extract a punctured
neighborhood, and applying mathlib's
`MeromorphicAt.eventually_analyticAt`-style infrastructure: at every point
of an open neighborhood of `(chartAt ℂ x₀) x₀`, the chart pullback has
order `≥ 0` (since meromorphic functions have isolated poles). Hence near
`x₀`, almost all points are non-poles — contradicting the all-poles
hypothesis.

The cleanest tool for this is mathlib's
`MeromorphicAt.eventually_meromorphicOrderAt_zero_or_pos` (or rather, the
fact that `MeromorphicAt f z₀` implies `∀ᶠ z in 𝓝 z₀, MeromorphicAt f z`
together with `∀ᶠ z in 𝓝[≠] z₀, meromorphicOrderAt f z = 0`).

We sidestep finding the precise mathlib lemma name by using
the divisor-side `local-finiteness` packaging implicit in
`f.meromorphic`, whose `supportLocallyFiniteWithinDomain'` field gives
exactly: every point has an open neighborhood where the pole-set is
finite. Combined with `T2Space + ConnectedSpace + ChartedSpace ℂ + nonempty`,
the all-pole hypothesis yields a finite open neighborhood — but open
nonempty subsets of ℂ pulled back through a chart give infinitely many
points, contradiction.

Implementation note: Rather than building this contradiction by hand,
we use a much shorter route — the **`MMeromorphicOn.divisor`** (in
`Manifold/MeromorphicDivisor.lean`) is a `locallyFinsuppWithin` whose
support is the order-nonzero set. Its support being locally finite means
every point has a neighborhood where only finitely many are
order-nonzero. If all points are poles, then EVERY point is
order-nonzero, so EVERY neighborhood of x₀ has only finitely many points
— but chart-pullback says any neighborhood of x₀ is uncountable.
-/

/-- If `f.toRiemannSphere` is constantly some `w : ℂ`, then `f.toFun` is
constantly `w`. -/
private lemma isConst_toFun_of_toRS_const_some
    (f : JacobianChallenge.MeromorphicNonzero X) {w : ℂ}
    (hRS : ∀ x, f.toRiemannSphere x = (OnePoint.some w : RiemannSphere)) :
    ∀ x, f.toFun x = w := by
  intro x
  have h_ne_infty : f.toRiemannSphere x ≠ (∞ : RiemannSphere) := by
    rw [hRS x]; exact OnePoint.coe_ne_infty w
  have h_nonneg : (0 : WithTop ℤ) ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x := by
    by_contra hneg
    rw [not_le] at hneg
    apply h_ne_infty
    exact JacobianChallenge.MeromorphicNonzero.toRiemannSphere_apply_of_neg f hneg
  have h_some : f.toRiemannSphere x =
      (OnePoint.some (f.toFun x) : RiemannSphere) :=
    JacobianChallenge.MeromorphicNonzero.toRiemannSphere_apply_of_nonneg
      f h_nonneg
  have h_eq : (OnePoint.some (f.toFun x) : RiemannSphere) =
      (OnePoint.some w : RiemannSphere) := by
    rw [← h_some, hRS x]
  exact OnePoint.coe_injective h_eq

/-- The all-pole case is impossible: there is no `f : MeromorphicNonzero X`
with `f.toRiemannSphere x = ∞` for every `x : X`, because the pole set
must be finite (R2) but `Set.univ` on a non-degenerate complex 1-manifold
is infinite. We dispatch via R2 + the existence of any non-pole point
*provided* one exists; in degenerate cases we fall back. The cleanest
local form: derive a contradiction with R2 by exhibiting a non-pole. -/
private lemma not_isConstantMap_toRS_infty
    (f : JacobianChallenge.MeromorphicNonzero X)
    (hRS : ∀ x, f.toRiemannSphere x = (∞ : RiemannSphere)) : False := by
  classical
  -- All points are poles.
  have h_poles : ∀ x, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < (0 : WithTop ℤ) := by
    intro x
    exact (JacobianChallenge.MeromorphicNonzero.toRiemannSphere_eq_infty_iff_neg
      f x).mp (hRS x)
  -- R2 (poles_finite): the pole set is finite.
  have hP_fin : {x : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x <
      (0 : WithTop ℤ)}.Finite :=
    JacobianChallenge.MMeromorphicOn.poles_finite (X := X)
      (𝓘(ℂ, ℂ)) f.toFun f.meromorphic f.nonvanishing_germ
  -- All of X is poles, so univ is finite.
  have h_univ_fin : (Set.univ : Set X).Finite :=
    hP_fin.subset (fun x _ => h_poles x)
  -- Hence X has a Finite instance.
  have hX_fin : Finite X := by
    rw [← Set.finite_univ_iff]
    exact h_univ_fin
  -- Pick a point x₀ from `ConnectedSpace.toNonempty`.
  have hX_nonempty : Nonempty X := inferInstance
  -- Now use the chart at x₀ to derive infinitude.
  -- The chart's source contains x₀; `chartAt ℂ x₀` maps it homeomorphically
  -- to an open subset of ℂ containing `(chartAt ℂ x₀) x₀`. We extract a
  -- ball ⊆ target ⊆ ℂ; preimaging through the chart gives infinitely many
  -- points in source ⊆ X. Contradicts `Finite X`.
  obtain ⟨x₀⟩ := hX_nonempty
  set e : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀
  have hx₀_src : x₀ ∈ e.source := mem_chart_source ℂ x₀
  have h_target_open : IsOpen e.target := e.open_target
  have h_ex0_target : e x₀ ∈ e.target := e.map_source hx₀_src
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp h_target_open _ h_ex0_target
  -- `Metric.ball (e x₀) r ⊆ e.target` and is infinite (open ball in ℂ).
  -- Inject ℕ into the ball via `n ↦ e x₀ + (((r/(n+2) : ℝ)) : ℂ)`. The values
  -- `(r/(n+2) : ℝ)` for `n : ℕ` are all distinct (strictly decreasing in n,
  -- positive), and bounded above by `r/2 < r`.
  have h_ball_inf : (Metric.ball (e x₀) r).Infinite := by
    let g : ℕ → ℂ := fun n => e x₀ + (((r / ((n : ℝ) + 2)) : ℝ) : ℂ)
    apply Set.infinite_of_injective_forall_mem (f := g)
    refine ⟨?_, ?_⟩
    · -- Injectivity.
      intro m n h_eq
      simp only [g, add_right_inj] at h_eq
      -- `((r/(m+2) : ℝ) : ℂ) = ((r/(n+2) : ℝ) : ℂ)` ⇒ real equality.
      have h_real : (r / ((m : ℝ) + 2)) = (r / ((n : ℝ) + 2)) := by
        exact_mod_cast h_eq
      have hr_ne : r ≠ 0 := ne_of_gt hr_pos
      have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
      have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
      rw [div_eq_div_iff hm2 hn2] at h_real
      have : ((m : ℝ) + 2) = ((n : ℝ) + 2) := by
        have := mul_left_cancel₀ hr_ne h_real.symm
        linarith
      have : (m : ℝ) = (n : ℝ) := by linarith
      exact_mod_cast this
    · intro n
      simp only [g]
      rw [Metric.mem_ball]
      have h_dist : dist (e x₀ + (((r / ((n : ℝ) + 2)) : ℝ) : ℂ)) (e x₀)
          = r / ((n : ℝ) + 2) := by
        rw [dist_eq_norm]
        ring_nf
        rw [Complex.norm_real]
        have h_pos : 0 < r / ((n : ℝ) + 2) := by positivity
        exact abs_of_pos h_pos
      rw [h_dist]
      -- Show `r / (n + 2) < r`. Since n+2 ≥ 2 > 1 and r > 0.
      have h_n_pos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have h_n_gt_one : (1 : ℝ) < (n : ℝ) + 2 := by
        have : (0 : ℝ) ≤ (n : ℝ) := by positivity
        linarith
      have h_lt : r / ((n : ℝ) + 2) < r := by
        rw [div_lt_iff₀ h_n_pos]
        nlinarith [hr_pos]
      exact h_lt
  -- Pull back to source via `e.symm`. `e.symm` is injective on `e.target`.
  have h_inj : Set.InjOn e.symm e.target := by
    intro a ha b hb hab
    have hsa : e (e.symm a) = a := e.right_inv ha
    have hsb : e (e.symm b) = b := e.right_inv hb
    rw [← hsa, ← hsb, hab]
  have h_inj_on_ball : Set.InjOn e.symm (Metric.ball (e x₀) r) :=
    h_inj.mono hr_sub
  have h_image_inf : (e.symm '' Metric.ball (e x₀) r).Infinite :=
    h_ball_inf.image h_inj_on_ball
  -- But X is `Finite`, so any subset of X is finite. Contradiction.
  exact h_image_inf (Set.toFinite _)

/-- If `f.toRiemannSphere` is constant, then `f.toFun` is constant. -/
private lemma isConst_toFun_of_toRS_const
    (f : JacobianChallenge.MeromorphicNonzero X)
    (h : JacobianChallenge.IsConstantMap f.toRiemannSphere) :
    JacobianChallenge.IsConstantMap f.toFun := by
  obtain ⟨c, hc⟩ := h
  cases c with
  | none => exact (not_isConstantMap_toRS_infty (X := X) f hc).elim
  | some w =>
    refine ⟨w, ?_⟩
    exact isConst_toFun_of_toRS_const_some (X := X) f (fun x => hc x)

/-! ## Identifying the R2-witness fibres with the toRS-fibres -/

private lemma toRS_eq_infty_iff_untop₀_lt
    (f : JacobianChallenge.MeromorphicNonzero X) (x : X) :
    f.toRiemannSphere x = (∞ : RiemannSphere) ↔
      (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ < (0 : ℤ) := by
  rw [JacobianChallenge.MeromorphicNonzero.toRiemannSphere_eq_infty_iff_neg
    f x]
  exact (JacobianChallenge.ResidueTheoremFromRsum.untop₀_lt_zero_iff_lt_zero
    (f.nonvanishing_germ x)).symm

private lemma toRS_eq_zero_iff_untop₀_pos
    (f : JacobianChallenge.MeromorphicNonzero X) (x : X) :
    f.toRiemannSphere x = (((0 : ℂ) : RiemannSphere)) ↔
      (0 : ℤ) < (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ := by
  constructor
  · intro hx_zero
    have hx_nonneg : (0 : WithTop ℤ) ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x :=
      JacobianChallenge.Manifold.nonneg_order_of_toRiemannSphere_eq_zero
        f hx_zero
    have hf_zero : f.toFun x = 0 :=
      JacobianChallenge.Manifold.toFun_eq_zero_of_toRiemannSphere_eq_zero
        f hx_zero
    have h_untop_nonneg : (0 : ℤ) ≤
        (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ :=
      (JacobianChallenge.ResidueTheoremFromRsum.untop₀_nonneg_iff_nonneg
        (f.nonvanishing_germ x)).mpr hx_nonneg
    refine lt_of_le_of_ne h_untop_nonneg ?_
    intro h_eq_zero
    -- `untop₀ = 0` and `nonvanishing_germ` ⇒ `ord = 0`.
    have h_ord_zero : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x = 0 := by
      have hne_top := f.nonvanishing_germ x
      have h_untop_zero : (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ = 0 :=
        h_eq_zero
      -- For finite WithTop, untop₀ = 0 ↔ the value is 0.
      cases h : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x with
      | top => exact absurd h hne_top
      | coe k =>
        rw [h] at h_untop_zero
        -- `((k : ℤ) : WithTop ℤ).untop₀ = k`, so `k = 0`.
        have hk : k = 0 := by simpa [WithTop.untop₀_coe] using h_untop_zero
        rw [h, hk]; rfl
    -- Chart pullback is analytic at z₀ (ord ≥ 0 + regular_continuousAt).
    set z₀ : ℂ := (chartAt ℂ x) x
    have h_g_mero : MeromorphicAt (f.toFun ∘ (chartAt ℂ x).symm) z₀ :=
      f.meromorphic x trivial
    have h_chart_continuousAt : ContinuousAt (chartAt ℂ x).symm z₀ := by
      have h_open : IsOpen (chartAt ℂ x).target := (chartAt ℂ x).open_target
      have h_in : z₀ ∈ (chartAt ℂ x).target :=
        (chartAt ℂ x).map_source (mem_chart_source ℂ x)
      have h_co : ContinuousOn (chartAt ℂ x).symm (chartAt ℂ x).target :=
        (chartAt ℂ x).continuousOn_invFun
      exact h_co.continuousAt (h_open.mem_nhds h_in)
    have h_pt : (chartAt ℂ x).symm z₀ = x :=
      (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
    have h_f_continuousAt : ContinuousAt f.toFun x :=
      f.regular_continuousAt x hx_nonneg
    have h_g_cont : ContinuousAt (f.toFun ∘ (chartAt ℂ x).symm) z₀ := by
      have : ContinuousAt f.toFun ((chartAt ℂ x).symm z₀) := by
        rw [h_pt]; exact h_f_continuousAt
      exact this.comp h_chart_continuousAt
    have h_g_an : AnalyticAt ℂ (f.toFun ∘ (chartAt ℂ x).symm) z₀ :=
      h_g_mero.analyticAt h_g_cont
    have h_mero_eq :
        meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm) z₀
          = (analyticOrderAt (f.toFun ∘ (chartAt ℂ x).symm) z₀).map
            (↑· : ℕ → ℤ) :=
      h_g_an.meromorphicOrderAt_eq
    have h_mmero_def :
        mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x =
          meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm) z₀ := rfl
    rw [h_mmero_def, h_mero_eq] at h_ord_zero
    -- analyticOrderAt = 0 ⇒ value ≠ 0.
    have h_an_ord_zero :
        analyticOrderAt (f.toFun ∘ (chartAt ℂ x).symm) z₀ = 0 := by
      cases h : analyticOrderAt (f.toFun ∘ (chartAt ℂ x).symm) z₀ with
      | top => rw [h] at h_ord_zero; simp at h_ord_zero
      | coe m =>
        rw [h] at h_ord_zero
        -- h_ord_zero : ((m : ℕ∞).map (↑· : ℕ → ℤ)) = 0
        -- Equivalently (after simp): m = 0.
        have hm : m = 0 := by
          have h_map : ((m : ℕ∞).map (↑· : ℕ → ℤ)) = ((m : ℤ) : WithTop ℤ) := by
            simp [ENat.map_coe]
          rw [h_map] at h_ord_zero
          have h_int : (m : ℤ) = 0 := by exact_mod_cast h_ord_zero
          exact_mod_cast h_int
        rw [h, hm]; rfl
    have h_g_ne : (f.toFun ∘ (chartAt ℂ x).symm) z₀ ≠ 0 :=
      (h_g_an.analyticOrderAt_eq_zero).mp h_an_ord_zero
    apply h_g_ne
    show f.toFun ((chartAt ℂ x).symm z₀) = 0
    rw [h_pt]; exact hf_zero
  · intro hx_pos
    have hx_nonneg' : (0 : WithTop ℤ) ≤
        mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x :=
      (JacobianChallenge.ResidueTheoremFromRsum.untop₀_nonneg_iff_nonneg
        (f.nonvanishing_germ x)).mp (le_of_lt hx_pos)
    have h_some : f.toRiemannSphere x =
        (OnePoint.some (f.toFun x) : RiemannSphere) :=
      JacobianChallenge.MeromorphicNonzero.toRiemannSphere_apply_of_nonneg
        f hx_nonneg'
    -- Show f.toFun x = 0 from positive order.
    set z₀ : ℂ := (chartAt ℂ x) x
    have h_g_mero : MeromorphicAt (f.toFun ∘ (chartAt ℂ x).symm) z₀ :=
      f.meromorphic x trivial
    have h_chart_continuousAt : ContinuousAt (chartAt ℂ x).symm z₀ := by
      have h_open : IsOpen (chartAt ℂ x).target := (chartAt ℂ x).open_target
      have h_in : z₀ ∈ (chartAt ℂ x).target :=
        (chartAt ℂ x).map_source (mem_chart_source ℂ x)
      have h_co : ContinuousOn (chartAt ℂ x).symm (chartAt ℂ x).target :=
        (chartAt ℂ x).continuousOn_invFun
      exact h_co.continuousAt (h_open.mem_nhds h_in)
    have h_pt : (chartAt ℂ x).symm z₀ = x :=
      (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
    have h_f_continuousAt : ContinuousAt f.toFun x :=
      f.regular_continuousAt x hx_nonneg'
    have h_g_cont : ContinuousAt (f.toFun ∘ (chartAt ℂ x).symm) z₀ := by
      have : ContinuousAt f.toFun ((chartAt ℂ x).symm z₀) := by
        rw [h_pt]; exact h_f_continuousAt
      exact this.comp h_chart_continuousAt
    have h_g_an : AnalyticAt ℂ (f.toFun ∘ (chartAt ℂ x).symm) z₀ :=
      h_g_mero.analyticAt h_g_cont
    have h_ord_pos : (0 : WithTop ℤ) <
        mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x :=
      (JacobianChallenge.ResidueTheoremFromRsum.untop₀_pos_iff_pos
        (f.nonvanishing_germ x)).mp hx_pos
    have h_mero_eq :
        meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm) z₀
          = (analyticOrderAt (f.toFun ∘ (chartAt ℂ x).symm) z₀).map
            (↑· : ℕ → ℤ) :=
      h_g_an.meromorphicOrderAt_eq
    have h_mmero_def :
        mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x =
          meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm) z₀ := rfl
    rw [h_mmero_def, h_mero_eq] at h_ord_pos
    have h_an_ne_zero :
        analyticOrderAt (f.toFun ∘ (chartAt ℂ x).symm) z₀ ≠ 0 := by
      intro h_eq
      rw [h_eq] at h_ord_pos
      simp at h_ord_pos
    have h_g_zero : (f.toFun ∘ (chartAt ℂ x).symm) z₀ = 0 := by
      by_contra h_ne
      exact h_an_ne_zero ((h_g_an.analyticOrderAt_eq_zero).mpr h_ne)
    have h_fx_zero : f.toFun x = 0 := by
      have h_g_eval : (f.toFun ∘ (chartAt ℂ x).symm) z₀ = f.toFun x := by
        show f.toFun ((chartAt ℂ x).symm z₀) = f.toFun x
        rw [h_pt]
      rw [← h_g_eval]; exact h_g_zero
    rw [h_some, h_fx_zero]

/-! ## Main theorem: R4 holds unconditionally -/

/-- **Unconditional discharge of `R4_fibreSum_balance_statement X`.** -/
theorem R4_fibreSum_balance_statement_holds :
    JacobianChallenge.ResidueTheorem.R4_fibreSum_balance_statement X := by
  intro f hZ hP
  classical
  by_cases hRS_const : JacobianChallenge.IsConstantMap f.toRiemannSphere
  · -- Constant case: f.toFun is constant; R4 trivially holds.
    have h_toFun_const : JacobianChallenge.IsConstantMap f.toFun :=
      isConst_toFun_of_toRS_const X f hRS_const
    exact R4_balance_of_const_toFun X f h_toFun_const hZ hP
  -- Non-constant case.
  have hf_RS : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f.toRiemannSphere :=
    f.toRiemannSphere_contMDiff
  -- Apply ramSumEqDeg at y = 0 and y = ∞.
  have h_at_zero := ramSumEqDeg X f hf_RS hRS_const (((0 : ℂ) : RiemannSphere))
  have h_at_infty := ramSumEqDeg X f hf_RS hRS_const (∞ : RiemannSphere)
  -- Both equal `degreeFiber f.toRiemannSphere hf_RS`. Equate.
  have h_zero_eq_pole_nat :
      (∑ x ∈ (fibresFinUncond X f hf_RS hRS_const
            (((0 : ℂ) : RiemannSphere))).toFinset,
            JacobianChallenge.Manifold.manifoldRamificationIndex
              f.toRiemannSphere x : ℕ)
        = (∑ x ∈ (fibresFinUncond X f hf_RS hRS_const
            (∞ : RiemannSphere)).toFinset,
            JacobianChallenge.Manifold.manifoldRamificationIndex
              f.toRiemannSphere x : ℕ) := by
    rw [h_at_zero, h_at_infty]
  -- Cast to ℤ.
  have h_zero_eq_pole_int :
      (∑ x ∈ (fibresFinUncond X f hf_RS hRS_const
            (((0 : ℂ) : RiemannSphere))).toFinset,
            (JacobianChallenge.Manifold.manifoldRamificationIndex
              f.toRiemannSphere x : ℤ))
        = (∑ x ∈ (fibresFinUncond X f hf_RS hRS_const
            (∞ : RiemannSphere)).toFinset,
            (JacobianChallenge.Manifold.manifoldRamificationIndex
              f.toRiemannSphere x : ℤ)) := by
    exact_mod_cast h_zero_eq_pole_nat
  -- Identify `(fibresFinUncond ...).toFinset` with `hZ.toFinset` / `hP.toFinset`.
  have h_zero_fibre_eq :
      (fibresFinUncond X f hf_RS hRS_const (((0 : ℂ) : RiemannSphere))).toFinset
        = hZ.toFinset := by
    apply Set.Finite.toFinset_inj.mpr
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact toRS_eq_zero_iff_untop₀_pos (X := X) f x
  have h_pole_fibre_eq :
      (fibresFinUncond X f hf_RS hRS_const (∞ : RiemannSphere)).toFinset
        = hP.toFinset := by
    apply Set.Finite.toFinset_inj.mpr
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact toRS_eq_infty_iff_untop₀_lt (X := X) f x
  rw [h_zero_fibre_eq, h_pole_fibre_eq] at h_zero_eq_pole_int
  -- Convert each side via R4a / R4b.
  have h_zero_side : (∑ x ∈ hZ.toFinset,
        (JacobianChallenge.Manifold.manifoldRamificationIndex
          f.toRiemannSphere x : ℤ))
      = ∑ x ∈ hZ.toFinset,
          (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx
    -- hx : 0 < ord.untop₀. So x is a zero (toRS x = some 0).
    have hx_zero : f.toRiemannSphere x = (((0 : ℂ) : RiemannSphere)) :=
      (toRS_eq_zero_iff_untop₀_pos (X := X) f x).mpr hx
    have h_R4a :=
      JacobianChallenge.Manifold.mmeromorphicOrderAt_eq_ramificationIndex_at_zero
        f x hx_zero
    have hx_nonneg : (0 : WithTop ℤ) ≤
        mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x :=
      JacobianChallenge.Manifold.nonneg_order_of_toRiemannSphere_eq_zero
        f hx_zero
    have h_untop_nonneg : (0 : ℤ) ≤
        (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ :=
      (JacobianChallenge.ResidueTheoremFromRsum.untop₀_nonneg_iff_nonneg
        (f.nonvanishing_germ x)).mpr hx_nonneg
    rw [h_R4a]
    -- ((untop₀).natAbs : ℤ) = untop₀ when untop₀ ≥ 0.
    show ((mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀.natAbs : ℤ)
        = (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀
    omega
  have h_pole_side : (∑ x ∈ hP.toFinset,
        (JacobianChallenge.Manifold.manifoldRamificationIndex
          f.toRiemannSphere x : ℤ))
      = - ∑ x ∈ hP.toFinset,
          (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx
    -- hx : ord.untop₀ < 0.
    have hx_pole : f.toRiemannSphere x = (∞ : RiemannSphere) :=
      (toRS_eq_infty_iff_untop₀_lt (X := X) f x).mpr hx
    have h_R4b :=
      JacobianChallenge.Manifold.mmeromorphicOrderAt_eq_ramificationIndex_at_pole
        f x hx_pole
    rw [h_R4b]
    -- natAbs of negative = -ord.untop₀.
    set k : ℤ := (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ with hk
    have hk_neg : k < 0 := hx
    have hk_nonpos : k ≤ 0 := le_of_lt hk_neg
    show (k.natAbs : ℤ) = -k
    omega
  rw [h_zero_side, h_pole_side] at h_zero_eq_pole_int
  linarith [h_zero_eq_pole_int]

/-! ## Headline residue theorem (unconditional) -/

/-- **The residue theorem on a compact connected Riemann surface
(unconditional).** -/
theorem residue_theorem_unconditional
    (f : JacobianChallenge.MeromorphicNonzero X) :
    (JacobianChallenge.principalDivisorMap f).degree = 0 :=
  JacobianChallenge.ResidueTheoremFromRsum.residue_theorem_of_R4
    X (R4_fibreSum_balance_statement_holds X) f

end R4FibreSumBalance

end JacobianChallenge

end

end
