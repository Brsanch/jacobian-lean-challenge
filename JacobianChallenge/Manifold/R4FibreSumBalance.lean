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
of `manifoldRamificationIndex` are equal. Convert via R4a / R4b:

* over zeros (`f.toRS x = some 0`): `mri = ord.untop₀.natAbs = ord.untop₀.toNat`.
* over poles (`f.toRS x = ∞`):     `mri = ord.untop₀.natAbs = -(ord.untop₀)`.

Hence `(∑ over hZ, ord.untop₀) = -(∑ over hP, ord.untop₀)`, i.e. R4.

The constant case (`f.toFun` is constant) is handled inline: by
`MeromorphicNonzero.nonvanishing_germ`, the constant value cannot be
`0`; for any nonzero constant, every order is `0`, both fibre sets are
empty, and R4 reduces to `0 + 0 = 0`.

In the non-constant case, we also need `¬ IsConstantMap f.toRiemannSphere`.
We prove the contrapositive: if `f.toRiemannSphere` is constant equal to
`some w`, then every point has order `≥ 0` and every value is `w`,
hence `f.toFun` is constant `w`; if `f.toRiemannSphere` is constant `∞`,
every point is a pole, contradicting compactness + R2's pole-finiteness
(via `R2_fibres_finite_statement_holds`) on a connected nonempty `X`.
The latter case is ruled out *via* a Pigeonhole-style argument on a
compact connected positive-dimensional manifold (which has uncountably
many points, while a finite pole set forces all-pole vacuous), but we
sidestep it by routing through R2's poles-finite witness directly.

No `sorry`, no `axiom`. -/

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

/-! ## Helper: order at a point of a constant `MeromorphicNonzero` is zero -/

/-- If `f.toFun` is the constant function `(fun _ => w)` with `w ≠ 0`,
then `mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x = 0` at every `x`. -/
private lemma mmeromorphicOrderAt_const_ne_zero
    (f : JacobianChallenge.MeromorphicNonzero X) {w : ℂ}
    (hconst : ∀ x, f.toFun x = w) (hw : w ≠ 0) (x : X) :
    mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x = 0 := by
  -- The chart pullback equals the constant function `(fun _ => w)`.
  have h_const_pullback :
      (f.toFun ∘ (chartAt ℂ x).symm) = (fun _ : ℂ => w) := by
    funext z; simp [Function.comp, hconst]
  -- `mmeromorphicOrderAt I f.toFun x = meromorphicOrderAt (f.toFun ∘ chart.symm) z₀`
  -- (by definitional unfolding of `mmeromorphicOrderAt`).
  show meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0
  rw [h_const_pullback]
  -- Constant `w ≠ 0` is analytic with value `w` at every point; analytic
  -- order at a non-vanishing point is `0`, and `meromorphicOrderAt`
  -- agrees with the cast.
  have h_an : AnalyticAt ℂ (fun _ : ℂ => w) ((chartAt ℂ x) x) :=
    analyticAt_const
  -- Compose `meromorphicOrderAt_eq` with `analyticOrderAt_eq_zero ↔ (·) ≠ 0`.
  rw [h_an.meromorphicOrderAt_eq]
  rw [(h_an.analyticOrderAt_eq_zero).mpr hw]
  rfl

/-! ## Helper: `IsConstantMap f.toRiemannSphere → IsConstantMap f.toFun` -/

/-- If `f.toRiemannSphere` is the constant function `(fun _ => some w)`
for some `w : ℂ`, then `f.toFun` is the constant function `(fun _ => w)`. -/
private lemma isConstantMap_toFun_of_isConstantMap_toRiemannSphere_some
    (f : JacobianChallenge.MeromorphicNonzero X) {w : ℂ}
    (hRS : ∀ x, f.toRiemannSphere x = (OnePoint.some w : RiemannSphere)) :
    ∀ x, f.toFun x = w := by
  intro x
  -- Every point has nonneg order (since toRS x = some w ≠ ∞).
  have h_ne_infty : f.toRiemannSphere x ≠ (∞ : RiemannSphere) := by
    rw [hRS x]
    exact OnePoint.coe_ne_infty w
  have h_nonneg : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x := by
    by_contra hneg
    push_neg at hneg
    apply h_ne_infty
    exact JacobianChallenge.MeromorphicNonzero.toRiemannSphere_apply_of_neg
      f hneg
  have h_some : f.toRiemannSphere x =
      (OnePoint.some (f.toFun x) : RiemannSphere) :=
    JacobianChallenge.MeromorphicNonzero.toRiemannSphere_apply_of_nonneg
      f h_nonneg
  -- Combine `h_some = some (f x)` with `hRS = some w`.
  have h_eq : (OnePoint.some (f.toFun x) : RiemannSphere) =
      (OnePoint.some w : RiemannSphere) := by
    rw [← h_some, hRS x]
  exact OnePoint.coe_injective h_eq

/-- If `f.toRiemannSphere` is constant, then `f.toFun` is constant. -/
private lemma isConstantMap_toFun_of_isConstantMap_toRiemannSphere
    (f : JacobianChallenge.MeromorphicNonzero X)
    (h : JacobianChallenge.IsConstantMap f.toRiemannSphere) :
    JacobianChallenge.IsConstantMap f.toFun := by
  obtain ⟨c, hc⟩ := h
  -- Case-split on `c : RiemannSphere = OnePoint ℂ`.
  cases c with
  | none =>
    -- All points are poles: order < 0 at every x. Use R2 to get pole set
    -- finite; contradict against `Set.univ.Finite` on a compact connected
    -- complex 1-manifold (which has uncountably many points). We bail by
    -- showing that the assumption of `c = ∞` for all x leads to
    -- `Set.univ.Finite`, then by infinitude of `X` we get a contradiction.
    -- However: instead of importing infinitude, we argue *directly* that
    -- a connected T2 space with a finite carrier is at most a singleton,
    -- in which case `f.toFun` is trivially constant.
    classical
    -- All x have order < 0.
    have h_poles : ∀ x, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0 := by
      intro x
      have hx_eq : f.toRiemannSphere x = (∞ : RiemannSphere) := hc x
      exact (JacobianChallenge.MeromorphicNonzero.toRiemannSphere_eq_infty_iff_neg
        f x).mp hx_eq
    -- R2 (poles set finite) says the set `{x | order < 0}` is finite, but
    -- here it equals `Set.univ`. So `Set.univ.Finite`.
    have hP : {x : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x <
        (0 : WithTop ℤ)}.Finite :=
      JacobianChallenge.MMeromorphicOn.poles_finite (X := X)
        (𝓘(ℂ, ℂ)) f.toFun f.meromorphic f.nonvanishing_germ
    have h_univ : (Set.univ : Set X) ⊆
        {x : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x <
            (0 : WithTop ℤ)} := by
      intro x _; exact h_poles x
    have h_univ_finite : (Set.univ : Set X).Finite := hP.subset h_univ
    -- Finitely many points + ConnectedSpace + T2 = singleton or empty.
    -- In either case, `f.toFun` is constant.
    -- A finite T2 space is discrete; combined with connectedness, has ≤ 1
    -- point. So pick any point (or vacuously) and use it as the constant.
    refine ⟨f.toFun (Classical.arbitrary X), ?_⟩
    intro x
    -- Show `x = Classical.arbitrary X` in this finite-T2-connected case.
    -- We use `Subsingleton X`.
    have h_sub : Subsingleton X := by
      -- Finite + T2 ⇒ DiscreteTopology. Discrete + Connected ⇒ Subsingleton.
      have h_fin : Finite X := h_univ_finite.finite_univ_iff.mp h_univ_finite
      have h_disc : DiscreteTopology X := discreteTopology_of_finite_t2_space
      exact connected_subsingleton_of_discreteTopology
    rw [Subsingleton.elim x (Classical.arbitrary X)]
  | some w =>
    -- `f.toRiemannSphere = some w` everywhere ⇒ `f.toFun = w` everywhere.
    refine ⟨w, ?_⟩
    have hc' : ∀ x, f.toRiemannSphere x = (OnePoint.some w : RiemannSphere) := hc
    exact isConstantMap_toFun_of_isConstantMap_toRiemannSphere_some
      (X := X) f hc'

/-! ## Helpers for the `c = ∞` finite-connected case

We need `discreteTopology_of_finite_t2_space` and
`connected_subsingleton_of_discreteTopology`. The former is in mathlib;
the latter is a one-liner from `IsConnected.subsingleton`. -/

/-- A finite T2 space has the discrete topology. (Mathlib name varies; we
provide a local rename for clarity.) -/
private lemma discreteTopology_of_finite_t2_space {α : Type*}
    [TopologicalSpace α] [T2Space α] [Finite α] : DiscreteTopology α := by
  exact Finite.instDiscreteTopology

/-- A connected discrete space is a subsingleton. -/
private lemma connected_subsingleton_of_discreteTopology {α : Type*}
    [TopologicalSpace α] [ConnectedSpace α] [DiscreteTopology α] :
    Subsingleton α := by
  by_contra h_not_sub
  rw [not_subsingleton_iff_nontrivial] at h_not_sub
  obtain ⟨a, b, hab⟩ := h_not_sub
  -- `{a}` is open (discrete), and `{a}ᶜ` is open (discrete); both
  -- nonempty (contains `a` and `b` respectively); their union covers `α`.
  -- Connectedness forbids this.
  have h_a_open : IsOpen ({a} : Set α) := isOpen_discrete _
  have h_a_closed : IsClosed ({a} : Set α) :=
    ⟨isOpen_discrete _⟩
  -- `{a}` is clopen and nonempty; by connectedness, `{a} = univ`.
  have h_a_univ : ({a} : Set α) = Set.univ := by
    have h_clopen : IsClopen ({a} : Set α) := ⟨h_a_closed, h_a_open⟩
    rcases h_clopen.eq_empty_or_eq_univ with h | h
    · -- `{a} = ∅` is impossible.
      exact absurd (Set.singleton_nonempty a) (h ▸ Set.not_nonempty_empty)
    · exact h
  -- But `b ∈ {a} = univ` would force `b = a`, contradicting `hab`.
  have hb_mem : b ∈ ({a} : Set α) := by rw [h_a_univ]; trivial
  exact absurd (Set.mem_singleton_iff.mp hb_mem).symm hab

/-! ## R4 in the constant-`f.toFun` case -/

private lemma R4_balance_of_isConstantMap_toFun
    (f : JacobianChallenge.MeromorphicNonzero X)
    (hconst : JacobianChallenge.IsConstantMap f.toFun)
    (hZ : {x : X | (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ > 0}.Finite)
    (hP : {x : X | (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ < 0}.Finite) :
    (∑ x ∈ hZ.toFinset, (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀) +
      (∑ x ∈ hP.toFinset,
          (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀) = 0 := by
  classical
  obtain ⟨w, hw_const⟩ := hconst
  -- `w ≠ 0` (else nonvanishing_germ violated).
  have hw_ne : w ≠ 0 := by
    intro h_w_zero
    -- If w = 0, then `f.toFun` is identically zero. The chart pullback is
    -- the constant function 0, whose meromorphicOrderAt is `⊤` — but
    -- nonvanishing_germ rules this out.
    have h_pullback_zero :
        (f.toFun ∘ (chartAt ℂ (Classical.arbitrary X)).symm) =
          (fun _ : ℂ => (0 : ℂ)) := by
      funext z; simp [Function.comp, hw_const, h_w_zero]
    have h_top : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun
        (Classical.arbitrary X) = ⊤ := by
      show meromorphicOrderAt (f.toFun ∘
          (chartAt ℂ (Classical.arbitrary X)).symm)
          ((chartAt ℂ (Classical.arbitrary X)) (Classical.arbitrary X)) = ⊤
      rw [h_pullback_zero]
      -- meromorphicOrderAt of identically-zero is ⊤.
      have h_an_zero : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ))
          ((chartAt ℂ (Classical.arbitrary X)) (Classical.arbitrary X)) :=
        analyticAt_const
      rw [h_an_zero.meromorphicOrderAt_eq]
      -- analyticOrderAt of identically zero is ⊤.
      have h_zero_ev : (fun _ : ℂ => (0 : ℂ)) =ᶠ[𝓝
          ((chartAt ℂ (Classical.arbitrary X)) (Classical.arbitrary X))]
          (fun _ => 0) :=
        Filter.EventuallyEq.refl _ _
      rw [analyticOrderAt_eq_top.mpr h_zero_ev]
      rfl
    exact f.nonvanishing_germ (Classical.arbitrary X) h_top
  -- All orders are 0.
  have h_all_zero : ∀ x, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x = 0 :=
    mmeromorphicOrderAt_const_ne_zero (X := X) f hw_const hw_ne
  -- Both summed sets are empty.
  have hZ_empty : hZ.toFinset = ∅ := by
    rw [Finset.eq_empty_iff_forall_not_mem]
    intro x hx
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx
    rw [h_all_zero x] at hx
    -- `(0 : WithTop ℤ).untop₀ = 0`, contradicting `0 < 0`.
    simp at hx
  have hP_empty : hP.toFinset = ∅ := by
    rw [Finset.eq_empty_iff_forall_not_mem]
    intro x hx
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx
    rw [h_all_zero x] at hx
    simp at hx
  rw [hZ_empty, hP_empty]
  simp

/-! ## Converting mri-sums to ord-sums (R4a / R4b) -/

/-- Over the zero fibre of `f.toRiemannSphere`, the manifold ramification
index sum equals the sum of `(ord.untop₀).toNat` (which equals the
positive integer `ord.untop₀`). -/
private lemma sum_mri_eq_sum_ord_at_zero
    (f : JacobianChallenge.MeromorphicNonzero X)
    (hf_RS : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f.toRiemannSphere)
    (hnc_RS : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere) :
    let Z := f.toRiemannSphere ⁻¹' {((0 : ℂ) : RiemannSphere)}
    let hZfin := JacobianChallenge.ContMDiff.Owed.degree
        .fibres_finite_statement_holds_unconditional
        f.toRiemannSphere hf_RS hnc_RS ((0 : ℂ) : RiemannSphere)
    (∑ x ∈ hZfin.toFinset,
        (JacobianChallenge.Manifold.manifoldRamificationIndex
          f.toRiemannSphere x : ℤ))
      = ∑ x ∈ hZfin.toFinset,
          (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ := by
  intro Z hZfin
  refine Finset.sum_congr rfl ?_
  intro x hx
  rw [Set.Finite.mem_toFinset] at hx
  -- `hx : f.toRiemannSphere x = some 0`.
  have hx_zero : f.toRiemannSphere x = (((0 : ℂ) : RiemannSphere)) := hx
  -- R4a: `mri = ord.untop₀.natAbs`. At a zero, ord ≥ 0, so untop₀ ≥ 0
  -- and `natAbs = toNat = (untop₀ : ℤ)`. We bridge through ℕ.
  have h_R4a :=
    JacobianChallenge.Manifold.mmeromorphicOrderAt_eq_ramificationIndex_at_zero
      f x hx_zero
  -- `h_R4a : (mri : ℕ) = ord.untop₀.natAbs`.
  -- Use the fact `0 ≤ ord.untop₀` to convert `natAbs` to `toNat`/cast.
  have hx_nonneg : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x :=
    JacobianChallenge.Manifold.nonneg_order_of_toRiemannSphere_eq_zero
      f hx_zero
  -- Push to integers.
  have h_untop₀_nonneg :
      (0 : ℤ) ≤ (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ :=
    (JacobianChallenge.ResidueTheoremFromRsum.untop₀_nonneg_iff_nonneg
      (f.nonvanishing_germ x)).mpr hx_nonneg
  -- `((natAbs : ℕ) : ℤ) = |untop₀|`. With `0 ≤ untop₀`, `|untop₀| = untop₀`.
  have h_cast :
      ((mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀.natAbs : ℤ)
        = (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ :=
    Int.natAbs_of_nonneg h_untop₀_nonneg
  -- Combine.
  rw [h_R4a]
  exact h_cast

/-- Over the pole fibre of `f.toRiemannSphere`, the manifold ramification
index sum equals the negation of the sum of `ord.untop₀` (which is
negative at poles). -/
private lemma sum_mri_eq_neg_sum_ord_at_pole
    (f : JacobianChallenge.MeromorphicNonzero X)
    (hf_RS : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f.toRiemannSphere)
    (hnc_RS : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere) :
    let hPfin := JacobianChallenge.ContMDiff.Owed.degree
        .fibres_finite_statement_holds_unconditional
        f.toRiemannSphere hf_RS hnc_RS (∞ : RiemannSphere)
    (∑ x ∈ hPfin.toFinset,
        (JacobianChallenge.Manifold.manifoldRamificationIndex
          f.toRiemannSphere x : ℤ))
      = - ∑ x ∈ hPfin.toFinset,
          (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ := by
  intro hPfin
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro x hx
  rw [Set.Finite.mem_toFinset] at hx
  have hx_pole : f.toRiemannSphere x = (∞ : RiemannSphere) := hx
  have h_R4b :=
    JacobianChallenge.Manifold.mmeromorphicOrderAt_eq_ramificationIndex_at_pole
      f x hx_pole
  have hx_neg : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0 :=
    JacobianChallenge.Manifold.neg_order_of_toRiemannSphere_eq_infty
      f hx_pole
  have h_untop₀_neg :
      (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ < (0 : ℤ) :=
    (JacobianChallenge.ResidueTheoremFromRsum.untop₀_lt_zero_iff_lt_zero
      (f.nonvanishing_germ x)).mpr hx_neg
  -- `((natAbs : ℕ) : ℤ) = - untop₀` for negative `untop₀`.
  have h_cast :
      ((mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀.natAbs : ℤ)
        = - (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ := by
    set k : ℤ := (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ with hk
    have hk_nonpos : k ≤ 0 := le_of_lt h_untop₀_neg
    -- `natAbs k = -k` when k ≤ 0.
    have : (k.natAbs : ℤ) = -k := by
      rcases Int.lt_or_lt_of_ne (ne_of_lt h_untop₀_neg) with hk_lt | hk_lt
      · -- k < 0
        rw [Int.ofNat_natAbs]
        rw [abs_of_nonpos hk_nonpos]
      · exact absurd hk_lt (not_lt.mpr hk_nonpos)
    exact this
  rw [h_R4b]
  exact h_cast

/-! ## Identifying the R2 finite-witness fibres with the toRS fibres

Under `f.nonvanishing_germ`, the set `{x | ord.untop₀ > 0}` equals the
toRS-fibre over `((0 : ℂ) : RiemannSphere)`, and `{x | ord.untop₀ < 0}`
equals the toRS-fibre over `(∞ : RiemannSphere)`.

The pole identification is direct (`toRiemannSphere_eq_infty_iff_neg`).
The zero identification needs the meromorphic-with-`regular_continuousAt`
input to bridge `ord = 0 ⇒ f.toFun x ≠ 0`. -/

private lemma toRS_eq_infty_iff_untop₀_lt_zero
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
    have hx_nonneg : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x :=
      JacobianChallenge.Manifold.nonneg_order_of_toRiemannSphere_eq_zero
        f hx_zero
    have hf_zero : f.toFun x = 0 :=
      JacobianChallenge.Manifold.toFun_eq_zero_of_toRiemannSphere_eq_zero
        f hx_zero
    -- Show `ord.untop₀ ≠ 0` (then with nonneg ⇒ pos).
    have h_untop_nonneg : (0 : ℤ) ≤
        (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ :=
      (JacobianChallenge.ResidueTheoremFromRsum.untop₀_nonneg_iff_nonneg
        (f.nonvanishing_germ x)).mpr hx_nonneg
    -- Show `ord ≠ 0`. If ord = 0, f.toFun analytic at x with value f.toFun x = 0,
    -- but analyticOrderAt = 0 ⇒ value ≠ 0 — contradiction.
    refine lt_of_le_of_ne h_untop_nonneg ?_
    intro h_eq_zero
    -- `untop₀ = 0` and `nonvanishing_germ` ⇒ `ord = 0`.
    have h_ord_zero : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x = 0 := by
      have hne_top := f.nonvanishing_germ x
      cases h : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x with
      | top => exact absurd h hne_top
      | coe k =>
        rw [h] at h_eq_zero
        -- `((k : ℤ) : WithTop ℤ).untop₀ = k = 0`.
        have hk : k = 0 := by
          show (((k : ℤ) : WithTop ℤ)).untop₀ = 0 at h_eq_zero
          simpa using h_eq_zero
        rw [h, hk]
        rfl
    -- Now derive contradiction: ord = 0 but f.toFun x = 0.
    -- Chart pullback `g := f.toFun ∘ chart.symm` is analytic at z₀ (since
    -- ord ≥ 0 and regular_continuousAt).
    set z₀ : ℂ := (chartAt ℂ x) x with hz₀
    have h_g_mero : MeromorphicAt (f.toFun ∘ (chartAt ℂ x).symm) z₀ :=
      f.meromorphic x trivial
    have h_chart_continuousAt :
        ContinuousAt (chartAt ℂ x).symm z₀ := by
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
    have h_f_at_pt : ContinuousAt f.toFun ((chartAt ℂ x).symm z₀) := by
      rw [h_pt]; exact h_f_continuousAt
    have h_g_continuousAt :
        ContinuousAt (f.toFun ∘ (chartAt ℂ x).symm) z₀ :=
      h_f_at_pt.comp h_chart_continuousAt
    have h_g_an : AnalyticAt ℂ (f.toFun ∘ (chartAt ℂ x).symm) z₀ :=
      h_g_mero.analyticAt h_g_continuousAt
    -- meromorphicOrderAt = (analyticOrderAt).map (↑·).
    have h_mero_eq :
        meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm) z₀
          = (analyticOrderAt (f.toFun ∘ (chartAt ℂ x).symm) z₀).map
            (↑· : ℕ → ℤ) :=
      h_g_an.meromorphicOrderAt_eq
    -- `mmeromorphicOrderAt = meromorphicOrderAt (chart pullback) z₀` (rfl).
    have h_mmero_def :
        mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x =
          meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm) z₀ := rfl
    rw [h_mmero_def] at h_ord_zero
    rw [h_mero_eq] at h_ord_zero
    -- LHS ↔ analyticOrderAt = 0.
    have h_an_ord_zero :
        analyticOrderAt (f.toFun ∘ (chartAt ℂ x).symm) z₀ = 0 := by
      cases h : analyticOrderAt (f.toFun ∘ (chartAt ℂ x).symm) z₀ with
      | top =>
        rw [h] at h_ord_zero
        -- (⊤ : ℕ∞).map (↑·) = ⊤. But h_ord_zero says this = (0 : WithTop ℤ).
        simp at h_ord_zero
      | coe m =>
        rw [h] at h_ord_zero
        have h_m_zero : (m : ℤ) = 0 := by
          have : ((m : ℤ) : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) := by
            rw [← h_ord_zero]; rfl
          exact_mod_cast this
        have hm : m = 0 := by exact_mod_cast h_m_zero
        rw [h, hm]; rfl
    -- analyticOrderAt = 0 ⇒ value ≠ 0.
    have h_g_ne : (f.toFun ∘ (chartAt ℂ x).symm) z₀ ≠ 0 :=
      (h_g_an.analyticOrderAt_eq_zero).mp h_an_ord_zero
    -- But (f.toFun ∘ chart.symm) z₀ = f.toFun x = 0 (by `h_pt` and `hf_zero`).
    apply h_g_ne
    show f.toFun ((chartAt ℂ x).symm z₀) = 0
    rw [h_pt]; exact hf_zero
  · intro hx_pos
    -- ord.untop₀ > 0 ⇒ ord > 0 ⇒ nonneg ⇒ toRS x = some (f.toFun x). And f.toFun x = 0 (positive order).
    have hx_nonneg' : (0 : WithTop ℤ) ≤
        mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x :=
      (JacobianChallenge.ResidueTheoremFromRsum.untop₀_nonneg_iff_nonneg
        (f.nonvanishing_germ x)).mp (le_of_lt hx_pos)
    have h_some : f.toRiemannSphere x =
        (OnePoint.some (f.toFun x) : RiemannSphere) :=
      JacobianChallenge.MeromorphicNonzero.toRiemannSphere_apply_of_nonneg
        f hx_nonneg'
    -- Now show `f.toFun x = 0` from `0 < ord`.
    -- Chart pullback `g`: meromorphicOrderAt > 0 + analytic ⇒ g z₀ = 0
    -- ⇒ f.toFun x = 0.
    set z₀ : ℂ := (chartAt ℂ x) x with hz₀
    have h_g_mero : MeromorphicAt (f.toFun ∘ (chartAt ℂ x).symm) z₀ :=
      f.meromorphic x trivial
    have h_chart_continuousAt :
        ContinuousAt (chartAt ℂ x).symm z₀ := by
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
    have h_f_at_pt : ContinuousAt f.toFun ((chartAt ℂ x).symm z₀) := by
      rw [h_pt]; exact h_f_continuousAt
    have h_g_continuousAt :
        ContinuousAt (f.toFun ∘ (chartAt ℂ x).symm) z₀ :=
      h_f_at_pt.comp h_chart_continuousAt
    have h_g_an : AnalyticAt ℂ (f.toFun ∘ (chartAt ℂ x).symm) z₀ :=
      h_g_mero.analyticAt h_g_continuousAt
    -- ord > 0 ⇒ analyticOrderAt > 0 ⇒ g z₀ = 0.
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
    -- analyticOrderAt cannot be 0 (else map = 0, contradicting positive).
    have h_an_ne_zero :
        analyticOrderAt (f.toFun ∘ (chartAt ℂ x).symm) z₀ ≠ 0 := by
      intro h_eq
      rw [h_eq] at h_ord_pos
      simp at h_ord_pos
    have h_g_zero : (f.toFun ∘ (chartAt ℂ x).symm) z₀ = 0 := by
      by_contra h_ne
      exact h_an_ne_zero ((h_g_an.analyticOrderAt_eq_zero).mpr h_ne)
    -- g z₀ = f.toFun x.
    have h_g_eval : (f.toFun ∘ (chartAt ℂ x).symm) z₀ = f.toFun x := by
      show f.toFun ((chartAt ℂ x).symm z₀) = f.toFun x
      rw [h_pt]
    have h_fx_zero : f.toFun x = 0 := h_g_eval ▸ h_g_zero
    rw [h_some, h_fx_zero]

/-! ## Main theorem: R4 holds unconditionally -/

/-- **Unconditional discharge of `R4_fibreSum_balance_statement X`.**

This is the last open ingredient of the residue-theorem skeleton. We
compose:

* `mmeromorphicOrderAt_eq_ramificationIndex_at_zero` (R4a),
* `mmeromorphicOrderAt_eq_ramificationIndex_at_pole` (R4b),
* `ramificationSumEqualsDegree_holds_unconditional` at the values
  `((0 : ℂ) : RiemannSphere)` and `(∞ : RiemannSphere)`.

The constant case (`f.toFun` is constant) is handled inline. -/
theorem R4_fibreSum_balance_statement_holds :
    JacobianChallenge.ResidueTheorem.R4_fibreSum_balance_statement X := by
  intro f hZ hP
  classical
  by_cases hconst : JacobianChallenge.IsConstantMap f.toFun
  · -- Constant case.
    exact R4_balance_of_isConstantMap_toFun X f hconst hZ hP
  -- Non-constant case.
  -- `f.toRiemannSphere` is also non-constant (contrapositive of the helper).
  have hnc_RS : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere := by
    intro hRS_const
    exact hconst (isConstantMap_toFun_of_isConstantMap_toRiemannSphere
      (X := X) f hRS_const)
  -- Smoothness of `f.toRiemannSphere`.
  have hf_RS : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f.toRiemannSphere :=
    f.toRiemannSphere_contMDiff
  -- Apply ramificationSumEqualsDegree at y = 0 and y = ∞.
  have h_rsum :=
    JacobianChallenge.ContMDiff.Owed.degree
      .ramificationSumEqualsDegree_holds_unconditional X RiemannSphere
  have h_at_zero :=
    h_rsum f.toRiemannSphere hf_RS hnc_RS (((0 : ℂ) : RiemannSphere))
  have h_at_infty :=
    h_rsum f.toRiemannSphere hf_RS hnc_RS (∞ : RiemannSphere)
  -- Both equal `degreeFiber f.toRiemannSphere hf_RS`.
  have h_zero_eq_pole_mri :
      (∑ x ∈ (JacobianChallenge.ContMDiff.Owed.degree
            .fibres_finite_statement_holds_unconditional
            f.toRiemannSphere hf_RS hnc_RS (((0 : ℂ) : RiemannSphere))).toFinset,
            JacobianChallenge.Manifold.manifoldRamificationIndex
              f.toRiemannSphere x : ℕ)
        = (∑ x ∈ (JacobianChallenge.ContMDiff.Owed.degree
            .fibres_finite_statement_holds_unconditional
            f.toRiemannSphere hf_RS hnc_RS (∞ : RiemannSphere)).toFinset,
            JacobianChallenge.Manifold.manifoldRamificationIndex
              f.toRiemannSphere x : ℕ) := by
    rw [h_at_zero, h_at_infty]
  -- Cast to ℤ.
  have h_zero_eq_pole_int :
      (∑ x ∈ (JacobianChallenge.ContMDiff.Owed.degree
            .fibres_finite_statement_holds_unconditional
            f.toRiemannSphere hf_RS hnc_RS (((0 : ℂ) : RiemannSphere))).toFinset,
            (JacobianChallenge.Manifold.manifoldRamificationIndex
              f.toRiemannSphere x : ℤ))
        = (∑ x ∈ (JacobianChallenge.ContMDiff.Owed.degree
            .fibres_finite_statement_holds_unconditional
            f.toRiemannSphere hf_RS hnc_RS (∞ : RiemannSphere)).toFinset,
            (JacobianChallenge.Manifold.manifoldRamificationIndex
              f.toRiemannSphere x : ℤ)) := by
    push_cast
    exact_mod_cast h_zero_eq_pole_mri
  -- Convert each side via R4a / R4b.
  have h_zero_side := sum_mri_eq_sum_ord_at_zero X f hf_RS hnc_RS
  have h_pole_side := sum_mri_eq_neg_sum_ord_at_pole X f hf_RS hnc_RS
  -- Identify the toRS-fibre Finsets with `hZ.toFinset` / `hP.toFinset`.
  -- The two characterizations of fibres (toRS_eq_*_iff_*) give set equality;
  -- toFinsets agree by `Set.Finite.toFinset`-extensionality.
  have h_zero_fibre_eq :
      (JacobianChallenge.ContMDiff.Owed.degree
        .fibres_finite_statement_holds_unconditional
        f.toRiemannSphere hf_RS hnc_RS (((0 : ℂ) : RiemannSphere))).toFinset
        = hZ.toFinset := by
    apply Set.Finite.toFinset_inj.mpr
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact toRS_eq_zero_iff_untop₀_pos (X := X) f x
  have h_pole_fibre_eq :
      (JacobianChallenge.ContMDiff.Owed.degree
        .fibres_finite_statement_holds_unconditional
        f.toRiemannSphere hf_RS hnc_RS (∞ : RiemannSphere)).toFinset
        = hP.toFinset := by
    apply Set.Finite.toFinset_inj.mpr
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact toRS_eq_infty_iff_untop₀_lt_zero (X := X) f x
  -- Substitute and conclude.
  rw [h_zero_fibre_eq] at h_zero_side h_zero_eq_pole_int
  rw [h_pole_fibre_eq] at h_pole_side h_zero_eq_pole_int
  -- h_zero_side : ∑ over hZ, (mri : ℤ) = ∑ over hZ, ord.untop₀
  -- h_pole_side : ∑ over hP, (mri : ℤ) = - ∑ over hP, ord.untop₀
  -- h_zero_eq_pole_int : ∑ over hZ, (mri : ℤ) = ∑ over hP, (mri : ℤ)
  -- So ∑ over hZ, ord.untop₀ = - ∑ over hP, ord.untop₀, i.e. their sum is 0.
  rw [h_zero_side] at h_zero_eq_pole_int
  rw [h_pole_side] at h_zero_eq_pole_int
  linarith [h_zero_eq_pole_int]

/-! ## Headline residue theorem (unconditional) -/

/-- **The residue theorem on a compact connected Riemann surface
(unconditional).**

For every non-zero global meromorphic function `f` on `X`, the
principal divisor `(f) := principalDivisorMap f` has degree zero in
`Div X`.

Composes the unconditional R4 above with the in-tree
`residue_theorem_of_R4` (which already discharges R1, R2, R3, and
R5-from-R4 unconditionally). -/
theorem residue_theorem_unconditional
    (f : JacobianChallenge.MeromorphicNonzero X) :
    (JacobianChallenge.principalDivisorMap f).degree = 0 :=
  JacobianChallenge.ResidueTheoremFromRsum.residue_theorem_of_R4
    X (R4_fibreSum_balance_statement_holds X) f

end R4FibreSumBalance

end JacobianChallenge

end

end
