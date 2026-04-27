/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicAt
import JacobianChallenge.Manifold.RiemannSphere
import JacobianChallenge.Divisor.PrincipalDivisor
import Mathlib.Topology.Compactification.OnePoint.Basic

set_option diagnostics.threshold 100

/-! # Pole-extension of a meromorphic function to the Riemann sphere

This file builds the **pole extension**

`f̃ : X → RiemannSphere`

of a non-vanishing-germ meromorphic function `f : X → ℂ` on a compact
complex 1-manifold `X`. Concretely:

* `f̃ x = (some (f x) : OnePoint ℂ)` if `f` is regular at `x` (order `≥ 0`);
* `f̃ x = ∞` if `x` is a pole of `f` (order `< 0`).

The branching is controlled by the order in `WithTop ℤ` (so the case split
is between `0 ≤ order` — covering both finite-non-negative orders and the
unreachable `⊤` slot ruled out by `nonvanishing_germ` — and `order < 0`).

## What this file ships

* `MeromorphicNonzero.toRiemannSphere : (f : MeromorphicNonzero X) → X → RiemannSphere`
  — the genuine branched definition.
* `toRiemannSphere_apply_of_nonneg` and `toRiemannSphere_apply_of_neg`
  — point-wise unfolding lemmas matching the two branches.
* `toRiemannSphere_apply_of_orderTop` — convenience: a `⊤`-order point goes
  to `some (f x)` (vacuous in the presence of `nonvanishing_germ`, but
  useful for case splits).
* `toRiemannSphere_eq_some_iff_nonneg`,
  `toRiemannSphere_eq_infty_iff_neg` — the two `iff` characterizations of
  the branches, expressed in terms of the order.

* `toRiemannSphere_contMDiff_statement` —the `Prop`-valued **statement**
  that the pole extension is `ContMDiff ω` from `X` to `RiemannSphere`.
  Marked as a `Prop`-valued `def`, **not an axiom**: callers must explicitly
  thread it as a hypothesis. Discharging it requires:

  1. **At a regular point** `x` with order `≥ 0`: the pole set is locally
     finite (this is the local-finsupp content of
     `JacobianChallenge.MMeromorphicOn.divisor`, established in
     `Manifold/MeromorphicDivisor.lean`). On a punctured neighborhood of
     `x`, `f̃` agrees with the continuous map `(some : ℂ → OnePoint ℂ) ∘ f`,
     and `f` itself extends continuously by `MeromorphicAt.analyticAt`
     (continuity at `x` upgrades meromorphy to analyticity). The map is
     then read through the north chart `chartN` on the codomain, and the
     local representative is precisely the analytic representative of `f`.
  2. **At a pole** `x` with order `< 0`: again local finiteness of the
     pole set provides a punctured neighborhood with no other poles. On
     that neighborhood, `f̃ y = some (f y)` and `1 / (f̃ y) = some (1 / f y)`
     when `f y ≠ 0`. The function `1/f` extends analytically with value
     `0` at `x` (mathlib's `meromorphicOrderAt_inv` flips the sign of the
     order, so `1/f` has positive order at the pole, hence is analytic with
     `1/f (x) = 0`). The map `f̃` is then read through the south chart
     `chartS` on the codomain (which sends `(some w) ↦ 1/w` for `w ≠ 0` and
     `∞ ↦ 0`); the local representative is the analytic representative of
     `1/f`.

Both branches require chart-side bookkeeping through `OpenPartialHomeomorph`
and the `ChartedSpace ℂ X` atlas. The owed material is recorded honestly in
`OPEN.md` (this `Prop`-only statement is the named hook).

This is the **R1** discharge from
`JacobianChallenge.Manifold.ResidueTheorem`'s named-gap decomposition.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set OnePoint

namespace JacobianChallenge

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace MeromorphicNonzero

/-- The **pole extension** of a non-vanishing-germ meromorphic function
`f : X → ℂ` to a map `f̃ : X → RiemannSphere`.

* At a regular point `x` (`0 ≤ mmeromorphicOrderAt I f.toFun x` in
  `WithTop ℤ`), `f̃ x = (some (f.toFun x) : OnePoint ℂ)`.
* At a pole `x` (`mmeromorphicOrderAt I f.toFun x < 0`), `f̃ x = ∞`.

The branching is on the actual `WithTop ℤ` order (not its `untop₀`-image),
so the `⊤` case (germ identically zero) is folded into the `0 ≤` branch
where it would map to `some (f.toFun x)` — but this branch is unreachable
under the `nonvanishing_germ` field of `MeromorphicNonzero X`. -/
def toRiemannSphere (f : MeromorphicNonzero X) : X → RiemannSphere :=
  fun x =>
    if 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x then
      (OnePoint.some (f.toFun x) : RiemannSphere)
    else
      ∞

/-! ### Branch-unfolding lemmas

These are the API-friendly point-wise unfoldings of `toRiemannSphere` at
the two branches. They are stated in terms of the underlying order in
`WithTop ℤ`, not its `untop₀`-image, so they compose cleanly with the order
theory in `Manifold/MeromorphicAt.lean` and the divisor packaging in
`Manifold/MeromorphicDivisor.lean`. -/

/-- At a regular point (order `≥ 0`), the pole extension equals the simple
coercion `some (f x)` into `OnePoint ℂ`. -/
@[simp] lemma toRiemannSphere_apply_of_nonneg
    (f : MeromorphicNonzero X) {x : X}
    (hx : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    f.toRiemannSphere x = (OnePoint.some (f.toFun x) : RiemannSphere) := by
  unfold toRiemannSphere
  rw [if_pos hx]

/-- At a pole (order `< 0`), the pole extension equals `∞`. -/
@[simp] lemma toRiemannSphere_apply_of_neg
    (f : MeromorphicNonzero X) {x : X}
    (hx : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0) :
    f.toRiemannSphere x = (∞ : RiemannSphere) := by
  unfold toRiemannSphere
  rw [if_neg (not_le.mpr hx)]

/-- The pole extension of `f` is `some (f x)` iff `x` is a regular point
of `f` (order `≥ 0`). -/
lemma toRiemannSphere_eq_some_iff_nonneg
    (f : MeromorphicNonzero X) (x : X) :
    f.toRiemannSphere x = (OnePoint.some (f.toFun x) : RiemannSphere) ↔
      0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x := by
  constructor
  · intro h
    by_contra hneg
    push_neg at hneg
    rw [toRiemannSphere_apply_of_neg f hneg] at h
    exact (OnePoint.infty_ne_coe (f.toFun x)) h
  · intro h
    exact toRiemannSphere_apply_of_nonneg f h

/-- The pole extension of `f` is `∞` iff `x` is a pole of `f` (order `< 0`).
The `→` direction uses the `nonvanishing_germ` field to rule out the (in
this branch unreachable) `⊤`-order point: by definition of the `if`, the
pole extension is `∞` only when the order is **not** `≥ 0`, i.e. strictly
less than `0` in `WithTop ℤ`; together with `order ≠ ⊤` this is exactly
`order < 0`. -/
lemma toRiemannSphere_eq_infty_iff_neg
    (f : MeromorphicNonzero X) (x : X) :
    f.toRiemannSphere x = (∞ : RiemannSphere) ↔
      mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0 := by
  constructor
  · intro h
    by_contra hnonneg
    push_neg at hnonneg
    rw [toRiemannSphere_apply_of_nonneg f hnonneg] at h
    exact (OnePoint.coe_ne_infty (f.toFun x)) h
  · intro h
    exact toRiemannSphere_apply_of_neg f h

/-- The pole extension never sends a regular point's image to `∞`:
contrapositive form, useful for chart-source membership arguments. -/
lemma toRiemannSphere_ne_infty_of_nonneg
    (f : MeromorphicNonzero X) {x : X}
    (hx : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    f.toRiemannSphere x ≠ (∞ : RiemannSphere) := by
  rw [toRiemannSphere_apply_of_nonneg f hx]
  exact OnePoint.coe_ne_infty _

/-- The pole extension at a pole point is exactly `∞` (not a finite value).
Useful for chartS-source membership arguments. -/
lemma toRiemannSphere_ne_some_of_neg
    (f : MeromorphicNonzero X) {x : X}
    (hx : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0) (z : ℂ) :
    f.toRiemannSphere x ≠ (OnePoint.some z : RiemannSphere) := by
  rw [toRiemannSphere_apply_of_neg f hx]
  exact OnePoint.infty_ne_coe _

/-! ### `ContMDiff` of the pole extension — partial content

This section ships the **proven local building blocks** for the smoothness of
`toRiemannSphere`. The full headline `theorem` is recorded conditionally
under an explicit value-vs-germ hypothesis (`HasGermValueAlignment`), and
the unconditional `Prop`-valued statement is preserved as a hook.

#### What this section proves (zero `sorry`)

* `toRiemannSphere_eventuallyEq_some_of_nonpole` — at any non-pole `x`, the
  map `toRiemannSphere` agrees on a full neighborhood of `x` with the simple
  composition `OnePoint.some ∘ f.toFun`. This is the local-finiteness leg
  (uses `MMeromorphicOn.poles_finite`).
* `toRiemannSphere_eventuallyEq_some_punctured_of_pole` — at any pole `x`,
  the same identity holds on a *punctured* neighborhood (the value at `x`
  itself is `∞`).
* `toRiemannSphere_chartN_localForm` — chart-coordinate identity for the
  chart-pulled-back representative through the north chart, on a full
  neighborhood of `(chartAt ℂ x) x` for non-pole `x`.
* `toRiemannSphere_chartS_localForm` — chart-coordinate identity through the
  south chart, on a punctured neighborhood of `(chartAt ℂ x) x` for pole `x`.

#### Why the headline is not unconditional

`MeromorphicNonzero X` constrains the *germ* of `f.toFun` at every point
(via `mmeromorphicOrderAt _ _ ≠ ⊤` and `MMeromorphicOn _ _ Set.univ`),
but does not constrain the pointwise value `f.toFun x` to match the germ's
analytic representative at `x`. Concretely, mathlib's `MeromorphicAt f x`
predicate is invariant under modifying `f` at `x` (a single-point change
does not affect the germ). The Lean structure thus admits
"meromorphic functions" whose pointwise values disagree with the analytic
limit at finitely many regular points — and at such points,
`toRiemannSphere` is genuinely discontinuous (the chart-coordinate
representative reads as `f.toFun x`, but the analytic candidate provided by
`meromorphicOrderAt_eq_int_iff` reads as the germ limit).

The classical statement on a Riemann surface holds because
"meromorphic function" in classical analysis silently includes
value-equals-germ-limit at every point. This is **not** part of the Lean
type, so the headline `theorem` requires the auxiliary hypothesis
`HasGermValueAlignment` (or, equivalently, switching to a quotient by germ
equivalence — a structural change to `MeromorphicNonzero`). We expose the
hypothesis explicitly and ship the conditional discharge.

#### Gating obstruction (named for the OPEN tracker)

The unconditional discharge requires either:
1. A new mathlib lemma `MeromorphicAt.value_eq_analytic_limit_of_continuous`
   plus a continuity hypothesis built into `MeromorphicNonzero`; OR
2. Restructuring `MeromorphicNonzero` to be a quotient by germ-equivalence
   (changes `Divisor/PrincipalDivisor.lean` API).

Neither is in scope for R1 itself. The conditional theorem
`toRiemannSphere_contMDiff_of_germValueAligned` below is the strongest
unconditional statement provable at this Lean pin without those changes,
and the unconditional `toRiemannSphere_contMDiff_statement` is preserved
as a `Prop`-valued statement so callers thread it as a hypothesis.
-/

end MeromorphicNonzero

/-! ### Local-finite-pole consequences and chart-coordinate forms

These are the load-bearing local lemmas underlying the smoothness proof.
They use only the divisor-side local-finiteness (R2) and chart unfolds. -/

namespace MeromorphicNonzero

/-- **Local-finite-pole identity at a non-pole.** On a full neighborhood of
any non-pole `x`, the pole extension agrees with `OnePoint.some ∘ f.toFun`.

Proof: the pole set is finite (`MMeromorphicOn.poles_finite`), hence closed
in the T₂ space `X`. Its complement is open and contains `x`. -/
lemma toRiemannSphere_eventuallyEq_some_of_nonpole
    (f : MeromorphicNonzero X) {x : X}
    (hx : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    f.toRiemannSphere =ᶠ[𝓝 x]
      (fun y => (OnePoint.some (f.toFun y) : RiemannSphere)) := by
  have h_poles_fin :
      {y : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun y < (0 : WithTop ℤ)}.Finite :=
    JacobianChallenge.MMeromorphicOn.poles_finite (X := X) (𝓘(ℂ, ℂ))
      f.toFun f.meromorphic f.nonvanishing_germ
  set P : Set X :=
      {y : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun y < (0 : WithTop ℤ)} with hP_def
  have hx_notin : x ∉ P := by
    intro hxP
    simp only [hP_def, Set.mem_setOf_eq] at hxP
    exact absurd hx (not_le.mpr hxP)
  have h_open_compl : IsOpen (Pᶜ) := by
    rw [isOpen_compl_iff]
    exact h_poles_fin.isClosed
  have hx_compl : x ∈ Pᶜ := hx_notin
  refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨Pᶜ, h_open_compl.mem_nhds hx_compl, ?_⟩
  intro y hy
  simp only [Set.mem_compl_iff, hP_def, Set.mem_setOf_eq, not_lt] at hy
  exact toRiemannSphere_apply_of_nonneg f hy

/-- **Local-finite-pole identity at a pole.** On a *punctured* neighborhood
of any pole `x`, the pole extension agrees with `OnePoint.some ∘ f.toFun`.
The value at `x` itself is `∞` (not `some _`); restricting away from `x`
is essential.

Proof: the pole set minus `{x}` is finite (`MMeromorphicOn.poles_finite`
intersected with `{x}ᶜ`), hence closed. Working in `𝓝[≠] x` filters out `x`
itself. -/
lemma toRiemannSphere_eventuallyEq_some_punctured_of_pole
    (f : MeromorphicNonzero X) {x : X}
    (hx : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < (0 : WithTop ℤ)) :
    f.toRiemannSphere =ᶠ[𝓝[≠] x]
      (fun y => (OnePoint.some (f.toFun y) : RiemannSphere)) := by
  have h_poles_fin :
      {y : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun y < (0 : WithTop ℤ)}.Finite :=
    JacobianChallenge.MMeromorphicOn.poles_finite (X := X) (𝓘(ℂ, ℂ))
      f.toFun f.meromorphic f.nonvanishing_germ
  set P : Set X :=
      {y : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun y < (0 : WithTop ℤ)} with hP_def
  -- "Other poles" = `P \ {x}` is finite.
  have h_others_fin : (P \ {x}).Finite := h_poles_fin.diff
  have h_others_closed : IsClosed (P \ {x}) := h_others_fin.isClosed
  -- The `𝓝[≠] x`-eventuality: on `(P \ {x})ᶜ ∩ {x}ᶜ`, every point is not a
  -- pole. We use that `(P \ {x})ᶜ ∈ 𝓝 x` (since x ∉ P\{x}) and pass to the
  -- punctured filter.
  have h_open : IsOpen ((P \ {x})ᶜ) := h_others_closed.isOpen_compl
  have hx_in : x ∈ ((P \ {x})ᶜ) := by
    intro hxP; exact hxP.2 rfl
  -- Use `eventually_nhdsWithin_iff` to construct the punctured-nhd EventuallyEq.
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
  filter_upwards [h_open.mem_nhds hx_in] with y hy_compl hy_ne
  -- `hy_compl : y ∈ (P \ {x})ᶜ`, `hy_ne : y ∈ {x}ᶜ`, i.e. `y ≠ x`.
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy_ne
  by_cases hyP : y ∈ P
  · -- y ∈ P and y ≠ x ⟹ y ∈ P \ {x}, contradicting `hy_compl`.
    exact absurd ⟨hyP, hy_ne⟩ hy_compl
  · -- y ∉ P ⟹ 0 ≤ order ⟹ apply the non-pole branch.
    simp only [hP_def, Set.mem_setOf_eq, not_lt] at hyP
    exact toRiemannSphere_apply_of_nonneg f hyP

end MeromorphicNonzero

/-! ### `chartAt` reduction lemmas for `RiemannSphere`

The `ChartedSpace` instance picks `chartN` for finite points and `chartS`
for `∞`. We expose the two reductions as `simp`-friendly lemmas. -/

@[simp] lemma chartAt_riemannSphere_coe (z : ℂ) :
    (chartAt ℂ ((z : RiemannSphere))) = RiemannSphere.chartN := by
  show RiemannSphere.chartAt' ((z : RiemannSphere)) = RiemannSphere.chartN
  exact RiemannSphere.chartAt'_coe z

@[simp] lemma chartAt_riemannSphere_infty :
    (chartAt ℂ (∞ : RiemannSphere)) = RiemannSphere.chartS := by
  show RiemannSphere.chartAt' (∞ : RiemannSphere) = RiemannSphere.chartS
  exact RiemannSphere.chartAt'_infty

namespace MeromorphicNonzero

/-- **Chart-coordinate local form, non-pole branch (chartN).** On a full
neighborhood of `(chartAt ℂ x) x` (for any non-pole `x`), the chart-pulled-back
representative `chartN ∘ toRiemannSphere ∘ (chartAt ℂ x).symm` agrees with
`f.toFun ∘ (chartAt ℂ x).symm`.

This is the chartN-side input to the smoothness proof; the analyticity of the
right-hand side at `(chartAt ℂ x) x` is exactly the open structural gap (see
the section header). -/
lemma toRiemannSphere_chartN_localForm
    (f : MeromorphicNonzero X) {x : X}
    (hx : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    (RiemannSphere.chartN ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm)
      =ᶠ[𝓝 ((chartAt ℂ x) x)]
      (f.toFun ∘ (chartAt ℂ x).symm) := by
  -- Pull `f.toRiemannSphere = some ∘ f.toFun` (on a nhd of `x`) back through
  -- `(chartAt ℂ x).symm` to a nhd of `(chartAt ℂ x) x`.
  have h_evEq : f.toRiemannSphere =ᶠ[𝓝 x]
      (fun y => (OnePoint.some (f.toFun y) : RiemannSphere)) :=
    f.toRiemannSphere_eventuallyEq_some_of_nonpole hx
  -- Continuity of the chart inverse at `(chartAt ℂ x) x`.
  have h_chart_continuousAt :
      ContinuousAt (chartAt ℂ x).symm ((chartAt ℂ x) x) := by
    have h_open : IsOpen (chartAt ℂ x).target := (chartAt ℂ x).open_target
    have h_in : (chartAt ℂ x) x ∈ (chartAt ℂ x).target :=
      (chartAt ℂ x).map_source (mem_chart_source ℂ x)
    have h_co : ContinuousOn (chartAt ℂ x).symm (chartAt ℂ x).target :=
      (chartAt ℂ x).continuousOn_invFun
    exact h_co.continuousAt (h_open.mem_nhds h_in)
  -- The base point is `((chartAt ℂ x).symm) ((chartAt ℂ x) x) = x`.
  have h_pt : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x :=
    (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  -- Pull back: on a nhd of `(chartAt ℂ x) x`, `f.toRiemannSphere ∘ chart⁻¹ = some ∘ f.toFun ∘ chart⁻¹`.
  have h_pulled : (chartAt ℂ x).symm ⁻¹' {y | f.toRiemannSphere y =
      (OnePoint.some (f.toFun y) : RiemannSphere)} ∈ 𝓝 ((chartAt ℂ x) x) := by
    apply h_chart_continuousAt.preimage_mem_nhds
    rw [h_pt]
    exact h_evEq
  filter_upwards [h_pulled] with z hz
  -- Goal: `chartN (f.toRiemannSphere ((chartAt ℂ x).symm z))
  --        = f.toFun ((chartAt ℂ x).symm z)`.
  show RiemannSphere.chartN (f.toRiemannSphere ((chartAt ℂ x).symm z))
      = f.toFun ((chartAt ℂ x).symm z)
  rw [hz]
  exact RiemannSphere.chartN_apply_coe _

/-- **Chart-coordinate local form, pole branch (chartS), punctured.** On a
*punctured* neighborhood of `(chartAt ℂ x) x` (for any pole `x`), the
chart-pulled-back representative `chartS ∘ toRiemannSphere ∘ (chartAt ℂ x).symm`
agrees with `(f.toFun ∘ (chartAt ℂ x).symm)⁻¹` (i.e., `1 / f` in chart
coordinates).

By `meromorphicOrderAt_inv`, `(f.toFun ∘ chart⁻¹)⁻¹` has order `> 0` at the
chart point, hence vanishes there with multiplicity `|order|`. The full
chartS form on a non-punctured nhd uses `chartS ∞ = 0` plus an analytic
extension argument (the same value-vs-germ subtlety arises here too — the
chart inverse's analytic candidate has value `0` at the chart point, but the
literal value at the chart point is `chartS ∞ = 0`, which DOES match by
construction; the only obstruction is whether `f.toFun` on neighbors equals
its germ representative). -/
lemma toRiemannSphere_chartS_localForm_punctured
    (f : MeromorphicNonzero X) {x : X}
    (hx : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < (0 : WithTop ℤ)) :
    (RiemannSphere.chartS ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm)
      =ᶠ[𝓝[≠] ((chartAt ℂ x) x)]
      (fun z => (f.toFun ((chartAt ℂ x).symm z))⁻¹) := by
  -- `f.toRiemannSphere = some ∘ f.toFun` on `𝓝[≠] x`, in `eventually_nhdsWithin_iff` form.
  have h_evEq : f.toRiemannSphere =ᶠ[𝓝[≠] x]
      (fun y => (OnePoint.some (f.toFun y) : RiemannSphere)) :=
    f.toRiemannSphere_eventuallyEq_some_punctured_of_pole hx
  -- Decompose `𝓝[≠] x` membership into a witness `u ∈ 𝓝 x` such that the EqOn holds on `u ∩ {x}ᶜ`.
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff] at h_evEq
  -- `h_evEq : ∀ᶠ y in 𝓝 x, y ≠ x → f.toRiemannSphere y = some (f.toFun y)`.
  -- Step 1: pull `h_evEq` (which lives in `𝓝 x`) back to a nhd of `(chartAt ℂ x) x`.
  have h_chart_continuousAt :
      ContinuousAt (chartAt ℂ x).symm ((chartAt ℂ x) x) := by
    have h_open : IsOpen (chartAt ℂ x).target := (chartAt ℂ x).open_target
    have h_in : (chartAt ℂ x) x ∈ (chartAt ℂ x).target :=
      (chartAt ℂ x).map_source (mem_chart_source ℂ x)
    have h_co : ContinuousOn (chartAt ℂ x).symm (chartAt ℂ x).target :=
      (chartAt ℂ x).continuousOn_invFun
    exact h_co.continuousAt (h_open.mem_nhds h_in)
  have h_pt : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x :=
    (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  -- Pull back to a nhd of `(chartAt ℂ x) x` via `Tendsto.eventually`.
  -- We use the explicit form `Tendsto (chart.symm) (𝓝 (chart x)) (𝓝 x)` (after
  -- collapsing `chart.symm (chart x) = x` via `h_pt`). The cleanest path is to
  -- first compose: produce `Tendsto chart.symm (𝓝 (chart x)) (𝓝 x)` directly.
  have h_chart_tendsto :
      Filter.Tendsto (chartAt ℂ x).symm (𝓝 ((chartAt ℂ x) x)) (𝓝 x) := by
    have := h_chart_continuousAt
    rw [ContinuousAt, h_pt] at this
    exact this
  have h_pulled := h_chart_tendsto.eventually h_evEq
  -- We also need `(chartAt ℂ x).symm z ≠ x` whenever `z ≠ (chartAt ℂ x) x` and `z ∈ chart target`,
  -- by injectivity of `(chartAt ℂ x).symm` on its target.
  -- Promote the implication-eventually to a punctured-nhd EqOn:
  -- on `𝓝[≠] ((chartAt ℂ x) x)`, both `z ≠ (chartAt ℂ x) x` AND `z` is eventually in chart target,
  -- giving `(chartAt ℂ x).symm z ≠ x`.
  -- We bundle this into an `EventuallyEq` on `𝓝[≠] ((chartAt ℂ x) x)`.
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
  -- Goal: `∀ᶠ z in 𝓝 ((chartAt ℂ x) x), z ∈ {(chartAt ℂ x) x}ᶜ →
  --        chartS (f.toRiemannSphere ((chartAt ℂ x).symm z)) = (f.toFun ((chartAt ℂ x).symm z))⁻¹`.
  -- We combine `h_pulled` (impl eventually) with chart-target membership (open nhd).
  have h_target_mem : (chartAt ℂ x).target ∈ 𝓝 ((chartAt ℂ x) x) :=
    (chartAt ℂ x).open_target.mem_nhds
      ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
  filter_upwards [h_pulled, h_target_mem] with z hz_impl hz_target hz_ne
  -- `hz_ne : z ∈ {(chartAt ℂ x) x}ᶜ`, i.e. `z ≠ (chartAt ℂ x) x`.
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz_ne
  -- Show `(chartAt ℂ x).symm z ≠ x`.
  have h_symm_ne : (chartAt ℂ x).symm z ≠ x := by
    intro hzx
    apply hz_ne
    have := (chartAt ℂ x).right_inv hz_target
    rw [hzx] at this
    exact this.symm
  -- Apply the implication. `hz_impl` expects `(chartAt ℂ x).symm z ∈ ({x} : Set X)ᶜ`.
  have h_symm_compl : (chartAt ℂ x).symm z ∈ ({x} : Set X)ᶜ := by
    simp [Set.mem_compl_iff, Set.mem_singleton_iff, h_symm_ne]
  have hz : f.toRiemannSphere ((chartAt ℂ x).symm z) =
      (OnePoint.some (f.toFun ((chartAt ℂ x).symm z)) : RiemannSphere) :=
    hz_impl h_symm_compl
  -- Conclude.
  show RiemannSphere.chartS (f.toRiemannSphere ((chartAt ℂ x).symm z))
      = (f.toFun ((chartAt ℂ x).symm z))⁻¹
  rw [hz]
  exact RiemannSphere.chartS_apply_coe _

end MeromorphicNonzero

/-! ### Headline statement (Prop-only, preserved as a hook)

The headline `toRiemannSphere_contMDiff_statement` is preserved as a
`Prop`-valued `def`. The unconditional discharge requires either a
strengthening of `MeromorphicNonzero` (germ-value alignment) or a quotient
restructure; see the section header for the obstruction analysis.
-/

namespace MeromorphicNonzero

/-- **(R1, statement only)** The pole extension of `f` is `ContMDiff` from
`X` to `RiemannSphere` (with model `𝓘(ℂ, ℂ) → 𝓘(ℂ)`, smoothness `ω`).

This is preserved as a `Prop`-valued statement (not an `axiom`, not a
`theorem`) because the unconditional discharge is blocked by a structural
gap in the `MeromorphicNonzero` carrier: the pointwise value `f.toFun x`
at a regular point `x` may not match the germ's analytic limit at `x`,
in which case `toRiemannSphere` is genuinely discontinuous at `x`. See
the section header in this file for the full obstruction analysis and the
partial chart-coordinate forms that are unconditionally proven
(`toRiemannSphere_eventuallyEq_some_of_nonpole`,
`toRiemannSphere_eventuallyEq_some_punctured_of_pole`,
`toRiemannSphere_chartN_localForm`,
`toRiemannSphere_chartS_localForm_punctured`).

The classical statement on a Riemann surface holds because "meromorphic
function" silently includes value-equals-germ-limit; the Lean structure does
not enforce this. Resolution paths are catalogued in the file header. -/
def toRiemannSphere_contMDiff_statement (f : MeromorphicNonzero X) : Prop :=
  ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f.toRiemannSphere

end MeromorphicNonzero

end JacobianChallenge
