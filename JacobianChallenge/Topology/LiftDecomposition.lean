/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.GermLimitLiftSetup
import JacobianChallenge.Topology.LinearSystemAPI
import JacobianChallenge.Topology.LinearSystemConstants
import JacobianChallenge.Topology.MeromorphicNonzeroBuilder
import JacobianChallenge.Topology.RRGenusZeroFinrankChain

set_option diagnostics.threshold 100

/-! # Decomposition of `LiftToMeromorphicNonzero` into three sub-hypotheses

zz362's `LiftToMeromorphicNonzero X` asks: given a non-constant
`g ∈ L(δp)`, produce a `MeromorphicNonzero X` with the same order
pattern. Via zz375/zz376's `MeromorphicNonzero.ofRegularContinuous`
builder, this decomposes into three more elementary sub-hypotheses
about `germLimitLift g`:

  (i)   `LiftMMeromorphicOn X` — for every `g ∈ L(δp)`,
        `germLimitLift g` is `MMeromorphicOn` on the whole manifold.

  (ii)  `LiftNonvanishingGerm X` — for every non-constant
        `g ∈ L(δp)`, `germLimitLift g` has order ≠ ⊤ everywhere.

  (iii) `LiftRegularContinuousAt X` — for every `g ∈ L(δp)`,
        `germLimitLift g` is `ContinuousAt` at every non-pole point.

  (iv)  `LiftOrderPreserved X` — `germLimitLift g` has the same
        order pattern as `g` (bounded by δp).

  (v)   `LiftNotConstant X` — `germLimitLift g` is non-constant when
        `g` is.

Under all five, the composition gives `LiftToMeromorphicNonzero X`.

This file names them and proves the composition. Each individual
discharge is a separate downstream chip. The classical content:
(i) and (iv) are germ-preservation under canonicalisation; (ii) is
the identity theorem for analytic functions; (iii) is the local
continuity at non-pole regular values from analytic continuation;
(v) is non-constancy preservation.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff

set_option linter.unusedSectionVars false

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Sub-hypothesis (i): `germLimitLift` preserves global meromorphy. -/
def LiftMMeromorphicOn : Prop :=
  ∀ (p : X) (g : X → ℂ), IsBoundedByDeltaP p g →
    MMeromorphicOn (𝓘(ℂ, ℂ)) (germLimitLift g) Set.univ

/-- Sub-hypothesis (ii): `germLimitLift` of a non-constant `L(δp)`
member has no identically-zero germ. -/
def LiftNonvanishingGerm : Prop :=
  ∀ (p : X) (g : X → ℂ), IsBoundedByDeltaP p g →
    g ∉ Submodule.span ℂ ({(1 : X → ℂ)} : Set (X → ℂ)) →
    ∀ x, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (germLimitLift g) x ≠ ⊤

/-- Sub-hypothesis (iii): `germLimitLift` is `ContinuousAt` at non-
pole points. -/
def LiftRegularContinuousAt : Prop :=
  ∀ (p : X) (g : X → ℂ), IsBoundedByDeltaP p g →
    ∀ x, 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (germLimitLift g) x →
      ContinuousAt (germLimitLift g) x

/-- Sub-hypothesis (iv): `germLimitLift` preserves the order pattern
of `g` (the L(δp) bounds carry over). -/
def LiftOrderPreserved : Prop :=
  ∀ (p : X) (g : X → ℂ), IsBoundedByDeltaP p g →
    IsBoundedByDeltaP p (germLimitLift g)

/-- Sub-hypothesis (v): `germLimitLift` preserves non-constancy. -/
def LiftNotConstant : Prop :=
  ∀ (_p : X) (g : X → ℂ),
    g ∉ Submodule.span ℂ ({(1 : X → ℂ)} : Set (X → ℂ)) →
    ¬ JacobianChallenge.IsConstantMap (germLimitLift g)

/-- **Composition: under all five sub-hypotheses,
`LiftToMeromorphicNonzero X` holds.** -/
theorem liftToMeromorphicNonzero_of_five_sub_hypotheses
    (h_mero : LiftMMeromorphicOn X)
    (h_nonvan : LiftNonvanishingGerm X)
    (h_reg_cts : LiftRegularContinuousAt X)
    (h_ord : LiftOrderPreserved X)
    (h_nc : LiftNotConstant X) :
    LiftToMeromorphicNonzero X := by
  intro p g hg_in hg_nin
  -- Build the MeromorphicNonzero via ofRegularContinuous.
  set f : MeromorphicNonzero X :=
    MeromorphicNonzero.ofRegularContinuous (germLimitLift g)
      (h_mero p g hg_in)
      (h_nonvan p g hg_in hg_nin)
      (h_reg_cts p g hg_in)
    with hf_def
  -- f.toFun = germLimitLift g.
  refine ⟨f, ?_, ?_, ?_⟩
  · -- ∀ x ≠ p, 0 ≤ ord f.toFun x.
    -- f.toFun = germLimitLift g, and h_ord says IsBoundedByDeltaP p (germLimitLift g).
    have h_lift_in : IsBoundedByDeltaP p (germLimitLift g) := h_ord p g hg_in
    -- Order condition at x ≠ p from h_lift_in.
    intro x hx
    show 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (germLimitLift g) x
    exact h_lift_in.order_nonneg_off x hx
  · -- Order at p ≥ -1.
    have h_lift_in : IsBoundedByDeltaP p (germLimitLift g) := h_ord p g hg_in
    show ((-1 : ℤ) : WithTop ℤ) ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (germLimitLift g) p
    exact h_lift_in.order_ge_neg_one_at_p
  · -- ¬ IsConstantMap f.toFun = germLimitLift g.
    exact h_nc p g hg_nin

end JacobianChallenge

end
