/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SinglePoleInftyFibre
import JacobianChallenge.Manifold.ToRSNonConstantFromSinglePole
import JacobianChallenge.Manifold.Degree
import JacobianChallenge.Manifold.MeromorphicExtension

set_option diagnostics.threshold 100

/-! # `RegularValueWitness` at `∞` for `f.toRiemannSphere` with one simple pole

For `f : MeromorphicNonzero X` with a single simple pole at `p` and
holomorphic elsewhere, this file builds the `RegularValueWitness
f.toRiemannSphere` carrying:

* `value = ∞`
* `fiber_finite : (f.toRiemannSphere ⁻¹' {∞}).Finite`  (from zz338)
* downstream `.card = 1`  (from zz338's cardinality lemma)

The companion regularity certificate (chart-pullback derivative at `p`
non-zero, in the south-chart-of-`RiemannSphere` coordinates) is *named*
here as a separate `Prop`:

  `chartPullback_deriv_at_simple_pole_ne_zero f p`

so that once it is discharged, the promotion to
`RegularValueWitnessReg` is mechanical via
`RegularValueWitness.toRegular`. Discharging the named regularity
certificate is the next chip (Forster §1.4 local-form argument:
`f ∼ c/z` near a simple pole forces `1/f ∼ z/c` to have derivative
`1/c ≠ 0` at `0`).

What this chip *does* close, unconditionally:

* The `RegularValueWitness` builder at `value = ∞`.
* The `.card = 1` identity for that witness.

What this chip *names but does not close*:

* The regularity certificate at the pole point.

These are honest, separable Lean lemmas. No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Set OnePoint

namespace JacobianChallenge

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace MeromorphicNonzero

/-- **The `RegularValueWitness` at `∞` for the pole-extension.**
Under one simple pole at `p` and holomorphy elsewhere, build the
`ContMDiff.RegularValueWitness f.toRiemannSphere` with value `∞` and finite
fibre `{p}`. -/
def regularValueWitness_at_infty_of_single_simple_pole
    (f : MeromorphicNonzero X) {p : X}
    (h_pole : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p = ((-1 : ℤ) : WithTop ℤ))
    (h_holo : ∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    ContMDiff.RegularValueWitness f.toRiemannSphere where
  value := (∞ : RiemannSphere)
  fiber_finite :=
    toRiemannSphere_preimage_infty_finite_of_single_simple_pole f h_pole h_holo

/-- **The `.value` field of the constructed witness is `∞`** (`rfl`). -/
@[simp] lemma regularValueWitness_at_infty_value
    (f : MeromorphicNonzero X) {p : X}
    (h_pole : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p = ((-1 : ℤ) : WithTop ℤ))
    (h_holo : ∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    (regularValueWitness_at_infty_of_single_simple_pole f h_pole h_holo).value
      = (∞ : RiemannSphere) := rfl

/-- **`.card = 1` for the constructed witness.** -/
theorem regularValueWitness_at_infty_card_eq_one
    (f : MeromorphicNonzero X) {p : X}
    (h_pole : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p = ((-1 : ℤ) : WithTop ℤ))
    (h_holo : ∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    (regularValueWitness_at_infty_of_single_simple_pole f h_pole h_holo).card = 1 := by
  unfold ContMDiff.RegularValueWitness.card regularValueWitness_at_infty_of_single_simple_pole
  exact toRiemannSphere_preimage_infty_card_eq_one_of_single_simple_pole
    f h_pole h_holo

/-- **Named regularity certificate at a simple pole.** The chart-pullback
of `f.toRiemannSphere` from `p` to `∞` has nonzero derivative at the
chart image of `p`.

Classical content: if `f` has a simple pole at `p`, then in any chart
around `p`, `f` looks like `c/z + O(1)` with `c ≠ 0`. The south chart
of `RiemannSphere` inverts: `chartS w = 1/w` for `w ≠ ∞`. So near `p`,
`chartS ∘ f.toRiemannSphere ∘ (chartAt ℂ p).symm` looks like
`z ↦ z/c + O(z²)`, which is differentiable at `0` with nonzero
derivative `1/c`. Discharging this is a forthcoming chip.

For now this is the named hypothesis form, ready to be plugged into
`RegularValueWitness.toRegular`. -/
def ChartPullback_Deriv_AtSimplePole_NeZero
    (f : MeromorphicNonzero X) (p : X) : Prop :=
  deriv ((chartAt ℂ (∞ : RiemannSphere)) ∘ f.toRiemannSphere
      ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) ≠ 0

/-- **Promotion to `RegularValueWitnessReg`** conditional on the named
regularity certificate. The non-trivial content here is exactly the
regularity certificate; this lemma is the mechanical packaging.

The hypothesis `h_reg_at_p` directly supplies the regularity at the
unique pre-image `p` (the ∞-fibre is `{p}` by zz338, so the
∀-quantification in `RegularValueWitnessReg.is_regular` collapses to
the single point `p`). -/
noncomputable def regularValueWitnessReg_at_infty_of_single_simple_pole
    (f : MeromorphicNonzero X) {p : X}
    (h_pole : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p = ((-1 : ℤ) : WithTop ℤ))
    (h_holo : ∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x)
    (h_reg_at_p : ChartPullback_Deriv_AtSimplePole_NeZero f p) :
    ContMDiff.RegularValueWitnessReg f.toRiemannSphere := by
  refine (regularValueWitness_at_infty_of_single_simple_pole f h_pole h_holo).toRegular ?_
  -- Goal: ∀ x ∈ f.toRiemannSphere ⁻¹' {(...).value}, deriv (chartAt ∘ ... ∘ chart.symm) ≠ 0.
  -- (... ).value = ∞ by `regularValueWitness_at_infty_value`.
  intro x hx
  -- Rewrite the preimage to {p} via zz338.
  have h_value : (regularValueWitness_at_infty_of_single_simple_pole f h_pole h_holo).value
      = (∞ : RiemannSphere) :=
    regularValueWitness_at_infty_value f h_pole h_holo
  rw [h_value] at hx
  have h_fibre :
      f.toRiemannSphere ⁻¹' {(∞ : RiemannSphere)} = {p} :=
    toRiemannSphere_preimage_infty_eq_singleton_of_single_simple_pole
      f h_pole h_holo
  rw [h_fibre] at hx
  rcases hx with rfl
  -- Now goal is the named regularity certificate at p.
  -- We need to align `chartAt ℂ (...).value` with `chartAt ℂ ∞`.
  rw [h_value]
  exact h_reg_at_p

/-- **`.card = 1` is preserved** under the conditional promotion. -/
theorem regularValueWitnessReg_at_infty_card_eq_one
    (f : MeromorphicNonzero X) {p : X}
    (h_pole : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p = ((-1 : ℤ) : WithTop ℤ))
    (h_holo : ∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x)
    (h_reg_at_p : ChartPullback_Deriv_AtSimplePole_NeZero f p) :
    (regularValueWitnessReg_at_infty_of_single_simple_pole
      f h_pole h_holo h_reg_at_p).card = 1 := by
  -- `RegularValueWitnessReg.card` is `.toWitness.card`. Use the
  -- `toRegular_card`-style argument: the underlying `.toWitness` is
  -- definitionally `regularValueWitness_at_infty_of_single_simple_pole`,
  -- whose `.card = 1` is `regularValueWitness_at_infty_card_eq_one`.
  unfold regularValueWitnessReg_at_infty_of_single_simple_pole
  show (regularValueWitness_at_infty_of_single_simple_pole f h_pole h_holo).card = 1
  exact regularValueWitness_at_infty_card_eq_one f h_pole h_holo

end MeromorphicNonzero

end JacobianChallenge

end
