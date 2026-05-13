/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PoleExtensionFibres
import JacobianChallenge.Manifold.MeromorphicExtension
import JacobianChallenge.Manifold.MeromorphicAt
import JacobianChallenge.Divisor.PrincipalDivisor

set_option diagnostics.threshold 100

/-! # The ∞-fibre of the pole extension is a singleton when `f` has one simple pole

For `f : MeromorphicNonzero X` with a *single simple pole* at `p`
(i.e. `mmeromorphicOrderAt _ f.toFun p = -1` and `0 ≤
mmeromorphicOrderAt _ f.toFun x` for every `x ≠ p`), the pole-extension
`f.toRiemannSphere : X → RiemannSphere` has

    f.toRiemannSphere ⁻¹' {∞} = {p}.

This is the fibre side of the analytic bridge needed to close the
`MeroSinglePoleExtendsToDeg1Map X` hypothesis from
`Topology/RiemannRochGenusZeroDecomposition.lean` (zz337). It is a thin
specialisation of the existing unconditional set-level identification
`MeromorphicNonzero.toRiemannSphere_preimage_infty_eq` (which says
"`∞`-fibre = pole set"); under the single-simple-pole hypothesis the
pole set is forced down to the singleton `{p}`.

The lemma is stated both as a set equality and as a `Set.Finite`
witness with cardinality `1`, the second form being the shape downstream
`RegularValueWitness`-construction code will want.

No `sorry`, no `axiom`.
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

/-- **Singleton characterization of the pole set under one simple pole.**
If `f : MeromorphicNonzero X` has order `-1` at `p` and order `≥ 0` at
every other point, then the set of poles of `f` (points of strictly
negative order) is exactly `{p}`. -/
lemma pole_set_eq_singleton_of_single_simple_pole
    (f : MeromorphicNonzero X) {p : X}
    (h_pole : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p = ((-1 : ℤ) : WithTop ℤ))
    (h_holo : ∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    {x : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0} = {p} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro hx_neg
    -- We show x = p by contradiction with `h_holo`.
    by_contra hne
    have h_nonneg : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x := h_holo x hne
    exact (not_le.mpr hx_neg) h_nonneg
  · intro hx_eq
    subst hx_eq
    -- At `p`: order = -1 < 0.
    rw [h_pole]
    -- Goal: ((-1 : ℤ) : WithTop ℤ) < 0
    exact_mod_cast (show (-1 : ℤ) < 0 from by decide)

/-- **∞-fibre singleton.** Under one simple pole at `p`, the preimage
`f.toRiemannSphere ⁻¹' {∞}` equals the singleton `{p}`. -/
theorem toRiemannSphere_preimage_infty_eq_singleton_of_single_simple_pole
    (f : MeromorphicNonzero X) {p : X}
    (h_pole : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p = ((-1 : ℤ) : WithTop ℤ))
    (h_holo : ∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    f.toRiemannSphere ⁻¹' {(∞ : RiemannSphere)} = {p} := by
  rw [f.toRiemannSphere_preimage_infty_eq]
  exact pole_set_eq_singleton_of_single_simple_pole f h_pole h_holo

/-- **Finite-witness form.** The ∞-fibre is a finite set with one element
under one simple pole. -/
theorem toRiemannSphere_preimage_infty_finite_of_single_simple_pole
    (f : MeromorphicNonzero X) {p : X}
    (h_pole : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p = ((-1 : ℤ) : WithTop ℤ))
    (h_holo : ∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    (f.toRiemannSphere ⁻¹' {(∞ : RiemannSphere)}).Finite := by
  rw [toRiemannSphere_preimage_infty_eq_singleton_of_single_simple_pole
      f h_pole h_holo]
  exact Set.finite_singleton p

/-- **Cardinality-one form.** Cast through `Set.Finite.toFinset`: the
∞-fibre's `toFinset` has cardinality `1`. -/
theorem toRiemannSphere_preimage_infty_card_eq_one_of_single_simple_pole
    (f : MeromorphicNonzero X) {p : X}
    (h_pole : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p = ((-1 : ℤ) : WithTop ℤ))
    (h_holo : ∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    (toRiemannSphere_preimage_infty_finite_of_single_simple_pole
      f h_pole h_holo).toFinset.card = 1 := by
  -- Reduce to `Set.toFinset` of the singleton.
  have h_eq :
      (toRiemannSphere_preimage_infty_finite_of_single_simple_pole
        f h_pole h_holo).toFinset = ({p} : Finset X) := by
    ext x
    rw [Set.Finite.mem_toFinset]
    rw [toRiemannSphere_preimage_infty_eq_singleton_of_single_simple_pole
      f h_pole h_holo]
    simp
  rw [h_eq]
  simp

end MeromorphicNonzero

end JacobianChallenge

end
