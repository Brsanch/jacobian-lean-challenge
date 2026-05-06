/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PoleExtensionFibres
import JacobianChallenge.Divisor.PrincipalDivisor

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # `fiberCount` bridge between topological fibres and the divisor support

For `f : MeromorphicNonzero X` on a compact complex 1-manifold `X`, the
pole-extension `f̃ := f.toRiemannSphere : X → RiemannSphere = OnePoint ℂ`
sends:

* `x` with `mmeromorphicOrderAt I f x < 0` (a pole)            ↦ `∞`,
* `x` with `mmeromorphicOrderAt I f x ≥ 0`                      ↦ `some (f x)`.

This file packages the **set/finset bookkeeping bridge** between

* the topological fibre `f̃ ⁻¹' {y}` for `y ∈ {∞}` and `y = some 0`, and
* the corresponding sign-filtered slice of `(principalDivisorMap f).supportFinset`,

with the `∞` side being a clean **set-equality on the nose** (and hence a
`Finset` equality after passing through `Set.Finite.toFinset`), and the
`some 0` side being a clean **set-equality** between the topological fibre
and the explicit subset
`{x | 0 ≤ mmeromorphicOrderAt I f x ∧ f.toFun x = 0}` of `X`.

## Main definitions

* `fiberCount f̃ y : ℕ` — `Set.ncard (f̃ ⁻¹' {y})`. Returns `0` if the
  fibre is infinite, otherwise its set-cardinality.

## Main lemmas

* `infty_fiber_toFinset_eq_filter_neg` — the `∞`-fibre's
  `Set.Finite.toFinset` (via the ZZ2 finiteness lemma) equals the
  `supportFinset.filter (orderFun … < 0)` slice. **Set-bijection on the
  nose.**

* `fiberCount_infty_eq_filter_neg_card` — corollary at the cardinality
  level: `fiberCount f̃ ∞ = (supportFinset.filter (orderFun … < 0)).card`.

* `some_zero_fiber_set_eq` — set-equality:
  `f̃ ⁻¹' {some 0} = {x | 0 ≤ mmeromorphicOrderAt I f x ∧ f.toFun x = 0}`.

These are pure bookkeeping. They do *not* claim that the fibre cardinality
equals `(zeroCount f).toNat` or `(poleCount f).toNat` — those are
multiplicity-weighted sums over the same finsets, and the relation
`mult ≥ 1 on the support` only gives the inequalities
`#fibre ≤ (poleCount f).toNat` and (under the chart-positive-order /
value-zero identification, which is *not* shipped here)
`#regular zero set ≤ (zeroCount f).toNat`.
-/

noncomputable section

open scoped Manifold Topology ContDiff BigOperators
open Filter Set OnePoint

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## `fiberCount` definition -/

/-- **Fibre cardinality of the pole extension.** `Set.ncard` of the fibre
`f̃ ⁻¹' {y}`. By convention `Set.ncard` returns `0` on an infinite set;
on the special fibres `y = ∞` (always finite by the ZZ2 lemma
`toRiemannSphere_preimage_infty_finite`) and on any fibre whose
finiteness is otherwise known, this is the genuine integer cardinality. -/
noncomputable def fiberCount (f : MeromorphicNonzero X)
    (y : RiemannSphere) : ℕ :=
  (f.toRiemannSphere ⁻¹' {y}).ncard

/-! ## ∞-side bridge: set-equality with the filtered support -/

/-- **Pole-fibre set equality with the divisor support, sign-filtered.**

The `∞`-fibre `f̃ ⁻¹' {∞}` of the pole extension equals, **as a set on
the nose**, the support points of the principal divisor where the order
is strictly negative.

This is a thin reshuffle of `toRiemannSphere_preimage_infty_eq` (ZZ2):
the `∞`-fibre is `{x | ord_x f < 0}`, and any such `x` automatically has
`(principalDivisorMap f) x ≠ 0`, hence lies in `supportFinset`. -/
lemma infty_fiber_set_eq_filter_neg (f : MeromorphicNonzero X) :
    f.toRiemannSphere ⁻¹' {(∞ : RiemannSphere)} =
      {x : X | (principalDivisorMap f : X → ℤ) x ≠ 0 ∧
                mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0} := by
  rw [toRiemannSphere_preimage_infty_eq f]
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hx
    refine ⟨?_, hx⟩
    -- `ord < 0 ⇒ orderFun ≠ 0`.
    have hne_top : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x ≠ ⊤ :=
      f.nonvanishing_germ x
    show (principalDivisorMap f : X → ℤ) x ≠ 0
    rw [principalDivisorMap_apply]
    intro h0
    -- `orderFun = 0` and `ord ≠ ⊤` ⇒ `ord = 0`, contradicting `ord < 0`.
    rcases WithTop.untop₀_eq_zero.mp h0 with hzero | htop
    · rw [hzero] at hx; exact lt_irrefl _ hx
    · exact hne_top htop
  · intro ⟨_, hneg⟩
    exact hneg

/-- **Pole-fibre `Finset.toFinset` equality with the support filter.**

The `Set.Finite.toFinset` of the `∞`-fibre (using the finiteness witness
from ZZ2 `toRiemannSphere_preimage_infty_finite`) coincides with the
`supportFinset.filter` cut by the strict-negativity predicate on
`mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun`. -/
lemma infty_fiber_toFinset_eq_filter_neg (f : MeromorphicNonzero X)
    [DecidablePred (fun x : X => mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0)] :
    (f.toRiemannSphere_preimage_infty_finite).toFinset =
      ((principalDivisorMap f).supportFinset).filter
        (fun x => mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0) := by
  classical
  ext x
  rw [Set.Finite.mem_toFinset, Finset.mem_filter,
      Div.mem_supportFinset, toRiemannSphere_preimage_infty_eq f]
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hx
    refine ⟨?_, hx⟩
    -- `ord < 0 ⇒ (principalDivisorMap f) x ≠ 0`.
    have hne_top : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x ≠ ⊤ :=
      f.nonvanishing_germ x
    rw [principalDivisorMap_apply]
    intro h0
    rcases WithTop.untop₀_eq_zero.mp h0 with hzero | htop
    · rw [hzero] at hx; exact lt_irrefl _ hx
    · exact hne_top htop
  · intro ⟨_, hneg⟩
    exact hneg

/-- **Cardinality form of the `∞`-fibre bridge.**

`fiberCount f̃ ∞ = (supportFinset.filter (ord_x f < 0)).card`. -/
lemma fiberCount_infty_eq_filter_neg_card (f : MeromorphicNonzero X)
    [DecidablePred (fun x : X => mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0)] :
    fiberCount f (∞ : RiemannSphere) =
      (((principalDivisorMap f).supportFinset).filter
        (fun x => mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0)).card := by
  classical
  unfold fiberCount
  rw [← infty_fiber_toFinset_eq_filter_neg f]
  exact Set.ncard_eq_toFinset_card _ f.toRiemannSphere_preimage_infty_finite

/-! ## `some 0` side bridge: set-equality with the regular zero set -/

/-- **Finite-zero-fibre set equality.**

The fibre `f̃ ⁻¹' {some 0}` of the pole extension over the finite value
`0 ∈ ℂ` equals, **as a set on the nose**, the regular zero locus
`{x | 0 ≤ mmeromorphicOrderAt I f x ∧ f.toFun x = 0}`.

Note: this is *not* the multiplicity-weighted `zeroCount f`; it is the
unweighted set of distinct points where `f` is regular and vanishes. The
two coincide only when every zero is simple. -/
lemma some_zero_fiber_set_eq (f : MeromorphicNonzero X) :
    f.toRiemannSphere ⁻¹' {(OnePoint.some (0 : ℂ) : RiemannSphere)} =
      {x : X | 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x ∧
                f.toFun x = 0} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · intro hx
    -- `f̃ x = some 0`; in particular `f̃ x ≠ ∞`, so order is `≥ 0`.
    have hnonneg : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x := by
      by_contra hneg
      push_neg at hneg
      rw [f.toRiemannSphere_apply_of_neg hneg] at hx
      exact (OnePoint.infty_ne_coe (0 : ℂ)) hx
    refine ⟨hnonneg, ?_⟩
    -- At a regular point `f̃ x = some (f x) = some 0`, so `f x = 0`.
    rw [f.toRiemannSphere_apply_of_nonneg hnonneg] at hx
    exact OnePoint.coe_injective hx
  · intro ⟨hnonneg, hzero⟩
    rw [f.toRiemannSphere_apply_of_nonneg hnonneg, hzero]

/-! ## Lower bound on `fiberCount` -/

/-- **Lower bound: a fibre in the image with finite preimage has cardinality
at least `1`.**

If `y : RiemannSphere` lies in the image of `f̃ = f.toRiemannSphere` and the
preimage `f̃ ⁻¹' {y}` is finite, then `1 ≤ fiberCount f y`. The finiteness
hypothesis is necessary because `Set.ncard` returns `0` on infinite sets;
on the `∞`-fibre and on any explicitly-known finite fibre this is just
`Set.Nonempty`. -/
lemma one_le_fiberCount_of_mem_range_of_finite (f : MeromorphicNonzero X)
    {y : RiemannSphere} (hy : y ∈ Set.range f.toRiemannSphere)
    (hfin : (f.toRiemannSphere ⁻¹' {y}).Finite) :
    1 ≤ fiberCount f y := by
  unfold fiberCount
  have hne : (f.toRiemannSphere ⁻¹' {y}).Nonempty := by
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, by simpa using hx⟩
  have hpos : 0 < (f.toRiemannSphere ⁻¹' {y}).ncard :=
    (Set.ncard_pos hfin).mpr hne
  exact hpos

/-- **Specialisation to the `∞`-fibre.**

If `∞` lies in the image of `f̃` (equivalently, `f` has at least one pole),
then `1 ≤ fiberCount f ∞`. The finiteness hypothesis is automatic from the
ZZ2 lemma `toRiemannSphere_preimage_infty_finite`. -/
lemma one_le_fiberCount_infty_of_mem_range (f : MeromorphicNonzero X)
    (hy : (∞ : RiemannSphere) ∈ Set.range f.toRiemannSphere) :
    1 ≤ fiberCount f (∞ : RiemannSphere) :=
  one_le_fiberCount_of_mem_range_of_finite f hy
    f.toRiemannSphere_preimage_infty_finite

/-! ## Summary headline -/

/-- **Pole-fibre is finite, zero-fibre is set-described.**

Composite headline lemma packaging the two set-level bridges. The `∞`
side is fully unconditional (set-equality + finiteness from ZZ2); the
`some 0` side gives a clean set-equality with the regular zero locus,
which is the first half of any subsequent multiplicity-weighted bridge. -/
lemma fiber_set_descriptions (f : MeromorphicNonzero X) :
    (f.toRiemannSphere ⁻¹' {(∞ : RiemannSphere)} =
        {x : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0}) ∧
      (f.toRiemannSphere ⁻¹' {(OnePoint.some (0 : ℂ) : RiemannSphere)} =
        {x : X | 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x ∧
                  f.toFun x = 0}) :=
  ⟨toRiemannSphere_preimage_infty_eq f, some_zero_fiber_set_eq f⟩

end MeromorphicNonzero

end JacobianChallenge

end
