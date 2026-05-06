/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicExtension
import JacobianChallenge.Manifold.MeromorphicDivisor

/-! # Finiteness of the fibres of the pole extension `f̃ : X → RiemannSphere`

For `f : MeromorphicNonzero X` on a compact complex 1-manifold `X`, this file
ships **finiteness of the special fibres** of the pole extension
`f̃ := f.toRiemannSphere`:

* `toRiemannSphere_preimage_infty_eq` — the `∞`-fibre `f̃ ⁻¹' {∞}`
  equals the pole set `{x | mmeromorphicOrderAt I f x < 0}` (set equality
  on the nose, by `toRiemannSphere_eq_infty_iff_neg`).

* `toRiemannSphere_preimage_infty_finite` — the `∞`-fibre is **finite**.
  Direct corollary of the equality above and
  `JacobianChallenge.MMeromorphicOn.poles_finite` from
  `Manifold/MeromorphicDivisor.lean`.

* `toRiemannSphere_preimage_some_subset_orderNonneg` — the fibre over any
  finite value `(some w : RiemannSphere)` is contained in the regular set
  `{x | 0 ≤ mmeromorphicOrderAt I f x}` (i.e. away from the poles).
  Direct from `toRiemannSphere_eq_some_iff_nonneg`.

* `toRiemannSphere_preimage_some_disjoint_pole` — the same fibre is
  disjoint from the pole set. Companion to the previous lemma in
  contrapositive form.

These are R2-style finite-fibre statements feeding
`Manifold/DegreeConstancy.lean` and `Manifold/GlobalResidueSum.lean`:
the named hooks `degreeConstant_statement` and the residue-sum
hypothesis both consume finiteness of `f̃ ⁻¹' {y}` for special `y`,
and the `∞`-side is now a proper `theorem` rather than a re-derivation
at every call site.

Why these are not redundant with `MeromorphicNonzero.toRiemannSphere_eq_*_iff_*`:
the existing `iff` characterisations are pointwise; the consumer
typically needs the *set-level* statement
`f̃ ⁻¹' {y} = {x | predicate}` and *finiteness of that set* in one hop,
without re-running the rewriter at every call site.
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

/-- **Set-level identification of the `∞`-fibre.** The preimage
`f̃ ⁻¹' {∞}` of the point at infinity under the pole extension is
exactly the set of poles of `f` (points of strictly negative order). -/
lemma toRiemannSphere_preimage_infty_eq (f : MeromorphicNonzero X) :
    f.toRiemannSphere ⁻¹' {(∞ : RiemannSphere)} =
      {x : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
    f.toRiemannSphere_eq_infty_iff_neg]

/-- **Finiteness of the `∞`-fibre of the pole extension.** On a compact
Hausdorff complex 1-manifold, the preimage `f̃ ⁻¹' {∞}` of the point at
infinity is a finite subset of `X`.

Proof: rewrite the fibre as the pole set via
`toRiemannSphere_preimage_infty_eq`, then apply
`JacobianChallenge.MMeromorphicOn.poles_finite` (which uses the
`meromorphic` and `nonvanishing_germ` fields of `f`). -/
theorem toRiemannSphere_preimage_infty_finite (f : MeromorphicNonzero X) :
    (f.toRiemannSphere ⁻¹' {(∞ : RiemannSphere)}).Finite := by
  rw [toRiemannSphere_preimage_infty_eq]
  exact JacobianChallenge.MMeromorphicOn.poles_finite (X := X) (𝓘(ℂ, ℂ))
    f.toFun f.meromorphic f.nonvanishing_germ

/-- **Finite values are taken only at non-poles.** The preimage
`f̃ ⁻¹' {(some w)}` over any finite value `w : ℂ` is contained in the
set of regular points (order `≥ 0`). -/
lemma toRiemannSphere_preimage_some_subset_orderNonneg
    (f : MeromorphicNonzero X) (w : ℂ) :
    f.toRiemannSphere ⁻¹' {(OnePoint.some w : RiemannSphere)} ⊆
      {x : X | 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x} := by
  intro x hx
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
  -- If `f̃ x = some w`, in particular `f̃ x ≠ ∞`, so `x` cannot be a pole.
  show 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x
  by_contra hpole
  -- `hpole : ¬ 0 ≤ mmeromorphicOrderAt _ f.toFun x`, hence order < 0.
  have hneg : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0 := not_le.mp hpole
  rw [f.toRiemannSphere_apply_of_neg hneg] at hx
  exact (OnePoint.infty_ne_coe w) hx

/-- **Pole-disjointness of finite-value fibres.** The preimage
`f̃ ⁻¹' {(some w)}` is disjoint from the pole set
`{x | mmeromorphicOrderAt I f x < 0}`. Companion to
`toRiemannSphere_preimage_some_subset_orderNonneg`. -/
lemma toRiemannSphere_preimage_some_disjoint_pole
    (f : MeromorphicNonzero X) (w : ℂ) :
    Disjoint (f.toRiemannSphere ⁻¹' {(OnePoint.some w : RiemannSphere)})
      {x : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0} := by
  rw [Set.disjoint_left]
  intro x hx hpole
  have hsub := toRiemannSphere_preimage_some_subset_orderNonneg f w hx
  -- Unwrap the setOf membership.
  have hnonneg : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x := hsub
  have hpole' : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0 := hpole
  exact (not_le.mpr hpole') hnonneg

end MeromorphicNonzero

end JacobianChallenge

end
