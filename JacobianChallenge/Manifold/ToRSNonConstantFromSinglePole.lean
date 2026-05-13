/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SinglePoleInftyFibre
import JacobianChallenge.Manifold.ChartedSpaceOpenInfinite
import JacobianChallenge.Manifold.MeromorphicExtension
import JacobianChallenge.Manifold.IsConstantMapAux

set_option diagnostics.threshold 100

/-! # `¬ IsConstantMap f.toRiemannSphere` under a single simple pole

For `f : MeromorphicNonzero X` with a single simple pole at `p` and
holomorphic elsewhere, the pole-extension `f.toRiemannSphere :
X → RiemannSphere` is automatically non-constant: it takes the value
`∞` at `p` and a finite value at any *other* point. Since `X` is a
complex 1-manifold, the chart at `p` has open source containing `p`,
and open neighbourhoods in a `ChartedSpace ℂ` are infinite
(zz333, `ChartedSpaceOpenInfinite.lean`), so a second point `q ≠ p`
exists in the chart source — and at `q` the order hypothesis forces
`f.toRiemannSphere q = some (f.toFun q) ≠ ∞`.

This is the *non-constancy half* of the analytic-bridge stack feeding
`MeroSinglePoleExtendsToDeg1Map` (zz337). Combined with zz338's
∞-fibre singleton characterization and a forthcoming regularity-at-`p`
chip, it will assemble the `RegularValueWitnessReg` with `value = ∞`
and `card = 1`.

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

/-- **Existence of a regular companion point.** Under one simple pole at
`p` and holomorphy elsewhere, there is some `q : X` with `q ≠ p`.
(Follows from the chart at `p` having open source — by
`open_nbhd_infinite_of_chartedSpace_complex` — whose underlying set is
infinite.) -/
lemma exists_ne_of_single_simple_pole
    (f : MeromorphicNonzero X) {p : X}
    (_h_pole : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p = ((-1 : ℤ) : WithTop ℤ))
    (_h_holo : ∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    ∃ q : X, q ≠ p := by
  -- The chart at p has open source containing p.
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ p with hc_def
  have hp_src : p ∈ c.source := mem_chart_source ℂ p
  have hSrc_open : IsOpen c.source := c.open_source
  -- Open neighbourhoods in a complex ChartedSpace are infinite.
  have hSrc_inf : c.source.Infinite :=
    open_nbhd_infinite_of_chartedSpace_complex (Y := X) hSrc_open hp_src
  -- An infinite set is nontrivial: it contains two distinct points.
  have hNT : c.source.Nontrivial := hSrc_inf.nontrivial
  -- From nontriviality, extract two distinct points and pick the one ≠ p.
  obtain ⟨a, _ha_src, b, _hb_src, hab⟩ := hNT
  by_cases hap : a = p
  · refine ⟨b, ?_⟩; intro hbp; exact hab (by rw [hap, hbp])
  · exact ⟨a, hap⟩

/-- **Non-constancy of `f.toRiemannSphere` from a single simple pole.**
Under one simple pole at `p` and holomorphy elsewhere,
`f.toRiemannSphere` is non-constant: it equals `∞` at `p` and equals
`some (f.toFun q)` (a *finite* value, not `∞`) at any other point `q`.

This direction does not need `¬ IsConstantMap f.toFun` separately; the
pole alone forces non-constancy of the pole-extension. -/
theorem toRiemannSphere_not_isConstantMap_of_single_simple_pole
    (f : MeromorphicNonzero X) {p : X}
    (h_pole : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p = ((-1 : ℤ) : WithTop ℤ))
    (h_holo : ∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere := by
  -- Pick a witness point `q ≠ p`.
  obtain ⟨q, hq_ne⟩ := exists_ne_of_single_simple_pole f h_pole h_holo
  -- The value at `p` is `∞`.
  have hp_pole : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p < 0 := by
    rw [h_pole]
    exact_mod_cast (show (-1 : ℤ) < 0 from by decide)
  have hFP_eq_infty : f.toRiemannSphere p = (∞ : RiemannSphere) :=
    f.toRiemannSphere_apply_of_neg hp_pole
  -- The value at `q` is `some (f.toFun q)`, which is not `∞`.
  have hQ_nonneg : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun q := h_holo q hq_ne
  have hFQ_eq_some : f.toRiemannSphere q = (OnePoint.some (f.toFun q) : RiemannSphere) :=
    f.toRiemannSphere_apply_of_nonneg hQ_nonneg
  -- `some _` ≠ `∞` in `OnePoint ℂ`.
  have hFQ_ne_infty : f.toRiemannSphere q ≠ (∞ : RiemannSphere) := by
    rw [hFQ_eq_some]
    exact (OnePoint.coe_ne_infty (f.toFun q))
  -- Now derive `¬ ∃ y, ∀ x, F x = y`.
  rintro ⟨y, hy⟩
  -- From `hy p` and `hp_eq` we get `y = ∞`. From `hy q` we'd get
  -- `F q = ∞`, contradicting `hFQ_ne_infty`.
  have hY_eq_infty : y = (∞ : RiemannSphere) := by
    rw [← hy p, hFP_eq_infty]
  have hFQ_eq_infty : f.toRiemannSphere q = (∞ : RiemannSphere) := by
    rw [hy q, hY_eq_infty]
  exact hFQ_ne_infty hFQ_eq_infty

end MeromorphicNonzero

end JacobianChallenge

end
