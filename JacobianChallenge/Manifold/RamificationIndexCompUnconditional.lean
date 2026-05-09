/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RamificationIndexChain
import JacobianChallenge.Manifold.RamificationIndexPositive
import JacobianChallenge.Manifold.ChartOverlapPropagationDischarge
import JacobianChallenge.Manifold.ClopennessOfLocallyConstDischarge

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Unconditional chain rule for `manifoldRamificationIndex`

`RamificationIndexChain.manifoldRamificationIndex_comp_of_finite` provides
the chain rule for `ContMDiff` analytic maps `f : X → Y` and `g : Y → Z`
*conditional* on the finite-positivity hypotheses
`1 ≤ manifoldRamificationIndex f x` and
`1 ≤ manifoldRamificationIndex g (f x)`.

This file discharges those hypotheses *unconditionally* on compact
connected complex 1-manifolds. The positivity at every fibre point of a
non-constant `ContMDiff` map is supplied by
`manifoldRamificationIndex_pos_at_fibre_of_perChartNonConstancy`
(`Manifold/RamificationIndexPositive.lean`), which itself becomes
unconditional after composing with
`perChartNonConstancy_of_clopennessOfLocallyConst` and
`clopennessOfLocallyConst_holds`.

The result is a clean chain rule
```
manifoldRamificationIndex (g ∘ f) x =
  manifoldRamificationIndex g (f x) * manifoldRamificationIndex f x
```
for non-constant `f : X → Y` and non-constant `g : Y → Z`, with no
finite-positivity sidedata required.

This is the chain-rule input that lets the multiplicity-weighted body of
`Jacobian.pullback` satisfy contravariant composition without leaking the
positivity hypotheses upstream.

No `sorry`, no `axiom`. -/

@[expose] public section

open Set Filter Topology
open scoped Manifold Topology ContDiff

namespace JacobianChallenge

namespace Manifold

universe u v w

/-- **Unconditional chain rule for `manifoldRamificationIndex`.**

For non-constant `ContMDiff` analytic maps `f : X → Y` and `g : Y → Z`
between compact connected complex 1-manifolds, the manifold ramification
indices multiply through composition at every base point. -/
theorem manifoldRamificationIndex_comp_unconditional
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
      [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
      [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    {Z : Type w} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
      [ChartedSpace ℂ Z] [IsManifold (𝓘(ℂ, ℂ)) ω Z]
    (f : X → Y) (g : Y → Z)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hf_nc : ¬ JacobianChallenge.IsConstantMap f)
    (hg_nc : ¬ JacobianChallenge.IsConstantMap g)
    (x : X) :
    JacobianChallenge.Manifold.manifoldRamificationIndex (g ∘ f) x =
      JacobianChallenge.Manifold.manifoldRamificationIndex g (f x) *
      JacobianChallenge.Manifold.manifoldRamificationIndex f x := by
  -- Unconditional `PerChartNonConstancyHypothesis` for X → Y and Y → Z.
  have HXY :
      JacobianChallenge.ContMDiff.Owed.degree.PerChartNonConstancyHypothesis X Y :=
    JacobianChallenge.ContMDiff.Owed.degree.perChartNonConstancy_of_clopennessOfLocallyConst
      (JacobianChallenge.ContMDiff.Owed.degree.clopennessOfLocallyConst_holds)
  have HYZ :
      JacobianChallenge.ContMDiff.Owed.degree.PerChartNonConstancyHypothesis Y Z :=
    JacobianChallenge.ContMDiff.Owed.degree.perChartNonConstancy_of_clopennessOfLocallyConst
      (JacobianChallenge.ContMDiff.Owed.degree.clopennessOfLocallyConst_holds)
  -- Positivity of `manifoldRamificationIndex f x`.
  have hf_pos : 1 ≤ manifoldRamificationIndex f x :=
    manifoldRamificationIndex_pos_at_fibre_of_perChartNonConstancy
      HXY hf hf_nc (rfl : f x = f x)
  -- Positivity of `manifoldRamificationIndex g (f x)`.
  have hg_pos : 1 ≤ manifoldRamificationIndex g (f x) :=
    manifoldRamificationIndex_pos_at_fibre_of_perChartNonConstancy
      HYZ hg hg_nc (rfl : g (f x) = g (f x))
  -- Apply the chain rule with the now-discharged hypotheses.
  exact manifoldRamificationIndex_comp_of_finite x
    hf.contMDiffAt hg.contMDiffAt hf_pos hg_pos

/-- **Pointwise form of the chain rule.** At every fibre point `x` of
`(g ∘ f)` over `z`, the ramification index of the composition factors as
the product of the indices of `g` at `f x` and of `f` at `x`. -/
theorem manifoldRamificationIndex_comp_eq_product_pointwise
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
      [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
      [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    {Z : Type w} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
      [ChartedSpace ℂ Z] [IsManifold (𝓘(ℂ, ℂ)) ω Z]
    (f : X → Y) (g : Y → Z)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hf_nc : ¬ JacobianChallenge.IsConstantMap f)
    (hg_nc : ¬ JacobianChallenge.IsConstantMap g)
    (z : Z) (x : X) (_hx : (g ∘ f) x = z) :
    JacobianChallenge.Manifold.manifoldRamificationIndex (g ∘ f) x =
      JacobianChallenge.Manifold.manifoldRamificationIndex g (f x) *
      JacobianChallenge.Manifold.manifoldRamificationIndex f x :=
  manifoldRamificationIndex_comp_unconditional f g hf hg hf_nc hg_nc x

end Manifold

end JacobianChallenge
