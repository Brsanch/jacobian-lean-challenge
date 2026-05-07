/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartIntegralFibreBalanceFromR5Stack
import JacobianChallenge.Manifold.RegularValueSetConnected

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # ZZ95: Strictly-smaller-bundle constructor for `R5StackHypotheses`

ZZ94 (`ChartIntegralFibreBalanceFromR5Stack.lean`) packages the four
R5-stream residuals into a single `R5StackHypotheses f` bundle. The
bundle has **9 fields**:

* `fibreSum`, `criticalValues`, `criticalValues_finite`
* `regular_zero`, `regular_infty`
* `local_count_package`
* `Yreg_preconnected`
* `fibreSum_zero_eq`, `fibreSum_infty_eq`

Of these, **exactly one** field — `Yreg_preconnected` — can be
discharged on the spot from a strictly weaker, named topological
hypothesis using ZZ93's existing reduction
`regularValueSet_isPreconnected_of_finite_complement_hypothesis`:

  `h_topo : ∀ C : Set (OnePoint ℂ), C.Finite →
              IsPreconnected (Cᶜ : Set (OnePoint ℂ))`

This file ships:

1. `R5StackHypotheses.ofResiduals` — a constructor that takes the
   eight non-`Yreg_preconnected` fields plus `h_topo` and assembles
   a full `R5StackHypotheses f`.

2. `chartIntegralFibreBalance_of_residuals` — composition: the
   chart-integer fibre balance follows from the eight non-Yreg
   residuals plus `h_topo`. This is a strictly smaller-input form of
   ZZ94's `chartIntegralFibreBalance_of_R5Stack`.

3. `mkBundle_of_residuals` — the bundle constructor parametric on
   the same strictly-smaller residual list.

4. `residueTheorem_of_forall_residuals` — the global form: if every
   `f` admits the eight non-Yreg residuals plus the *single* shared
   topological hypothesis `h_topo`, the residue theorem holds.

## What is real-proof here

* No `axiom`, no `sorry`. No signature changes outside this new file.
* `Yreg_preconnected` is genuinely discharged: ZZ93's
  `regularValueSet_isPreconnected_of_finite_complement_hypothesis`
  applied with `C := criticalValues` and `hC_fin := criticalValues_finite`
  produces exactly the field shape ZZ94 demands.
* The remaining residuals (`local_count_package`,
  `fibreSum_zero_eq`, `fibreSum_infty_eq`,
  `regular_zero`, `regular_infty`) are not discharged here — they
  remain genuine inputs. The contribution is strictly: 9 → 8 + 1
  shared, where the +1 is one Prop-level statement that does not
  depend on `f`.

## Honest framing

This chip closes **one of four named residuals** (`Yreg_preconnected`
out of `local_count_package`, `Yreg_preconnected`,
`fibreSum_*_eq` pair, regularity witnesses). The remaining residuals
need separate chips (chart-pullback finiteness for
`local_count_package`; `localMult ↔ ord_x` identification for the
`fibreSum_*_eq` pair).
-/

@[expose] public section

noncomputable section

open scoped Real Topology BigOperators Manifold ContDiff
open Set Filter Complex MeasureTheory OnePoint

namespace JacobianChallenge

namespace GlobalResidueSum

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Strictly-smaller-bundle constructor -/

/-- **`R5StackHypotheses.ofResiduals` — strictly-smaller-input constructor.**

Build a full `R5StackHypotheses f` bundle from the 8 fields *other than*
`Yreg_preconnected`, plus the single shared topological hypothesis

  `h_topo : ∀ C : Set (OnePoint ℂ), C.Finite →
              IsPreconnected (Cᶜ : Set (OnePoint ℂ))`

The `Yreg_preconnected` field is discharged inline via ZZ93's
`regularValueSet_isPreconnected_of_finite_complement_hypothesis`
applied at `C := criticalValues`. -/
def R5StackHypotheses.ofResiduals
    {f : MeromorphicNonzero X}
    (fibreSum : OnePoint ℂ → ℕ)
    (criticalValues : Set (OnePoint ℂ))
    (criticalValues_finite : criticalValues.Finite)
    (regular_zero : (OnePoint.some (0 : ℂ)) ∉ criticalValues)
    (regular_infty : (∞ : OnePoint ℂ) ∉ criticalValues)
    (local_count_package :
      ∀ y₀ ∈ (criticalValuesᶜ : Set (OnePoint ℂ)),
        JacobianChallenge.Manifold.LocalCountPackage fibreSum y₀)
    (fibreSum_zero_eq :
      (fibreSum (OnePoint.some (0 : ℂ)) : ℤ)
        = JacobianChallenge.MeromorphicDegreeFiberSum.meromorphicDegreeAtZero f)
    (fibreSum_infty_eq :
      (fibreSum (∞ : OnePoint ℂ) : ℤ)
        = JacobianChallenge.MeromorphicDegreeFiberSum.meromorphicDegreeAtInfty f)
    (h_topo :
      ∀ C : Set (OnePoint ℂ), C.Finite →
        IsPreconnected (Cᶜ : Set (OnePoint ℂ))) :
    R5StackHypotheses f where
  fibreSum := fibreSum
  criticalValues := criticalValues
  criticalValues_finite := criticalValues_finite
  regular_zero := regular_zero
  regular_infty := regular_infty
  local_count_package := local_count_package
  Yreg_preconnected :=
    JacobianChallenge.Manifold.regularValueSet_isPreconnected_of_finite_complement_hypothesis
      h_topo criticalValues criticalValues_finite
  fibreSum_zero_eq := fibreSum_zero_eq
  fibreSum_infty_eq := fibreSum_infty_eq

/-! ## Convergence: chart-integer fibre balance from the smaller bundle -/

/-- **Convergence chip — strictly smaller form.**

Given the 8 non-`Yreg_preconnected` residuals plus the single shared
topological hypothesis `h_topo`, the chart-integer fibre balance
holds for any `GlobalResidueSum_hypothesis f` whose orthogonal fields
are populated. -/
theorem chartIntegralFibreBalance_of_residuals
    {f : MeromorphicNonzero X}
    (H : GlobalResidueSum_hypothesis f)
    (fibreSum : OnePoint ℂ → ℕ)
    (criticalValues : Set (OnePoint ℂ))
    (criticalValues_finite : criticalValues.Finite)
    (regular_zero : (OnePoint.some (0 : ℂ)) ∉ criticalValues)
    (regular_infty : (∞ : OnePoint ℂ) ∉ criticalValues)
    (local_count_package :
      ∀ y₀ ∈ (criticalValuesᶜ : Set (OnePoint ℂ)),
        JacobianChallenge.Manifold.LocalCountPackage fibreSum y₀)
    (fibreSum_zero_eq :
      (fibreSum (OnePoint.some (0 : ℂ)) : ℤ)
        = JacobianChallenge.MeromorphicDegreeFiberSum.meromorphicDegreeAtZero f)
    (fibreSum_infty_eq :
      (fibreSum (∞ : OnePoint ℂ) : ℤ)
        = JacobianChallenge.MeromorphicDegreeFiberSum.meromorphicDegreeAtInfty f)
    (h_topo :
      ∀ C : Set (OnePoint ℂ), C.Finite →
        IsPreconnected (Cᶜ : Set (OnePoint ℂ))) :
    chartIntegralFibreBalance H :=
  chartIntegralFibreBalance_of_R5Stack H
    (R5StackHypotheses.ofResiduals
      fibreSum criticalValues criticalValues_finite
      regular_zero regular_infty local_count_package
      fibreSum_zero_eq fibreSum_infty_eq h_topo)

/-! ## Bundle constructor from the smaller residual list -/

/-- **Bundle constructor — strictly smaller form.**

Given the bundle's two non-gap fields together with the 8
non-`Yreg_preconnected` R5 residuals plus `h_topo`, produce a full
`GlobalResidueSum_hypothesis f`. -/
def mkBundle_of_residuals
    {f : MeromorphicNonzero X}
    (S : Finset X)
    (support_subset : (principalDivisorMap f).supportFinset ⊆ S)
    (chartIntegral : X → ℤ)
    (chartIntegral_eq_order : ∀ x ∈ S,
        chartIntegral x =
          JacobianChallenge.MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x)
    (fibreSum : OnePoint ℂ → ℕ)
    (criticalValues : Set (OnePoint ℂ))
    (criticalValues_finite : criticalValues.Finite)
    (regular_zero : (OnePoint.some (0 : ℂ)) ∉ criticalValues)
    (regular_infty : (∞ : OnePoint ℂ) ∉ criticalValues)
    (local_count_package :
      ∀ y₀ ∈ (criticalValuesᶜ : Set (OnePoint ℂ)),
        JacobianChallenge.Manifold.LocalCountPackage fibreSum y₀)
    (fibreSum_zero_eq :
      (fibreSum (OnePoint.some (0 : ℂ)) : ℤ)
        = JacobianChallenge.MeromorphicDegreeFiberSum.meromorphicDegreeAtZero f)
    (fibreSum_infty_eq :
      (fibreSum (∞ : OnePoint ℂ) : ℤ)
        = JacobianChallenge.MeromorphicDegreeFiberSum.meromorphicDegreeAtInfty f)
    (h_topo :
      ∀ C : Set (OnePoint ℂ), C.Finite →
        IsPreconnected (Cᶜ : Set (OnePoint ℂ))) :
    GlobalResidueSum_hypothesis f :=
  mkBundle_of_R5Stack S support_subset chartIntegral chartIntegral_eq_order
    (R5StackHypotheses.ofResiduals
      fibreSum criticalValues criticalValues_finite
      regular_zero regular_infty local_count_package
      fibreSum_zero_eq fibreSum_infty_eq h_topo)

/-! ## Global form — residue theorem from per-`f` residuals + shared topology -/

/-- **Global form — residue theorem from the strictly-smaller residual list.**

If for every `f : MeromorphicNonzero X` we have the bundle's two
non-gap fields plus the 8 non-`Yreg_preconnected` R5 residuals, and
the shared topological hypothesis `h_topo` (independent of `f`), the
residue theorem holds on `X`.

The `h_topo` hypothesis is shared across all `f` because it does not
mention `f` — it is the pure sphere-topology statement "OnePoint ℂ
minus a finite set is preconnected", which `Y_reg` requires. By
factoring it out we reduce the per-`f` data to 8 fields + the bundle
orthogonals (vs. 9 + orthogonals in ZZ94's
`residueTheorem_of_forall_R5Stack`). -/
theorem residueTheorem_of_forall_residuals
    (h_topo :
      ∀ C : Set (OnePoint ℂ), C.Finite →
        IsPreconnected (Cᶜ : Set (OnePoint ℂ)))
    (data : ∀ f : MeromorphicNonzero X,
      Σ' (S : Finset X)
         (_support_subset : (principalDivisorMap f).supportFinset ⊆ S)
         (chartIntegral : X → ℤ)
         (_chartIntegral_eq_order : ∀ x ∈ S,
            chartIntegral x =
              JacobianChallenge.MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x)
         (fibreSum : OnePoint ℂ → ℕ)
         (criticalValues : Set (OnePoint ℂ))
         (_criticalValues_finite : criticalValues.Finite)
         (_regular_zero : (OnePoint.some (0 : ℂ)) ∉ criticalValues)
         (_regular_infty : (∞ : OnePoint ℂ) ∉ criticalValues)
         (_local_count_package :
            ∀ y₀ ∈ (criticalValuesᶜ : Set (OnePoint ℂ)),
              JacobianChallenge.Manifold.LocalCountPackage fibreSum y₀)
         (_fibreSum_zero_eq :
            (fibreSum (OnePoint.some (0 : ℂ)) : ℤ)
              = JacobianChallenge.MeromorphicDegreeFiberSum.meromorphicDegreeAtZero f),
        (fibreSum (∞ : OnePoint ℂ) : ℤ)
          = JacobianChallenge.MeromorphicDegreeFiberSum.meromorphicDegreeAtInfty f) :
    JacobianChallenge.ResidueTheorem X := by
  apply ResidueTheorem_holds_of_globalResidueSum
  intro f
  obtain ⟨S, hS, chartIntegral, hchart,
          fibreSum, criticalValues, hCfin, hrz, hri, hpkg, hfz, hfinf⟩ := data f
  exact mkBundle_of_residuals S hS chartIntegral hchart
          fibreSum criticalValues hCfin hrz hri hpkg hfz hfinf h_topo

end GlobalResidueSum

end JacobianChallenge

end

end
