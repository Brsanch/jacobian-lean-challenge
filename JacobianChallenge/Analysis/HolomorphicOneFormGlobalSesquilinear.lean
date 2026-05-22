/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.HolomorphicOneFormChartLocalSesquilinear
import JacobianChallenge.Analysis.RealModelManifoldFromComplex
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Global Petersson Hermitian form via partition-of-unity sum

Chip **S.2** of arc S (surface integration assembly). The
ℂ-valued analog of chip D₃'s `globalPettersonL2Sq`:

```
HolomorphicOneForm.globalPettersonHermitian om eta f
  : ℂ
  := ∑ᶠ y, chartLocalSesquilinear om eta y (f.toFun y)
```

i.e. each chart at `y : X` contributes a chart-local Bochner-integrated
Hermitian pairing with the partition function `f y`, summed via
`finsum` over the locally-finite support of the partition.

Specialized to `om = eta`, this is the diagonal Petersson L²-square
norm; specifically, its real part equals `(globalPettersonL2Sq om f).toReal`
(modulo coercion). The off-diagonal pairing is the substantive content
that will be identified with the period-matrix Hermitian form in
downstream chips (arc S).

This chip ships:
* `globalPettersonHermitian` — the definition;
* `globalPettersonHermitian_zero_left` — zero on the zero `om`;
* `globalPettersonHermitian_zero_right` — zero on the zero `eta`;
* `globalPettersonHermitian_hermitian` — Hermitian symmetry
  `H(om, eta) = conj(H(eta, om))`.

ℂ-linearity in `om` and conj-linearity in `eta` follow from
`localCoeff`'s linearity + `integral_add`/`integral_smul`; deferred to
a follow-up chip.

No `sorry`, no `axiom`. -/

set_option linter.unusedSectionVars false

noncomputable section

open scoped Manifold ContDiff ComplexConjugate
open MeasureTheory ENNReal NNReal Complex

namespace HolomorphicOneForm

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Global Petersson Hermitian form** built from a smooth partition of
unity subordinate to the chart-source cover. ℂ-valued. -/
def globalPettersonHermitian (om eta : HolomorphicOneForm X)
    (f : SmoothPartitionOfUnity X 𝓘(ℝ, ℂ) X (Set.univ : Set X)) : ℂ :=
  ∑ᶠ y, chartLocalSesquilinear om eta y (fun x => f.toFun y x)

/-- **Global form of the zero `om` is zero**, on every partition. -/
@[simp]
lemma globalPettersonHermitian_zero_left (eta : HolomorphicOneForm X)
    (f : SmoothPartitionOfUnity X 𝓘(ℝ, ℂ) X (Set.univ : Set X)) :
    globalPettersonHermitian (0 : HolomorphicOneForm X) eta f = 0 := by
  unfold globalPettersonHermitian
  simp [chartLocalSesquilinear_zero_left]

/-- **Global form with the zero `eta` is zero**, on every partition. -/
@[simp]
lemma globalPettersonHermitian_zero_right (om : HolomorphicOneForm X)
    (f : SmoothPartitionOfUnity X 𝓘(ℝ, ℂ) X (Set.univ : Set X)) :
    globalPettersonHermitian om (0 : HolomorphicOneForm X) f = 0 := by
  unfold globalPettersonHermitian
  simp [chartLocalSesquilinear_zero_right]

/-- **Hermitian symmetry of the global Petersson form**: swapping
`om` and `eta` conjugates the value. -/
theorem globalPettersonHermitian_hermitian
    (om eta : HolomorphicOneForm X)
    (f : SmoothPartitionOfUnity X 𝓘(ℝ, ℂ) X (Set.univ : Set X)) :
    globalPettersonHermitian om eta f
      = (starRingEnd ℂ) (globalPettersonHermitian eta om f) := by
  unfold globalPettersonHermitian
  -- Each term: chartLocalSesquilinear om eta y _ = conj (chartLocalSesquilinear eta om y _).
  -- Sum of conj = conj of sum.
  rw [show (fun y : X => chartLocalSesquilinear om eta y (fun x => f.toFun y x))
        = (fun y : X => (starRingEnd ℂ)
            (chartLocalSesquilinear eta om y (fun x => f.toFun y x)))
        from funext fun y => chartLocalSesquilinear_hermitian om eta y _]
  -- ∑ᶠ y, conj (g y) = conj (∑ᶠ y, g y) — finsum commutes with the
  -- injective additive monoid hom `(starRingEnd ℂ).toAddMonoidHom`.
  have h_inj : Function.Injective (starRingEnd ℂ) := by
    intro a b hab
    have : star a = star b := hab
    exact star_injective this
  exact ((starRingEnd ℂ).toAddMonoidHom.map_finsum_of_injective h_inj
    (fun y => chartLocalSesquilinear eta om y (fun x => f.toFun y x))).symm

end HolomorphicOneForm

end
