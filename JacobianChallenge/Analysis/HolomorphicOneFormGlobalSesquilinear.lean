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

/-- **Diagonal of `globalPettersonHermitian` is real-valued.**
Follows from Hermitian symmetry (`H(om, om) = conj(H(om, om))` ⇒
imaginary part vanishes). -/
theorem globalPettersonHermitian_diagonal_im
    (om : HolomorphicOneForm X)
    (f : SmoothPartitionOfUnity X 𝓘(ℝ, ℂ) X (Set.univ : Set X)) :
    (globalPettersonHermitian om om f).im = 0 := by
  -- H(om, om) = conj(H(om, om)) so im = -im, hence im = 0.
  have h_eq : globalPettersonHermitian om om f
      = (starRingEnd ℂ) (globalPettersonHermitian om om f) :=
    globalPettersonHermitian_hermitian om om f
  -- Take imaginary parts: c.im = (conj c).im = -c.im ⇒ 2·c.im = 0 ⇒ c.im = 0.
  have h_im_eq : (globalPettersonHermitian om om f).im
      = ((starRingEnd ℂ) (globalPettersonHermitian om om f)).im := by
    rw [← h_eq]
  rw [Complex.conj_im] at h_im_eq
  -- h_im_eq : (globalPettersonHermitian om om f).im = -(...).im
  linarith

/-! ## Global diagonal nonneg

Lifts the chart-local `chartLocalSesquilinear_diagonal_re_nonneg`
(chip S.5) to the global Petersson Hermitian form, via the
`SmoothPartitionOfUnity.nonneg` field + finite-support extraction. -/

/-- The set of partition-active indices is finite on compact X. -/
private lemma globalPettersonHermitian_finsupp_term
    (om : HolomorphicOneForm X)
    (f : SmoothPartitionOfUnity X 𝓘(ℝ, ℂ) X (Set.univ : Set X)) :
    Set.Finite (Function.support
      (fun y : X => chartLocalSesquilinear om om y (fun x => f.toFun y x))) := by
  -- Support of the term function ⊆ {y | support (f.toFun y) ≠ ∅}.
  have h_lf : LocallyFinite (fun y : X => Function.support (fun x => (f y) x)) :=
    f.locallyFinite
  have h_finite_active :
      {y : X | (Function.support (fun x => (f y) x)).Nonempty}.Finite :=
    h_lf.finite_nonempty_of_compact
  refine h_finite_active.subset ?_
  intro y hy
  by_contra h_empty
  apply hy
  -- h_empty : y ∉ {y | support(f y) is Nonempty} ⇒ support(f y) = ∅ ⇒ f y ≡ 0.
  have h_not_nonempty : ¬ (Function.support (fun x => (f y) x)).Nonempty := h_empty
  have h_support_empty : Function.support (fun x => (f y) x) = ∅ := by
    rw [Set.not_nonempty_iff_eq_empty] at h_not_nonempty
    exact h_not_nonempty
  have h_fy_zero : (fun x => (f y) x) = fun _ => 0 := by
    rw [Function.support_eq_empty_iff] at h_support_empty
    exact h_support_empty
  -- f.toFun y ≡ 0 ⇒ chartLocalSesquilinear om om y (f.toFun y) = 0.
  show chartLocalSesquilinear om om y (fun x => (f y) x) = 0
  unfold chartLocalSesquilinear
  have h_zero : ∀ z : ℂ,
      ((fun x => (f y) x) ((chartAt ℂ y).symm z) : ℂ)
        * localCoeff om y z * (starRingEnd ℂ) (localCoeff om y z) = 0 := by
    intro z
    rw [h_fy_zero]
    simp
  simp [h_zero]

/-- **Global diagonal nonneg.**

For any smooth partition of unity `f`, the real part of the global
Petersson Hermitian form's diagonal is nonneg. -/
theorem globalPettersonHermitian_diagonal_re_nonneg
    (om : HolomorphicOneForm X)
    (f : SmoothPartitionOfUnity X 𝓘(ℝ, ℂ) X (Set.univ : Set X)) :
    0 ≤ (globalPettersonHermitian om om f).re := by
  unfold globalPettersonHermitian
  -- Pull .re inside the finsum via map_finsum on Complex.reCLM (AddMonoidHom).
  rw [show ((∑ᶠ y : X, chartLocalSesquilinear om om y (fun x => f.toFun y x)).re)
        = ∑ᶠ y : X, (chartLocalSesquilinear om om y (fun x => f.toFun y x)).re from ?_]
  · -- Each term .re ≥ 0 by chart-local nonneg + f.nonneg.
    refine finsum_nonneg ?_
    intro y
    refine chartLocalSesquilinear_diagonal_re_nonneg om y ?_
    intro x
    exact f.nonneg y x
  · -- map_finsum for Complex.reCLM.toAddMonoidHom + finite support.
    have h_finsupp := globalPettersonHermitian_finsupp_term om f
    exact (Complex.reCLM.toLinearMap.toAddMonoidHom.map_finsum
      (f := fun y : X => chartLocalSesquilinear om om y (fun x => f.toFun y x))
      h_finsupp)

end HolomorphicOneForm

end
