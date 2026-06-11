/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PartialZBar
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod

set_option linter.unusedSectionVars false

/-! # Integration by parts for `∂̄` on ℂ (Arc 1, chip 2 core)

Two statements, the formal-adjoint toolkit for the L²-Hodge-lite route
(`HANDOFF_ITEM14.md`, ACTIVE ARC):

* **divergence form** — for `h : ℂ → ℂ` of class `C¹` with compact
  support, `∫_ℂ ∂̄h = 0`;
* **adjoint identity** — for `ψ` `C¹` compactly supported and `g` `C¹`,
  `∫ ∂̄ψ · g = −∫ ψ · ∂̄g`.

The second is the identity every orthogonality computation in chips
3–5 consumes: it converts "`β` is L²-orthogonal to `im ∂̄`" into the
weak `∂̄`-condition that chip 1's Weyl lemma
(`Analysis/WeylDBarMollification.lean`) upgrades to holomorphy.

## Proof

`∂̄h = ½(∂₁h + i·∂ᵢh)` pointwise. Transfer `∫_ℂ` to `∫_{ℝ×ℝ}` by the
measure-preserving equivalence `ℂ ≃ᵐ ℝ × ℝ`, apply Fubini in the order
matching the differentiated variable, and kill each line integral with
the 1-D fundamental theorem of calculus for integrable functions
(`integral_eq_zero_of_hasDerivAt_of_integrable`): each slice
`t ↦ h(t + iy)` (resp. `t ↦ h(x + it)`) is `C¹` with compact support.
The adjoint identity is then the Leibniz rule `∂̄(ψg) = ∂̄ψ·g + ψ·∂̄g`
(in tree: `partialZBar_mul`) integrated against the divergence form.

## What this file ships

* `DBarIBP.integral_partialZBar_eq_zero` — the divergence form.
* `DBarIBP.integral_partialZBar_mul` — the adjoint identity.
* Support/continuity helpers for `z ↦ fderiv ℝ h z v` and for the
  real-line slices, reusable by the later L² chips.

No `sorry`, no `axiom`. -/

noncomputable section

open MeasureTheory Metric Filter Function
open scoped Topology

namespace JacobianChallenge

namespace DBarIBP

/-! ## Applied-derivative helpers -/

variable {h : ℂ → ℂ}

/-- The derivative vanishes off the topological support. -/
lemma fderiv_apply_eq_zero_of_notMem_tsupport {z : ℂ}
    (hz : z ∉ tsupport h) (v : ℂ) : fderiv ℝ h z v = 0 := by
  have hzero : h =ᶠ[𝓝 z] 0 := by
    filter_upwards [(isClosed_tsupport h).isOpen_compl.mem_nhds hz] with s hs
    exact image_eq_zero_of_notMem_tsupport hs
  rw [hzero.fderiv_eq]
  simp

/-- `z ↦ (fderiv ℝ h z) v` is continuous for `C¹` `h`. -/
lemma continuous_fderiv_apply (hh : ContDiff ℝ 1 h) (v : ℂ) :
    Continuous fun z => fderiv ℝ h z v :=
  (ContinuousLinearMap.apply ℝ ℂ v).continuous.comp
    (contDiff_one_iff_fderiv.mp hh).2

/-- `z ↦ (fderiv ℝ h z) v` has compact support when `h` does. -/
lemma hasCompactSupport_fderiv_apply (hc : HasCompactSupport h) (v : ℂ) :
    HasCompactSupport fun z => fderiv ℝ h z v := by
  have hsub : Function.support (fun z => fderiv ℝ h z v) ⊆ tsupport h := by
    intro z hz
    by_contra hzn
    exact hz (fderiv_apply_eq_zero_of_notMem_tsupport hzn v)
  exact hc.of_isClosed_subset isClosed_closure
    (closure_minimal hsub (isClosed_tsupport h))

/-- Integrability of the applied derivative. -/
lemma integrable_fderiv_apply (hh : ContDiff ℝ 1 h)
    (hc : HasCompactSupport h) (v : ℂ) :
    Integrable (fun z => fderiv ℝ h z v) volume :=
  (continuous_fderiv_apply hh v).integrable_of_hasCompactSupport
    (hasCompactSupport_fderiv_apply hc v)

/-- `partialZBar h` is continuous for `C¹` `h`. -/
lemma continuous_partialZBar (hh : ContDiff ℝ 1 h) :
    Continuous (partialZBar h) := by
  have h1 := continuous_fderiv_apply hh 1
  have hI := continuous_fderiv_apply hh Complex.I
  exact continuous_const.mul (h1.add (continuous_const.mul hI))

/-- `partialZBar h` vanishes off the support of `h`. -/
lemma support_partialZBar_subset :
    Function.support (partialZBar h) ⊆ tsupport h := by
  intro z hz
  by_contra hzn
  apply hz
  unfold partialZBar
  rw [fderiv_apply_eq_zero_of_notMem_tsupport hzn 1,
    fderiv_apply_eq_zero_of_notMem_tsupport hzn Complex.I]
  simp

/-- `partialZBar h` has compact support when `h` does. -/
lemma hasCompactSupport_partialZBar (hc : HasCompactSupport h) :
    HasCompactSupport (partialZBar h) :=
  hc.of_isClosed_subset isClosed_closure
    (closure_minimal support_partialZBar_subset (isClosed_tsupport h))

/-! ## Real-line slices -/

/-- Horizontal slice of a compactly supported `F : ℂ → ℂ` has compact
support on ℝ. -/
lemma hasCompactSupport_slice_re {F : ℂ → ℂ} (hc : HasCompactSupport F)
    (y : ℝ) : HasCompactSupport fun x : ℝ => F (↑x + ↑y * Complex.I) := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall 0
  have hsub : Function.support (fun x : ℝ => F (↑x + ↑y * Complex.I))
      ⊆ Metric.closedBall (0 : ℝ) R := by
    intro x hx
    have hmem : (↑x + ↑y * Complex.I) ∈ tsupport F :=
      subset_tsupport F hx
    have hnorm : ‖(↑x + ↑y * Complex.I : ℂ)‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hR hmem
    have hre : |x| ≤ ‖(↑x + ↑y * Complex.I : ℂ)‖ := by
      have : ((↑x + ↑y * Complex.I : ℂ)).re = x := by simp
      calc |x| = |((↑x + ↑y * Complex.I : ℂ)).re| := by rw [this]
        _ ≤ ‖(↑x + ↑y * Complex.I : ℂ)‖ := Complex.abs_re_le_norm _
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    linarith
  exact (isCompact_closedBall (0 : ℝ) R).of_isClosed_subset isClosed_closure
    (closure_minimal hsub Metric.isClosed_closedBall)

/-- Vertical slice of a compactly supported `F : ℂ → ℂ` has compact
support on ℝ. -/
lemma hasCompactSupport_slice_im {F : ℂ → ℂ} (hc : HasCompactSupport F)
    (x : ℝ) : HasCompactSupport fun y : ℝ => F (↑x + ↑y * Complex.I) := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall 0
  have hsub : Function.support (fun y : ℝ => F (↑x + ↑y * Complex.I))
      ⊆ Metric.closedBall (0 : ℝ) R := by
    intro y hy
    have hmem : (↑x + ↑y * Complex.I) ∈ tsupport F :=
      subset_tsupport F hy
    have hnorm : ‖(↑x + ↑y * Complex.I : ℂ)‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hR hmem
    have him : |y| ≤ ‖(↑x + ↑y * Complex.I : ℂ)‖ := by
      have : ((↑x + ↑y * Complex.I : ℂ)).im = y := by simp
      calc |y| = |((↑x + ↑y * Complex.I : ℂ)).im| := by rw [this]
        _ ≤ ‖(↑x + ↑y * Complex.I : ℂ)‖ := Complex.abs_im_le_norm _
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    linarith
  exact (isCompact_closedBall (0 : ℝ) R).of_isClosed_subset isClosed_closure
    (closure_minimal hsub Metric.isClosed_closedBall)

/-- The horizontal parametrization `t ↦ ↑t + ↑y·I` is continuous. -/
lemma continuous_param_re (y : ℝ) :
    Continuous fun x : ℝ => (↑x + ↑y * Complex.I : ℂ) :=
  Complex.continuous_ofReal.add continuous_const

/-- The vertical parametrization `t ↦ ↑x + ↑t·I` is continuous. -/
lemma continuous_param_im (x : ℝ) :
    Continuous fun y : ℝ => (↑x + ↑y * Complex.I : ℂ) :=
  continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

/-- Derivative of the horizontal slice: `d/dx h(x + iy) = (Dh)(1)`. -/
lemma hasDerivAt_slice_re (hh : ContDiff ℝ 1 h) (y x : ℝ) :
    HasDerivAt (fun t : ℝ => h (↑t + ↑y * Complex.I))
      (fderiv ℝ h (↑x + ↑y * Complex.I) 1) x := by
  have hγ : HasDerivAt (fun t : ℝ => (↑t + ↑y * Complex.I : ℂ)) 1 x := by
    have h0 : HasDerivAt (fun t : ℝ => (↑t : ℂ)) 1 x := by
      simpa using Complex.ofRealCLM.hasDerivAt
    exact h0.add_const _
  have hf : HasFDerivAt h (fderiv ℝ h (↑x + ↑y * Complex.I))
      (↑x + ↑y * Complex.I) :=
    ((hh.differentiable one_ne_zero) _).hasFDerivAt
  simpa using hf.comp_hasDerivAt x hγ

/-- Derivative of the vertical slice: `d/dy h(x + iy) = (Dh)(I)`. -/
lemma hasDerivAt_slice_im (hh : ContDiff ℝ 1 h) (x y : ℝ) :
    HasDerivAt (fun t : ℝ => h (↑x + ↑t * Complex.I))
      (fderiv ℝ h (↑x + ↑y * Complex.I) Complex.I) y := by
  have hγ : HasDerivAt (fun t : ℝ => (↑x + ↑t * Complex.I : ℂ))
      Complex.I y := by
    have h0 : HasDerivAt (fun t : ℝ => (↑t : ℂ)) 1 y := by
      simpa using Complex.ofRealCLM.hasDerivAt
    simpa using (h0.mul_const Complex.I).const_add (↑x : ℂ)
  have hf : HasFDerivAt h (fderiv ℝ h (↑x + ↑y * Complex.I))
      (↑x + ↑y * Complex.I) :=
    ((hh.differentiable one_ne_zero) _).hasFDerivAt
  simpa using hf.comp_hasDerivAt y hγ

/-! ## Transfer to ℝ × ℝ -/

/-- The measurable equivalence inverse, in `↑x + ↑y·I` form. -/
lemma symm_realProd_eq (p : ℝ × ℝ) :
    Complex.measurableEquivRealProd.symm p = ↑p.1 + ↑p.2 * Complex.I := by
  apply Complex.ext <;>
    simp [Complex.measurableEquivRealProd_symm_apply]

/-- Transfer an integral over ℂ to the explicit `ℝ × ℝ` parametrization. -/
lemma integral_complex_eq_realProd (F : ℂ → ℂ) :
    ∫ z, F z ∂volume
      = ∫ p : ℝ × ℝ, F (↑p.1 + ↑p.2 * Complex.I) ∂volume := by
  rw [← MeasurePreserving.integral_comp
    (Complex.volume_preserving_equiv_real_prod.symm
      Complex.measurableEquivRealProd)
    Complex.measurableEquivRealProd.symm.measurableEmbedding F]
  exact integral_congr_ae (Filter.Eventually.of_forall fun p => by
    show F (Complex.measurableEquivRealProd.symm p)
      = F (↑p.1 + ↑p.2 * Complex.I)
    rw [symm_realProd_eq])

/-- Compact support transfers to the `ℝ × ℝ` parametrization. -/
lemma hasCompactSupport_realProd {F : ℂ → ℂ} (hc : HasCompactSupport F) :
    HasCompactSupport fun p : ℝ × ℝ => F (↑p.1 + ↑p.2 * Complex.I) := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall 0
  have hsub : Function.support (fun p : ℝ × ℝ => F (↑p.1 + ↑p.2 * Complex.I))
      ⊆ Metric.closedBall (0 : ℝ × ℝ) R := by
    intro p hp
    have hmem : (↑p.1 + ↑p.2 * Complex.I) ∈ tsupport F :=
      subset_tsupport F hp
    have hnorm : ‖(↑p.1 + ↑p.2 * Complex.I : ℂ)‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hR hmem
    have hre : |p.1| ≤ R := by
      have hx : ((↑p.1 + ↑p.2 * Complex.I : ℂ)).re = p.1 := by simp
      have := Complex.abs_re_le_norm (↑p.1 + ↑p.2 * Complex.I : ℂ)
      rw [hx] at this
      linarith
    have him : |p.2| ≤ R := by
      have hy : ((↑p.1 + ↑p.2 * Complex.I : ℂ)).im = p.2 := by simp
      have := Complex.abs_im_le_norm (↑p.1 + ↑p.2 * Complex.I : ℂ)
      rw [hy] at this
      linarith
    simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def,
      Real.norm_eq_abs, max_le_iff]
    exact ⟨hre, him⟩
  exact (isCompact_closedBall (0 : ℝ × ℝ) R).of_isClosed_subset
    isClosed_closure (closure_minimal hsub Metric.isClosed_closedBall)

/-! ## The two coordinate integrals vanish -/

/-- `∫_ℂ (Dh)(1) = 0` for compactly supported `C¹` `h`. -/
lemma integral_fderiv_apply_one_eq_zero (hh : ContDiff ℝ 1 h)
    (hc : HasCompactSupport h) :
    ∫ z, fderiv ℝ h z 1 ∂volume = 0 := by
  rw [integral_complex_eq_realProd (fun z => fderiv ℝ h z 1)]
  have hGcont : Continuous
      fun p : ℝ × ℝ => fderiv ℝ h (↑p.1 + ↑p.2 * Complex.I) 1 :=
    (continuous_fderiv_apply hh 1).comp
      ((Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul
          continuous_const))
  have hGint : Integrable
      (fun p : ℝ × ℝ => fderiv ℝ h (↑p.1 + ↑p.2 * Complex.I) 1) volume :=
    hGcont.integrable_of_hasCompactSupport
      (hasCompactSupport_realProd (hasCompactSupport_fderiv_apply hc 1))
  rw [Measure.volume_eq_prod ℝ ℝ] at hGint ⊢
  rw [integral_prod_symm _ hGint]
  have hinner : ∀ y : ℝ,
      ∫ x : ℝ, fderiv ℝ h (↑x + ↑y * Complex.I) 1 = 0 := by
    intro y
    apply integral_eq_zero_of_hasDerivAt_of_integrable
      (f := fun x : ℝ => h (↑x + ↑y * Complex.I))
    · exact fun x => hasDerivAt_slice_re hh y x
    · exact ((continuous_fderiv_apply hh 1).comp
          (continuous_param_re y)).integrable_of_hasCompactSupport
        (hasCompactSupport_slice_re (hasCompactSupport_fderiv_apply hc 1) y)
    · exact ((hh.continuous).comp
          (continuous_param_re y)).integrable_of_hasCompactSupport
        (hasCompactSupport_slice_re hc y)
  simp only [hinner, integral_zero]

/-- `∫_ℂ (Dh)(I) = 0` for compactly supported `C¹` `h`. -/
lemma integral_fderiv_apply_I_eq_zero (hh : ContDiff ℝ 1 h)
    (hc : HasCompactSupport h) :
    ∫ z, fderiv ℝ h z Complex.I ∂volume = 0 := by
  rw [integral_complex_eq_realProd (fun z => fderiv ℝ h z Complex.I)]
  have hGcont : Continuous
      fun p : ℝ × ℝ => fderiv ℝ h (↑p.1 + ↑p.2 * Complex.I) Complex.I :=
    (continuous_fderiv_apply hh Complex.I).comp
      ((Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul
          continuous_const))
  have hGint : Integrable
      (fun p : ℝ × ℝ => fderiv ℝ h (↑p.1 + ↑p.2 * Complex.I) Complex.I)
      volume :=
    hGcont.integrable_of_hasCompactSupport
      (hasCompactSupport_realProd
        (hasCompactSupport_fderiv_apply hc Complex.I))
  rw [Measure.volume_eq_prod ℝ ℝ] at hGint ⊢
  rw [integral_prod _ hGint]
  have hinner : ∀ x : ℝ,
      ∫ y : ℝ, fderiv ℝ h (↑x + ↑y * Complex.I) Complex.I = 0 := by
    intro x
    apply integral_eq_zero_of_hasDerivAt_of_integrable
      (f := fun y : ℝ => h (↑x + ↑y * Complex.I))
    · exact fun y => hasDerivAt_slice_im hh x y
    · exact ((continuous_fderiv_apply hh Complex.I).comp
          (continuous_param_im x)).integrable_of_hasCompactSupport
        (hasCompactSupport_slice_im
          (hasCompactSupport_fderiv_apply hc Complex.I) x)
    · exact ((hh.continuous).comp
          (continuous_param_im x)).integrable_of_hasCompactSupport
        (hasCompactSupport_slice_im hc x)
  simp only [hinner, integral_zero]

/-! ## Headlines -/

/-- **Divergence form: `∫_ℂ ∂̄h = 0`** for compactly supported `C¹` `h`. -/
theorem integral_partialZBar_eq_zero (hh : ContDiff ℝ 1 h)
    (hc : HasCompactSupport h) :
    ∫ z, partialZBar h z ∂volume = 0 := by
  have h1 := integral_fderiv_apply_one_eq_zero hh hc
  have hI := integral_fderiv_apply_I_eq_zero hh hc
  have hint1 := integrable_fderiv_apply hh hc 1
  have hintI := integrable_fderiv_apply hh hc Complex.I
  calc ∫ z, partialZBar h z ∂volume
      = ∫ z, (2 : ℂ)⁻¹ * (fderiv ℝ h z 1
          + Complex.I * fderiv ℝ h z Complex.I) ∂volume := rfl
    _ = (2 : ℂ)⁻¹ * ∫ z, (fderiv ℝ h z 1
          + Complex.I * fderiv ℝ h z Complex.I) ∂volume :=
        integral_const_mul _ _
    _ = (2 : ℂ)⁻¹ * ((∫ z, fderiv ℝ h z 1 ∂volume)
          + ∫ z, Complex.I * fderiv ℝ h z Complex.I ∂volume) := by
        rw [integral_add hint1 (hintI.const_mul Complex.I)]
    _ = (2 : ℂ)⁻¹ * ((∫ z, fderiv ℝ h z 1 ∂volume)
          + Complex.I * ∫ z, fderiv ℝ h z Complex.I ∂volume) := by
        congr 1
        congr 1
        exact integral_const_mul Complex.I fun z => fderiv ℝ h z Complex.I
    _ = (2 : ℂ)⁻¹ * (0 + Complex.I * 0) := by rw [h1, hI]
    _ = 0 := by ring

variable {ψ g : ℂ → ℂ}

/-- **Adjoint identity: `∫ ∂̄ψ · g = −∫ ψ · ∂̄g`** for `ψ` compactly
supported `C¹` and `g` `C¹`. This is the formal-adjoint relation the
L² orthogonality computations consume. -/
theorem integral_partialZBar_mul (hψ : ContDiff ℝ 1 ψ)
    (hcψ : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) :
    ∫ z, partialZBar ψ z * g z ∂volume
      = -∫ z, ψ z * partialZBar g z ∂volume := by
  have hprod : ContDiff ℝ 1 (ψ * g) := hψ.mul hg
  have hcprod : HasCompactSupport (ψ * g) := hcψ.mul_right
  have h0 := integral_partialZBar_eq_zero hprod hcprod
  have hsplit : ∀ z, partialZBar (ψ * g) z
      = partialZBar ψ z * g z + ψ z * partialZBar g z := fun z =>
    partialZBar_mul ((hψ.differentiable one_ne_zero) z)
      ((hg.differentiable one_ne_zero) z)
  -- integrabilities of the two summands
  have hint_a : Integrable (fun z => partialZBar ψ z * g z) volume := by
    refine (((continuous_partialZBar hψ).mul hg.continuous)).integrable_of_hasCompactSupport ?_
    refine (hasCompactSupport_partialZBar hcψ).of_isClosed_subset
      isClosed_closure (closure_minimal ?_ (isClosed_tsupport _))
    intro z hz
    have : partialZBar ψ z ≠ 0 := fun h0' => hz (by simp [h0'])
    exact subset_tsupport _ this
  have hint_b : Integrable (fun z => ψ z * partialZBar g z) volume := by
    refine ((hψ.continuous.mul (continuous_partialZBar hg))).integrable_of_hasCompactSupport ?_
    refine hcψ.of_isClosed_subset isClosed_closure
      (closure_minimal ?_ (isClosed_tsupport _))
    intro z hz
    have : ψ z ≠ 0 := fun h0' => hz (by simp [h0'])
    exact subset_tsupport _ this
  have hsum : (∫ z, partialZBar ψ z * g z ∂volume)
      + ∫ z, ψ z * partialZBar g z ∂volume = 0 := by
    rw [← integral_add hint_a hint_b]
    rw [← h0]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z =>
      (hsplit z).symm)
  exact eq_neg_of_add_eq_zero_left hsum

end DBarIBP

end JacobianChallenge

end
