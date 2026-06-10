/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Order.ProjIcc

set_option linter.unusedSectionVars false

/-! # The exp-identity for log-derivative integrals, and winding integrality

The analytic engine of the `TLDivSumHypothesis` contour arc
(`HANDOFF_TLDIVSUM.md`, pieces 2 and keystone-1):

* `exp_integral_logDeriv` — for `φ : ℝ → ℂ` with continuous derivative
  data and no zeros on `[0,1]`:
  `exp (∫ t in 0..1, φ' t / φ t) = φ 1 / φ 0`.
  Proof: `h := exp (−ψ) · φ` with `ψ` the primitive of `φ'/φ` has zero
  derivative, hence is constant on `[0,1]`.
* `integral_logDeriv_closed_mem` — closed loop (`φ 1 = φ 0`): the
  integral lies in `2πi·ℤ`.
* `sum_integral_logDeriv_chain_mem` — **cyclic chain version**: for
  segments `φ i` with `φ i 1 = φ (i+1) 0` cyclically (`i : Fin n`), the
  *sum* of the segment integrals lies in `2πi·ℤ` (the product of the
  endpoint quotients telescopes to `1`). With `n = 4` and affine
  segments this is the integrality half of the parallelogram keystone
  `∮_{∂Π} dz/(z−x) ∈ 2πi·ℤ`, and with `n = 1` it recovers the closed
  loop case used for the period-side windings `Δ_h, Δ_v`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set MeasureTheory intervalIntegral
open scoped Real

namespace JacobianChallenge

namespace LogDerivWinding

/-! ## The exp-identity -/

/-- **Exp-identity for the log-derivative integral.** If `φ` has
derivative `φ'` at every point of `[0,1]`, `φ'` is continuous on `[0,1]`,
and `φ` never vanishes on `[0,1]`, then
`exp (∫ t in 0..1, φ' t / φ t) = φ 1 / φ 0`. -/
theorem exp_integral_logDeriv {φ φ' : ℝ → ℂ}
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (Icc (0 : ℝ) 1))
    (hne : ∀ t ∈ Icc (0 : ℝ) 1, φ t ≠ 0) :
    Complex.exp (∫ t in (0 : ℝ)..1, φ' t / φ t) = φ 1 / φ 0 := by
  classical
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  -- The integrand, continuous on `[0,1]`.
  set q : ℝ → ℂ := fun t => φ' t / φ t with hq_def
  have hφcont : ContinuousOn φ (Icc (0 : ℝ) 1) := fun t ht =>
    (hd t ht).continuousAt.continuousWithinAt
  have hqc : ContinuousOn q (Icc (0 : ℝ) 1) := hc.div hφcont hne
  -- Globalize the integrand by clamping to `[0,1]`.
  set qext : ℝ → ℂ := IccExtend h01 ((Icc (0 : ℝ) 1).restrict q)
    with hqext_def
  have hqext_cont : Continuous qext :=
    Continuous.Icc_extend' (continuousOn_iff_continuous_restrict.mp hqc)
  have hqext_eq : ∀ t ∈ Icc (0 : ℝ) 1, qext t = q t := by
    intro t ht
    rw [hqext_def, IccExtend_of_mem h01 _ ht]
    rfl
  -- The primitive of the globalized integrand.
  set ψ : ℝ → ℂ := fun u => ∫ s in (0 : ℝ)..u, qext s with hψ_def
  have hψd : ∀ u : ℝ, HasDerivAt ψ (qext u) u := by
    intro u
    exact integral_hasDerivAt_right
      (hqext_cont.intervalIntegrable 0 u)
      (hqext_cont.stronglyMeasurable.stronglyMeasurableAtFilter)
      hqext_cont.continuousAt
  -- The auxiliary function with zero derivative.
  set h : ℝ → ℂ := fun t => Complex.exp (-ψ t) * φ t with hh_def
  have hh_deriv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt h 0 t := by
    intro t ht
    have h1 : HasDerivAt (fun u => Complex.exp (-ψ u))
        (-qext t * Complex.exp (-ψ t)) t := by
      have h2 : HasDerivAt (fun u => -ψ u) (-qext t) t := (hψd t).neg
      have h3 := h2.cexp
      -- h3 : HasDerivAt (fun u => exp (-ψ u)) (exp (-ψ t) * -qext t) t
      convert h3 using 1
      ring
    have h4 : HasDerivAt h
        ((-qext t * Complex.exp (-ψ t)) * φ t
          + Complex.exp (-ψ t) * φ' t) t :=
      h1.mul (hd t ht)
    have h5 : (-qext t * Complex.exp (-ψ t)) * φ t
        + Complex.exp (-ψ t) * φ' t = 0 := by
      rw [hqext_eq t ht, hq_def]
      have hφt : φ t ≠ 0 := hne t ht
      field_simp
      ring
    rw [h5] at h4
    exact h4
  -- Constancy on `[0,1]`.
  have hh_cont : ContinuousOn h (Icc (0 : ℝ) 1) := fun t ht =>
    (hh_deriv t ht).continuousAt.continuousWithinAt
  have hh_const : h 1 = h 0 := by
    have := constant_of_has_deriv_right_zero hh_cont
      (fun t ht => (hh_deriv t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    exact this 1 (right_mem_Icc.mpr h01)
  -- Unwind.
  have hψ0 : ψ 0 = 0 := integral_same
  have hψ1 : ψ 1 = ∫ t in (0 : ℝ)..1, q t := by
    rw [hψ_def]
    apply integral_congr
    intro t ht
    rw [uIcc_of_le h01] at ht
    exact hqext_eq t ht
  have hφ0 : φ 0 ≠ 0 := hne 0 (left_mem_Icc.mpr h01)
  -- From `h 1 = h 0`: `exp (−ψ 1) · φ 1 = φ 0`.
  rw [hh_def] at hh_const
  simp only [hψ0, neg_zero, Complex.exp_zero, one_mul] at hh_const
  -- Hence `exp (ψ 1) = φ 1 / φ 0`.
  have hexp_ne : Complex.exp (-ψ 1) ≠ 0 := Complex.exp_ne_zero _
  have hφ1 : φ 1 ≠ 0 := hne 1 (right_mem_Icc.mpr h01)
  rw [← hψ1, ← hh_const]
  rw [eq_div_iff (mul_ne_zero hexp_ne hφ1)]
  rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero,
    one_mul]

/-! ## Closed-loop winding integrality -/

/-- **Closed-loop integrality**: for a closed nonvanishing `C¹` loop
(`φ 1 = φ 0`), the log-derivative integral lies in `2πi·ℤ`. -/
theorem integral_logDeriv_closed_mem {φ φ' : ℝ → ℂ}
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (Icc (0 : ℝ) 1))
    (hne : ∀ t ∈ Icc (0 : ℝ) 1, φ t ≠ 0)
    (hclosed : φ 1 = φ 0) :
    ∃ k : ℤ, (∫ t in (0 : ℝ)..1, φ' t / φ t)
      = k * (2 * Real.pi * Complex.I) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hφ0 : φ 0 ≠ 0 := hne 0 (left_mem_Icc.mpr h01)
  have hexp := exp_integral_logDeriv hd hc hne
  rw [hclosed, div_self hφ0] at hexp
  exact Complex.exp_eq_one_iff.mp hexp

/-! ## Cyclic-chain winding integrality -/

/-- **Cyclic-chain integrality**: for `n` nonvanishing `C¹` segments
`φ i` on `[0,1]` whose endpoints match cyclically
(`φ i 1 = φ (i+1) 0` in `Fin n`), the sum of the segment log-derivative
integrals lies in `2πi·ℤ`. The endpoint quotients telescope around the
cycle. -/
theorem sum_integral_logDeriv_chain_mem {n : ℕ} [NeZero n]
    {φ φ' : Fin n → ℝ → ℂ}
    (hd : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (φ i) (φ' i t) t)
    (hc : ∀ i, ContinuousOn (φ' i) (Icc (0 : ℝ) 1))
    (hne : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, φ i t ≠ 0)
    (hcyc : ∀ i : Fin n, φ i 1 = φ (i + 1) 0) :
    ∃ k : ℤ, (∑ i : Fin n, ∫ t in (0 : ℝ)..1, φ' i t / φ i t)
      = k * (2 * Real.pi * Complex.I) := by
  classical
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  apply Complex.exp_eq_one_iff.mp
  rw [Complex.exp_sum]
  have hterm : ∀ i : Fin n,
      Complex.exp (∫ t in (0 : ℝ)..1, φ' i t / φ i t)
        = φ i 1 / φ i 0 := fun i =>
    exp_integral_logDeriv (hd i) (hc i) (hne i)
  rw [Finset.prod_congr rfl (fun i _ => hterm i)]
  -- The product telescopes around the cycle.
  rw [Finset.prod_div_distrib]
  have hreindex : (∏ i : Fin n, φ i 1) = ∏ i : Fin n, φ (i + 1) 0 := by
    exact Finset.prod_congr rfl (fun i _ => by rw [hcyc i])
  have hcycle : (∏ i : Fin n, φ (i + 1) 0) = ∏ i : Fin n, φ i 0 := by
    apply Fintype.prod_equiv (Equiv.addRight (1 : Fin n))
    intro i
    rfl
  rw [hreindex, hcycle]
  have hne0 : (∏ i : Fin n, φ i 0) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr
      (fun i _ => hne i 0 (left_mem_Icc.mpr h01))
  exact div_self hne0

end LogDerivWinding

end JacobianChallenge

end
