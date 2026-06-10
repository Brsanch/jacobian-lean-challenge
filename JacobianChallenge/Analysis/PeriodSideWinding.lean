/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.LogDerivWinding
import JacobianChallenge.Analysis.ParallelogramPairing
import Mathlib.Analysis.Calculus.Deriv.Shift

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # Period-side winding: the lattice membership of the Abel integral

The remaining half of piece 1/2 of the forward-Abel contour argument
(`HANDOFF_TLDIVSUM.md`): applying the winding engine
(`LogDerivWinding.integral_logDeriv_closed_mem`) to the two one-sided
log-integrals `Δ_h, Δ_v` produced by the pairing algebra.

* `periodSide_logDeriv_integral_mem` — for `F` analytic and
  nonvanishing along the segment `a + [0,1]·ω` with `F(a+ω) = F(a)`,
  the weighted log-derivative integral
  `∫₀¹ (F′/F)(a + t·ω)·ω dt` lies in `2πi·ℤ` (chain rule through `ℂ`
  composed with `ofReal`, then closed-loop integrality);
* `deriv_eq_of_periodic` — the derivative of a periodic function is
  periodic;
* **`boundaryIntegral_mul_logDeriv_mem`** — combining with the pairing
  algebra: for `F` doubly periodic, analytic and nonvanishing along
  both generator sides,
  `∮_{∂Π(a)} z·(F′/F)(z) dz = 2πi·(k₁·ω₁ + k₂·ω₂)` for some
  `k₁ k₂ : ℤ` — the **lattice membership** of the Abel integral, the
  pairing-side evaluation that piece 5 equates with the residue-side
  `ε·2πi·∑ ord·x̃`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set intervalIntegral

namespace JacobianChallenge

namespace ParallelogramWinding

open LogDerivWinding

/-- **Period-side winding integrality**: for `F` analytic and
nonvanishing along the segment `a + [0,1]·ω` with matching endpoints
`F(a+ω) = F(a)`, the weighted log-derivative integral lies in
`2πi·ℤ`. -/
theorem periodSide_logDeriv_integral_mem {F : ℂ → ℂ} (a ω : ℂ)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ F (a + t • ω))
    (hne : ∀ t ∈ Icc (0 : ℝ) 1, F (a + t • ω) ≠ 0)
    (hper : F (a + ω) = F a) :
    ∃ k : ℤ, (∫ t in (0 : ℝ)..1,
        deriv F (a + t • ω) / F (a + t • ω) * ω)
      = k * (2 * Real.pi * Complex.I) := by
  have key : ∀ t : ℝ, a + t • ω = a + (t : ℂ) * ω := fun t => by
    rw [Complex.real_smul]
  -- The path and its derivative, as data for the winding engine.
  have hd : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => F (a + s • ω))
        (deriv F (a + t • ω) * ω) t := by
    intro t ht
    have hfun_eq : (fun s : ℝ => F (a + s • ω))
        = fun s : ℝ => F (a + (s : ℂ) * ω) := by
      funext s
      rw [key s]
    rw [hfun_eq, key t]
    -- Inner `ℂ`-derivative of `F` at the path point.
    have hFd : HasDerivAt F (deriv F (a + (t : ℂ) * ω))
        (a + (t : ℂ) * ω) := by
      have h := (hF t ht).differentiableAt.hasDerivAt
      rw [key t] at h
      exact h
    -- The affine path over `ℂ`.
    have haffine : HasDerivAt (fun w : ℂ => a + w * ω) ω
        ((t : ℝ) : ℂ) := by
      have h := ((hasDerivAt_id ((t : ℝ) : ℂ)).mul_const ω).const_add a
      simpa using h
    -- Chain rule over `ℂ`, then compose with `ofReal`.
    have hcomp := hFd.comp ((t : ℝ) : ℂ) haffine
    exact hcomp.comp_ofReal
  -- Continuity of the path derivative.
  have hpath : Continuous (fun t : ℝ => a + t • ω) := by
    have heq : (fun t : ℝ => a + t • ω)
        = fun t : ℝ => a + (t : ℂ) * ω := by
      funext t
      rw [key t]
    rw [heq]
    exact continuous_const.add (Complex.continuous_ofReal.mul
      continuous_const)
  have hc : ContinuousOn (fun t : ℝ => deriv F (a + t • ω) * ω)
      (Icc (0 : ℝ) 1) := by
    apply ContinuousOn.mul ?_ continuousOn_const
    intro t ht
    exact (ContinuousAt.comp (g := deriv F)
      (f := fun s : ℝ => a + s • ω) ((hF t ht).deriv.continuousAt)
      hpath.continuousAt).continuousWithinAt
  -- The loop closes by the period relation.
  have hclosed : (fun s : ℝ => F (a + s • ω)) 1
      = (fun s : ℝ => F (a + s • ω)) 0 := by
    show F (a + (1 : ℝ) • ω) = F (a + (0 : ℝ) • ω)
    rw [key 1, key 0]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul,
      zero_mul, add_zero]
    exact hper
  obtain ⟨k, hk⟩ := integral_logDeriv_closed_mem
    (φ := fun s : ℝ => F (a + s • ω))
    (φ' := fun t : ℝ => deriv F (a + t • ω) * ω)
    hd hc hne hclosed
  refine ⟨k, ?_⟩
  rw [← hk]
  apply integral_congr
  intro t _
  show deriv F (a + t • ω) / F (a + t • ω) * ω
    = deriv F (a + t • ω) * ω / F (a + t • ω)
  ring

/-- The derivative of a periodic function is periodic. -/
lemma deriv_eq_of_periodic {F : ℂ → ℂ} {ω : ℂ}
    (hper : ∀ z, F (z + ω) = F z) (z : ℂ) :
    deriv F (z + ω) = deriv F z := by
  have hfun : (fun w : ℂ => F (w + ω)) = F := funext hper
  rw [← deriv_comp_add_const F ω z, hfun]

/-- **Lattice membership of the Abel integral** (pairing side, piece
1/2 complete): for `F` doubly periodic, analytic and nonvanishing along
both generator sides of `∂Π(a; ω₁, ω₂)`,

  `∮_{∂Π(a)} z·(F′/F)(z) dz = 2πi·(k₁·ω₁ + k₂·ω₂)`

for some integers `k₁, k₂`. -/
theorem boundaryIntegral_mul_logDeriv_mem {F : ℂ → ℂ} (a ω₁ ω₂ : ℂ)
    (hper₁ : ∀ z, F (z + ω₁) = F z)
    (hper₂ : ∀ z, F (z + ω₂) = F z)
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ F (a + t • ω₁))
    (hHne : ∀ t ∈ Icc (0 : ℝ) 1, F (a + t • ω₁) ≠ 0)
    (hV : ∀ t ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ F (a + t • ω₂))
    (hVne : ∀ t ∈ Icc (0 : ℝ) 1, F (a + t • ω₂) ≠ 0) :
    ∃ k₁ k₂ : ℤ, boundaryIntegral a ω₁ ω₂
        (fun z => z * (deriv F z / F z))
      = (2 * Real.pi * Complex.I) * ((k₁ : ℂ) * ω₁ + (k₂ : ℂ) * ω₂) := by
  -- The log derivative is doubly periodic.
  have hgper₁ : ∀ z, deriv F (z + ω₁) / F (z + ω₁) = deriv F z / F z := by
    intro z
    rw [deriv_eq_of_periodic hper₁ z, hper₁ z]
  have hgper₂ : ∀ z, deriv F (z + ω₂) / F (z + ω₂) = deriv F z / F z := by
    intro z
    rw [deriv_eq_of_periodic hper₂ z, hper₂ z]
  -- Continuity of the log derivative along the two generator sides.
  have hpath₁ : Continuous (fun t : ℝ => a + t • ω₁) := by
    have heq : (fun t : ℝ => a + t • ω₁)
        = fun t : ℝ => a + (t : ℂ) * ω₁ := by
      funext t
      rw [Complex.real_smul]
    rw [heq]
    exact continuous_const.add (Complex.continuous_ofReal.mul
      continuous_const)
  have hpath₂ : Continuous (fun t : ℝ => a + t • ω₂) := by
    have heq : (fun t : ℝ => a + t • ω₂)
        = fun t : ℝ => a + (t : ℂ) * ω₂ := by
      funext t
      rw [Complex.real_smul]
    rw [heq]
    exact continuous_const.add (Complex.continuous_ofReal.mul
      continuous_const)
  have hcH : ContinuousOn
      (fun t : ℝ => deriv F (a + t • ω₁) / F (a + t • ω₁))
      (Icc 0 1) := by
    apply ContinuousOn.div
    · intro t ht
      exact (ContinuousAt.comp (g := deriv F)
        (f := fun s : ℝ => a + s • ω₁) ((hH t ht).deriv.continuousAt)
        hpath₁.continuousAt).continuousWithinAt
    · intro t ht
      exact (ContinuousAt.comp (g := F)
        (f := fun s : ℝ => a + s • ω₁) ((hH t ht).continuousAt)
        hpath₁.continuousAt).continuousWithinAt
    · exact fun t ht => hHne t ht
  have hcV : ContinuousOn
      (fun t : ℝ => deriv F (a + t • ω₂) / F (a + t • ω₂))
      (Icc 0 1) := by
    apply ContinuousOn.div
    · intro t ht
      exact (ContinuousAt.comp (g := deriv F)
        (f := fun s : ℝ => a + s • ω₂) ((hV t ht).deriv.continuousAt)
        hpath₂.continuousAt).continuousWithinAt
    · intro t ht
      exact (ContinuousAt.comp (g := F)
        (f := fun s : ℝ => a + s • ω₂) ((hV t ht).continuousAt)
        hpath₂.continuousAt).continuousWithinAt
    · exact fun t ht => hVne t ht
  -- The pairing algebra.
  have hpair := boundaryIntegral_mul_eq_pairing a ω₁ ω₂
    (g := fun z => deriv F z / F z) hgper₁ hgper₂ hcH hcV
  -- The two one-sided windings.
  obtain ⟨kh, hkh⟩ := periodSide_logDeriv_integral_mem a ω₁ hH hHne
    (hper₁ a)
  obtain ⟨kv, hkv⟩ := periodSide_logDeriv_integral_mem a ω₂ hV hVne
    (hper₂ a)
  refine ⟨kv, -kh, ?_⟩
  push_cast
  linear_combination hpair + ω₁ * hkv - ω₂ * hkh

end ParallelogramWinding

end JacobianChallenge

end
