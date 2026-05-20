/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LevelSetChainPeriodVectorExplicit

set_option linter.unusedSectionVars false

/-! # Real and imaginary parts of the level-set chain period vector

Split
`complexChainPeriodVector_levelSetChain_apply_eq_sum_real_imag` into
its **real** and **imaginary** components: each is a pure
`ℝ`-valued `Finset.sum` of per-path real integrals of the
corresponding `realComponent`/`imagComponent` of `α j`.

This is the natural endpoint of the period-decomposition arc: the
substantive content of the period-in-lattice claim reduces to two
real Finset sums, each of which is identifiable (via the chain-rule
pathway) with a `β`-line integral against `realComponent` or
`imagComponent` of the trace 1-form `traceAt (α j) f`.

## What ships

* `complexChainPeriodVector_levelSetChain_apply_re_eq_sum` — real
  part as a real Finset sum.
* `complexChainPeriodVector_levelSetChain_apply_im_eq_sum` — imag
  part as a real Finset sum.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter Module
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Real part of `j`-th period coordinate as a real Finset sum.** -/
theorem complexChainPeriodVector_levelSetChain_apply_re_eq_sum
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (j : Fin (JacobianChallenge.genus X)) :
    let hβ0_reg : β 0 ∈ f.regularValueSet :=
      hβ_reg 0 ⟨le_refl _, by norm_num⟩
    (complexChainPeriodVector α (f.levelSetChain hnc hβ_smooth hβ_reg) j).re
      = ∑ p ∈ (f.sourceFiber hβ0_reg).attach,
          (f.sourceFiberPath hnc hβ_smooth hβ_reg
              ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).integrate
              (realComponent (α j)) := by
  intro hβ0_reg
  rw [complexChainPeriodVector_levelSetChain_apply_eq_sum_real_imag
        f hnc hβ_smooth hβ_reg α j]
  -- Pull `.re` inside the sum.
  rw [show (∑ p ∈ (f.sourceFiber hβ0_reg).attach,
            ((((f.sourceFiberPath hnc hβ_smooth hβ_reg
                ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).integrate
                (realComponent (α j)) : ℝ) : ℂ)
              + Complex.I *
                  (((f.sourceFiberPath hnc hβ_smooth hβ_reg
                    ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).integrate
                    (imagComponent (α j)) : ℝ) : ℂ))).re
        = ∑ p ∈ (f.sourceFiber hβ0_reg).attach,
            ((((f.sourceFiberPath hnc hβ_smooth hβ_reg
                ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).integrate
                (realComponent (α j)) : ℝ) : ℂ)
              + Complex.I *
                  (((f.sourceFiberPath hnc hβ_smooth hβ_reg
                    ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).integrate
                    (imagComponent (α j)) : ℝ) : ℂ)).re from
      Complex.re_sum _ _]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  -- (a + I * b).re = a.re - b.im = a (for a, b real).
  simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]

/-- **Imaginary part of `j`-th period coordinate as a real Finset sum.** -/
theorem complexChainPeriodVector_levelSetChain_apply_im_eq_sum
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (j : Fin (JacobianChallenge.genus X)) :
    let hβ0_reg : β 0 ∈ f.regularValueSet :=
      hβ_reg 0 ⟨le_refl _, by norm_num⟩
    (complexChainPeriodVector α (f.levelSetChain hnc hβ_smooth hβ_reg) j).im
      = ∑ p ∈ (f.sourceFiber hβ0_reg).attach,
          (f.sourceFiberPath hnc hβ_smooth hβ_reg
              ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).integrate
              (imagComponent (α j)) := by
  intro hβ0_reg
  rw [complexChainPeriodVector_levelSetChain_apply_eq_sum_real_imag
        f hnc hβ_smooth hβ_reg α j]
  rw [show (∑ p ∈ (f.sourceFiber hβ0_reg).attach,
            ((((f.sourceFiberPath hnc hβ_smooth hβ_reg
                ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).integrate
                (realComponent (α j)) : ℝ) : ℂ)
              + Complex.I *
                  (((f.sourceFiberPath hnc hβ_smooth hβ_reg
                    ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).integrate
                    (imagComponent (α j)) : ℝ) : ℂ))).im
        = ∑ p ∈ (f.sourceFiber hβ0_reg).attach,
            ((((f.sourceFiberPath hnc hβ_smooth hβ_reg
                ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).integrate
                (realComponent (α j)) : ℝ) : ℂ)
              + Complex.I *
                  (((f.sourceFiberPath hnc hβ_smooth hβ_reg
                    ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property)).integrate
                    (imagComponent (α j)) : ℝ) : ℂ)).im from
      Complex.im_sum _ _]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  -- (a + I * b).im = a.im + b.re = b (for a, b real).
  simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]

end MeromorphicNonzero

end JacobianChallenge

end
