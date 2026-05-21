/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HodgeInnerProductHypothesis
import JacobianChallenge.Manifold.DefaultHolomorphicOneFormBasis

set_option linter.unusedSectionVars false

/-! # `HodgeInnerProductHypothesis X` UNCONDITIONAL on any compact connected
complex 1-manifold (chip 10)

The original `HodgeInnerProductHypothesis X` was a named existence
statement because formalising the classical Hodge inner product
`(i/2) ∫_X ω ∧ η̄` requires wedge products + integration on manifolds,
which are not in the mathlib pin used by this project.

However, the *hypothesis itself* — there exists SOME positive-definite
Hermitian form on `HolomorphicOneForm X` — can be discharged
**unconditionally** by constructing the "basis-coordinate" Hermitian
form: for any basis `basis_ω` of `HolomorphicOneForm X`,

  `H(ω, η) := ∑_i (basis_ω.repr ω) i * star ((basis_ω.repr η) i)`

is positive-definite Hermitian. This is NOT the classical Hodge form
(which matches the period matrix expression via the bridge identity);
it's the standard "ℓ² in the basis" inner product. The classical
content lives in the **bridge identity** atom of
`CompleteHodgeRiemannHypothesis`, which is unaffected by this chip.

Net effect: `CompleteHodgeRiemannHypothesis` reduces from
`∃ J H, H.IsPositiveDefinite ∧ first ∧ bridge` to (effectively)
`∃ J H, first ∧ bridge` since the PD atom is automatic. The deep
content lives in: `(i) the choice of J/cycleGens, (ii) the bridge
identity tying them together with H`.

## What this file ships

* `standardHodgeForm basis_ω` — explicit construction of a PD Hermitian
  form from any ℂ-basis of `HolomorphicOneForm X`.
* `standardHodgeForm_isPositiveDefinite` — PD discharge.
* `hodgeInnerProductHypothesis_unconditional X` — unconditional
  discharge.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`standardHodgeForm basis_ω`** — the basis-coordinate Hermitian
form: `H(ω, η) := ∑_i (basis_ω.repr ω) i * star ((basis_ω.repr η) i)`. -/
noncomputable def standardHodgeForm
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)) :
    HermitianOnHolomorphicOneForm X where
  toFun om eta :=
    ∑ i, (basis_ω.repr om) i * star ((basis_ω.repr eta) i)
  map_zero_left _ := by simp
  map_add_left _ _ _ := by
    simp [Finset.sum_add_distrib, add_mul]
  map_smul_left c _ _ := by
    simp [Finset.mul_sum, mul_assoc]
  conjSymm _ _ := by
    simp only [star_sum, star_mul, star_star]

/-- **Standard Hodge form is positive definite.** -/
theorem standardHodgeForm_isPositiveDefinite
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)) :
    (standardHodgeForm basis_ω).IsPositiveDefinite := by
  -- Rewrite using `Complex.mul_conj : z * star z = ↑(Complex.normSq z)`.
  have h_term : ∀ (om : HolomorphicOneForm X) (i : Fin (JacobianChallenge.genus X)),
      (basis_ω.repr om) i * star ((basis_ω.repr om) i)
        = (Complex.normSq ((basis_ω.repr om) i) : ℂ) := by
    intro om i; exact Complex.mul_conj _
  have h_sum : ∀ (om : HolomorphicOneForm X),
      (standardHodgeForm basis_ω).toFun om om
        = ((∑ i, Complex.normSq ((basis_ω.repr om) i) : ℝ) : ℂ) := by
    intro om
    show ∑ i, (basis_ω.repr om) i * star ((basis_ω.repr om) i)
          = ((∑ i, Complex.normSq ((basis_ω.repr om) i) : ℝ) : ℂ)
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact h_term om i
  constructor
  · -- Real + non-negative.
    intro om
    rw [h_sum om]
    refine ⟨Complex.ofReal_im _, ?_⟩
    rw [Complex.ofReal_re]
    exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  · -- H(ω, ω) = 0 ⟹ ω = 0.
    intro om h
    rw [h_sum om] at h
    have h_real : (∑ i, Complex.normSq ((basis_ω.repr om) i) : ℝ) = 0 := by
      exact_mod_cast h
    have h_each : ∀ i, Complex.normSq ((basis_ω.repr om) i) = 0 := by
      intros i
      apply (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => Complex.normSq_nonneg _)).mp h_real i (Finset.mem_univ i)
    have h_each_coord : ∀ i, (basis_ω.repr om) i = 0 := by
      intros i; exact Complex.normSq_eq_zero.mp (h_each i)
    apply basis_ω.repr.injective
    ext i
    simp [h_each_coord i]

/-- **`HodgeInnerProductHypothesis X` holds unconditionally** on any
compact connected complex 1-manifold via the basis-coordinate
construction. -/
theorem hodgeInnerProductHypothesis_unconditional :
    HodgeInnerProductHypothesis X :=
  ⟨standardHodgeForm (defaultHolomorphicOneFormBasis X),
    standardHodgeForm_isPositiveDefinite _⟩

end JacobianChallenge

end
