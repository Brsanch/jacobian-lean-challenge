/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexPairImStarMulFromLinearIndependent
import JacobianChallenge.Manifold.HasJacobianHodgeChainComplexTorusSwap
import JacobianChallenge.Manifold.PeriodLatticeSymplecticBundleComplexTorus

set_option linter.unusedSectionVars false

/-! # Positively oriented ℤ-basis of `L ≤ ℂ` exists (chip 19s)

For every discrete full-rank ℤ-lattice `L ≤ ℂ`, there exists a pair
`(lam₁, lam₂) ∈ L²` satisfying:

* `IsZBasisOfL L lam₁ lam₂` — every `z ∈ L` is an integer combination
  `m₁ • lam₁ + m₂ • lam₂`;
* `0 < (star lam₁ · lam₂).im` — positive orientation (the
  "Im τ > 0" / fundamental-domain condition).

The proof composes:

* `basisFin2OfL` (unconditional ℤ-basis of `L`);
* `basisFin2OfL_realLinearIndependent` (ℝ-LI of the basis pair in `ℂ`,
  from `Basis.ofZLatticeBasis`);
* chip 19q (`im_star_mul_ne_zero_of_linearIndependent_pair`,
  reducing nonvanishing of `Im(star · ·)` to ℝ-LI);
* `isZBasisOfL_swap` (swapping `(lam₁, lam₂) → (lam₂, lam₁)` flips
  the sign of `Im(star · ·)`).

By case-split on the sign of `Im(star (lam₁_complexTorus L) ·
(lam₂_complexTorus L))` (nonzero by chip 19q), one of the two
orderings yields a positively oriented ℤ-basis.

## What this file ships

* `JacobianChallenge.ComplexTorus.exists_positively_oriented_ZBasisOfL`
  — the existence statement.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **Sign flip under swap.** `Im(star lam₂ · lam₁) = -Im(star lam₁ · lam₂)`. -/
private lemma im_star_mul_swap (a b : ℂ) :
    (star b * a).im = -(star a * b).im := by
  rw [show star b * a = star (star a * b) from by rw [StarMul.star_mul, star_star]]
  exact Complex.conj_im _

/-- **Positively oriented ℤ-basis of `L`.** For every discrete
full-rank ℤ-lattice `L ≤ ℂ`, the canonical `Fin 2` ℤ-basis
`(lam₁_complexTorus L, lam₂_complexTorus L)` has nonzero
`(star lam₁ · lam₂).im` (via chip 19q + `basisFin2OfL_realLinearIndependent`);
a case-split on its sign produces a *positively oriented* ℤ-basis
by either using `(lam₁, lam₂)` directly or swapping to
`(lam₂, lam₁)`. -/
theorem exists_positively_oriented_ZBasisOfL :
    ∃ (lam₁ lam₂ : ℂ) (_hlam₁ : lam₁ ∈ L) (_hlam₂ : lam₂ ∈ L),
      IsZBasisOfL L lam₁ lam₂ ∧
      0 < (star lam₁ * lam₂).im := by
  -- ℝ-LI of the canonical basis pair.
  have h_LI :
      LinearIndependent ℝ
        (![lam₁_complexTorus L, lam₂_complexTorus L] : Fin 2 → ℂ) :=
    basisFin2OfL_realLinearIndependent L
  -- Nonvanishing of `Im(star · ·)` via chip 19q.
  have h_im_ne :
      (star (lam₁_complexTorus L) * (lam₂_complexTorus L)).im ≠ 0 :=
    Complex.im_star_mul_ne_zero_of_linearIndependent_pair h_LI
  -- Case split on sign.
  rcases lt_or_gt_of_ne h_im_ne with h_neg | h_pos
  · -- Negative case: swap to `(lam₂, lam₁)`.
    refine ⟨lam₂_complexTorus L, lam₁_complexTorus L,
            lam₂_complexTorus_mem L, lam₁_complexTorus_mem L,
            ?_, ?_⟩
    · exact isZBasisOfL_swap L basisFin2OfL_isZBasisOfL
    · rw [im_star_mul_swap]; linarith
  · -- Positive case: use directly.
    exact ⟨lam₁_complexTorus L, lam₂_complexTorus L,
           lam₁_complexTorus_mem L, lam₂_complexTorus_mem L,
           basisFin2OfL_isZBasisOfL, h_pos⟩

end ComplexTorus

end JacobianChallenge

end
