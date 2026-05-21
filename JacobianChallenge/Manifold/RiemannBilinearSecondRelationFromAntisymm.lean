/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodMatrixAntiHermitian
import JacobianChallenge.Manifold.RiemannBilinearRelations

set_option linter.unusedSectionVars false

/-! # Second relation reduces to positivity from anti-sym J (chip 20m)

`RiemannBilinearSecondRelation` is `M.IsHermitian ∧ positivity` where
`M := i • Πᵀ J Π̄`. Chip 19a (`iPeriodMatrixForm_isHermitian`) shows
the Hermitian conjunct is **automatic** from anti-symmetry of `J`,
without any classical content. This file packages that into a
discharge of the second relation that takes only the positivity
input.

## What this file ships

* `riemannBilinearSecondRelation_of_positivity_of_antisymm` —
  forward implication: anti-sym `J` + positivity ⟹ second relation.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`RiemannBilinearSecondRelation` from anti-sym `J` + positivity.**

The Hermitian conjunct of the second relation is automatic from
anti-symmetry of `J` (chip 19a `iPeriodMatrixForm_isHermitian`). So
the second relation reduces to only the *positivity* input:
`∀ x ≠ 0, (star x ⬝ᵥ (M *ᵥ x)).im = 0 ∧ 0 < (star x ⬝ᵥ (M *ᵥ x)).re`.

Note: `(periodMatrix _ α cycleGens).map star = (periodMatrix _ α cycleGens).map star`
in the definition uses the entrywise complex conjugate. -/
theorem riemannBilinearSecondRelation_of_positivity_of_antisymm
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    (hJ : Jᵀ = -J)
    (h_pos :
      ∀ x : Fin (JacobianChallenge.genus X) → ℂ, x ≠ 0 →
        let M : Matrix (Fin (JacobianChallenge.genus X))
                (Fin (JacobianChallenge.genus X)) ℂ :=
          (Complex.I : ℂ) •
            ((periodMatrix data α cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)
              * (periodMatrix data α cycleGens).map star)
        (star x ⬝ᵥ (M *ᵥ x)).im = 0 ∧
          0 < (star x ⬝ᵥ (M *ᵥ x)).re) :
    RiemannBilinearSecondRelation data α cycleGens J := by
  unfold RiemannBilinearSecondRelation
  refine ⟨?_, h_pos⟩
  -- Hermitian conjunct: chip 19a applied to (pmat, J).
  -- `periodMatrixForm pm J := pmᵀ * J.cast * pm.map star`, so the
  -- target matrix `i • Πᵀ J Π̄` equals `i • periodMatrixForm Π J`
  -- up to the definitional unfolding inside the bundle.
  exact iPeriodMatrixForm_isHermitian
    (periodMatrix data α cycleGens) J hJ

end JacobianChallenge

end
