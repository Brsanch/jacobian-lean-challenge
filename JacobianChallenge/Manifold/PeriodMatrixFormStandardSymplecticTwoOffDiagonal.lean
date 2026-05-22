/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodMatrixFormStandardSymplecticTwo

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Closed form for the off-diagonal of `i • periodMatrixForm pm (standardSymplectic 2)`

At literal `Fin 4 / Fin 2`, the off-diagonal entry of `i • M` for
`M = periodMatrixForm pm (standardSymplectic 2)` at `(0, 1)`:

  `(i • M)_{0, 1} = i · (pm_{0,0} · star(pm_{2,1}) + pm_{1,0} · star(pm_{3,1})
                        − pm_{2,0} · star(pm_{0,1}) − pm_{3,0} · star(pm_{1,1}))`.

Unlike the diagonal, this is generally **complex** (not real). However,
its conjugate equals `(i • M)_{1, 0}` by Hermitian symmetry.

## What ships

* `iPeriodMatrixForm_standardSymplectic_two_offdiagonal_apply` —
  closed form for the `(0, 1)` entry.

No `sorry`, no `axiom`. -/

noncomputable section

open Matrix

namespace JacobianChallenge

/-- **Closed form for `(i • periodMatrixForm pm (standardSymplectic 2))_{0, 1}`.** -/
theorem iPeriodMatrixForm_standardSymplectic_two_offdiagonal_apply
    (pm : Matrix (Fin 4) (Fin 2) ℂ) :
    ((Complex.I : ℂ) • periodMatrixForm pm (standardSymplectic 2)) 0 1
      = Complex.I * (pm 0 0 * star (pm 2 1) + pm 1 0 * star (pm 3 1)
          - pm 2 0 * star (pm 0 1) - pm 3 0 * star (pm 1 1)) := by
  rw [Matrix.smul_apply, periodMatrixForm_standardSymplectic_two_apply]
  ring

end JacobianChallenge

end
