/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelHypothesisReductionComplexTorus
import JacobianChallenge.Manifold.AbelJacobiInjectiveComplexTorus
import JacobianChallenge.Manifold.AbelJacobiSmoothnessComplexTorus

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # `Nonempty (C3FullInputExtSymp (ℂ⧸L))` from two named classical
hypotheses

Final packaging step. The PLSB, AJ input, smoothness, and injectivity
discharges are all unconditional in tree. The remaining gap reduces to:

1. **`TLDivSumHypothesis L`** (Abel's theorem on elliptic functions).
2. **`JacobiInversion (canonicalAbelJacobiInputSymp L h) hAbel`** (Jacobi
   inversion: injective + surjective on `Pic⁰ T_L`).

Together they yield `Nonempty (C3FullInputExtSymp (ℂ⧸L))` —
the analytic Jacobian inhabitant for `T_L` matching the C3 closure
template.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **Final packaging: `Nonempty (C3FullInputExtSymp (ℂ⧸L))` from
two named classical hypotheses.**

Inputs:
* `h` — any `PLSB` witness on `(basis_g_dz L)`.
* `hTL : TLDivSumHypothesis L` — Abel's theorem on elliptic functions.
* `hJI` — Jacobi inversion (parametric on the Abel discharge of `hTL`).

Output: `Nonempty (C3FullInputExtSymp (ℂ⧸L))` — the analytic Jacobian
inhabitant of `T_L` matching the C3 closure template. -/
theorem nonempty_C3FullInputExtSymp_complexTorus_of_TLDivSum_and_jacobiInversion
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L))
    (hTL : TLDivSumHypothesis L)
    (hJI : AbelJacobiInputSymp.JacobiInversion
      (canonicalAbelJacobiInputSymp L h)
      (abelHypothesis_complexTorus_of_TLDivSum L h hTL)) :
    Nonempty (JacobianChallenge.C3FullInputExtSymp (ℂ ⧸ L)) :=
  nonempty_C3FullInputExtSymp_complexTorus L h
    (abelHypothesis_complexTorus_of_TLDivSum L h hTL)
    hJI
    (abelJacobiSmoothness_complexTorus L h)
    (abelJacobiInjective_complexTorus L h)

end ComplexTorus

end JacobianChallenge

end
