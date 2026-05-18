/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3PeriodLatticeStokesCanonicalH1Subsingleton

set_option linter.unusedSectionVars false

/-! # Canonical-bundle `trivial_at_genus_zero`

The legacy `trivial_at_genus_zero` in
`C3PeriodLatticeStokesGenusZero.lean` uses an *unconventional*
Stokes-bundle choice (`boundaries := ⊤, closedForms := ⊥`) to make
genus-0 work for ANY `X` with `Subsingleton (HolomorphicOneForm X)`.
That choice is honest but throws away the canonical `Smooth2Chain`-
based Stokes data.

This file ships the *canonical-bundle* analogue:
`C3PeriodLatticeStokesSpanTopInputs.trivial_at_genus_zero_canonical`.
Requires one additional subsingleton hypothesis, namely that the
canonical Stokes H₁ quotient `SmoothCycle 𝓘(ℝ, ℂ) X ⧸ stokesBoundaries
𝓘(ℝ, ℂ) X` is subsingleton.

Classically: at genus 0 the manifold is homeomorphic to `S²`, and
`H₁(S²; ℤ) = 0` makes the canonical quotient trivial. The canonical
H₁ subsingleton is therefore the topological "H₁(X; ℤ) = 0" content
at genus 0.

## Headline

```
noncomputable def
  C3PeriodLatticeStokesSpanTopInputs.trivial_at_genus_zero_canonical
    [Subsingleton (HolomorphicOneForm X)]
    [Subsingleton (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).H1]
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (hgenus : JacobianChallenge.genus X = 0) :
    C3PeriodLatticeStokesSpanTopInputs basis
```

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **Canonical-bundle trivial-at-genus-zero.** At genus 0 with the
two subsingleton hypotheses (`HolomorphicOneForm X` and the canonical
Stokes H₁ quotient), `C3PeriodLatticeStokesSpanTopInputs basis` is
unconditionally inhabited via the canonical `Smooth2Chain`-based
Stokes bundle — no unconventional `boundaries := ⊤` choice needed. -/
noncomputable def C3PeriodLatticeStokesSpanTopInputs.trivial_at_genus_zero_canonical
    [Subsingleton (HolomorphicOneForm X)]
    [Subsingleton (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).H1]
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (hgenus : JacobianChallenge.genus X = 0) :
    C3PeriodLatticeStokesSpanTopInputs basis := by
  -- Empty `cycleGens` tuple after rewriting `2 * 0 = 0`.
  have hempty : IsEmpty (Fin (2 * JacobianChallenge.genus X)) := by
    rw [hgenus, Nat.mul_zero]; infer_instance
  refine
    C3PeriodLatticeStokesSpanTopInputs.ofCanonicalGenusZeroSubsingleton
      basis ?_ ?_
  · -- cycleGens : Fin (2 * genus X) → ... — empty after rewriting.
    rw [hgenus, Nat.mul_zero]
    exact Fin.elim0
  · -- riemannBilinear: ℝ-LI over empty type.
    exact linearIndependent_empty_type

end JacobianChallenge

end
