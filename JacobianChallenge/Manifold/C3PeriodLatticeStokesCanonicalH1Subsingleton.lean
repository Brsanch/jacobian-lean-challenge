/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3PeriodLatticeStokesCanonicalFromHypothesis

set_option linter.unusedSectionVars false

/-! # H₁-subsingleton discharges `H1_spans_top_canonical`

In `C3PeriodLatticeStokesSpanTopInputs.ofCanonical`, the fourth
classical input is:

```
H1_spans_top_canonical :
  (Submodule.span ℤ
    (Set.range (fun i => (StokesBoundaryInvariance.canonical I X).proj
                          (cycleGens i)))) = ⊤
```

When `(StokesBoundaryInvariance.canonical I X).H1` is subsingleton —
classically, `H₁(X; ℤ) = 0` (genus-0 case, when `X` is homeomorphic to
`S²`) — any submodule of it equals `⊤` automatically. So
`H1_spans_top_canonical` is **trivial** at genus 0 once the subsingleton
hypothesis is in scope, including for the empty tuple at `genus X = 0`.

This file ships:

* `h1_spans_top_canonical_of_subsingleton` — the generic statement (any
  tuple, any `n : ℕ`).
* `h1_spans_top_canonical_of_subsingleton_empty` — specialisation to
  the empty tuple `(fun (i : Fin 0) => _)`, which is exactly the
  shape needed at `genus X = 0`.

The named classical input shrinks from "the chosen tuple's classes
ℤ-generate H₁" to "the canonical H₁ quotient is subsingleton" — which
on `RiemannSphere` is the well-known fact `H₁(S²; ℤ) = 0`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **Generic statement.** If the canonical Stokes H₁ quotient is
subsingleton, then for any tuple of cycles the ℤ-span of their
projected classes equals `⊤`. -/
theorem h1_spans_top_canonical_of_subsingleton
    [hsub : Subsingleton (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).H1]
    {n : ℕ}
    (cycleGens : Fin n → SmoothCycle 𝓘(ℝ, ℂ) X) :
    (Submodule.span ℤ
      (Set.range (fun i : Fin n =>
        ((StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).proj
            (cycleGens i) :
          (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).H1)))) = ⊤ := by
  -- In a subsingleton additive group, every submodule is `⊤` (and `⊥`).
  exact Subsingleton.elim _ _

/-- **Empty-tuple specialisation.** At `genus X = 0`, the symplectic
tuple has index `Fin (2 * 0) = Fin 0`. Combined with subsingleton
canonical H₁, the H₁ generation hypothesis is unconditionally
discharged. -/
theorem h1_spans_top_canonical_of_subsingleton_empty
    [hsub : Subsingleton (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).H1]
    (cycleGens :
      Fin (2 * JacobianChallenge.genus X) →
        (PeriodPairingData.ofSmoothCycle X).H1) :
    (Submodule.span ℤ
      (Set.range (fun i : Fin (2 * JacobianChallenge.genus X) =>
        ((StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).proj
            (cycleGens i) :
          (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).H1)))) = ⊤ :=
  h1_spans_top_canonical_of_subsingleton cycleGens

/-! ## Composed constructor: canonical-bundle inputs at subsingleton H₁ -/

/-- **Constructor from the most-reduced classical input boundary.** At a
manifold `X` with (i) `Subsingleton (HolomorphicOneForm X)` (genus-0
analytic input) and (ii) `Subsingleton (StokesBoundaryInvariance.canonical
𝓘(ℝ, ℂ) X).H1` (genus-0 topological input, i.e. `H₁(X; ℤ) = 0`), the
only consumer choices that remain for `C3PeriodLatticeStokesSpanTopInputs`
are the (empty at genus 0) `cycleGens` tuple and the vacuous
`riemannBilinear`. -/
noncomputable def C3PeriodLatticeStokesSpanTopInputs.ofCanonicalGenusZeroSubsingleton
    [Subsingleton (HolomorphicOneForm X)]
    [Subsingleton (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).H1]
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens :
      Fin (2 * JacobianChallenge.genus X) →
        (PeriodPairingData.ofSmoothCycle X).H1)
    (riemannBilinear :
      LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus X) =>
          periodVector (PeriodPairingData.ofSmoothCycle X) basis (cycleGens i))) :
    C3PeriodLatticeStokesSpanTopInputs basis :=
  C3PeriodLatticeStokesSpanTopInputs.ofCanonicalGenusZero basis cycleGens
    riemannBilinear
    (h1_spans_top_canonical_of_subsingleton_empty cycleGens)

end JacobianChallenge

end
