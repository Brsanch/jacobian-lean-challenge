/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodLatticeSymplecticBundleClassical
import JacobianChallenge.Manifold.PeriodPairingDataFromSmoothCycle

set_option linter.unusedSectionVars false

/-! # Named-classical-input data structure for the period lattice

The period-lattice side of `C3FullInputSymp X` reduces (via
`PeriodLatticeSymplecticBundleClassical.lean`) to **two** named
classical hypotheses (Riemann bilinear non-degeneracy + H₁
generation), plus a tuple of `2g` cycle generators chosen as a
witness for a symplectic homology basis.

This file packages those three pieces into a single data structure
`C3PeriodLatticeClassicalInputs basis` and exposes the headline
constructor `toBundle` producing the full
`PeriodLatticeSymplecticBundle`. Downstream code can now cite a
single named hypothesis "the period-lattice classical inputs exist"
rather than three separate ones.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **Bundled classical inputs for the period-lattice symplectic
bundle.** Three named hypotheses, parametrised over a chosen
ℂ-basis `basis` of the holomorphic 1-forms:

* `cycleGens` — a tuple of `2g` smooth cycles (classically: chosen
  representatives of a symplectic homology basis of `X`).
* `riemannBilinear` — the `2g` period vectors of `cycleGens` are
  ℝ-linearly independent in `Fin g → ℂ` (classical Riemann bilinear
  non-degeneracy).
* `homologySpans` — every smooth cycle's period vector lies in the
  ℤ-span of the `cycleGens` period vectors (classically: the chosen
  generators ℤ-span H₁(X; ℤ) modulo boundaries, plus Stokes).

Once an inhabitant of this structure is produced (the genuine
classical content), the full `PeriodLatticeSymplecticBundle` follows
mechanically via `toBundle`. -/
structure C3PeriodLatticeClassicalInputs
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    where
  /-- Tuple of `2g` smooth cycle generators (symplectic homology basis). -/
  cycleGens :
    Fin (2 * JacobianChallenge.genus X) → (PeriodPairingData.ofSmoothCycle X).H1
  /-- Riemann bilinear non-degeneracy: the `2g` period vectors are
  ℝ-linearly independent. -/
  riemannBilinear :
    LinearIndependent ℝ
      (fun i : Fin (2 * JacobianChallenge.genus X) =>
        periodVector (PeriodPairingData.ofSmoothCycle X) basis (cycleGens i))
  /-- Homology spanning: every cycle's period lies in the ℤ-span of the
  `cycleGens` periods. -/
  homologySpans :
    ∀ γ : (PeriodPairingData.ofSmoothCycle X).H1,
      periodVector (PeriodPairingData.ofSmoothCycle X) basis γ ∈
        Submodule.span ℤ
          (Set.range
            (fun i : Fin (2 * JacobianChallenge.genus X) =>
              periodVector (PeriodPairingData.ofSmoothCycle X) basis (cycleGens i)))

namespace C3PeriodLatticeClassicalInputs

variable
    {basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}

/-- **From the bundled classical inputs, produce a
`PeriodLatticeSymplecticBundle`.** Direct application of
`PeriodLatticeSymplecticBundle.ofClassicalInputs`. -/
noncomputable def toBundle (cls : C3PeriodLatticeClassicalInputs basis) :
    PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) basis :=
  PeriodLatticeSymplecticBundle.ofClassicalInputs
    (PeriodPairingData.ofSmoothCycle X) basis
    cls.cycleGens cls.riemannBilinear cls.homologySpans

end C3PeriodLatticeClassicalInputs

end JacobianChallenge

end
