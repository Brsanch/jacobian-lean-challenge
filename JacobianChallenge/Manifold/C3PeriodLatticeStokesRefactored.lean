/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3PeriodLatticeClassicalInputs
import JacobianChallenge.Manifold.ComplexPeriodH1

set_option linter.unusedSectionVars false

/-! # Refactored classical inputs for the period lattice: Stokes + homology
generation

The headline named-hypothesis data structure for inhabiting
`PeriodLatticeSymplecticBundle` is `C3PeriodLatticeClassicalInputs basis`
(in `C3PeriodLatticeClassicalInputs.lean`), which bundles three fields:

* `cycleGens` — a tuple of `2g` smooth cycle generators (symplectic
  basis representatives);
* `riemannBilinear` — ℝ-linear independence of their period vectors;
* `homologySpans` — every smooth cycle's period vector lies in the
  ℤ-span of the chosen tuple's periods.

The third field silently bundles two textbook-distinct pieces of
classical content:

1. **Homology generation** — every smooth cycle is, modulo a smooth
   boundary, a ℤ-combination of the chosen cycle generators.
2. **Stokes for holomorphic 1-forms** — smooth boundaries have zero
   period against any holomorphic 1-form.

This file factors `homologySpans` along that boundary. The user supplies
the two atomic textbook inputs (plus a `StokesBoundaryInvariance` bundle
to package the Stokes data and a "every holomorphic 1-form is
Stokes-closed" hypothesis), and `.toClassical` derives `homologySpans`
mechanically via the additivity of `periodVector` and the
period-on-boundary vanishing lemma already proven in
`ComplexPeriodH1.lean`.

## Significance

The refactoring exposes the *exact* classical content the period-lattice
construction depends on. A downstream provider of
`C3PeriodLatticeStokesInputs basis` no longer has to bundle the Stokes
work and the homological work into the single opaque `homologySpans`
field; the two are surfaced separately and can be discharged from
separate sources (e.g. a future Stokes-on-compact-surface theorem and a
future H₁(X; ℤ) ≅ ℤ²ᵍ + smooth-de-Rham comparison).

## What this file ships

* `C3PeriodLatticeStokesInputs basis` — refactored data structure with
  the two atomic classical inputs surfaced.
* `C3PeriodLatticeStokesInputs.periodVector_eq_zero_of_boundary` —
  Stokes-vanishing of `periodVector` against smooth boundaries.
* `C3PeriodLatticeStokesInputs.homologySpans_holds` — derivation of the
  unrefactored `homologySpans` predicate.
* `C3PeriodLatticeStokesInputs.toClassical` — projection to
  `C3PeriodLatticeClassicalInputs`.
* `C3PeriodLatticeStokesInputs.toBundle` — convenience composition to
  `PeriodLatticeSymplecticBundle`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **Refactored classical inputs for the period-lattice symplectic
bundle.** Splits `C3PeriodLatticeClassicalInputs.homologySpans` into the
two textbook-distinct classical inputs: Stokes for holomorphic 1-forms
(packaged as a `StokesBoundaryInvariance` bundle plus a
"closed-holomorphic" hypothesis), and homology generation (every smooth
cycle is, modulo a Stokes-boundary, a ℤ-combination of the chosen
generators).

Fields:

* `cycleGens` — tuple of `2g` smooth cycle generators (symplectic basis
  representatives), as in the unrefactored bundle.
* `riemannBilinear` — ℝ-linear independence of their period vectors, as
  in the unrefactored bundle.
* `stokes` — a `StokesBoundaryInvariance 𝓘(ℝ, ℂ) X` bundle: a chosen
  subgroup of smooth Stokes-boundaries and a chosen submodule of closed
  real 1-forms, with the standard vanishing hypothesis on integrals
  over the boundaries.
* `holomorphic_closed` — every holomorphic 1-form is closed-holomorphic
  in the sense of `stokes.closedHolomorphicForms`, i.e. its real and
  imaginary components are Stokes-closed. On a compact complex
  1-manifold this is automatic because a holomorphic 1-form is
  d-closed (`dω = 0` for any type-(1,0) form on a 1-complex-dimensional
  manifold).
* `homologyGeneration` — every smooth cycle differs from a
  ℤ-combination of `cycleGens` by an element of `stokes.boundaries`.
-/
structure C3PeriodLatticeStokesInputs
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
  /-- Stokes-boundary-invariance data: a chosen subgroup of smooth
  boundaries and a chosen submodule of closed real 1-forms, with the
  vanishing hypothesis. -/
  stokes : StokesBoundaryInvariance 𝓘(ℝ, ℂ) X
  /-- Every holomorphic 1-form is Stokes-closed (its real and imaginary
  components lie in `stokes.closedForms`). Automatic on a compact
  complex 1-manifold. -/
  holomorphic_closed :
    ∀ om : HolomorphicOneForm X, om ∈ stokes.closedHolomorphicForms
  /-- Homology generation: every smooth cycle differs from a
  ℤ-combination of `cycleGens` by a Stokes-boundary. -/
  homologyGeneration :
    ∀ γ : (PeriodPairingData.ofSmoothCycle X).H1,
      ∃ (n : Fin (2 * JacobianChallenge.genus X) → ℤ)
        (b : (PeriodPairingData.ofSmoothCycle X).H1),
        b ∈ stokes.boundaries ∧
          γ = (∑ i, n i • cycleGens i) + b

namespace C3PeriodLatticeStokesInputs

variable
    {basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
    (inputs : C3PeriodLatticeStokesInputs basis)

/-- **Stokes-vanishing of `periodVector` on smooth boundaries.** Each
component of the period vector is `complexPeriod b (basis j) = 0` by
`StokesBoundaryInvariance.complexPeriod_eq_zero_of_boundary` (the basis
form is closed-holomorphic by `holomorphic_closed`). -/
lemma periodVector_eq_zero_of_boundary
    {b : (PeriodPairingData.ofSmoothCycle X).H1}
    (hb : b ∈ inputs.stokes.boundaries) :
    periodVector (PeriodPairingData.ofSmoothCycle X) basis b = 0 := by
  funext j
  show PeriodPairing (PeriodPairingData.ofSmoothCycle X) b (basis j) = 0
  rw [PeriodPairing_ofSmoothCycle]
  exact inputs.stokes.complexPeriod_eq_zero_of_boundary hb
    (inputs.holomorphic_closed (basis j))

/-- **`homologySpans` derived from Stokes + homology generation.** Given
the refactored inputs, every smooth cycle's period vector lies in the
ℤ-span of the `cycleGens`' periods. The proof factors as: write
`γ = (∑ n i • cycleGens i) + b` with `b` a Stokes-boundary
(homology generation); apply `periodVector` and split additively;
the boundary contribution vanishes by Stokes; the remaining sum is a
ℤ-combination of `cycleGens`-periods, hence in the ℤ-span. -/
lemma homologySpans_holds (γ : (PeriodPairingData.ofSmoothCycle X).H1) :
    periodVector (PeriodPairingData.ofSmoothCycle X) basis γ ∈
      Submodule.span ℤ
        (Set.range
          (fun i : Fin (2 * JacobianChallenge.genus X) =>
            periodVector (PeriodPairingData.ofSmoothCycle X) basis
              (inputs.cycleGens i))) := by
  obtain ⟨n, b, hb, hγ⟩ := inputs.homologyGeneration γ
  -- Step 1. periodVector γ = periodVector (∑ n i • cycleGens i) + periodVector b.
  have h_add :
      periodVector (PeriodPairingData.ofSmoothCycle X) basis γ =
        periodVector (PeriodPairingData.ofSmoothCycle X) basis
          (∑ i, n i • inputs.cycleGens i) +
        periodVector (PeriodPairingData.ofSmoothCycle X) basis b := by
    rw [hγ]
    exact periodVector_add_left (PeriodPairingData.ofSmoothCycle X) basis _ _
  -- Step 2. periodVector b = 0 by Stokes.
  have h_b :
      periodVector (PeriodPairingData.ofSmoothCycle X) basis b = 0 :=
    inputs.periodVector_eq_zero_of_boundary hb
  rw [h_add, h_b, add_zero]
  -- Step 3. periodVector (∑ n i • cycleGens i) = ∑ n i • periodVector (cycleGens i),
  -- via the bundled `periodVectorHom` and `AddMonoidHom.map_zsmul`.
  have h_sum :
      periodVector (PeriodPairingData.ofSmoothCycle X) basis
          (∑ i, n i • inputs.cycleGens i) =
        ∑ i, n i • periodVector (PeriodPairingData.ofSmoothCycle X) basis
              (inputs.cycleGens i) := by
    have h_eq :
        periodVector (PeriodPairingData.ofSmoothCycle X) basis
            (∑ i, n i • inputs.cycleGens i)
          = periodVectorHom (PeriodPairingData.ofSmoothCycle X) basis
            (∑ i, n i • inputs.cycleGens i) := rfl
    rw [h_eq, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [AddMonoidHom.map_zsmul]
    rfl
  rw [h_sum]
  -- Step 4. The ℤ-combination is in the ℤ-span of the generators' periods.
  refine Submodule.sum_mem _ (fun i _ => ?_)
  exact Submodule.smul_mem _ (n i) (Submodule.subset_span ⟨i, rfl⟩)

/-- **Conversion to `C3PeriodLatticeClassicalInputs`.** Derive the bundled
`homologySpans` field from Stokes + homology generation. -/
noncomputable def toClassical : C3PeriodLatticeClassicalInputs basis where
  cycleGens := inputs.cycleGens
  riemannBilinear := inputs.riemannBilinear
  homologySpans := inputs.homologySpans_holds

/-- **Convenience composition to `PeriodLatticeSymplecticBundle`.** -/
noncomputable def toBundle :
    PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) basis :=
  inputs.toClassical.toBundle

end C3PeriodLatticeStokesInputs

end JacobianChallenge

end
