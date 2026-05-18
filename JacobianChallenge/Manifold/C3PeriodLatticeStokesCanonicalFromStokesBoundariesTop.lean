/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3PeriodLatticeStokesCanonicalTrivialAtGenusZero
import JacobianChallenge.Manifold.StokesCanonicalH1SubsingletonChar

set_option linter.unusedSectionVars false

/-! # Trivial-at-genus-zero canonical bundle with `stokesBoundaries = ⊤` input

The canonical-bundle headline
`C3PeriodLatticeStokesSpanTopInputs.trivial_at_genus_zero_canonical`
takes the H₁-quotient subsingleton hypothesis. Via the
`H1SubsingletonChar` chip, this is *equivalent* to the SmoothCycle-
level statement `stokesBoundaries I X = ⊤`. This file exposes the
alternative-formulation constructor where the consumer supplies the
SmoothCycle-level hypothesis directly.

Useful for downstream chips that prove `stokesBoundaries = ⊤` via
direct cycle-by-cycle construction (e.g., the future smooth Hurewicz
route: simply-connected + smooth singular Hurewicz → every smooth
1-cycle is a 2-chain boundary → `stokesBoundaries = ⊤`).

## What this file ships

* `trivial_at_genus_zero_canonical_of_stokesBoundaries_top` — the
  alternative-formulation constructor.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **Alternative-formulation constructor.** Replaces the
H₁-subsingleton typeclass hypothesis of
`trivial_at_genus_zero_canonical` with the SmoothCycle-level
hypothesis `stokesBoundaries 𝓘(ℝ, ℂ) X = ⊤`. Useful for downstream
chips that prove `stokesBoundaries = ⊤` via direct cycle-by-cycle
construction. -/
noncomputable def
  C3PeriodLatticeStokesSpanTopInputs.trivial_at_genus_zero_canonical_of_stokesBoundaries_top
    [Subsingleton (HolomorphicOneForm X)]
    (h_stokes_top : stokesBoundaries 𝓘(ℝ, ℂ) X = ⊤)
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (hgenus : JacobianChallenge.genus X = 0) :
    C3PeriodLatticeStokesSpanTopInputs basis :=
  haveI : Subsingleton (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).H1 :=
    subsingleton_canonical_H1_of_stokesBoundaries_eq_top h_stokes_top
  C3PeriodLatticeStokesSpanTopInputs.trivial_at_genus_zero_canonical
    basis hgenus

/-! ## Nonempty version for downstream consumers -/

/-- **Nonempty alternative-formulation constructor.** Same as
`trivial_at_genus_zero_canonical_of_stokesBoundaries_top` but returns
a `Nonempty` instance instead of a definitional term — convenient for
downstream consumers that just want existence. -/
theorem nonempty_C3PeriodLatticeStokesSpanTopInputs_canonical_of_stokesBoundaries_top
    [Subsingleton (HolomorphicOneForm X)]
    (h_stokes_top : stokesBoundaries 𝓘(ℝ, ℂ) X = ⊤)
    (basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (hgenus : JacobianChallenge.genus X = 0) :
    Nonempty (C3PeriodLatticeStokesSpanTopInputs basis) :=
  ⟨C3PeriodLatticeStokesSpanTopInputs.trivial_at_genus_zero_canonical_of_stokesBoundaries_top
    h_stokes_top basis hgenus⟩

end JacobianChallenge

end
