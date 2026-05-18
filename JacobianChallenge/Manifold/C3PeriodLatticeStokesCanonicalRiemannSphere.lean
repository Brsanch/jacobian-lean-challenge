/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3PeriodLatticeStokesCanonicalTrivialAtGenusZero
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option linter.unusedSectionVars false

/-! # Riemann-sphere headline via the canonical Stokes bundle

The legacy headline `nonempty_C3PeriodLatticeStokesSpanTopInputs_RiemannSphere`
(in `C3PeriodLatticeStokesRiemannSphere.lean`) is unconditional but uses
an unconventional Stokes bundle (`boundaries := ⊤, closedForms := ⊥`).

This file ships the parallel headline via the **canonical** Stokes
bundle. It composes:

* `JacobianChallenge.RiemannSphere.genus_RiemannSphere_eq_zero`
  (unconditional);
* `instance : Subsingleton (HolomorphicOneForm RiemannSphere)`
  (unconditional, from `RiemannSphereChartSCoeffOverlap.lean`);
* a `Subsingleton (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ)
  RiemannSphere).H1` hypothesis (the unproven "H₁(S²; ℤ) = 0" content,
  surfaced here as a single named typeclass hypothesis on the
  canonical Stokes quotient).

The third hypothesis is the residual classical input for the genus-0
case of the canonical-bundle headline. Classically it is `H₁(S²; ℤ) = 0`
(a consequence of `π₁(S²) = 0` + smooth singular homology theory); the
unconditional formalisation of this fact is a substantial separate
arc not at the mathlib pin.

## What this file ships

* `nonempty_C3PeriodLatticeStokesSpanTopInputs_RiemannSphere_canonical` —
  the canonical-bundle headline, conditional on the canonical-H₁
  subsingleton hypothesis.
* `periodLatticeSymplecticBundle_RiemannSphere_canonical` — the
  resulting `PeriodLatticeSymplecticBundle` on RS via the canonical
  chain.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

/-- **Canonical-bundle headline for `RiemannSphere`, conditional on
the canonical-H₁ subsingleton hypothesis.** -/
theorem nonempty_C3PeriodLatticeStokesSpanTopInputs_RiemannSphere_canonical
    [Subsingleton (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ)
        RiemannSphere).H1]
    (basis :
      Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
        (HolomorphicOneForm RiemannSphere)) :
    Nonempty (C3PeriodLatticeStokesSpanTopInputs basis) :=
  ⟨C3PeriodLatticeStokesSpanTopInputs.trivial_at_genus_zero_canonical
    (X := RiemannSphere) basis
    JacobianChallenge.RiemannSphere.genus_RiemannSphere_eq_zero⟩

/-- **`PeriodLatticeSymplecticBundle` on `RiemannSphere` via the
canonical chain**, conditional on the canonical-H₁ subsingleton. -/
noncomputable def periodLatticeSymplecticBundle_RiemannSphere_canonical
    [Subsingleton (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ)
        RiemannSphere).H1]
    (basis :
      Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
        (HolomorphicOneForm RiemannSphere)) :
    PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle RiemannSphere) basis :=
  (C3PeriodLatticeStokesSpanTopInputs.trivial_at_genus_zero_canonical
    (X := RiemannSphere) basis
    JacobianChallenge.RiemannSphere.genus_RiemannSphere_eq_zero).toBundle

end JacobianChallenge

end
