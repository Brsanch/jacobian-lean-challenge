/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3PeriodLatticeStokesGenusZero
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option linter.unusedSectionVars false

/-! # Unconditional `C3PeriodLatticeStokesSpanTopInputs` on the Riemann sphere

The Riemann sphere case combines two unconditional facts in tree:

* `genus_RiemannSphere_eq_zero` (`Manifold/RiemannSphereChartSCoeffOverlap.lean`),
* `instance : Subsingleton (HolomorphicOneForm RiemannSphere)` (same file).

With both unconditional, `C3PeriodLatticeStokesSpanTopInputs.trivial_at_genus_zero`
fires on RiemannSphere for any chosen basis, producing an inhabitant of
the refactored period-lattice classical-input bundle. From there the
chain to `PeriodLatticeSymplecticBundle` is mechanical (`toBundle`).

This is the analogue, going through the refactored chain, of the
unconditional `PeriodLatticeSymplecticBundle.trivial_at_genus_zero`
already in tree. The added value is **structural**: future consumers
that want to fix a chosen basis and a chosen set of classical inputs
on a per-X basis have an example showing the full chain compiles
end-to-end at the genus-0 corner.

## Net contribution

* `nonempty_C3PeriodLatticeStokesSpanTopInputs_RiemannSphere` —
  unconditional `Nonempty` instance.
* `periodLatticeSymplecticBundle_RiemannSphere_of_stokesSpanTop` —
  the resulting `PeriodLatticeSymplecticBundle` term on RS via the
  refactored chain.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

/-- **`C3PeriodLatticeStokesSpanTopInputs` for `RiemannSphere` is
unconditionally inhabited.** Uses `genus_RiemannSphere_eq_zero` +
the unconditional `Subsingleton (HolomorphicOneForm RiemannSphere)`
instance to fire `trivial_at_genus_zero`. -/
theorem nonempty_C3PeriodLatticeStokesSpanTopInputs_RiemannSphere
    (basis :
      Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
        (HolomorphicOneForm RiemannSphere)) :
    Nonempty (C3PeriodLatticeStokesSpanTopInputs basis) :=
  ⟨C3PeriodLatticeStokesSpanTopInputs.trivial_at_genus_zero
    (X := RiemannSphere) basis
    JacobianChallenge.RiemannSphere.genus_RiemannSphere_eq_zero⟩

/-- **`PeriodLatticeSymplecticBundle` on `RiemannSphere` via the
refactored chain.** Composes
`nonempty_C3PeriodLatticeStokesSpanTopInputs_RiemannSphere` with
`toBundle`. -/
noncomputable def periodLatticeSymplecticBundle_RiemannSphere_of_stokesSpanTop
    (basis :
      Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
        (HolomorphicOneForm RiemannSphere)) :
    PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle RiemannSphere) basis :=
  (C3PeriodLatticeStokesSpanTopInputs.trivial_at_genus_zero
    (X := RiemannSphere) basis
    JacobianChallenge.RiemannSphere.genus_RiemannSphere_eq_zero).toBundle

end JacobianChallenge

end
