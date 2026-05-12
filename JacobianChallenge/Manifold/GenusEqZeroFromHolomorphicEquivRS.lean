/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicEquivGenusInvariance
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option diagnostics.threshold 100

/-! # `genus X = 0` from `HolomorphicEquiv X RS` — clean route via zz310

This file provides a clean alternate one-line proof of
`genus_eq_zero_of_holomorphicEquiv_RiemannSphere` using:

* zz310's `HolomorphicEquiv.genus_eq` — `e : HolomorphicEquiv X Y` gives
  `genus X = genus Y` unconditionally.
* zz274's `genus_RiemannSphere_eq_zero` — `genus RS = 0` unconditionally.

Proof is `e.genus_eq ▸ genus_RiemannSphere_eq_zero` — one line, no
appeal to the Subsingleton route that zz307 uses.

This is the most compressed proof currently available. Useful as a
sanity-check and as a model for "any X biholomorphic to a known-genus
surface inherits the genus" patterns once we have more concrete
example surfaces.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

namespace JacobianChallenge

variable {X : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **`genus X = 0` from a biholomorphism with the Riemann sphere —
clean route.** Single-step via zz310's `HolomorphicEquiv.genus_eq`
plus zz274's `genus_RiemannSphere_eq_zero`. Both ingredients are
unconditional. -/
theorem genus_eq_zero_of_HolomorphicEquiv_RiemannSphere_clean
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere) :
    JacobianChallenge.genus X = 0 :=
  e.genus_eq.trans RiemannSphere.genus_RiemannSphere_eq_zero

/-- **`Nonempty` form.** Convenience wrapper. -/
theorem genus_eq_zero_of_nonempty_HolomorphicEquiv_RiemannSphere
    (h : Nonempty (HolomorphicEquiv X JacobianChallenge.RiemannSphere)) :
    JacobianChallenge.genus X = 0 :=
  h.elim genus_eq_zero_of_HolomorphicEquiv_RiemannSphere_clean

end JacobianChallenge
