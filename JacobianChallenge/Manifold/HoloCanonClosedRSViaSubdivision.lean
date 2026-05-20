/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SubdivisionTelescopingFromSubsingleton
import JacobianChallenge.Manifold.HolomorphicOneFormRiemannSphereInstances

set_option linter.unusedSectionVars false

/-! # `HolomorphicComponentsCanonicalClosed RiemannSphere` via the subdivision route

This file ships the **alternate route** to
`HolomorphicComponentsCanonicalClosed RiemannSphere`, going through:

1. `subdivisionTelescopingTo2Simplex_of_subsingleton` — discharge of
   `SubdivisionTelescopingTo2Simplex_named RiemannSphere` via the
   in-tree `Subsingleton (HolomorphicOneForm RiemannSphere)` instance.
2. `holomorphicComponentsCanonicalClosed_of_subdivisionTo2Simplex` —
   the named reduction from `ChartContainedSmooth2Simplex.lean`.

The existing in-tree `HolomorphicComponentsCanonicalClosed.of_subsingleton`
provides the SAME conclusion via a shorter direct route (one-step
subsingleton discharge). This file routes through the new subdivision
infrastructure to demonstrate that:

* The unconditional `pointwiseChartEvalIdentity` chain works.
* The chart-contained 2-simplex Stokes pipeline composes correctly.
* The four-named-atom reduction is functionally exercised on RS.

## What this file ships

* `holomorphicComponentsCanonicalClosed_RS_via_subdivision` — the
  alternate-route theorem.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

/-- **`HolomorphicComponentsCanonicalClosed RiemannSphere` via the
2-simplex subdivision route.**

Composes `subdivisionTelescopingTo2Simplex_of_subsingleton` (using
the in-tree `Subsingleton (HolomorphicOneForm RiemannSphere)`) with
`holomorphicComponentsCanonicalClosed_of_subdivisionTo2Simplex`. -/
theorem holomorphicComponentsCanonicalClosed_RS_via_subdivision :
    HolomorphicComponentsCanonicalClosed RiemannSphere :=
  holomorphicComponentsCanonicalClosed_of_subdivisionTo2Simplex
    (subdivisionTelescopingTo2Simplex_of_subsingleton (X := RiemannSphere))

end JacobianChallenge

end
