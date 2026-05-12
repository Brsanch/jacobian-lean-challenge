/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HodgeRiemannSphereUnconditional

set_option diagnostics.threshold 100

/-! # Global `Module.Finite` / `FiniteDimensional` instances for `HolomorphicOneForm RiemannSphere`

zz279 ships `holomorphicOneFormFiniteDim_riemannSphere_unconditional` as a
theorem-valued discharge. To make every downstream call site that wants
`[Module.Finite ℂ (HolomorphicOneForm RiemannSphere)]` or
`[FiniteDimensional ℂ (HolomorphicOneForm RiemannSphere)]` typeclass-free,
we promote zz279's theorem to global `instance`s here.

Both instances are derivable from the unconditional
`Subsingleton (HolomorphicOneForm RiemannSphere)` instance shipped by
zz274 (`Manifold/RiemannSphereChartSCoeffOverlap.lean`):

* `Subsingleton → Module.Finite` via `moduleFinite_of_subsingleton`.
* `Module.Finite ℂ V → FiniteDimensional ℂ V` (a mathlib definitional
  identity at the pin: `FiniteDimensional` is `Module.Finite`).

The point of this file is purely instance-availability: callers no longer
need to invoke the discharge theorem manually; mathlib's typeclass search
finds the instance.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-- **Global instance.** `HolomorphicOneForm RiemannSphere` is a
finite `ℂ`-module. Unconditional via zz274's subsingleton instance. -/
noncomputable instance instModuleFiniteHolomorphicOneFormRiemannSphere :
    Module.Finite ℂ (HolomorphicOneForm JacobianChallenge.RiemannSphere) :=
  holomorphicOneFormFiniteDim_riemannSphere_unconditional

/-- **Global instance.** `HolomorphicOneForm RiemannSphere` is a
finite-dimensional `ℂ`-vector space. Unconditional via zz274. -/
noncomputable instance instFiniteDimensionalHolomorphicOneFormRiemannSphere :
    FiniteDimensional ℂ (HolomorphicOneForm JacobianChallenge.RiemannSphere) :=
  inferInstance

/-- **Genus of the Riemann sphere as a `simp`-friendly equation.** With
the finite-dim instance in scope, `genus RiemannSphere = 0` is a
`@[simp]`-ready closed form. (The underlying theorem is zz274's
`genus_RiemannSphere_eq_zero`; we record it here under a name that
matches the in-namespace convention used by zz279.) -/
@[simp] theorem genus_RiemannSphere_eq_zero_simp :
    JacobianChallenge.genus JacobianChallenge.RiemannSphere = 0 :=
  JacobianChallenge.RiemannSphere.genus_RiemannSphere_eq_zero

end RiemannSphere

end JacobianChallenge
