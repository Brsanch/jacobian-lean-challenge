/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphereTranslate

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Möbius transitivity on the Riemann sphere

The Möbius group `PSL(2, ℂ)` acts transitively on the Riemann sphere.
For the genus-0 Riemann–Roch reduction, the relevant statement is the
unconditional existence of a self-biholomorphism `e : HolomorphicEquiv
RiemannSphere RiemannSphere` sending an arbitrary point `p : RS` to
`∞`. Two concrete witnesses suffice:

* `p = ∞`: take `HolomorphicEquiv.refl`.
* `p = coe z₀`: compose `translateEquiv (-z₀)` (sending `coe z₀ ↦ coe 0`)
  with `antipodeEquiv` (sending `coe 0 ↦ ∞`).

Both `antipodeEquiv` (in `RiemannSphereAntipodeSmooth.lean`) and
`translateEquiv` (in `RiemannSphereTranslate.lean`) are unconditional
biholomorphisms. Their composition discharges the existence statement
without any open hypothesis.

## What ships

* `RiemannSphere.existsMobiusToInftyRS : ∀ p : RiemannSphere,
    ∃ e : HolomorphicEquiv RiemannSphere RiemannSphere,
      e p = (∞ : RiemannSphere)`

This is the exact statement of `ExistsMobiusToInftyRS` (Möbius-transitivity
input to `LinearSystemGermDeltaPFiniteDim RiemannSphere` in the genus-0
Riemann–Roch reduction tracked by Session A on `feat/linear-system-divisor`).
When that branch lands on main, the `_local`-suffixed name here can be
identified with that file's `ExistsMobiusToInftyRS` definitionally.

No `sorry`, no `axiom`. -/

open OnePoint
open scoped Manifold

namespace JacobianChallenge

namespace RiemannSphere

/-- **Möbius transitivity on the Riemann sphere.** For every point
`p : RiemannSphere`, there exists a self-biholomorphism of the Riemann
sphere mapping `p` to `∞`.

Concrete witnesses:

* `p = ∞`: the identity biholomorphism `HolomorphicEquiv.refl`.
* `p = coe z₀`: `(translateEquiv (-z₀)).trans antipodeEquiv`, which
  sends `coe z₀ ↦ coe 0 ↦ ∞` via the translation by `-z₀` followed
  by the antipode `z ↦ -1/z`. -/
theorem existsMobiusToInftyRS :
    ∀ p : RiemannSphere,
      ∃ e : JacobianChallenge.HolomorphicEquiv RiemannSphere RiemannSphere,
        e p = (∞ : RiemannSphere) := by
  intro p
  induction p using OnePoint.rec with
  | infty =>
    refine ⟨JacobianChallenge.HolomorphicEquiv.refl, ?_⟩
    rfl
  | coe z₀ =>
    -- (translateEquiv (-z₀)) sends coe z₀ ↦ coe 0; antipodeEquiv sends coe 0 ↦ ∞.
    refine ⟨(translateEquiv (-z₀)).trans antipodeEquiv, ?_⟩
    -- Evaluate the composition using Diffeomorph.trans_apply.
    show antipodeEquiv (translateEquiv (-z₀) ((z₀ : RiemannSphere))) = ∞
    rw [translateEquiv_apply, translateBy_coe]
    -- coe (z₀ + (-z₀)) = coe 0
    have h_zero : z₀ + (-z₀) = (0 : ℂ) := by ring
    rw [h_zero, antipodeEquiv_apply, antipode_coe_zero]

end RiemannSphere

end JacobianChallenge
