/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LinearSystemGermDeltaPFiniteDimTransport
import JacobianChallenge.Manifold.RiemannSphereSimplePole
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `LinearSystemGermDeltaPFiniteDim RiemannSphere` from two named inputs

This file architecturally reduces the named hypothesis
`LinearSystemGermDeltaPFiniteDim RiemannSphere`
(`∀ p : RS, Module.Finite ℂ (linearSystemGermDeltaP p)`) to **exactly
two named classical inputs**:

1. **`LinearSystemAtInftyRS_BoundedBySimplePoleSpan`** — the
   polynomial-growth Liouville bound at `∞`: every germ in `L(δ∞)` on
   the Riemann sphere is a ℂ-linear combination of the constant `1`
   and the canonical simple-pole germ `RSSimplePoleGerm`. Equivalently,
   `L(δ∞) ≤ Submodule.span ℂ {1, RSSimplePoleGerm}`.

2. **`ExistsMobiusToInftyRS`** — the Möbius group acts transitively on
   `RiemannSphere`: for every `p : RS`, there is a `HolomorphicEquiv
   RiemannSphere RiemannSphere` taking `p` to `∞`.

Under these two inputs, the conclusion is unconditional.

The chip composes three pieces:

* A **per-point** version of the finite-dim transport
  (`linearSystemGermDeltaPLinearEquiv_via_holomorphicEquiv` already
  exists; we wrap it into a pointwise `Module.Finite` statement).
* A pure linear-algebra step "submodule of finite-span is
  finite-dim" via `Module.Finite.of_injective` applied to
  `Submodule.inclusion`.
* The final composition: from the Liouville bound at `∞`, obtain
  `Module.Finite ℂ (L(δ∞))`; from Möbius transitivity, transport to
  every `p`.

## What this chip does NOT do

The two named inputs are **not** discharged in this chip:

* `LinearSystemAtInftyRS_BoundedBySimplePoleSpan` is the analytic
  Liouville-polynomial bound (entire `ℂ → ℂ` with `|f(z)| = O(|z|)` at
  infinity is a polynomial of degree `≤ 1`). Mathlib at the pin has
  the basic Liouville theorem
  (`Complex.liouville_theorem_aux`: bounded entire is constant) but
  not the polynomial-growth extension. Discharging this in-tree would
  pass through Cauchy's derivative estimate
  (`norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`, available)
  to vanish higher derivatives, followed by an analyticity argument.

* `ExistsMobiusToInftyRS` is the Möbius transitivity statement. For
  finite `z₀ ∈ ℂ`, the candidate Möbius map is `z ↦ z + z₀` (RS-side:
  `coe w ↦ coe (w + z₀)`, `∞ ↦ ∞`) composed with the antipode
  `z ↦ 1/z` (RS-side: `coe 0 ↦ ∞`, `∞ ↦ coe 0`, `coe w ↦ coe (1/w)`
  for `w ≠ 0`). Packaging these as `HolomorphicEquiv`s requires
  checking smoothness in both directions on the two-chart atlas.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff OnePoint
open Filter Set

namespace JacobianChallenge.MeromorphicFunctionField

universe u v

open JacobianChallenge

/-! ## Per-point finite-dim transport via `HolomorphicEquiv` -/

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable {Y : Type v}
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-- **Per-point version of `LinearSystemGermDeltaPFiniteDim.of_holomorphicEquiv`.**
Given a `HolomorphicEquiv X Y` and a point `p : X`, finite-dimensionality
of `linearSystemGermDeltaP (e p)` transports to `linearSystemGermDeltaP p`
via `linearSystemGermDeltaPLinearEquiv_via_holomorphicEquiv`. -/
theorem linearSystemGermDeltaP_finite_of_holomorphicEquiv
    (e : HolomorphicEquiv X Y) (p : X)
    (h : Module.Finite ℂ (linearSystemGermDeltaP (e p))) :
    Module.Finite ℂ (linearSystemGermDeltaP p) := by
  haveI := h
  exact Module.Finite.equiv
    (linearSystemGermDeltaPLinearEquiv_via_holomorphicEquiv e p)

/-! ## Module.Finite from inclusion in a finite-span Submodule -/

/-- A general linear-algebra fact specialised to `linearSystemGermDeltaP`:
if `L(δp)` is contained in the ℂ-span of two specific germs, then it is
finite-dimensional. The proof uses `Module.Finite.span_of_finite` plus
`Module.Finite.of_injective` on `Submodule.inclusion`. -/
theorem linearSystemGermDeltaP_finite_of_le_span_pair
    (p : X) (ψ : MeromorphicFunctionGerm X)
    (h_le : linearSystemGermDeltaP p
        ≤ Submodule.span ℂ
            ({(1 : MeromorphicFunctionGerm X), ψ} : Set _)) :
    Module.Finite ℂ (linearSystemGermDeltaP p) := by
  -- The span of a finite set is `Module.Finite`.
  have h_set_finite : Set.Finite
      ({(1 : MeromorphicFunctionGerm X), ψ} : Set _) :=
    (Set.finite_singleton _).insert _
  haveI h_span_finite : Module.Finite ℂ
      ((Submodule.span ℂ
          ({(1 : MeromorphicFunctionGerm X), ψ} : Set _))
        : Submodule ℂ (MeromorphicFunctionGerm X)) :=
    Module.Finite.span_of_finite ℂ h_set_finite
  -- The inclusion `L(δp) →ₗ[ℂ] span ℂ {1, ψ}` is injective, so
  -- `L(δp)` is finite-dim as a submodule of a finite-dim space.
  exact Module.Finite.of_injective
    (Submodule.inclusion h_le)
    (Submodule.inclusion_injective h_le)

end JacobianChallenge.MeromorphicFunctionField

/-! ## The two named classical inputs (on `RiemannSphere`) -/

namespace JacobianChallenge.MeromorphicFunctionField

open JacobianChallenge

/-- **Named analytic hypothesis** ("Liouville-polynomial bound at `∞`"):
on the Riemann sphere, every germ in `linearSystemGermDeltaP (∞ : RS)`
lies in the `ℂ`-span of the constant `1` and the canonical simple-pole
germ `RSSimplePoleGerm`.

Classical content: an entire function `f : ℂ → ℂ` with growth
`|f(z)| = O(|z|)` at infinity is a polynomial of degree `≤ 1`. This is
the polynomial-growth generalization of Liouville's theorem. Mathlib at
the pin (`Mathlib.Analysis.Complex.Liouville`) has the basic Liouville
result (bounded entire is constant) but not the polynomial-growth
extension; a Cauchy-estimate-based proof would yield it. -/
def LinearSystemAtInftyRS_BoundedBySimplePoleSpan : Prop :=
  linearSystemGermDeltaP (∞ : RiemannSphere)
    ≤ Submodule.span ℂ
        ({(1 : MeromorphicFunctionGerm RiemannSphere), RSSimplePoleGerm}
          : Set _)

/-- **Named existence hypothesis** ("Möbius transitivity on `RS`"): for
every `p : RiemannSphere`, there exists a `HolomorphicEquiv
RiemannSphere RiemannSphere` taking `p` to `∞`.

Classical content: the Möbius group `PSL(2, ℂ)` acts transitively on
the Riemann sphere. Concrete witnesses:

* `p = ∞`: take the identity `HolomorphicEquiv.refl`.
* `p = (z₀ : RS)` finite: compose the antipode `z ↦ 1/z` (sending
  `0 ↦ ∞` and `coe z ↦ coe z⁻¹` for `z ≠ 0`) with a translation
  `z ↦ z - z₀` (on the `ℂ`-side coordinates). The composite takes
  `(z₀ : RS) ↦ (0 : RS) ↦ ∞`.

Packaging each as a `HolomorphicEquiv RS RS` requires checking
smoothness on the two-chart atlas in both directions. -/
def ExistsMobiusToInftyRS : Prop :=
  ∀ p : RiemannSphere,
    ∃ e : HolomorphicEquiv RiemannSphere RiemannSphere,
      e p = (∞ : RiemannSphere)

/-! ## Stepping-stone: `Module.Finite` at `∞` from the polynomial bound -/

/-- From the Liouville-polynomial bound at `∞`, conclude
`Module.Finite ℂ (linearSystemGermDeltaP (∞ : RS))`. -/
theorem linearSystemGermDeltaP_finite_at_infty_of_polyBound
    (h : LinearSystemAtInftyRS_BoundedBySimplePoleSpan) :
    Module.Finite ℂ (linearSystemGermDeltaP (∞ : RiemannSphere)) :=
  linearSystemGermDeltaP_finite_of_le_span_pair
    (X := RiemannSphere) (∞ : RiemannSphere) RSSimplePoleGerm h

/-! ## Final assembly -/

/-- **`LinearSystemGermDeltaPFiniteDim RiemannSphere`** from the two
named classical inputs `LinearSystemAtInftyRS_BoundedBySimplePoleSpan`
and `ExistsMobiusToInftyRS`.

The composition is direct:

1. The polynomial bound gives `Module.Finite ℂ (L(δ∞))`.
2. For arbitrary `p : RS`, Möbius transitivity supplies `e : HolomorphicEquiv RS RS`
   with `e p = ∞`. The per-point transport
   (`linearSystemGermDeltaP_finite_of_holomorphicEquiv`) lifts the
   finiteness at `e p = ∞` back to `p`. -/
theorem linearSystemGermDeltaPFiniteDim_RiemannSphere
    (h_polyBound : LinearSystemAtInftyRS_BoundedBySimplePoleSpan)
    (h_mobius : ExistsMobiusToInftyRS) :
    LinearSystemGermDeltaPFiniteDim RiemannSphere := by
  intro p
  obtain ⟨e, h_e_p⟩ := h_mobius p
  -- `Module.Finite ℂ (linearSystemGermDeltaP (e p))`, by `e p = ∞`.
  have h_at_ep : Module.Finite ℂ (linearSystemGermDeltaP (e p)) := by
    rw [h_e_p]
    exact linearSystemGermDeltaP_finite_at_infty_of_polyBound h_polyBound
  -- Transport along `e` to `p`.
  exact linearSystemGermDeltaP_finite_of_holomorphicEquiv e p h_at_ep

end JacobianChallenge.MeromorphicFunctionField

end
