/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.SurfaceClassificationGenus
import JacobianChallenge.Manifold.HolomorphicOneFormLinear
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

set_option diagnostics.threshold 100

/-! # `S2ImpliesGenus0 X` from two clean classical inputs

`S2ImpliesGenus0 X := Nonempty (X ≃ₜ StandardS2) → genus X = 0` is the
reverse leg of challenge item 14. Its classical proof goes through
**simple-connectedness**:

  `X ≃ₜ S² ⇒ SimplyConnectedSpace X ⇒ Subsingleton (HolomorphicOneForm X) ⇒ genus X = 0`.

This file performs the **architectural reduction** that splits
`S2ImpliesGenus0 X` into the two precise classical inputs that the
above chain depends on:

1. `SimplyConnectedSpace StandardS2` — a *topological* fact (π₁(S²) is
   trivial). Mathlib at the pin (`8e3c989...`) defines
   `SimplyConnectedSpace` but does not yet have an instance for the
   2-sphere; this is a small mathlib gap.

2. `HolomorphicOneFormSubsingletonOfSimplyConnected X` — the *analytic*
   bridge: on a simply-connected compact connected complex 1-manifold,
   every holomorphic 1-form is zero. The classical proof: any
   holomorphic 1-form ω has zero period over every closed cycle (by
   simple-connectedness via `Stokes` on the homotopy disk), hence admits
   a global holomorphic primitive `F : X → ℂ`. The repository's already-
   proven `liouvilleOnCompactConnected_holds` forces `F` to be constant,
   so `ω = dF = 0`. The primitive existence requires Stokes-style
   boundary invariance which is itself a named hypothesis elsewhere in
   the repo (`StokesBoundaryInvariance`); we therefore expose this whole
   chain as a single named input.

The point of this reduction: it replaces the broad-strokes
"geometric vs topological genus bridge" rhetoric in
`SurfaceClassificationGenus.lean`'s comment for `S2ImpliesGenus0` with
**two specific, citable classical facts**, both of which are individually
attainable (the first is a small mathlib chip, the second a
2-3-chip analytic arc using existing repo infrastructure).

The downstream Item-14 reverse leg now sits on
`S2ImpliesGenus0FromSimplyConnected`'s two inputs rather than the
single coarse `S2ImpliesGenus0` Prop.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Named classical inputs -/

/-- **Topological input.** The standard 2-sphere is simply connected.
Mathlib at the pin has the `SimplyConnectedSpace` class and the
fundamental-groupoid machinery, but no instance for
`Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`. The named hypothesis
isolates this small mathlib gap. -/
def SimplyConnectedS2 : Prop :=
  SimplyConnectedSpace JacobianChallenge.StandardS2

/-- **Analytic input.** On a simply-connected compact connected complex
1-manifold, every holomorphic 1-form is the zero form. Equivalently,
`HolomorphicOneForm X` is a `Subsingleton`.

Classical proof: a holomorphic 1-form `ω` on a connected complex
1-manifold is automatically closed (`dω = 0`, since `Ω²(X) = 0` in
real dimension 2). On a simply connected space, every closed 1-form
admits a global primitive `F : X → ℂ` (Poincaré / Stokes on the
homotopy disk between any two paths). `F` is holomorphic because `ω`
is; on a compact connected `X`, Liouville
(`liouvilleOnCompactConnected_holds`, in
`Topology/HolomorphicLocallyConstantDischarge.lean`) forces `F`
constant, hence `ω = dF = 0`.

The primitive-existence step depends on
`StokesBoundaryInvariance` — already a named hypothesis elsewhere in
the repo — so we expose this whole conditional chain as a single
input. -/
def HolomorphicOneFormSubsingletonOfSimplyConnected : Prop :=
  SimplyConnectedSpace X → Subsingleton (HolomorphicOneForm X)

/-! ## The architectural reduction -/

/-- **`S2ImpliesGenus0 X` from the two classical inputs.** Composes:

* The mathlib transport
  `ContinuousMap.HomotopyEquiv.simplyConnectedSpace` along the
  `Homeomorph.toHomotopyEquiv` of `X ≃ₜ StandardS2`, applied to
  `SimplyConnectedS2`, to obtain `SimplyConnectedSpace X`.
* The analytic input
  `HolomorphicOneFormSubsingletonOfSimplyConnected X` to obtain
  `Subsingleton (HolomorphicOneForm X)`.
* The unconditional repo lemma
  `genus_eq_zero_of_holomorphicOneForm_subsingleton` to conclude
  `genus X = 0`.

This is the **complete** reduction of `S2ImpliesGenus0 X` to the two
classical inputs above; no other hypotheses are needed. -/
theorem s2ImpliesGenus0_from_simplyConnected
    (h_S2_sc : SimplyConnectedS2)
    (h_sub : HolomorphicOneFormSubsingletonOfSimplyConnected X) :
    S2ImpliesGenus0 X := by
  intro ⟨e⟩
  -- Step 1: transport simple-connectedness through the homeomorphism.
  -- `e : X ≃ₜ StandardS2`, so `e.toHomotopyEquiv : X ≃ₕ StandardS2`.
  -- Then `ContinuousMap.HomotopyEquiv.simplyConnectedSpace` from mathlib.
  haveI : SimplyConnectedSpace JacobianChallenge.StandardS2 := h_S2_sc
  have h_sc : SimplyConnectedSpace X :=
    ContinuousMap.HomotopyEquiv.simplyConnectedSpace e.toHomotopyEquiv
  -- Step 2: analytic input ⇒ Subsingleton.
  have h_subsing : Subsingleton (HolomorphicOneForm X) := h_sub h_sc
  -- Step 3: Subsingleton ⇒ genus = 0 (unconditional repo lemma).
  exact genus_eq_zero_of_holomorphicOneForm_subsingleton X h_subsing

/-! ## Bundle assembly with the existing forward-leg path

Combines with `Item14ForwardFromFiniteDim`'s
`genus0ImpliesS2_from_existsSimplePoleGerm_and_finiteDim` to give the
full Item 14 biconditional under **four** classical inputs, all of
which are individually citable:

* `[FiniteDimensional ℂ (HolomorphicOneForm X)]` — Hodge finite-dim
  (typeclass; forward leg).
* `ExistsSimplePoleGermAtSomePoint X` — RR existence at genus 0
  (forward leg).
* `SimplyConnectedS2` — π₁(S²) trivial (this file, reverse leg).
* `HolomorphicOneFormSubsingletonOfSimplyConnected X` — simply-connected
  ⇒ subsingleton holomorphic 1-forms (this file, reverse leg).

This is a sharper reduction than the single broad `S2ImpliesGenus0 X`
hypothesis. -/

end JacobianChallenge

end
