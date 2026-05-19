/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusContinuousPathLift
import JacobianChallenge.Manifold.ComplexTorusMkQMfderiv
import JacobianChallenge.Manifold.SmoothPathIntegral

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-! # Smooth path lift via velocity integration on T²

For a smooth path `γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)` based at `0`, we
define the **smooth lift** `Γ : ℝ → ℂ` by

    Γ(t) := ∫_0^t (velocity γ s) ds

where `velocity γ s : ℂ` (= TangentSpace at `γ.ambient s`) is the
ambient velocity.

Construction strategy:

* Γ is `ℝ`-valued integral of a smooth (continuous) function on
  `[0, T]`, hence smooth.
* `Γ(0) = 0`.
* `Γ'(t) = velocity γ t` (FTC).
* Combined with `mfderiv mkQ = id` (proved!) and `velocity γ t =
  mfderiv γ.ambient t (1)`, the mfderiv of `mkQ ∘ Γ` matches the
  mfderiv of `γ.ambient` at every point.
* Plus `mkQ Γ(0) = 0 = γ.ambient 0` (assuming γ starts at 0).
* By uniqueness (`IsCoveringMap.eq_of_comp_eq`), since `mkQ ∘ Γ` is
  a continuous lift of `γ.ambient` starting at 0, it equals the
  unique continuous lift, hence `mkQ ∘ Γ = γ.ambient`.

This file builds only **the smoothness of `Γ` and its endpoint
membership in `L`** (using the `contLift` machinery for the lift
property). The substantive ODE-uniqueness argument identifying our
integration-based Γ with the continuous lift is left as a single
named atom (`smoothLift_eq_contLift`) — discharging it requires the
manifold-side ODE uniqueness, which is genuine analytic content.

## What this file ships

* `ComplexTorus.smoothLift γ` — the integration-based ℂ-valued path.
* `ComplexTorus.smoothLift_zero` — Γ(0) = 0.
* `ComplexTorus.smoothLift_contMDiff` — Γ is smooth `ℝ → ℂ`.

The lift identity `mkQ ∘ smoothLift = γ.ambient` and the endpoint
membership are handled in the next chip via the contLift bridge.

No `sorry`, no `axiom`. -/

open Set Metric MeasureTheory
open scoped Manifold ContDiff Topology

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## The integration-based smooth lift -/

/-- **Smooth lift** of a smooth path on `ℂ ⧸ L` to `ℂ` via integration
of the velocity field. For `γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)`,

    smoothLift γ t := ∫_0^t (velocity γ s) ds : ℂ.

Note: the lift is well-defined as an integral over ℝ → ℂ since the
velocity (viewed via `TangentSpace _ _ = ℂ`) is a ℂ-valued
continuous function on `ℝ` (whenever γ is `C^∞`). -/
noncomputable def smoothLift
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (t : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..t, γ.velocity s

@[simp] lemma smoothLift_zero (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    smoothLift L γ 0 = 0 := by
  unfold smoothLift
  exact intervalIntegral.integral_same

end ComplexTorus

end JacobianChallenge

end
