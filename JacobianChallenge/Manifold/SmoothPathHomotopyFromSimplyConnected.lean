/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothChain
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.Path

/-! # `SmoothPath` paths-homotopic from `SimplyConnectedSpace`

Foundation chip for the
`HolomorphicOneFormSubsingletonOfSimplyConnected` arc. On a simply
connected base space `X`, any two `SmoothPath I X` with matching
endpoints have *continuously* homotopic underlying paths. This is a
direct wrapper over mathlib's
`SimplyConnectedSpace.paths_homotopic`, repackaged for the repo's
`SmoothPath` carrier.

Subsequent chips in the arc will smooth-approximate the continuous
homotopy delivered here (via collar/Whitney smoothing in charts) and
integrate a closed 1-form against the smoothed 2-chain to obtain
path-independence of `∫_γ ω`.

## Main definitions

* `SmoothPath.toPath_homotopic_of_simplyConnected` — the wrapper
  theorem: any two smooth paths with matching endpoints have homotopic
  underlying `Path`s.

* `SmoothPath.continuousHomotopyOfSimplyConnected` — a concrete choice
  of `Path.Homotopy` between the underlying paths, picked from the
  `Nonempty` witness above. Subsequent chips access the continuous
  `I × I → X` map via the `ContinuousMap` underlying this
  `Path.Homotopy`.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

set_option diagnostics.threshold 100

namespace JacobianChallenge

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type u} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

/-- **Two smooth paths between the same endpoints in a simply-connected
space are continuously homotopic.**

This is a one-line repackaging of `SimplyConnectedSpace.paths_homotopic`
at the level of `SmoothPath`'s underlying `Path` data, handling the
endpoint coercion via `Path.cast`. -/
theorem SmoothPath.toPath_homotopic_of_simplyConnected
    [SimplyConnectedSpace X]
    (γ₁ γ₂ : SmoothPath I X)
    (h_src : γ₁.src = γ₂.src) (h_tgt : γ₁.tgt = γ₂.tgt) :
    Path.Homotopic (γ₁.toPath.cast h_src.symm h_tgt.symm) γ₂.toPath :=
  SimplyConnectedSpace.paths_homotopic _ _

/-- **A concrete continuous homotopy between two smooth paths in a
simply-connected space.** Picks a witness from the `Nonempty (Homotopy …)`
delivered by `toPath_homotopic_of_simplyConnected`. -/
def SmoothPath.continuousHomotopyOfSimplyConnected
    [SimplyConnectedSpace X]
    (γ₁ γ₂ : SmoothPath I X)
    (h_src : γ₁.src = γ₂.src) (h_tgt : γ₁.tgt = γ₂.tgt) :
    Path.Homotopy (γ₁.toPath.cast h_src.symm h_tgt.symm) γ₂.toPath :=
  (SmoothPath.toPath_homotopic_of_simplyConnected γ₁ γ₂ h_src h_tgt).some

/-- The underlying continuous map `I × I → X` of the continuous homotopy
furnished by `continuousHomotopyOfSimplyConnected`. Subsequent chips
smooth-approximate this map in charts. -/
def SmoothPath.homotopyMapOfSimplyConnected
    [SimplyConnectedSpace X]
    (γ₁ γ₂ : SmoothPath I X)
    (h_src : γ₁.src = γ₂.src) (h_tgt : γ₁.tgt = γ₂.tgt) :
    C(unitInterval × unitInterval, X) :=
  (SmoothPath.continuousHomotopyOfSimplyConnected γ₁ γ₂ h_src h_tgt).toContinuousMap

/-- At parameter `s = 0`, the homotopy delivered by
`continuousHomotopyOfSimplyConnected` recovers (the cast of) `γ₁`. -/
@[simp] lemma SmoothPath.homotopyMapOfSimplyConnected_zero
    [SimplyConnectedSpace X]
    (γ₁ γ₂ : SmoothPath I X)
    (h_src : γ₁.src = γ₂.src) (h_tgt : γ₁.tgt = γ₂.tgt)
    (t : unitInterval) :
    SmoothPath.homotopyMapOfSimplyConnected γ₁ γ₂ h_src h_tgt (0, t)
      = (γ₁.toPath.cast h_src.symm h_tgt.symm) t :=
  (SmoothPath.continuousHomotopyOfSimplyConnected γ₁ γ₂ h_src h_tgt).apply_zero t

/-- At parameter `s = 1`, the homotopy delivered by
`continuousHomotopyOfSimplyConnected` recovers `γ₂`. -/
@[simp] lemma SmoothPath.homotopyMapOfSimplyConnected_one
    [SimplyConnectedSpace X]
    (γ₁ γ₂ : SmoothPath I X)
    (h_src : γ₁.src = γ₂.src) (h_tgt : γ₁.tgt = γ₂.tgt)
    (t : unitInterval) :
    SmoothPath.homotopyMapOfSimplyConnected γ₁ γ₂ h_src h_tgt (1, t)
      = γ₂.toPath t :=
  (SmoothPath.continuousHomotopyOfSimplyConnected γ₁ γ₂ h_src h_tgt).apply_one t

end JacobianChallenge

end
