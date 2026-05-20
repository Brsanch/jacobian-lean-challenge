/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.UniformChartContainmentDepth
import JacobianChallenge.Manifold.PrimitiveOnSmoothPathConnected

set_option linter.unusedSectionVars false

/-! # `LoopPeriodVanishes` from `SmoothNullBounding` via chip D

If a smooth loop `γ` at `x₀` is **smoothly null-bounded** — i.e.,
there exists a smooth 2-simplex `σ` with `face0 σ = face1 σ =
SmoothPath.const x₀` and `face2 σ = γ` — then by chip D's unconditional
`HolomorphicStokesHypothesis_holds_unconditional`, every holomorphic
1-form `om` has zero period along `γ`.

This factors the open content of `LoopPeriodVanishes` cleanly: the
substantive remaining piece is the **smooth-null-bounding property**
(equivalently, smooth Poincaré: every smooth based loop on a
simply-connected smooth manifold smoothly bounds a 2-simplex with
constant boundary on two faces). On a complex 1-manifold, with chip
D in hand, the Stokes step is automatic.

## What ships

* `SmoothNullBounding γ x₀` — the named Prop.
* `loopPeriodVanishes_of_smoothNullBounding` — given the null-bounding
  witness, every holomorphic 1-form's period along `γ` is `0`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Topology Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`SmoothNullBounding γ x₀`** — the smooth loop `γ` based at `x₀`
is the `face2` of some smooth 2-simplex whose other two faces are
constant at `x₀`. Equivalently, `γ` smoothly bounds a 2-simplex with
constant boundary on two faces. -/
def SmoothNullBounding (γ : SmoothPath 𝓘(ℝ, ℂ) X) (x₀ : X) : Prop :=
  ∃ σ : Smooth2Simplex 𝓘(ℝ, ℂ) X,
    Smooth2Simplex.face0 σ = SmoothPath.const 𝓘(ℝ, ℂ) X x₀ ∧
    Smooth2Simplex.face1 σ = SmoothPath.const 𝓘(ℝ, ℂ) X x₀ ∧
    Smooth2Simplex.face2 σ = γ

/-- **`LoopPeriodVanishes om x₀` at `γ` from `SmoothNullBounding γ x₀`.**

By chip D's `HolomorphicStokesHypothesis_holds_unconditional`,
`integrate (boundary σ) (realComponent om) = 0` and the same for
`imagComponent`. The boundary of `σ` is
`single (face0 σ) - single (face1 σ) + single (face2 σ)`; with the
null-bounding hypothesis, this simplifies to
`SmoothChain.single γ + 0 = SmoothChain.single γ` (the two constant
faces cancel since they're identical). Hence `complexChainPeriod
(single γ) om = 0`. -/
theorem loopPeriodVanishes_of_smoothNullBounding
    {γ : SmoothPath 𝓘(ℝ, ℂ) X} {x₀ : X}
    (_h_src : γ.src = x₀) (_h_tgt : γ.tgt = x₀)
    (h_nb : SmoothNullBounding γ x₀)
    (om : HolomorphicOneForm X) :
    complexChainPeriod (SmoothChain.single γ) om = 0 := by
  obtain ⟨σ, h_face0, h_face1, h_face2⟩ := h_nb
  -- Stokes via chip D's unconditional theorem.
  have h_stokes := holomorphicStokesHypothesis_holds_unconditional (X := X) σ om
  -- complexChainPeriod (boundary σ) om = 0.
  have h_boundary_period :
      complexChainPeriod (Smooth2Simplex.boundary σ) om = 0 := by
    unfold complexChainPeriod
    rw [h_stokes.1, h_stokes.2]
    push_cast
    ring
  -- boundary σ = single γ (since face0 σ = face1 σ).
  have h_boundary_eq : Smooth2Simplex.boundary σ = SmoothChain.single γ := by
    unfold Smooth2Simplex.boundary
    rw [h_face0, h_face1, h_face2]
    -- single c - single c + single γ = 0 + single γ = single γ.
    rw [sub_self, zero_add]
  rw [h_boundary_eq] at h_boundary_period
  exact h_boundary_period

end JacobianChallenge

end
