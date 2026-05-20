/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.UniformChartContainmentDepth
import JacobianChallenge.Manifold.StokesBoundaryInvarianceFromSimplex
import JacobianChallenge.Manifold.PrimitiveOnSmoothPathConnected
import JacobianChallenge.Manifold.BasedSmoothLoopsBound

set_option linter.unusedSectionVars false

/-! # Universal `LoopPeriodVanishes` from `BasedSmoothLoopsBoundHypothesis`

If every smooth based loop `γ` at `x₀` has its `singleCycle` in
`stokesBoundaries` (the `BasedSmoothLoopsBoundHypothesis`), then every
holomorphic 1-form's period vanishes along every such `γ`. This is a
**weaker** input than `SmoothlyNullBoundedHypothesis` (which requires
a *single* 2-simplex with constant boundary on two faces).

The argument is via chip D + 2-chain linearity:

1. By `BasedSmoothLoopsBoundHypothesis`, `single γ = boundary₂ d` for
   some 2-chain `d`.
2. By chip D's unconditional `HolomorphicStokesHypothesis`, both
   `realComponent om` and `imagComponent om` are closed (per-simplex
   integral of boundary vanishes).
3. By linearity (`Finsupp.induction_linear`),
   `integrate (boundary₂ d) ω = 0` for `ω ∈ {realComponent om,
   imagComponent om}`.
4. Hence `complexChainPeriod (single γ) om = 0`.

## What ships

* `loopPeriodVanishes_of_basedSmoothLoopsBoundHypothesis` — the
  universal discharge.

Direct application: `RiemannSphere` has unconditional
`basedSmoothLoopsBoundHypothesis_RS_holds`, so on `RiemannSphere`
the conclusion `LoopPeriodVanishes om x₀` is now unconditional for
every `om` (no `Subsingleton (HolomorphicOneForm)` needed —
strengthening the existing `loopPeriodVanishes_of_subsingleton` route).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Topology Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Helper.** Integral of a holomorphic 1-form's component over a
2-chain's boundary vanishes — via chip D + 2-chain linearity. -/
private theorem integrate_boundary₂_realComponent_eq_zero
    (om : HolomorphicOneForm X) (d : Smooth2Chain 𝓘(ℝ, ℂ) X) :
    SmoothChain.integrate (Smooth2Chain.boundary₂ d) (realComponent om) = 0 := by
  classical
  induction d using Finsupp.induction_linear with
  | zero =>
      show (Smooth2Chain.boundary₂ (0 : Smooth2Chain 𝓘(ℝ, ℂ) X)).integrate _ = 0
      rw [(map_zero (Smooth2Chain.boundary₂ : Smooth2Chain 𝓘(ℝ, ℂ) X →ₗ[ℤ] _)),
        SmoothChain.integrate_zero]
  | add c₁ c₂ ih₁ ih₂ =>
      have h_a : (Smooth2Chain.boundary₂ : Smooth2Chain 𝓘(ℝ, ℂ) X →ₗ[ℤ] _) (c₁ + c₂)
          = Smooth2Chain.boundary₂ c₁ + Smooth2Chain.boundary₂ c₂ := map_add _ _ _
      rw [h_a, SmoothChain.integrate_add, ih₁, ih₂, add_zero]
  | single σ k =>
      have h_single_eq :
          (Finsupp.single σ k : Smooth2Chain 𝓘(ℝ, ℂ) X)
            = k • Smooth2Chain.single σ := by
        show Finsupp.single σ k = k • Finsupp.single σ (1 : ℤ)
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      have h_smul : (Smooth2Chain.boundary₂ : Smooth2Chain 𝓘(ℝ, ℂ) X →ₗ[ℤ] _)
          (k • Smooth2Chain.single σ)
          = k • Smooth2Chain.boundary₂ (Smooth2Chain.single σ) := map_smul _ _ _
      rw [h_single_eq, h_smul, Smooth2Chain.boundary₂_single]
      -- Chip D supplies the per-simplex Stokes for realComponent.
      rw [SmoothChain.integrate_zsmul,
        (holomorphicStokesHypothesis_holds_unconditional (X := X) σ om).1,
        smul_zero]

/-- **Helper.** Imaginary-component analogue. -/
private theorem integrate_boundary₂_imagComponent_eq_zero
    (om : HolomorphicOneForm X) (d : Smooth2Chain 𝓘(ℝ, ℂ) X) :
    SmoothChain.integrate (Smooth2Chain.boundary₂ d) (imagComponent om) = 0 := by
  classical
  induction d using Finsupp.induction_linear with
  | zero =>
      show (Smooth2Chain.boundary₂ (0 : Smooth2Chain 𝓘(ℝ, ℂ) X)).integrate _ = 0
      rw [(map_zero (Smooth2Chain.boundary₂ : Smooth2Chain 𝓘(ℝ, ℂ) X →ₗ[ℤ] _)),
        SmoothChain.integrate_zero]
  | add c₁ c₂ ih₁ ih₂ =>
      have h_a : (Smooth2Chain.boundary₂ : Smooth2Chain 𝓘(ℝ, ℂ) X →ₗ[ℤ] _) (c₁ + c₂)
          = Smooth2Chain.boundary₂ c₁ + Smooth2Chain.boundary₂ c₂ := map_add _ _ _
      rw [h_a, SmoothChain.integrate_add, ih₁, ih₂, add_zero]
  | single σ k =>
      have h_single_eq :
          (Finsupp.single σ k : Smooth2Chain 𝓘(ℝ, ℂ) X)
            = k • Smooth2Chain.single σ := by
        show Finsupp.single σ k = k • Finsupp.single σ (1 : ℤ)
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      have h_smul : (Smooth2Chain.boundary₂ : Smooth2Chain 𝓘(ℝ, ℂ) X →ₗ[ℤ] _)
          (k • Smooth2Chain.single σ)
          = k • Smooth2Chain.boundary₂ (Smooth2Chain.single σ) := map_smul _ _ _
      rw [h_single_eq, h_smul, Smooth2Chain.boundary₂_single]
      rw [SmoothChain.integrate_zsmul,
        (holomorphicStokesHypothesis_holds_unconditional (X := X) σ om).2,
        smul_zero]

/-- **Universal `LoopPeriodVanishes` from `BasedSmoothLoopsBoundHypothesis`.**

For every holomorphic 1-form `om`, `LoopPeriodVanishes om x₀` holds
under the universal based-loops-bound hypothesis. By chip D's
unconditional `HolomorphicStokesHypothesis` lifted to 2-chains by
linearity. -/
theorem loopPeriodVanishes_of_basedSmoothLoopsBoundHypothesis
    {x₀ : X} (h : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀)
    (om : HolomorphicOneForm X) :
    LoopPeriodVanishes om x₀ := by
  intro γ h_src h_tgt
  -- single_smoothLoop_smoothCycle γ ∈ stokesBoundaries.
  have h_in : single_smoothLoop_smoothCycle γ (h_src.trans h_tgt.symm)
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) X := h γ h_src h_tgt
  -- ∃ d, boundary₂Cycle d = single_smoothLoop_smoothCycle γ ...
  obtain ⟨d, hd⟩ := (mem_stokesBoundaries_iff (I := 𝓘(ℝ, ℂ)) (X := X)).mp h_in
  -- single γ = boundary₂ d (as SmoothChain).
  have h_chain_eq : SmoothChain.single γ = Smooth2Chain.boundary₂ d := by
    have h_coe : ((Smooth2Chain.boundary₂Cycle d :
        JacobianChallenge.SmoothCycle 𝓘(ℝ, ℂ) X) : SmoothChain 𝓘(ℝ, ℂ) X)
        = ((single_smoothLoop_smoothCycle γ (h_src.trans h_tgt.symm) :
        JacobianChallenge.SmoothCycle 𝓘(ℝ, ℂ) X) : SmoothChain 𝓘(ℝ, ℂ) X) := by
      rw [hd]
    rw [Smooth2Chain.boundary₂Cycle_coe,
        single_smoothLoop_smoothCycle_coe] at h_coe
    exact h_coe.symm
  -- complexChainPeriod (single γ) om = complexChainPeriod (boundary₂ d) om = 0.
  unfold complexChainPeriod
  rw [h_chain_eq,
    integrate_boundary₂_realComponent_eq_zero om d,
    integrate_boundary₂_imagComponent_eq_zero om d]
  push_cast
  ring

end JacobianChallenge

end
