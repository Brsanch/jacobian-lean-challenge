/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathConnected
import JacobianChallenge.Manifold.AbelJacobiPath
import JacobianChallenge.Manifold.SmoothPathConcat
import JacobianChallenge.Manifold.SmoothPathReverse
import JacobianChallenge.Manifold.ComplexChainPeriodFormLinear

set_option linter.unusedSectionVars false

/-! # Primitive of a holomorphic 1-form via path integrals

Toward item 14 reverse leg. For `X` smooth-path-connected (compact complex
1-manifold), pick a basepoint `x₀` and define

  `pathPrimitive ω x := complexChainPeriod (single γ_x) ω`

where `γ_x : SmoothPath` is a Classical.choice path from `x₀` to `x` (via
`SmoothPathConnected.exists_smoothPath`).

`pathPrimitive` depends on the path choice in general. It is
**well-defined modulo a path-independence hypothesis** which is the
classical content of "every smooth loop based at `x₀` has zero period
integral" — equivalent on simply-connected `X` to the Stokes / homotopy-
invariance argument for closed 1-forms.

This file:

* defines `pathPrimitive`;
* surfaces the named hypothesis `LoopPeriodVanishes ω x₀` (every loop
  based at `x₀` has zero period);
* shows that under `LoopPeriodVanishes`, `pathPrimitive` is independent
  of the choice of path.

The named hypothesis is the **single classical open input** for the
primitive-existence step of item 14's reverse leg.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology ContDiff
open Module

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **Loop-period-vanishes hypothesis**: every smooth loop based at `x₀`
has zero complex period against `ω`.

Classical content: on a simply-connected manifold, every smooth loop is
null-homotopic; Stokes + closedness (= holomorphy) of `ω` gives the
vanishing. -/
def LoopPeriodVanishes (om : HolomorphicOneForm X) (x₀ : X) : Prop :=
  ∀ γ : SmoothPath 𝓘(ℝ, ℂ) X, γ.src = x₀ → γ.tgt = x₀ →
    complexChainPeriod (SmoothChain.single γ) om = 0

/-- **Path-primitive via classical choice**: pick a smooth path from the
basepoint to each point and integrate `ω` along it. The choice depends on
the path-picker; well-definedness is conditional on `LoopPeriodVanishes`. -/
noncomputable def pathPrimitive
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X) (x : X) : ℂ :=
  complexChainPeriod
    (SmoothChain.single (h_conn x₀ x).choose) om

/-- The path-picker's source is `x₀`. -/
private lemma pathPrimitive_path_src (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ x : X) : (h_conn x₀ x).choose.src = x₀ :=
  (h_conn x₀ x).choose_spec.1

/-- The path-picker's target is `x`. -/
private lemma pathPrimitive_path_tgt (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ x : X) : (h_conn x₀ x).choose.tgt = x :=
  (h_conn x₀ x).choose_spec.2

/-- **Well-definedness**: under `LoopPeriodVanishes`, any two smooth paths
from `x₀` to `x` give the same period integral. The path-primitive at
`x` therefore equals the integral along *any* smooth path from `x₀`
to `x`. -/
theorem pathPrimitive_eq_integral_of_loopPeriodVanishes
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X) (x₀ : X)
    (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (x : X) (γ : SmoothPath 𝓘(ℝ, ℂ) X)
    (h_src : γ.src = x₀) (h_tgt : γ.tgt = x) :
    pathPrimitive h_conn x₀ om x = complexChainPeriod (SmoothChain.single γ) om := by
  -- Let γ₀ := the Classical.choice path; γ := the given path.
  -- Build the loop `γ ++ γ₀.reverse` based at x₀ (γ ends at x, γ₀.reverse
  -- starts at x and ends at x₀).
  -- Period of the loop = 0 by LoopPeriodVanishes, hence period(γ) =
  -- period(γ₀).
  set γ₀ : SmoothPath 𝓘(ℝ, ℂ) X := (h_conn x₀ x).choose with hγ₀_def
  have hγ₀_src : γ₀.src = x₀ := pathPrimitive_path_src h_conn x₀ x
  have hγ₀_tgt : γ₀.tgt = x := pathPrimitive_path_tgt h_conn x₀ x
  -- Concatenation `γ ++ γ₀.reverse`: γ goes x₀ → x, γ₀.reverse goes x → x₀.
  have h_concat_endpoint : γ.tgt = γ₀.reverse.src := by
    rw [h_tgt, SmoothPath.reverse_src, hγ₀_tgt]
  set loop : SmoothPath 𝓘(ℝ, ℂ) X :=
    SmoothPath.concat γ γ₀.reverse h_concat_endpoint with hloop_def
  -- Loop is based at x₀.
  have hloop_src : loop.src = x₀ := by
    rw [hloop_def, SmoothPath.concat_src, h_src]
  have hloop_tgt : loop.tgt = x₀ := by
    rw [hloop_def, SmoothPath.concat_tgt, SmoothPath.reverse_tgt, hγ₀_src]
  -- Period of loop = 0.
  have h_loop_zero : complexChainPeriod (SmoothChain.single loop) om = 0 :=
    h_loop loop hloop_src hloop_tgt
  -- Period of concat = period(γ) + period(γ₀.reverse).
  have h_concat_period :
      complexChainPeriod (SmoothChain.single loop) om
        = complexChainPeriod (SmoothChain.single γ) om
          + complexChainPeriod (SmoothChain.single γ₀.reverse) om := by
    rw [hloop_def]
    exact complexChainPeriod_single_concat γ γ₀.reverse h_concat_endpoint om
  -- Period of reverse(γ₀) = -period(γ₀).
  have h_reverse_period :
      complexChainPeriod (SmoothChain.single γ₀.reverse) om
        = -complexChainPeriod (SmoothChain.single γ₀) om :=
    complexChainPeriod_single_reverse γ₀ om
  -- Combine: 0 = period(γ) + (-period(γ₀)), so period(γ) = period(γ₀).
  rw [h_concat_period, h_reverse_period] at h_loop_zero
  -- h_loop_zero : complexChainPeriod (single γ) om + -complexChainPeriod (single γ₀) om = 0
  have heq : complexChainPeriod (SmoothChain.single γ) om
      = complexChainPeriod (SmoothChain.single γ₀) om := by
    linear_combination h_loop_zero
  unfold pathPrimitive
  rw [← hγ₀_def, heq]

end JacobianChallenge

end
