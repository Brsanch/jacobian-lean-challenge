/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PrimitiveOnSmoothPathConnected
import JacobianChallenge.Topology.SubsingletonFromPrimitiveExistence

set_option linter.unusedSectionVars false

/-! # `Subsingleton (HolomorphicOneForm X)` from path-integral primitives

End-to-end conditional reduction for item 14 reverse leg:

```
SmoothPathConnected X
+ ∀ om, LoopPeriodVanishes om x₀
+ pathPrimitiveSmoothness (smoothness of x ↦ pathPrimitive om x)
+ pathPrimitiveFTC (mfderiv pathPrimitive = om.eval pointwise)
⇒ Subsingleton (HolomorphicOneForm X)
```

The first input is structural (no analytic content). The remaining three
are the named classical inputs corresponding to the analytic content
of Stokes + parameter-dependent integral smoothness + FTC for line
integrals.

Composing with the existing `subsingleton_of_primitiveExistence`
delivers the headline.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology ContDiff
open Module

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Smoothness of the path-primitive** (named hypothesis): for every
holomorphic 1-form `om`, the function `x ↦ pathPrimitive h_conn x₀ om x`
is `ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω`. Classical content: parameter-
dependent integral smoothness. -/
def PathPrimitiveSmoothness
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X) (x₀ : X) : Prop :=
  ∀ om : HolomorphicOneForm X,
    ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (pathPrimitive h_conn x₀ om)

/-- **FTC for the path-primitive** (named hypothesis): for every `om` and
every `x`, `om.eval x = mfderiv (pathPrimitive h_conn x₀ om) x`. Classical
content: fundamental theorem of calculus for line integrals. -/
def PathPrimitiveFTC
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X) (x₀ : X) : Prop :=
  ∀ om : HolomorphicOneForm X, ∀ x : X,
    om.eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (pathPrimitive h_conn x₀ om) x

/-- **All loops vanish** (named hypothesis): the `LoopPeriodVanishes`
condition holds for every `om`. -/
def AllLoopsVanish (x₀ : X) : Prop :=
  ∀ om : HolomorphicOneForm X, LoopPeriodVanishes om x₀

/-- **Bridge from path-primitive hypotheses to `Subsingleton`.**
Composes `subsingleton_of_primitiveExistence` with the path-primitive
construction. -/
theorem subsingleton_of_pathPrimitive_hypotheses
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X) (x₀ : X)
    (_h_loop : AllLoopsVanish (X := X) x₀)
    (h_smooth : PathPrimitiveSmoothness h_conn x₀)
    (h_ftc : PathPrimitiveFTC h_conn x₀) :
    Subsingleton (HolomorphicOneForm X) := by
  refine subsingleton_of_primitiveExistence (fun om => ?_)
  exact ⟨pathPrimitive h_conn x₀ om, h_smooth om, fun x => h_ftc om x⟩

/-- **Conditional discharge of `HolomorphicOneFormSubsingletonOfSimplyConnected`.**
From simple-connectedness + the path-primitive analytic hypotheses, get
the named predicate discharged. -/
theorem holomorphicOneFormSubsingletonOfSimplyConnected_of_pathPrimitive
    (x₀ : X) (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (h_loop : SimplyConnectedSpace X → AllLoopsVanish (X := X) x₀)
    (h_smooth : SimplyConnectedSpace X → PathPrimitiveSmoothness h_conn x₀)
    (h_ftc : SimplyConnectedSpace X → PathPrimitiveFTC h_conn x₀) :
    HolomorphicOneFormSubsingletonOfSimplyConnected X := fun h_sc =>
  subsingleton_of_pathPrimitive_hypotheses h_conn x₀
    (h_loop h_sc) (h_smooth h_sc) (h_ftc h_sc)

end JacobianChallenge

end
