/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.EtalePrimitivesCovering
import Mathlib.Topology.Homotopy.Lifting

set_option linter.unusedSectionVars false

/-! # Global continuous section of `proj om` on simply-connected `X` (Chip 4c)

Applies mathlib's `IsCoveringMap.existsUnique_continuousMap_lifts` to the
covering map `proj : EtalePrimitives om → X` (Chip 4b) under
`[SimplyConnectedSpace X]` + `[LocPathConnectedSpace X]` (the latter
from Chip 4a's `chartedSpaceComplex_locPathConnectedSpace`) to extract
a unique continuous section `globalSection om x₀ : C(X, EtalePrimitives om)`
with

* `(globalSection om x₀) x₀ = ⟨x₀, 0⟩`
* `proj om ∘ globalSection om x₀ = id`

The composite `globalPrimitive om x₀ := primValue ∘ globalSection om x₀ :
X → ℂ` is then the candidate continuous global primitive of `om` on
simply-connected `X`. Its smoothness (`ContMDiff`) is deferred to Chip 4d.

## What this file ships

* `continuous_primValue : Continuous (EtalePrimitives.primValue)` — the
  second projection is globally continuous. Proof: at each `e`, the basic
  sheet at `(e.point, source(e.point), e.primValue)` is an open
  neighborhood on which `primValue` agrees with the continuous function
  `localPrimitiveAtBallCenter om e.point ∘ proj + e.primValue`.
* `globalSection om x₀ : C(X, EtalePrimitives om)` — the continuous
  global section produced by `existsUnique_continuousMap_lifts`.
* `globalSection_basepoint` — `globalSection om x₀ x₀ = ⟨x₀, 0⟩`.
* `proj_globalSection` — `proj om (globalSection om x₀ x) = x` for all `x`.
* `globalPrimitive om x₀ : X → ℂ` — the candidate global primitive.
* `continuous_globalPrimitive` — global primitive is continuous.
* `globalPrimitive_basepoint` — `globalPrimitive om x₀ x₀ = 0`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set Filter

namespace JacobianChallenge

namespace EtalePrimitives

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  {om : HolomorphicOneForm X}

/-! ## `primValue` is continuous -/

/-- **The second projection `primValue : EtalePrimitives om → ℂ` is
continuous.** At each `e : EtalePrimitives om`, the basic sheet at
`(e.point, (convexBallChartAt e.point).source, e.primValue)` is an open
neighborhood on which `primValue` agrees with
`localPrimitiveAtBallCenter om e.point ∘ proj + e.primValue` (a
continuous function), so `primValue` is continuous at `e`. -/
theorem continuous_primValue (om : HolomorphicOneForm X) :
    Continuous (fun e : EtalePrimitives om => e.primValue) := by
  rw [continuous_iff_continuousAt]
  intro e
  -- Open neighborhood of `e`: the basic sheet at `(e.point, source, e.primValue)`.
  set y : X := e.point with hy_def
  set c_off : ℂ := e.primValue with hc_def
  set B : Set (EtalePrimitives om) :=
    basicSheet om y (convexBallChartAt y).source (subset_refl _) c_off
    with hB_def
  have hB_open : IsOpen B :=
    basicSheet_isOpen om y _ (convexBallChartAt y).open_source
      (subset_refl _) c_off
  have he_in_B : e ∈ B := by
    have h_eta : e = (⟨y, c_off⟩ : EtalePrimitives om) := by cases e; rfl
    rw [h_eta]
    exact self_mem_basicSheet om y _ (subset_refl _)
      (convexBallChartAt_x_mem_source y) c_off
  -- On `B`, `primValue` equals `localPrimitiveAtBallCenter om y ∘ proj + c_off`.
  have h_eqOn :
      EqOn (fun e' : EtalePrimitives om => e'.primValue)
           (fun e' : EtalePrimitives om =>
             localPrimitiveAtBallCenter om y e'.point + c_off) B := by
    intro e' he'_in_B
    have h_val := basicSheet_primValue_eq om y _ (subset_refl _) c_off he'_in_B
    have hpt : e'.point ∈ (convexBallChartAt y).source :=
      basicSheet_point_mem om y _ _ _ he'_in_B
    show e'.primValue = localPrimitiveAtBallCenter om y e'.point + c_off
    rw [h_val]
    unfold localPrimitiveAtBallCenter
    rw [chartLocalPrimitiveExtendMax_eq_chartLocalPrimitiveMax
          (convexBallChartAt y) (convexBallChartAt_mem_maximalAtlas_real y)
          (convexBallChartAt_target_convex y) y
          (convexBallChartAt_x_mem_source y) om e'.point hpt]
  -- ContinuousAt of the surrogate at `e`: F_y is ContinuousOn source(y), and
  -- e.point = y ∈ source(y); proj is globally continuous.
  have hF_y_cont_at_y :
      ContinuousAt (localPrimitiveAtBallCenter om y) y := by
    have h_contOn :
        ContinuousOn (localPrimitiveAtBallCenter om y)
                     (convexBallChartAt y).source :=
      (localPrimitiveAtBallCenter_contMDiffOn om y).continuousOn
    exact h_contOn.continuousAt
      ((convexBallChartAt y).open_source.mem_nhds
        (convexBallChartAt_x_mem_source y))
  have h_proj_at_e : ContinuousAt (fun e' : EtalePrimitives om => e'.point) e :=
    (continuous_proj om).continuousAt
  have h_proj_eq : (fun e' : EtalePrimitives om => e'.point) e = y := rfl
  have h_F_proj :
      ContinuousAt (fun e' : EtalePrimitives om =>
                      localPrimitiveAtBallCenter om y e'.point) e :=
    hF_y_cont_at_y.comp_of_eq h_proj_at_e h_proj_eq
  have h_surrogate :
      ContinuousAt
        (fun e' : EtalePrimitives om =>
          localPrimitiveAtBallCenter om y e'.point + c_off) e :=
    h_F_proj.add continuousAt_const
  -- Eventually-equal on the open nhd `B`, so `primValue` is also ContinuousAt e.
  have h_evtEq :
      (fun e' : EtalePrimitives om =>
        localPrimitiveAtBallCenter om y e'.point + c_off)
        =ᶠ[𝓝 e] (fun e' : EtalePrimitives om => e'.primValue) :=
    Filter.eventuallyEq_of_mem (hB_open.mem_nhds he_in_B) (fun e' he' => (h_eqOn he').symm)
  exact h_surrogate.congr h_evtEq

/-! ## Global continuous section (Chip 4c main) -/

variable [SimplyConnectedSpace X]

/-- **The unique continuous global section.** Applies mathlib's
`IsCoveringMap.existsUnique_continuousMap_lifts` to `proj om`
(`IsCoveringMap` from Chip 4b) with `f := id`, `a₀ := x₀`,
`e₀ := ⟨x₀, 0⟩`. -/
noncomputable def globalSection (om : HolomorphicOneForm X) (x₀ : X) :
    C(X, EtalePrimitives om) := by
  haveI : LocPathConnectedSpace X :=
    chartedSpaceComplex_locPathConnectedSpace (X := X)
  exact ((isCoveringMap_proj om).existsUnique_continuousMap_lifts
    (ContinuousMap.id X) x₀ ⟨x₀, 0⟩ rfl).choose

/-- **Defining-properties witness for `globalSection`.** -/
lemma globalSection_spec (om : HolomorphicOneForm X) (x₀ : X) :
    (globalSection om x₀) x₀ = ⟨x₀, 0⟩ ∧
      proj om ∘ (globalSection om x₀) = ContinuousMap.id X := by
  haveI : LocPathConnectedSpace X :=
    chartedSpaceComplex_locPathConnectedSpace (X := X)
  exact ((isCoveringMap_proj om).existsUnique_continuousMap_lifts
    (ContinuousMap.id X) x₀ ⟨x₀, 0⟩ rfl).choose_spec.1

/-- **Basepoint identity.** `(globalSection om x₀) x₀ = ⟨x₀, 0⟩`. -/
@[simp] lemma globalSection_basepoint (om : HolomorphicOneForm X) (x₀ : X) :
    (globalSection om x₀) x₀ = (⟨x₀, 0⟩ : EtalePrimitives om) :=
  (globalSection_spec om x₀).1

/-- **Section identity.** `proj om (globalSection om x₀ x) = x` for all `x`. -/
@[simp] lemma proj_globalSection (om : HolomorphicOneForm X) (x₀ x : X) :
    proj om ((globalSection om x₀) x) = x := by
  have h := (globalSection_spec om x₀).2
  -- h : proj om ∘ ⇑(globalSection om x₀) = ⇑(ContinuousMap.id X)
  simpa using congrFun h x

/-- **Point identity.** `(globalSection om x₀ x).point = x` for all `x`. -/
@[simp] lemma globalSection_point (om : HolomorphicOneForm X) (x₀ x : X) :
    ((globalSection om x₀) x).point = x := proj_globalSection om x₀ x

/-! ## Global primitive -/

/-- **The candidate global primitive of `om` on simply-connected `X`.**
`globalPrimitive om x₀ x := (globalSection om x₀ x).primValue`. -/
noncomputable def globalPrimitive (om : HolomorphicOneForm X) (x₀ : X) :
    X → ℂ := fun x => ((globalSection om x₀) x).primValue

/-- **Continuity of the global primitive.** -/
theorem continuous_globalPrimitive (om : HolomorphicOneForm X) (x₀ : X) :
    Continuous (globalPrimitive om x₀) :=
  (continuous_primValue om).comp (globalSection om x₀).continuous

/-- **Basepoint identity.** `globalPrimitive om x₀ x₀ = 0`. -/
@[simp] lemma globalPrimitive_basepoint (om : HolomorphicOneForm X) (x₀ : X) :
    globalPrimitive om x₀ x₀ = 0 := by
  show ((globalSection om x₀) x₀).primValue = 0
  rw [globalSection_basepoint]

end EtalePrimitives

end JacobianChallenge

end
