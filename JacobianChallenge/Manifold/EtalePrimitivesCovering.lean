/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.EtalePrimitivesCoveringInfra
import Mathlib.Topology.Covering.Basic

set_option linter.unusedSectionVars false

/-! # The étale projection `proj : EtalePrimitives om → X` is a covering map (Chip 4b)

Builds the per-`x` trivializing homeomorphism

```
(proj om ⁻¹' (convexBallChartAt x).source) ≃ₜ (convexBallChartAt x).source × (proj om ⁻¹' {x})
```

and concludes `IsCoveringMap (proj om)`.

## Construction

For each `x : X`, set `U := (convexBallChartAt x).source` and
`F_x := localPrimitiveAtBallCenter om x`. The homeomorphism `H`:

* `H.toFun e := (⟨e.val.point, _⟩, ⟨⟨x, e.val.primValue − F_x e.val.point⟩, _⟩)`.

  - First component: `e.val.point ∈ U` since `e ∈ proj⁻¹ U`.
  - Second component lands in the fiber `proj om ⁻¹' {x}` (its `point` is
    `x` by construction).

* `H.invFun (⟨x', hx'⟩, ⟨e₀, he₀⟩) := chartSection om x e₀.primValue x' hx'`
  wrapped to land in `proj⁻¹ U` (since `x' ∈ U`).

Round trips:
- `inv ∘ fwd`: `e ↦ chartSection om x (e.primValue − F_x e.point) e.point
   = ⟨e.point, F_x e.point + (e.primValue − F_x e.point)⟩ = ⟨e.point, e.primValue⟩ = e`.
- `fwd ∘ inv`: `(⟨x', _⟩, ⟨e₀, _⟩) ↦ (⟨x', _⟩, ⟨⟨x, e₀.primValue⟩, _⟩) = (⟨x', _⟩, ⟨e₀, _⟩)`
  (the last equality is η on `e₀`, using `e₀.point = x`).

Continuity:

* `H.toFun` continuous: first component = `proj` composed (continuous);
  second component is a map into a *discrete* space (Chip 4a) — open
  preimage of `⟨⟨x, c₀⟩, _⟩` is the basic sheet at `(x, U, c₀)`.

* `H.invFun` continuous: target's second factor is discrete, so by
  `continuous_prod_of_discrete_right` it suffices that for each fixed
  `e₀ ∈ Fiber`, the slice `x' ↦ chartSection om x e₀.primValue x'` is
  continuous on `U` — given directly by `continuousOn_chartSectionTotal`
  (Chip 3).

## What this file ships

* `isOpen_proj_preimage_chartBallSource` — open preimage of `U`.
* `etaleCoveringHomeoFwd / etaleCoveringHomeoInv` — the maps.
* `etaleCoveringEquiv x` — underlying `Equiv`.
* `etaleCoveringHomeo x` — the `Homeomorph`.
* `isEvenlyCovered_proj` — for each `x`, `IsEvenlyCovered (proj om) x …`.
* `isCoveringMap_proj : IsCoveringMap (proj om)` — main theorem.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

namespace EtalePrimitives

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  {om : HolomorphicOneForm X}

/-! ## Openness of `proj om ⁻¹' (convexBallChartAt x).source` -/

/-- **Preimage of the chart-ball-source is open.** Direct consequence
of `Continuous (proj om)` from Chip 1. -/
lemma isOpen_proj_preimage_chartBallSource
    (om : HolomorphicOneForm X) (x : X) :
    IsOpen (proj om ⁻¹' (convexBallChartAt x).source) :=
  (convexBallChartAt x).open_source.preimage (continuous_proj om)

/-! ## Forward and inverse maps -/

/-- **Forward map of the trivialization at `x`.**
`e ↦ (⟨e.point, _⟩, ⟨⟨x, e.primValue − F_x(e.point)⟩, _⟩)`. -/
def etaleCoveringHomeoFwd (om : HolomorphicOneForm X) (x : X)
    (e : (proj om ⁻¹' (convexBallChartAt x).source :
            Set (EtalePrimitives om))) :
    (convexBallChartAt x).source × (proj om ⁻¹' {x} :
        Set (EtalePrimitives om)) :=
  (⟨e.val.point, e.property⟩,
    ⟨⟨x, e.val.primValue - localPrimitiveAtBallCenter om x e.val.point⟩,
      by show (⟨x, _⟩ : EtalePrimitives om).point = x; rfl⟩)

@[simp] lemma etaleCoveringHomeoFwd_fst_val
    (om : HolomorphicOneForm X) (x : X)
    (e : (proj om ⁻¹' (convexBallChartAt x).source :
            Set (EtalePrimitives om))) :
    (etaleCoveringHomeoFwd om x e).1.val = e.val.point := rfl

@[simp] lemma etaleCoveringHomeoFwd_snd_val
    (om : HolomorphicOneForm X) (x : X)
    (e : (proj om ⁻¹' (convexBallChartAt x).source :
            Set (EtalePrimitives om))) :
    (etaleCoveringHomeoFwd om x e).2.val
      = ⟨x, e.val.primValue
              - localPrimitiveAtBallCenter om x e.val.point⟩ := rfl

/-- **Inverse map of the trivialization at `x`.**
`(⟨x', _⟩, ⟨e₀, _⟩) ↦ ⟨chartSection om x e₀.primValue x' _, _⟩`. -/
def etaleCoveringHomeoInv (om : HolomorphicOneForm X) (x : X)
    (p : (convexBallChartAt x).source × (proj om ⁻¹' {x} :
            Set (EtalePrimitives om))) :
    (proj om ⁻¹' (convexBallChartAt x).source : Set (EtalePrimitives om)) :=
  ⟨chartSection om x p.2.val.primValue p.1.val p.1.property,
    by
      show (chartSection om x p.2.val.primValue p.1.val p.1.property).point
        ∈ (convexBallChartAt x).source
      rw [chartSection_point]; exact p.1.property⟩

@[simp] lemma etaleCoveringHomeoInv_val_point
    (om : HolomorphicOneForm X) (x : X)
    (p : (convexBallChartAt x).source × (proj om ⁻¹' {x} :
            Set (EtalePrimitives om))) :
    (etaleCoveringHomeoInv om x p).val.point = p.1.val := by
  show (chartSection om x p.2.val.primValue p.1.val p.1.property).point = p.1.val
  rfl

@[simp] lemma etaleCoveringHomeoInv_val_primValue
    (om : HolomorphicOneForm X) (x : X)
    (p : (convexBallChartAt x).source × (proj om ⁻¹' {x} :
            Set (EtalePrimitives om))) :
    (etaleCoveringHomeoInv om x p).val.primValue
      = localPrimitiveAtBallCenter om x p.1.val + p.2.val.primValue := by
  show (chartSection om x p.2.val.primValue p.1.val p.1.property).primValue
    = localPrimitiveAtBallCenter om x p.1.val + p.2.val.primValue
  exact chartSection_primValue_eq_localPrimitiveAtBallCenter_add
    om x p.2.val.primValue p.1.val p.1.property

/-! ## Round-trip identities -/

/-- **Inverse-then-forward.** -/
lemma etaleCoveringHomeoFwd_invFwd
    (om : HolomorphicOneForm X) (x : X)
    (p : (convexBallChartAt x).source × (proj om ⁻¹' {x} :
            Set (EtalePrimitives om))) :
    etaleCoveringHomeoFwd om x (etaleCoveringHomeoInv om x p) = p := by
  -- Decompose the pair.
  obtain ⟨⟨x', hx'⟩, ⟨e₀, he₀⟩⟩ := p
  -- e₀.point = x from fiber membership.
  have he₀_point : e₀.point = x := he₀
  -- Show the two pair components are equal.
  apply Prod.ext
  · -- First component.
    apply Subtype.ext
    show (etaleCoveringHomeoFwd om x (etaleCoveringHomeoInv om x _)).1.val = x'
    rw [etaleCoveringHomeoFwd_fst_val, etaleCoveringHomeoInv_val_point]
  · -- Second component.
    apply Subtype.ext
    show (etaleCoveringHomeoFwd om x (etaleCoveringHomeoInv om x _)).2.val = e₀
    rw [etaleCoveringHomeoFwd_snd_val, etaleCoveringHomeoInv_val_point,
        etaleCoveringHomeoInv_val_primValue]
    -- Goal: ⟨x, (F_x x' + e₀.primValue) - F_x x'⟩ = e₀.
    apply EtalePrimitives.ext
    · exact he₀_point.symm
    · show (localPrimitiveAtBallCenter om x x' + e₀.primValue)
            - localPrimitiveAtBallCenter om x x' = e₀.primValue
      ring

/-- **Forward-then-inverse.** -/
lemma etaleCoveringHomeoFwd_fwdInv
    (om : HolomorphicOneForm X) (x : X)
    (e : (proj om ⁻¹' (convexBallChartAt x).source :
            Set (EtalePrimitives om))) :
    etaleCoveringHomeoInv om x (etaleCoveringHomeoFwd om x e) = e := by
  apply Subtype.ext
  -- Show .val equality in EtalePrimitives.
  show (etaleCoveringHomeoInv om x (etaleCoveringHomeoFwd om x e)).val = e.val
  apply EtalePrimitives.ext
  · -- point side.
    rw [etaleCoveringHomeoInv_val_point]; rfl
  · -- primValue side.
    rw [etaleCoveringHomeoInv_val_primValue]
    -- Goal: F_x(e.point) + (e.primValue - F_x(e.point)) = e.primValue
    show localPrimitiveAtBallCenter om x e.val.point
        + ((etaleCoveringHomeoFwd om x e).2.val.primValue)
      = e.val.primValue
    rw [etaleCoveringHomeoFwd_snd_val]
    show localPrimitiveAtBallCenter om x e.val.point
        + (e.val.primValue - localPrimitiveAtBallCenter om x e.val.point)
      = e.val.primValue
    ring

/-! ## Underlying Equiv -/

/-- **The trivialization `Equiv` at `x`.** -/
def etaleCoveringEquiv (om : HolomorphicOneForm X) (x : X) :
    (proj om ⁻¹' (convexBallChartAt x).source : Set (EtalePrimitives om))
      ≃ (convexBallChartAt x).source × (proj om ⁻¹' {x} :
            Set (EtalePrimitives om)) where
  toFun := etaleCoveringHomeoFwd om x
  invFun := etaleCoveringHomeoInv om x
  left_inv := etaleCoveringHomeoFwd_fwdInv om x
  right_inv := etaleCoveringHomeoFwd_invFwd om x

/-! ## Continuity of the forward map -/

/-- **Forward map second component preimage.** For each `e₀ ∈ proj⁻¹{x}`,
the preimage under the forward map's second projection is the basic
sheet at `(x, U, e₀.primValue)` intersected with the source subspace. -/
lemma etaleCoveringHomeoFwd_snd_preimage
    (om : HolomorphicOneForm X) (x : X)
    (e₀_sub : (proj om ⁻¹' {x} : Set (EtalePrimitives om))) :
    (fun e : (proj om ⁻¹' (convexBallChartAt x).source :
                Set (EtalePrimitives om)) =>
        (etaleCoveringHomeoFwd om x e).2) ⁻¹' {e₀_sub}
      = Subtype.val ⁻¹'
          basicSheet om x (convexBallChartAt x).source (subset_refl _)
            e₀_sub.val.primValue := by
  have he₀_point : e₀_sub.val.point = x := e₀_sub.property
  ext ⟨e, he⟩
  -- he : e ∈ proj⁻¹ U
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h_eq
    -- h_eq : (etaleCoveringHomeoFwd om x ⟨e, he⟩).2 = e₀_sub
    -- Extract val-level equality, then primValue equality.
    have h_val_eq := congrArg Subtype.val h_eq
    -- h_val_eq : ⟨x, e.primValue - F_x e.point⟩ = e₀_sub.val
    have h_primValue :
        e.primValue - localPrimitiveAtBallCenter om x e.point
          = e₀_sub.val.primValue :=
      congrArg EtalePrimitives.primValue h_val_eq
    -- Show e ∈ basicSheet om x U _ e₀.primValue: witness x' := e.point.
    refine ⟨e.point, he, ?_⟩
    apply EtalePrimitives.ext
    · rfl
    · rw [chartSection_primValue_eq_localPrimitiveAtBallCenter_add]
      linear_combination h_primValue
  · intro h_sheet
    -- h_sheet : e ∈ basicSheet om x U _ e₀.primValue
    -- Compute F_x(e.point) + e₀.primValue = e.primValue from basicSheet.
    have h_primValue := basicSheet_primValue_eq om x _ _ _ h_sheet
    -- h_primValue : e.primValue = F^Max_x(e.point) + e₀.primValue
    -- Goal: (etaleCoveringHomeoFwd om x ⟨e, he⟩).2 = e₀_sub
    apply Subtype.ext
    show (etaleCoveringHomeoFwd om x ⟨e, he⟩).2.val = e₀_sub.val
    rw [etaleCoveringHomeoFwd_snd_val]
    apply EtalePrimitives.ext
    · exact he₀_point.symm
    · -- e.primValue - F_x(e.point) = e₀_sub.val.primValue
      -- Bridge basicSheet's chartLocalPrimitiveMax to localPrimitiveAtBallCenter.
      have hpt : e.point ∈ (convexBallChartAt x).source := he
      have h_bridge :
          chartLocalPrimitiveMax (convexBallChartAt x)
              (convexBallChartAt_mem_maximalAtlas_real x)
              (convexBallChartAt_target_convex x) x
              (convexBallChartAt_x_mem_source x) om e.point hpt
            = localPrimitiveAtBallCenter om x e.point := by
        unfold localPrimitiveAtBallCenter
        rw [chartLocalPrimitiveExtendMax_eq_chartLocalPrimitiveMax]
      rw [h_bridge] at h_primValue
      linear_combination h_primValue

/-- **Forward map is continuous.** First component via `proj`;
second component via discrete-target characterisation. -/
lemma continuous_etaleCoveringHomeoFwd
    (om : HolomorphicOneForm X) (x : X) :
    Continuous (etaleCoveringHomeoFwd om x) := by
  apply Continuous.prodMk
  · -- First component: e ↦ ⟨e.val.point, e.property⟩ as a map to the
    -- subtype `(convexBallChartAt x).source`.
    apply Continuous.subtype_mk
    -- Goal: Continuous (fun e => e.val.point)
    exact (continuous_proj om).comp continuous_subtype_val
  · -- Second component: map into discrete fiber.
    haveI := discreteTopology_proj_preimage_singleton om x
    rw [continuous_discrete_rng]
    intro e₀_sub
    -- Goal: openness of preimage of `{e₀_sub}` (Lean has β-reduced the
    -- forward map). The preimage equals `Subtype.val ⁻¹' basicSheet`.
    -- Prove the set equality inline, then apply `basicSheet_isOpen` +
    -- `Continuous.preimage`.
    have h_preimage_eq :
        (fun e : (proj om ⁻¹' (convexBallChartAt x).source :
                    Set (EtalePrimitives om)) =>
          (etaleCoveringHomeoFwd om x e).2) ⁻¹' {e₀_sub}
          = Subtype.val ⁻¹'
              basicSheet om x (convexBallChartAt x).source (subset_refl _)
                e₀_sub.val.primValue :=
      etaleCoveringHomeoFwd_snd_preimage om x e₀_sub
    -- Convert the goal's β-reduced LHS to the helper-lemma form.
    have h_open : IsOpen
        ((fun e : (proj om ⁻¹' (convexBallChartAt x).source :
                    Set (EtalePrimitives om)) =>
            (etaleCoveringHomeoFwd om x e).2) ⁻¹' {e₀_sub}) := by
      rw [h_preimage_eq]
      exact (basicSheet_isOpen om x _ (convexBallChartAt x).open_source
        (subset_refl _) e₀_sub.val.primValue).preimage continuous_subtype_val
    exact h_open

/-! ## Continuity of the inverse map -/

/-- **Inverse map is continuous.** The source's second factor is
discrete (Chip 4a), so by `continuous_prod_of_discrete_right` it
suffices that for each fixed `e₀ : Fiber`, the slice
`x' ↦ chartSection om x e₀.primValue x' …` is continuous on `U`. -/
lemma continuous_etaleCoveringHomeoInv
    (om : HolomorphicOneForm X) (x : X) :
    Continuous (etaleCoveringHomeoInv om x) := by
  haveI := discreteTopology_proj_preimage_singleton om x
  rw [continuous_prod_of_discrete_right]
  intro e₀_sub
  -- For fixed `e₀_sub : Fiber`, prove continuity of
  -- `x_1 ↦ etaleCoveringHomeoInv om x (x_1, e₀_sub)` as a map into the
  -- subtype `(proj om ⁻¹' (convexBallChartAt x).source)`.
  apply Continuous.subtype_mk
  -- Goal: `Continuous (fun x_1 : U => chartSection om x e₀_sub.val.primValue x_1.val x_1.property)`.
  -- Bridge `chartSection` (partial) ↔ `chartSectionTotal` (total) on source,
  -- then use the cascade's `continuousOn_chartSectionTotal` from Chip 3.
  refine Continuous.congr
    ((continuousOn_chartSectionTotal om x e₀_sub.val.primValue).comp_continuous
      (continuous_subtype_val : Continuous
        (Subtype.val : (convexBallChartAt x).source → X))
      (fun x_1 => x_1.property)) ?_
  intro x_1
  -- Goal: chartSectionTotal om x e₀_sub.val.primValue x_1.val
  --       = chartSection om x e₀_sub.val.primValue x_1.val x_1.property
  exact chartSectionTotal_apply_of_mem
    om x e₀_sub.val.primValue x_1.val x_1.property

/-! ## The trivialization homeomorphism -/

/-- **The trivialization homeomorphism at `x`.** -/
def etaleCoveringHomeo (om : HolomorphicOneForm X) (x : X) :
    (proj om ⁻¹' (convexBallChartAt x).source : Set (EtalePrimitives om))
      ≃ₜ (convexBallChartAt x).source × (proj om ⁻¹' {x} :
            Set (EtalePrimitives om)) where
  toEquiv := etaleCoveringEquiv om x
  continuous_toFun := continuous_etaleCoveringHomeoFwd om x
  continuous_invFun := continuous_etaleCoveringHomeoInv om x

/-! ## `IsEvenlyCovered` and `IsCoveringMap` -/

/-- **Each `x : X` is evenly covered by `proj om`** with fiber
`proj om ⁻¹' {x}`. -/
theorem isEvenlyCovered_proj
    (om : HolomorphicOneForm X) (x : X) :
    IsEvenlyCovered (proj om) x (proj om ⁻¹' {x} :
        Set (EtalePrimitives om)) := by
  refine ⟨discreteTopology_proj_preimage_singleton om x,
    (convexBallChartAt x).source,
    convexBallChartAt_x_mem_source x,
    (convexBallChartAt x).open_source,
    isOpen_proj_preimage_chartBallSource om x,
    etaleCoveringHomeo om x, ?_⟩
  -- H(e).1.val = proj e.
  intro e
  show (etaleCoveringHomeo om x e).1.val = proj om e.val
  exact rfl

/-- **The étale projection is a covering map.** Main theorem. -/
theorem isCoveringMap_proj (om : HolomorphicOneForm X) :
    IsCoveringMap (proj om) := isEvenlyCovered_proj om

end EtalePrimitives

end JacobianChallenge

end
