/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.BoundaryPeriodFromDepthN
import JacobianChallenge.Manifold.ChartContainedSmooth2SimplexFromFaces

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Bridge: `UniformChartContainmentDepth_named X →
`SubdivisionTelescopingTo2Simplex_named X`

Given the named uniform-depth hypothesis (existence of an iterated
midpoint subdivision depth at which every sub-simplex is chart-contained
on `Δ²`), provide the list of `ChartContainedSmooth2Simplex X`es
required by `SubdivisionTelescopingTo2Simplex_named X`.

This wires the new `MidpointSubdivisionTelescoping` UNCONDITIONAL +
iterated subdivision arc into the existing
`GenericGenusPeriodLatticeInputs.ofFourNamedAtoms` constructor, allowing
the third atomic input to be discharged from
`UniformChartContainmentDepth_named` instead of
`SubdivisionTelescopingTo2Simplex_named` directly.

## Strategy

1. Convert each `ChartContainmentWitness T` to a `ChartContainedSmooth2Simplex T`
   via `ChartContainedSmooth2Simplex.ofChartContainedFaces`, using
   the `face_iParam ⊆ standardSimplex2` lemmas to derive per-face
   conditions from the Δ²-level conditions.

2. Lift the per-element conversion to a list-level conversion via
   `List.attach.map`.

3. The period sum identity follows from the unconditional iterated
   midpoint subdivision identity (`complexChainPeriod_boundary_eq_iteratedMidpointList_sum`).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Convert a `ChartContainmentWitness T` to a `ChartContainedSmooth2Simplex X`.**

Given Δ²-level chart-containment of `T`, derive the per-face conditions
required by `ChartContainedSmooth2Simplex.ofChartContainedFaces` via the
`face_iParam ⊆ standardSimplex2` lemmas. -/
noncomputable def ChartContainmentWitness.toChartContained
    {T : Smooth2Simplex 𝓘(ℝ, ℂ) X} (w : ChartContainmentWitness T) :
    ChartContainedSmooth2Simplex X :=
  ChartContainedSmooth2Simplex.ofChartContainedFaces
    T w.basePoint w.ballCentre w.ballRadius w.radius_pos w.ball_sub_target
    (fun s hs =>
      w.image_in_source (Smooth2Simplex.face0Param s)
        (face0Param_mem_standardSimplex2 hs))
    (fun s hs =>
      w.image_in_source (Smooth2Simplex.face1Param s)
        (face1Param_mem_standardSimplex2 hs))
    (fun s hs =>
      w.image_in_source (Smooth2Simplex.face2Param s)
        (face2Param_mem_standardSimplex2 hs))
    (fun s hs =>
      w.chart_image_in_ball (Smooth2Simplex.face0Param s)
        (face0Param_mem_standardSimplex2 hs))
    (fun s hs =>
      w.chart_image_in_ball (Smooth2Simplex.face1Param s)
        (face1Param_mem_standardSimplex2 hs))
    (fun s hs =>
      w.chart_image_in_ball (Smooth2Simplex.face2Param s)
        (face2Param_mem_standardSimplex2 hs))

/-- **The σ-field of the converted `ChartContainedSmooth2Simplex` equals `T`.** -/
@[simp] lemma ChartContainmentWitness.toChartContained_σ
    {T : Smooth2Simplex 𝓘(ℝ, ℂ) X} (w : ChartContainmentWitness T) :
    w.toChartContained.σ = T := rfl

/-- **`SubdivisionTelescopingTo2Simplex_named X` from
`UniformChartContainmentDepth_named X`.**

Given the named uniform-depth hypothesis, produce the list of
chart-contained sub-simplices required by the subdivision-telescoping
named hypothesis. The period-sum identity follows from
`complexChainPeriod_boundary_eq_iteratedMidpointList_sum`. -/
theorem subdivisionTelescopingTo2Simplex_named_of_uniformChartContainmentDepth
    (h : UniformChartContainmentDepth_named X) :
    SubdivisionTelescopingTo2Simplex_named (X := X) := by
  intro σ α
  obtain ⟨n, h_n⟩ := h σ
  -- Convert each T in iteratedMidpointList σ n to a ChartContainedSmooth2Simplex via witness.
  let L := Smooth2Simplex.iteratedMidpointList σ n
  -- Use Classical.choice on Nonempty (ChartContainmentWitness T) to get an actual witness.
  let witness : ∀ T ∈ L, ChartContainedSmooth2Simplex X :=
    fun T hT => (h_n T hT).some.toChartContained
  -- Map L.attach to the witness-derived list.
  refine ⟨L.attach.map (fun T => witness T.val T.property), ?_⟩
  -- Period-sum identity.
  rw [Smooth2Simplex.complexChainPeriod_boundary_eq_iteratedMidpointList_sum σ α n]
  -- LHS: ((iteratedMidpointList σ n).map fun T => chainPeriod (∂T) α).sum.
  -- RHS: ((L.attach.map (fun T => witness T.val T.property)).map
  --       (fun s => chainPeriod (∂s.σ) α)).sum.
  --
  -- Use `List.map_attach` and the σ-field identity to align.
  rw [List.map_map]
  show (List.map (fun T => complexChainPeriod (Smooth2Simplex.boundary T) α) L).sum
      = (L.attach.map (fun T => complexChainPeriod
              (Smooth2Simplex.boundary (witness T.val T.property).σ) α)).sum
  -- Since `witness T _ |>.σ = T` (via `toChartContained_σ`), the inner functions match.
  rw [show (fun T : { x // x ∈ L } => complexChainPeriod
          (Smooth2Simplex.boundary (witness T.val T.property).σ) α)
        = (fun T : { x // x ∈ L } => complexChainPeriod
            (Smooth2Simplex.boundary T.val) α) by
    funext T
    show complexChainPeriod (Smooth2Simplex.boundary (witness T.val T.property).σ) α
        = complexChainPeriod (Smooth2Simplex.boundary T.val) α
    have h_σ : (witness T.val T.property).σ = T.val :=
      ChartContainmentWitness.toChartContained_σ _
    rw [h_σ]]
  -- Reduce L.attach.map (... T.val) to L.map (...). Use the
  -- attach-map identity at the Subtype level.
  rw [show (L.attach.map (fun T : { x // x ∈ L } =>
            complexChainPeriod (Smooth2Simplex.boundary T.val) α))
        = (L.map (fun T => complexChainPeriod (Smooth2Simplex.boundary T) α)) by
    induction L with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.attach_cons, List.map_cons]
      congr 1
      -- For the tail: `tl.attach` was rewritten by `List.attach_cons` to
      -- `List.map (fun x => ⟨↑x, _⟩) tl.attach`. Compose the two outer
      -- `List.map`s via `List.map_map`; the composed function reduces
      -- definitionally to the LHS function of `ih`.
      rw [List.map_map]
      exact ih]

/-- **`HolomorphicComponentsCanonicalClosed X` from
`UniformChartContainmentDepth_named X`.** Direct corollary of the
above bridge composed with the subdivision-telescoping discharge. -/
theorem holomorphicComponentsCanonicalClosed_of_uniformChartContainmentDepth'
    (h : UniformChartContainmentDepth_named X) :
    HolomorphicComponentsCanonicalClosed X :=
  holomorphicComponentsCanonicalClosed_of_subdivisionTo2Simplex
    (subdivisionTelescopingTo2Simplex_named_of_uniformChartContainmentDepth h)

end JacobianChallenge

end
