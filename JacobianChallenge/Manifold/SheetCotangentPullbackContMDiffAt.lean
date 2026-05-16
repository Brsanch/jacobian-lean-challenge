/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PullbackSectionSmoothness
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalSheetSmoothOn

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Per-sheet cotangent-pullback section smoothness at a regular value

For a smooth-at-`y₀` map `g : Y → X` between complex 1-manifolds and a
`HolomorphicOneForm X` `α`, the **pointwise cotangent pullback** section

  `y ↦ (α.toFun (g y)).comp (mfderiv g y)
        : CotangentSpace 𝓘(ℂ, ℂ) y`

is `ContMDiffAt 𝓘(ℂ, ℂ) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω` at `y₀`
when viewed as a total-space-valued map.

This is the local-sheet analogue of
`HolomorphicEquiv.pullbackSection_contMDiffAt` in
`Manifold/PullbackSectionSmoothness.lean`. The two proofs share the
same scaffold (`ContMDiffAt.clm_apply_of_inCoordinates` plus the
cotangent↔tangent inCoordinates bridge); this version only assumes
**pointwise** `ContMDiffAt ω` of the underlying map, not a global
`HolomorphicEquiv`.

Application: feeding the local biholomorphism `sheet.g` produced by
`MeromorphicNonzero.localSheetData_at_regular` (with its
`ContMDiffAt ω` witness from
`Manifold/MeromorphicNonzeroLocalSheetSmoothOn.lean`) into
`pullbackSection_contMDiffAt_of_localSheet` yields per-sheet
smoothness at every regular value `f.toRiemannSphere p`. This is the
building block for the trace section `f_*α`'s smoothness on
`f.regularValueSet` (subsequent chips: Finset sum over the fiber,
then `SmoothOneFormOn` gluing).

The proof structure:

* `cotangent_inCoordinates_flip_eventually_eq_of_continuousAt` —
  local eventually-form of the cotangent↔tangent inCoordinates
  bridge identity, requiring only `ContinuousAt g y₀` instead of
  global continuity. (Bridge identity itself is universal in `g` and
  available from `PullbackSectionSmoothness`.)

* `pullbackSection_contMDiffAt_of_localSheet` — the headline. Mirrors
  the `clm_apply_of_inCoordinates` assembly from
  `HolomorphicEquiv.pullbackSection_contMDiffAt`, with the global
  `e.contMDiff_forward` smoothness witness replaced by a pointwise
  `ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g y₀` hypothesis.

* `MeromorphicNonzero.sheetPullbackSection_contMDiffAt` — wrapper
  specialised to the local sheet at a regular value, discharging the
  smoothness hypothesis via
  `f.contMDiffAt_localSheet_g_at_basePoint`.

No `sorry`, no `axiom`. -/

open Set Filter
open scoped Manifold ContDiff Topology
open ContinuousLinearMap

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-- `ω + 1 ≤ ω` in `WithTop ℕ∞`. (Inline copy of the same fact in
`Manifold/PullbackPointwiseFunctionSmooth.lean`, which is `private`
there.) -/
private theorem analytic_succ_le_analytic' : (ω + 1 : WithTop ℕ∞) ≤ ω := by
  decide

/-! ## Local eventually-form of the cotangent↔tangent inCoordinates bridge

Generalises `cotangent_inCoordinates_flip_eventually_eq_flip_inTangentCoordinates`
(which requires global `Continuous g`) to the local case
`ContinuousAt g y₀`. The pointwise identity
`cotangent_inCoordinates_flip_eq_flip_inTangentCoordinates` is already
stated for an arbitrary function `g`; this lemma just packages the
neighbourhood-of-`y₀` quantifier. -/

/-- **Local cotangent↔tangent inCoordinates bridge, eventually form.**
For any `g : Y → X` with `ContinuousAt g y₀`, the cotangent
`inCoordinates` of `((compL).flip (mfderiv g _))` agrees, in a
neighbourhood of `y₀`, with `(compL).flip` of the tangent
`inCoordinates` of `mfderiv g _`. -/
private theorem cotangent_inCoordinates_flip_eventually_eq_of_continuousAt
    (g : Y → X) {y₀ : Y} (hg : ContinuousAt g y₀) :
    (fun y : Y =>
      ContinuousLinearMap.inCoordinates (ℂ →L[ℂ] ℂ)
        (CotangentSpace (𝓘(ℂ, ℂ)) : X → Type _) (ℂ →L[ℂ] ℂ)
        (CotangentSpace (𝓘(ℂ, ℂ)) : Y → Type _)
        (g y₀) (g y) y₀ y
        ((ContinuousLinearMap.compL ℂ ℂ ℂ ℂ).flip
          (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) g y)))
    =ᶠ[nhds y₀] (fun y : Y =>
      (ContinuousLinearMap.compL ℂ ℂ ℂ ℂ).flip
        (inTangentCoordinates (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) id g
          (fun y => mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) g y) y₀ y)) := by
  have h_chart_Y : (chartAt ℂ y₀).source ∈ nhds y₀ :=
    (chartAt ℂ y₀).open_source.mem_nhds (mem_chart_source ℂ y₀)
  have h_chart_X : g ⁻¹' (chartAt ℂ (g y₀)).source ∈ nhds y₀ :=
    hg ((chartAt ℂ (g y₀)).open_source.mem_nhds (mem_chart_source ℂ (g y₀)))
  filter_upwards [h_chart_Y, h_chart_X] with y hy hgy
  exact cotangent_inCoordinates_flip_eq_flip_inTangentCoordinates g hy hgy

/-! ## Headline: pullback-section smoothness at a regular point of a
local biholomorphism -/

/-- **Pointwise pullback along a map `g : Y → X`.** The dependently-typed
form `∀ y : Y, CotangentSpace 𝓘(ℂ, ℂ) y` (rather than the displayed
`ℂ →L[ℂ] ℂ`), matching the `HolomorphicEquiv.pullbackPointwise` shape.
Needed for clean bundle-instance resolution in the smoothness theorem. -/
def localSheetPullbackPointwise (g : Y → X) (α : HolomorphicOneForm X) :
    ∀ y : Y, CotangentSpace (𝓘(ℂ, ℂ)) y :=
  fun y => ContinuousLinearMap.comp (α.toFun (g y))
    (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) g y)

/-- Definitional unfolding of `localSheetPullbackPointwise`. -/
theorem localSheetPullbackPointwise_apply
    (g : Y → X) (α : HolomorphicOneForm X) (y : Y) :
    localSheetPullbackPointwise g α y
      = ContinuousLinearMap.comp (α.toFun (g y))
          (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) g y) := rfl

/-- **Per-local-sheet pullback section smoothness.** For a map
`g : Y → X` between complex 1-manifolds with
`ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g y₀` (e.g. a local biholomorphism
near `y₀`), and a holomorphic 1-form `α : HolomorphicOneForm X`,
the section

  `y ↦ TotalSpace.mk' (ℂ →L[ℂ] ℂ) y (localSheetPullbackPointwise g α y)`

is `ContMDiffAt 𝓘(ℂ, ℂ) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω` at `y₀`. -/
theorem pullbackSection_contMDiffAt_of_localSheet
    (g : Y → X) {y₀ : Y} (hg : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g y₀)
    (α : HolomorphicOneForm X) :
    ContMDiffAt (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun y : Y => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) y
        (localSheetPullbackPointwise g α y)) y₀ := by
  -- Recast the section in `ϕ y (v y)` shape with
  --   ϕ y := (compL).flip (mfderiv g y),
  --   v y := α.toFun (g y).
  -- This is the form needed by `ContMDiffAt.clm_apply_of_inCoordinates`.
  let b₁ : Y → X := g
  let b₂ : Y → Y := id
  let v : ∀ y : Y, CotangentSpace (𝓘(ℂ, ℂ)) (b₁ y) := fun y => α.toFun (b₁ y)
  let ϕ : ∀ y : Y,
      CotangentSpace (𝓘(ℂ, ℂ)) (b₁ y) →L[ℂ]
        CotangentSpace (𝓘(ℂ, ℂ)) (b₂ y) :=
    fun y => (ContinuousLinearMap.compL ℂ ℂ ℂ ℂ).flip
      (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) g y)
  -- The pullback equals ϕ y (v y) by direct computation.
  have h_eq : ∀ y : Y,
      localSheetPullbackPointwise g α y = ϕ y (v y) := by
    intro y
    show ContinuousLinearMap.comp (α.toFun (g y))
        (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) g y)
      = ((ContinuousLinearMap.compL ℂ ℂ ℂ ℂ).flip
          (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) g y))
            (α.toFun (g y))
    rfl
  have h_funext : (fun y : Y => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) y
      (localSheetPullbackPointwise g α y))
    = (fun y : Y => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) (b₂ y) (ϕ y (v y))) := by
    funext y; rw [h_eq y]; rfl
  rw [h_funext]
  -- ϕ-side smoothness.
  have h_phi : ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, (ℂ →L[ℂ] ℂ) →L[ℂ] (ℂ →L[ℂ] ℂ))) ω
      (fun y : Y => ContinuousLinearMap.inCoordinates (ℂ →L[ℂ] ℂ)
        (CotangentSpace (𝓘(ℂ, ℂ)) : X → Type _) (ℂ →L[ℂ] ℂ)
        (CotangentSpace (𝓘(ℂ, ℂ)) : Y → Type _)
        (b₁ y₀) (b₁ y) (b₂ y₀) (b₂ y) (ϕ y)) y₀ := by
    have h_mfderiv_transpose : ContMDiffAt (𝓘(ℂ, ℂ))
        (𝓘(ℂ, (ℂ →L[ℂ] ℂ) →L[ℂ] (ℂ →L[ℂ] ℂ))) ω
        (fun y : Y => (ContinuousLinearMap.compL ℂ ℂ ℂ ℂ).flip
          (inTangentCoordinates (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) id g
            (fun y => mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) g y) y₀ y)) y₀ :=
      hg.mfderiv_transpose analytic_succ_le_analytic'
    have h_bridge :=
      cotangent_inCoordinates_flip_eventually_eq_of_continuousAt
        (g := g) hg.continuousAt
    exact h_mfderiv_transpose.congr_of_eventuallyEq h_bridge
  -- v-side smoothness: α composed with g.
  have h_v : ContMDiffAt (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun y : Y => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) (b₁ y) (v y)) y₀ :=
    α.contMDiff.contMDiffAt.comp y₀ hg
  exact ContMDiffAt.clm_apply_of_inCoordinates (hϕ := h_phi) (hv := h_v)
    (hb₂ := contMDiffAt_id)

/-! ## MeromorphicNonzero specialisation -/

namespace MeromorphicNonzero

universe u

variable {Z : Type u}
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold (𝓘(ℂ, ℂ)) ω Z]

/-- **Per-sheet pullback section smoothness at a regular value.**

For a non-constant `f : MeromorphicNonzero Z` and a regular preimage
`p ∈ f.regularSet`, the local sheet
`(f.localSheetData_at_regular hnc hp_reg).g : RiemannSphere → Z`
gives rise to a pullback section

  `v ↦ TotalSpace.mk' (ℂ →L[ℂ] ℂ) v
        ((α.toFun (sheet.g v)).comp (mfderiv sheet.g v))`

which is `ContMDiffAt ω` at `v₀ := f.toRiemannSphere p`. -/
theorem sheetPullbackSection_contMDiffAt
    (f : MeromorphicNonzero Z)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {p : Z} (hp_reg : p ∈ f.regularSet)
    (α : HolomorphicOneForm Z) :
    ContMDiffAt (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun v : RiemannSphere => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) v
        (localSheetPullbackPointwise
          (f.localSheetData_at_regular hnc hp_reg).g α v))
      (f.toRiemannSphere p) :=
  pullbackSection_contMDiffAt_of_localSheet
    (g := (f.localSheetData_at_regular hnc hp_reg).g)
    (f.contMDiffAt_localSheet_g_at_basePoint hnc hp_reg) α

end MeromorphicNonzero

end JacobianChallenge

end
