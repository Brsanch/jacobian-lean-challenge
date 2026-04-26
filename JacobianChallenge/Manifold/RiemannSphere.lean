/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.MetricSpace.Bounded

/-! # The Riemann sphere — carrier, topology, and two-chart atlas

This file declares the **Riemann sphere** as the type abbreviation
`RiemannSphere := OnePoint ℂ`, records the inherited compactness/Hausdorff/
connectedness instances, and constructs an explicit two-chart atlas on it
giving a `ChartedSpace ℂ RiemannSphere` instance.

## What ships

* `JacobianChallenge.RiemannSphere` — type abbreviation for `OnePoint ℂ`,
  carrying the one-point compactification topology.
* Inherited `CompactSpace`, `T2Space`, `ConnectedSpace` instances, recorded
  as `example` declarations so the file fails fast if mathlib's `OnePoint`
  API ever drops them.
* `RiemannSphere.chartN : OpenPartialHomeomorph RiemannSphere ℂ` — the
  "north" chart `(some z) ↦ z`, defined on the open set `{x ≠ ∞}`.
  Built as `(IsOpenEmbedding.toOpenPartialHomeomorph ...).symm` so its
  source equals `Set.range (↑) = {∞}ᶜ` (via `OnePoint.compl_infty`) and
  its target equals `Set.univ`.
* `RiemannSphere.chartS : OpenPartialHomeomorph RiemannSphere ℂ` — the
  "south" chart sending `(some z) ↦ z⁻¹` for `z ≠ 0` and `∞ ↦ 0`, defined
  on the open set `{some 0}ᶜ` (open because `{some 0}` is closed in the T₁
  space `OnePoint ℂ`). Built directly via
  `OpenPartialHomeomorph.ofContinuousOpen` from a hand-written
  `PartialEquiv` whose left/right inverse equations are checked by an
  explicit `OnePoint.rec` case split.
* `instance : ChartedSpace ℂ RiemannSphere` — the two-chart atlas
  `{chartN, chartS}`, with `chartAt x = chartN` if `x ≠ ∞` and `chartS`
  otherwise. Decidability of `x = ∞` comes from the underlying
  `Option`/`OnePoint` decidable instance (Lean's `decEq` on `Option`
  delegates the first slot — `∞ = none` — without needing
  `DecidableEq ℂ`).

## Deferred to follow-up

The `IsManifold 𝓘(ℂ) ω RiemannSphere` instance — which would require
verifying analyticity of the transition map `chartN ∘ chartS.symm = 1/z`
on `ℂ \ {0}` along with the trivial diagonal cases — is intentionally
not proved here. The transition-map composition manipulation
(`OpenPartialHomeomorph.symm_trans_*` source/target intersection chasing
through the model-with-corners identity) is delicate enough at this
mathlib pin (`8e3c989...`, 2026-04-15) that landing it in the same patch
risks the same fate as the previous chart attempt that was reverted on
`feat/riemann-sphere`. It is queued as a follow-up PR. The pure
analyticity ingredient is already present in mathlib at this pin
(`analyticOnNhd_inv : AnalyticOnNhd 𝕜 (fun z ↦ z⁻¹) {z | z ≠ 0}`,
`Mathlib/Analysis/Analytic/Constructions.lean`); only the
chart-transition wiring remains to write. -/

open OnePoint Set Topology

namespace JacobianChallenge

/-- The **Riemann sphere**: the one-point compactification of `ℂ`. As a type,
this is `Option ℂ` with the compactification topology making it compact,
Hausdorff, and connected. -/
abbrev RiemannSphere : Type := OnePoint ℂ

namespace RiemannSphere

/-- Compactness of the Riemann sphere — inherited from
`OnePoint.instCompactSpace`. -/
example : CompactSpace RiemannSphere := inferInstance

/-- Hausdorff property — inherited from `OnePoint`'s `T2Space` instance,
which applies because `ℂ` is weakly locally compact and Hausdorff. -/
example : T2Space RiemannSphere := inferInstance

/-- Connectedness — inherited because `ℂ` is preconnected and noncompact. -/
example : ConnectedSpace RiemannSphere := inferInstance

/-! ### The "north" chart `chartN`

This is the chart that "removes ∞" — it sends `(some z) ↦ z` and is defined
on the open complement of `{∞}`. We build it as the symmetric of the open
embedding `(↑) : ℂ → OnePoint ℂ`.

Concretely:

* source = `Set.range ((↑) : ℂ → OnePoint ℂ) = {∞}ᶜ` (via `compl_infty`)
* target = `Set.univ`
* `chartN (some z) = z`, `chartN.symm z = some z`. -/

/-- The "north" chart on the Riemann sphere: `(some z) ↦ z` on `{x ≠ ∞}`. -/
noncomputable def chartN : OpenPartialHomeomorph RiemannSphere ℂ :=
  (IsOpenEmbedding.toOpenPartialHomeomorph
      ((↑) : ℂ → OnePoint ℂ) OnePoint.isOpenEmbedding_coe).symm

@[simp] lemma chartN_source : chartN.source = {x : RiemannSphere | x ≠ ∞} := by
  -- `chartN.source = (toOpenPartialHomeomorph coe).target = range coe`,
  -- and `range coe = {∞}ᶜ = {x | x ≠ ∞}` via `compl_infty`.
  unfold chartN
  rw [OpenPartialHomeomorph.symm_source,
      IsOpenEmbedding.toOpenPartialHomeomorph_target]
  ext x
  simp [← OnePoint.compl_infty, Set.mem_compl_iff, Set.mem_singleton_iff]

@[simp] lemma chartN_target : chartN.target = (Set.univ : Set ℂ) := by
  unfold chartN
  rw [OpenPartialHomeomorph.symm_target,
      IsOpenEmbedding.toOpenPartialHomeomorph_source]

/-! ### The "south" chart `chartS`

This chart "removes `0`" — it sends `(some z) ↦ z⁻¹` (for `z ≠ 0`) and
`∞ ↦ 0`, defined on the open complement of `{some 0}`. The complement is
open because `{some 0}` is a single coercion-image point, closed in the T₂
(hence T₁) space `OnePoint ℂ`.

We build it directly via `OpenPartialHomeomorph.ofContinuousOpen` from a
hand-written `PartialEquiv`. -/

/-- The underlying set function of `chartS`: `(some z) ↦ z⁻¹`, `∞ ↦ 0`. -/
noncomputable def chartSToFun : RiemannSphere → ℂ :=
  fun x => OnePoint.rec 0 (fun z => z⁻¹) x

/-- The set function inverse for `chartS`: `0 ↦ ∞`, `z ≠ 0 ↦ some z⁻¹`.
On `ℂ` we use `if z = 0 then ∞ else (some z⁻¹)`; since equality with `0` in
`ℂ` is decidable propositionally we use `Classical.dec` here. -/
noncomputable def chartSInvFun : ℂ → RiemannSphere :=
  fun z => if z = 0 then (∞ : RiemannSphere) else ((z⁻¹ : ℂ) : RiemannSphere)

@[simp] lemma chartSToFun_infty : chartSToFun ∞ = 0 := rfl

@[simp] lemma chartSToFun_coe (z : ℂ) : chartSToFun ((z : RiemannSphere)) = z⁻¹ := rfl

@[simp] lemma chartSInvFun_zero : chartSInvFun 0 = (∞ : RiemannSphere) := by
  simp [chartSInvFun]

lemma chartSInvFun_of_ne {z : ℂ} (hz : z ≠ 0) :
    chartSInvFun z = ((z⁻¹ : ℂ) : RiemannSphere) := by
  simp [chartSInvFun, hz]

/-- The underlying `PartialEquiv` of `chartS`. Source = `{some 0}ᶜ`,
target = `Set.univ`. -/
noncomputable def chartSPartialEquiv : PartialEquiv RiemannSphere ℂ where
  toFun := chartSToFun
  invFun := chartSInvFun
  source := {x : RiemannSphere | x ≠ ((0 : ℂ) : RiemannSphere)}
  target := Set.univ
  map_source' := by intro _ _; trivial
  map_target' := by
    intro z _
    show chartSInvFun z ≠ ((0 : ℂ) : RiemannSphere)
    by_cases hz : z = 0
    · subst hz
      rw [chartSInvFun_zero]
      exact OnePoint.infty_ne_coe (0 : ℂ)
    · rw [chartSInvFun_of_ne hz]
      have hzinv : z⁻¹ ≠ 0 := inv_ne_zero hz
      intro h
      exact hzinv (OnePoint.coe_injective h)
  left_inv' := by
    intro x hx
    -- `x ≠ some 0`. Cases on `x : OnePoint ℂ`.
    rcases x with _ | z
    · -- x = ∞: chartSToFun ∞ = 0; chartSInvFun 0 = ∞.
      show chartSInvFun (chartSToFun ∞) = ∞
      rw [chartSToFun_infty, chartSInvFun_zero]
    · -- x = some z. Membership says `some z ≠ some 0`, hence `z ≠ 0`.
      have hz : z ≠ 0 := by
        intro h
        apply hx
        show ((z : ℂ) : RiemannSphere) = ((0 : ℂ) : RiemannSphere)
        rw [h]
      have hzinv : z⁻¹ ≠ 0 := inv_ne_zero hz
      show chartSInvFun (chartSToFun ((z : RiemannSphere))) = (z : RiemannSphere)
      rw [chartSToFun_coe, chartSInvFun_of_ne hzinv, inv_inv]
  right_inv' := by
    intro z _
    by_cases hz : z = 0
    · subst hz
      show chartSToFun (chartSInvFun (0 : ℂ)) = 0
      rw [chartSInvFun_zero, chartSToFun_infty]
    · show chartSToFun (chartSInvFun z) = z
      rw [chartSInvFun_of_ne hz, chartSToFun_coe, inv_inv]

/-- Continuity of `chartSInvFun : ℂ → RiemannSphere`. The map is `0 ↦ ∞` and
`z ≠ 0 ↦ some z⁻¹`. We check continuity at every point: at `0` we use
`OnePoint.tendsto_nhds_infty` (closed-compact ball complement maps into a
neighborhood of `∞`); at `z ≠ 0` the map locally agrees with `(↑) ∘ (·⁻¹)`. -/
lemma continuous_chartSInvFun : Continuous chartSInvFun := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · -- ContinuousAt at 0, where chartSInvFun 0 = ∞.
    subst hz
    have h0 : chartSInvFun (0 : ℂ) = (∞ : RiemannSphere) := chartSInvFun_zero
    rw [ContinuousAt, h0, OnePoint.nhds_infty_eq]
    -- We must show `Tendsto chartSInvFun (𝓝 0) (map ↑ (coclosedCompact ℂ) ⊔ pure ∞)`.
    -- Strategy: show `Tendsto chartSInvFun (𝓝[≠] 0) (map ↑ (coclosedCompact ℂ))` and
    -- `Tendsto chartSInvFun (pure 0) (pure ∞)`, then combine.
    rw [show (𝓝 (0 : ℂ)) = 𝓝[≠] (0 : ℂ) ⊔ pure 0 from
      (nhdsNE_sup_pure (0 : ℂ)).symm]
    rw [Filter.tendsto_sup]
    refine ⟨?_, ?_⟩
    · -- On `𝓝[≠] 0`, chartSInvFun w = ↑ w⁻¹. We aim into the left summand
      -- `map ↑ (coclosedCompact ℂ)`.
      apply Filter.Tendsto.mono_right _ le_sup_left
      have hcongr : (fun w : ℂ => ((w⁻¹ : ℂ) : RiemannSphere))
          =ᶠ[𝓝[≠] (0 : ℂ)] chartSInvFun := by
        refine Filter.eventually_of_mem
          (self_mem_nhdsWithin (a := (0 : ℂ)) (s := {(0 : ℂ)}ᶜ)) ?_
        intro w hw
        exact (chartSInvFun_of_ne hw).symm
      refine Filter.Tendsto.congr' hcongr ?_
      -- Tendsto Inv.inv (𝓝[≠] 0) (cobounded ℂ) = (cocompact ℂ) ≤ coclosedCompact ℂ.
      have hinv : Filter.Tendsto (fun w : ℂ => w⁻¹) (𝓝[≠] (0 : ℂ))
          (Filter.coclosedCompact ℂ) := by
        refine (Filter.tendsto_inv₀_nhdsNE_zero (α := ℂ)).mono_right ?_
        rw [Metric.cobounded_eq_cocompact]
        exact Filter.cocompact_le_coclosedCompact
      -- Push forward through `(↑) : ℂ → RiemannSphere`.
      have hcoe : Filter.Tendsto ((↑) : ℂ → RiemannSphere)
          (Filter.coclosedCompact ℂ) (Filter.map (↑) (Filter.coclosedCompact ℂ)) :=
        Filter.tendsto_map
      exact hcoe.comp hinv
    · -- pure 0 ↦ pure ∞ ≤ map ↑ (coclosedCompact ℂ) ⊔ pure ∞.
      have h := Filter.tendsto_pure_pure chartSInvFun 0
      rw [chartSInvFun_zero] at h
      exact h.mono_right le_sup_right
  · -- ContinuousAt at z ≠ 0.
    have hloc : (chartSInvFun : ℂ → RiemannSphere)
        =ᶠ[𝓝 z] (fun w => ((w⁻¹ : ℂ) : RiemannSphere)) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
      exact chartSInvFun_of_ne hw
    rw [ContinuousAt]
    have hzval : chartSInvFun z = ((z⁻¹ : ℂ) : RiemannSphere) := chartSInvFun_of_ne hz
    rw [hzval]
    refine Filter.Tendsto.congr' (hloc.symm) ?_
    -- `(↑) ∘ (·⁻¹)` is continuous at z (since z ≠ 0).
    exact (OnePoint.continuous_coe.continuousAt).comp (continuousAt_inv₀ hz)

/-- The "south" chart on the Riemann sphere: `(some z) ↦ z⁻¹`, `∞ ↦ 0`,
on `{x ≠ some 0}`. We construct it directly via the
`OpenPartialHomeomorph` structure: forward continuity on the source is
proved point-wise; inverse continuity holds on all of `ℂ`
(`continuous_chartSInvFun`); both `source` and `target = Set.univ` are open. -/
noncomputable def chartS : OpenPartialHomeomorph RiemannSphere ℂ where
  toPartialEquiv := chartSPartialEquiv
  open_source := by
    -- `{x | x ≠ some 0}` is the complement of the closed point `{some 0}`.
    show IsOpen ({x : RiemannSphere | x ≠ ((0 : ℂ) : RiemannSphere)})
    rw [show ({x : RiemannSphere | x ≠ ((0 : ℂ) : RiemannSphere)} : Set RiemannSphere)
          = ({((0 : ℂ) : RiemannSphere)} : Set RiemannSphere)ᶜ from rfl]
    exact isClosed_singleton.isOpen_compl
  open_target := isOpen_univ
  continuousOn_toFun := by
    -- continuity of `chartSToFun` on `{x ≠ some 0}`
    apply continuousOn_of_forall_continuousAt
    intro x hx
    induction x using OnePoint.rec with
    | infty =>
      -- ContinuousAt at ∞.
      rw [OnePoint.continuousAt_infty]
      intro s hs
      rw [show (chartSToFun ∞ : ℂ) = 0 from rfl] at hs
      rcases Metric.mem_nhds_iff.mp hs with ⟨r, hr_pos, hball⟩
      refine ⟨Metric.closedBall (0 : ℂ) r⁻¹, Metric.isClosed_closedBall,
              isCompact_closedBall 0 r⁻¹, ?_⟩
      intro z hz
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hz
      have hz_ne : z ≠ 0 := by
        intro h
        subst h
        simp at hz
        exact absurd hz (not_lt.mpr (by positivity))
      have h1 : (chartSToFun ∘ ((↑) : ℂ → RiemannSphere)) z = z⁻¹ := rfl
      rw [h1]
      apply hball
      simp only [Metric.mem_ball, dist_zero_right, norm_inv]
      rw [inv_lt_comm₀ (by positivity) hr_pos] at hz
      · exact hz
    | coe z =>
      -- ContinuousAt at `(some z)` with `some z ≠ some 0`, hence `z ≠ 0`.
      have hz : z ≠ 0 := by
        intro h
        apply hx
        show ((z : ℂ) : RiemannSphere) = ((0 : ℂ) : RiemannSphere)
        rw [h]
      rw [OnePoint.continuousAt_coe]
      exact (continuous_inv₀.continuousAt (x := z) hz).congr (by intro w; rfl)
  continuousOn_invFun := continuous_chartSInvFun.continuousOn

end RiemannSphere

end JacobianChallenge
