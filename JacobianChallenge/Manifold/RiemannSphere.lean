/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

set_option diagnostics.threshold 100

/-! # The Riemann sphere as a `ChartedSpace ℂ`

This file constructs the **Riemann sphere** `RiemannSphere := OnePoint ℂ` as a
`ChartedSpace ℂ` with the standard two-chart atlas (`chartN`, `chartS`), and
proves analyticity of all four atlas-pair transitions as a private lemma
(`riemannSphere_compatible`) ready to be fed to `isManifold_of_contDiffOn`
once the consumer code wants it.

## Main definitions

* `JacobianChallenge.RiemannSphere`  — type abbreviation for `OnePoint ℂ`,
  carrying the inherited compactification topology and the
  `T2Space`/`CompactSpace`/`ConnectedSpace` instances from mathlib.
* `JacobianChallenge.RiemannSphere.chartN` — northern chart, source
  `{x : RiemannSphere | x ≠ ∞}`; on `some z` returns `z`.
* `JacobianChallenge.RiemannSphere.chartS` — southern chart, source
  `{x : RiemannSphere | x ≠ some 0}`; on `some z` returns `z⁻¹`
  (with `(0 : ℂ)⁻¹ = 0` by mathlib's junk convention) and on `∞` returns `0`.
* The `ChartedSpace ℂ RiemannSphere` instance assembling the two-chart atlas.
* `riemannSphere_compatible` — analytic compatibility of all four atlas-pair
  transitions. The actual `IsManifold 𝓘(ℂ) ω RiemannSphere` instance is left
  for a follow-up: building it from this lemma requires lining up
  `contDiffGroupoid`/`analyticGroupoid` membership shapes against the
  current mathlib API.

## Design notes

The transition map between the two charts is `z ↦ z⁻¹` on `ℂ \ {0}`, which is
holomorphic — this is the only non-trivial content of the manifold instance.
Of the two diagonal transitions, `chartN.symm ≫ chartN` is `id` on `univ` and
**`chartS.symm ≫ chartS` is also `id` on `univ`** — `chartS_inv 0 = ∞`, so
the source predicate `chartS_inv z ≠ some 0` holds for *every* `z ∈ ℂ`,
including `z = 0`. (An earlier draft of this file mistakenly identified that
source as `{z ≠ 0}`.)

Continuity at `∞` for the off-diagonal pieces is handled via
`OnePoint.continuous_iff` and `tendsto_inv₀_cobounded`, plus
`Filter.coclosedCompact_eq_cocompact` (R₁ space) and
`Metric.cobounded_eq_cocompact` (proper space) to bridge cobounded ↔
cocompact ↔ coclosedCompact filters on `ℂ`. -/

open scoped Manifold Topology
open OnePoint Set Filter Topology

noncomputable section

namespace JacobianChallenge

/-! ## The underlying type and inherited instances -/

/-- The **Riemann sphere**: the one-point compactification of `ℂ`. As a type,
this is `Option ℂ` with the compactification topology making it compact,
Hausdorff, and connected. -/
abbrev RiemannSphere : Type := OnePoint ℂ

namespace RiemannSphere

/-- Compactness of the Riemann sphere — inherited from
`OnePoint.instCompactSpace`. -/
example : CompactSpace RiemannSphere := inferInstance

/-- Hausdorff property — inherited from `OnePoint`'s normal-space instance,
which applies because `ℂ` is weakly locally compact and Hausdorff. -/
example : T2Space RiemannSphere := inferInstance

/-- Connectedness — inherited because `ℂ` is preconnected and noncompact. -/
example : ConnectedSpace RiemannSphere := inferInstance

/-! ## Two charts: northern (away from `∞`) and southern (away from `some 0`)

For the southern chart, the inverse map `chartS_inv : ℂ → RiemannSphere`
has `chartS_inv 0 = ∞` and `chartS_inv z = some z⁻¹` for `z ≠ 0`. We prove
its continuity once and reuse the result. -/

/-- Inverse of the southern chart, viewed as a function `ℂ → RiemannSphere`.
Sends `0 ↦ ∞` and `z ↦ some z⁻¹` for `z ≠ 0`. -/
def chartS_inv (z : ℂ) : RiemannSphere :=
  if z = 0 then ∞ else ((z⁻¹ : ℂ) : RiemannSphere)

@[simp] lemma chartS_inv_zero : chartS_inv 0 = ∞ := by simp [chartS_inv]
lemma chartS_inv_of_ne {z : ℂ} (hz : z ≠ 0) :
    chartS_inv z = ((z⁻¹ : ℂ) : RiemannSphere) := by simp [chartS_inv, hz]

/-- `chartS_inv` is continuous everywhere. The non-trivial point is `z = 0`,
where the function jumps to `∞`; we use the basis description of `𝓝 ∞` via
`OnePoint.tendsto_nhds_infty` together with `tendsto_inv₀_cobounded`. -/
lemma continuous_chartS_inv : Continuous chartS_inv := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · -- At `z = 0`: `chartS_inv 0 = ∞`. Show `Tendsto chartS_inv (𝓝 0) (𝓝 ∞)`.
    subst hz
    rw [ContinuousAt, chartS_inv_zero]
    -- Use `OnePoint.tendsto_nhds_infty`: for every `t ∈ 𝓝 ∞`, eventually
    -- `chartS_inv z ∈ t` for `z` near `0`. Equivalently we show
    -- `Tendsto (chartS_inv : ℂ → RiemannSphere) (𝓝 0) (𝓝 ∞)` by reducing to
    -- the `(↑) ∘ (·⁻¹)` form on a punctured neighborhood and using
    -- `tendsto_inv₀_cobounded`.
    -- Step 1: `chartS_inv` agrees with `(↑) ∘ (·⁻¹)` on `{0}ᶜ ∈ 𝓝[≠] 0`.
    have hagree : (fun z : ℂ => chartS_inv z) =ᶠ[𝓝[≠] 0]
        (fun z => (((z⁻¹ : ℂ) : RiemannSphere))) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact chartS_inv_of_ne hz
    -- Step 2: We split `𝓝 0 = 𝓝[≠] 0 ⊔ pure 0` and prove tendsto on each.
    have hpure : Tendsto (chartS_inv : ℂ → RiemannSphere) (pure 0) (𝓝 ∞) := by
      rw [tendsto_pure_left]; intro s hs
      rw [chartS_inv_zero] at hs ⊢
      exact mem_of_mem_nhds hs
    have hpunctured :
        Tendsto (chartS_inv : ℂ → RiemannSphere) (𝓝[≠] 0) (𝓝 ∞) := by
      rw [Filter.tendsto_congr' hagree]
      -- `Tendsto ((↑) ∘ (·⁻¹)) (𝓝[≠] 0) (𝓝 ∞)`. Compose:
      -- `(·⁻¹) : 𝓝[≠] 0 → cobounded ℂ`, then `(↑) : cobounded ℂ → 𝓝 ∞`.
      -- The first leg: `tendsto_inv₀_nhdsWithin_zero` gives `(·⁻¹)` tends to
      -- `cobounded`. Use `OnePoint.tendsto_coe_infty` for the second leg
      -- (which uses `coclosedCompact = cocompact = cobounded` for `ℂ`).
      have h1 : Tendsto (fun z : ℂ => z⁻¹) (𝓝[≠] (0 : ℂ)) (cobounded ℂ) := by
        exact (Filter.tendsto_inv_nhdsNE_zero)
      have h2 : Tendsto ((↑) : ℂ → RiemannSphere) (cobounded ℂ) (𝓝 ∞) := by
        rw [show (cobounded ℂ) = coclosedCompact ℂ by
              rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]]
        exact OnePoint.tendsto_coe_infty
      exact h2.comp h1
    -- Combine `𝓝 0 = 𝓝[≠] 0 ⊔ pure 0`.
    rw [show (𝓝 (0 : ℂ)) = 𝓝[≠] 0 ⊔ pure 0 from (nhdsWithin_compl_singleton_sup_pure 0).symm]
    exact Tendsto.sup hpunctured hpure
  · -- At `z ≠ 0`: `chartS_inv` agrees with `(↑) ∘ (·⁻¹)` on a neighborhood.
    apply ContinuousAt.congr (f := fun w : ℂ => (((w⁻¹ : ℂ) : RiemannSphere)))
    · exact (OnePoint.continuous_coe.continuousAt).comp (continuousAt_inv₀ hz)
    · -- `chartS_inv =ᶠ (↑) ∘ (·⁻¹)` near `z ≠ 0`.
      filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
      exact chartS_inv_of_ne hw

/-- Underlying `PartialEquiv` for the northern chart. Source `{x | x ≠ ∞}`,
target `Set.univ`; `some z ↦ z`. -/
def chartN_partialEquiv : PartialEquiv RiemannSphere ℂ where
  toFun x := x.elim 0 id
  invFun z := (z : RiemannSphere)
  source := {x : RiemannSphere | x ≠ ∞}
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' z _ := OnePoint.coe_ne_infty z
  left_inv' x hx := by
    rcases x with _ | z
    · exact (hx rfl).elim
    · rfl
  right_inv' _ _ := rfl

/-- The northern chart of the Riemann sphere as an `OpenPartialHomeomorph`. -/
def chartN : OpenPartialHomeomorph RiemannSphere ℂ where
  toPartialEquiv := chartN_partialEquiv
  open_source := by
    have h : ({x : RiemannSphere | x ≠ ∞}) = ({∞} : Set RiemannSphere)ᶜ := by
      ext x; simp [Set.mem_compl_iff]
    rw [show chartN_partialEquiv.source = {x : RiemannSphere | x ≠ ∞} from rfl, h]
    exact OnePoint.isClosed_infty.isOpen_compl
  open_target := isOpen_univ
  continuousOn_toFun := by
    intro x hx
    rcases x with _ | z
    · exact (hx rfl).elim
    · apply ContinuousAt.continuousWithinAt
      rw [OnePoint.continuousAt_coe]
      change ContinuousAt (fun w : ℂ => w) z
      exact continuous_id.continuousAt
  continuousOn_invFun := by
    intro z _
    exact OnePoint.continuous_coe.continuousAt.continuousWithinAt

@[simp] lemma chartN_apply_coe (z : ℂ) : chartN ((z : RiemannSphere)) = z := rfl
@[simp] lemma chartN_apply_infty : chartN (∞ : RiemannSphere) = 0 := rfl
@[simp] lemma chartN_symm_apply (z : ℂ) : chartN.symm z = (z : RiemannSphere) := rfl
@[simp] lemma chartN_source : chartN.source = {x : RiemannSphere | x ≠ ∞} := rfl
@[simp] lemma chartN_target : chartN.target = Set.univ := rfl

/-- Underlying `PartialEquiv` for the southern chart. Source
`{x | x ≠ some 0}`, target `Set.univ`; `some z ↦ z⁻¹` and `∞ ↦ 0`. -/
def chartS_partialEquiv : PartialEquiv RiemannSphere ℂ where
  toFun x := x.elim 0 (fun z => z⁻¹)
  invFun := chartS_inv
  source := {x : RiemannSphere | x ≠ ((0 : ℂ) : RiemannSphere)}
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' z _ := by
    by_cases hz : z = 0
    · subst hz; simp [chartS_inv]; exact OnePoint.infty_ne_coe (0 : ℂ)
    · rw [chartS_inv_of_ne hz]
      intro hcoe
      exact (inv_ne_zero hz) (OnePoint.coe_injective hcoe)
  left_inv' x hx := by
    rcases x with _ | z
    · simp [chartS_inv]
    · have hz : z ≠ 0 := fun hz0 => hx (by rw [hz0])
      have hinv : z⁻¹ ≠ 0 := inv_ne_zero hz
      show chartS_inv (z⁻¹) = ((z : ℂ) : RiemannSphere)
      rw [chartS_inv_of_ne hinv, inv_inv]
  right_inv' z _ := by
    by_cases hz : z = 0
    · subst hz; simp [chartS_inv]
    · rw [chartS_inv_of_ne hz]
      show ((((z⁻¹ : ℂ) : RiemannSphere)).elim (0 : ℂ) (fun w : ℂ => w⁻¹)) = z
      change (z⁻¹ : ℂ)⁻¹ = z
      rw [inv_inv]

/-- The southern chart of the Riemann sphere as an `OpenPartialHomeomorph`. -/
def chartS : OpenPartialHomeomorph RiemannSphere ℂ where
  toPartialEquiv := chartS_partialEquiv
  open_source := by
    have h : ({x : RiemannSphere | x ≠ ((0 : ℂ) : RiemannSphere)})
        = ({((0 : ℂ) : RiemannSphere)} : Set RiemannSphere)ᶜ := by
      ext x; simp [Set.mem_compl_iff]
    rw [show chartS_partialEquiv.source
          = {x : RiemannSphere | x ≠ ((0 : ℂ) : RiemannSphere)} from rfl, h]
    exact isClosed_singleton.isOpen_compl
  open_target := isOpen_univ
  continuousOn_toFun := by
    intro x hx
    rcases x with _ | z
    · -- At `∞`.
      apply ContinuousAt.continuousWithinAt
      rw [OnePoint.continuousAt_infty']
      show Tendsto (fun z : ℂ => z⁻¹) (coclosedCompact ℂ) (𝓝 0)
      rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_cobounded
    · have hz : z ≠ 0 := fun hz0 => hx (by rw [hz0])
      apply ContinuousAt.continuousWithinAt
      rw [OnePoint.continuousAt_coe]
      change ContinuousAt (fun w : ℂ => w⁻¹) z
      exact continuousAt_inv₀ hz
  continuousOn_invFun := continuous_chartS_inv.continuousOn

@[simp] lemma chartS_apply_coe (z : ℂ) :
    chartS ((z : RiemannSphere)) = z⁻¹ := rfl
@[simp] lemma chartS_apply_infty : chartS (∞ : RiemannSphere) = 0 := rfl
@[simp] lemma chartS_symm_zero : chartS.symm 0 = ∞ := by
  show chartS_inv 0 = ∞
  exact chartS_inv_zero
lemma chartS_symm_apply_of_ne {z : ℂ} (hz : z ≠ 0) :
    chartS.symm z = ((z⁻¹ : ℂ) : RiemannSphere) := chartS_inv_of_ne hz
@[simp] lemma chartS_source :
    chartS.source = {x : RiemannSphere | x ≠ ((0 : ℂ) : RiemannSphere)} := rfl
@[simp] lemma chartS_target : chartS.target = Set.univ := rfl

/-! ## `ChartedSpace ℂ` instance: each point gets the chart that contains it -/

/-- Pick the appropriate chart at `x ∈ RiemannSphere`: `chartN` if `x ≠ ∞`,
otherwise `chartS` (`x = ∞ ⇒ x ≠ some 0`). -/
def chartAtFun (x : RiemannSphere) : OpenPartialHomeomorph RiemannSphere ℂ :=
  if x = ∞ then chartS else chartN

instance : ChartedSpace ℂ RiemannSphere where
  atlas := {chartN, chartS}
  chartAt := chartAtFun
  mem_chart_source x := by
    by_cases hx : x = ∞
    · -- chartS source: `x ≠ some 0`. `x = ∞ ≠ some 0`.
      simp [chartAtFun, hx, chartS]
      show (∞ : RiemannSphere) ≠ ((0 : ℂ) : RiemannSphere)
      exact OnePoint.infty_ne_coe (0 : ℂ)
    · -- chartN source: `x ≠ ∞`. By assumption.
      simp [chartAtFun, hx, chartN]
      exact hx
  chart_mem_atlas x := by
    by_cases hx : x = ∞ <;> simp [chartAtFun, hx]

/-! ## Analytic compatibility of the four atlas-pair transitions

This is the input `IsManifold 𝓘(ℂ) ω RiemannSphere` would need; a follow-up
file should consume `riemannSphere_compatible` to build that instance. -/

/-- The transition map `z ↦ z⁻¹` is analytic (`C^ω`) on `{z : ℂ | z ≠ 0}`. -/
private lemma analyticOn_inv_compl_zero :
    AnalyticOnNhd ℂ (fun z : ℂ => z⁻¹) {z : ℂ | z ≠ 0} := by
  intro z hz
  exact (analyticAt_id (𝕜 := ℂ) (x := z)).inv hz

/-- The transition `chartN.symm ≫ chartS` is `z ↦ z⁻¹`, analytic on its
source `{z : ℂ | z ≠ 0}`. -/
private lemma contDiffOn_chartN_chartS :
    ContDiffOn ℂ ω (fun z : ℂ => z⁻¹) {z : ℂ | z ≠ 0} :=
  analyticOn_inv_compl_zero.contDiffOn

/-- All four transition maps among the two-chart atlas of the Riemann sphere
are analytic. This is the analytic-manifold hypothesis fed to
`isManifold_of_contDiffOn`. -/
private lemma riemannSphere_compatible :
    ∀ (e e' : OpenPartialHomeomorph RiemannSphere ℂ),
      e ∈ atlas ℂ RiemannSphere → e' ∈ atlas ℂ RiemannSphere →
        ContDiffOn ℂ ω
          ((𝓘(ℂ) : ModelWithCorners ℂ ℂ ℂ) ∘ e.symm ≫ₕ e' ∘ (𝓘(ℂ)).symm)
          ((𝓘(ℂ)).symm ⁻¹' (e.symm ≫ₕ e').source ∩ Set.range (𝓘(ℂ))) := by
  -- For `I = 𝓘(ℂ)`, both `I` and `I.symm` are `id`, and `range I = univ`.
  -- Goal reduces to `ContDiffOn ℂ ω (e' ∘ e.symm) (e.symm ≫ₕ e').source`.
  intro e e' he he'
  -- Unfold the atlas: each of `e, e'` is `chartN` or `chartS`.
  have he2 : e = chartN ∨ e = chartS := by
    rcases he with h | h
    · exact Or.inl h
    · exact Or.inr (Set.mem_singleton_iff.mp h)
  have he'2 : e' = chartN ∨ e' = chartS := by
    rcases he' with h | h
    · exact Or.inl h
    · exact Or.inr (Set.mem_singleton_iff.mp h)
  -- The model is trivial: `I = id`, `I.symm = id`.
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.preimage_id, Set.range_id, Set.inter_univ]
  rcases he2 with rfl | rfl <;> rcases he'2 with rfl | rfl
  · -- chartN.symm ≫ chartN: identity-on-univ-style.
    -- The composite is `(z ↦ z) = id` on its source = `{x | x ≠ ∞} → ℂ → univ`.
    -- More concretely, source = chartN.target ∩ chartN.symm⁻¹'(chartN.source) = univ.
    have hsrc : (chartN.symm ≫ₕ chartN).source = Set.univ := by
      rw [OpenPartialHomeomorph.trans_source]
      simp [chartN, chartN_partialEquiv]
      ext z
      constructor
      · intro _; trivial
      · intro _
        refine ⟨trivial, ?_⟩
        -- `(z : RiemannSphere) ≠ ∞` automatic.
        exact OnePoint.coe_ne_infty z
    rw [hsrc]
    -- The composite is `id` on univ.
    have heq : Set.EqOn (chartN ∘ chartN.symm) id (Set.univ : Set ℂ) := by
      intro z _
      show chartN ((z : RiemannSphere)) = z
      rfl
    exact (contDiff_id.contDiffOn).congr heq
  · -- chartN.symm ≫ chartS: `z ↦ chartS (some z) = z⁻¹` on source = `{z | z ≠ 0}`.
    have hsrc : (chartN.symm ≫ₕ chartS).source = {z : ℂ | z ≠ 0} := by
      rw [OpenPartialHomeomorph.trans_source]
      ext z
      simp only [chartN, chartN_partialEquiv, chartS, chartS_partialEquiv,
        OpenPartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_source,
        Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq,
        OpenPartialHomeomorph.mk_coe, PartialEquiv.coe_mk, ne_eq]
      -- Goal: `(z ∈ univ) ∧ ((z : RiemannSphere) ≠ some 0) ↔ z ≠ 0`.
      constructor
      · rintro ⟨_, h⟩ hz
        apply h
        rw [hz]
      · intro hz
        refine ⟨trivial, ?_⟩
        intro hcoe
        exact hz (OnePoint.coe_injective hcoe)
    rw [hsrc]
    have heq : Set.EqOn (chartS ∘ chartN.symm) (fun z : ℂ => z⁻¹) {z : ℂ | z ≠ 0} := by
      intro z _; rfl
    exact contDiffOn_chartN_chartS.congr heq
  · -- chartS.symm ≫ chartN: `z ↦ chartN (chartS_inv z) = z⁻¹` on `{z | z ≠ 0}`.
    have hsrc : (chartS.symm ≫ₕ chartN).source = {z : ℂ | z ≠ 0} := by
      rw [OpenPartialHomeomorph.trans_source]
      ext z
      simp only [chartS, chartS_partialEquiv, chartN, chartN_partialEquiv,
        OpenPartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_source,
        Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq,
        OpenPartialHomeomorph.mk_coe, PartialEquiv.coe_mk, ne_eq]
      -- Goal: `(z ∈ univ) ∧ chartS_inv z ≠ ∞ ↔ z ≠ 0`.
      constructor
      · rintro ⟨_, h⟩ hz
        apply h
        subst hz
        exact chartS_inv_zero
      · intro hz
        refine ⟨trivial, ?_⟩
        rw [chartS_inv_of_ne hz]
        exact OnePoint.coe_ne_infty (z⁻¹)
    rw [hsrc]
    have heq : Set.EqOn (chartN ∘ chartS.symm) (fun z : ℂ => z⁻¹) {z : ℂ | z ≠ 0} := by
      intro z hz
      show chartN (chartS_inv z) = z⁻¹
      rw [chartS_inv_of_ne hz]
      rfl
    exact contDiffOn_chartN_chartS.congr heq
  · -- chartS.symm ≫ chartS: source is `univ` (because `chartS_inv z ≠ some 0`
    -- holds for ALL z: at z=0 we have `chartS_inv 0 = ∞ ≠ some 0`; at z≠0 we
    -- have `chartS_inv z = some z⁻¹` and `z⁻¹ ≠ 0`). The composite is `id`.
    have hsrc : (chartS.symm ≫ₕ chartS).source = (Set.univ : Set ℂ) := by
      rw [OpenPartialHomeomorph.trans_source]
      ext z
      simp only [chartS, chartS_partialEquiv,
        OpenPartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_source,
        Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq,
        OpenPartialHomeomorph.mk_coe, PartialEquiv.coe_mk, ne_eq, Set.mem_univ,
        true_and, iff_true]
      -- Goal: `chartS_inv z ≠ some 0` for all `z`.
      by_cases hz : z = 0
      · subst hz
        rw [chartS_inv_zero]
        exact OnePoint.infty_ne_coe (0 : ℂ)
      · rw [chartS_inv_of_ne hz]
        intro hcoe
        exact (inv_ne_zero hz) (OnePoint.coe_injective hcoe)
    rw [hsrc]
    -- Composite is `id`: at z=0, `chartS(chartS_inv 0) = chartS ∞ = 0`.
    -- At z≠0, `chartS(chartS_inv z) = chartS(some z⁻¹) = (z⁻¹)⁻¹ = z`.
    have heq : Set.EqOn (chartS ∘ chartS.symm) id (Set.univ : Set ℂ) := by
      intro z _
      show chartS (chartS_inv z) = z
      by_cases hz : z = 0
      · subst hz
        rw [chartS_inv_zero]
        rfl
      · rw [chartS_inv_of_ne hz]
        show ((((z⁻¹ : ℂ) : RiemannSphere)).elim (0 : ℂ) (fun w : ℂ => w⁻¹)) = z
        change (z⁻¹ : ℂ)⁻¹ = z
        rw [inv_inv]
    exact (contDiff_id.contDiffOn).congr heq

end RiemannSphere
end JacobianChallenge
end
