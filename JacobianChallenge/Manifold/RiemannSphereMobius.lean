/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphere

set_option diagnostics.threshold 100

/-! # A concrete Möbius self-map of the Riemann sphere

We define the antipodal Möbius transformation `antipode : RiemannSphere → RiemannSphere`
which sends `z ↦ -1/z` (with the convention `(some 0) ↔ ∞`) and prove it is
continuous. This exercises the chart machinery from `RiemannSphere.lean`
(`chartN`, `chartS`, the `ChartedSpace ℂ` instance) on a worked example of a
self-homeomorphism of a Riemann surface.

## Setup

`antipode` is defined by an `OnePoint.rec` case split:
* `antipode ∞ = (some 0)`
* `antipode (some 0) = ∞`
* `antipode (some z) = some (-z⁻¹)` for `z ≠ 0`

(The latter two are unified by the formula `if z = 0 then ∞ else some (-z⁻¹)`
on the `coe` branch.)

## Chart-coordinate formulas (informal — used to motivate the smoothness
extension; see the doc-comment of `contMDiff_antipode_TODO` below)

Reading `antipode` through pairs of charts:
* `chartN ∘ antipode ∘ chartN.symm = z ↦ -z⁻¹` on `{z ≠ 0}`
* `chartN ∘ antipode ∘ chartS.symm = z ↦ -z` on all of `ℂ`
* `chartS ∘ antipode ∘ chartN.symm = z ↦ -z` on all of `ℂ`
* `chartS ∘ antipode ∘ chartS.symm = z ↦ -z⁻¹` on `{z ≠ 0}`

`z ↦ -z` is entire and `z ↦ -z⁻¹` is analytic on `{z ≠ 0}` — both upgrade to
`ContDiffOn ℂ ω` via `AnalyticOnNhd.contDiffOn_of_completeSpace`. The
`ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω antipode` statement is left as a follow-up; the
continuity proof in this file already handles the three-way `OnePoint.rec`
case split that the smoothness proof needs.

## What ships

* `RiemannSphere.antipode : RiemannSphere → RiemannSphere`
* `RiemannSphere.antipode_infty`, `antipode_coe_zero`, `antipode_coe_of_ne` —
  the three defining equations.
* `RiemannSphere.continuous_antipode : Continuous antipode` -/

open OnePoint Set Topology
open scoped Manifold

namespace JacobianChallenge

namespace RiemannSphere

/-! ### Definition and basic properties of the antipode -/

/-- The antipodal Möbius transformation `z ↦ -1/z` on the Riemann sphere.
On charts: swaps `(some 0) ↔ ∞` and sends `(some z)` to `some (-z⁻¹)` for
`z ≠ 0`. Geometrically this is the antipodal map under the standard
identification of the Riemann sphere with the unit `2`-sphere in `ℝ³`. -/
noncomputable def antipode : RiemannSphere → RiemannSphere :=
  fun x => OnePoint.rec ((0 : ℂ) : RiemannSphere)
    (fun z => if z = 0 then (∞ : RiemannSphere)
              else (((-z⁻¹) : ℂ) : RiemannSphere)) x

@[simp] lemma antipode_infty : antipode (∞ : RiemannSphere) = ((0 : ℂ) : RiemannSphere) := rfl

@[simp] lemma antipode_coe_zero :
    antipode (((0 : ℂ) : RiemannSphere)) = (∞ : RiemannSphere) := by
  show (if (0 : ℂ) = 0 then (∞ : RiemannSphere) else (((-(0:ℂ)⁻¹) : ℂ) : RiemannSphere))
    = (∞ : RiemannSphere)
  simp

lemma antipode_coe_of_ne {z : ℂ} (hz : z ≠ 0) :
    antipode ((z : RiemannSphere)) = (((-z⁻¹) : ℂ) : RiemannSphere) := by
  show (if z = 0 then (∞ : RiemannSphere) else (((-z⁻¹) : ℂ) : RiemannSphere))
    = (((-z⁻¹) : ℂ) : RiemannSphere)
  simp [hz]

/-- `antipode` is an involution: applying it twice gives the identity. -/
lemma antipode_antipode (x : RiemannSphere) : antipode (antipode x) = x := by
  induction x using OnePoint.rec with
  | infty => rw [antipode_infty, antipode_coe_zero]
  | coe w =>
    by_cases hw : w = 0
    · subst hw; rw [antipode_coe_zero, antipode_infty]
    · have hwinv : -w⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hw)
      rw [antipode_coe_of_ne hw, antipode_coe_of_ne hwinv]
      congr 1
      rw [inv_neg, inv_inv, neg_neg]

/-! ### Continuity of `antipode`

We split into three cases on `x` (`∞`, `(some 0)`, `(some w)` with `w ≠ 0`).
The `∞` and `(some 0)` cases use the swap-of-the-pole structure, and the
generic finite case reduces to continuity of `(↑) ∘ Neg.neg ∘ Inv.inv` on
`{z ≠ 0}`. -/

lemma continuous_antipode : Continuous antipode := by
  rw [continuous_iff_continuousAt]
  intro x
  induction x using OnePoint.rec with
  | infty =>
    -- `antipode ∞ = some 0`. We show `Tendsto antipode (𝓝 ∞) (𝓝 (some 0))`.
    rw [ContinuousAt, antipode_infty, OnePoint.nhds_infty_eq, Filter.tendsto_sup]
    refine ⟨?_, ?_⟩
    · -- Image of `map ↑ (coclosedCompact ℂ)`. Compose with antipode and rewrite
      -- `antipode ∘ ↑` to `↑ ∘ (-·⁻¹)` on the cofinal set `{z ≠ 0}`.
      rw [Filter.tendsto_map'_iff]
      have h_inv_cocomp : Filter.Tendsto (fun w : ℂ => w⁻¹)
          (Filter.cocompact ℂ) (𝓝 (0 : ℂ)) := by
        rw [← Metric.cobounded_eq_cocompact]
        exact Filter.tendsto_inv₀_cobounded
      have h_inv : Filter.Tendsto (fun w : ℂ => w⁻¹)
          (Filter.coclosedCompact ℂ) (𝓝 (0 : ℂ)) :=
        h_inv_cocomp.mono_left Filter.cocompact_le_coclosedCompact
      have h_neg_inv : Filter.Tendsto (fun w : ℂ => -w⁻¹)
          (Filter.coclosedCompact ℂ) (𝓝 (0 : ℂ)) := by
        simpa using h_inv.neg
      have h_to_sphere :=
        (OnePoint.continuous_coe (X := ℂ)).continuousAt.tendsto.comp h_neg_inv
      refine Filter.Tendsto.congr' ?_ h_to_sphere
      have hmem : {z : ℂ | z ≠ 0} ∈ Filter.coclosedCompact ℂ := by
        rw [Filter.mem_coclosedCompact]
        refine ⟨{(0 : ℂ)}, isClosed_singleton, isCompact_singleton, ?_⟩
        intro z hz; simp at hz; exact hz
      filter_upwards [hmem] with z hz
      exact (antipode_coe_of_ne hz).symm
    · have h := Filter.tendsto_pure_pure antipode (∞ : RiemannSphere)
      rw [antipode_infty] at h
      exact h.mono_right (pure_le_nhds _)
  | coe w =>
    by_cases hw : w = 0
    · -- `antipode (some 0) = ∞`. Show `Tendsto antipode (𝓝 (some 0)) (𝓝 ∞)`.
      subst hw
      rw [ContinuousAt, antipode_coe_zero]
      have h_open : (𝓝 ((0 : ℂ) : RiemannSphere))
          = Filter.map ((↑) : ℂ → RiemannSphere) (𝓝 (0 : ℂ)) :=
        ((OnePoint.isOpenEmbedding_coe (X := ℂ)).map_nhds_eq 0).symm
      rw [h_open, Filter.tendsto_map'_iff,
        show (𝓝 (0 : ℂ)) = 𝓝[≠] (0 : ℂ) ⊔ pure 0 from
          (nhdsNE_sup_pure (0 : ℂ)).symm,
        Filter.tendsto_sup]
      refine ⟨?_, ?_⟩
      · rw [OnePoint.nhds_infty_eq]
        -- Replace `antipode (some z)` with `(-z⁻¹ : ℂ) : RiemannSphere` on 𝓝[≠] 0,
        -- then compose with `(↑) : ℂ → RiemannSphere` and the divergence statement
        -- `Tendsto (-·⁻¹) (𝓝[≠] 0) (cobounded ℂ)`, which holds because
        -- `‖-z⁻¹‖ = ‖z⁻¹‖ → ∞`.
        have hcongr : (fun z : ℂ => antipode ((z : RiemannSphere)))
            =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => (((-z⁻¹) : ℂ) : RiemannSphere)) := by
          refine Filter.eventually_of_mem
            (self_mem_nhdsWithin (a := (0 : ℂ)) (s := {(0 : ℂ)}ᶜ)) ?_
          intro z hz; exact antipode_coe_of_ne hz
        refine Filter.Tendsto.congr' hcongr.symm ?_
        apply Filter.Tendsto.mono_right _ le_sup_left
        -- We use that on `𝓝[≠] 0`, `-z⁻¹` and `z⁻¹` agree up to negation, which
        -- is an isometry in `ℂ` and hence preserves the cocompact filter via a
        -- direct preimage-of-compact argument.
        have h_inv_cocomp : Filter.Tendsto (fun z : ℂ => z⁻¹) (𝓝[≠] (0 : ℂ))
            (Filter.cocompact ℂ) := by
          rw [← Metric.cobounded_eq_cocompact]
          exact Filter.tendsto_inv₀_nhdsNE_zero
        -- Negation preserves cocompact: since `(- ·)` is continuous, the preimage
        -- of any compact set is compact (`-K` itself), so `(- ·)⁻¹ Kᶜ = (-K)ᶜ`
        -- belongs to the cocompact filter.
        have h_neg_cocomp :
            Filter.Tendsto (fun w : ℂ => -w) (Filter.cocompact ℂ) (Filter.cocompact ℂ) := by
          intro s hs
          rw [Filter.mem_cocompact] at hs ⊢
          rcases hs with ⟨t, ht_compact, ht_sub⟩
          refine ⟨((- ·) ⁻¹' t : Set ℂ), ?_, ?_⟩
          · -- `(- ·)⁻¹ t` is compact since `(- ·)` is continuous and the preimage of a
            -- compact set under a homeomorphism is compact. Use the homeomorphism
            -- property via `IsCompact.image (continuous_neg)`.
            have : ((- ·) ⁻¹' t : Set ℂ) = (- ·) '' t := by
              ext z
              constructor
              · intro hz
                refine ⟨-z, hz, by ring⟩
              · rintro ⟨y, hy, rfl⟩
                show -(-y) ∈ t
                rwa [neg_neg]
            rw [this]
            exact ht_compact.image continuous_neg
          · intro z hz
            apply ht_sub
            simp only [Set.mem_preimage] at hz
            exact hz
        have h_neg_inv_cocomp : Filter.Tendsto (fun z : ℂ => -z⁻¹) (𝓝[≠] (0 : ℂ))
            (Filter.cocompact ℂ) := h_neg_cocomp.comp h_inv_cocomp
        have h_to_cocomp : Filter.Tendsto (fun z : ℂ => -z⁻¹) (𝓝[≠] (0 : ℂ))
            (Filter.coclosedCompact ℂ) :=
          h_neg_inv_cocomp.mono_right Filter.cocompact_le_coclosedCompact
        exact (Filter.tendsto_map (m := (↑) : ℂ → RiemannSphere)
          (f := Filter.coclosedCompact ℂ)).comp h_to_cocomp
      · have h := Filter.tendsto_pure_pure
          (fun z : ℂ => antipode ((z : RiemannSphere))) (0 : ℂ)
        simp only [antipode_coe_zero] at h
        exact h.mono_right (pure_le_nhds _)
    · -- `antipode (some w) = some (-w⁻¹)`, `w ≠ 0`.
      rw [ContinuousAt]
      rw [(OnePoint.isOpenEmbedding_coe (X := ℂ)).map_nhds_eq w |>.symm,
        Filter.tendsto_map'_iff, antipode_coe_of_ne hw]
      have hloc : (antipode : RiemannSphere → RiemannSphere) ∘ ((↑) : ℂ → RiemannSphere)
          =ᶠ[𝓝 w] (fun z => (((-z⁻¹) : ℂ) : RiemannSphere)) := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hw] with z hz
        exact antipode_coe_of_ne hz
      refine Filter.Tendsto.congr' hloc.symm ?_
      exact (OnePoint.continuous_coe (X := ℂ)).continuousAt.tendsto.comp
        ((continuousAt_inv₀ hw).neg)

end RiemannSphere

end JacobianChallenge
