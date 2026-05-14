/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphereAntipodeSmooth

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! # Translation Möbius maps on the Riemann sphere

For each `a : ℂ`, the affine map `z ↦ z + a` on `ℂ` extends to a
biholomorphism of `RiemannSphere` fixing `∞`. This file provides:

* `RiemannSphere.translateBy (a : ℂ) : RiemannSphere → RiemannSphere`
  — the function `coe z ↦ coe (z + a)`, `∞ ↦ ∞`.
* `RiemannSphere.continuous_translateBy` — continuity.
* `RiemannSphere.contMDiff_translateBy` — `C^ω` smoothness.
* `RiemannSphere.translateEquiv (a : ℂ) :
    HolomorphicEquiv RiemannSphere RiemannSphere` — the packaged
  biholomorphism, with inverse `translateBy (-a)`.

## Strategy

Chart calculations under the canonical chart selection (`chartN` for
finite, `chartS` for `∞`):

| `x`               | source chart | target chart | local map           |
|-------------------|--------------|--------------|---------------------|
| `(z₀ : ℂ : RS)`   | `chartN`     | `chartN`     | `z ↦ z + a`         |
| `∞`               | `chartS`     | `chartS`     | `z ↦ z / (1 + a·z)` |

The local map at `∞` is `(z⁻¹ + a)⁻¹` on `z ≠ 0`, which simplifies to
`z / (1 + a·z)` on the open neighborhood `{z | 1 + a·z ≠ 0}` of `0`
(using Lean's `0⁻¹ = 0` for the boundary case). Both local maps are
analytic at the point `(chartAt x) x`.

For the `∞`-side continuity, the shift `· + a : ℂ → ℂ` is a
homeomorphism, so it sends cocompact to cocompact, and `OnePoint`'s
neighborhood basis of `∞` transports cleanly through it.

No `sorry`, no `axiom`. -/

open OnePoint Set Topology Filter Bornology
open scoped Manifold ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-! ### Definition and defining equations -/

/-- The translation Möbius map `z ↦ z + a` on the Riemann sphere
(fixing `∞`). -/
def translateBy (a : ℂ) : RiemannSphere → RiemannSphere :=
  fun x => OnePoint.rec (∞ : RiemannSphere)
    (fun z => (((z + a) : ℂ) : RiemannSphere)) x

@[simp] lemma translateBy_infty (a : ℂ) :
    translateBy a (∞ : RiemannSphere) = (∞ : RiemannSphere) := rfl

@[simp] lemma translateBy_coe (a z : ℂ) :
    translateBy a ((z : RiemannSphere)) = (((z + a) : ℂ) : RiemannSphere) := rfl

/-- `translateBy 0` is the identity. -/
@[simp] lemma translateBy_zero (x : RiemannSphere) :
    translateBy 0 x = x := by
  induction x using OnePoint.rec with
  | infty => rfl
  | coe z => show (((z + 0) : ℂ) : RiemannSphere) = ((z : ℂ) : RiemannSphere)
             simp

/-- Composition: `translateBy a ∘ translateBy b = translateBy (a + b)`. -/
lemma translateBy_translateBy (a b : ℂ) (x : RiemannSphere) :
    translateBy a (translateBy b x) = translateBy (a + b) x := by
  induction x using OnePoint.rec with
  | infty => simp
  | coe z =>
    show (((z + b + a) : ℂ) : RiemannSphere)
        = (((z + (a + b)) : ℂ) : RiemannSphere)
    congr 1; ring

/-- `translateBy a` is a left inverse of `translateBy (-a)`. -/
lemma translateBy_translateBy_neg (a : ℂ) (x : RiemannSphere) :
    translateBy a (translateBy (-a) x) = x := by
  rw [translateBy_translateBy]; simp

/-- `translateBy (-a)` is a left inverse of `translateBy a`. -/
lemma translateBy_neg_translateBy (a : ℂ) (x : RiemannSphere) :
    translateBy (-a) (translateBy a x) = x := by
  rw [translateBy_translateBy]; simp

/-! ### Continuity of `translateBy` -/

/-- The shift `· + a : ℂ → ℂ` sends `cocompact ℂ` into `cocompact ℂ`.
This is the key cocompact-transport used in the `∞`-side continuity
calculation. -/
lemma tendsto_add_cocompact (a : ℂ) :
    Filter.Tendsto (fun z : ℂ => z + a) (Filter.cocompact ℂ)
      (Filter.cocompact ℂ) := by
  intro s hs
  rw [Filter.mem_cocompact] at hs
  obtain ⟨K, hK, hKs⟩ := hs
  rw [Filter.mem_map, Filter.mem_cocompact]
  refine ⟨(fun z : ℂ => z + a) ⁻¹' K, ?_, ?_⟩
  · -- Preimage of compact under continuous = closed of compact + … here
    -- `· + a` is a homeomorphism, so preimage of compact is compact.
    have h_cont : Continuous (fun z : ℂ => z - a) := continuous_id.sub continuous_const
    have h_eq : (fun z : ℂ => z + a) ⁻¹' K = (fun z : ℂ => z - a) '' K := by
      ext z; constructor
      · intro hz
        refine ⟨z + a, hz, ?_⟩; ring
      · rintro ⟨k, hk, rfl⟩
        show k - a + a ∈ K
        have : k - a + a = k := by ring
        rw [this]; exact hk
    rw [h_eq]
    exact hK.image h_cont
  · intro z hz
    -- z ∉ preimage K means z + a ∉ K, i.e., z + a ∈ Kᶜ ⊆ s.
    show z + a ∈ s
    exact hKs hz

/-- `translateBy a` is continuous. -/
lemma continuous_translateBy (a : ℂ) : Continuous (translateBy a) := by
  rw [continuous_iff_continuousAt]
  intro x
  induction x using OnePoint.rec with
  | infty =>
    -- translateBy a ∞ = ∞. Show Tendsto on 𝓝 ∞.
    rw [ContinuousAt, translateBy_infty, OnePoint.nhds_infty_eq,
      Filter.tendsto_sup]
    refine ⟨?_, ?_⟩
    · -- cocompact branch
      rw [Filter.tendsto_map'_iff]
      simp only [Filter.coclosedCompact_eq_cocompact]
      -- target is `map coe cocompact ⊔ pure ∞`; we land in the `map coe` side
      apply Filter.Tendsto.mono_right _ le_sup_left
      -- `translateBy a ∘ coe = coe ∘ (· + a)`, then push cocompact ↦ cocompact.
      have h_eq : (translateBy a ∘ ((↑) : ℂ → RiemannSphere))
          = ((↑) : ℂ → RiemannSphere) ∘ (fun z => z + a) := by
        funext z; simp
      rw [h_eq]
      have h_shift := tendsto_add_cocompact a
      have h_map : Filter.Tendsto ((↑) : ℂ → RiemannSphere)
          (Filter.cocompact ℂ)
          (Filter.map ((↑) : ℂ → RiemannSphere) (Filter.cocompact ℂ)) :=
        Filter.tendsto_map
      exact h_map.comp h_shift
    · -- pure ∞ branch: target is the sup, so use `le_sup_right` directly.
      have h := Filter.tendsto_pure_pure (translateBy a) (∞ : RiemannSphere)
      rw [translateBy_infty] at h
      exact h.mono_right le_sup_right
  | coe z =>
    -- `translateBy a (coe z) = coe (z + a)`. Local pattern: `coe ∘ (· + a)` at z.
    rw [ContinuousAt, translateBy_coe]
    -- Open embedding of coe gives `𝓝 (coe z) = map coe (𝓝 z)`.
    have h_open_eq : 𝓝 ((z : ℂ) : RiemannSphere)
        = Filter.map ((↑) : ℂ → RiemannSphere) (𝓝 z) :=
      ((OnePoint.isOpenEmbedding_coe (X := ℂ)).map_nhds_eq z).symm
    rw [h_open_eq, Filter.tendsto_map'_iff]
    have h_loc : (translateBy a) ∘ ((↑) : ℂ → RiemannSphere)
        = ((↑) : ℂ → RiemannSphere) ∘ (fun w => w + a) := by
      funext w; simp
    rw [h_loc]
    have h_add : Filter.Tendsto (fun w : ℂ => w + a) (𝓝 z) (𝓝 (z + a)) :=
      (continuous_id.add continuous_const).tendsto z
    have h_coe : Filter.Tendsto ((↑) : ℂ → RiemannSphere) (𝓝 (z + a))
        (𝓝 (((z + a : ℂ) : RiemannSphere))) :=
      (OnePoint.continuous_coe (X := ℂ)).tendsto (z + a)
    exact h_coe.comp h_add

/-! ### Chart-pullback formulas for `translateBy`

Two pointwise identities describe the local form of `translateBy` in
the two chart pairings relevant to its smoothness proof. -/

/-- Local copy of `chartAt ℂ (coe z) = chartN`. -/
private lemma chartAt_coe' (z : ℂ) :
    (chartAt ℂ ((z : RiemannSphere))) = chartN := by
  show chartAt' ((z : RiemannSphere)) = chartN
  exact chartAt'_coe z

/-- Local copy of `chartAt ℂ ∞ = chartS`. -/
private lemma chartAt_infty' :
    (chartAt ℂ (∞ : RiemannSphere)) = chartS := by
  show chartAt' (∞ : RiemannSphere) = chartS
  exact chartAt'_infty

/-- `chartN ∘ translateBy a ∘ chartN.symm = (· + a)` pointwise. -/
lemma chartN_translateBy_chartN_symm (a z : ℂ) :
    chartN (translateBy a (chartN.symm z)) = z + a := by
  rw [chartN_symm_apply, translateBy_coe, chartN_apply_coe]

/-- `chartS ∘ translateBy a ∘ chartS.symm` agrees with `z ↦ z / (1 + a·z)`
on the open neighborhood `{z | 1 + a·z ≠ 0}` of `0`. -/
lemma chartS_translateBy_chartS_symm {a z : ℂ} (hz : 1 + a * z ≠ 0) :
    chartS (translateBy a (chartS.symm z)) = z / (1 + a * z) := by
  by_cases hz0 : z = 0
  · subst hz0
    rw [chartS_symm_apply_zero, translateBy_infty, chartS_apply_infty]
    simp
  · rw [chartS_symm_apply_of_ne hz0, translateBy_coe, chartS_apply_coe]
    -- (z⁻¹ + a)⁻¹ = z / (1 + a·z) under z ≠ 0 and 1 + a*z ≠ 0.
    have h_rewrite : z⁻¹ + a = (1 + a * z) / z := by field_simp
    rw [h_rewrite, inv_div]

/-! ### Smoothness of `translateBy` -/

/-- The translation `translateBy a` is `C^ω` as a self-map of the
Riemann sphere. -/
theorem contMDiff_translateBy (a : ℂ) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (translateBy a) := by
  intro x
  have hx_source : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hax_source : translateBy a x ∈ (chartAt ℂ (translateBy a x)).source :=
    mem_chart_source ℂ (translateBy a x)
  rw [contMDiffAt_iff_of_mem_source hx_source hax_source]
  have h_range : Set.range (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ) = Set.univ :=
    ModelWithCorners.range_eq_univ _
  rw [h_range, contDiffWithinAt_univ]
  refine ⟨(continuous_translateBy a).continuousAt, ?_⟩
  induction x using OnePoint.rec with
  | infty =>
    -- chartAt ∞ = chartS; chartAt (T_a ∞) = chartAt ∞ = chartS.
    -- Local form: `chartS ∘ T_a ∘ chartS.symm = z/(1+a·z)`, analytic at 0.
    have h_chart_x : chartAt ℂ (∞ : RiemannSphere) = chartS := chartAt_infty'
    have h_chart_ax : chartAt ℂ (translateBy a (∞ : RiemannSphere)) = chartS := by
      rw [translateBy_infty]; exact chartAt_infty'
    have h_pt : (extChartAt 𝓘(ℂ, ℂ) (∞ : RiemannSphere)) (∞ : RiemannSphere)
        = (0 : ℂ) := by
      simp [extChartAt, OpenPartialHomeomorph.extend, h_chart_x, chartS_apply_infty]
    rw [h_pt]
    -- `z ↦ z/(1+a·z)` is analytic at 0 (since 1 + a·0 = 1 ≠ 0).
    have h_one_ne : (1 : ℂ) + a * 0 ≠ 0 := by simp
    have h_den : AnalyticAt ℂ (fun z : ℂ => 1 + a * z) 0 :=
      analyticAt_const.add (analyticAt_const.mul analyticAt_id)
    have h_num : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
    have h_an : AnalyticAt ℂ (fun z : ℂ => z / (1 + a * z)) 0 := by
      have h_den_val : (fun z : ℂ => 1 + a * z) 0 ≠ 0 := by simp
      exact h_num.div h_den h_den_val
    have h_cd : ContDiffAt ℂ (ω : WithTop ℕ∞) (fun z : ℂ => z / (1 + a * z)) 0 :=
      h_an.contDiffAt
    refine h_cd.congr_of_eventuallyEq ?_
    -- Eventually equality on the open nbhd `{z | 1 + a·z ≠ 0}` of 0.
    have h_open : IsOpen {z : ℂ | 1 + a * z ≠ 0} := by
      refine IsOpen.preimage ?_ (T1Space.t1 (0 : ℂ)).isOpen_compl
      exact continuous_const.add (continuous_const.mul continuous_id)
    have h_mem : (0 : ℂ) ∈ {z : ℂ | 1 + a * z ≠ 0} := by
      show (1 : ℂ) + a * 0 ≠ 0; simp
    refine Filter.eventually_of_mem (h_open.mem_nhds h_mem) (fun z hz => ?_)
    show (extChartAt 𝓘(ℂ, ℂ) (translateBy a (∞ : RiemannSphere)))
            (translateBy a ((extChartAt 𝓘(ℂ, ℂ) (∞ : RiemannSphere)).symm z))
        = z / (1 + a * z)
    have h_symm : (extChartAt 𝓘(ℂ, ℂ) (∞ : RiemannSphere)).symm z
        = chartS.symm z := by
      simp [extChartAt, OpenPartialHomeomorph.extend, h_chart_x]
    have h_apply : (extChartAt 𝓘(ℂ, ℂ) (translateBy a (∞ : RiemannSphere)))
            (translateBy a (chartS.symm z))
        = chartS (translateBy a (chartS.symm z)) := by
      simp [extChartAt, OpenPartialHomeomorph.extend, h_chart_ax]
    rw [h_symm, h_apply]
    exact chartS_translateBy_chartS_symm hz
  | coe z₀ =>
    -- chartAt (coe z₀) = chartN; chartAt (T_a (coe z₀)) = chartAt (coe (z₀+a)) = chartN.
    -- Local form: `chartN ∘ T_a ∘ chartN.symm = (·+a)`, entire.
    have h_chart_x : chartAt ℂ ((z₀ : RiemannSphere)) = chartN := chartAt_coe' z₀
    have h_chart_ax : chartAt ℂ (translateBy a ((z₀ : RiemannSphere))) = chartN := by
      rw [translateBy_coe]; exact chartAt_coe' (z₀ + a)
    have h_pt : (extChartAt 𝓘(ℂ, ℂ) ((z₀ : RiemannSphere))) ((z₀ : RiemannSphere))
        = z₀ := by
      simp [extChartAt, OpenPartialHomeomorph.extend, h_chart_x, chartN_apply_coe]
    rw [h_pt]
    have h_cd : ContDiffAt ℂ (ω : WithTop ℕ∞) (fun z : ℂ => z + a) z₀ :=
      contDiffAt_id.add contDiffAt_const
    refine h_cd.congr_of_eventuallyEq ?_
    refine Filter.Eventually.of_forall (fun z => ?_)
    show (extChartAt 𝓘(ℂ, ℂ) (translateBy a ((z₀ : RiemannSphere))))
            (translateBy a ((extChartAt 𝓘(ℂ, ℂ) ((z₀ : RiemannSphere))).symm z))
        = z + a
    have h_symm : (extChartAt 𝓘(ℂ, ℂ) ((z₀ : RiemannSphere))).symm z
        = chartN.symm z := by
      simp [extChartAt, OpenPartialHomeomorph.extend, h_chart_x]
    have h_apply : (extChartAt 𝓘(ℂ, ℂ) (translateBy a ((z₀ : RiemannSphere))))
            (translateBy a (chartN.symm z))
        = chartN (translateBy a (chartN.symm z)) := by
      simp [extChartAt, OpenPartialHomeomorph.extend, h_chart_ax]
    rw [h_symm, h_apply, chartN_translateBy_chartN_symm]

/-! ### Packaging as a `HolomorphicEquiv` -/

/-- The set-level translation equiv. -/
noncomputable def translateEquiv' (a : ℂ) : RiemannSphere ≃ RiemannSphere where
  toFun := translateBy a
  invFun := translateBy (-a)
  left_inv := translateBy_neg_translateBy a
  right_inv := translateBy_translateBy_neg a

@[simp] lemma translateEquiv'_apply (a : ℂ) (x : RiemannSphere) :
    translateEquiv' a x = translateBy a x := rfl

@[simp] lemma translateEquiv'_symm_apply (a : ℂ) (x : RiemannSphere) :
    (translateEquiv' a).symm x = translateBy (-a) x := rfl

/-- The translation Möbius transformation as a biholomorphism of the
Riemann sphere. -/
noncomputable def translateEquiv (a : ℂ) :
    JacobianChallenge.HolomorphicEquiv RiemannSphere RiemannSphere :=
  JacobianChallenge.HolomorphicEquiv.ofEquiv (translateEquiv' a)
    (contMDiff_translateBy a)
    (by
      change ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (translateBy (-a))
      exact contMDiff_translateBy (-a))

@[simp] lemma translateEquiv_apply (a : ℂ) (x : RiemannSphere) :
    (translateEquiv a : RiemannSphere → RiemannSphere) x = translateBy a x := rfl

end RiemannSphere

end JacobianChallenge
