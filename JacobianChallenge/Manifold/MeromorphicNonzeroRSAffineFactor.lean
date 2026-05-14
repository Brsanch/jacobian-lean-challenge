/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroRSSimplePole

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Translation generator `f(z) = z - a` as `MeromorphicNonzero RS`

For any `a : ℂ`, builds `RSAffineFactor a : RS → ℂ` as
`RSSimplePole - (const a)`, with principal divisor `δ_{some a} -
δ_∞`. The chart-pullback identities use `RSSimplePole_comp_chartN_symm`
and `RSSimplePole_comp_chartS_symm_eq` from
`Manifold/RiemannSphereSimplePole.lean`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Filter Set OnePoint

namespace JacobianChallenge

/-- The affine factor `some z ↦ z - a`, `∞ ↦ -a`. -/
noncomputable def RSAffineFactor (a : ℂ) : RiemannSphere → ℂ :=
  fun x => RSSimplePole x - a

@[simp] lemma RSAffineFactor_infty (a : ℂ) :
    RSAffineFactor a (∞ : RiemannSphere) = -a := by
  show RSSimplePole ∞ - a = -a
  rw [RSSimplePole_infty]; ring

@[simp] lemma RSAffineFactor_coe (a z : ℂ) :
    RSAffineFactor a ((z : RiemannSphere)) = z - a := rfl

/-! ## Chart-pullback identities -/

lemma RSAffineFactor_comp_chartN_symm (a : ℂ) :
    RSAffineFactor a ∘ RiemannSphere.chartN.symm = (fun w : ℂ => w - a) := by
  funext w
  show RSSimplePole (RiemannSphere.chartN.symm w) - a = w - a
  have h : (RSSimplePole ∘ RiemannSphere.chartN.symm) w = w := by
    rw [RSSimplePole_comp_chartN_symm]; rfl
  show RSSimplePole (RiemannSphere.chartN.symm w) - a = w - a
  rw [show RSSimplePole (RiemannSphere.chartN.symm w) = w from h]

lemma RSAffineFactor_comp_chartS_symm_eq (a : ℂ) :
    RSAffineFactor a ∘ RiemannSphere.chartS.symm = (fun w : ℂ => w⁻¹ - a) := by
  funext w
  show RSSimplePole (RiemannSphere.chartS.symm w) - a = w⁻¹ - a
  congr 1
  show (RSSimplePole ∘ RiemannSphere.chartS.symm) w = w⁻¹
  rw [RSSimplePole_comp_chartS_symm_eq]

/-! ## Meromorphicity -/

lemma RSAffineFactor_mmeromorphicOn (a : ℂ) :
    MMeromorphicOn 𝓘(ℂ, ℂ) (RSAffineFactor a) Set.univ := by
  have h : RSAffineFactor a = RSSimplePole - (fun _ : RiemannSphere => a) := by
    funext x; rfl
  rw [h]
  exact RSSimplePole_mmeromorphicOn.sub (MMeromorphicOn.const a)

/-! ## Order at `∞`: equal to `-1` -/

/-- `meromorphicOrderAt (fun w => w⁻¹ - a) 0 = -1`. The pole of `w⁻¹`
dominates the constant `a`. Proof via the factorisation `w⁻¹ - a =
(1 - a w)/w` valid on a punctured nbhd of `0`. -/
lemma meromorphicOrderAt_inv_sub_const_zero (a : ℂ) :
    meromorphicOrderAt (fun w : ℂ => w⁻¹ - a) 0 = ((-1 : ℤ) : WithTop ℤ) := by
  -- Rewrite on a punctured nbhd of 0: `w⁻¹ - a = (1 - a*w) / w`.
  have h_eq : (fun w : ℂ => w⁻¹ - a) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun w : ℂ => (1 - a*w) / w) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw' : (w : ℂ) ≠ 0 := hw
    field_simp
  rw [meromorphicOrderAt_congr h_eq]
  -- Goal: meromorphicOrderAt ((1 - a*w)/w) 0 = -1.
  have h_div : (fun w : ℂ => (1 - a*w) / w)
      = (fun w : ℂ => 1 - a*w) / (id : ℂ → ℂ) := by
    funext w; rfl
  rw [h_div]
  have hf : MeromorphicAt (fun w : ℂ => 1 - a*w) 0 :=
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).meromorphicAt
  have hg : MeromorphicAt (id : ℂ → ℂ) 0 := analyticAt_id.meromorphicAt
  rw [meromorphicOrderAt_div hf hg]
  -- numerator order = 0, denominator order = 1.
  have h_num : meromorphicOrderAt (fun w : ℂ => 1 - a*w) 0 = 0 := by
    have hAn : AnalyticAt ℂ (fun w : ℂ => 1 - a*w) 0 :=
      analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
    rw [hAn.meromorphicOrderAt_eq]
    have h_val : (fun w : ℂ => 1 - a*w) 0 ≠ 0 := by
      show (1 - a*0 : ℂ) ≠ 0
      simp
    have h_ord : analyticOrderAt (fun w : ℂ => 1 - a*w) 0 = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr h_val)
    rw [h_ord]; rfl
  have h_den : meromorphicOrderAt (id : ℂ → ℂ) 0 = 1 := meromorphicOrderAt_id
  rw [h_num, h_den]
  rfl

/-- `mmeromorphicOrderAt 𝓘(ℂ,ℂ) (RSAffineFactor a) ∞ = -1`. -/
lemma RSAffineFactor_orderAt_infty (a : ℂ) :
    mmeromorphicOrderAt 𝓘(ℂ, ℂ) (RSAffineFactor a) (∞ : RiemannSphere)
      = ((-1 : ℤ) : WithTop ℤ) := by
  show meromorphicOrderAt
      ((RSAffineFactor a) ∘ (chartAt ℂ (∞ : RiemannSphere)).symm)
      ((chartAt ℂ (∞ : RiemannSphere)) ∞) = _
  have h_chart : (chartAt ℂ (∞ : RiemannSphere)
      : OpenPartialHomeomorph RiemannSphere ℂ)
        = RiemannSphere.chartS := rfl
  rw [h_chart, RSAffineFactor_comp_chartS_symm_eq, RiemannSphere.chartS_apply_infty]
  exact meromorphicOrderAt_inv_sub_const_zero a

/-! ## Continuity at finite points -/

lemma RSAffineFactor_continuousAt_coe (a : ℂ) (z : ℂ) :
    ContinuousAt (RSAffineFactor a) ((z : RiemannSphere)) := by
  have h_nhds : 𝓝 ((z : ℂ) : RiemannSphere)
      = Filter.map ((↑) : ℂ → RiemannSphere) (𝓝 z) :=
    ((OnePoint.isOpenEmbedding_coe (X := ℂ)).map_nhds_eq z).symm
  rw [ContinuousAt, h_nhds, Filter.tendsto_map'_iff]
  have h_eq : (RSAffineFactor a ∘ ((↑) : ℂ → RiemannSphere))
      = (fun w : ℂ => w - a) := by
    funext w; rfl
  rw [h_eq]
  show Filter.Tendsto (fun w : ℂ => w - a) (𝓝 z) (𝓝 (z - a))
  exact (continuousAt_id.sub continuousAt_const).tendsto

/-! ## Packaged `MeromorphicNonzero RiemannSphere` -/

/-- **The affine-factor `MeromorphicNonzero RS`.** For any `a : ℂ`,
principal divisor is `δ_{some a} - δ_∞`. -/
noncomputable def mnRSAffineFactor (a : ℂ) :
    MeromorphicNonzero RiemannSphere :=
  MeromorphicNonzero.ofRegularContinuous
    (g := RSAffineFactor a)
    (h_mero := RSAffineFactor_mmeromorphicOn a)
    (h_nonvanish := by
      intro x
      induction x using OnePoint.rec with
      | infty =>
        rw [RSAffineFactor_orderAt_infty a]
        decide
      | coe z =>
        show mmeromorphicOrderAt 𝓘(ℂ, ℂ) (RSAffineFactor a) ((z : RiemannSphere)) ≠ ⊤
        show meromorphicOrderAt
            ((RSAffineFactor a) ∘ (chartAt ℂ ((z : RiemannSphere))).symm)
            ((chartAt ℂ ((z : RiemannSphere))) ((z : RiemannSphere))) ≠ ⊤
        have h_chart : (chartAt ℂ ((z : RiemannSphere))
            : OpenPartialHomeomorph RiemannSphere ℂ)
              = RiemannSphere.chartN := rfl
        rw [h_chart, RSAffineFactor_comp_chartN_symm a,
          RiemannSphere.chartN_apply_coe]
        -- Goal: meromorphicOrderAt (fun w => w - a) z ≠ ⊤.
        show meromorphicOrderAt
          ((id : ℂ → ℂ) - (fun _ : ℂ => a)) z ≠ ⊤
        rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero
          (analyticAt_id.meromorphicAt.sub analyticAt_const.meromorphicAt)]
        -- ∀ᶠ w in 𝓝[≠] z, (id - const a) w ≠ 0, i.e., w - a ≠ 0, i.e., w ≠ a.
        by_cases hza : z = a
        · subst hza
          filter_upwards [self_mem_nhdsWithin] with w hw
          show w - z ≠ 0
          exact sub_ne_zero.mpr hw
        · have h_ev : ∀ᶠ w in 𝓝 z, w ≠ a := continuousAt_id.eventually_ne hza
          exact (h_ev.filter_mono nhdsWithin_le_nhds).mono
            (fun w hw => by show w - a ≠ 0; exact sub_ne_zero.mpr hw))
    (h_reg_cts := by
      intro x _hreg
      induction x using OnePoint.rec with
      | infty =>
        -- Order at ∞ is -1; hypothesis `0 ≤ -1` is false.
        exfalso
        rw [RSAffineFactor_orderAt_infty a] at _hreg
        exact absurd _hreg (by decide)
      | coe z =>
        exact RSAffineFactor_continuousAt_coe a z)

@[simp] lemma mnRSAffineFactor_toFun (a : ℂ) :
    (mnRSAffineFactor a : MeromorphicNonzero RiemannSphere).toFun
      = RSAffineFactor a := rfl

end JacobianChallenge

end
