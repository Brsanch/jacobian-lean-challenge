/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroRegularValueSet
import JacobianChallenge.Manifold.SmoothPathLinearInChart
import JacobianChallenge.Manifold.SmoothPathConcat
import JacobianChallenge.Manifold.SmoothPathConnectedRiemannSphere

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Existence of a regular smooth path `0 → ∞` on the Riemann sphere

For `f : MeromorphicNonzero X` with `f.toRiemannSphere` non-constant
and with `0` and `∞` both regular values of `f`, this file produces
a smooth function `β : ℝ → RiemannSphere` such that:

* `β 0 = ((0 : ℂ) : RiemannSphere)`,
* `β 1 = OnePoint.infty`,
* `ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β`,
* `∀ t ∈ Icc 0 1, β t ∈ f.regularValueSet`.

This is the **β-existence input** for the level-set chain construction
in C3 step 9: combined with step 7d-d's boundary identification
(`boundary_levelSetChain_eq_neg_principalDivisorMap_pointwise`), it
reduces the structural hypothesis `h_struct` of
`abelGeneratorPeriodCondition_of_levelSet_lattice` to the
lattice-period clause alone.

## Construction

Pick `s ∈ ℝ` avoiding the finite forbidden set
`{w.re / w.im | w ∈ ℂ, some w ∈ f.criticalValues, w.im > 0}`. Set
`r := some(s + i) : RiemannSphere`. Then:

* **Segment 1** (`linearInChartSegment` in `chartN`): from `(0 : RS)`
  to `r`. The chart-coord segment `{t(s+i) | t ∈ [0,1]}` in ℂ avoids
  all `chartN`-images of critical values: any `w ∈ ℂ` with `some w ∈
  criticalValues` either equals `0` (excluded since `0 ∈
  regularValueSet`) or has `w.re ≠ s * w.im` (excluded by choice of `s`).
* **Segment 2** (`linearInChartSegment` in `chartS`): from `r` to `∞`.
  In `chartS`, the chart-coord goes from `1/r` to `0`. The same `s`-choice
  makes the segment avoid `chartS`-images of critical values by the
  symmetric reciprocal argument.
* Concatenate via `SmoothPath.concat` through the bridge point `r`.

The smoothness extension to all of ℝ is provided by `SmoothPath`'s
`smooth` field (a `ContMDiff` ambient `ℝ → RS` agreeing with the
underlying `Path` on `unitInterval`).

No `sorry`, no `axiom`. -/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Generic real `s` avoiding a finite set of `w.re / w.im` -/

/-- For any finite set `S ⊂ ℂ`, there exists `s ∈ ℝ` such that for every
`w ∈ S` with `w.im > 0`, `s * w.im ≠ w.re`. -/
lemma exists_s_avoiding_critical (S : Finset ℂ) :
    ∃ s : ℝ, ∀ w ∈ S, 0 < w.im → s * w.im ≠ w.re := by
  classical
  set T : Finset ℝ :=
    (S.filter (fun w => 0 < w.im)).image (fun w => w.re / w.im) with hT
  have h_exists : ∃ s : ℝ, s ∉ T := by
    by_contra h_all
    push Not at h_all
    have h_sub : (Set.univ : Set ℝ) ⊆ (T : Set ℝ) := fun x _ => h_all x
    exact Set.infinite_univ (T.finite_toSet.subset h_sub)
  obtain ⟨s, hs⟩ := h_exists
  refine ⟨s, fun w hwS hw_im h_eq => ?_⟩
  apply hs
  rw [hT]
  refine Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨hwS, hw_im⟩, ?_⟩
  field_simp
  linarith [h_eq]

/-! ## chartN-segment avoidance: `{t(s+i) | t ∈ [0,1]}` misses critical values -/

/-- The chart-coordinate segment from `0` to `s + i` in `chartN.target = ℂ`
contains no `chartN`-image of a critical value, under the hypotheses
`0 ∈ f.regularValueSet` and `s * w.im ≠ w.re` for every `w ∈ ℂ` with
`some w ∈ f.criticalValues` and `w.im > 0`. -/
lemma chartN_segment_mem_regularValueSet
    (f : MeromorphicNonzero X)
    (h0_reg : (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet)
    {s : ℝ}
    (hs : ∀ w : ℂ, ((w : RiemannSphere)) ∈ f.criticalValues →
            0 < w.im → s * w.im ≠ w.re)
    {z : ℂ}
    (hz : z ∈ segment ℝ (0 : ℂ) (((s : ℂ) + Complex.I))) :
    ((z : RiemannSphere)) ∈ f.regularValueSet := by
  intro h_crit
  rw [show segment ℝ (0 : ℂ) (((s : ℂ) + Complex.I))
      = (fun θ : ℝ => (1 - θ) • (0 : ℂ) + θ • (((s : ℂ) + Complex.I))) ''
        Set.Icc (0 : ℝ) 1 from segment_eq_image ℝ _ _] at hz
  obtain ⟨t, ⟨ht0, ht1⟩, hzt⟩ := hz
  simp only at hzt
  -- hzt : (1 - t) • 0 + t • (s + i) = z, after β-reduction
  have hzt' : z = t • (((s : ℂ) + Complex.I)) := by
    rw [← hzt]; simp
  -- z.re = t * s, z.im = t.
  have hzre : z.re = t * s := by
    rw [hzt']
    simp [Complex.add_re, Complex.I_re, Complex.ofReal_re]
  have hzim : z.im = t := by
    rw [hzt']
    simp [Complex.add_im, Complex.I_im, Complex.ofReal_im]
  -- Case split: t = 0 or t > 0.
  rcases eq_or_lt_of_le ht0 with rfl | ht_pos
  · -- t = 0: z = 0, contradiction with h0_reg.
    have hz_eq : z = 0 := by rw [hzt']; simp
    subst hz_eq
    exact h0_reg h_crit
  · -- t > 0: z.im = t > 0, and hs gives s * z.im = s * t = t * s = z.re. Contradiction.
    have ht_pos' : 0 < z.im := by rw [hzim]; exact ht_pos
    have h_eq : s * z.im = z.re := by rw [hzim, hzre]; ring
    exact hs z h_crit ht_pos' h_eq

/-! ## chartS-segment avoidance: `{(1-u)*(1/(s+i)) | u ∈ [0,1]}` misses critical values -/

/-- The chart-coordinate segment from `1/(s+i)` to `0` in `chartS.target = ℂ`
contains no `chartS`-image of a critical value, under the hypotheses
`∞ ∈ f.regularValueSet` and `s * w.im ≠ w.re` for every `w ∈ ℂ` with
`some w ∈ f.criticalValues` and `w.im > 0`.

The proof uses the fact that for `r = s + i` and `w = a + bi` with
`b > 0`, the condition `r/w ∈ ℝ_{>0}` reduces to `s = a/b`. -/
lemma chartS_segment_mem_regularValueSet
    (f : MeromorphicNonzero X)
    (h_inf_reg : (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet)
    {s : ℝ}
    (hs : ∀ w : ℂ, ((w : RiemannSphere)) ∈ f.criticalValues →
            0 < w.im → s * w.im ≠ w.re)
    {z : ℂ}
    (hz : z ∈ segment ℝ (((s : ℂ) + Complex.I)⁻¹) (0 : ℂ)) :
    RiemannSphere.chartS.symm z ∈ f.regularValueSet := by
  intro h_crit
  rw [show segment ℝ (((s : ℂ) + Complex.I)⁻¹) (0 : ℂ)
      = (fun θ : ℝ => (1 - θ) • (((s : ℂ) + Complex.I)⁻¹) + θ • (0 : ℂ)) ''
        Set.Icc (0 : ℝ) 1 from segment_eq_image ℝ _ _] at hz
  obtain ⟨u, ⟨hu0, hu1⟩, hzu⟩ := hz
  simp only at hzu
  -- z = (1-u) • (1/(s+i)) + u • 0 = (1-u) • (1/(s+i)).
  have hzu' : z = (1 - u) • (((s : ℂ) + Complex.I)⁻¹) := by
    rw [← hzu]; simp
  -- s + i ≠ 0 because its imaginary part is 1.
  have h_s_i_ne_zero : ((s : ℂ) + Complex.I) ≠ 0 := by
    intro h_eq
    have h_im : ((s : ℂ) + Complex.I).im = 1 := by
      simp [Complex.add_im, Complex.I_im, Complex.ofReal_im]
    rw [h_eq] at h_im
    exact zero_ne_one h_im
  rcases eq_or_lt_of_le hu1 with rfl | hu_lt_one
  · -- u = 1: z = 0, so chartS.symm 0 = ∞. h_crit ⇒ ∞ ∈ criticalValues. Contradiction.
    have hz_eq : z = 0 := by rw [hzu']; simp
    subst hz_eq
    rw [RiemannSphere.chartS_symm_apply_zero] at h_crit
    exact h_inf_reg h_crit
  · -- u < 1: z = (1-u) • (1/(s+i)) ≠ 0.
    have h_one_sub_u : (0 : ℝ) < 1 - u := by linarith
    have hz_ne_zero : z ≠ 0 := by
      rw [hzu']
      intro h_eq
      have h_smul_zero : (1 - u : ℝ) • (((s : ℂ) + Complex.I)⁻¹) = (0 : ℂ) := h_eq
      have h_inv_ne : ((s : ℂ) + Complex.I)⁻¹ ≠ 0 := inv_ne_zero h_s_i_ne_zero
      rcases smul_eq_zero.mp h_smul_zero with h | h
      · have : (1 - u : ℝ) = 0 := by exact_mod_cast h
        linarith
      · exact h_inv_ne h
    -- chartS.symm z = some(1/z).
    have h_chartS_symm : RiemannSphere.chartS.symm z = (((z⁻¹) : ℂ) : RiemannSphere) :=
      RiemannSphere.chartS_symm_apply_of_ne hz_ne_zero
    rw [h_chartS_symm] at h_crit
    -- Let w := z⁻¹. Then w = (s + i) / (1 - u).
    set w := z⁻¹ with hw_def
    have h_w_eq : w = ((s : ℂ) + Complex.I) / ((1 - u : ℝ) : ℂ) := by
      rw [hw_def, hzu']
      rw [show ((1 - u : ℝ) • (((s : ℂ) + Complex.I)⁻¹))
            = (((1 - u : ℝ) : ℂ) * ((s : ℂ) + Complex.I)⁻¹) from
          Complex.real_smul]
      rw [mul_inv]
      rw [inv_inv]
      rw [mul_comm]
      rfl
    have h_one_sub_u_C_ne : ((1 - u : ℝ) : ℂ) ≠ 0 := by
      intro h_eq
      have : (1 - u : ℝ) = 0 := by exact_mod_cast h_eq
      linarith
    have h_one_sub_u_ne : (1 - u : ℝ) ≠ 0 := ne_of_gt h_one_sub_u
    have h_one_sub_u_ne : (1 - u : ℝ) ≠ 0 := ne_of_gt h_one_sub_u
    have hw_re : w.re = s / (1 - u) := by
      rw [h_w_eq, Complex.div_re]
      simp [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
      field_simp
    have hw_im : w.im = 1 / (1 - u) := by
      rw [h_w_eq, Complex.div_im]
      simp [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
    have hw_im_pos : 0 < w.im := by rw [hw_im]; positivity
    have h_s_mul : s * w.im = w.re := by
      rw [hw_re, hw_im]
      field_simp
    exact hs w h_crit hw_im_pos h_s_mul

/-! ## Auxiliary disequalities for the bridge point `r := some(s + i)` -/

private lemma s_i_RS_ne_infty (s : ℝ) :
    ((((s : ℂ) + Complex.I) : RiemannSphere)) ≠ (OnePoint.infty : RiemannSphere) :=
  OnePoint.coe_ne_infty _

private lemma s_i_RS_ne_zero (s : ℝ) :
    ((((s : ℂ) + Complex.I) : RiemannSphere)) ≠ (((0 : ℂ) : RiemannSphere)) := by
  intro h
  have h_eq : ((s : ℂ) + Complex.I) = (0 : ℂ) := OnePoint.coe_injective h
  have h_im : ((s : ℂ) + Complex.I).im = 1 := by
    simp [Complex.add_im, Complex.I_im, Complex.ofReal_im]
  rw [h_eq] at h_im
  exact zero_ne_one h_im

private lemma zero_RS_ne_infty' : (((0 : ℂ) : RiemannSphere)) ≠ (OnePoint.infty : RiemannSphere) :=
  OnePoint.coe_ne_infty _

/-! ## Endpoint membership in chart sources -/

private lemma zero_RS_mem_chartN_source :
    (((0 : ℂ) : RiemannSphere)) ∈ RiemannSphere.chartN.source := by
  rw [RiemannSphere.chartN_source]
  exact zero_RS_ne_infty'

private lemma s_i_RS_mem_chartN_source (s : ℝ) :
    ((((s : ℂ) + Complex.I) : RiemannSphere)) ∈ RiemannSphere.chartN.source := by
  rw [RiemannSphere.chartN_source]
  exact s_i_RS_ne_infty s

private lemma s_i_RS_mem_chartS_source (s : ℝ) :
    ((((s : ℂ) + Complex.I) : RiemannSphere)) ∈ RiemannSphere.chartS.source := by
  rw [RiemannSphere.chartS_source]
  exact s_i_RS_ne_zero s

private lemma infty_mem_chartS_source :
    (OnePoint.infty : RiemannSphere) ∈ RiemannSphere.chartS.source := by
  rw [RiemannSphere.chartS_source]
  exact fun h => zero_RS_ne_infty' h.symm

/-! ## Chart applications at the endpoints -/

private lemma chartN_zero_RS :
    RiemannSphere.chartN (((0 : ℂ) : RiemannSphere)) = (0 : ℂ) :=
  RiemannSphere.chartN_apply_coe 0

private lemma chartN_s_i_RS (s : ℝ) :
    RiemannSphere.chartN ((((s : ℂ) + Complex.I) : RiemannSphere))
      = ((s : ℂ) + Complex.I) :=
  RiemannSphere.chartN_apply_coe _

private lemma chartS_s_i_RS (s : ℝ) :
    RiemannSphere.chartS ((((s : ℂ) + Complex.I) : RiemannSphere))
      = (((s : ℂ) + Complex.I))⁻¹ :=
  RiemannSphere.chartSToFun_coe _

private lemma chartS_infty :
    RiemannSphere.chartS (OnePoint.infty : RiemannSphere) = (0 : ℂ) :=
  RiemannSphere.chartSToFun_infty

/-! ## Headline -/

/-- **Existence of a regular smooth path `0 → ∞` on the Riemann sphere.**

For `f : MeromorphicNonzero X` non-constant with `0` and `∞` both
regular values, there exists a smooth function `β : ℝ → RiemannSphere`
with `β 0 = (0 : ℂ) : RS`, `β 1 = ∞`, and `β t ∈ f.regularValueSet`
for all `t ∈ [0, 1]`.

This is the existence input for the level-set chain construction in
C3 step 9. Combined with step 7d-d's boundary identification, it
reduces `h_struct` of `abelGeneratorPeriodCondition_of_levelSet_lattice`
to the lattice-period clause alone. -/
theorem exists_regular_path_zero_to_infty
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (h0_reg : (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet)
    (h_inf_reg : (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet) :
    ∃ β : ℝ → RiemannSphere,
      ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) ∞ β ∧
      β 0 = (((0 : ℂ) : RiemannSphere)) ∧
      β 1 = (OnePoint.infty : RiemannSphere) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, β t ∈ f.regularValueSet := by
  classical
  -- Step 1: pick `s ∈ ℝ` avoiding all `w.re / w.im` for finite critical values
  -- with positive imaginary part.
  have h_finite : (((OnePoint.some : ℂ → RiemannSphere) ⁻¹' f.criticalValues)).Finite :=
    (f.criticalValues_finite hnc).preimage (OnePoint.coe_injective.injOn)
  obtain ⟨s, hs⟩ := exists_s_avoiding_critical h_finite.toFinset
  have hs' : ∀ w : ℂ, ((w : RiemannSphere)) ∈ f.criticalValues →
      0 < w.im → s * w.im ≠ w.re := by
    intro w hw_crit hw_im h_eq
    refine hs w ?_ hw_im h_eq
    rw [Set.Finite.mem_toFinset]
    exact hw_crit
  -- Step 2: build the chartN segment path `γ : 0_RS → some(s + i)`.
  set r : RiemannSphere := ((((s : ℂ) + Complex.I)) : RiemannSphere) with hr_def
  have h_seg_chartN :
      segment ℝ (RiemannSphere.chartN (((0 : ℂ) : RiemannSphere)))
                (RiemannSphere.chartN r)
        ⊆ RiemannSphere.chartN.target := by
    rw [RiemannSphere.chartN_target]
    exact fun _ _ => Set.mem_univ _
  set γ : SmoothPath 𝓘(ℝ, ℂ) RiemannSphere :=
    SmoothPath.linearInChartSegment RiemannSphere.chartN
      RiemannSphere.chartN_mem_atlas (((0 : ℂ) : RiemannSphere)) r
      zero_RS_mem_chartN_source (s_i_RS_mem_chartN_source s) h_seg_chartN
    with hγ_def
  -- Step 3: build the chartS segment path `δ : some(s + i) → ∞`.
  have h_seg_chartS :
      segment ℝ (RiemannSphere.chartS r) (RiemannSphere.chartS OnePoint.infty)
        ⊆ RiemannSphere.chartS.target := by
    rw [RiemannSphere.chartS_target]
    exact fun _ _ => Set.mem_univ _
  set δ : SmoothPath 𝓘(ℝ, ℂ) RiemannSphere :=
    SmoothPath.linearInChartSegment RiemannSphere.chartS
      RiemannSphere.chartS_mem_atlas r OnePoint.infty
      (s_i_RS_mem_chartS_source s) infty_mem_chartS_source h_seg_chartS
    with hδ_def
  -- Step 4: concat.
  have h_concat : γ.tgt = δ.src := by
    show r = r
    rfl
  set ψ : SmoothPath 𝓘(ℝ, ℂ) RiemannSphere := γ.concat δ h_concat with hψ_def
  -- Step 5: extract ambient.
  refine ⟨ψ.ambient, ?_, ?_, ?_, ?_⟩
  · -- C^∞ smoothness of the ambient.
    exact ψ.ambient_contMDiff.of_le (by decide)
  · -- ψ.ambient 0 = γ.src = 0_RS.
    have h_eq : ψ.ambient 0 = ψ.toPath ⟨0, by constructor <;> norm_num⟩ :=
      ψ.ambient_eq_on_unitInterval ⟨0, by constructor <;> norm_num⟩
    rw [h_eq]
    have h_src : ψ.toPath ⟨0, by constructor <;> norm_num⟩ = ψ.src :=
      ψ.toPath.source'
    rw [h_src]
    show γ.src = _
    rfl
  · -- ψ.ambient 1 = δ.tgt = ∞.
    have h_eq : ψ.ambient 1 = ψ.toPath ⟨1, by constructor <;> norm_num⟩ :=
      ψ.ambient_eq_on_unitInterval ⟨1, by constructor <;> norm_num⟩
    rw [h_eq]
    have h_tgt : ψ.toPath ⟨1, by constructor <;> norm_num⟩ = ψ.tgt :=
      ψ.toPath.target'
    rw [h_tgt]
    show δ.tgt = _
    rfl
  · -- Regularity on [0, 1].
    intro t ht
    -- ψ.ambient t = ψ.toPath ⟨t, ht⟩.
    have h_unit : t ∈ unitInterval := ht
    have h_eq : ψ.ambient t = ψ.toPath ⟨t, h_unit⟩ := by
      have := ψ.ambient_eq_on_unitInterval ⟨t, h_unit⟩
      exact this
    rw [h_eq]
    -- Unfold ψ.toPath via concatAmbient and case-split.
    show (γ.concat δ h_concat).toPath ⟨t, h_unit⟩ ∈ f.regularValueSet
    -- The path value is γ.concatAmbient δ t.
    have h_path : (γ.concat δ h_concat).toPath ⟨t, h_unit⟩
        = γ.concatAmbient δ t := rfl
    rw [h_path]
    -- Case split: t ≤ 1/2 or t > 1/2.
    by_cases h_left : t ≤ 1/2
    · -- Left half: γ.concatAmbient δ t = γ.ambient (concatRepLeft t).
      rw [γ.concatAmbient_eqOn_left δ h_left]
      change γ.ambient (SmoothPath.concatRepLeft t) ∈ f.regularValueSet
      -- concatRepLeft t ∈ [0, 1].
      have h_rep_unit : SmoothPath.concatRepLeft t ∈ unitInterval := by
        refine ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
      -- γ.ambient ... = γ.toPath ⟨concatRepLeft t, ...⟩.
      have h_γ_eq : γ.ambient (SmoothPath.concatRepLeft t)
          = γ.toPath ⟨SmoothPath.concatRepLeft t, h_rep_unit⟩ :=
        γ.ambient_eq_on_unitInterval ⟨SmoothPath.concatRepLeft t, h_rep_unit⟩
      rw [h_γ_eq]
      -- γ.toPath is chartN.symm (bumpedSegment ...) for linearInChartSegment.
      show RiemannSphere.chartN.symm (bumpedSegment
              (RiemannSphere.chartN (((0 : ℂ) : RiemannSphere)))
              (RiemannSphere.chartN r) (SmoothPath.concatRepLeft t))
          ∈ f.regularValueSet
      rw [chartN_zero_RS, chartN_s_i_RS]
      have h_in_seg : bumpedSegment (0 : ℂ) ((s : ℂ) + Complex.I)
              (SmoothPath.concatRepLeft t)
          ∈ segment ℝ (0 : ℂ) ((s : ℂ) + Complex.I) :=
        bumpedSegment_mem_segment _ _ _
      exact f.chartN_segment_mem_regularValueSet h0_reg hs' h_in_seg
    · -- Right half: γ.concatAmbient δ t = δ.ambient (concatRepRight t).
      push Not at h_left
      rw [γ.concatAmbient_eqOn_right δ h_left]
      change δ.ambient (SmoothPath.concatRepRight t) ∈ f.regularValueSet
      have h_rep_unit : SmoothPath.concatRepRight t ∈ unitInterval := by
        refine ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
      have h_δ_eq : δ.ambient (SmoothPath.concatRepRight t)
          = δ.toPath ⟨SmoothPath.concatRepRight t, h_rep_unit⟩ :=
        δ.ambient_eq_on_unitInterval ⟨SmoothPath.concatRepRight t, h_rep_unit⟩
      rw [h_δ_eq]
      show RiemannSphere.chartS.symm (bumpedSegment
              (RiemannSphere.chartS r)
              (RiemannSphere.chartS OnePoint.infty)
              (SmoothPath.concatRepRight t))
          ∈ f.regularValueSet
      rw [chartS_s_i_RS, chartS_infty]
      have h_in_seg : bumpedSegment (((s : ℂ) + Complex.I))⁻¹ (0 : ℂ)
              (SmoothPath.concatRepRight t)
          ∈ segment ℝ (((s : ℂ) + Complex.I))⁻¹ (0 : ℂ) :=
        bumpedSegment_mem_segment _ _ _
      exact f.chartS_segment_mem_regularValueSet h_inf_reg hs' h_in_seg

end MeromorphicNonzero

end JacobianChallenge

end
