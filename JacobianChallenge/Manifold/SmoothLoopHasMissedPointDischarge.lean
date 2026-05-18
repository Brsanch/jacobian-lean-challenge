/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphereChartSymmSmooth
import JacobianChallenge.Manifold.LoopFactorsThroughVectorSpaceFromMissedPoint
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-! # Discharge of `SmoothLoopHasMissedPointHypothesis`

**Headline.** `SmoothLoopHasMissedPointHypothesis p₀` holds
**unconditionally** for every basepoint `p₀ : RiemannSphere`. I.e.,
every smooth loop `γ : SmoothPath 𝓘(ℝ, ℂ) RS` based at `p₀` misses
some point of `RS`.

## Proof outline (Sard via Hausdorff dimension)

Let `W := γ.ambient ⁻¹' chartN.source ⊆ ℝ`. Set
`s := W ∩ Icc 0 1`.

1. `chartN ∘ γ.ambient` is `C¹` at every `x ∈ W` (smooth composition,
   `γ.ambient x ∈ chartN.source` where `chartN` is smooth).
2. By `ContDiffAt.exists_lipschitzOnWith`, at each such `x`, the
   composition is Lipschitz on a neighborhood.
3. By `dimH_image_le_of_locally_lipschitzOn` (mathlib),
   `dimH ((chartN ∘ γ.ambient) '' ((γ.ambient ⁻¹' chartN.source) ∩ Set.Icc (0 : ℝ) (1 : ℝ))) ≤ dimH ((γ.ambient ⁻¹' chartN.source) ∩ Set.Icc (0 : ℝ) (1 : ℝ)) ≤ dimH (univ : Set ℝ) = 1`.
4. `1 < 2 = finrank ℝ ℂ`, so by `dense_compl_of_dimH_lt_finrank`, the
   complement is dense in `ℂ`, hence non-empty.
5. Pick `z` in the complement. Then `chartN.symm z ∈ RS` is the missed
   point: if it were `γ.toPath t`, then `t.val ∈ s` and
   `(chartN ∘ γ.ambient) t.val = z`, contradicting `z ∉` image.

No `sorry`, no `axiom`. -/

open OnePoint Set
open scoped Manifold ContDiff Topology

namespace JacobianChallenge

namespace RiemannSphere

variable (p₀ : RiemannSphere)

/-- **Unconditional discharge of `SmoothLoopHasMissedPointHypothesis p₀`.** -/
theorem smoothLoopHasMissedPointHypothesis_holds :
    SmoothLoopHasMissedPointHypothesis p₀ := by
  intro γ _h_src _h_tgt
  -- Set up s = γ.ambient ⁻¹' chartN.source ∩ Icc 0 1.
  have hW_open : IsOpen (γ.ambient ⁻¹' chartN.source) :=
    chartN.open_source.preimage γ.ambient_contMDiff.continuous
  set s : Set ℝ := (γ.ambient ⁻¹' chartN.source) ∩ Set.Icc (0 : ℝ) (1 : ℝ)
    with hs_def
  -- Step 1: chartN ∘ γ.ambient is locally Lipschitz on s.
  have h_locally_lipschitz : ∀ x ∈ s, ∃ C : NNReal, ∃ t ∈ 𝓝[s] x,
      LipschitzOnWith C ((chartN : RiemannSphere → ℂ) ∘ γ.ambient) t := by
    intro x hx
    have h_amb_at : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        γ.ambient x := γ.ambient_contMDiff x
    have hx_chartN_source : γ.ambient x ∈ chartN.source := hx.1
    have h_chartN_at : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (chartN : RiemannSphere → ℂ) (γ.ambient x) := by
      have h_chartN_on : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤
          (chartN : RiemannSphere → ℂ) chartN.source := chartN_contMDiffOn
      have h_on : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (chartN : RiemannSphere → ℂ) chartN.source :=
        h_chartN_on.of_le le_top
      exact h_on.contMDiffAt (chartN.open_source.mem_nhds hx_chartN_source)
    have h_comp_at : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        ((chartN : RiemannSphere → ℂ) ∘ γ.ambient) x :=
      h_chartN_at.comp x h_amb_at
    have h_contDiffAt : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        ((chartN : RiemannSphere → ℂ) ∘ γ.ambient) x := by
      rw [contMDiffAt_iff_contDiffAt] at h_comp_at
      exact h_comp_at
    have h_C1 : ContDiffAt ℝ 1
        ((chartN : RiemannSphere → ℂ) ∘ γ.ambient) x := by
      apply h_contDiffAt.of_le
      -- 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞).
      exact_mod_cast le_top
    obtain ⟨K, t, ht_nhds, hf_lip⟩ := h_C1.exists_lipschitzOnWith
    refine ⟨K, t ∩ s, ?_, hf_lip.mono Set.inter_subset_left⟩
    exact Filter.inter_mem (Filter.mem_inf_of_left ht_nhds) self_mem_nhdsWithin
  -- Step 2: dimH ((chartN ∘ γ.ambient) '' ((γ.ambient ⁻¹' chartN.source) ∩ Set.Icc (0 : ℝ) (1 : ℝ))) ≤ 1.
  have h_dimH_image_le_s :
      dimH ((chartN : RiemannSphere → ℂ) ∘ γ.ambient '' ((γ.ambient ⁻¹' chartN.source) ∩ Set.Icc (0 : ℝ) (1 : ℝ))) ≤ dimH ((γ.ambient ⁻¹' chartN.source) ∩ Set.Icc (0 : ℝ) (1 : ℝ)) :=
    dimH_image_le_of_locally_lipschitzOn h_locally_lipschitz
  have h_dimH_s_le_one :
      dimH ((γ.ambient ⁻¹' chartN.source) ∩ Set.Icc (0 : ℝ) (1 : ℝ)) ≤ 1 := by
    have h_sub : (γ.ambient ⁻¹' chartN.source) ∩ Set.Icc (0 : ℝ) (1 : ℝ)
        ⊆ Set.Icc (0 : ℝ) (1 : ℝ) := fun _ hx => hx.2
    calc dimH ((γ.ambient ⁻¹' chartN.source) ∩ Set.Icc (0 : ℝ) (1 : ℝ))
        ≤ dimH (Set.Icc (0 : ℝ) (1 : ℝ)) := dimH_mono h_sub
      _ ≤ dimH (Set.univ : Set ℝ) := dimH_mono (Set.subset_univ _)
      _ = (Module.finrank ℝ ℝ : ℕ∞) := Real.dimH_univ_eq_finrank ℝ
      _ = 1 := by simp [Module.finrank_self]
  have h_dimH_image : dimH ((chartN : RiemannSphere → ℂ) ∘ γ.ambient '' ((γ.ambient ⁻¹' chartN.source) ∩ Set.Icc (0 : ℝ) (1 : ℝ))) ≤ 1 :=
    h_dimH_image_le_s.trans h_dimH_s_le_one
  -- Step 3: 1 < finrank ℝ ℂ ⟹ dense complement in ℂ.
  have h_dimH_lt :
      dimH ((chartN : RiemannSphere → ℂ) ∘ γ.ambient '' ((γ.ambient ⁻¹' chartN.source) ∩ Set.Icc (0 : ℝ) (1 : ℝ)))
        < (Module.finrank ℝ ℂ : ℕ∞) := by
    have h_finrank_C : (Module.finrank ℝ ℂ : ℕ∞) = 2 := by
      simp [Complex.finrank_real_complex]
    rw [h_finrank_C]
    calc dimH ((chartN : RiemannSphere → ℂ) ∘ γ.ambient '' ((γ.ambient ⁻¹' chartN.source) ∩ Set.Icc (0 : ℝ) (1 : ℝ)))
        ≤ 1 := h_dimH_image
      _ < 2 := by norm_num
  have h_dense : Dense (((chartN : RiemannSphere → ℂ) ∘ γ.ambient '' ((γ.ambient ⁻¹' chartN.source) ∩ Set.Icc (0 : ℝ) (1 : ℝ)))ᶜ) :=
    dense_compl_of_dimH_lt_finrank h_dimH_lt
  obtain ⟨z, hz_compl⟩ := h_dense.nonempty
  -- Step 4: chartN.symm z is the missed point.
  refine ⟨chartN.symm z, ?_⟩
  intro t h_eq_path
  apply hz_compl
  -- Show z ∈ (chartN ∘ γ.ambient) '' s.
  rw [Set.mem_image]
  refine ⟨t.val, ?_, ?_⟩
  · -- t.val ∈ s = W ∩ Icc 0 1.
    refine ⟨?_, t.property⟩
    -- t.val ∈ W = γ.ambient ⁻¹' chartN.source.
    -- γ.ambient t.val = γ.toPath t (via ambient_eq_on_unitInterval).
    -- γ.toPath t = chartN.symm z (by h_eq_path).
    -- chartN.symm z ∈ chartN.source (chartN.symm maps target → source).
    show γ.ambient t.val ∈ chartN.source
    have h_amb_eq := γ.ambient_eq_on_unitInterval t
    rw [h_amb_eq, h_eq_path]
    have hz_target : z ∈ chartN.target := by rw [chartN_target]; trivial
    exact chartN.map_target' hz_target
  · -- (chartN ∘ γ.ambient) t.val = z.
    show (chartN : RiemannSphere → ℂ) (γ.ambient t.val) = z
    have h_amb_eq := γ.ambient_eq_on_unitInterval t
    rw [h_amb_eq, h_eq_path]
    -- chartN (chartN.symm z) = z (right inverse on target).
    have hz_target : z ∈ chartN.target := by rw [chartN_target]; trivial
    exact chartN.right_inv hz_target

end RiemannSphere

end JacobianChallenge
