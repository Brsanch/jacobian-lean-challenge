/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphereMobiusComposed
import JacobianChallenge.Manifold.SmoothLoopChartNPullbackDischarge
import JacobianChallenge.Manifold.SmoothCyclePushComp
import JacobianChallenge.Manifold.SmoothCyclePushId

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Discharge of `LoopFactorsThroughVectorSpaceHypothesis ℂ RS p₀` from missed-point hypothesis

**Headline.** Define the named hypothesis

```
SmoothLoopHasMissedPointHypothesis p₀ :=
  ∀ γ : SmoothPath 𝓘(ℝ, ℂ) RS, γ.src = p₀ → γ.tgt = p₀ →
    ∃ q : RS, ∀ t : unitInterval, γ.toPath t ≠ q
```

(every smooth loop based at `p₀` misses some point of `RS`).

Then `SmoothLoopHasMissedPointHypothesis p₀ →
LoopFactorsThroughVectorSpaceHypothesis ℂ RS p₀`.

## Case analysis on the missed point

* **q = ∞**: γ misses `∞`, so `γ.toPath '' univ ⊆ chartN.source`.
  Direct application of `smoothLoopChartNPullbackExistsHypothesis_holds`
  with `f := chartN.symm`.

* **q = (some c)** for `c : ℂ`: apply the Möbius shift
  `T := mobiusComposed c : RS → RS` sending `(some c) ↦ ∞`. Since `γ`
  misses `(some c)`, the pushed loop `push T γ` misses `∞`, so it has
  image in `chartN.source`. Apply the chart-N pullback to get
  `γ' : SmoothPath 𝓘(ℝ, ℂ) ℂ` with `push T γ = push chartN.symm γ'`.
  Then `γ = push T_inv (push chartN.symm γ') = push (T_inv ∘ chartN.symm) γ'`,
  using `mobiusComposedInv c ∘ mobiusComposed c = id` extensionally.

## What this file ships

* `SmoothLoopHasMissedPointHypothesis p₀ : Prop`.
* `loopFactorsThroughVectorSpaceHypothesis_of_missedPoint` — the
  headline discharge.

No `sorry`, no `axiom`. -/

open OnePoint
open scoped Manifold ContDiff Topology

namespace JacobianChallenge

namespace RiemannSphere

/-! ## Named missed-point hypothesis -/

/-- **`SmoothLoopHasMissedPointHypothesis p₀`** — every smooth loop on
`RS` based at `p₀` misses some point of `RS`. -/
def SmoothLoopHasMissedPointHypothesis (p₀ : RiemannSphere) : Prop :=
  ∀ γ : SmoothPath 𝓘(ℝ, ℂ) RiemannSphere,
    γ.src = p₀ → γ.tgt = p₀ →
    ∃ q : RiemannSphere, ∀ t : unitInterval, γ.toPath t ≠ q

/-! ## Pushed-loop is a loop -/

/-- `SmoothPath.push f hf γ` is a loop when `γ` is a loop. -/
lemma push_smoothPath_isLoop {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℝ, ℂ) ⊤ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℝ, ℂ) ⊤ Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) (h_loop : γ.src = γ.tgt) :
    (SmoothPath.push f hf γ).src = (SmoothPath.push f hf γ).tgt := by
  simp [SmoothPath.push_src, SmoothPath.push_tgt, h_loop]

/-! ## Headline discharge -/

/-- **From `SmoothLoopHasMissedPointHypothesis p₀`, derive
`LoopFactorsThroughVectorSpaceHypothesis ℂ RS p₀`.** -/
theorem loopFactorsThroughVectorSpaceHypothesis_of_missedPoint
    (p₀ : RiemannSphere)
    (h_missed : SmoothLoopHasMissedPointHypothesis p₀) :
    JacobianChallenge.LoopFactorsThroughVectorSpaceHypothesis
      ℂ RiemannSphere p₀ := by
  intro γ h_src h_tgt
  obtain ⟨q, h_q_missed⟩ := h_missed γ h_src h_tgt
  -- Case analysis on q.
  match q, h_q_missed with
  | (OnePoint.infty : RiemannSphere), h_q_missed =>
    -- Case q = ∞: γ misses ∞, so image is in chartN.source.
    have h_in_chartN : ∀ t : unitInterval, γ.toPath t ∈ chartN.source := by
      intro t
      rw [chartN_source]
      exact h_q_missed t
    obtain ⟨γ', h_γ'_loop, h_γ_eq⟩ :=
      smoothLoopChartNPullbackExistsHypothesis_holds p₀ γ h_src h_tgt h_in_chartN
    exact ⟨chartN.symm, chartN_symm_contMDiff.of_le (le_top), γ', h_γ'_loop, h_γ_eq⟩
  | ((c : ℂ) : RiemannSphere), h_q_missed =>
    -- Case q = (some c): apply mobiusComposed c shift.
    have hT : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (mobiusComposed c) :=
      contMDiff_mobiusComposed_real c
    have hT_inv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (mobiusComposedInv c) :=
      contMDiff_mobiusComposedInv_real c
    -- T ∘ γ as a SmoothPath.
    set γ_T : SmoothPath 𝓘(ℝ, ℂ) RiemannSphere :=
      SmoothPath.push (mobiusComposed c) hT γ with hγ_T_def
    -- γ_T is a loop based at T p₀.
    have h_γT_loop : γ_T.src = γ_T.tgt :=
      push_smoothPath_isLoop (mobiusComposed c) hT γ (h_src.trans h_tgt.symm)
    -- γ_T avoids ∞.
    have h_γT_avoids_infty : ∀ t : unitInterval,
        γ_T.toPath t ≠ (OnePoint.infty : RiemannSphere) := by
      intro t h_eq
      apply h_q_missed t
      have h_γT_apply : γ_T.toPath t = mobiusComposed c (γ.toPath t) := by
        show γ.toPath.map hT.continuous t = mobiusComposed c (γ.toPath t)
        rfl
      rw [h_γT_apply] at h_eq
      -- mobiusComposed c (γ.toPath t) = ∞ ⟹ γ.toPath t = (some c).
      -- Use the left-inverse: mobiusComposedInv c (mobiusComposed c x) = x.
      have h_apply_Tinv :=
        congrArg (mobiusComposedInv c) h_eq
      -- h_apply_Tinv : mobiusComposedInv c (mobiusComposed c (γ.toPath t))
      --              = mobiusComposedInv c ∞.
      rw [mobiusComposed_left_inv c (γ.toPath t)] at h_apply_Tinv
      -- And mobiusComposedInv c ∞ = some c.
      have h_Tinv_infty : mobiusComposedInv c (OnePoint.infty : RiemannSphere)
          = ((c : ℂ) : RiemannSphere) := by
        show translateBy c (antipode (OnePoint.infty : RiemannSphere))
          = ((c : ℂ) : RiemannSphere)
        rw [antipode_infty]
        show ((((0 + c : ℂ)) : RiemannSphere)) = (((c : ℂ)) : RiemannSphere)
        congr 1; ring
      rw [h_Tinv_infty] at h_apply_Tinv
      exact h_apply_Tinv
    have h_γT_in_chartN : ∀ t : unitInterval, γ_T.toPath t ∈ chartN.source := by
      intro t
      rw [chartN_source]
      exact h_γT_avoids_infty t
    -- Apply chart-N pullback.
    obtain ⟨γ', h_γ'_loop, h_γ_T_eq⟩ :=
      smoothLoopChartNPullbackExistsHypothesis_holds
        (mobiusComposed c p₀) γ_T
        (by show mobiusComposed c γ.src = mobiusComposed c p₀; rw [h_src])
        (by show mobiusComposed c γ.tgt = mobiusComposed c p₀; rw [h_tgt])
        h_γT_in_chartN
    -- Factorisation: f := mobiusComposedInv c ∘ chartN.symm.
    refine ⟨mobiusComposedInv c ∘ (chartN.symm : ℂ → RiemannSphere),
      hT_inv.comp (chartN_symm_contMDiff.of_le (le_top)),
      γ', h_γ'_loop, ?_⟩
    have h_chartN_pullback :
        SmoothPath.push (chartN.symm : ℂ → RiemannSphere)
          (chartN_symm_contMDiff.of_le (le_top)) γ' = γ_T := h_γ_T_eq.symm
    -- Compute push (mobiusComposedInv c ∘ chartN.symm) γ' via push_comp +
    -- push (T_inv ∘ T) γ = γ (via SmoothPath.ext + mobiusComposed_left_inv).
    have h_compose :
        SmoothPath.push (mobiusComposedInv c ∘ (chartN.symm : ℂ → RiemannSphere))
          (hT_inv.comp (chartN_symm_contMDiff.of_le (le_top))) γ'
          = SmoothPath.push (mobiusComposedInv c) hT_inv
              (SmoothPath.push (chartN.symm : ℂ → RiemannSphere)
                (chartN_symm_contMDiff.of_le (le_top)) γ') :=
      SmoothPath.push_comp (mobiusComposedInv c) hT_inv
        (chartN.symm : ℂ → RiemannSphere)
        (chartN_symm_contMDiff.of_le (le_top)) γ'
    have h_TinvT :
        SmoothPath.push (mobiusComposedInv c) hT_inv
            (SmoothPath.push (mobiusComposed c) hT γ)
          = SmoothPath.push (mobiusComposedInv c ∘ mobiusComposed c)
              (hT_inv.comp hT) γ :=
      (SmoothPath.push_comp (mobiusComposedInv c) hT_inv
        (mobiusComposed c) hT γ).symm
    have h_TinvT_eq_id :
        SmoothPath.push (mobiusComposedInv c ∘ mobiusComposed c)
            (hT_inv.comp hT) γ = γ := by
      apply SmoothPath.ext
      · show mobiusComposedInv c (mobiusComposed c γ.src) = γ.src
        exact mobiusComposed_left_inv c γ.src
      · show mobiusComposedInv c (mobiusComposed c γ.tgt) = γ.tgt
        exact mobiusComposed_left_inv c γ.tgt
      · intro t
        show (γ.toPath.map (hT_inv.comp hT).continuous) t = γ.toPath t
        show mobiusComposedInv c (mobiusComposed c (γ.toPath t)) = γ.toPath t
        exact mobiusComposed_left_inv c (γ.toPath t)
    calc γ
        = SmoothPath.push (mobiusComposedInv c ∘ mobiusComposed c)
            (hT_inv.comp hT) γ := h_TinvT_eq_id.symm
      _ = SmoothPath.push (mobiusComposedInv c) hT_inv
            (SmoothPath.push (mobiusComposed c) hT γ) := h_TinvT.symm
      _ = SmoothPath.push (mobiusComposedInv c) hT_inv γ_T := by rw [← hγ_T_def]
      _ = SmoothPath.push (mobiusComposedInv c) hT_inv
            (SmoothPath.push (chartN.symm : ℂ → RiemannSphere)
              (chartN_symm_contMDiff.of_le (le_top)) γ') := by
            rw [h_chartN_pullback]
      _ = SmoothPath.push (mobiusComposedInv c ∘ (chartN.symm : ℂ → RiemannSphere))
            (hT_inv.comp (chartN_symm_contMDiff.of_le (le_top))) γ' :=
            h_compose.symm

end RiemannSphere

end JacobianChallenge
