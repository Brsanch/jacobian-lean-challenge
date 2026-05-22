/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathPush
import JacobianChallenge.Manifold.SmoothPathIntegral
import JacobianChallenge.Manifold.SmoothOneFormPullback

set_option linter.unusedSectionVars false

/-! # Path-level change-of-variables: `SmoothPath.integrate_push`

The cornerstone of F8 OneForm functoriality:

    `(SmoothPath.push f hf γ).integrate ω
        = γ.integrate (SmoothOneForm.pullback f hf_ω ω)`

i.e., integrating a smooth 1-form along the pushed path equals
integrating the pulled-back 1-form along the original path. This is the
classical change-of-variables theorem for line integrals on smooth
manifolds.

Sister file to `SmoothPathCompSmoothIntegrate.lean`, which proves the
same identity for `ContMDiff.compSmoothPath`. The two pushforwards are
structurally distinct (different `Classical.choose` witnesses), so the
identity must be proven independently for `JacobianChallenge.SmoothPath.push`,
the pushforward used by `SmoothChain.push` and downstream
`SmoothCycle.pushHom`.

The hypothesis is `hf_ω : ContMDiff I I ω f` (analytic level) to match
`SmoothOneForm.pullback`'s requirement; `SmoothPath.push` needs only
the downcast `hf_ω.of_le le_top : ContMDiff I I ∞ f`. In F8 use cases
the input is the real-side analytic lift of a holomorphic curve map
(via `ContMDiff.complex_to_real`).

## What this file ships

* `JacobianChallenge.SmoothPath.push_ambient_eq_on_unitInterval` —
  pointwise: `(push f hf γ).ambient s = f (γ.ambient s)` on
  `s ∈ unitInterval`.
* `JacobianChallenge.SmoothPath.push_ambient_eventuallyEq` —
  eventually-equal on `Ioo 0 1`.
* `JacobianChallenge.SmoothPath.velocity_push_of_mem_Ioo` — chain-rule
  velocity identity:
  `(push f hf γ).velocity t = mfderiv f (γ.ambient t) (γ.velocity t)`
  on `Ioo 0 1`.
* `JacobianChallenge.SmoothPath.integrate_push` — the
  change-of-variables identity.

No `sorry`, no `axiom`. -/

noncomputable section

open MeasureTheory Set Filter Topology Function SmoothPath
open scoped Manifold Topology ContDiff

namespace JacobianChallenge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ⊤ Y]

namespace SmoothPath

/-- **The C^∞ downcast** of an analytic-level smoothness hypothesis. -/
private lemma hf_smooth {f : X → Y} (hf : ContMDiff I I ω f) :
    ContMDiff I I ∞ f :=
  hf.of_le le_top

/-- **Pointwise ambient identity for `SmoothPath.push`.** On
`unitInterval`, the Classical-chosen ambient of the pushed path equals
`f ∘ γ.ambient`. Both project to `γ.toPath.map hf.continuous`. -/
lemma push_ambient_eq_on_unitInterval {f : X → Y}
    (hf : ContMDiff I I ω f) (γ : _root_.SmoothPath I X) (s : ℝ)
    (hs : s ∈ unitInterval) :
    (JacobianChallenge.SmoothPath.push f (hf_smooth hf) γ).ambient s
      = f (γ.ambient s) := by
  have h_eq_push :=
    (JacobianChallenge.SmoothPath.push f (hf_smooth hf) γ).ambient_eq_on_unitInterval
      ⟨s, hs⟩
  have h_val : (⟨s, hs⟩ : unitInterval).val = s := rfl
  rw [h_val] at h_eq_push
  rw [h_eq_push]
  show (γ.toPath.map (hf_smooth hf).continuous) ⟨s, hs⟩ = f (γ.ambient s)
  rw [γ.ambient_eq_on_unitInterval ⟨s, hs⟩]
  rfl

/-- **Eventually-equal version** on `Ioo 0 1`. -/
lemma push_ambient_eventuallyEq {f : X → Y}
    (hf : ContMDiff I I ω f) (γ : _root_.SmoothPath I X) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    (JacobianChallenge.SmoothPath.push f (hf_smooth hf) γ).ambient
      =ᶠ[𝓝 t] (fun s : ℝ => f (γ.ambient s)) := by
  refine eventually_of_mem (IsOpen.mem_nhds isOpen_Ioo ht) ?_
  intro s hs
  exact push_ambient_eq_on_unitInterval hf γ s
    ⟨le_of_lt hs.1, le_of_lt hs.2⟩

/-- **Chain-rule velocity identity** on `Ioo 0 1`:
`(push f hf γ).velocity t = mfderiv f (γ.ambient t) (γ.velocity t)`. -/
lemma velocity_push_of_mem_Ioo {f : X → Y}
    (hf : ContMDiff I I ω f) (γ : _root_.SmoothPath I X) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    (JacobianChallenge.SmoothPath.push f (hf_smooth hf) γ).velocity t
      = mfderiv I I f (γ.ambient t) (γ.velocity t) := by
  unfold _root_.SmoothPath.velocity
  have h_eq : mfderiv (𝓘(ℝ, ℝ)) I
        (JacobianChallenge.SmoothPath.push f (hf_smooth hf) γ).ambient t
      = mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => f (γ.ambient s)) t :=
    (push_ambient_eventuallyEq hf γ ht).mfderiv_eq
  rw [h_eq]
  have h_amb_diff : MDifferentiableAt (𝓘(ℝ, ℝ)) I γ.ambient t :=
    (γ.ambient_contMDiff t).mdifferentiableAt (by decide)
  have h_f_diff : MDifferentiableAt I I f (γ.ambient t) :=
    ((hf_smooth hf) (γ.ambient t)).mdifferentiableAt (by decide)
  show ((mfderiv (𝓘(ℝ, ℝ)) I (f ∘ γ.ambient) t :
          ℝ →L[ℝ] TangentSpace I (f (γ.ambient t))) (1 : ℝ))
        = (mfderiv I I f (γ.ambient t))
            ((mfderiv (𝓘(ℝ, ℝ)) I γ.ambient t :
              ℝ →L[ℝ] TangentSpace I (γ.ambient t)) (1 : ℝ))
  exact mfderiv_comp_apply t h_f_diff h_amb_diff (1 : ℝ)

/-- **Path-level change-of-variables.**
`(SmoothPath.push f (hf_smooth hf) γ).integrate ω
  = γ.integrate (SmoothOneForm.pullback f hf ω)`.

The integrand identity on `Ioo 0 1` combines the ambient identity, the
chain-rule velocity identity, and the definitional unfold of
`SmoothOneForm.pullback_apply`. Mismatch on the measure-zero endpoint
`{1}` is handled by `intervalIntegral.integral_congr_ae`. -/
theorem integrate_push {f : X → Y}
    (hf : ContMDiff I I ω f)
    (γ : _root_.SmoothPath I X) (om : SmoothOneForm I Y) :
    (JacobianChallenge.SmoothPath.push f (hf_smooth hf) γ).integrate om
      = γ.integrate (SmoothOneForm.pullback (I := I) (I' := I) f hf om) := by
  unfold _root_.SmoothPath.integrate
  have h_meas_one : MeasureTheory.volume ({1} : Set ℝ) = 0 :=
    Real.volume_singleton
  have h_almost : ∀ᵐ x ∂MeasureTheory.volume, x ≠ (1 : ℝ) := by
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨{1}ᶜ, ?_, fun x hx => hx⟩
    rw [MeasureTheory.mem_ae_iff, compl_compl]
    exact h_meas_one
  have h_congr : ∀ᵐ x ∂MeasureTheory.volume,
      x ∈ Set.uIoc (0 : ℝ) 1 →
        (JacobianChallenge.SmoothPath.push f (hf_smooth hf) γ).integrand om x
          = γ.integrand (SmoothOneForm.pullback (I := I) (I' := I) f hf om) x := by
    filter_upwards [h_almost] with x hx hx_uIoc
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx_uIoc
    have ht : x ∈ Ioo (0 : ℝ) 1 :=
      ⟨hx_uIoc.1, lt_of_le_of_ne hx_uIoc.2 hx⟩
    change applyCotangent (om
            ((JacobianChallenge.SmoothPath.push f (hf_smooth hf) γ).ambient x))
           ((JacobianChallenge.SmoothPath.push f (hf_smooth hf) γ).velocity x)
      = applyCotangent
          ((SmoothOneForm.pullback (I := I) (I' := I) f hf om) (γ.ambient x))
          (γ.velocity x)
    rw [push_ambient_eq_on_unitInterval hf γ x
          ⟨le_of_lt ht.1, le_of_lt ht.2⟩]
    rw [velocity_push_of_mem_Ioo hf γ ht]
    rw [SmoothOneForm.pullback_apply]
    -- Definitional: `applyCotangent (φ.comp T) v = applyCotangent φ (T v)`
    -- via `cotangentEquiv = id`.
    rfl
  rw [intervalIntegral.integral_congr_ae h_congr]

end SmoothPath

end JacobianChallenge

end
