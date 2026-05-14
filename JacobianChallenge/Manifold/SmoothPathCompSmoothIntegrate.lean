/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import JacobianChallenge.Manifold.SmoothPathCompSmooth
import JacobianChallenge.Manifold.SmoothPathIntegral
import JacobianChallenge.Manifold.SmoothPathIntegrability

set_option linter.unusedSectionVars false

/-! # Pushforward path integral via chain rule

For a `C^∞` map `f : X → Y` and a smooth path `γ : SmoothPath I X`, the
pushforward path `f.compSmoothPath γ : SmoothPath I' Y` (defined in
`Manifold/SmoothPathCompSmooth.lean`) integrates a 1-form `ω : SmoothOneForm
I' Y` via the chain-rule identity:

    `(hf.compSmoothPath γ).integrate ω
      = ∫ t in 0..1, applyCotangent (ω (f (γ.ambient t)))
                                     (mfderiv f (γ.ambient t) (γ.velocity t))`.

The RHS is the path integral of the "pullback 1-form" `f^*ω` along `γ`,
without explicitly constructing `f^*ω` as a `SmoothOneForm I X`. Useful
toward the C3 level-set chain construction: when `f = MeromorphicNonzero
g.toRiemannSphere`, paths in `X` push to paths in `RiemannSphere`, and
period integrals on `RS` relate to the period integrals of the AJ chain on
`X` via this chain-rule identity.

## What this file delivers

* `SmoothPath.compSmoothPath_ambient_eq_on_unitInterval` — pointwise
  ambient identity: `(hf.compSmoothPath γ).ambient s = f (γ.ambient s)`
  on `s ∈ unitInterval`.

* `SmoothPath.compSmoothPath_ambient_eventuallyEq` — eventually-equal on
  `Ioo 0 1`.

* `SmoothPath.velocity_compSmoothPath_of_mem_Ioo` — velocity identity
  `(hf.compSmoothPath γ).velocity t = mfderiv f (γ.ambient t)
   (γ.velocity t)` on `Ioo 0 1`.

* `SmoothPath.integrand_compSmoothPath_of_mem_Ioo` — integrand identity
  on `Ioo 0 1`.

* `SmoothPath.integrate_compSmoothPath` — the integral identity.

No `sorry`, no `axiom`. -/

noncomputable section

open MeasureTheory Set Filter Topology Function
open scoped Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ⊤ Y]

namespace SmoothPath

/-! ## Pointwise ambient identity -/

/-- **On `unitInterval`, the Classical-chosen ambient of the pushforward
path equals `f ∘ γ.ambient`.** Both project to
`γ.toPath.map hf.continuous` via `ambient_eq_on_unitInterval`. -/
lemma compSmoothPath_ambient_eq_on_unitInterval {f : X → Y}
    (hf : ContMDiff I I' ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (γ : SmoothPath I X) (s : ℝ) (hs : s ∈ unitInterval) :
    (hf.compSmoothPath γ).ambient s = f (γ.ambient s) := by
  have h_eq_push :=
    (hf.compSmoothPath γ).ambient_eq_on_unitInterval ⟨s, hs⟩
  have h_val : (⟨s, hs⟩ : unitInterval).val = s := rfl
  rw [h_val] at h_eq_push
  rw [h_eq_push]
  -- The underlying continuous path of `hf.compSmoothPath γ` is
  -- `γ.toPath.map hf.continuous`, whose value at `⟨s, hs⟩` is
  -- `f (γ.toPath ⟨s, hs⟩) = f (γ.ambient s)` by `Path.map`.
  show (γ.toPath.map hf.continuous) ⟨s, hs⟩ = f (γ.ambient s)
  -- `Path.map γ h ⟨s, hs⟩ = h ∘ γ ⟨s, hs⟩ = f (γ.toPath ⟨s, hs⟩)`.
  show f (γ.toPath ⟨s, hs⟩) = f (γ.ambient s)
  congr 1
  have h_fwd := γ.ambient_eq_on_unitInterval ⟨s, hs⟩
  rw [h_val] at h_fwd
  exact h_fwd.symm

/-! ## Eventually-equal on `Ioo 0 1` -/

/-- **On `Ioo 0 1`, the pushforward ambient locally equals
`f ∘ γ.ambient`.** -/
lemma compSmoothPath_ambient_eventuallyEq {f : X → Y}
    (hf : ContMDiff I I' ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (γ : SmoothPath I X) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    (hf.compSmoothPath γ).ambient =ᶠ[𝓝 t] (fun s : ℝ => f (γ.ambient s)) := by
  refine eventually_of_mem (IsOpen.mem_nhds isOpen_Ioo ht) ?_
  intro s hs
  exact compSmoothPath_ambient_eq_on_unitInterval hf γ s
    ⟨le_of_lt hs.1, le_of_lt hs.2⟩

/-! ## Velocity identity on `Ioo 0 1` -/

/-- **Pushforward velocity on `Ioo 0 1`.** Via `Filter.EventuallyEq.mfderiv_eq`
and `mfderiv_comp_apply` (chain rule):
`(hf.compSmoothPath γ).velocity t = mfderiv f (γ.ambient t) (γ.velocity t)`. -/
lemma velocity_compSmoothPath_of_mem_Ioo {f : X → Y}
    (hf : ContMDiff I I' ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (γ : SmoothPath I X) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (hf.compSmoothPath γ).velocity t
      = mfderiv I I' f (γ.ambient t) (γ.velocity t) := by
  unfold velocity
  have h_eq : mfderiv (𝓘(ℝ, ℝ)) I' (hf.compSmoothPath γ).ambient t
      = mfderiv (𝓘(ℝ, ℝ)) I' (fun s : ℝ => f (γ.ambient s)) t :=
    (compSmoothPath_ambient_eventuallyEq hf γ ht).mfderiv_eq
  rw [h_eq]
  -- Chain rule for `f ∘ γ.ambient`.
  have h_amb_diff : MDifferentiableAt (𝓘(ℝ, ℝ)) I γ.ambient t :=
    (γ.ambient_contMDiff t).mdifferentiableAt (by decide)
  have h_f_diff : MDifferentiableAt I I' f (γ.ambient t) :=
    (hf (γ.ambient t)).mdifferentiableAt (by decide)
  show ((mfderiv (𝓘(ℝ, ℝ)) I' (f ∘ γ.ambient) t :
          ℝ →L[ℝ] TangentSpace I' (f (γ.ambient t))) (1 : ℝ))
        = (mfderiv I I' f (γ.ambient t))
            ((mfderiv (𝓘(ℝ, ℝ)) I γ.ambient t :
              ℝ →L[ℝ] TangentSpace I (γ.ambient t)) (1 : ℝ))
  exact mfderiv_comp_apply t h_f_diff h_amb_diff (1 : ℝ)

/-! ## Integrand identity on `Ioo 0 1` -/

/-- **Pushforward integrand on `Ioo 0 1`.** Composes the ambient and
velocity identities through `applyCotangent`. -/
lemma integrand_compSmoothPath_of_mem_Ioo {f : X → Y}
    (hf : ContMDiff I I' ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (γ : SmoothPath I X) (om : SmoothOneForm I' Y) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    (hf.compSmoothPath γ).integrand om t
      = applyCotangent (om (f (γ.ambient t)))
          (mfderiv I I' f (γ.ambient t) (γ.velocity t)) := by
  unfold integrand
  rw [compSmoothPath_ambient_eq_on_unitInterval hf γ t
        ⟨le_of_lt ht.1, le_of_lt ht.2⟩]
  rw [velocity_compSmoothPath_of_mem_Ioo hf γ ht]

/-! ## The integral identity -/

/-- **Pushforward path integral via chain rule.**
`(hf.compSmoothPath γ).integrate ω = ∫ t in 0..1,
   applyCotangent (ω (f (γ.ambient t)))
                  (mfderiv f (γ.ambient t) (γ.velocity t))`.

The integrand identity holds almost-everywhere on `Ι 0 1 = Ioc 0 1`:
the endpoint singleton `{1}` (Lebesgue-null, by
`Real.volume_singleton`) is excluded from `Ioo 0 1`. Apply
`intervalIntegral.integral_congr_ae`. -/
theorem integrate_compSmoothPath {f : X → Y}
    (hf : ContMDiff I I' ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (γ : SmoothPath I X) (om : SmoothOneForm I' Y) :
    (hf.compSmoothPath γ).integrate om
      = ∫ t in (0 : ℝ)..1, applyCotangent (om (f (γ.ambient t)))
          (mfderiv I I' f (γ.ambient t) (γ.velocity t)) := by
  unfold integrate
  have h_meas_one : MeasureTheory.volume ({1} : Set ℝ) = 0 :=
    Real.volume_singleton
  have h_almost : ∀ᵐ x ∂MeasureTheory.volume, x ≠ (1 : ℝ) := by
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨{1}ᶜ, ?_, fun x hx => hx⟩
    rw [MeasureTheory.mem_ae_iff, compl_compl]
    exact h_meas_one
  have h_congr : ∀ᵐ x ∂MeasureTheory.volume,
      x ∈ Set.uIoc (0 : ℝ) 1 →
        (hf.compSmoothPath γ).integrand om x
          = applyCotangent (om (f (γ.ambient x)))
              (mfderiv I I' f (γ.ambient x) (γ.velocity x)) := by
    filter_upwards [h_almost] with x hx hx_uIoc
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx_uIoc
    exact integrand_compSmoothPath_of_mem_Ioo hf γ om
      ⟨hx_uIoc.1, lt_of_le_of_ne hx_uIoc.2 hx⟩
  rw [intervalIntegral.integral_congr_ae h_congr]

end SmoothPath

end
