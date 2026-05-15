/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathVelocityEqLocal

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Velocity / integrand identification against an external function

Extends the `SmoothPath.velocity_eq_of_ambient_eqOn_Icc` primitive (from
`SmoothPathVelocityEqLocal.lean`) to compare a smooth path's velocity
**against an external function** `f : ℝ → X`, given pointwise
ambient-equals-function on a closed interval.

Use site: `sourceFiberPath x` locally equals `sheet.g ∘ β ∘ σ` on a
sub-interval `[0, δ]` (via
`sourceFiberPath_toPath_extend_eq_sheet_g_locally`); the velocity of
`sourceFiberPath x` on `Ioo 0 δ` then matches the `mfderiv` of
`sheet.g ∘ β ∘ σ`. This is the per-fiber-point chain-rule entry point.

No `sorry`, no `axiom`. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace SmoothPath

/-! ## Ambient eventually-equal an external function -/

/-- **Eventually-equal an external function** at `u ∈ Ioo s t` from
pointwise equality on `Icc s t`. -/
lemma ambient_eventuallyEq_fun_of_eqOn_Icc
    (γ : SmoothPath I X) (f : ℝ → X) {s t : ℝ}
    (heq : ∀ u, u ∈ Icc s t → γ.ambient u = f u)
    {u : ℝ} (hu : u ∈ Ioo s t) :
    γ.ambient =ᶠ[𝓝 u] f := by
  refine eventually_of_mem (IsOpen.mem_nhds isOpen_Ioo hu) ?_
  intro v hv
  exact heq v (Ioo_subset_Icc_self hv)

/-! ## Velocity equals `mfderiv` of the external function -/

/-- **Velocity equals `mfderiv` of the external function** at every
interior point. Same template as
`velocity_eq_of_ambient_eqOn_Icc`, comparing `γ.velocity u` against
`(mfderiv f u) 1`. -/
theorem velocity_eq_mfderiv_of_ambient_eqOn_Icc
    {γ : SmoothPath I X} {f : ℝ → X} {s t : ℝ}
    (heq : ∀ u, u ∈ Icc s t → γ.ambient u = f u)
    {u : ℝ} (hu : u ∈ Ioo s t) :
    γ.velocity u
      = (mfderiv (𝓘(ℝ, ℝ)) I f u : ℝ →L[ℝ] TangentSpace I (f u)) (1 : ℝ) := by
  unfold velocity
  have h_eq : mfderiv (𝓘(ℝ, ℝ)) I γ.ambient u
      = mfderiv (𝓘(ℝ, ℝ)) I f u :=
    (γ.ambient_eventuallyEq_fun_of_eqOn_Icc f heq hu).mfderiv_eq
  rw [h_eq]
  rfl

/-! ## Integrand equals chain-pull through `f` -/

/-- **Integrand identification against an external function.** At every
interior point `u ∈ Ioo s t`, the integrand `t ↦ ω(γ t)(γ' t)` of `γ`
equals `applyCotangent (ω (f u)) ((mfderiv f u) 1)`. -/
theorem integrand_eq_of_ambient_eqOn_Icc_fun
    {γ : SmoothPath I X} {f : ℝ → X} {s t : ℝ}
    (heq : ∀ u, u ∈ Icc s t → γ.ambient u = f u)
    (ω : SmoothOneForm I X)
    {u : ℝ} (hu : u ∈ Ioo s t) :
    γ.integrand ω u
      = applyCotangent (ω (f u))
          ((mfderiv (𝓘(ℝ, ℝ)) I f u : ℝ →L[ℝ] TangentSpace I (f u)) (1 : ℝ)) := by
  unfold integrand
  have h_pt : γ.ambient u = f u := heq u (Ioo_subset_Icc_self hu)
  have h_vel := velocity_eq_mfderiv_of_ambient_eqOn_Icc heq hu
  rw [h_pt, h_vel]

/-! ## Integral on `[s, t]` equals integral of the chain-pull -/

/-- **Integral on `[s, t]` equals integral against the external
function.** The endpoint singletons are Lebesgue-null. -/
theorem intervalIntegral_integrand_eq_of_ambient_eqOn_Icc_fun
    {γ : SmoothPath I X} {f : ℝ → X} {s t : ℝ} (hst : s ≤ t)
    (heq : ∀ u, u ∈ Icc s t → γ.ambient u = f u)
    (ω : SmoothOneForm I X) :
    (∫ u in s..t, γ.integrand ω u)
      = ∫ u in s..t, applyCotangent (ω (f u))
          ((mfderiv (𝓘(ℝ, ℝ)) I f u : ℝ →L[ℝ] TangentSpace I (f u)) (1 : ℝ)) := by
  have h_ae_not_t : ∀ᵐ x ∂MeasureTheory.volume, x ≠ t := by
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨{t}ᶜ, ?_, fun x hx => hx⟩
    rw [MeasureTheory.mem_ae_iff, compl_compl]
    exact Real.volume_singleton
  have h_congr : ∀ᵐ u ∂MeasureTheory.volume,
      u ∈ Set.uIoc s t → γ.integrand ω u
        = applyCotangent (ω (f u))
            ((mfderiv (𝓘(ℝ, ℝ)) I f u : ℝ →L[ℝ] TangentSpace I (f u)) (1 : ℝ)) := by
    filter_upwards [h_ae_not_t] with u hu_t hu_uIoc
    rw [Set.uIoc_of_le hst] at hu_uIoc
    have hu_in : u ∈ Ioo s t :=
      ⟨hu_uIoc.1, lt_of_le_of_ne hu_uIoc.2 hu_t⟩
    exact integrand_eq_of_ambient_eqOn_Icc_fun heq ω hu_in
  exact intervalIntegral.integral_congr_ae h_congr

end SmoothPath

end
