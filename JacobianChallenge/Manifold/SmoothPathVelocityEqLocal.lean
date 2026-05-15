/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import JacobianChallenge.Manifold.SmoothPathIntegral

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Local velocity, integrand, and integral equality from local ambient equality

If two smooth paths `γ γ' : SmoothPath I X` agree pointwise on a closed
interval `Icc s t`, then their velocities agree on the open interior
`Ioo s t` (via `Filter.EventuallyEq.mfderiv_eq`, since `Ioo s t` is an
open neighborhood of each interior point). Hence their integrands
against any smooth 1-form agree on `Ioo s t`, and their integrals over
`[s, t]` are equal.

This is the building block for piecewise chain-rule identifications:
on each subinterval of a Lebesgue subdivision adapted to a local-sheet
cover (`exists_subdivision_hurwitzPatching`), the level-set path locally
agrees with a chart pullback
(`sourceFiberPath_toPath_extend_eq_sheet_g_locally`); the integrals match
this lemma on each subinterval.

The proof template follows the same pattern as
`velocity_compSmoothPath_of_mem_Ioo` in
`SmoothPathCompSmoothIntegrate.lean`.

No `sorry`, no `axiom`. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace SmoothPath

/-! ## Eventually-equal ambient from `Icc` equality -/

/-- **Eventually-equal ambient** at `u ∈ Ioo s t` from pointwise equality on
`Icc s t`: `Ioo s t` is an open neighborhood of `u` contained in
`Icc s t`. -/
lemma ambient_eventuallyEq_of_eqOn_Icc
    {γ γ' : SmoothPath I X} {s t : ℝ}
    (heq : ∀ u, u ∈ Icc s t → γ.ambient u = γ'.ambient u)
    {u : ℝ} (hu : u ∈ Ioo s t) :
    γ.ambient =ᶠ[𝓝 u] γ'.ambient := by
  refine eventually_of_mem (IsOpen.mem_nhds isOpen_Ioo hu) ?_
  intro v hv
  exact heq v (Ioo_subset_Icc_self hv)

/-! ## Velocity equality on the interior -/

/-- **Velocity equality from local ambient equality.** Two smooth paths
agreeing on `Icc s t` have equal velocity at every interior point
`u ∈ Ioo s t`.

Follows the same template as `velocity_compSmoothPath_of_mem_Ioo`:
the locally-equal ambient via `Filter.EventuallyEq.mfderiv_eq` gives
equal `mfderiv`s, then apply to `1` and `cotangentEquiv`-coerce. -/
theorem velocity_eq_of_ambient_eqOn_Icc
    {γ γ' : SmoothPath I X} {s t : ℝ}
    (heq : ∀ u, u ∈ Icc s t → γ.ambient u = γ'.ambient u)
    {u : ℝ} (hu : u ∈ Ioo s t) :
    γ.velocity u = γ'.velocity u := by
  unfold velocity
  have h_eq : mfderiv (𝓘(ℝ, ℝ)) I γ.ambient u
      = mfderiv (𝓘(ℝ, ℝ)) I γ'.ambient u :=
    (ambient_eventuallyEq_of_eqOn_Icc heq hu).mfderiv_eq
  rw [h_eq]
  rfl

/-! ## Integrand equality on the interior -/

/-- **Integrand equality from local ambient equality.** Two smooth paths
agreeing on `Icc s t` have equal integrands `t ↦ ω(γ t)(γ' t)` on
`Ioo s t`. -/
theorem integrand_eq_of_ambient_eqOn_Icc
    {γ γ' : SmoothPath I X} {s t : ℝ}
    (heq : ∀ u, u ∈ Icc s t → γ.ambient u = γ'.ambient u)
    (ω : SmoothOneForm I X)
    {u : ℝ} (hu : u ∈ Ioo s t) :
    γ.integrand ω u = γ'.integrand ω u := by
  unfold integrand
  have h_pt : γ.ambient u = γ'.ambient u :=
    heq u (Ioo_subset_Icc_self hu)
  have h_vel : γ.velocity u = γ'.velocity u :=
    velocity_eq_of_ambient_eqOn_Icc heq hu
  rw [h_pt, h_vel]

/-! ## Integral equality on a closed subinterval -/

/-- **Integral equality from local ambient equality.** Two smooth paths
agreeing on `Icc s t` (with `s ≤ t`) have equal **integrals** of any
smooth 1-form `ω` over `[s, t]`. The endpoints `{s, t}` are
Lebesgue-null, so the open-interior integrand equality lifts to the
whole `[s, t]` integral via `intervalIntegral.integral_congr_ae`. -/
theorem intervalIntegral_integrand_eq_of_ambient_eqOn_Icc
    {γ γ' : SmoothPath I X} {s t : ℝ} (hst : s ≤ t)
    (heq : ∀ u, u ∈ Icc s t → γ.ambient u = γ'.ambient u)
    (ω : SmoothOneForm I X) :
    (∫ u in s..t, γ.integrand ω u) = ∫ u in s..t, γ'.integrand ω u := by
  -- Endpoints `{s, t}` are Lebesgue-null; the open interior `Ioo s t`
  -- has full measure inside `Ioc s t = Set.uIoc s t` (since `s ≤ t`).
  have h_ae_not_t : ∀ᵐ x ∂MeasureTheory.volume, x ≠ t := by
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨{t}ᶜ, ?_, fun x hx => hx⟩
    rw [MeasureTheory.mem_ae_iff, compl_compl]
    exact Real.volume_singleton
  have h_congr : ∀ᵐ u ∂MeasureTheory.volume,
      u ∈ Set.uIoc s t → γ.integrand ω u = γ'.integrand ω u := by
    filter_upwards [h_ae_not_t] with u hu_t hu_uIoc
    rw [Set.uIoc_of_le hst] at hu_uIoc
    -- `hu_uIoc : u ∈ Ioc s t`, so `s < u` directly; `u < t` from `u ≤ t ∧ u ≠ t`.
    have hu_in : u ∈ Ioo s t :=
      ⟨hu_uIoc.1, lt_of_le_of_ne hu_uIoc.2 hu_t⟩
    exact integrand_eq_of_ambient_eqOn_Icc heq ω hu_in
  exact intervalIntegral.integral_congr_ae h_congr

end SmoothPath

end
