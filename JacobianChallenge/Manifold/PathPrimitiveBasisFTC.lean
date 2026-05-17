/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PathPrimitiveBasisReduction
import JacobianChallenge.Manifold.PrimitiveSubsingletonReduction
import JacobianChallenge.Manifold.HolomorphicOneFormRealificationLinearity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

set_option linter.unusedSectionVars false

/-! # Basis-wise reduction of `PathPrimitiveSmoothness` and `PathPrimitiveFTC`

By ℂ-linearity of `pathPrimitive`, both the smoothness hypothesis and
the FTC hypothesis extend from a ℂ-spanning set to all forms.

`PathPrimitiveSmoothness` and `PathPrimitiveFTC` reduce to per-basis
versions, so the remaining open work is at most `2 · genus X`
individual analytic checks (one smoothness + one FTC per basis element
of `HolomorphicOneForm X`).

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology ContDiff
open Module

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

private theorem analytic_ne_zero : (ω : WithTop ℕ∞) ≠ 0 := by
  intro h; exact absurd h (by decide)

/-- **`PathPrimitiveSmoothness` reduces to a basis-wise check.** If
`x ↦ pathPrimitive om x` is `ContMDiff ω` for each basis element `b i`,
then for every form (by ℂ-linearity). -/
theorem pathPrimitiveSmoothness_of_basis
    [FiniteDimensional ℂ (HolomorphicOneForm X)]
    {ι : Type*} (b : Basis ι ℂ (HolomorphicOneForm X))
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X) (x₀ : X)
    (h_b : ∀ i, ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (pathPrimitive h_conn x₀ (b i))) :
    PathPrimitiveSmoothness h_conn x₀ := by
  intro om
  have hmem : om ∈ Submodule.span ℂ (Set.range b) := by
    rw [b.span_eq]; trivial
  refine Submodule.span_induction
    (p := fun v _ => ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (pathPrimitive h_conn x₀ v))
    (mem := ?_) (zero := ?_) (add := ?_) (smul := ?_) hmem
  · rintro _ ⟨i, rfl⟩
    exact h_b i
  · show ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (pathPrimitive h_conn x₀ 0)
    rw [pathPrimitive_zero]
    exact contMDiff_const
  · intros v₁ v₂ _ _ hv₁ hv₂
    rw [pathPrimitive_add]
    exact hv₁.add hv₂
  · intros c v _ hv
    rw [pathPrimitive_smul]
    -- ContMDiff (fun x => c * pathPrimitive v x) via ContMDiff.smul (= ContMDiff.mul on ℂ).
    have h_smul : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
        (fun y => (fun _ : X => c) y • pathPrimitive h_conn x₀ v y) :=
      contMDiff_const.smul hv
    exact h_smul

/-- **`PathPrimitiveFTC` reduces to a basis-wise check.** If for each
basis element `b i` the FTC identity `(b i).eval x = mfderiv (pathPrimitive
(b i)) x` holds and each `pathPrimitive (b i)` is `ContMDiff ω`, then the
FTC identity holds for every holomorphic 1-form (by ℂ-linearity, using
`mfderiv_add` and `const_smul_mfderiv` on differentiable summands). -/
theorem pathPrimitiveFTC_of_basis
    [FiniteDimensional ℂ (HolomorphicOneForm X)]
    {ι : Type*} (b : Basis ι ℂ (HolomorphicOneForm X))
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X) (x₀ : X)
    (h_smooth_b : ∀ i, ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (pathPrimitive h_conn x₀ (b i)))
    (h_ftc_b : ∀ i, ∀ x, (b i).eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
      (pathPrimitive h_conn x₀ (b i)) x) :
    PathPrimitiveFTC h_conn x₀ := by
  -- Lift basis smoothness to all-forms smoothness via the smoothness chip.
  have h_smooth : PathPrimitiveSmoothness h_conn x₀ :=
    pathPrimitiveSmoothness_of_basis b h_conn x₀ h_smooth_b
  intro om x
  -- Span-induction on om.
  have hmem : om ∈ Submodule.span ℂ (Set.range b) := by
    rw [b.span_eq]; trivial
  refine Submodule.span_induction
    (p := fun v _ => v.eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
      (pathPrimitive h_conn x₀ v) x)
    (mem := ?_) (zero := ?_) (add := ?_) (smul := ?_) hmem
  · rintro _ ⟨i, rfl⟩
    exact h_ftc_b i x
  · -- zero case: (0).eval x = 0 and pathPrimitive 0 is the zero function.
    show (0 : HolomorphicOneForm X).eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (pathPrimitive h_conn x₀ (0 : HolomorphicOneForm X)) x
    rw [HolomorphicOneForm.eval_zero, pathPrimitive_zero, mfderiv_const]
    rfl
  · -- add case: split eval via eval_add, split mfderiv via mfderiv_add.
    intros v₁ v₂ _ _ hv₁ hv₂
    rw [HolomorphicOneForm.eval_add, hv₁, hv₂, pathPrimitive_add]
    have hmd1 : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (pathPrimitive h_conn x₀ v₁) x :=
      (h_smooth v₁).mdifferentiableAt analytic_ne_zero
    have hmd2 : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (pathPrimitive h_conn x₀ v₂) x :=
      (h_smooth v₂).mdifferentiableAt analytic_ne_zero
    have hfun : (fun y => pathPrimitive h_conn x₀ v₁ y
        + pathPrimitive h_conn x₀ v₂ y)
        = pathPrimitive h_conn x₀ v₁ + pathPrimitive h_conn x₀ v₂ :=
      funext fun _ => rfl
    rw [hfun, mfderiv_add hmd1 hmd2]
    rfl
  · -- smul case: split eval via eval_smul, split mfderiv via const_smul_mfderiv.
    intros c v _ hv
    rw [HolomorphicOneForm.eval_smul, hv, pathPrimitive_smul]
    have hmd : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (pathPrimitive h_conn x₀ v) x :=
      (h_smooth v).mdifferentiableAt analytic_ne_zero
    have hfun : (fun y => c * pathPrimitive h_conn x₀ v y)
        = c • pathPrimitive h_conn x₀ v := by
      funext y
      show c * _ = c • _
      rw [smul_eq_mul]
    rw [hfun, const_smul_mfderiv hmd]
    rfl

end JacobianChallenge

end
