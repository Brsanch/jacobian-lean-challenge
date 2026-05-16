/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.Basic
import JacobianChallenge.Manifold.ComplexManifoldRealification

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Realification of `mfderiv` at the function-application level

For `g : X → Y` between complex 1-manifolds (modelled on `ℂ` via
`𝓘(ℂ, ℂ) ω`), the **realified manifold derivative** `mfderiv 𝓘(ℝ, ℂ) g x`
and the **holomorphic manifold derivative** `mfderiv 𝓘(ℂ, ℂ) g x` agree
when applied to any tangent vector `w : ℂ`.

This bypasses the formal type-distinction `TangentSpace 𝓘(ℂ, ℂ) x` vs
`TangentSpace 𝓘(ℝ, ℂ) x` (both unfold to `ℂ` but `TangentSpace` is
**not reducible** by mathlib design, per the comment in
`Mathlib/Geometry/Manifold/IsManifold/Basic.lean:1037`).

## Synth hazard

`DifferentiableAt.restrictScalars`'s auto-synth for `IsScalarTower ℝ ℂ ℂ`
**fails** at the call site — Lean's discrimination tree for the
implicit instance argument never tries `IsScalarTower.right`, only
`Complex.instIsScalarTowerOfReal` (which fails with `?m ≟ ℂ` second-arg
unification) and `NonUnitalSeminormedRing.isBoundedSMul` (a red herring
for `IsBoundedSMul`, not `IsScalarTower`). Even a `haveI` providing the
instance doesn't fire — synth doesn't search hypotheses for this
specific position.

Workaround: pass the instance explicitly via `@DifferentiableAt.restrictScalars`
with all implicit args supplied. The same workaround is needed for
`HasFDerivAt.restrictScalars` and similar.

## Application

For the holomorphic-side trace identity `realPartCLM
(holCotangentPullbackAt g v α) = cotangentPullbackAt g v (realComponent α)`,
the substantive content reduces to this `mfderiv` application identity.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Manifold Topology ContDiff

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-- Manually-constructed `IsScalarTower ℝ ℂ ℂ`. Mathlib synth doesn't
find this in `restrictScalars`-call contexts (see synth-hazard note in
the file docstring), so we pass it explicitly to `@`-applied lemmas. -/
private def isScalarTower_R_C_C : IsScalarTower ℝ ℂ ℂ :=
  ⟨fun (r : ℝ) (c c' : ℂ) => by
    show (r • c) • c' = r • c • c'
    rw [smul_assoc]⟩

/-- Wrapper for `DifferentiableAt.restrictScalars ℝ` with explicit
`IsScalarTower ℝ ℂ ℂ` instance. -/
private theorem differentiableAt_restrictScalars_R_C_C
    {f : ℂ → ℂ} {x : ℂ} (h : DifferentiableAt ℂ f x) :
    DifferentiableAt ℝ f x :=
  @DifferentiableAt.restrictScalars ℝ _ ℂ _ _ ℂ _ _ _ isScalarTower_R_C_C
    ℂ _ _ _ isScalarTower_R_C_C _ _ h

/-- Wrapper for `HasFDerivAt.restrictScalars ℝ` with explicit
`IsScalarTower ℝ ℂ ℂ` instance. `ContinuousLinearMap.restrictScalars`
argument order is `A M₁ M₂ R …`; our case is `A=ℂ, M₁=ℂ, M₂=ℂ, R=ℝ`. -/
private theorem hasFDerivAt_restrictScalars_R_C_C
    {f : ℂ → ℂ} {f' : ℂ →L[ℂ] ℂ} {x : ℂ} (h : HasFDerivAt f f' x) :
    HasFDerivAt f
      (@ContinuousLinearMap.restrictScalars ℂ ℂ ℂ ℝ _ _ _ _ _ _ _ _ _ _ _ f') x :=
  @HasFDerivAt.restrictScalars ℝ _ ℂ _ _ ℂ _ _ _ isScalarTower_R_C_C
    ℂ _ _ _ isScalarTower_R_C_C _ _ _ h

/-- The chart-pullback function `writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x g`
and `writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) x g` agree as `ℂ → ℂ` functions.
Both reduce to `chartAt ℂ (g x) ∘ g ∘ (chartAt ℂ x).symm`. -/
private theorem writtenInExtChartAt_complex_eq_real
    (g : X → Y) (x : X) :
    writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x g
      = writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) x g := by
  funext z
  show (extChartAt 𝓘(ℂ, ℂ) (g x)) (g ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
    = (extChartAt 𝓘(ℝ, ℂ) (g x)) (g ((extChartAt 𝓘(ℝ, ℂ) x).symm z))
  have h_ext_c_x : ⇑(extChartAt 𝓘(ℂ, ℂ) x).symm = ⇑(chartAt ℂ x).symm := by
    funext w; simp
  have h_ext_r_x : ⇑(extChartAt 𝓘(ℝ, ℂ) x).symm = ⇑(chartAt ℂ x).symm := by
    funext w; simp
  have h_ext_c_gx : ⇑(extChartAt 𝓘(ℂ, ℂ) (g x)) = ⇑(chartAt ℂ (g x)) := by
    funext w; simp
  have h_ext_r_gx : ⇑(extChartAt 𝓘(ℝ, ℂ) (g x)) = ⇑(chartAt ℂ (g x)) := by
    funext w; simp
  rw [h_ext_c_x, h_ext_r_x, h_ext_c_gx, h_ext_r_gx]

/-- `(extChartAt 𝓘(ℂ, ℂ) x) x = (extChartAt 𝓘(ℝ, ℂ) x) x`. -/
private theorem extChartAt_apply_complex_eq_real (x : X) :
    (extChartAt 𝓘(ℂ, ℂ) x) x = (extChartAt 𝓘(ℝ, ℂ) x) x := by
  have h_c : ⇑(extChartAt 𝓘(ℂ, ℂ) x) = ⇑(chartAt ℂ x) := by funext w; simp
  have h_r : ⇑(extChartAt 𝓘(ℝ, ℂ) x) = ⇑(chartAt ℂ x) := by funext w; simp
  rw [h_c, h_r]

/-- **ℂ-`MDifferentiableAt` implies ℝ-`MDifferentiableAt`.** -/
theorem MDifferentiableAt.complex_to_real
    {g : X → Y} {x : X}
    (hg : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g x) :
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g x := by
  rw [mdifferentiableAt_iff] at hg ⊢
  obtain ⟨h_cont, h_diff_c⟩ := hg
  refine ⟨h_cont, ?_⟩
  simp only [ModelWithCorners.range_eq_univ, differentiableWithinAt_univ] at h_diff_c ⊢
  rw [← writtenInExtChartAt_complex_eq_real g x,
      ← extChartAt_apply_complex_eq_real x]
  exact differentiableAt_restrictScalars_R_C_C h_diff_c

/-- **Application-level realification of `mfderiv`.**

For `g : X → Y` ℂ-differentiable at `x`, applying `mfderiv 𝓘(ℝ, ℂ) g x`
to `w : ℂ` gives the same `ℂ`-value as applying `mfderiv 𝓘(ℂ, ℂ) g x`
to `w`. -/
theorem mfderiv_complex_to_real_apply
    {g : X → Y} {x : X}
    (hg : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g x) (w : ℂ) :
    ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g x) w : ℂ)
      = ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g x) w : ℂ) := by
  -- ℝ-mdifferentiability (downward).
  have hg_r : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g x :=
    MDifferentiableAt.complex_to_real hg
  -- Express both mfderivs as fderivWithins.
  have h_eq_c : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g x
      = fderivWithin ℂ (writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x g)
          (range 𝓘(ℂ, ℂ)) ((extChartAt 𝓘(ℂ, ℂ) x) x) := hg.mfderiv
  have h_eq_r : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g x
      = fderivWithin ℝ (writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) x g)
          (range 𝓘(ℝ, ℂ)) ((extChartAt 𝓘(ℝ, ℂ) x) x) := hg_r.mfderiv
  -- range 𝓘 = univ ⇒ fderivWithin _ _ univ = fderiv _.
  simp only [ModelWithCorners.range_eq_univ, fderivWithin_univ] at h_eq_c h_eq_r
  -- Identify chart-pullback + chart application point across models.
  rw [← writtenInExtChartAt_complex_eq_real g x,
      ← extChartAt_apply_complex_eq_real x] at h_eq_r
  -- Function-level chart pullback at chart point.
  set f := writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x g with hf_def
  set z := (extChartAt 𝓘(ℂ, ℂ) x) x with hz_def
  -- ℂ-differentiability of f at z.
  have h_diff_c : DifferentiableAt ℂ f z := by
    have h_dwa := hg.differentiableWithinAt_writtenInExtChartAt
    simp only [ModelWithCorners.range_eq_univ, differentiableWithinAt_univ] at h_dwa
    exact h_dwa
  -- ℝ-fderiv = restrictScalars of ℂ-fderiv.
  have h_has_c : HasFDerivAt f (fderiv ℂ f z) z := h_diff_c.hasFDerivAt
  have h_has_r := hasFDerivAt_restrictScalars_R_C_C h_has_c
  have h_restrictScalars := h_has_r.fderiv
  -- Combine.
  rw [h_eq_r, h_eq_c, h_restrictScalars]
  rfl

end JacobianChallenge

end
