/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PathPrimitiveBasisReduction
import JacobianChallenge.Manifold.PrimitiveSubsingletonReduction
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option linter.unusedSectionVars false

/-! # Basis-wise reduction of `PathPrimitiveSmoothness`

By ℂ-linearity of `pathPrimitive`, the smoothness hypothesis extends
from a ℂ-spanning set to all forms.

`PathPrimitiveSmoothness` reduces to per-basis smoothness, so the
remaining open work is at most `genus X` individual smoothness checks
(one per basis element of `HolomorphicOneForm X`).

(The matching FTC basis-reduction is deferred — the `mfderiv_add` /
`mfderiv_const_smul` API around the `ω`-smoothness level requires
slightly different plumbing than the smoothness case.)

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology ContDiff
open Module

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

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

end JacobianChallenge

end
