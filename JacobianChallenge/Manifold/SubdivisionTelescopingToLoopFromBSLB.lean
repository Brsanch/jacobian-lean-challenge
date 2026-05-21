/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Item14ReverseLegFullAssembly
import JacobianChallenge.Manifold.LoopPeriodVanishesOfBasedSmoothLoopsBound

set_option linter.unusedSectionVars false

/-! # `SubdivisionTelescopingToLoop_named X` from universal `BasedSmoothLoopsBoundHypothesis`

The named hypothesis `SubdivisionTelescopingToLoop_named X` reduces to:
"for every smooth loop `γ`, its `complexChainPeriod` against any
holomorphic 1-form vanishes". This file ships the discharge of that
hypothesis under the **universal** form of `BasedSmoothLoopsBoundHypothesis`
— i.e. when *every* basepoint admits the based-loops-bound discharge.

This is a clean architectural reduction: the *single* remaining open
classical input for `SubdivisionTelescopingToLoop_named X` reduces to
the BSLB-at-every-basepoint hypothesis. BSLB itself is the smooth-
Hurewicz step (smooth bordism of every based loop to the constant),
and is discharged unconditionally on `RiemannSphere` (via missed-point
+ Möbius) and `ℂ` (via straight-line) in tree.

## What this file ships

* `subdivisionTelescopingToLoop_of_universal_bslb` — discharge of
  `SubdivisionTelescopingToLoop_named X` from
  `∀ p₀ : X, BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X p₀`. Routes via
  `loopPeriodVanishes_of_basedSmoothLoopsBoundHypothesis` per-basepoint,
  then the empty subdivision-list since each loop's period is `0`.

This reduces the remaining open content for item-14 reverse leg under
`[SimplyConnectedSpace X]` to **a single, unambiguously classical
hypothesis**: discharge BSLB at every basepoint of a simply-connected
compact connected complex 1-manifold.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`SubdivisionTelescopingToLoop_named X` from universal BSLB.**

If `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X p₀` holds for every
basepoint `p₀ : X`, then `SubdivisionTelescopingToLoop_named X` holds.

For any smooth loop `γ` with `γ.src = γ.tgt = p₀`, the period
`complexChainPeriod (single γ) α = 0` by
`loopPeriodVanishes_of_basedSmoothLoopsBoundHypothesis`. The empty
subdivision-list witnesses the `∃` since `0 = ([].map _).sum`. -/
theorem subdivisionTelescopingToLoop_of_universal_bslb
    (h_bslb : ∀ p₀ : X, BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X p₀) :
    SubdivisionTelescopingToLoop_named (X := X) := by
  intro _inst γ h_loop α
  refine ⟨[], ?_⟩
  -- Use BSLB at p₀ := γ.src.
  have h_period :
      complexChainPeriod (SmoothChain.single γ) α = 0 :=
    loopPeriodVanishes_of_basedSmoothLoopsBoundHypothesis
      (h_bslb γ.src) α γ rfl h_loop.symm
  rw [h_period]
  simp

end JacobianChallenge

end
