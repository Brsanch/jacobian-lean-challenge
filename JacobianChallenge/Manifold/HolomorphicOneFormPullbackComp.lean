/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackGeneral

set_option linter.unusedSectionVars false

/-! # Composition functoriality of `HolomorphicOneForm.pullback`

For composable smooth maps `g : Y → X` and `f : Z → Y` between
complex 1-manifolds, the pullback respects composition contravariantly:

  `(g ∘ f)^* α = f^* (g^* α)`

for every `α : HolomorphicOneForm X`.

Proof: pointwise at `z : Z`, both sides reduce to
`(α (g (f z))) ∘ mfderiv (g ∘ f) z`, using the chain rule
`mfderiv (g ∘ f) z = mfderiv g (f z) ∘ mfderiv f z`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

namespace HolomorphicOneForm

variable {X Y Z : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
  [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ, ℂ) ω Z]

/-- Pointwise pullback respects composition contravariantly. -/
theorem holCotangentPullbackAt_comp
    (g : Y → X) (hg : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g)
    (f : Z → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (z : Z) (α : HolomorphicOneForm X) :
    holCotangentPullbackAt (g ∘ f) z α
      = holCotangentPullbackAt f z (pullback g hg α) := by
  -- Unfold both sides.
  show (α.toFun ((g ∘ f) z)).comp
      (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (g ∘ f) z)
    = ((pullback g hg α).toFun (f z)).comp
        (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) f z)
  -- RHS pullback unfold.
  rw [pullback_apply g hg α (f z)]
  show (α.toFun ((g ∘ f) z)).comp
      (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (g ∘ f) z)
    = (holCotangentPullbackAt g (f z) α).comp
        (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) f z)
  show (α.toFun ((g ∘ f) z)).comp
      (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (g ∘ f) z)
    = ((α.toFun (g (f z))).comp
        (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) g (f z))).comp
        (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) f z)
  -- Chain rule for `mfderiv`. `ω ≠ 0` lets `ContMDiff.mdifferentiable` fire.
  have h_chain : mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (g ∘ f) z
      = (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) g (f z)).comp
          (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) f z) :=
    mfderiv_comp z (hg.mdifferentiable (by decide) (f z))
      (hf.mdifferentiable (by decide) z)
  rw [h_chain]
  -- After the rewrite both sides are identical; closes by `rfl`.
  rfl

/-- **Composition functoriality of pullback.** -/
theorem pullback_comp
    (g : Y → X) (hg : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g)
    (f : Z → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (α : HolomorphicOneForm X) :
    pullback (g ∘ f) (hg.comp hf) α
      = pullback f hf (pullback g hg α) := by
  apply ContMDiffSection.ext
  intro z
  show (pullback (g ∘ f) (hg.comp hf) α).toFun z
    = (pullback f hf (pullback g hg α)).toFun z
  rw [pullback_apply, pullback_apply]
  exact holCotangentPullbackAt_comp g hg f hf z α

/-- **Composition functoriality of `pullbackLinearMap`.** -/
theorem pullbackLinearMap_comp
    (g : Y → X) (hg : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g)
    (f : Z → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) :
    pullbackLinearMap (g ∘ f) (hg.comp hf)
      = (pullbackLinearMap f hf).comp (pullbackLinearMap g hg) := by
  ext α
  show pullback (g ∘ f) (hg.comp hf) α = pullback f hf (pullback g hg α)
  exact pullback_comp g hg f hf α

end HolomorphicOneForm

end JacobianChallenge

end
