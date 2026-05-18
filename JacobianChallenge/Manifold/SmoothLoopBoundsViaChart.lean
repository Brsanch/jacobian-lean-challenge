/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothLoopBoundsInVectorSpace
import JacobianChallenge.Manifold.Smooth2SimplexPush

set_option linter.unusedSectionVars false

/-! # Smooth loops factor-bound via a chart-style smooth map

**Headline.** For any smooth manifold `X` (modelled on `H` with model
`I : ModelWithCorners ℝ E H`), any normed ℝ-vector space `V` with the
same chart space (i.e., the manifold structure on `V` matches the
chart pattern), and any smooth map `f : V → X`:

```
For any smooth loop γ' : SmoothPath 𝓘(ℝ, V) V (γ'.src = γ'.tgt),
  single (SmoothPath.push f hf γ') ∈ stokesBoundaries 𝓘(ℝ, V) X.
```

Wait — note that `SmoothPath.push` requires both source and target to
have the **same** model `I` (mathlib's `IsManifold I ⊤ Y`), but here
the source has model `𝓘(ℝ, V)` and the target `X` has model `I`. So
we can't directly apply `SmoothPath.push f hf` between them.

The **right framing** for the chart-based S² lift is therefore:

```
If both X and V can be viewed as manifolds modelled on the SAME
ModelWithCorners 𝓘(ℝ, V) (with chart space V), then a smooth map
f : V → X pushes the V-bounded 2-chain into a 2-chain in X bounding
single (SmoothPath.push f hf γ').
```

For the Riemann sphere `RS`, this means viewing both `ℂ` and `RS` as
manifolds modelled on `𝓘(ℝ, ℂ)` (which `RS` is, as a real 2-manifold
modelled on `ℂ`). With this match, the smooth chart inverse
`φ⁻¹ : ℂ → RS \ {q} ⊆ RS` becomes a `ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞`
map (total, since φ⁻¹ is defined on all of ℂ for a stereographic
chart), and the push framework applies directly.

## What this file ships

* `single_pushSmoothLoop_in_stokesBoundaries_of_vectorSpaceSource` —
  for any smooth loop γ' in V (where V is a chart space) and smooth
  map f : V → X (both modelled on `𝓘(ℝ, V)`), the push `f ∘ γ'` has
  `single (push f hf γ') ∈ stokesBoundaries 𝓘(ℝ, V) X`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {X : Type*} [TopologicalSpace X] [ChartedSpace V X]
  [IsManifold 𝓘(ℝ, V) ⊤ X]

/-- **Pushed smooth loops bound.**

Given a smooth loop `γ' : SmoothPath 𝓘(ℝ, V) V` in a normed
vector space `V` and a smooth map `f : V → X` (both with model
`𝓘(ℝ, V)`), the `single` of the pushed loop `SmoothPath.push f hf γ'`
lies in `stokesBoundaries 𝓘(ℝ, V) X`.

Proof: apply `single_smoothLoop_in_stokesBoundaries_vectorSpace` to
get `single γ' ∈ stokesBoundaries V` (packaged as a SmoothCycle),
then push via `stokesBoundaries_push`. The push of a single is the
single of the pushed path, so the conclusion follows. -/
theorem single_pushSmoothLoop_in_stokesBoundaries_of_vectorSpaceSource
    (γ' : SmoothPath 𝓘(ℝ, V) V) (h_loop : γ'.src = γ'.tgt)
    (f : V → X) (hf : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, V) ∞ f) :
    single_smoothLoop_smoothCycle (SmoothPath.push f hf γ') (by
      simp [h_loop])
      ∈ stokesBoundaries 𝓘(ℝ, V) X := by
  -- Step 1: V-loop-bounds gives single γ' ∈ stokesBoundaries V.
  have h_V : single_smoothLoop_smoothCycle γ' h_loop
        ∈ stokesBoundaries 𝓘(ℝ, V) V :=
    single_smoothLoop_in_stokesBoundaries_vectorSpace γ' h_loop
  -- Step 2: push to X.
  have h_pushed :
      SmoothCycle.pushHom f hf (single_smoothLoop_smoothCycle γ' h_loop)
        ∈ stokesBoundaries 𝓘(ℝ, V) X :=
    stokesBoundaries_push f hf _ h_V
  -- Step 3: show the pushed cycle equals
  -- `single_smoothLoop_smoothCycle (push f hf γ') _`.
  have h_eq :
      SmoothCycle.pushHom f hf (single_smoothLoop_smoothCycle γ' h_loop)
        = single_smoothLoop_smoothCycle (SmoothPath.push f hf γ') (by
          simp [h_loop]) := by
    apply Subtype.ext
    show SmoothChain.push f hf
            (single_smoothLoop_smoothCycle γ' h_loop : SmoothChain 𝓘(ℝ, V) V)
        = (single_smoothLoop_smoothCycle (SmoothPath.push f hf γ') _
            : SmoothChain 𝓘(ℝ, V) X)
    rw [single_smoothLoop_smoothCycle_coe γ' h_loop,
        single_smoothLoop_smoothCycle_coe (SmoothPath.push f hf γ')]
    rw [SmoothChain.push_single]
  rw [← h_eq]
  exact h_pushed

end JacobianChallenge

end
