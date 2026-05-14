/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicExtension
import JacobianChallenge.Manifold.ContMDiffRealification
import JacobianChallenge.Manifold.SmoothPathCompSmooth
import JacobianChallenge.Manifold.SmoothChainPushforward

set_option linter.unusedSectionVars false

/-! # Real C^∞-smoothness of `MeromorphicNonzero.toRiemannSphere` + pushforward API

The pole-extension `f.toRiemannSphere : X → RiemannSphere` of a
`MeromorphicNonzero X` is unconditionally `ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ) ω`
(established in `Manifold/MeromorphicExtension.lean` via
`MeromorphicNonzero.toRiemannSphere_contMDiff`). Composing with the
function-level realification
`ContMDiff.complex_to_real` (this repo,
`Manifold/ContMDiffRealification.lean`) gives the C^∞-real version:

    `ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f.toRiemannSphere`

which is the regularity that `SmoothPath` / `SmoothChain`'s
pushforward primitives (`ContMDiff.compSmoothPath`,
`SmoothChain.compSmoothMap`) require.

## What this file delivers

* `MeromorphicNonzero.toRiemannSphere_contMDiff_real f` — the C^∞-real
  smoothness of the pole-extension.

* `MeromorphicNonzero.smoothPathPushforward f γ` — pushforward of a
  smooth path `γ : SmoothPath 𝓘(ℝ,ℂ) X` through `f.toRiemannSphere`,
  producing `SmoothPath 𝓘(ℝ,ℂ) RiemannSphere`.

* `MeromorphicNonzero.smoothChainPushforward f` — the linear pushforward
  on chains.

* `MeromorphicNonzero.boundary_smoothChainPushforward` — boundary
  commutes with the chain pushforward.

This is the infrastructure layer used by the C3 level-set chain
construction: given a meromorphic function `f` and a path `β` in
`RiemannSphere` (e.g., from 0 to ∞ in the affine chart), the
preimage `f^{-1}(β)` is constructed by lifting `β` to paths in `X`
via the inverse of `f.toRiemannSphere`. The pushforward direction
above is the "trivial" direction (X → RS); the pullback is the
non-trivial direction that needs additional work (lifting paths
through a non-injective holomorphic map).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **C^∞-real smoothness of the pole-extension.** Composes the
ω-complex smoothness `toRiemannSphere_contMDiff` (from
`MeromorphicExtension.lean`) with the function-level realification
`ContMDiff.complex_to_real` (from `ContMDiffRealification.lean`). -/
theorem toRiemannSphere_contMDiff_real (f : MeromorphicNonzero X) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      f.toRiemannSphere := by
  -- `𝓘(ℂ) = 𝓘(ℂ, ℂ)` definitionally; the holomorphic ContMDiff is at
  -- the complex model at level ω, which `ContMDiff.complex_to_real`
  -- downgrades to the real model at level ∞.
  have h_complex : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f.toRiemannSphere :=
    f.toRiemannSphere_contMDiff
  exact ContMDiff.complex_to_real h_complex

/-! ## Pushforward of paths through `f.toRiemannSphere` -/

/-- **Pushforward of a smooth path** through `f.toRiemannSphere`.
Given `γ : SmoothPath 𝓘(ℝ,ℂ) X`, produces
`SmoothPath 𝓘(ℝ,ℂ) RiemannSphere` whose endpoints are
`f.toRiemannSphere γ.src` and `f.toRiemannSphere γ.tgt`. -/
noncomputable def smoothPathPushforward (f : MeromorphicNonzero X)
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) :
    SmoothPath 𝓘(ℝ, ℂ) RiemannSphere :=
  f.toRiemannSphere_contMDiff_real.compSmoothPath γ

@[simp] lemma smoothPathPushforward_src (f : MeromorphicNonzero X)
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) :
    (f.smoothPathPushforward γ).src = f.toRiemannSphere γ.src := rfl

@[simp] lemma smoothPathPushforward_tgt (f : MeromorphicNonzero X)
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) :
    (f.smoothPathPushforward γ).tgt = f.toRiemannSphere γ.tgt := rfl

/-! ## Pushforward of chains through `f.toRiemannSphere` -/

/-- **ℤ-linear pushforward of a smooth chain** through
`f.toRiemannSphere`. -/
noncomputable def smoothChainPushforward (f : MeromorphicNonzero X) :
    SmoothChain 𝓘(ℝ, ℂ) X →ₗ[ℤ] SmoothChain 𝓘(ℝ, ℂ) RiemannSphere :=
  SmoothChain.compSmoothMap f.toRiemannSphere_contMDiff_real

/-- **Pushforward of a single-path chain.** -/
@[simp] lemma smoothChainPushforward_single (f : MeromorphicNonzero X)
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) :
    f.smoothChainPushforward (SmoothChain.single γ)
      = SmoothChain.single (f.smoothPathPushforward γ) :=
  SmoothChain.compSmoothMap_single f.toRiemannSphere_contMDiff_real γ

/-- **Boundary commutes with chain pushforward.** -/
theorem boundary_smoothChainPushforward (f : MeromorphicNonzero X)
    (c : SmoothChain 𝓘(ℝ, ℂ) X) :
    SmoothChain.boundary (f.smoothChainPushforward c)
      = Finsupp.mapDomain f.toRiemannSphere (SmoothChain.boundary c) :=
  SmoothChain.boundary_compSmoothMap f.toRiemannSphere_contMDiff_real c

end MeromorphicNonzero

end JacobianChallenge

end
