/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothChain

set_option linter.unusedSectionVars false

/-! # Pushforward of `SmoothPath` along a smooth map

For a smooth map `f : X → Y` between smooth manifolds (with shared
model `I`), the **pushforward** of a `SmoothPath I X` along `f` is the
`SmoothPath I Y` given by composing the path with `f`:

  `f_* γ := ⟨f γ.src, f γ.tgt, γ.toPath.map f.continuous, ...⟩`.

The smoothness witness is obtained by composing the original path's
ambient smooth function with `f`.

## Net contribution

* `SmoothPath.push f hf : SmoothPath I X → SmoothPath I Y`
  (functorial pushforward at the path level).
* `SmoothPath.push_src`, `SmoothPath.push_tgt` — endpoint identities.

These are the building blocks for `SmoothChain.push` (Finsupp-linear
extension) and `SmoothCycle.push` (preservation of boundary).
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ⊤ Y]

/-- **Pushforward of a smooth path along a smooth map.** For `f : X → Y`
with `ContMDiff I I ∞ f`, and `γ : SmoothPath I X`, the pushforward
`f_* γ : SmoothPath I Y` is `f ∘ γ` with all endpoints and smoothness
inherited via composition. -/
noncomputable def SmoothPath.push
    (f : X → Y) (hf : ContMDiff I I ∞ f) (γ : SmoothPath I X) :
    SmoothPath I Y where
  src := f γ.src
  tgt := f γ.tgt
  toPath := γ.toPath.map (by
    -- `f` is continuous since it is `ContMDiff`.
    exact hf.continuous)
  smooth := by
    -- Lift the original smoothness witness.
    obtain ⟨g, hg_smooth, hg_eq⟩ := γ.smooth
    refine ⟨f ∘ g, ?_, ?_⟩
    · exact hf.comp hg_smooth
    · intro t
      -- `f ∘ g (t.val) = f (g t.val) = f (γ.toPath t) = (γ.toPath.map f.continuous) t`.
      show f (g t.val) = (γ.toPath.map hf.continuous) t
      rw [hg_eq t]
      -- `(γ.toPath.map cont) t = cont.toFun (γ.toPath t)` essentially.
      rfl

@[simp] theorem SmoothPath.push_src
    (f : X → Y) (hf : ContMDiff I I ∞ f) (γ : SmoothPath I X) :
    (SmoothPath.push f hf γ).src = f γ.src := rfl

@[simp] theorem SmoothPath.push_tgt
    (f : X → Y) (hf : ContMDiff I I ∞ f) (γ : SmoothPath I X) :
    (SmoothPath.push f hf γ).tgt = f γ.tgt := rfl

end JacobianChallenge

end
