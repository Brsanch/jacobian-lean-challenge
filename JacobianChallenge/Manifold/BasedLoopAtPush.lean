/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathPush
import JacobianChallenge.Manifold.ConcatListBasedLoopHomology

set_option linter.unusedSectionVars false

/-! # Pushforward of `BasedLoopAt` along a smooth map

For a smooth map `f : X → Y` between smooth manifolds (shared model
`I`) and a smooth based loop `γ : BasedLoopAt I X p₀`, the **pushforward**
`f_* γ : BasedLoopAt I Y (f p₀)` is the composite `f ∘ γ`, packaged as a
based loop at `f p₀`. Lifts the existing `SmoothPath.push` to the
basepoint-preserving subtype.

## Headline use

When `f = L.mkQ : ℂ → ℂ ⧸ L` and `p₀ = 0`, this lets us push smooth
based loops from `ℂ` to the complex torus `T_L = ℂ ⧸ L` while preserving
the basepoint at the zero class.

## What this file ships

* `BasedLoopAt.push f hf γ` — pushforward of a `BasedLoopAt I X p₀`
  along `f : X → Y` smooth, producing `BasedLoopAt I Y (f p₀)`.
* `BasedLoopAt.push_toPath` — the underlying `SmoothPath` is
  `SmoothPath.push f hf γ.toPath`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ⊤ Y]

namespace BasedLoopAt

/-- **Pushforward of a `BasedLoopAt` along a smooth map.** -/
noncomputable def push (f : X → Y) (hf : ContMDiff I I ∞ f)
    {p₀ : X} (γ : BasedLoopAt I X p₀) :
    BasedLoopAt I Y (f p₀) :=
  ⟨SmoothPath.push f hf γ.toPath, by
    refine ⟨?_, ?_⟩
    · rw [SmoothPath.push_src]; exact congrArg f γ.toPath_src
    · rw [SmoothPath.push_tgt]; exact congrArg f γ.toPath_tgt⟩

@[simp] lemma push_toPath (f : X → Y) (hf : ContMDiff I I ∞ f)
    {p₀ : X} (γ : BasedLoopAt I X p₀) :
    (γ.push f hf).toPath = SmoothPath.push f hf γ.toPath := rfl

end BasedLoopAt

end JacobianChallenge

end
