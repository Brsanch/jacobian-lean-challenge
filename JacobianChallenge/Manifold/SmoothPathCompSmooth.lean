/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothChain
import JacobianChallenge.Manifold.SmoothPathIntegral

set_option linter.unusedSectionVars false

/-! # `SmoothPath` pushforward by a smooth map

Functorial composition primitive: given a smooth path `γ : SmoothPath
I X` and a C^∞ map `f : X → Y` between manifolds (with their own
model `I'` on `Y`, possibly distinct from `I`), produces a smooth
path `f.compSmoothPath γ : SmoothPath I' Y` from `f γ.src` to
`f γ.tgt`.

The construction is the natural one: the underlying continuous path
is `γ.toPath.map hf.continuous` (mathlib's `Path.map`), and the
ambient extension is `f ∘ γ.ambient : ℝ → Y`, which is C^∞ as the
composition of two C^∞ maps. Agreement on `unitInterval` follows
from `γ.ambient_eq_on_unitInterval` plus the `Path.map` definition.

## What this file delivers

* `ContMDiff.compSmoothPath f hf γ : SmoothPath I' Y` — the
  pushforward of `γ : SmoothPath I X` by a C^∞ map `f : X → Y`.
* `ContMDiff.compSmoothPath_src` / `_tgt` — endpoint identities.

## Use cases

* Pulling back paths from `RiemannSphere` through `f.toRiemannSphere`
  for `f : MeromorphicNonzero X`: lifts paths in `RS` to paths in
  `X` (via the inverse map on smooth points, sub-chip ahead).
* Constructing the AJ chain image of a smooth chain under a smooth
  map between Riemann surfaces.
* Functorial reasoning about smooth-path-connectedness.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ⊤ Y]

namespace ContMDiff

/-- **`SmoothPath` pushforward by a C^∞ map.** Given `γ : SmoothPath I
X` and `hf : ContMDiff I I' ∞ f` for `f : X → Y`, produces a
`SmoothPath I' Y` from `f γ.src` to `f γ.tgt`. The underlying
continuous path is `γ.toPath.map hf.continuous`, and the C^∞ ambient
is `f ∘ γ.ambient`. -/
noncomputable def compSmoothPath {f : X → Y}
    (hf : ContMDiff I I' ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (γ : SmoothPath I X) :
    SmoothPath I' Y where
  src := f γ.src
  tgt := f γ.tgt
  toPath := γ.toPath.map hf.continuous
  smooth := by
    refine ⟨f ∘ γ.ambient, ?_, ?_⟩
    · -- `f ∘ γ.ambient` is C^∞ as composition of two C^∞ maps.
      intro t
      have h_amb : ContMDiffAt 𝓘(ℝ, ℝ) I ((⊤ : ℕ∞) : WithTop ℕ∞)
          γ.ambient t := γ.ambient_contMDiff t
      have h_f : ContMDiffAt I I' ((⊤ : ℕ∞) : WithTop ℕ∞)
          f (γ.ambient t) := hf (γ.ambient t)
      exact h_f.comp t h_amb
    · -- Agreement on unitInterval: `(f ∘ γ.ambient) t.val =
      -- f (γ.ambient t.val) = f (γ.toPath t) = γ.toPath.map h t`.
      intro t
      show f (γ.ambient t.val) = (γ.toPath.map hf.continuous) t
      rw [γ.ambient_eq_on_unitInterval t]
      -- Goal: `f (γ.toPath t) = (γ.toPath.map hf.continuous) t`.
      -- `Path.map` is defined so this is `rfl`.
      rfl

@[simp] lemma compSmoothPath_src {f : X → Y}
    (hf : ContMDiff I I' ((⊤ : ℕ∞) : WithTop ℕ∞) f) (γ : SmoothPath I X) :
    (hf.compSmoothPath γ).src = f γ.src := rfl

@[simp] lemma compSmoothPath_tgt {f : X → Y}
    (hf : ContMDiff I I' ((⊤ : ℕ∞) : WithTop ℕ∞) f) (γ : SmoothPath I X) :
    (hf.compSmoothPath γ).tgt = f γ.tgt := rfl

end ContMDiff

end
