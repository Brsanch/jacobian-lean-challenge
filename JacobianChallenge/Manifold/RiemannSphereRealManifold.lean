/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphere
import JacobianChallenge.Manifold.ComplexManifoldRealification
import JacobianChallenge.Manifold.ContMDiffRealification

set_option diagnostics.threshold 100

/-! # Real C^∞ manifold structure on `RiemannSphere` + open-set realification

`RiemannSphere = OnePoint ℂ` carries a holomorphic atlas via `chartN` and
`chartS`, giving `IsManifold 𝓘(ℂ, ℂ) ω RiemannSphere`. Composing this
with `complexManifoldRealification`
(`Manifold/ComplexManifoldRealification.lean`) downgrades to
`IsManifold 𝓘(ℝ, ℂ) n RiemannSphere` for any regularity `n`.

This file:

* Documents the auto-derived real-model instance via `inferInstance`
  examples — these confirm the typeclass resolution chains
  `RiemannSphere.instIsManifold` (complex-analytic ω) →
  `complexManifoldRealification` (generic conversion) →
  `IsManifold 𝓘(ℝ, ℂ) n RiemannSphere`.

* Provides `ContMDiffOn.complex_to_real_of_isOpen`: a sister lemma to
  the existing pointwise `ContMDiffAt.complex_to_real` and global
  `ContMDiff.complex_to_real` (in `Manifold/ContMDiffRealification.lean`),
  generalised to **smoothness on an open subset**. This is the
  workhorse for downstream constructions that consume the
  complex-analytic local-inverse smoothness
  (`exists_contMDiffOn_localSheet_g_near_basePoint`) and need the
  real-smooth version for `SmoothOneForm`-style sections.

These are the prerequisite layer for `SmoothOneForm 𝓘(ℝ, ℂ) RiemannSphere`
and downstream constructions (`f_*ω` trace on `regularValueSet`, period
pairing on `ℙ¹`, etc.).

No `sorry`, no `axiom`. -/

open Set Filter
open scoped Manifold ContDiff Topology

namespace JacobianChallenge

namespace RiemannSphere

/-! ## Real C^∞ manifold instances on `RiemannSphere`

These are inherited from the holomorphic atlas via
`complexManifoldRealification`. We expose them via `inferInstance`
examples so that downstream files have a discoverable reference
point. -/

example (n : WithTop ℕ∞) : IsManifold 𝓘(ℝ, ℂ) n RiemannSphere :=
  inferInstance

example : IsManifold 𝓘(ℝ, ℂ) ∞ RiemannSphere := inferInstance

example : IsManifold 𝓘(ℝ, ℂ) ⊤ RiemannSphere := inferInstance

end RiemannSphere

/-! ## Open-set realification of `ContMDiffOn`

Sister to `ContMDiffAt.complex_to_real` (pointwise) and
`ContMDiff.complex_to_real` (global) in
`Manifold/ContMDiffRealification.lean`. -/

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-- **Open-set realification.** If `f : X → Y` is holomorphic
(`ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω`) on an *open* subset `u`, then it is
C^∞-real (`ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞`) on the same `u`.

This is the workhorse for converting the smoothness witnesses produced
by local-sheet infrastructure (e.g.,
`exists_contMDiffOn_localSheet_g_near_basePoint`) into the regularity
required by `SmoothOneForm 𝓘(ℝ, ℂ) X` pullbacks. -/
theorem ContMDiffOn.complex_to_real_of_isOpen {f : X → Y} {u : Set X}
    (hu : IsOpen u)
    (hf : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f u) :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f u := by
  intro x hx
  have h_at_complex : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f x :=
    hf.contMDiffAt (hu.mem_nhds hx)
  have h_at_real : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f x :=
    ContMDiffAt.complex_to_real h_at_complex
  exact h_at_real.contMDiffWithinAt

end JacobianChallenge
