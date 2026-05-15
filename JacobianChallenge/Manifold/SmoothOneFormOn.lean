/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothOneForm

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Smooth 1-forms on an open subset

`SmoothOneFormOn I X s` is the type of smooth 1-form sections of the
cotangent bundle of `X` defined and smooth on a subset `s : Set X`.

Unlike the global `SmoothOneForm I X` (defined as a
`ContMDiffSection` of the cotangent bundle), the smoothness witness
here is `ContMDiffOn ... s`. The total-space lift of the section is
required to be `C^∞` on `s` only; outside `s`, the underlying function
`(x : X) → CotangentSpace I x` may take arbitrary (junk) values.

This is the prerequisite type for the **trace `f_*ω`** of a meromorphic
function `f` evaluated as a 1-form on `regularValueSet f` (an open
subset of `RiemannSphere`). Subsequent chips will:

* Show `f_*ω` (built from `Manifold/MeromorphicNonzeroTraceAt.lean`'s
  pointwise `traceAt`) is a `SmoothOneFormOn 𝓘(ℝ, ℂ) RiemannSphere
  (regularValueSet f)`.
* Define `SmoothPath.integrateOn` for paths landing in the partial
  domain, enabling `∫_β (f_*ω) dβ`.

This file ships only the **type definition** and basic `CoeFun`
instance. Algebra (`AddCommGroup`, `Module ℝ`) and the restriction
relation `(restrictOn : SmoothOneForm I X → SmoothOneFormOn I X s)` are
deferred to later chips.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (X : Type*) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]
  (s : Set X)

/-- **Smooth 1-form on a subset.** A function `toFun : ∀ x, CotangentSpace I x`
together with a proof that the total-space lift `x ↦ ⟨x, toFun x⟩` is
`ContMDiffOn` on `s`. Outside `s`, the value of `toFun` is unconstrained. -/
structure SmoothOneFormOn where
  /-- The underlying function-valued section. -/
  toFun : ∀ x : X, CotangentSpace I x
  /-- The smoothness witness on `s`. -/
  contMDiffOn_section : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ⊤
    (fun x : X => @Bundle.TotalSpace.mk X (E →L[ℝ] ℝ) (CotangentSpace I) x (toFun x)) s

namespace SmoothOneFormOn

variable {I X s}

instance instCoeFun : CoeFun (SmoothOneFormOn I X s)
    (fun _ => ∀ x : X, CotangentSpace I x) :=
  ⟨SmoothOneFormOn.toFun⟩

@[simp] lemma coeFun_mk
    (f : ∀ x : X, CotangentSpace I x)
    (hf : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ⊤
      (fun x : X => @Bundle.TotalSpace.mk X (E →L[ℝ] ℝ) (CotangentSpace I) x (f x)) s) :
    (mk f hf : ∀ x : X, CotangentSpace I x) = f := rfl

end SmoothOneFormOn

end
