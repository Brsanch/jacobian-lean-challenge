/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothChain

set_option linter.unusedSectionVars false

/-! # Extensionality for `SmoothPath`

`SmoothPath I X` is a structure with fields `src`, `tgt`, `toPath`,
and `smooth` (the last being a `Prop`-valued existential). Two
smooth paths are equal iff their src/tgt agree AND their underlying
`Path`'s `toFun` agrees pointwise. This file ships the corresponding
`SmoothPath.ext` lemma.

## Proof sketch

By case-analysis on both `SmoothPath` terms, we reduce to equality
of structure-mk-form with matching src/tgt fields and the requirement
that the `toPath` fields agree (an equation between two `Path`s with
the same endpoints). `Path.ext` from mathlib closes this from the
pointwise-toFun equality. The `smooth` field is `Prop` (existential
over the ambient witness), so proof-irrelevant.

## What this file ships

* `SmoothPath.ext` — the extensionality lemma.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-- **Extensionality of `SmoothPath`.** Two smooth paths are equal
iff they have the same endpoints and their underlying continuous
paths agree pointwise on `unitInterval`. -/
@[ext]
theorem SmoothPath.ext {γ₁ γ₂ : SmoothPath I X}
    (h_src : γ₁.src = γ₂.src) (h_tgt : γ₁.tgt = γ₂.tgt)
    (h_path : ∀ t : unitInterval, γ₁.toPath t = γ₂.toPath t) :
    γ₁ = γ₂ := by
  obtain ⟨src₁, tgt₁, p₁, s₁⟩ := γ₁
  obtain ⟨src₂, tgt₂, p₂, s₂⟩ := γ₂
  -- After destructuring, h_src/h_tgt are equalities between the
  -- exposed src/tgt fields.
  cases h_src
  cases h_tgt
  -- Now both terms are SmoothPath.mk with the SAME src and tgt.
  -- Path equality reduces to function equality (Path.ext).
  congr 1
  apply Path.ext
  funext t
  exact h_path t

end JacobianChallenge

end
