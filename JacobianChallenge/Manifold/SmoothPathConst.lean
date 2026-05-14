/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothChain

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Smooth-path-connectedness primitive 1: constant self-loop

First piece in the smooth-path-connectedness sub-arc (toward discharging
`AbelJacobiInput` existence in
`Manifold/AbelJacobiPoint.lean`). Builds the simplest `SmoothPath`:
the constant self-loop at a given point.

## What this file delivers

* `SmoothPath.const I X P : SmoothPath I X` — the constant path at `P`,
  with `src = tgt = P`, underlying `Path.refl P`, and smoothness witness
  `(fun _ ↦ P)` (the constantly-`P` ambient function).

* `SmoothPath.const_src` / `SmoothPath.const_tgt` — endpoint
  identities.

This primitive is the base case for the inductive construction of
smooth paths between any two points on a compact connected complex
1-manifold. It serves as the `Nonempty (SmoothPath I X)` witness when
`X` is nonempty.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace JacobianChallenge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (X : Type*) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

/-- **The constant smooth path** at a point `P : X`. Has `src = tgt = P`,
underlying continuous path `Path.refl P`, and the constant function
`(fun _ : ℝ ↦ P)` as smooth ambient. -/
noncomputable def SmoothPath.const (P : X) : SmoothPath I X where
  src := P
  tgt := P
  toPath := Path.refl P
  smooth := by
    refine ⟨fun _ : ℝ => P, ?_, ?_⟩
    · -- ContMDiff of a constant function is automatic.
      exact contMDiff_const
    · -- Agreement on unitInterval: both sides return P.
      intro t
      rfl

variable {I X}

@[simp] lemma SmoothPath.const_src (P : X) :
    (SmoothPath.const I X P).src = P := rfl

@[simp] lemma SmoothPath.const_tgt (P : X) :
    (SmoothPath.const I X P).tgt = P := rfl

/-! ## `Nonempty (SmoothPath I X)` from `Nonempty X` -/

/-- **`SmoothPath I X` is nonempty whenever `X` is.** Witnessed by
the constant path at any point of `X`. -/
instance SmoothPath.instNonempty [Nonempty X] : Nonempty (SmoothPath I X) :=
  ⟨SmoothPath.const I X (Classical.arbitrary X)⟩

end JacobianChallenge

end
