/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LinearSystemDeltaP
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Dimension.Free

set_option diagnostics.threshold 100

/-! # Constants subspace of `linearSystemDeltaP p`

Every constant function `(fun _ => c) : X → ℂ` is in `L(δp)` (zz352's
`IsBoundedByDeltaP.const`). The ℂ-linear span of the constant
function `1` is therefore a sub-Submodule of `linearSystemDeltaP p`.
This file ships:

* `constants_subspace_le_linearSystemDeltaP` — the inclusion as
  `Submodule`s.

* `one_mem_linearSystemDeltaP` — `(1 : X → ℂ) ∈ linearSystemDeltaP p`.

* `constant_function_mem_linearSystemDeltaP` — generalisation:
  every `c : ℂ` constant is in `L(δp)`.

These wire the elementary fact "constants live in `L(δp)`" — the
trivial 1-dimensional subspace — to the rest of the Riemann-Roch
infrastructure. The "dim `L(δp)` ≥ 2 at genus 0" content
(zz346's `ExistsNonConstantBoundedByDeltaP_GenusZero X`) then
literally asserts that `L(δp)` *strictly contains* the constants
subspace.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **`(1 : X → ℂ) ∈ linearSystemDeltaP p`.** -/
lemma one_mem_linearSystemDeltaP (p : X) :
    (1 : X → ℂ) ∈ linearSystemDeltaP p := by
  rw [mem_linearSystemDeltaP]
  -- 1 : X → ℂ is the constant function 1.
  -- Need `IsBoundedByDeltaP p (1 : X → ℂ)`.
  -- The `1` for `X → ℂ` is `fun _ => 1`.
  have h_eq : (1 : X → ℂ) = (fun _ : X => (1 : ℂ)) := rfl
  rw [h_eq]
  exact IsBoundedByDeltaP.const p 1

/-- **Every constant function is in `linearSystemDeltaP p`.** -/
lemma constant_function_mem_linearSystemDeltaP (p : X) (c : ℂ) :
    (fun _ : X => c) ∈ linearSystemDeltaP p := by
  rw [mem_linearSystemDeltaP]
  exact IsBoundedByDeltaP.const p c

/-- **The ℂ-span of the constant function 1 sits inside
`linearSystemDeltaP p`.** -/
theorem constants_subspace_le_linearSystemDeltaP (p : X) :
    (Submodule.span ℂ ({(1 : X → ℂ)} : Set (X → ℂ)))
      ≤ linearSystemDeltaP p := by
  rw [Submodule.span_le]
  intro f hf
  rw [Set.mem_singleton_iff] at hf
  rw [hf]
  exact one_mem_linearSystemDeltaP p

/-- **Bridge: `L(δp)` properly contains constants iff there is a
non-constant element.** This is the linear-algebra form of zz346's
`ExistsNonConstantBoundedByDeltaP_GenusZero` existence statement. -/
theorem linearSystemDeltaP_strictly_gt_constants_iff_exists_non_constant
    (p : X) :
    (Submodule.span ℂ ({(1 : X → ℂ)} : Set (X → ℂ)))
        < linearSystemDeltaP p ↔
    ∃ f ∈ linearSystemDeltaP p, f ∉ Submodule.span ℂ ({(1 : X → ℂ)} : Set (X → ℂ)) := by
  refine ⟨?_, ?_⟩
  · intro hlt
    rcases SetLike.lt_iff_le_and_exists.mp hlt with ⟨_hle, ⟨f, hf_in_L, hf_nin_const⟩⟩
    exact ⟨f, hf_in_L, hf_nin_const⟩
  · intro ⟨f, hf_in_L, hf_nin_const⟩
    refine lt_of_le_of_ne (constants_subspace_le_linearSystemDeltaP p) ?_
    intro h_eq
    -- If constants = L(δp), then f ∈ L(δp) ⇒ f ∈ constants, contradicting hf_nin_const.
    apply hf_nin_const
    rw [h_eq]
    exact hf_in_L

end JacobianChallenge

end
