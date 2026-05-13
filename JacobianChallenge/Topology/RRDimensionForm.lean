/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.ExistenceBridge
import JacobianChallenge.Topology.ConstantsFinrank
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

set_option diagnostics.threshold 100

/-! # Dimension form of the Riemann-Roch existence hypothesis

This file ships the *dimension form* of zz346's
`ExistsNonConstantBoundedByDeltaP_GenusZero X` content:

  `RR_DimGE2_GenusZero X` :=
    `genus X = 0 → ∃ p, 2 ≤ Module.finrank ℂ (linearSystemDeltaP p)`

This is the natural shape a Riemann-Roch formula chip will produce
(via `dim L(D) - dim L(K - D) = deg D + 1 - g` with `D = δp`,
`deg D = 1`, `g = 0`, and Serre duality `dim L(K - δp) = 0`).

We prove the forward direction:

  `RR_DimGE2_GenusZero X → ∃ p, constants < linearSystemDeltaP p`

This combined with zz354/zz355 chains back to the **strict-gt** form,
positioning a future RR-formula chip to plug into the closure chain.

The fully circular equivalence
`RR_DimGE2_GenusZero ↔ ExistsNonConstantBoundedByDeltaP_GenusZero`
requires the nonvanishing-germ globalisation in the reverse direction
(extending a `g : X → ℂ` in `L(δp)` to a `MeromorphicNonzero X`),
a separate substantive chip.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Named hypothesis (dimension form of RR at δp, genus 0):**
under `genus X = 0`, the linear system `L(δp)` has ℂ-dimension at
least 2 for some `p : X`. -/
def RR_DimGE2_GenusZero : Prop :=
  JacobianChallenge.genus X = 0 →
  ∃ p : X, 2 ≤ Module.finrank ℂ (linearSystemDeltaP p)

set_option linter.unusedSectionVars false

/-- **Strict containment of constants from `dim ≥ 2`.** If a
submodule has `finrank ≥ 2` and contains a 1-dim subspace, then it
strictly contains that 1-dim subspace. -/
lemma constants_lt_of_finrank_ge_two [Nonempty X] {p : X}
    (h_ge_2 : 2 ≤ Module.finrank ℂ (linearSystemDeltaP p)) :
    (Submodule.span ℂ ({(1 : X → ℂ)} : Set (X → ℂ))) < linearSystemDeltaP p := by
  -- Constants ≤ linearSystemDeltaP (zz354).
  refine lt_of_le_of_ne (constants_subspace_le_linearSystemDeltaP p) ?_
  -- And ≠ because their finranks differ: constants has finrank 1, L(δp) has ≥ 2.
  intro h_eq
  have h_finrank_const : Module.finrank ℂ
      (Submodule.span ℂ ({(1 : X → ℂ)} : Set (X → ℂ))) = 1 :=
    finrank_span_one_eq_one (X := X)
  -- After h_eq the two finranks must agree, but 1 ≠ ≥ 2.
  rw [h_eq] at h_finrank_const
  -- h_finrank_const : Module.finrank ℂ (linearSystemDeltaP p) = 1.
  -- h_ge_2 : 2 ≤ Module.finrank ℂ (linearSystemDeltaP p).
  omega

/-- **Forward direction:** the dimension form of RR implies the
strict-containment form. -/
theorem strict_lt_constants_le_linearSystemDeltaP_of_RR_DimGE2
    [Nonempty X]
    (hRR : RR_DimGE2_GenusZero X) :
    JacobianChallenge.genus X = 0 →
    ∃ p : X, (Submodule.span ℂ ({(1 : X → ℂ)} : Set (X → ℂ)))
      < linearSystemDeltaP p := by
  intro hg
  obtain ⟨p, h_ge_2⟩ := hRR hg
  exact ⟨p, constants_lt_of_finrank_ge_two X h_ge_2⟩

end JacobianChallenge

end
