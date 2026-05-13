/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LinearSystemGermDeltaP
import JacobianChallenge.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Dimension form of Riemann–Roch at `δp` on the germ field

This file is the germ-side counterpart of
`Topology/RRDimensionForm.lean`, with `linearSystemDeltaP : Submodule ℂ
(X → ℂ)` replaced by `linearSystemGermDeltaP : Submodule ℂ
(MeromorphicFunctionGerm X)`. Under the architectural rebuild flagged
in `OPEN.md`, this is the natural shape a Riemann-Roch chip will
produce on the honest germ ambient.

## What this chip delivers

* `constantsGerm X : Submodule ℂ (MeromorphicFunctionGerm X)` — the
  one-dimensional ℂ-subspace of *germ* constants, i.e.
  `Submodule.span ℂ {1}` in the germ field.
* `constantsGerm_le_linearSystemGermDeltaP` — constants embed into
  `L(δp)`.
* `finrank_constantsGerm_eq_one` — `dim ℂ (constantsGerm X) = 1` (uses
  the `Nontrivial (MeromorphicFunctionGerm X)` instance from the
  `Field` construction).
* `RR_DimGE2_GenusZero_Germ X : Prop` — the named hypothesis:
  `genus X = 0 → ∃ p, 2 ≤ finrank ℂ (linearSystemGermDeltaP p)`.
* `constantsGerm_lt_of_finrank_ge_two` — strict containment from
  `finrank ≥ 2`, i.e. `dim ≥ 2 ⇒ ∃ germ ∈ L(δp), germ ∉ constants`.

## What is *not* delivered (chip discipline)

The dimension hypothesis `RR_DimGE2_GenusZero_Germ` is the *named
classical input* — the heavy Riemann-Roch + Serre-duality content that
a future formula chip will discharge. This chip does *not* discharge
it; the positioning is on purpose, mirroring the existing pointwise
`RR_DimGE2_GenusZero` named hypothesis.

The extraction step "non-constant germ ⇒ `MeromorphicNonzero X`
representative" (the germ-side analog of `LiftToMeromorphicNonzero`,
which on the germ side collapses to picking a representative and
invoking the identity theorem proved in
`Manifold/MeromorphicFunctionField.lean`) is a separate follow-up chip.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge.MeromorphicFunctionField

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## The constants subspace of the germ field -/

/-- The one-dimensional ℂ-subspace of *germ* constants in
`MeromorphicFunctionGerm X`. Spanned by `1`. -/
def constantsGerm : Submodule ℂ (MeromorphicFunctionGerm X) :=
  Submodule.span ℂ ({(1 : MeromorphicFunctionGerm X)} :
    Set (MeromorphicFunctionGerm X))

/-- `1 ∈ constantsGerm`. -/
lemma one_mem_constantsGerm :
    (1 : MeromorphicFunctionGerm X) ∈ constantsGerm X :=
  Submodule.subset_span (Set.mem_singleton _)

/-- The constants are contained in `L(δp)` for any `p : X`. -/
lemma constantsGerm_le_linearSystemGermDeltaP (p : X) :
    constantsGerm X ≤ linearSystemGermDeltaP p := by
  -- `L(δp)` is a Submodule, contains `1`, hence contains the span of `{1}`.
  rw [constantsGerm]
  rw [Submodule.span_le]
  intro φ hφ
  rcases hφ with rfl
  exact one_mem_linearSystemGermDeltaP p

/-! ## `dim ℂ (constantsGerm X) = 1`

The germ field is non-trivial (`zero_ne_one_germ`, available via the
`Field` instance), so `1 ≠ 0` in `MeromorphicFunctionGerm X`. Then
`Submodule.span ℂ {1}` is one-dimensional via `finrank_span_singleton`. -/

/-- `(1 : MeromorphicFunctionGerm X) ≠ 0`. Direct from the `Field`
instance's nontriviality (which is the identity theorem upgrade of
`nhdsNE_neBot`). -/
lemma one_ne_zero_germ :
    (1 : MeromorphicFunctionGerm X) ≠ 0 := by
  intro h
  exact zero_ne_one h.symm

/-- The constants subspace of the germ field is one-dimensional. -/
theorem finrank_constantsGerm_eq_one :
    Module.finrank ℂ (constantsGerm X) = 1 := by
  rw [constantsGerm]
  exact finrank_span_singleton (one_ne_zero_germ X)

/-! ## `RR_DimGE2_GenusZero_Germ` and strict-containment -/

/-- **Named hypothesis (dimension form of RR at δp, genus 0, germ
field):** under `genus X = 0`, the linear system
`linearSystemGermDeltaP p` has ℂ-dimension at least 2 for some `p : X`.

This is the germ-side counterpart of
`JacobianChallenge.RR_DimGE2_GenusZero`. It is the natural shape the
classical Riemann-Roch formula `dim L(D) - dim L(K - D) = deg D + 1
- g` produces with `D = δp`, `deg D = 1`, `g = 0`, and Serre duality
`dim L(K - δp) = 0`. The hypothesis remains classical Riemann-Roch
content; discharging it is owed to a separate chip. -/
def RR_DimGE2_GenusZero_Germ : Prop :=
  JacobianChallenge.genus X = 0 →
  ∃ p : X, 2 ≤ Module.finrank ℂ (linearSystemGermDeltaP (X := X) p)

/-- **Strict containment of constants from `dim ≥ 2`.** If a submodule
has `finrank ≥ 2` and contains the 1-dim constants subspace, it
strictly contains constants — there is some non-constant germ in
`L(δp)`. -/
lemma constantsGerm_lt_of_finrank_ge_two {p : X}
    (h_ge_2 : 2 ≤ Module.finrank ℂ (linearSystemGermDeltaP (X := X) p)) :
    constantsGerm X < linearSystemGermDeltaP p := by
  refine lt_of_le_of_ne (constantsGerm_le_linearSystemGermDeltaP X p) ?_
  -- If equal, the finranks would have to coincide, but they don't (1 ≠ ≥ 2).
  intro h_eq
  have h_finrank_const : Module.finrank ℂ (constantsGerm X) = 1 :=
    finrank_constantsGerm_eq_one X
  rw [h_eq] at h_finrank_const
  -- `h_finrank_const : Module.finrank ℂ (linearSystemGermDeltaP p) = 1`,
  -- contradicting `h_ge_2`.
  omega

/-- **Forward direction:** the germ-side dimension form of RR implies
the strict-containment form (under `genus X = 0`). -/
theorem strict_lt_constantsGerm_le_linearSystemGermDeltaP_of_RR_DimGE2_Germ
    (hRR : RR_DimGE2_GenusZero_Germ X) :
    JacobianChallenge.genus X = 0 →
    ∃ p : X, constantsGerm X < linearSystemGermDeltaP (X := X) p := by
  intro hg
  obtain ⟨p, h_ge_2⟩ := hRR hg
  exact ⟨p, constantsGerm_lt_of_finrank_ge_two X h_ge_2⟩

/-! ## Existence of a non-constant germ in `L(δp)`

The strict-containment form unpacks to an explicit witness: a germ in
`L(δp)` that is not in `constantsGerm`. This is the germ-side
counterpart of zz357's
`exists_mem_linearSystem_not_in_constants_of_RR_DimGE2`. -/

/-- From `constantsGerm X < linearSystemGermDeltaP p`, extract an
explicit germ in `L(δp)` that is not a constant germ. -/
lemma exists_mem_linearSystemGermDeltaP_not_in_constantsGerm
    {p : X} (hlt : constantsGerm X < linearSystemGermDeltaP (X := X) p) :
    ∃ φ : MeromorphicFunctionGerm X,
      φ ∈ linearSystemGermDeltaP p ∧ φ ∉ constantsGerm X := by
  -- Strict `<` ⇒ there is a witness in the bigger set not in the smaller.
  rcases SetLike.exists_of_lt hlt with ⟨φ, hφ_in, hφ_not⟩
  exact ⟨φ, hφ_in, hφ_not⟩

/-- **Combined extraction:** under the germ-side dim hypothesis and
`genus X = 0`, there exists a non-constant germ in `L(δp)` for some
`p`. -/
theorem exists_mem_linearSystemGermDeltaP_not_constants_of_RR_DimGE2_Germ
    (hRR : RR_DimGE2_GenusZero_Germ X) (hg : JacobianChallenge.genus X = 0) :
    ∃ p : X, ∃ φ : MeromorphicFunctionGerm X,
      φ ∈ linearSystemGermDeltaP p ∧ φ ∉ constantsGerm X := by
  obtain ⟨p, hlt⟩ :=
    strict_lt_constantsGerm_le_linearSystemGermDeltaP_of_RR_DimGE2_Germ X hRR hg
  obtain ⟨φ, hφ_in, hφ_not⟩ :=
    exists_mem_linearSystemGermDeltaP_not_in_constantsGerm X hlt
  exact ⟨p, φ, hφ_in, hφ_not⟩

end JacobianChallenge.MeromorphicFunctionField

end
