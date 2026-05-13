/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.RRDimensionForm

set_option diagnostics.threshold 100

/-! # `RR_DimGE2_GenusZero` ⇒ `∃ g ∈ L(δp), g ∉ constants`

Existence-of-non-constant-element form of the Riemann-Roch
dimensional hypothesis. Composes zz354's strict-gt-iff-exists with
zz357's finrank-bound-implies-strict-gt into a direct one-step
result.

The output is `∃ p, ∃ g : X → ℂ, g ∈ linearSystemDeltaP p ∧ g ∉
Submodule.span ℂ {(1 : X → ℂ)}` — the **plain-function** non-
constant L(δp)-existence statement. (The remaining gap to zz346's
`ExistsNonConstantBoundedByDeltaP_GenusZero X` is the lifting of
this `g : X → ℂ` to a `MeromorphicNonzero X`, which requires the
identity theorem for analytic functions plus a chart-redefinition
argument to ensure the `regular_continuousAt` field.)

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`RR_DimGE2_GenusZero` ⇒ `∃ p, ∃ g ∈ L(δp), g ∉ constants`.**

Direct composition: zz357 says finrank ≥ 2 gives strict containment,
zz354 says strict containment is equivalent to existence of a
non-constant element. -/
theorem exists_mem_linearSystem_not_in_constants_of_RR_DimGE2
    [Nonempty X]
    (hRR : RR_DimGE2_GenusZero X) :
    JacobianChallenge.genus X = 0 →
    ∃ p : X, ∃ g : X → ℂ,
      g ∈ linearSystemDeltaP p ∧
      g ∉ Submodule.span ℂ ({(1 : X → ℂ)} : Set (X → ℂ)) := by
  intro hg
  obtain ⟨p, hlt⟩ :=
    strict_lt_constants_le_linearSystemDeltaP_of_RR_DimGE2 X hRR hg
  -- Convert strict-lt to existence via zz354.
  rcases (linearSystemDeltaP_strictly_gt_constants_iff_exists_non_constant p).mp hlt with
    ⟨g, hg_in, hg_nin⟩
  exact ⟨p, g, hg_in, hg_nin⟩

end JacobianChallenge

end
