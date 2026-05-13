/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.ExistsMeroSimplePoleSplit
import JacobianChallenge.Topology.LinearSystemConstants
import JacobianChallenge.Manifold.IsConstantMapAux

set_option diagnostics.threshold 100

/-! # Bridge: `ExistsNonConstantBoundedByDeltaP_GenusZero` ↔ strict-gt
constants form

zz346's `ExistsNonConstantBoundedByDeltaP_GenusZero X` asserts the
existence of a non-constant `MeromorphicNonzero X` element of
`L(δp)`. This file shows it implies — and is essentially equivalent
to — the **linear-algebra strict-containment** form:

  ∃ p : X, Submodule.span ℂ {(1 : X → ℂ)} < linearSystemDeltaP p

This positions the Riemann-Roch existence content as a clean
*dimension* statement, the form a future Riemann-Roch formula chip
would actually deliver.

## Forward direction (this chip)

Under the existence hypothesis, `f.toFun ∈ linearSystemDeltaP p`
(order conditions match), and `f.toFun ∉ Submodule.span ℂ {1}`
(non-constancy ⇔ not-in-span-of-1 over a nonempty X).

The reverse direction would require, from `g ∈ linearSystemDeltaP p
\ constants`, lifting `g : X → ℂ` to `MeromorphicNonzero X` —
needing nonvanishing-germ globalisation, which is a separate
substantive chip.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

set_option linter.unusedSectionVars false in
/-- **Constants in `X → ℂ` are exactly the span of `1` (over `ℂ`)
when `X` is nonempty.** -/
lemma isConstantMap_iff_mem_span_one [Nonempty X] (g : X → ℂ) :
    JacobianChallenge.IsConstantMap g
      ↔ g ∈ Submodule.span ℂ ({(1 : X → ℂ)} : Set (X → ℂ)) := by
  refine ⟨?_, ?_⟩
  · -- Constant g = const c ⇒ g = c • 1 ∈ span {1}.
    rintro ⟨c, hg⟩
    have h_eq : g = c • (1 : X → ℂ) := by
      ext x
      rw [hg x]
      simp
    rw [h_eq]
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))
  · -- g ∈ span {1} ⇒ g = c • 1 ⇒ g is constant.
    intro hg
    rcases Submodule.mem_span_singleton.mp hg with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    intro x
    rw [← hc]
    simp

/-- **From `MeromorphicNonzero` existence, get `f.toFun ∈ L(δp)`.** -/
lemma toFun_mem_linearSystemDeltaP_of_bounded
    {p : X} {f : MeromorphicNonzero X}
    (h_off : ∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x)
    (h_p : ((-1 : ℤ) : WithTop ℤ) ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p) :
    f.toFun ∈ linearSystemDeltaP p := by
  rw [mem_linearSystemDeltaP]
  refine ⟨?_, h_off, h_p⟩
  exact f.meromorphic

/-- **Forward direction of the bridge.** From the
`MeromorphicNonzero` existence, deliver the strict-containment
form. -/
theorem strict_lt_constants_le_linearSystemDeltaP_of_existsBoundedByDeltaP
    [Nonempty X]
    (hA : ExistsNonConstantBoundedByDeltaP_GenusZero X) :
    JacobianChallenge.genus X = 0 →
    ∃ p : X, (Submodule.span ℂ ({(1 : X → ℂ)} : Set (X → ℂ)))
      < linearSystemDeltaP p := by
  intro hg
  obtain ⟨p, f, h_off, h_p, h_nonconst⟩ := hA hg
  refine ⟨p, ?_⟩
  -- f.toFun is in L(δp) but not in constants.
  have h_in_L : f.toFun ∈ linearSystemDeltaP p :=
    toFun_mem_linearSystemDeltaP_of_bounded h_off h_p
  have h_not_const : f.toFun ∉ Submodule.span ℂ ({(1 : X → ℂ)} : Set (X → ℂ)) := by
    rw [← isConstantMap_iff_mem_span_one]
    exact h_nonconst
  -- Use zz354's strict-lt-iff-exists-nonconstant.
  rw [linearSystemDeltaP_strictly_gt_constants_iff_exists_non_constant]
  exact ⟨f.toFun, h_in_L, h_not_const⟩

end JacobianChallenge

end
