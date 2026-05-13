/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.ExistenceFromFinrank
import JacobianChallenge.Topology.RiemannRochGenusZeroSingleInput
import JacobianChallenge.Topology.ExistsMeroSimplePoleSplit
import JacobianChallenge.Topology.HolomorphicLocallyConstantDischarge

set_option diagnostics.threshold 100

/-! # Full closure chain `RR_DimGE2_GenusZero` ⇒ `RiemannRochGenusZero`

This file ships the final composition theorem closing
`RiemannRochGenusZero X` (zz325's named conditional) conditional on
**exactly two** named classical inputs:

  (i)  `RR_DimGE2_GenusZero X` — the Riemann-Roch dimension
       inequality `∃ p, 2 ≤ finrank ℂ (linearSystemDeltaP p)` at
       genus 0. The heavy classical content (RR + Serre).

  (ii) `LiftToMeromorphicNonzero X` — the technical lifting that
       given a non-constant plain function `g ∈ L(δp)` produces a
       `MeromorphicNonzero X` with the same order pattern. The
       missing piece is global identity-theorem propagation +
       chart redefinition for `regular_continuousAt`.

Combined with the unconditional theorems landed in zz344
(`UniformSimplePoleRegularity`) and zz350
(`LiouvilleOnCompactConnected`), these two inputs are *all* that
stands between `RR_DimGE2_GenusZero X` + lifting and a fully
discharged `RiemannRochGenusZero X`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff

set_option linter.unusedSectionVars false

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Named technical hypothesis: lifting plain L(δp) elements to
`MeromorphicNonzero X`.** From a non-constant `g : X → ℂ` in
`L(δp)`, produce a `MeromorphicNonzero X` with the same order
bounds and non-constancy.

The lifting requires the identity theorem for analytic functions
(to globalize the nonvanishing-germ field) plus a chart-redefinition
argument (to ensure regular_continuousAt). Both are classical
content not yet formalised in this repo. -/
def LiftToMeromorphicNonzero : Prop :=
  ∀ (p : X) (g : X → ℂ),
    g ∈ linearSystemDeltaP p →
    g ∉ Submodule.span ℂ ({(1 : X → ℂ)} : Set (X → ℂ)) →
    ∃ f : MeromorphicNonzero X,
      (∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) ∧
      (((-1 : ℤ) : WithTop ℤ) ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p) ∧
      ¬ JacobianChallenge.IsConstantMap f.toFun

/-- **`RR_DimGE2_GenusZero` + lifting ⇒
`ExistsNonConstantBoundedByDeltaP_GenusZero`.** -/
theorem existsNonConstantBoundedByDeltaP_of_RR_and_lifting
    [Nonempty X]
    (hRR : RR_DimGE2_GenusZero X)
    (hLift : LiftToMeromorphicNonzero X) :
    ExistsNonConstantBoundedByDeltaP_GenusZero X := by
  intro hg
  -- From RR_DimGE2 get a non-constant g ∈ L(δp).
  obtain ⟨p, g, hg_in, hg_nin⟩ :=
    exists_mem_linearSystem_not_in_constants_of_RR_DimGE2 X hRR hg
  -- Lift g to a MeromorphicNonzero X with the same bounds.
  obtain ⟨f, h_off, h_p, h_nonconst⟩ := hLift p g hg_in hg_nin
  refine ⟨p, f, h_off, h_p, h_nonconst⟩

/-- **The maximally-compressed closure chain.** Under the two named
classical inputs `RR_DimGE2_GenusZero X` (Riemann-Roch + Serre
duality at δp, genus 0) and `LiftToMeromorphicNonzero X` (identity
theorem + chart redefinition), the named conditional
`RiemannRochGenusZero X` from zz325 follows. -/
theorem riemannRochGenusZero_from_RR_DimGE2_and_lifting
    [Nonempty X]
    (hRR : RR_DimGE2_GenusZero X)
    (hLift : LiftToMeromorphicNonzero X) :
    RiemannRochGenusZero X := by
  -- ExistsNonConstantBoundedByDeltaP from RR + lifting.
  have hExists : ExistsNonConstantBoundedByDeltaP_GenusZero X :=
    existsNonConstantBoundedByDeltaP_of_RR_and_lifting X hRR hLift
  -- From there, riemannRochGenusZero_from_existsBoundedByDeltaP (zz350)
  -- chains through.
  exact riemannRochGenusZero_from_existsBoundedByDeltaP X hExists

end JacobianChallenge

end
