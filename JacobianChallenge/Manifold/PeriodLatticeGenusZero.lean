/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodLatticeFromPairing
import Mathlib.LinearAlgebra.Dimension.Finite

/-! # Genus-zero unconditional period lattice (chip PL-3c)

For a manifold `X` with `JacobianChallenge.genus X = 0`, the
`Fin (genus X) → ℂ` model space collapses to `Fin 0 → ℂ`, which is a
`Subsingleton` (only the zero function inhabits it). Then:

* the trivial subgroup `⊥` carries rank `0 = 2 * 0 = 2 * genus X`,
* `IsClosed (⊥ : Set _)` reduces to `IsClosed {0}` in a T2 space,
* every quotient of a `Subsingleton` is itself a `Subsingleton`,
* `Subsingleton ⇒ CompactSpace`, `T2Space`, `DiscreteTopology` are
  all automatic mathlib instances.

So in the genus-zero case, the entire `PeriodLatticeOfRankTwoG`
machinery — and thus items 4, 5, 10, 11, 12 of `OPEN.md` for the
parallel-Jacobian shape — is **unconditional**.

This is useful for the topological-sphere branch of item 14 (the
`X ≃ₜ S² → genus X = 0` direction), where `genus X = 0` would be the
output and the analytic Jacobian then carries a trivial structure.

## What this file delivers

* `PeriodLatticeOfRankTwoG.genusZero h` — the unconditional bundle for
  `h : genus X = 0`. Uses `lattice := ⊥`.

* `JacobianOfLattice.subsingleton_of_genus_zero` — the resulting
  analytic Jacobian is a `Subsingleton`.

* Three downstream instances chained from the `Subsingleton` fact:
  `compactSpace`, `t2Space`, `discreteTopology` on the genus-zero
  `JacobianOfLattice`.

## Anti-hack interaction

The trivial-bundle `lattice = ⊥` hack is rejected by the bundle's
`lattice_rank_eq` field (`finrank ℤ ⊥ = 0 ≠ 2 * g` for `g ≥ 1`) and
by the wiring's `IsZLattice ℝ ⊥` instance (`span ℝ ⊥ = ⊥ ≠ ⊤` for
real-dim `≥ 1`). Both hack rejections **vanish for `g = 0`**, which is
correct: at genus 0, the trivial lattice IS the honest answer.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

set_option diagnostics.threshold 100

namespace JacobianChallenge

variable (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- For `genus X = 0`, the model space `Fin (genus X) → ℂ` is a
`Subsingleton` (only the zero function inhabits `Fin 0 → ℂ`). -/
lemma subsingleton_pi_complex_of_genus_zero (h : JacobianChallenge.genus X = 0) :
    Subsingleton (Fin (JacobianChallenge.genus X) → ℂ) := by
  haveI : IsEmpty (Fin (JacobianChallenge.genus X)) := by
    rw [h]; exact Fin.isEmpty
  infer_instance

/-- For `genus X = 0`, the trivial subgroup `⊥ ⊆ Fin (genus X) → ℂ`
satisfies the `PeriodLatticeOfRankTwoG` requirements unconditionally. -/
def PeriodLatticeOfRankTwoG.genusZero (h : JacobianChallenge.genus X = 0) :
    PeriodLatticeOfRankTwoG X where
  lattice := ⊥
  lattice_isClosed := by
    haveI := subsingleton_pi_complex_of_genus_zero X h
    -- In a Subsingleton space, every set is closed.
    change IsClosed
      ((⊥ : AddSubgroup (Fin (JacobianChallenge.genus X) → ℂ)) :
        Set (Fin (JacobianChallenge.genus X) → ℂ))
    exact (Set.subsingleton_of_subsingleton).isClosed
  lattice_rank_eq := by
    -- `(⊥ : AddSubgroup _).toIntSubmodule = ⊥ : Submodule ℤ _` (rfl-level)
    -- and `finrank ℤ (⊥ : Submodule ℤ _) = 0`. The RHS is `2 * 0 = 0` under `h`.
    have h₁ : (⊥ : AddSubgroup (Fin (JacobianChallenge.genus X) → ℂ)).toIntSubmodule
        = (⊥ : Submodule ℤ (Fin (JacobianChallenge.genus X) → ℂ)) := rfl
    rw [h₁, finrank_bot, h]

/-- The genus-zero analytic Jacobian inherits the `Subsingleton`
structure of the model space `Fin 0 → ℂ`: a quotient of a Subsingleton
is itself a Subsingleton. -/
instance JacobianOfLattice.subsingleton_of_genus_zero
    (h : JacobianChallenge.genus X = 0) :
    Subsingleton
      (JacobianOfLattice X (PeriodLatticeOfRankTwoG.genusZero X h)) := by
  haveI := subsingleton_pi_complex_of_genus_zero X h
  -- `JacobianOfLattice X data := (Fin g → ℂ) ⧸ data.lattice`. A
  -- quotient of a Subsingleton is a Subsingleton.
  change Subsingleton
    ((Fin (JacobianChallenge.genus X) → ℂ) ⧸
      (PeriodLatticeOfRankTwoG.genusZero X h).lattice)
  exact Quotient.instSubsingletonQuotient _

/-- **OPEN.md item 11 — unconditional in the genus-zero case.** -/
instance JacobianOfLattice.compactSpace_of_genus_zero
    (h : JacobianChallenge.genus X = 0) :
    CompactSpace
      (JacobianOfLattice X (PeriodLatticeOfRankTwoG.genusZero X h)) :=
  Subsingleton.compactSpace

/-- **OPEN.md item 10 — unconditional in the genus-zero case.** The
quotient already inherits `T2Space` from
`PeriodLatticeRankTwoG.lean`'s `instT2Space`, but we record the
genus-zero shortcut for symmetry with `compactSpace_of_genus_zero` and
`discreteTopology_of_genus_zero`. -/
instance JacobianOfLattice.t2Space_of_genus_zero
    (h : JacobianChallenge.genus X = 0) :
    T2Space (JacobianOfLattice X (PeriodLatticeOfRankTwoG.genusZero X h)) :=
  inferInstance

/-- A `Subsingleton`-quotient is discrete. Strengthens
`OPEN.md` item 4 (`TopologicalSpace`, currently `⊥` discrete in `Basic.lean`):
in the genus-zero case the genuine analytic-Jacobian topology coincides
with the discrete topology, so the `Basic.lean` stub is honest at `g = 0`
(though still wrong-by-construction at `g ≥ 1`). -/
instance JacobianOfLattice.discreteTopology_of_genus_zero
    (h : JacobianChallenge.genus X = 0) :
    DiscreteTopology
      (JacobianOfLattice X (PeriodLatticeOfRankTwoG.genusZero X h)) := by
  haveI := JacobianOfLattice.subsingleton_of_genus_zero X h
  -- `Subsingleton ⇒ DiscreteTopology` via `discreteTopology_of_subsingleton`
  -- (mathlib `Topology.Order`).
  exact ⟨by ext s; constructor
            · intro _; trivial
            · intro _; exact isOpen_discrete s⟩

end JacobianChallenge

end
