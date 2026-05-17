/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodLatticeRankTwoG
import JacobianChallenge.Manifold.PeriodLatticeOfRankTwoG_Wiring
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option linter.unusedSectionVars false

/-! # `PeriodLatticeOfRankTwoG RiemannSphere` — direct construction at genus 0

The `ofBundle` route through `PeriodLatticeDiscretenessBundle` is
structurally blocked at genus 0: it requires `h1Basis : Basis (Fin 0)
ℤ (SmoothCycle 𝓘(ℝ, ℂ) RS)`, which forces
`SmoothCycle 𝓘(ℝ, ℂ) RS = 0` — false (the SmoothCycle module is
non-trivial even when its homology classes collapse to 0). The bundle
encodes a stricter classical condition than the geometric statement.

For `X = RiemannSphere`, however, the target structure
`PeriodLatticeOfRankTwoG RiemannSphere` is trivially constructible
**directly**, bypassing the bundle:

* The lattice lives in `Fin (genus RS) → ℂ = Fin 0 → ℂ ≃ {0}`
  (the unique-element type).
* The only `AddSubgroup` of `{0}` is `⊥`.
* `⊥ : Set _` is closed.
* `Module.finrank ℤ ⊥ = 0 = 2 * 0 = 2 * genus RS`.

The resulting `PeriodLatticeOfRankTwoG RiemannSphere` has
`lattice = ⊥`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Submodule Module

namespace JacobianChallenge

/-- **The trivial period lattice at genus 0.** `Fin (genus X) → ℂ` is
trivial (`genus X = 0`), so the only `AddSubgroup` is `⊥`. The
required rank equation `finrank ℤ ⊥ = 2 * genus X = 0` is automatic. -/
noncomputable def PeriodLatticeOfRankTwoG.trivialAtGenusZero
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
    (hgenus : JacobianChallenge.genus X = 0) :
    PeriodLatticeOfRankTwoG X where
  lattice := ⊥
  lattice_isClosed := by
    -- `⊥ : AddSubgroup _` as a `Set` equals `{0}`, which is closed.
    simp [AddSubgroup.coe_bot]
  lattice_rank_eq := by
    -- `(⊥ : AddSubgroup _).toIntSubmodule = ⊥`; `finrank ℤ ⊥ = 0`.
    rw [hgenus, Nat.mul_zero]
    -- Goal: `Module.finrank ℤ (⊥ : AddSubgroup (Fin (genus X) → ℂ)).toIntSubmodule = 0`.
    -- Use `Subsingleton`-of-`⊥` to discharge.
    have hsub : Subsingleton
        ((⊥ : AddSubgroup (Fin (JacobianChallenge.genus X) → ℂ)).toIntSubmodule) := by
      refine ⟨fun x y => ?_⟩
      apply Subtype.ext
      have hx : x.1 ∈ (⊥ : AddSubgroup (Fin (JacobianChallenge.genus X) → ℂ)) := x.2
      have hy : y.1 ∈ (⊥ : AddSubgroup (Fin (JacobianChallenge.genus X) → ℂ)) := y.2
      rw [AddSubgroup.mem_bot] at hx hy
      rw [hx, hy]
    -- Subsingleton modules have finrank 0.
    haveI := hsub
    exact Module.finrank_zero_of_subsingleton

/-- **`PeriodLatticeOfRankTwoG RiemannSphere`** — unconditional. -/
noncomputable def periodLatticeOfRankTwoG_RiemannSphere :
    PeriodLatticeOfRankTwoG RiemannSphere :=
  PeriodLatticeOfRankTwoG.trivialAtGenusZero
    RiemannSphere.genus_RiemannSphere_eq_zero

/-! ## Trivial-lattice `ℤ`-lattice instances (for use in the
JacobianOfLattice wiring on RiemannSphere). -/

/-- The lattice of `periodLatticeOfRankTwoG_RiemannSphere` is `⊥`. -/
@[simp] theorem periodLatticeOfRankTwoG_RiemannSphere_lattice :
    periodLatticeOfRankTwoG_RiemannSphere.lattice = ⊥ := rfl

/-- The ambient `Fin (genus RS) → ℂ` is subsingleton (genus RS = 0). -/
private lemma fin_genus_RS_to_complex_subsingleton :
    Subsingleton (Fin (JacobianChallenge.genus RiemannSphere) → ℂ) := by
  rw [RiemannSphere.genus_RiemannSphere_eq_zero]
  haveI : Unique (Fin 0 → ℂ) := Pi.uniqueOfIsEmpty (fun _ : Fin 0 => ℂ)
  infer_instance

/-- The trivial period lattice's `toIntSubmodule` subtype is subsingleton. -/
private lemma subsingleton_periodLattice_subtype :
    Subsingleton
      (periodLatticeOfRankTwoG_RiemannSphere.lattice.toIntSubmodule) := by
  haveI := fin_genus_RS_to_complex_subsingleton
  refine ⟨fun x y => ?_⟩
  apply Subtype.ext
  exact Subsingleton.elim _ _

/-- **`DiscreteTopology` on the trivial period lattice's `toIntSubmodule`.**
A subsingleton type has a unique topology, which is discrete. -/
instance discreteTopology_periodLattice_RiemannSphere :
    DiscreteTopology
      (periodLatticeOfRankTwoG_RiemannSphere.lattice.toIntSubmodule) :=
  haveI := subsingleton_periodLattice_subtype
  Subsingleton.discreteTopology

/-- **`IsZLattice ℝ` on the trivial period lattice's `toIntSubmodule`.**
The ambient `Fin (genus RS) → ℂ = Fin 0 → ℂ` is itself trivial, so any
submodule's ℝ-span equals `⊤`. -/
instance isZLattice_periodLattice_RiemannSphere :
    IsZLattice ℝ
      (periodLatticeOfRankTwoG_RiemannSphere.lattice.toIntSubmodule) where
  span_top := by
    -- Subsingleton ambient ⇒ all `Submodule` values are equal (=`⊤` =`⊥`).
    haveI := fin_genus_RS_to_complex_subsingleton
    exact Subsingleton.elim _ _

/-- **`CompactSpace` on the analytic Jacobian for `RiemannSphere`** —
unconditional. Specialises `PeriodLatticeOfRankTwoG.compactSpaceHypothesis_holds`
to the unconditional `periodLatticeOfRankTwoG_RiemannSphere`. -/
theorem compactSpaceHypothesis_holds_RiemannSphere :
    JacobianOfLattice.CompactSpaceHypothesis
      periodLatticeOfRankTwoG_RiemannSphere :=
  PeriodLatticeOfRankTwoG.compactSpaceHypothesis_holds
    periodLatticeOfRankTwoG_RiemannSphere

end JacobianChallenge

end
