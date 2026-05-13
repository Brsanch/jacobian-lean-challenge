/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodPairingDefinition
import JacobianChallenge.Manifold.PeriodLatticeRankTwoG
import JacobianChallenge.Manifold.PeriodLatticeOfRankTwoG_Wiring
import JacobianChallenge.Manifold.PeriodLatticeOfRankTwoG_ComplexWiring
import Mathlib.LinearAlgebra.Basis.Defs

/-! # Bridge: `PeriodPairingData X` + basis ⇒ `PeriodLatticeOfRankTwoG X`
(chip PL-3a)

This file is the explicit bridge between the two existing Tier-2 named
hypothesis bundles in the period-lattice arc:

* `JacobianChallenge.PeriodPairingData X` (`PeriodPairingDefinition.lean`)
  — packages `H₁(X; ℤ)` and a pairing
  `H1 →+ HolomorphicOneForm X →ₗ[ℂ] ℂ`.

* `JacobianChallenge.PeriodLatticeOfRankTwoG X` (`PeriodLatticeRankTwoG.lean`)
  — packages a candidate lattice `Λ ⊆ ℂ^g` with `IsClosed`-and-rank-`2g`
  certificates and downstream `JacobianOfLattice X data`
  quotient.

The bridge constructs the period-lattice candidate `Λ` as the image of
the period vector `γ ↦ (∫_γ α_j)_{j=1..g}`, expressed in a chosen
ℂ-basis `α : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)` of the
holomorphic-one-forms space. The basis is supplied as a structure field
— at the current mathlib pin we do not have Hodge theory and hence no
unconditional source of such a basis (the geometric genus `genus X =
Module.finrank ℂ (HolomorphicOneForm X)` is the right integer only on
the assumption that `HolomorphicOneForm X` is finite-dimensional, which
is Phase 4 work).

## What this file delivers

* `periodVector data α γ : Fin (genus X) → ℂ` — the `g`-tuple of
  periods of a basis form along a 1-cycle.

* `periodVectorHom data α : data.H1 →+ (Fin (genus X) → ℂ)` — the same
  thing as an `AddMonoidHom`, with `ℤ`-additivity in the cycle argument
  inherited from `PeriodPairingData.pairing`'s `AddMonoidHom` structure.

* `periodLatticeImage data α : AddSubgroup (Fin (genus X) → ℂ)` — the
  image of `periodVectorHom`. The mathematical period lattice.

* `PeriodLatticeAnalyticHypotheses data α` — a structure bundling the
  three named gaps (closedness, rank-`2g`, and the `ℤ`-lattice
  instance data) that promote `periodLatticeImage` into an honest
  `PeriodLatticeOfRankTwoG` term. Each field is the Riemann
  bilinear-relations content of one classical theorem.

* `PeriodLatticeOfRankTwoG.ofPeriodPairing data α h` — the bridge: from
  the period-pairing data, a chosen basis, and the analytic
  hypotheses, produce a `PeriodLatticeOfRankTwoG X`. Downstream chips
  `*_Wiring` then fire automatically.

## What this file does NOT do

* It does **not** assert that a basis exists. The Hodge gap
  `HolomorphicOneForm X` is finite-dimensional remains open.
* It does **not** prove rank-`2g` or discreteness of the period image
  itself. Those are the Riemann bilinear-relations content and are
  surfaced as fields of `PeriodLatticeAnalyticHypotheses`.
* It does **not** modify `Basic.lean`. All new content is additive.

## Anti-hack

The "trivial-image hack" `data.pairing = 0` gives
`periodLatticeImage = ⊥`. Then `lattice_rank_eq : finrank ℤ ⊥ = 2 * g`
forces `g = 0`, exactly the trivial-bundle hack rejected by
`PeriodLatticeOfRankTwoG.lattice_rank_eq` already. Discreteness is
trivially true on `⊥`; the `IsZLattice ℝ ⊥` instance is the obstacle
(it forces `Submodule.span ℝ (⊥ : Set _) = ⊤`, false in real
dimension `≥ 1`), matching the existing anti-hack on the wiring
chain.
-/

open scoped Manifold Topology Bundle ContDiff
open Submodule Module

noncomputable section

set_option diagnostics.threshold 100

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- The `g`-tuple period vector: feed each basis-form into the period
pairing along `γ` and collect the resulting `ℂ`-values. -/
def periodVector
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (γ : data.H1) : Fin (JacobianChallenge.genus X) → ℂ :=
  fun j => PeriodPairing data γ (α j)

@[simp] lemma periodVector_apply
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (γ : data.H1) (j : Fin (JacobianChallenge.genus X)) :
    periodVector data α γ j = PeriodPairing data γ (α j) := rfl

@[simp] lemma periodVector_zero_left
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)) :
    periodVector data α (0 : data.H1) = 0 := by
  funext j
  show PeriodPairing data 0 (α j) = (0 : Fin (JacobianChallenge.genus X) → ℂ) j
  rw [PeriodPairing_zero_left]
  rfl

lemma periodVector_add_left
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (γ γ' : data.H1) :
    periodVector data α (γ + γ')
      = periodVector data α γ + periodVector data α γ' := by
  funext j
  show PeriodPairing data (γ + γ') (α j)
      = (periodVector data α γ + periodVector data α γ') j
  rw [PeriodPairing_add_left]
  rfl

/-- The period vector as an `AddMonoidHom` in the cycle argument, with
the basis held fixed. -/
def periodVectorHom
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)) :
    data.H1 →+ (Fin (JacobianChallenge.genus X) → ℂ) where
  toFun γ := periodVector data α γ
  map_zero' := periodVector_zero_left data α
  map_add' γ γ' := periodVector_add_left data α γ γ'

@[simp] lemma periodVectorHom_apply
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (γ : data.H1) :
    periodVectorHom data α γ = periodVector data α γ := rfl

/-- The **period lattice** of `X` (given pairing data and a basis): the
image of the period-vector hom inside `ℂ^g`. -/
def periodLatticeImage
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)) :
    AddSubgroup (Fin (JacobianChallenge.genus X) → ℂ) :=
  AddMonoidHom.range (periodVectorHom data α)

lemma mem_periodLatticeImage_iff
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (v : Fin (JacobianChallenge.genus X) → ℂ) :
    v ∈ periodLatticeImage data α ↔ ∃ γ : data.H1, periodVector data α γ = v := by
  unfold periodLatticeImage
  exact AddMonoidHom.mem_range

/-- Named-hypothesis bundle for the **Riemann bilinear / discreteness**
content needed to upgrade the period image to a
`PeriodLatticeOfRankTwoG`.

Each field is *one classical theorem away*:

* `isClosed` — image of an `H₁(X;ℤ) ≃ ℤ^{2g}` carrier under a finite
  ℂ-linear functional family is a closed `ℤ`-spanned subset of `ℂ^g`,
  via standard arguments on discrete subgroups of `ℝ^n`.
* `rank_eq` — Riemann bilinear relations + `H₁(X;ℤ) ≃ ℤ^{2g}` give the
  rank certificate.
* `discreteTopology` and `isZLattice` — instance-level packaging of the
  same content for the downstream `*_Wiring` discharges
  (`PeriodLatticeOfRankTwoG_Wiring.lean`,
  `PeriodLatticeOfRankTwoG_ComplexWiring.lean`).

Mathlib at the pin does not have any of these for the period image
specifically; we surface them rather than fabricate. -/
structure PeriodLatticeAnalyticHypotheses
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)) where
  /-- Closedness of the period image as a set in `ℂ^g`. Needed for the
  `T2Space` instance of the quotient. -/
  isClosed :
    IsClosed ((periodLatticeImage data α :
      Set (Fin (JacobianChallenge.genus X) → ℂ)))
  /-- Free `ℤ`-rank of the period image is `2 * genus X`. The trivial
  hack `data.pairing = 0` makes the LHS `0`, so this field forces
  `genus X = 0` in the hack scenario. -/
  rank_eq :
    Module.finrank ℤ (periodLatticeImage data α).toIntSubmodule
      = 2 * JacobianChallenge.genus X
  /-- Discrete-topology instance data for the underlying
  `Submodule ℤ`, required by the `*_Wiring` discharges. -/
  discreteTopology :
    DiscreteTopology (periodLatticeImage data α).toIntSubmodule
  /-- `IsZLattice ℝ` instance data for the underlying
  `Submodule ℤ`, required by the `*_Wiring` discharges. The content is
  `Submodule.span ℝ (Λ : Set ℂ^g) = ⊤`, false on `Λ = ⊥` for `g ≥ 1`. -/
  isZLattice :
    @IsZLattice ℝ _ (Fin (JacobianChallenge.genus X) → ℂ) _ _
      (periodLatticeImage data α).toIntSubmodule discreteTopology

/-- **The bridge.** From a period-pairing bundle, a chosen ℂ-basis of
`HolomorphicOneForm X`, and the named analytic hypotheses, build a
`PeriodLatticeOfRankTwoG X` term. -/
def PeriodLatticeOfRankTwoG.ofPeriodPairing
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeAnalyticHypotheses data α) :
    PeriodLatticeOfRankTwoG X where
  lattice := periodLatticeImage data α
  lattice_isClosed := h.isClosed
  lattice_rank_eq := h.rank_eq

@[simp] lemma PeriodLatticeOfRankTwoG.ofPeriodPairing_lattice
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeAnalyticHypotheses data α) :
    (PeriodLatticeOfRankTwoG.ofPeriodPairing data α h).lattice
      = periodLatticeImage data α := rfl

/-! ### Downstream wiring discharges

The fields of `PeriodLatticeAnalyticHypotheses` are exactly the
instance-class inputs needed by the existing `*_Wiring` discharges
(`PeriodLatticeOfRankTwoG.compactSpaceHypothesis_holds`,
`PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds`). Surfacing these
here closes the diagram: any consumer that supplies pairing data,
basis, and analytic hypotheses gets items 4, 5, 10, 11, 12 of `OPEN.md`
discharged simultaneously on the resulting `JacobianOfLattice`. -/

/-- Item-11 discharge from the bridge bundle. The bundled
`discreteTopology` and `isZLattice` fields supply the instance arguments
that `PeriodLatticeOfRankTwoG.compactSpaceHypothesis_holds` needs. -/
theorem PeriodLatticeOfRankTwoG.ofPeriodPairing_compactSpace
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeAnalyticHypotheses data α) :
    haveI := h.discreteTopology
    haveI := h.isZLattice
    JacobianOfLattice.CompactSpaceHypothesis
      (PeriodLatticeOfRankTwoG.ofPeriodPairing data α h) := by
  -- `(ofPeriodPairing data α h).lattice` reduces to `periodLatticeImage data α`,
  -- so the bundled instances on `(periodLatticeImage data α).toIntSubmodule`
  -- are exactly what `compactSpaceHypothesis_holds` consumes.
  change CompactSpace
      (JacobianOfLattice X (PeriodLatticeOfRankTwoG.ofPeriodPairing data α h))
  haveI : DiscreteTopology
      (PeriodLatticeOfRankTwoG.ofPeriodPairing data α h).lattice.toIntSubmodule :=
    h.discreteTopology
  haveI : IsZLattice ℝ
      (PeriodLatticeOfRankTwoG.ofPeriodPairing data α h).lattice.toIntSubmodule :=
    h.isZLattice
  exact PeriodLatticeOfRankTwoG.compactSpaceHypothesis_holds _

/-- Items-5+12 discharge from the bridge bundle. -/
noncomputable def PeriodLatticeOfRankTwoG.ofPeriodPairing_chartedSpace
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeAnalyticHypotheses data α) :
    haveI := h.discreteTopology
    haveI := h.isZLattice
    JacobianOfLattice.ChartedSpaceHypothesis
      (PeriodLatticeOfRankTwoG.ofPeriodPairing data α h) :=
  haveI : DiscreteTopology
      (PeriodLatticeOfRankTwoG.ofPeriodPairing data α h).lattice.toIntSubmodule :=
    h.discreteTopology
  haveI : IsZLattice ℝ
      (PeriodLatticeOfRankTwoG.ofPeriodPairing data α h).lattice.toIntSubmodule :=
    h.isZLattice
  PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds _

end JacobianChallenge

end
