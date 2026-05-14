/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodLatticeFromPairing
import Mathlib.Algebra.Module.ZLattice.Basic

set_option diagnostics.threshold 100

/-! # `DiscreteTopology` + `IsZLattice` on `periodLatticeImage` from a
Riemann-bilinear bundle

The slim constructor
`PeriodLatticeAnalyticHypotheses.ofDiscrete` in
`Manifold/PeriodLatticeFromPairing.lean` (closed 2026-05-13)
takes:

* `discrete : DiscreteTopology (periodLatticeImage data α).toIntSubmodule`,
* `zlat   : IsZLattice ℝ (periodLatticeImage data α).toIntSubmodule`.

These are the two type-class instances the downstream wiring
(`PeriodLatticeOfRankTwoG_Wiring.lean`,
`PeriodLatticeOfRankTwoG_ComplexWiring.lean`) consumes to discharge
the analytic-Jacobian instances on `JacobianOfLattice` (items 4, 5,
10, 11, 12 of OPEN.md).

This chip provides a **named-hypothesis bundle** that packages the
classical Riemann-bilinear content needed to derive both instances at
once, via mathlib's existing `instIsZLatticeRealSpan` plus
`ZSpan.instDiscreteTopology` machinery for spans of bases.

## What this file delivers

* `PeriodLatticeDiscretenessBundle data α` — a bundled structure
  carrying:
  * `h1Basis : Basis (Fin (2 * genus X)) ℤ data.H1` — a ℤ-basis of
    `data.H1`. Classical: H₁(X; ℤ) on a compact connected complex
    1-manifold is free abelian of rank `2 · genus X` (Hodge identification
    + Hurewicz/Universal Coefficients).
  * `periodBasis : Basis (Fin (2 * genus X)) ℝ (Fin (genus X) → ℂ)` — the
    period vectors of the H₁ basis viewed as ℝ-basis of `ℝ^{2g} ≃ ℂ^g`.
    Classical: Riemann bilinear relations imply ℝ-linear independence
    of the periods (positive definiteness of the imaginary part of the
    period matrix).
  * `periodBasis_eq` — these two structures are compatible: the
    `i`-th period basis vector equals the period of the `i`-th H₁
    basis element. Calibration constraint, no math content.

* `periodLatticeImage_toIntSubmodule_eq_span_periodBasis` — the
  underlying identity: under the bundle, the period image's
  `Submodule ℤ` equals `Submodule.span ℤ (Set.range periodBasis)`.

* `periodLatticeImage_discreteTopology_of_bundle` — derived
  `DiscreteTopology` instance via `ZSpan.instDiscreteTopology` on the
  span of an ℝ-basis (`Finite ι`).

* `periodLatticeImage_isZLattice_of_bundle` — derived `IsZLattice ℝ`
  instance via mathlib's `instIsZLatticeRealSpan`.

* `PeriodLatticeAnalyticHypotheses.ofBundle` — composition with the
  slim constructor, giving a one-input form: from
  `PeriodLatticeDiscretenessBundle`, directly produce
  `PeriodLatticeAnalyticHypotheses`.

The two `Basis` fields each carry one classical theorem's worth of
content (rank H₁ = 2g; Riemann bilinear non-degeneracy), but the
**bundling pattern** means each can be discharged independently when
the corresponding upstream mathlib content lands.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff
open Submodule Module

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- **Riemann-bilinear bundle.** Carries the two classical inputs
needed to upgrade `periodLatticeImage data α` to a discrete `ℤ`-lattice
spanning `ℂ^g` over `ℝ`. -/
structure PeriodLatticeDiscretenessBundle
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)) where
  /-- A ℤ-basis of `data.H1` of rank `2 · genus X`. Classical:
  `H₁(X; ℤ) ≃ ℤ^{2g}` on a compact connected complex 1-manifold of
  genus `g`. -/
  h1Basis : Basis (Fin (2 * JacobianChallenge.genus X)) ℤ data.H1
  /-- The 2g period vectors of the H₁ basis form an ℝ-basis of
  `Fin (genus X) → ℂ ≃ ℝ^{2g}`. Classical: Riemann bilinear relations
  (positive-definiteness of the imaginary period matrix). -/
  periodBasis :
    Basis (Fin (2 * JacobianChallenge.genus X)) ℝ (Fin (JacobianChallenge.genus X) → ℂ)
  /-- Compatibility: the `i`-th period basis vector equals the period
  vector of the `i`-th H₁ basis element. -/
  periodBasis_eq :
    ∀ i, periodBasis i = periodVector data α (h1Basis i)

namespace PeriodLatticeDiscretenessBundle

variable {data : PeriodPairingData X}
  {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}

/-- The `Set.range` of the period basis equals the `Set.image` of the
period-vector hom restricted to the H₁ basis range. -/
lemma range_periodBasis_eq_image
    (h : PeriodLatticeDiscretenessBundle data α) :
    Set.range h.periodBasis = periodVectorHom data α '' Set.range h.h1Basis := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨h.h1Basis i, ⟨i, rfl⟩, ?_⟩
    show periodVector data α (h.h1Basis i) = h.periodBasis i
    exact (h.periodBasis_eq i).symm
  · rintro ⟨γ, ⟨i, hi⟩, hv⟩
    refine ⟨i, ?_⟩
    -- Goal: periodBasis i = v.
    -- hv : periodVectorHom data α γ = v, hi : h.h1Basis i = γ.
    have : periodVector data α γ = v := hv
    rw [h.periodBasis_eq i, hi]
    exact this

/-- `Set.range h.h1Basis` generates `data.H1` as an `AddCommGroup`. -/
lemma top_eq_span_int_range_h1Basis
    (h : PeriodLatticeDiscretenessBundle data α) :
    (Submodule.span ℤ (Set.range h.h1Basis) : Submodule ℤ data.H1) = ⊤ :=
  h.h1Basis.span_eq

end PeriodLatticeDiscretenessBundle

/-! ## Identification of `periodLatticeImage` with the ZSpan -/

/-- **The key identity.** Under the bundle, the period image's
`Submodule ℤ` equals `Submodule.span ℤ (Set.range periodBasis)`.

The reasoning chain:
1. `periodLatticeImage` is the `AddMonoidHom.range` of `periodVectorHom`.
2. The range of an `AddMonoidHom` whose domain is generated by `S` is
   `AddSubgroup.closure (f '' S)`.
3. With `S := Set.range h1Basis`, the image `f '' S = Set.range periodBasis`
   by `range_periodBasis_eq_image`.
4. `(AddSubgroup.closure T).toIntSubmodule = Submodule.span ℤ T` by
   `AddSubgroup.toIntSubmodule_closure`. -/
theorem periodLatticeImage_toIntSubmodule_eq_span_periodBasis
    {data : PeriodPairingData X}
    {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
    (h : PeriodLatticeDiscretenessBundle data α) :
    (periodLatticeImage data α).toIntSubmodule
      = Submodule.span ℤ (Set.range h.periodBasis) := by
  rw [h.range_periodBasis_eq_image]
  -- Goal: (periodLatticeImage data α).toIntSubmodule
  --     = Submodule.span ℤ (periodVectorHom data α '' Set.range h.h1Basis)
  --
  -- Bridge the AddMonoidHom coercion to its toIntLinearMap counterpart so
  -- mathlib's `Submodule.map_span` (linear-map flavour) fires.
  rw [show ((periodVectorHom data α : data.H1 → (Fin (JacobianChallenge.genus X) → ℂ))
              '' Set.range h.h1Basis)
        = ((periodVectorHom data α).toIntLinearMap : data.H1 → _)
              '' Set.range h.h1Basis from rfl]
  -- Strategy: span ℤ (f '' S) = (span ℤ S).map f, with S = range h1Basis,
  -- span ℤ S = ⊤, (⊤).map f = LinearMap.range f.
  rw [← Submodule.map_span (periodVectorHom data α).toIntLinearMap]
  rw [h.top_eq_span_int_range_h1Basis]
  rw [Submodule.map_top]
  -- Goal: (periodLatticeImage data α).toIntSubmodule
  --     = LinearMap.range (periodVectorHom data α).toIntLinearMap
  -- Both sides have the same carrier set: { v | ∃ γ, periodVectorHom data α γ = v }.
  ext v
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨γ, hγ⟩
  · rintro ⟨γ, hγ⟩
    exact ⟨γ, hγ⟩

/-! ## Derived `DiscreteTopology` and `IsZLattice` instances -/

/-- **Derived `DiscreteTopology`.** Under the bundle, the period image's
`Submodule ℤ` carries the discrete topology, via mathlib's
`ZSpan.instDiscreteTopology` applied to `periodBasis`. -/
theorem periodLatticeImage_discreteTopology_of_bundle
    {data : PeriodPairingData X}
    {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
    (h : PeriodLatticeDiscretenessBundle data α) :
    DiscreteTopology (periodLatticeImage data α).toIntSubmodule := by
  rw [periodLatticeImage_toIntSubmodule_eq_span_periodBasis h]
  -- Goal: DiscreteTopology (Submodule.span ℤ (Set.range h.periodBasis))
  -- Apply mathlib's instance on span of a finite real basis.
  infer_instance

/-- **Derived `IsZLattice ℝ`.** Under the bundle, the period image's
`Submodule ℤ` spans `ℂ^g` over `ℝ`, via mathlib's
`instIsZLatticeRealSpan` applied to `periodBasis`. -/
theorem periodLatticeImage_isZLattice_of_bundle
    {data : PeriodPairingData X}
    {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
    (h : PeriodLatticeDiscretenessBundle data α) :
    haveI := periodLatticeImage_discreteTopology_of_bundle h
    IsZLattice ℝ (periodLatticeImage data α).toIntSubmodule := by
  -- Convert through the span identity.
  haveI := periodLatticeImage_discreteTopology_of_bundle h
  have h_eq := periodLatticeImage_toIntSubmodule_eq_span_periodBasis h
  -- Mathlib's `instIsZLatticeRealSpan` gives `IsZLattice ℝ (span ℤ (Set.range b))`
  -- for a `Basis ι ℝ E` with `Finite ι`. Transport across `h_eq`.
  refine ⟨?_⟩
  -- Goal: span ℝ ((periodLatticeImage data α).toIntSubmodule : Set _) = ⊤.
  rw [h_eq]
  -- Goal: span ℝ ((Submodule.span ℤ (Set.range h.periodBasis)) : Set _) = ⊤.
  exact ZSpan.span_top h.periodBasis

/-! ## Composition with the slim constructor -/

/-- **One-input form.** From a `PeriodLatticeDiscretenessBundle`, build
the full `PeriodLatticeAnalyticHypotheses` via the slim constructor. -/
noncomputable def PeriodLatticeAnalyticHypotheses.ofBundle
    {data : PeriodPairingData X}
    {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
    (h : PeriodLatticeDiscretenessBundle data α) :
    PeriodLatticeAnalyticHypotheses data α :=
  PeriodLatticeAnalyticHypotheses.ofDiscrete data α
    (periodLatticeImage_discreteTopology_of_bundle h)
    (periodLatticeImage_isZLattice_of_bundle h)

end JacobianChallenge

end
