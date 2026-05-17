/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodLatticeDiscretenessFromBilinear

set_option linter.unusedSectionVars false

/-! # Symplectic-tuple period-lattice bundle (refactor of `PeriodLatticeDiscretenessBundle`)

The existing `PeriodLatticeDiscretenessBundle` (in
`PeriodLatticeDiscretenessFromBilinear.lean`) has a structural error:

```
h1Basis : Basis (Fin (2 * genus X)) ℤ data.H1
```

For the canonical `data = PeriodPairingData.ofSmoothCycle X`, the
carrier `data.H1` is the **full submodule of smooth 1-cycles**
`SmoothCycle 𝓘(ℝ, ℂ) X` — the kernel of the boundary map, NOT the
homology quotient `H₁(X; ℤ) = SmoothCycle / SmoothBoundary`. The
SmoothCycle module is infinite-dimensional over `ℤ` for any
non-trivial `X` (uncountably many smoothly inequivalent loops), so
`Basis (Fin 2g) ℤ (SmoothCycle X)` is **never inhabited** — the
bundle's `ofBundle` construction path is dead code at every genus.

The classical content is weaker than the bundle asserts: we want
a chosen **tuple of `2g` cycles** whose period vectors form an
`ℝ`-basis of `Fin g → ℂ` AND ℤ-span the entire period image
(`periodLatticeImage`). The latter follows classically from "every
homology class is a ℤ-combination of the symplectic-basis classes"
+ Stokes (boundaries have zero period), and is the geometric input,
NOT "data.H1 is free of rank 2g".

This file introduces `PeriodLatticeSymplecticBundle` — the corrected
shape — alongside the legacy bundle. The legacy bundle is strictly
stronger (a `Basis` of `data.H1` is a specific tuple, plus the extra
constraint of spanning + linear independence), so a conversion
`legacy → symplectic` is straightforward.

## The new bundle

* `cycleGenerators : Fin (2 * genus X) → data.H1` — a tuple, not a
  basis.
* `periodBasis : Basis (Fin (2 * genus X)) ℝ (Fin (genus X) → ℂ)` —
  the `ℝ`-basis of the ambient (unchanged from legacy).
* `periodBasis_eq : ∀ i, periodBasis i = periodVector data α
  (cycleGenerators i)` — compatibility (unchanged).
* `period_image_spanned : ∀ γ : data.H1, periodVector data α γ ∈
  Submodule.span ℤ (Set.range periodBasis)` — the corrected
  geometric content: every cycle's period lies in the ℤ-span of the
  chosen symplectic-basis periods. Classically: "the chosen tuple
  represents the homology classes" + Stokes.

## What this chip ships

* The new `PeriodLatticeSymplecticBundle` type.
* `PeriodLatticeDiscretenessBundle.toSymplectic` — conversion from
  the legacy bundle (when an inhabitant exists, which it never does
  classically for `ofSmoothCycle`; this is a "type-level no-op" for
  ongoing refactor work).
* Re-derivation of the `DiscreteTopology` and `IsZLattice` properties
  on `periodLatticeImage` from the new bundle, **without** appealing
  to the legacy bundle's over-strong basis assumption.
* `PeriodLatticeSymplecticBundle.trivial_at_genus_zero` — the new
  bundle is trivially constructible at `genus = 0` (the empty tuple),
  validating that the genus-0 case flows through cleanly without the
  bypass used in `PeriodLatticeRiemannSphere.lean`.

This is a side-by-side refactor; no existing consumers are touched
in this chip.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff
open Submodule Module

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- **Symplectic-tuple period-lattice bundle (corrected design).**

Replaces `PeriodLatticeDiscretenessBundle`'s over-strong
`h1Basis : Basis (Fin 2g) ℤ data.H1` with a **tuple** of `2g`
cycle elements + a **geometric** spanning condition on their period
vectors. -/
structure PeriodLatticeSymplecticBundle
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)) where
  /-- A chosen tuple of `2g` cycle elements (not asserted to be a basis
  of `data.H1` — that condition is too strong since `data.H1 =
  SmoothCycle X` is infinite-dimensional in general). -/
  cycleGenerators : Fin (2 * JacobianChallenge.genus X) → data.H1
  /-- The `2g` period vectors of the chosen tuple form an `ℝ`-basis of
  `Fin (genus X) → ℂ ≃ ℝ^{2g}`. (Riemann bilinear non-degeneracy.) -/
  periodBasis :
    Basis (Fin (2 * JacobianChallenge.genus X)) ℝ (Fin (JacobianChallenge.genus X) → ℂ)
  /-- Compatibility: the `i`-th period basis vector equals the period
  vector of the `i`-th cycle generator. -/
  periodBasis_eq :
    ∀ i, periodBasis i = periodVector data α (cycleGenerators i)
  /-- **Geometric spanning condition**: every cycle's period vector
  lies in the `ℤ`-span of the chosen tuple's periods. Classically:
  "the chosen tuple represents a generating set of homology classes"
  + Stokes (boundaries have zero period). -/
  period_image_spanned :
    ∀ γ : data.H1,
      periodVector data α γ ∈ Submodule.span ℤ (Set.range periodBasis)

namespace PeriodLatticeSymplecticBundle

variable {data : PeriodPairingData X}
  {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}

/-- `Set.range periodBasis` equals the image of `cycleGenerators` under
`periodVectorHom`. Counterpart of
`PeriodLatticeDiscretenessBundle.range_periodBasis_eq_image`. -/
lemma range_periodBasis_eq_image
    (h : PeriodLatticeSymplecticBundle data α) :
    Set.range h.periodBasis =
      periodVectorHom data α '' Set.range h.cycleGenerators := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨h.cycleGenerators i, ⟨i, rfl⟩, ?_⟩
    show periodVector data α (h.cycleGenerators i) = h.periodBasis i
    exact (h.periodBasis_eq i).symm
  · rintro ⟨γ, ⟨i, hi⟩, hv⟩
    refine ⟨i, ?_⟩
    have : periodVector data α γ = v := hv
    rw [h.periodBasis_eq i, hi]
    exact this

/-! ## Identification of `periodLatticeImage` with the ZSpan -/

/-- **The key identity** (refactored). Under the symplectic bundle,
`periodLatticeImage`'s `toIntSubmodule` equals the `ℤ`-span of
`periodBasis`. The proof uses the new `period_image_spanned` field
where the legacy proof used `h1Basis.span_eq`. -/
theorem periodLatticeImage_toIntSubmodule_eq_span_periodBasis
    (h : PeriodLatticeSymplecticBundle data α) :
    (periodLatticeImage data α).toIntSubmodule
      = Submodule.span ℤ (Set.range h.periodBasis) := by
  apply le_antisymm
  · -- `periodLatticeImage ⊆ span periodBasis`: every period vector
    -- lies in `span periodBasis` by the new `period_image_spanned`.
    intro v hv
    -- `v ∈ (periodLatticeImage data α).toIntSubmodule` unfolds (via
    -- `AddSubgroup.coe_toIntSubmodule`) to `v ∈ periodLatticeImage data α`.
    have hv' : v ∈ periodLatticeImage data α := hv
    rcases (mem_periodLatticeImage_iff data α v).mp hv' with ⟨γ, hγ⟩
    rw [← hγ]
    exact h.period_image_spanned γ
  · -- `span periodBasis ⊆ periodLatticeImage`: each `periodBasis i =
    -- periodVector (cycleGenerators i) ∈ periodLatticeImage`.
    rw [Submodule.span_le]
    rintro v ⟨i, rfl⟩
    rw [SetLike.mem_coe]
    -- Goal: `h.periodBasis i ∈ (periodLatticeImage data α).toIntSubmodule`.
    -- Reduce to membership in the AddSubgroup (defeq via SetLike).
    show h.periodBasis i ∈ periodLatticeImage data α
    rw [h.periodBasis_eq i]
    rw [mem_periodLatticeImage_iff]
    exact ⟨h.cycleGenerators i, rfl⟩

/-! ## Derived `DiscreteTopology` and `IsZLattice` instances -/

/-- **Derived `DiscreteTopology`** (refactored). Same as the legacy
`periodLatticeImage_discreteTopology_of_bundle` but using the new
bundle. -/
theorem periodLatticeImage_discreteTopology_of_bundle
    (h : PeriodLatticeSymplecticBundle data α) :
    DiscreteTopology (periodLatticeImage data α).toIntSubmodule := by
  rw [periodLatticeImage_toIntSubmodule_eq_span_periodBasis h]
  infer_instance

/-- **Derived `IsZLattice ℝ`** (refactored). Same as the legacy
`periodLatticeImage_isZLattice_of_bundle` but using the new bundle. -/
theorem periodLatticeImage_isZLattice_of_bundle
    (h : PeriodLatticeSymplecticBundle data α) :
    haveI := periodLatticeImage_discreteTopology_of_bundle h
    IsZLattice ℝ (periodLatticeImage data α).toIntSubmodule := by
  haveI := periodLatticeImage_discreteTopology_of_bundle h
  have h_eq := periodLatticeImage_toIntSubmodule_eq_span_periodBasis h
  refine ⟨?_⟩
  rw [h_eq]
  exact ZSpan.span_top h.periodBasis

end PeriodLatticeSymplecticBundle

/-! ## Legacy → symplectic conversion

The legacy `PeriodLatticeDiscretenessBundle` is strictly stronger (a
`Basis` provides a tuple + linear independence + spanning of
`data.H1`). The new bundle's `period_image_spanned` follows from the
legacy's `h1Basis.span_eq` + linearity of `periodVectorHom`. -/

namespace PeriodLatticeDiscretenessBundle

variable {data : PeriodPairingData X}
  {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}

/-- **Conversion to the symplectic bundle.** Forgets the
basis structure on `cycleGenerators` (now a tuple) and derives the new
geometric spanning condition from the legacy's full-basis assumption.

Note: this conversion compiles, but inhabitants of the legacy bundle
are classically never produced for `data = ofSmoothCycle X` (the
legacy `h1Basis : Basis (Fin 2g) ℤ (SmoothCycle X)` requires
`SmoothCycle X = 0`, false in general). The conversion is here for
refactor hygiene: code that previously took the legacy bundle can be
transitioned to the new bundle without breaking existing call sites. -/
noncomputable def toSymplectic
    (h : PeriodLatticeDiscretenessBundle data α) :
    PeriodLatticeSymplecticBundle data α where
  cycleGenerators := h.h1Basis
  periodBasis := h.periodBasis
  periodBasis_eq := h.periodBasis_eq
  period_image_spanned := by
    intro γ
    -- The legacy bundle gives `Submodule.span ℤ (Set.range h.h1Basis) = ⊤`.
    -- So every `γ ∈ data.H1` is in this span; apply `periodVectorHom`
    -- (a `ℤ`-linear hom) to get `periodVector γ ∈ Submodule.span ℤ
    -- (periodVectorHom '' range h1Basis) = span ℤ (range periodBasis)`.
    have h_span : (⊤ : Submodule ℤ data.H1)
        = Submodule.span ℤ (Set.range h.h1Basis) := h.h1Basis.span_eq.symm
    have hγ_mem : γ ∈ Submodule.span ℤ (Set.range h.h1Basis) := by
      rw [← h_span]; trivial
    -- The map `periodVectorHom data α : data.H1 →+ (Fin g → ℂ)` lifts to
    -- a `ℤ`-linear map; ℤ-linear maps preserve `ℤ`-span membership.
    have hlin := Submodule.span_le.mpr
      (show (Set.range h.h1Basis) ⊆
        (Submodule.span ℤ (Set.range h.periodBasis)).comap
          (periodVectorHom data α).toIntLinearMap from ?_)
    · exact hlin hγ_mem
    · rintro c ⟨i, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      show periodVector data α (h.h1Basis i)
        ∈ Submodule.span ℤ (Set.range h.periodBasis)
      rw [← h.periodBasis_eq i]
      exact Submodule.subset_span ⟨i, rfl⟩

end PeriodLatticeDiscretenessBundle

/-! ## Trivial inhabitant at `genus = 0`

The new bundle is trivially constructible at `genus X = 0` (the
`cycleGenerators` tuple has empty index `Fin 0`, the `periodBasis` is
the empty basis of the trivial space `Fin 0 → ℂ`, and the geometric
spanning condition is vacuous since every period vector is `0`).

This validates the refactor: the genus-0 case now flows through the
bundle cleanly, without the bypass that
`Manifold/PeriodLatticeRiemannSphere.lean` had to use for the legacy
bundle. -/

namespace PeriodLatticeSymplecticBundle

variable {data : PeriodPairingData X}
  {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}

/-- **`PeriodLatticeSymplecticBundle` is trivially constructible at
genus 0.** All four fields are vacuous / trivial. -/
noncomputable def trivial_at_genus_zero
    (hgenus : JacobianChallenge.genus X = 0) :
    PeriodLatticeSymplecticBundle data α := by
  -- Subsingleton ambient: `Fin (genus X) → ℂ` is `Fin 0 → ℂ ≃ {0}`.
  haveI hsub : Subsingleton (Fin (JacobianChallenge.genus X) → ℂ) := by
    rw [hgenus]
    haveI : Unique (Fin 0 → ℂ) := Pi.uniqueOfIsEmpty (fun _ : Fin 0 => ℂ)
    infer_instance
  -- The empty cycleGenerators tuple.
  refine
    { cycleGenerators := ?_
      periodBasis := ?_
      periodBasis_eq := ?_
      period_image_spanned := ?_ }
  · -- `Fin (2 * 0) → data.H1`: rewrite to `Fin 0 → data.H1` and use
    -- `Fin.elim0`.
    rw [hgenus, Nat.mul_zero]
    exact Fin.elim0
  · -- `Basis (Fin (2 * 0)) ℝ (Fin 0 → ℂ)`: the empty basis of the
    -- trivial space. Use `Module.finBasisOfFinrankEq` or `Basis.empty`.
    -- Easiest: `Basis.empty` on `Fin 0` since the codomain is
    -- subsingleton (hence has rank 0).
    rw [hgenus, Nat.mul_zero]
    haveI : Unique (Fin 0 → ℂ) := Pi.uniqueOfIsEmpty (fun _ : Fin 0 => ℂ)
    haveI : Subsingleton (Fin 0 → ℂ) := inferInstance
    exact Basis.empty _
  · -- Compatibility: `∀ i : Fin (2 * genus X), …`. At `2 * 0 = 0`,
    -- `Fin 0` is empty, so `intro i` then `exact i.elim0`.
    intro i
    -- The Fin (2 * genus X) value `i` doesn't normalise to Fin 0 without
    -- the rewrite — but we can still apply `Subsingleton.elim` on both
    -- sides since the codomain (`Fin g → ℂ`) is subsingleton.
    exact Subsingleton.elim _ _
  · -- Geometric spanning: every period vector is 0 (subsingleton
    -- codomain), and 0 is in any submodule.
    intro γ
    have : periodVector data α γ = 0 := Subsingleton.elim _ _
    rw [this]
    exact Submodule.zero_mem _

end PeriodLatticeSymplecticBundle

/-! ## Composition with `PeriodLatticeAnalyticHypotheses`

Mirrors `PeriodLatticeAnalyticHypotheses.ofBundle` for the new bundle. -/

/-- **From the symplectic bundle, build the full
`PeriodLatticeAnalyticHypotheses`** via the slim constructor.
Parallels `PeriodLatticeAnalyticHypotheses.ofBundle`. -/
noncomputable def PeriodLatticeAnalyticHypotheses.ofSymplecticBundle
    {data : PeriodPairingData X}
    {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
    (h : PeriodLatticeSymplecticBundle data α) :
    PeriodLatticeAnalyticHypotheses data α :=
  PeriodLatticeAnalyticHypotheses.ofDiscrete data α
    (PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle h)
    (PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle h)

/-! ## Genus-0 → PeriodLatticeOfRankTwoG via the symplectic bundle

Validates the refactor: the genus-0 analytic Jacobian construction
now flows through the bundle CLEANLY (no bypass). -/

/-- **Genus-0 `PeriodLatticeOfRankTwoG` via the symplectic bundle.**
At genus 0, the symplectic bundle is trivially constructible
(`trivial_at_genus_zero`), so `PeriodLatticeOfRankTwoG.ofPeriodPairing`
fires unconditionally on any pairing data + basis. -/
noncomputable def PeriodLatticeOfRankTwoG.ofGenusZeroSymplectic
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (hgenus : JacobianChallenge.genus X = 0) :
    PeriodLatticeOfRankTwoG X :=
  PeriodLatticeOfRankTwoG.ofPeriodPairing data α
    (PeriodLatticeAnalyticHypotheses.ofSymplecticBundle
      (PeriodLatticeSymplecticBundle.trivial_at_genus_zero (data := data)
        (α := α) hgenus))

/-! ## Equivalence with the bypass construction at genus 0

The bypass in `Manifold/PeriodLatticeRiemannSphere.lean`
(`PeriodLatticeOfRankTwoG.trivialAtGenusZero`) gives `lattice = ⊥`.
The bundle route here gives `lattice = periodLatticeImage data α`.
At genus 0, the ambient `Fin (genus X) → ℂ` is subsingleton, so
`periodLatticeImage data α = ⊥` (the only subgroup of a singleton
group). The two constructions therefore produce identical
`PeriodLatticeOfRankTwoG` data. -/

/-- **At genus 0, `periodLatticeImage` is `⊥`.** Direct consequence of
the subsingleton ambient `Fin 0 → ℂ`. -/
theorem periodLatticeImage_eq_bot_of_genus_zero
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (hgenus : JacobianChallenge.genus X = 0) :
    periodLatticeImage data α = ⊥ := by
  haveI : Subsingleton (Fin (JacobianChallenge.genus X) → ℂ) := by
    rw [hgenus]
    haveI : Unique (Fin 0 → ℂ) := Pi.uniqueOfIsEmpty (fun _ : Fin 0 => ℂ)
    infer_instance
  -- Both `periodLatticeImage` and `⊥` are AddSubgroups of a subsingleton
  -- ambient; their underlying sets agree (both = {0}).
  ext v
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · -- `v` is in the singleton ambient, hence `= 0`, hence in `⊥`.
    have : v = 0 := Subsingleton.elim _ _
    rw [this]
    exact zero_mem _
  · -- `v ∈ ⊥` means `v = 0`; show `0 ∈ periodLatticeImage`.
    rw [AddSubgroup.mem_bot] at *
    rename_i hv
    rw [hv]
    exact zero_mem _

/-- **The genus-0 bundle-route and bypass constructions agree on the
lattice field.** -/
theorem PeriodLatticeOfRankTwoG.ofGenusZeroSymplectic_lattice
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (hgenus : JacobianChallenge.genus X = 0) :
    (PeriodLatticeOfRankTwoG.ofGenusZeroSymplectic data α hgenus).lattice
      = ⊥ :=
  periodLatticeImage_eq_bot_of_genus_zero data α hgenus

end JacobianChallenge

end
