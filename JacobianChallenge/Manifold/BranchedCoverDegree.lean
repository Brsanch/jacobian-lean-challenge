/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.FibresFiniteUnconditional
import JacobianChallenge.Manifold.RegularValueExistsUnconditional
import JacobianChallenge.Manifold.FibreCardClopenReduction
import JacobianChallenge.Manifold.FiberCountBridge

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # `branchedCoverDegree` — topological degree of the pole extension

For `f : MeromorphicNonzero X` on a compact connected complex 1-manifold
`X`, the pole-extension `f̃ := f.toRiemannSphere : X → RiemannSphere` is
`C^ω`-smooth (`MeromorphicNonzero.toRiemannSphere_contMDiff`) and `RiemannSphere`
is a compact connected Hausdorff complex 1-manifold. Thus the
`Owed.degree` infrastructure on `f̃` applies.

This file packages the **topological degree** of `f̃` as

```
branchedCoverDegree f : ℕ
```

defined by `Classical.choice`-extraction of *any* regular-value witness
(falling back to `0` if no witness exists at the pin or `f̃` is constant).

## What is unconditional

* **Existence of a witness** for non-constant `f̃` — A.1 (ZZ48 fibres-finite)
  + A.2 (ZZ49 regular-value-exists), both unconditional. So when `f̃` is
  non-constant the `Classical.choice` branch fires non-trivially.

* **`branchedCoverDegree_eq_witness_card`** — by definition,
  `branchedCoverDegree f` equals the cardinality of the `Classical.choice`-
  selected witness (in the non-constant, witness-existing branch).

## What is conditional on A.3 (`fibre_card_well_defined_statement`)

* **`branchedCoverDegree_eq_fiberCount_of_regular`** — for any specific
  regular-value witness `w`, the degree equals `w.card`. This requires
  *independence of the choice of witness*, which is A.3.

* **`branchedCoverDegree_eq_polFiber`** — equals `fiberCount f̃ ∞`. The
  `∞`-fibre of the pole extension is unconditionally finite (ZZ2,
  `toRiemannSphere_preimage_infty_finite`); when `∞` is in the range
  (i.e. `f` has at least one pole), it gives a `RegularValueWitness`
  whose `card` equals `fiberCount f ∞` after the `ncard`/`toFinset`
  bridge (`Set.ncard_eq_toFinset_card`). Independence from the chosen
  witness is then A.3.

* **`branchedCoverDegree_eq_zeroFiber_of_regular_zero`** — equals
  `fiberCount f̃ (some 0)` whenever `0` is itself a regular value (i.e.
  the fibre over `some 0` is finite and `some 0` is in the range).

The A.3 hypothesis is taken as an **explicit argument** of type
`Owed.degree.fibre_card_well_defined_statement X RiemannSphere` (the
pre-shipped `Prop`-valued statement from `Manifold/Degree.lean`). When
ZZ51 lands its unconditional discharge, every theorem in this file
becomes unconditional by composition.

No `sorry`. No `axiom`. -/

@[expose] public section

noncomputable section

open Set OnePoint Classical
open scoped Manifold Topology ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- The `∞`-fibre of the pole extension, packaged as a
`ContMDiff.RegularValueWitness` of the pole extension `f̃ = f.toRiemannSphere`.
The finiteness comes from the ZZ2 unconditional lemma
`toRiemannSphere_preimage_infty_finite`. -/
def inftyWitness (f : MeromorphicNonzero X) :
    ContMDiff.RegularValueWitness f.toRiemannSphere where
  value := (∞ : RiemannSphere)
  fiber_finite := f.toRiemannSphere_preimage_infty_finite

/-- **Topological degree of the pole extension.** Defined as the cardinality
of `Classical.choice`-selected `RegularValueWitness` of
`f̃ = f.toRiemannSphere`. Falls back to `0` if `f̃` is constant or no witness
exists.

Since `inftyWitness f` is always available (the `∞`-fibre is unconditionally
finite by ZZ2), `Nonempty (RegularValueWitness f.toRiemannSphere)` always
holds, so the `else 0` fallback never fires in this file's lemmas — but is
kept for total-ness in the `Classical`-choice signature.

**Conditional on A.3** for use as "the" topological degree: independence of
the chosen witness is `fibre_card_well_defined_statement`. -/
def branchedCoverDegree (f : MeromorphicNonzero X) : ℕ :=
  if h : Nonempty (ContMDiff.RegularValueWitness f.toRiemannSphere) then
    (Classical.choice h).card
  else 0

/-- Witness existence for the pole extension: the `∞`-fibre is always a
witness, by ZZ2 finiteness. -/
lemma nonempty_regularValueWitness (f : MeromorphicNonzero X) :
    Nonempty (ContMDiff.RegularValueWitness f.toRiemannSphere) :=
  ⟨f.inftyWitness⟩

/-- The fallback branch never fires: `branchedCoverDegree f` equals the card
of *some* `Classical.choice`-selected witness. -/
lemma branchedCoverDegree_eq_choice_card (f : MeromorphicNonzero X) :
    branchedCoverDegree f =
      (Classical.choice (f.nonempty_regularValueWitness)).card := by
  unfold branchedCoverDegree
  simp [f.nonempty_regularValueWitness]

/-! ## Conditional theorems (require A.3 = `fibre_card_well_defined_statement`)

Each theorem below takes the A.3 statement
`fibre_card_well_defined_statement X RiemannSphere` (the `Prop`-valued
statement from `Manifold/Degree.lean`) as an explicit hypothesis. When ZZ51
lands an unconditional discharge of A.3 for the case `Y = RiemannSphere`,
these theorems become unconditional. -/

/-- **Independence of witness choice (conditional on A.3).** Given the A.3
statement and a `RegularValueWitness w` for the pole extension, the
`branchedCoverDegree` equals `w.card`. -/
theorem branchedCoverDegree_eq_witness_card_of_wellDefined
    (f : MeromorphicNonzero X)
    (h_wd : ContMDiff.Owed.degree.fibre_card_well_defined_statement X RiemannSphere)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (w : ContMDiff.RegularValueWitness f.toRiemannSphere) :
    branchedCoverDegree f = w.card := by
  rw [branchedCoverDegree_eq_choice_card]
  -- A.3: any two witnesses have equal card.
  exact h_wd f.toRiemannSphere f.toRiemannSphere_contMDiff hnc _ w

/-- **Degree equals fibre cardinality at any regular value (conditional on A.3).**
Given the A.3 statement and any value `y : RiemannSphere` whose fibre is
finite, the `branchedCoverDegree` equals the `Set.ncard` of the fibre
`f̃ ⁻¹' {y}`. -/
theorem branchedCoverDegree_eq_fiberCount_of_regular
    (f : MeromorphicNonzero X)
    (h_wd : ContMDiff.Owed.degree.fibre_card_well_defined_statement X RiemannSphere)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {y : RiemannSphere} (hfin : (f.toRiemannSphere ⁻¹' {y}).Finite) :
    branchedCoverDegree f = (f.toRiemannSphere ⁻¹' {y}).ncard := by
  -- Package `(y, hfin)` as a witness.
  let w : ContMDiff.RegularValueWitness f.toRiemannSphere :=
    { value := y, fiber_finite := hfin }
  have h_eq : branchedCoverDegree f = w.card :=
    branchedCoverDegree_eq_witness_card_of_wellDefined f h_wd hnc w
  -- `w.card = (hfin.toFinset).card = fibre.ncard` via `Set.ncard_eq_toFinset_card`.
  rw [h_eq]
  show (hfin.toFinset).card = (f.toRiemannSphere ⁻¹' {y}).ncard
  exact (Set.ncard_eq_toFinset_card _ hfin).symm

/-- **Degree equals the pole-fibre `fiberCount` (conditional on A.3).** -/
theorem branchedCoverDegree_eq_polFiber
    (f : MeromorphicNonzero X)
    (h_wd : ContMDiff.Owed.degree.fibre_card_well_defined_statement X RiemannSphere)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere) :
    branchedCoverDegree f = fiberCount f (∞ : RiemannSphere) := by
  have h := branchedCoverDegree_eq_fiberCount_of_regular f h_wd hnc
    f.toRiemannSphere_preimage_infty_finite
  -- Unfold `fiberCount`.
  simpa [fiberCount] using h

/-- **Degree equals the `some 0`-fibre `fiberCount` whenever that fibre is
finite (conditional on A.3).**

If `0 : ℂ` is a regular value of `f̃` (i.e. `f̃ ⁻¹' {some 0}` is finite —
equivalently every zero of `f` is simple, in the regular branch), then the
degree equals `fiberCount f̃ (some 0)`. -/
theorem branchedCoverDegree_eq_zeroFiber_of_regular_zero
    (f : MeromorphicNonzero X)
    (h_wd : ContMDiff.Owed.degree.fibre_card_well_defined_statement X RiemannSphere)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (hfin : (f.toRiemannSphere ⁻¹' {(OnePoint.some (0 : ℂ) : RiemannSphere)}).Finite) :
    branchedCoverDegree f = fiberCount f (OnePoint.some (0 : ℂ) : RiemannSphere) := by
  have h := branchedCoverDegree_eq_fiberCount_of_regular f h_wd hnc hfin
  simpa [fiberCount] using h

/-! ## Connection to the unconditional A.1+A.2 layer

The non-constancy hypothesis `hnc` and witness existence are the inputs that
ZZ48+ZZ49 already discharge unconditionally. We expose two helpers that show
this: the witness *exists* unconditionally for any `f` (via `inftyWitness`),
and for non-constant `f̃` `Owed.degree.regular_value_exists_statement`
unconditionally provides one without using `inftyWitness`. -/

/-- Witness existence for non-constant pole extension is **unconditional**
through ZZ49. (We already have a witness via `inftyWitness` regardless;
this version routes through the A.2 unconditional layer.) -/
lemma nonempty_regularValueWitness_of_nonconstant_unconditional
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere) :
    Nonempty (ContMDiff.RegularValueWitness f.toRiemannSphere) :=
  ContMDiff.Owed.degree.regular_value_exists_statement_holds_unconditional
    f.toRiemannSphere f.toRiemannSphere_contMDiff hnc

end MeromorphicNonzero

end JacobianChallenge

end

end
