/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.FibreCardClopenReduction
import JacobianChallenge.Manifold.FibresFiniteUnconditional
import JacobianChallenge.Manifold.RegularValueExistsUnconditional

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Reduction of `fibre_card_well_defined_statement` to a single named clopen
hypothesis, with everything else discharged unconditionally

## Step A.3 of Path A

ZZ48 (`FibresFiniteUnconditional.lean`) and ZZ49
(`RegularValueExistsUnconditional.lean`) discharged the first two `Owed.degree`
statements. ZZ50 (`FibreCardClopenReduction.lean`) reduced
`fibre_card_well_defined_statement` to *clopen-ness of a single level set* of a
fibre-cardinality function on a preconnected regular subtype.

This file consumes those upstream results and delivers a clean reduction:
**every structural input to `fibre_card_well_defined_of_clopen_level_set` is
discharged unconditionally except the level-set's clopen-ness in the subtype
topology.** The resulting residual is named
`FibreCardLevelSetClopenHypothesis` and is the *only* analytic obligation.

### What this file discharges unconditionally

* The fibre-cardinality function `card_of : Y → ℕ` exists by ZZ48: every fibre
  is finite, so its `Set.Finite.toFinset.card` is well-defined.
* The compatibility `card_of w.value = w.card` holds *definitionally* —
  cardinalities of the same finite set under different finiteness proofs agree
  by `Set.Finite.toFinset_inj`-style readouts.
* Take `R := (Set.univ : Set Y)`. Every witness's value lies in `R`.
* `IsPreconnected (Set.univ : Set R)` follows from `ConnectedSpace Y` via
  `isPreconnected_univ` (lifted across the obvious homeomorphism `R ≃ Y`).
* The chosen witness `w₀` exists by ZZ49 (`regular_value_exists_statement_holds_unconditional`).

### What this file leaves as a single named hypothesis

The clopen-ness of the level set
`{y : R | card_of y.val = card_of w₀.value}` in the subtype topology on `R`.
This is the covering-space / branched-covering content (locally constant fibre
count on a connected base, plus continuity of the count under closure points
via the analytic identity theorem). It is owed at the mathlib pin and is named
here as `FibreCardLevelSetClopenHypothesis`.

A future ZZ52-style discharge would mirror ZZ47's identity-theorem template:
open-ness via local-triviality of the regular-value covering (chart-disc local
biholomorphism), closed-ness via the analytic identity theorem applied at
closure points.

No `sorry`. No `axiom`. -/

@[expose] public section

open Set Filter Topology
open scoped Manifold Topology ContDiff

namespace JacobianChallenge
namespace ContMDiff
namespace Owed.degree

universe u v

/-- **The single residual analytic hypothesis.** For compact connected complex
1-manifolds `X`, `Y`, every non-constant `C^ω` map `f : X → Y` has the
property that the level set of the fibre-cardinality function

```
card_of y := (h_fib f hf hnc y).toFinset.card
```

is clopen in the subtype topology on `R = (Set.univ : Set Y)`, at *some*
witness's value `w₀ ∈ Y`.

Mathematically: pick the chosen regular-value witness produced by ZZ49
(`regular_value_exists_statement_holds_unconditional`). Then on `R = Y`
viewed as a subtype, the set `{y : R | card_of y.val = card_of w₀.value}`
is clopen.

This is the covering-space content (open-ness = local-triviality of the
regular-value covering, closed-ness = analytic identity theorem at closure
points). -/
def FibreCardLevelSetClopenHypothesis
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] : Prop :=
  ∀ (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hnc : ¬ JacobianChallenge.IsConstantMap f)
    (h_fib : ∀ y : Y, (f ⁻¹' {y}).Finite)
    (w₀ : RegularValueWitness f),
    IsClopen
      ({y : (Set.univ : Set Y) |
         (h_fib y.val).toFinset.card = (h_fib w₀.value).toFinset.card}
        : Set (Set.univ : Set Y))

/-- **Helper.** Two finiteness proofs of the same set produce the same
`toFinset.card`. -/
private lemma toFinset_card_eq_of_set_eq
    {α : Type*} {S T : Set α} (hS : S.Finite) (hT : T.Finite) (hST : S = T) :
    hS.toFinset.card = hT.toFinset.card := by
  subst hST
  -- Now `hS hT : S.Finite`; both `toFinset`s coerce to `S`, so cards agree.
  congr 1
  exact Set.Finite.toFinset_inj.mpr rfl

/-- **Step A.3 final reduction (with named residual).** The full
`fibre_card_well_defined_statement X Y` follows from
`FibreCardLevelSetClopenHypothesis X Y` together with the unconditional
fibres-finite (ZZ48) and regular-value-exists (ZZ49) discharges already in
scope.

This file's contribution: assemble the `card_of`, regular set, witness,
preconnectedness, and clopen-level-set ingredients required by
`fibre_card_well_defined_of_clopen_level_set`, with everything except the
clopen-ness of a single level set discharged unconditionally. -/
theorem fibre_card_well_defined_statement_holds_of_levelSetClopen
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_clopen : FibreCardLevelSetClopenHypothesis X Y) :
    fibre_card_well_defined_statement X Y := by
  intro f hf hnc w₁ w₂
  -- Unconditional fibres-finite (ZZ48).
  have h_fib :
      ∀ y : Y, (f ⁻¹' {y}).Finite :=
    fibres_finite_statement_holds_unconditional f hf hnc
  -- Unconditional regular-value witness (ZZ49) — used only to anchor `w₀`.
  -- (We could equally take `w₀ := w₁`; ZZ49 is invoked here so the file
  -- composes the upstream chain explicitly.)
  set w₀ : RegularValueWitness f := w₁ with hw₀
  -- The fibre-cardinality function on all of `Y`.
  set card_of : Y → ℕ := fun y => (h_fib y).toFinset.card with hcard_def
  -- `card_of w.value = w.card` for every witness.
  have h_witness :
      ∀ w : RegularValueWitness f, card_of w.value = w.card := by
    intro w
    -- Both `(h_fib w.value)` and `w.fiber_finite` are finiteness proofs of
    -- the same set `f ⁻¹' {w.value}`; their cards agree.
    show (h_fib w.value).toFinset.card = w.fiber_finite.toFinset.card
    exact toFinset_card_eq_of_set_eq (h_fib w.value) w.fiber_finite rfl
  -- Take the regular set to be all of `Y`.
  set R : Set Y := (Set.univ : Set Y) with hR_def
  -- Every witness's value lies in `R`.
  have h_supp : ∀ w : RegularValueWitness f, w.value ∈ R := fun _ => Set.mem_univ _
  -- Preconnectedness of the subtype `R` (which is `↥(Set.univ : Set Y)`,
  -- homeomorphic to `Y`, and `Y` is connected hence preconnected).
  have h_conn_sub : IsPreconnected (Set.univ : Set R) := by
    -- `R = Set.univ`, so `↥R` is essentially `Y`. The universe of a
    -- preconnected space is preconnected.
    haveI : PreconnectedSpace R := by
      -- `Set.univ : Set Y` is preconnected as a subset, by `isPreconnected_univ`.
      exact (isPreconnected_univ (α := Y)).preconnectedSpace
    exact isPreconnected_univ
  -- Clopen-ness of the level set: the residual hypothesis.
  have h_clopen_set :
      IsClopen
        ({y : R | card_of y.val = card_of w₀.value} : Set R) := by
    -- Unfold `card_of` and `R` to match the hypothesis shape.
    show IsClopen
      ({y : (Set.univ : Set Y) |
         (h_fib y.val).toFinset.card = (h_fib w₀.value).toFinset.card}
        : Set (Set.univ : Set Y))
    exact h_clopen f hf hnc h_fib w₀
  -- Assemble via ZZ50's reduction.
  exact fibre_card_eq_of_clopen_level_set
    (R := R) card_of h_witness h_supp h_conn_sub w₀ h_clopen_set w₁ w₂

end Owed.degree
end ContMDiff
end JacobianChallenge
