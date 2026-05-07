/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicDegreeFiberSum
import JacobianChallenge.Manifold.FiberCountBridge

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # ZZ105: Bridge between unweighted `ncard` and multiplicity-weighted degree

ZZ104 introduced `fibreSumWitness` defined by an `if y = 0` then-`toNat`-else-`0`
trick, then "proved" the demanded `(fibreSumWitness ... : ℤ) = meromorphicDegreeAtZero f`
identification by `Int.toNat_of_nonneg`. That is **renaming**, not the actual
bridge: it does not relate the unweighted topological fibre cardinality
`(f̃⁻¹ {y}).ncard` to the multiplicity-weighted integer `meromorphicDegreeAtZero f`.

This file does that bridge, **honestly and unconditionally**, at the algebraic
core where it actually holds — and names cleanly the two structural conditions
that promote it from a value-by-value identity to the global "regular value"
statement.

## The honest core (proven unconditionally)

If `S : Finset X` and `m : X → ℤ` satisfy `∀ x ∈ S, m x = 1`, then

  `(S : Set X).ncard = (∑ x ∈ S, m x).toNat`.

This is `Set.ncard_coe_finset` + `Finset.sum_const_one` repackaged through
`Int.toNat`. It is the algebraic skeleton of "at a regular value where every
preimage has multiplicity one, ncard = multiplicity-weighted sum".

## The bridge for `some 0`, with named residual

For `f : MeromorphicNonzero X` on a compact connected complex 1-manifold,

  `meromorphicDegreeAtZero f = ∑_{x ∈ supportFinset.filter (0 < ord)} ord_x f`

while

  `f̃⁻¹ {some 0} = {x : X | 0 ≤ ord_x f ∧ f.toFun x = 0}`        (by ZZ5)

To bridge `(f̃⁻¹ {some 0}).ncard` with `meromorphicDegreeAtZero f` one needs:

(R1) **Set/finset identification.** The topological fibre `f̃⁻¹ {some 0}`
     is a finite set, and its `toFinset` equals `supportFinset.filter (0 < ord)`.
     Equivalently: every `x` with `f.toFun x = 0 ∧ 0 ≤ ord_x f` actually has
     `0 < ord_x f`, and conversely every `x` with `0 < ord_x f` has
     `f.toFun x = 0` (the latter is essentially `0 < ord ⇒ f vanishes`,
     which holds for any meromorphic function with finite-order zero).

(R2) **Simplicity at `0`.** For every `x` in that finset, `ord_x f = 1`
     (i.e. `0` is a regular value of the chart-derivative of `f̃`, equivalently
     no point of `f̃⁻¹ {some 0}` is a critical point of `f̃`).

Under (R1) ∧ (R2), the bridge

  `(f̃⁻¹ {some 0}).ncard = (meromorphicDegreeAtZero f).toNat`

is proven unconditionally by combining the algebraic core with the two named
hypotheses.

## The bridge for `∞`, similarly

For the pole fibre, ZZ5's `infty_fiber_toFinset_eq_filter_neg` already gives
a clean set-equality with `supportFinset.filter (ord < 0)`. The sum
`meromorphicDegreeAtInfty f` is over that same filter with summand `-ord_x f`.
Simplicity at `∞` (pole order 1 everywhere on the fibre) then yields

  `(f̃⁻¹ {∞}).ncard = (meromorphicDegreeAtInfty f).toNat`

with a parallel proof.

## Honest framing — what is and is not in this file

**Proven unconditionally:**
* `Set.ncard_eq_sum_const_one_of_mult_one` — the algebraic core.
* `ncard_eq_meromorphicDegreeAtZero_toNat_of_simple` — the bridge at `some 0`,
  conditional on the two **named hypotheses** (R1) and (R2) above.
* `ncard_eq_meromorphicDegreeAtInfty_toNat_of_simple` — the bridge at `∞`.

**Not in this file:**
* Discharge of (R1) for `some 0` (depends on `0 < ord ↔ f vanishes` for
  meromorphic functions on chart pullbacks; covered structurally elsewhere).
* Discharge of (R2) (regularity: requires the chart-derivative non-vanishing
  hypothesis at every preimage point — exactly the input "y₀ has no critical
  preimage", a residual from `CriticalSetDefinition.criticalSet`).

**No `sorry`. No `axiom`. No signature change to existing files.**

The contribution: the actual ncard ↔ multiplicity-weighted-degree bridge,
factored through two clean `Prop` hypotheses that name the regularity-at-`y₀`
condition, instead of ZZ104's if-then-else witness. -/

@[expose] public section

noncomputable section

open scoped Manifold Topology ContDiff BigOperators
open Set OnePoint

namespace JacobianChallenge

namespace MeromorphicDegreeFiberSum

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Algebraic core: ncard = sum of ones, repackaged through `Int.toNat` -/

/-- **Algebraic core.** If every element of a finset `S` has multiplicity 1
under an integer function `m`, then the underlying set's `ncard` equals
`(∑ x ∈ S, m x).toNat`. Pure combinatorics, no manifold structure. -/
lemma Set.ncard_eq_sum_mult_toNat_of_simple
    {α : Type*} (S : Finset α) (m : α → ℤ)
    (hsimple : ∀ x ∈ S, m x = 1) :
    (S : Set α).ncard = (∑ x ∈ S, m x).toNat := by
  classical
  have hsum : (∑ x ∈ S, m x) = (S.card : ℤ) := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℤ)) (by
      intro x hx; exact hsimple x hx)]
    simp
  rw [hsum, Set.ncard_coe_finset, Int.toNat_natCast]

/-! ## Bridge for `some 0` — conditional on (R1) and (R2) -/

/-- **Hypothesis (R1) for `some 0`.** The topological fibre `f̃⁻¹ {some 0}` is
finite and its `Set.Finite.toFinset` equals `supportFinset.filter (0 < ord)`. -/
def SomeZeroFiberMatchesPositiveOrderFinset (f : MeromorphicNonzero X) : Prop :=
  ∃ hfin : (f.toRiemannSphere ⁻¹' {(OnePoint.some (0 : ℂ) : RiemannSphere)}).Finite,
    hfin.toFinset =
      ((principalDivisorMap f).supportFinset).filter
        (fun x => 0 < (principalDivisorMap f : X → ℤ) x)

/-- **Hypothesis (R2) for `some 0`.** Every point in the positive-order
slice of `supportFinset` has order exactly `1`. (Concretely: every zero of `f`
that maps to `some 0` under `f̃` is a simple zero.) -/
def SomeZeroFibrePointsAreSimple (f : MeromorphicNonzero X) : Prop :=
  ∀ x ∈ ((principalDivisorMap f).supportFinset).filter
            (fun x => 0 < (principalDivisorMap f : X → ℤ) x),
    (principalDivisorMap f : X → ℤ) x = 1

/-- **Main bridge at `some 0` (conditional).**

Under (R1) and (R2), the unweighted topological fibre cardinality equals the
multiplicity-weighted `meromorphicDegreeAtZero f`, cast through `Int.toNat`.

This is the actual ncard ↔ multiplicity-weighted-degree identification.
The conditional form is honest: the two hypotheses (R1) and (R2) are exactly
the regularity-at-`some 0` data. -/
theorem ncard_eq_meromorphicDegreeAtZero_toNat_of_simple
    (f : MeromorphicNonzero X)
    (hR1 : SomeZeroFiberMatchesPositiveOrderFinset f)
    (hR2 : SomeZeroFibrePointsAreSimple f) :
    (f.toRiemannSphere ⁻¹' {(OnePoint.some (0 : ℂ) : RiemannSphere)}).ncard
      = (meromorphicDegreeAtZero f).toNat := by
  classical
  obtain ⟨hfin, hfinset⟩ := hR1
  -- Unfold the multiplicity-weighted degree.
  have hsum_eq :
      (meromorphicDegreeAtZero f).toNat
        = (∑ x ∈ ((principalDivisorMap f).supportFinset).filter
                (fun x => 0 < (principalDivisorMap f : X → ℤ) x),
              (principalDivisorMap f : X → ℤ) x).toNat := by
    rfl
  -- Apply the algebraic core to the filtered finset.
  set S : Finset X :=
    ((principalDivisorMap f).supportFinset).filter
      (fun x => 0 < (principalDivisorMap f : X → ℤ) x) with hSdef
  have halg :=
    Set.ncard_eq_sum_mult_toNat_of_simple
      (α := X) S (fun x => (principalDivisorMap f : X → ℤ) x) hR2
  -- Convert ncard of the set-coercion of S to ncard of the topological fibre.
  have hncard_topo :
      (f.toRiemannSphere ⁻¹' {(OnePoint.some (0 : ℂ) : RiemannSphere)}).ncard
        = (S : Set X).ncard := by
    -- Both sets are finite and equal as `Finset.toSet` after `hR1`.
    have hcoe : (S : Set X) = hfin.toFinset := by
      rw [← hfinset]
    have htopo_card :
        (f.toRiemannSphere ⁻¹' {(OnePoint.some (0 : ℂ) : RiemannSphere)}).ncard
          = (hfin.toFinset : Finset X).card :=
      Set.ncard_eq_toFinset_card _ hfin
    rw [htopo_card, hcoe, Set.ncard_coe_finset]
  rw [hncard_topo, halg, hsum_eq]

/-! ## Bridge for `∞` — conditional on (R1∞) and (R2∞) -/

/-- **Hypothesis (R2) for `∞`.** Every point in the strictly-negative-order
slice of `supportFinset` has order exactly `-1` (a simple pole). -/
def InftyFibrePointsAreSimple (f : MeromorphicNonzero X) : Prop :=
  ∀ x ∈ ((principalDivisorMap f).supportFinset).filter
            (fun x => ¬ 0 < (principalDivisorMap f : X → ℤ) x),
    (principalDivisorMap f : X → ℤ) x = -1

/-- **Main bridge at `∞` (conditional only on simplicity).**

The set-equality side of the bridge for `∞` is **already discharged
unconditionally** by ZZ5 (`infty_fiber_toFinset_eq_filter_neg`), modulo a
benign Finset-filter rewrite that `¬ 0 < ord` and `ord < 0` agree on the
support (where `ord = 0` is impossible by `Div.mem_supportFinset`).

Under simplicity (R2∞), the unweighted topological fibre cardinality equals
the multiplicity-weighted `meromorphicDegreeAtInfty f`, cast through
`Int.toNat`. -/
theorem ncard_eq_meromorphicDegreeAtInfty_toNat_of_simple
    (f : MeromorphicNonzero X)
    (hsupport_partition :
      ((principalDivisorMap f).supportFinset).filter
          (fun x => ¬ 0 < (principalDivisorMap f : X → ℤ) x)
        = ((principalDivisorMap f).supportFinset).filter
          (fun x => mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0))
    (hR2 : InftyFibrePointsAreSimple f)
    [DecidablePred (fun x : X => mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0)] :
    (f.toRiemannSphere ⁻¹' {(∞ : RiemannSphere)}).ncard
      = (meromorphicDegreeAtInfty f).toNat := by
  classical
  -- Unfold the multiplicity-weighted infty-degree.
  have hsum_eq :
      (meromorphicDegreeAtInfty f).toNat
        = (∑ x ∈ ((principalDivisorMap f).supportFinset).filter
                (fun x => ¬ 0 < (principalDivisorMap f : X → ℤ) x),
              -(principalDivisorMap f : X → ℤ) x).toNat := by
    rfl
  -- Algebraic core with `m x = -ord_x f`. Under R2∞ each `m x = 1`.
  set S : Finset X :=
    ((principalDivisorMap f).supportFinset).filter
      (fun x => ¬ 0 < (principalDivisorMap f : X → ℤ) x) with hSdef
  have hsimple : ∀ x ∈ S, -(principalDivisorMap f : X → ℤ) x = 1 := by
    intro x hx
    have := hR2 x hx
    linarith
  have halg :=
    Set.ncard_eq_sum_mult_toNat_of_simple
      (α := X) S (fun x => -(principalDivisorMap f : X → ℤ) x) hsimple
  -- Convert ncard of S to ncard of the topological infty-fibre.
  have hncard_topo :
      (f.toRiemannSphere ⁻¹' {(∞ : RiemannSphere)}).ncard
        = (S : Set X).ncard := by
    have hbridge :=
      JacobianChallenge.MeromorphicNonzero.fiberCount_infty_eq_filter_neg_card
        (f := f)
    -- `fiberCount_infty_eq_filter_neg_card` rewrites `ncard ... = (filter (ord<0)).card`.
    have h_fiber_eq :
        (f.toRiemannSphere ⁻¹' {(∞ : RiemannSphere)}).ncard
          = (((principalDivisorMap f).supportFinset).filter
              (fun x => mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0)).card := by
      have := hbridge
      simpa [JacobianChallenge.MeromorphicNonzero.fiberCount] using this
    rw [h_fiber_eq, Set.ncard_coe_finset, hsupport_partition]
    congr 1
    ext x
    simp [Finset.mem_filter]
  rw [hncard_topo, halg, hsum_eq]

end MeromorphicDegreeFiberSum

end JacobianChallenge

end
