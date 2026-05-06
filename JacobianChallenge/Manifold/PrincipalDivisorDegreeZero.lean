/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ZeroCountEqPoleCount
import JacobianChallenge.Manifold.MeromorphicDegreeFiberSumEquivalences
import JacobianChallenge.Manifold.ResidueTheorem

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Step A.5 — `(principalDivisorMap f).degree = 0` modulo a single named hypothesis

For `f : MeromorphicNonzero X` on a compact connected complex 1-manifold,
the residue-theorem conclusion

  `(principalDivisorMap f).degree = 0`

is, by `signedMult_eq_zeroCount_sub_poleCount` (proven in
`Manifold/ResidueViaTopologicalDegree.lean`), the same `Prop` as

  `zeroCount f = poleCount f`,

i.e. the multiplicity-weighted equality of the zero-fibre and pole-fibre
sums of the pole-extension `f̃ : X → S² = OnePoint ℂ`.

The four named global statements at this pin are all pairwise
`Iff`-equivalent (proven in `MeromorphicDegreeFiberSumEquivalences.lean`):

* `R5_principal_degree_zero_statement X` — the per-`f` form
  `∀ f, (principalDivisorMap f).degree = 0`.
* `ResidueTheorem X` — the named `Prop` (literally the same as `R5`).
* `(∀ f, TopologicalDegreeFibreBalance_hypothesis f)` — the Route-B
  bundle.
* `(∀ f, meromorphicDegreeAtZero f = meromorphicDegreeAtInfty f)`
  — the multiplicity-weighted fibre-balance form.

This file is an **explicit consolidation chip**: it exposes the
per-`f` discharge

  `zeroCount f = poleCount f`

modulo a single named hypothesis `R5_principal_degree_zero_statement X`,
and similarly for `(principalDivisorMap f).degree = 0`. Every Iff
chain used below is already `sorry`-free at this pin; the residual is
exactly the residue theorem itself, named as `R5` (= `ResidueTheorem X`).

## What is real-proof here

* `principalDivisorMap_degree_zero_of_R5` — given the named hypothesis
  `R5_principal_degree_zero_statement X`, the principal divisor of any
  non-zero meromorphic function has degree zero. (`fun hR5 f => hR5 f`.)
* `zeroCount_eq_poleCount_of_R5` — given `R5`, the zero count equals the
  pole count for any `f`. Chains through
  `tdfb_of_principalDegree_zero` (proven, in
  `Manifold/ZeroCountEqPoleCount.lean`).
* `meromorphicDegrees_eq_of_R5` — given `R5`, the multiplicity-weighted
  fibre-balance equality for any `f`. Chains through
  `meromorphicDegrees_eq_of_degree_zero` (proven, in
  `Manifold/MeromorphicDegreeFiberSum.lean`).
* `R5_iff_residueTheorem` — the per-`f` named statement `R5` and
  `ResidueTheorem X` are the same `Prop`. (Iff.rfl.)
* `R5_iff_zeroCount_eq_poleCount` — global Iff between `R5` and the
  per-`f` `zeroCount = poleCount` (chaining proven Iffs).

## Honest framing

* No `sorry`, no `axiom`, no signature change.
* This file does **not** discharge the residue theorem. It packages the
  named residual `R5` (= `ResidueTheorem X`) as the *single* hypothesis
  required to conclude any of the four equivalent statements above for
  a generic `f`. The unconditional discharge of `R5` itself awaits one
  of the two classical packages named in
  `Manifold/TopologicalDegree.lean` and `Manifold/ResidueTheorem.lean`'s
  "Owed" sections (branched-covering theory or `d log f` Stokes), both
  multi-thousand-LOC mathlib projects absent at the pin
  `8e3c989104daaa052921bf43de9eef0e1ac9fbf5`.

The point of this file is to make the *single* named residual auditable
in one place: a future agent who lands `R5` discharges every form of
the residue theorem in this repository at once via the lemmas below. -/

noncomputable section

open scoped Manifold Topology ContDiff BigOperators

namespace JacobianChallenge

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Per-`f` discharges modulo `R5` -/

/-- **Per-`f` discharge of the principal-divisor degree from `R5`.** Given
the named hypothesis `R5_principal_degree_zero_statement X` (the residue
theorem in summed-over-the-support form), every non-zero meromorphic
function on `X` has principal-divisor degree zero. -/
theorem principalDivisorMap_degree_zero_of_R5
    (hR5 : ResidueTheorem.R5_principal_degree_zero_statement X)
    (f : MeromorphicNonzero X) :
    (principalDivisorMap f).degree = 0 :=
  hR5 f

/-- **Per-`f` discharge of `zeroCount = poleCount` from `R5`.** Given the
named hypothesis `R5`, the multiplicity-weighted zero count equals the
multiplicity-weighted pole count for every non-zero meromorphic function
on `X`.

Proof: from `R5 f` we get `(principalDivisorMap f).degree = 0`; the
proven decomposition `signedMult_eq_zeroCount_sub_poleCount` then rewrites
the LHS as `zeroCount f - poleCount f`, and `sub_eq_zero` finishes. -/
theorem zeroCount_eq_poleCount_of_R5
    (hR5 : ResidueTheorem.R5_principal_degree_zero_statement X)
    (f : MeromorphicNonzero X) :
    ResidueViaTopologicalDegree.zeroCount f
      = ResidueViaTopologicalDegree.poleCount f :=
  ((ResidueViaTopologicalDegree.tdfb_of_principalDegree_zero
      (principalDivisorMap_degree_zero_of_R5 hR5 f)).zero_eq_pole)

/-- **Per-`f` discharge of the fibre-degree equality from `R5`.** Given
the named hypothesis `R5`, the multiplicity-weighted fibre-degree at `0`
equals the multiplicity-weighted fibre-degree at `∞`, for every non-zero
meromorphic function on `X`.

Proof: from `R5 f` we get `(principalDivisorMap f).degree = 0`; the
proven Iff `degree_eq_zero_iff_meromorphicDegrees_eq` (in
`Manifold/MeromorphicDegreeFiberSum.lean`) finishes via
`meromorphicDegrees_eq_of_degree_zero`. -/
theorem meromorphicDegrees_eq_of_R5
    (hR5 : ResidueTheorem.R5_principal_degree_zero_statement X)
    (f : MeromorphicNonzero X) :
    MeromorphicDegreeFiberSum.meromorphicDegreeAtZero f
      = MeromorphicDegreeFiberSum.meromorphicDegreeAtInfty f :=
  MeromorphicDegreeFiberSum.meromorphicDegrees_eq_of_degree_zero
    (principalDivisorMap_degree_zero_of_R5 hR5 f)

/-! ## Global equivalences -/

/-- **`R5` is the residue theorem, on the nose.** The named statement
`R5_principal_degree_zero_statement X` and `ResidueTheorem X` are
*the same* `Prop` definitionally — both unfold to
`∀ f, (principalDivisorMap f).degree = 0`. -/
lemma R5_iff_residueTheorem :
    ResidueTheorem.R5_principal_degree_zero_statement X
      ↔ JacobianChallenge.ResidueTheorem X :=
  Iff.rfl

/-- **Global equivalence: `R5` ↔ per-`f` `zeroCount = poleCount`.**

Chains the per-`f` decomposition `signedMult_eq_zeroCount_sub_poleCount`
(proven) through `R5_iff_residueTheorem` (proven, `Iff.rfl`) and the
existing global Iff `forall_tdfb_iff_residueTheorem` (proven) to give a
direct named bridge between the named residual `R5` and the per-`f`
integer-equality form `zeroCount f = poleCount f`. -/
lemma R5_iff_zeroCount_eq_poleCount :
    ResidueTheorem.R5_principal_degree_zero_statement X
      ↔ ∀ f : MeromorphicNonzero X,
          ResidueViaTopologicalDegree.zeroCount f
            = ResidueViaTopologicalDegree.poleCount f := by
  constructor
  · intro hR5 f
    exact zeroCount_eq_poleCount_of_R5 hR5 f
  · intro hZP f
    -- Reverse: from `zeroCount = poleCount` per `f`, build the bundle
    -- and feed it into the proven `forall_tdfb_iff_residueTheorem` Iff.
    have hbundle :
        ∀ f : MeromorphicNonzero X,
          ResidueViaTopologicalDegree.TopologicalDegreeFibreBalance_hypothesis f :=
      fun f => ⟨hZP f⟩
    -- The proven Iff converts `∀ f, bundle f` into `ResidueTheorem X`.
    exact ResidueViaTopologicalDegree.forall_tdfb_iff_residueTheorem.mp hbundle

/-- **Global equivalence: `R5` ↔ per-`f` fibre-degree equality.**

Chains `R5_iff_residueTheorem` (proven, `Iff.rfl`) with the existing
proven global Iff `forall_meromorphicDegrees_eq_iff_residueTheorem`. -/
lemma R5_iff_meromorphicDegrees_eq :
    ResidueTheorem.R5_principal_degree_zero_statement X
      ↔ ∀ f : MeromorphicNonzero X,
          MeromorphicDegreeFiberSum.meromorphicDegreeAtZero f
            = MeromorphicDegreeFiberSum.meromorphicDegreeAtInfty f :=
  MeromorphicDegreeFiberSum.forall_meromorphicDegrees_eq_iff_residueTheorem.symm

/-! ## Honest summary

The five named per-`f` and global statements

* `R5_principal_degree_zero_statement X` (= `ResidueTheorem X` definitionally)
* `(principalDivisorMap f).degree = 0` for every `f`
* `zeroCount f = poleCount f` for every `f`
* `meromorphicDegreeAtZero f = meromorphicDegreeAtInfty f` for every `f`
* `(∀ f, TopologicalDegreeFibreBalance_hypothesis f)`

are pairwise `Iff`-equivalent at this pin, and this file gives the
direct per-`f` discharges from a single named hypothesis (`R5`).

**No discharge of `R5` itself.** That awaits the branched-covering
package or the `d log f` Stokes package referenced in the "Owed" sections
of `Manifold/ResidueTheorem.lean` and `Manifold/TopologicalDegree.lean`.
-/

end JacobianChallenge

end
