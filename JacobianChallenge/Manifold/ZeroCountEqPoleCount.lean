/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ResidueViaTopologicalDegree
import JacobianChallenge.Manifold.FibreBalance
import JacobianChallenge.Manifold.TopologicalDegree

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # The Route-B integer gap is equivalent to the residue theorem

This file analyses the single named gap of
`Manifold/ResidueViaTopologicalDegree.lean`:

  `zero_eq_pole : zeroCount f = poleCount f`.

Concretely, we ask: is the integer hypothesis
`zero_eq_pole` *strictly smaller* than the residue theorem (R5,
`(principalDivisorMap f).degree = 0`), or is it the same statement
in disguise?

## Result (proven, no `sorry`, no `axiom`)

Per `f`:

  `TopologicalDegreeFibreBalance_hypothesis f
     ↔ (principalDivisorMap f).degree = 0`.

Globally:

  `(∀ f, TopologicalDegreeFibreBalance_hypothesis f)
     ↔ JacobianChallenge.ResidueTheorem X
     ↔ JacobianChallenge.TopologicalDegreeBalance X
     ↔ ∀ f, JacobianChallenge.signedMult f = 0`.

The forward implications are already in
`Manifold/ResidueViaTopologicalDegree.lean`
(`global_sum_zero_via_topological_degree`,
`ResidueTheorem_holds_of_topologicalDegreeFibreBalance`,
`topologicalDegreeBalance_of_fibreBalance`,
`signedMult_zero_of_fibreBalance`). This file supplies the *reverse*
implications via the proven decomposition lemma
`signedMult_eq_zeroCount_sub_poleCount`, closing the per-`f` `Iff`.

## Honest framing — the named gap is not strictly smaller than R5

The classical route to `zeroCount f = poleCount f` *would* go through
the topological-degree theorem for the proper holomorphic map
`f̃ : X → S² = OnePoint ℂ` (M3-shipped as
`MeromorphicNonzero.toRiemannSphere_contMDiff`): both fibres
`f̃⁻¹{0}` (zeros) and `f̃⁻¹{∞}` (poles), counted with local
multiplicity, equal the topological degree of `f̃`, which is constant
on regular values.

Three mathlib pieces are owed at the pin
`8e3c989104daaa052921bf43de9eef0e1ac9fbf5` to formalise this route:

* `Mathlib.Topology.Covering` only handles unbranched coverings; the
  branched-covering API (excision around the finite critical-value
  set) is owed.
* The "fibre-cardinality counted with multiplicity equals the
  topological degree" lemma for proper maps between compact oriented
  2-manifolds is owed (the cardinality form is in
  `Manifold/Degree.lean` as `degreeFiber`; the multiplicity-weighted
  form is owed).
* The R3 equality refinement (local multiplicity = `|ord_x f|`) is
  partial at this pin: the `≥ 1` form is in
  `Manifold/LocalMultiplicity.lean`, the equality form is the
  J3+L2 follow-up.

None of these three is strictly smaller than the original residue
theorem under the existing manifold-side API: each one *is* a
classical theorem of comparable depth, and at the mathlib pin none
is yet packaged.

Therefore the Route-B bundle of
`Manifold/ResidueViaTopologicalDegree.lean` is **definitionally the
same `Prop`** as `R4_signedMult_zero_statement` and
`TopologicalDegreeBalance` and `ResidueTheorem`. It is *not* a
reduction to a strictly smaller mathlib-shaped gap; it is a
**renaming** of the residue theorem in a form whose discharge would
naturally come from a future topological-degree API rather than a
future Stokes / `d log f` API. (See the corresponding "Owed" sections
in `Manifold/TopologicalDegree.lean` and
`Manifold/DegreeConstancy.lean`.)

This file pins that fact: the per-`f` integer `zero_eq_pole` is
`Iff`-equivalent (via the proven decomposition lemma) to
`(principalDivisorMap f).degree = 0`. The four global named statements
all coincide. Discharging any one closes all four.

## What is *strictly* delivered here

* `tdfb_iff_principalDegree_zero` — per-`f` `Iff` between the bundle
  field and `(principalDivisorMap f).degree = 0`.
* `forall_tdfb_iff_residueTheorem` — global `Iff` between the
  `∀ f`-bundle and `ResidueTheorem X`.
* `forall_tdfb_iff_topologicalDegreeBalance` — global `Iff` against
  `TopologicalDegreeBalance X`.
* `forall_tdfb_iff_R4` — global `Iff` against
  `R4_signedMult_zero_statement X`.

No `sorry`. No `axiom`. No new hypothesis. No signature change.
Strictly: the equivalence between the named gap and the residue
theorem itself, made precise. -/

noncomputable section

open scoped Manifold Topology ContDiff BigOperators

namespace JacobianChallenge

namespace ResidueViaTopologicalDegree

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Per-`f` equivalence: the bundle is exactly per-`f` R5 -/

/-- **Reverse direction (proven).** From `(principalDivisorMap f).degree = 0`
to the bundle.

Combined with the forward direction
`global_sum_zero_via_topological_degree`, this shows the bundle is
*definitionally the same* `Prop` (per `f`) as
`(principalDivisorMap f).degree = 0`, modulo the proven decomposition
`signedMult_eq_zeroCount_sub_poleCount`.

Proof: from `signedMult_eq_zeroCount_sub_poleCount`, we have
`(principalDivisorMap f).degree = zeroCount f - poleCount f`. The
hypothesis `(principalDivisorMap f).degree = 0` then gives
`zeroCount f - poleCount f = 0`, which by `sub_eq_zero` rearranges to
`zeroCount f = poleCount f`. -/
lemma tdfb_of_principalDegree_zero
    {f : MeromorphicNonzero X}
    (h : (principalDivisorMap f).degree = 0) :
    TopologicalDegreeFibreBalance_hypothesis f := by
  refine ⟨?_⟩
  have hdec := signedMult_eq_zeroCount_sub_poleCount f
  -- `hdec : (principalDivisorMap f).degree = zeroCount f - poleCount f`.
  rw [h] at hdec
  -- `hdec : 0 = zeroCount f - poleCount f`.
  exact (sub_eq_zero.mp hdec.symm)

/-- **Per-`f` equivalence (proven).**

The Route-B bundle field for an individual `f` is `Iff`-equivalent to
the per-`f` residue-theorem statement
`(principalDivisorMap f).degree = 0`.

This pins the *honest framing* of `Manifold/ResidueViaTopologicalDegree.lean`:
the bundle is a *renaming* of per-`f` R5, not a reduction to a strictly
smaller gap. -/
lemma tdfb_iff_principalDegree_zero (f : MeromorphicNonzero X) :
    TopologicalDegreeFibreBalance_hypothesis f
      ↔ (principalDivisorMap f).degree = 0 :=
  ⟨global_sum_zero_via_topological_degree, tdfb_of_principalDegree_zero⟩

/-! ## Global equivalences -/

/-- **Global equivalence with `ResidueTheorem X` (proven).**

`(∀ f, TopologicalDegreeFibreBalance_hypothesis f)` and
`JacobianChallenge.ResidueTheorem X` are the same `Prop`. -/
lemma forall_tdfb_iff_residueTheorem :
    (∀ f : MeromorphicNonzero X,
        TopologicalDegreeFibreBalance_hypothesis f)
      ↔ JacobianChallenge.ResidueTheorem X :=
  ⟨ResidueTheorem_holds_of_topologicalDegreeFibreBalance,
    fun hRT f => tdfb_of_principalDegree_zero (hRT f)⟩

/-- **Global equivalence with `TopologicalDegreeBalance X` (proven).**

By `topologicalDegreeBalance_iff_residueTheorem` (`Iff.rfl` in
`Manifold/TopologicalDegree.lean`), this is `Iff`-equivalent to
`forall_tdfb_iff_residueTheorem`. -/
lemma forall_tdfb_iff_topologicalDegreeBalance :
    (∀ f : MeromorphicNonzero X,
        TopologicalDegreeFibreBalance_hypothesis f)
      ↔ JacobianChallenge.TopologicalDegreeBalance X :=
  forall_tdfb_iff_residueTheorem.trans
    JacobianChallenge.topologicalDegreeBalance_iff_residueTheorem.symm

/-- **Global equivalence with `R4_signedMult_zero_statement X` (proven).**

By `R4_signedMult_zero_iff_residueTheorem` (`Iff.rfl` in
`Manifold/FibreBalance.lean`), this is `Iff`-equivalent to
`forall_tdfb_iff_residueTheorem`. -/
lemma forall_tdfb_iff_R4 :
    (∀ f : MeromorphicNonzero X,
        TopologicalDegreeFibreBalance_hypothesis f)
      ↔ JacobianChallenge.R4_signedMult_zero_statement X :=
  forall_tdfb_iff_residueTheorem.trans
    JacobianChallenge.R4_signedMult_zero_iff_residueTheorem.symm

/-! ## Honest summary

The four named statements

* `∀ f, TopologicalDegreeFibreBalance_hypothesis f` (this Route-B bundle)
* `JacobianChallenge.ResidueTheorem X`
* `JacobianChallenge.TopologicalDegreeBalance X`
* `JacobianChallenge.R4_signedMult_zero_statement X`

are pairwise `Iff`-equivalent. Three of those equivalences are
`Iff.rfl`; the fourth (involving the bundle) goes through the proven
decomposition `signedMult_eq_zeroCount_sub_poleCount`.

**No discharge.** The bundle's `zero_eq_pole` field is the residue
theorem in disguise, not a strictly smaller mathlib-shaped gap. A real
proof requires either branched-covering theory (Route A) or
`d log f` Stokes (Route B), both of which are mathlib-multi-thousand-LOC
projects absent at pin `8e3c989104daaa052921bf43de9eef0e1ac9fbf5`.

**This file's purpose** is to make that fact *auditable*:
`tdfb_iff_principalDegree_zero` is a one-line lemma that locks the
bundle to the residue-theorem `Prop`. Future agents looking for
"smaller gaps" know, by direct inspection of this lemma's `Iff`, that
the Route-B integer formulation has not bought any reduction over the
divisor-degree formulation.

The closure of `ResidueTheorem` therefore awaits one of the two
classical packages named in `Manifold/TopologicalDegree.lean`'s "Owed
mathlib infrastructure" section, not a further reformulation. -/

end ResidueViaTopologicalDegree

end JacobianChallenge

end
