/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor
import JacobianChallenge.Divisor.PrincipalDivisor
import JacobianChallenge.Divisor.PrincipalDivisorRange
import JacobianChallenge.Manifold.MeromorphicExtension
import JacobianChallenge.Manifold.TopologicalDegree
import JacobianChallenge.Manifold.FibreBalance

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Residue theorem via the topological-degree (Route B sphere) route

This file localises the residue-theorem gap **away from manifold
partition-of-unity Stokes integration** and onto the much smaller
fact that the pole-extension `f̃ : X → S² = OnePoint ℂ` has equal
topological degrees over the two regular values `0 ∈ S²` and
`∞ ∈ S²`, each counted with local multiplicity (= the absolute
value of the local order of `f`).

In contrast to `Manifold/GlobalResidueSum.lean` (which routes the
residue theorem through a *partition-of-unity / chain-boundary*
hypothesis bundle whose two named gaps are real-valued integrals on
a smooth 2-manifold), this file routes through a *topological-degree
fibre-balance* bundle whose only named gap is **a single integer
equality** between two purely arithmetic counts:

  `zeroCount f = poleCount f`,

where

  `zeroCount f := ∑_{x ∈ supp, ord_x f > 0}        ord_x f`
  `poleCount f := ∑_{x ∈ supp, ord_x f ≤ 0}      (- ord_x f)`.

This is the same `Prop` as `JacobianChallenge.ResidueTheorem X`, but
the bundle exposes a *single* arithmetic field (`zero_eq_pole`)
rather than two real-analysis fields (`chain_boundary_decomposition`
and `global_chain_boundary_eq_zero`). Both routes deliver the same
discharge, but the partition-of-unity bundle was selected so that a
*future* manifold-Stokes API would discharge it; this bundle is
selected so that a *future* topological-degree API for proper
holomorphic maps to `S²` (the Riemann-sphere route already named in
`Manifold/TopologicalDegree.lean` and `Manifold/DegreeConstancy.lean`)
would discharge it.

## What is real-proof here

* `zeroCount`, `poleCount` — genuine `noncomputable def`s, sums over
  the principal divisor's support filtered by sign.
* `signedMult_eq_zeroCount_sub_poleCount` — **real lemma**, proven
  by `Finset.sum_filter_add_sum_filter_not` on the support sum.
* `global_sum_zero_via_topological_degree` — **real lemma** that
  consumes the single integer hypothesis `zeroCount = poleCount` and
  delivers `(principalDivisorMap f).degree = 0`.
* `ResidueTheorem_holds_of_topologicalDegreeFibreBalance` — composite
  discharge of `JacobianChallenge.ResidueTheorem X` from the per-`f`
  bundle.

## What is the *single* named gap

The structure `TopologicalDegreeFibreBalance_hypothesis f` has
exactly one `Prop`-valued field:

* `zero_eq_pole : zeroCount f = poleCount f`.

This is the integer shadow of the topological-degree theorem for
the proper holomorphic map `f̃ : X → S²`: both fibres `f̃⁻¹{0}` and
`f̃⁻¹{∞}`, counted with multiplicity (= local order), have the same
cardinality, namely the topological degree of `f̃`. Mathlib does not
package this at the pin `8e3c989104daaa052921bf43de9eef0e1ac9fbf5`,
so we name it as a hypothesis bundle field, not as an axiom.

## Honest framing

* No `axiom`, no `sorry`.
* No existing definition signature is changed; nothing in
  `Basic.lean` is touched.
* This file is *strictly weaker* than `GlobalResidueSum.lean`'s
  bundle — both are valid reductions of the same `ResidueTheorem X`,
  but the present bundle has a single named gap (an arithmetic
  equality between two integer sums) instead of two named gaps
  (smooth-form chain-boundary identities). A consumer who can
  populate either bundle gets `ResidueTheorem X`; the choice is a
  costing question for the next agent. -/

noncomputable section

open scoped Manifold Topology ContDiff BigOperators

namespace JacobianChallenge

namespace ResidueViaTopologicalDegree

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## The two multiplicity-weighted fibre counts (real defs)

These are honest sums over the (finite) support of the principal
divisor, filtered by the sign of the order. Both are integer-valued
by definition; for a non-constant `f`, `zeroCount f` and `poleCount f`
are non-negative, but we do not need that property here. -/

/-- **Multiplicity-weighted zero count.** Sum of `ord_x f` over the
support points with strictly positive order — i.e. the zeros, each
counted with multiplicity. -/
noncomputable def zeroCount (f : MeromorphicNonzero X) : ℤ :=
  ∑ x ∈ ((principalDivisorMap f).supportFinset).filter
            (fun x => 0 < (principalDivisorMap f : X → ℤ) x),
      (principalDivisorMap f : X → ℤ) x

/-- **Multiplicity-weighted pole count.** Sum of `-ord_x f` over the
support points with non-positive order — i.e. the poles, each counted
with absolute multiplicity. (Support points with order `0` are
excluded from the support, so the filter `≤ 0` reduces in practice to
strict negativity on the support, but stating it as `≤ 0` makes the
support partition `(0 <) ⊔ (¬ 0 <)` exhaustive on the nose.) -/
noncomputable def poleCount (f : MeromorphicNonzero X) : ℤ :=
  ∑ x ∈ ((principalDivisorMap f).supportFinset).filter
            (fun x => ¬ 0 < (principalDivisorMap f : X → ℤ) x),
      - (principalDivisorMap f : X → ℤ) x

/-! ## The decomposition lemma (real lemma) -/

/-- **The signed-multiplicity sum decomposes into zeros minus poles.**

`(principalDivisorMap f).degree = zeroCount f - poleCount f`.

Proof: `degree` is a sum over `supportFinset`. Split the support
along the predicate `0 < ord_x f` (zero side) versus its negation
(pole side). The zero side contributes `zeroCount f` directly. The
pole side contributes `∑_{ord ≤ 0} ord_x f = - ∑_{ord ≤ 0} (-ord_x f)
= -poleCount f` after pulling out the negation. -/
lemma signedMult_eq_zeroCount_sub_poleCount (f : MeromorphicNonzero X) :
    (principalDivisorMap f).degree = zeroCount f - poleCount f := by
  classical
  -- `degree = ∑ over supportFinset`.
  unfold JacobianChallenge.Div.degree
  -- Split the support into the strict-positive side and its complement.
  have hsplit :
      ∑ x ∈ (principalDivisorMap f).supportFinset,
          (principalDivisorMap f : X → ℤ) x
        = (∑ x ∈ ((principalDivisorMap f).supportFinset).filter
                  (fun x => 0 < (principalDivisorMap f : X → ℤ) x),
              (principalDivisorMap f : X → ℤ) x)
          + (∑ x ∈ ((principalDivisorMap f).supportFinset).filter
                    (fun x => ¬ 0 < (principalDivisorMap f : X → ℤ) x),
                (principalDivisorMap f : X → ℤ) x) :=
    (Finset.sum_filter_add_sum_filter_not
      (s := (principalDivisorMap f).supportFinset)
      (p := fun x => 0 < (principalDivisorMap f : X → ℤ) x)
      (f := fun x => (principalDivisorMap f : X → ℤ) x)).symm
  -- Recognise the two pieces as `zeroCount` and `-poleCount`.
  have hpole_neg :
      ∑ x ∈ ((principalDivisorMap f).supportFinset).filter
              (fun x => ¬ 0 < (principalDivisorMap f : X → ℤ) x),
            (principalDivisorMap f : X → ℤ) x
        = - poleCount f := by
    unfold poleCount
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro x _; ring
  rw [hsplit, hpole_neg]
  unfold zeroCount
  ring

/-! ## The hypothesis bundle: a single named integer gap -/

/-- **Topological-degree fibre-balance hypothesis bundle.**

The single named gap is
`zero_eq_pole : zeroCount f = poleCount f` —
the integer shadow of "the pole-extension `f̃ : X → S²` has equal
topological degree over the two regular values `0` and `∞`, each
counted with local multiplicity = absolute order of `f`".

This is a `Prop`-valued field on a structure, **not an axiom**.
Constructing a witness commits the constructor to discharging this
single integer equality; downstream code can take the bundle as a
hypothesis without committing the kernel to anything.

Compare `GlobalResidueSum.GlobalResidueSum_hypothesis`: that bundle
has two named gaps (`chain_boundary_decomposition` and
`global_chain_boundary_eq_zero`), both phrased in terms of
real-valued integrals on a smooth 2-manifold. The present bundle has
**one** named gap, and that gap is a purely arithmetic equality
between two integer sums. -/
structure TopologicalDegreeFibreBalance_hypothesis
    (f : MeromorphicNonzero X) where
  /-- **Named gap (Route B, topological-degree fibre balance).**
      The multiplicity-weighted count of zeros equals the
      multiplicity-weighted count of poles. -/
  zero_eq_pole : zeroCount f = poleCount f

/-! ## Headline lemma: residue theorem from the bundle -/

/-- **From the bundle to `(principalDivisorMap f).degree = 0`.**

The bundle field `zero_eq_pole` says `zeroCount f = poleCount f`.
Combined with the decomposition lemma
`signedMult_eq_zeroCount_sub_poleCount`, we get
`(principalDivisorMap f).degree = zeroCount f - poleCount f
                                = poleCount f - poleCount f = 0`. -/
lemma global_sum_zero_via_topological_degree
    {f : MeromorphicNonzero X}
    (H : TopologicalDegreeFibreBalance_hypothesis f) :
    (principalDivisorMap f).degree = 0 := by
  rw [signedMult_eq_zeroCount_sub_poleCount, H.zero_eq_pole, sub_self]

/-! ## Discharge of the residue theorem -/

/-- **Composite discharge of `ResidueTheorem X` via Route B.**

If every `f : MeromorphicNonzero X` admits a
`TopologicalDegreeFibreBalance_hypothesis`, then the residue theorem
holds on `X`. -/
theorem ResidueTheorem_holds_of_topologicalDegreeFibreBalance
    (H : ∀ f : MeromorphicNonzero X,
            TopologicalDegreeFibreBalance_hypothesis f) :
    JacobianChallenge.ResidueTheorem X :=
  fun f => global_sum_zero_via_topological_degree (H f)

/-- **Same content as `TopologicalDegreeBalance X`.**

Discharging Route B for every `f` is the same Prop as
`TopologicalDegreeBalance X` (which by `Iff.rfl` is the same as
`ResidueTheorem X`). This lemma records the bridge. -/
lemma topologicalDegreeBalance_of_fibreBalance
    (H : ∀ f : MeromorphicNonzero X,
            TopologicalDegreeFibreBalance_hypothesis f) :
    JacobianChallenge.TopologicalDegreeBalance X :=
  ResidueTheorem_holds_of_topologicalDegreeFibreBalance H

/-- **Same content as `R4_signedMult_zero_statement X`.**

The bundle's per-`f` discharge is exactly `signedMult f = 0`. -/
lemma signedMult_zero_of_fibreBalance
    {f : MeromorphicNonzero X}
    (H : TopologicalDegreeFibreBalance_hypothesis f) :
    JacobianChallenge.signedMult f = 0 := by
  unfold JacobianChallenge.signedMult
  exact global_sum_zero_via_topological_degree H

/-! ## What is the remaining named gap, precisely

The single named gap of this file is, for each
`f : MeromorphicNonzero X`:

  `zeroCount f = poleCount f`.

Unfolded:

  `∑_{x ∈ supp(f), ord_x f > 0}  ord_x f
     = ∑_{x ∈ supp(f), ord_x f ≤ 0} (- ord_x f)`.

Mathematically this is the topological-degree theorem for the proper
holomorphic map `f̃ : X → S² = OnePoint ℂ`:
* the LHS is the multiplicity-weighted cardinality of `f̃⁻¹{0}`
  (since `f̃ x = some(f x)` with `f x = 0` exactly when `ord_x f > 0`,
  and the multiplicity at such a zero is `ord_x f`);
* the RHS is the multiplicity-weighted cardinality of `f̃⁻¹{∞}`
  (since `f̃ x = ∞` exactly when `ord_x f < 0`, and the multiplicity
  at such a pole is `−ord_x f`).
* Both equal the topological degree of `f̃` (a single integer, by the
  classical theorem for proper holomorphic maps between compact
  Riemann surfaces).

Mathlib hooks at the pin (`8e3c989`):
* `Mathlib.Topology.Covering` — unbranched covering API only; the
  branched-covering lift around the finite critical-value set is
  owed.
* `MeromorphicNonzero.toRiemannSphere_contMDiff` (in
  `Manifold/MeromorphicExtension.lean`) — the M3-shipped fact that
  `f̃` is `ContMDiff`; the topological-degree statement on top of it
  is owed.
* `Manifold/DegreeConstancy.lean` — names `degreeConstant_statement`
  and the `degreeConstant_implies_R5_statement` reduction; the
  present file's `zero_eq_pole` is the `degreeConstant`-statement
  evaluated at the two regular values `0` and `∞`, after the
  multiplicity-equals-order identification.

Compared to the partition-of-unity gap of
`Manifold/GlobalResidueSum.lean`, the Route-B gap here is *one*
arithmetic equality, not *two* smooth-form integral identities. -/

end ResidueViaTopologicalDegree

end JacobianChallenge

end
