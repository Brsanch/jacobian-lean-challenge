/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor
import JacobianChallenge.Divisor.PrincipalDivisor
import JacobianChallenge.Divisor.PrincipalDivisorRange
import JacobianChallenge.Manifold.ResidueViaTopologicalDegree

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Topological degree of a meromorphic function via its zero/pole fibres

This file is a *clean reformulation* of the same arithmetic content
that powers `ResidueViaTopologicalDegree.lean`, but phrased as two
**fibre-degree integers**

  `meromorphicDegreeAtZero  f := ∑_{x ∈ supp, ord_x f > 0}  ord_x f`
  `meromorphicDegreeAtInfty f := ∑_{x ∈ supp, ord_x f > 0} (-ord_x f)
                                  taken over the pole fibre`

— mirroring, on the integer side, the topological degree of the
pole-extension `f̃ : X → S² = OnePoint ℂ` over the two regular values
`0 ∈ S²` and `∞ ∈ S²`.

By `principalDivisorMap_apply`, the pointwise integer
`(principalDivisorMap f : X → ℤ) x` is exactly
`(mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x).untop₀`, so the sums below
are also the multiplicity-weighted fibre cardinalities phrased
through `mmeromorphicOrderAt`.

The point of this file: expose the residue theorem
`(principalDivisorMap f).degree = 0` as the statement
`meromorphicDegreeAtZero f = meromorphicDegreeAtInfty f`,
i.e. as an equality between two fibre integers (rather than as a
single integer being zero). Both phrasings are equivalent by
`sub_eq_zero`, but downstream consumers — in particular any future
proper-holomorphic-map topological-degree API — typically produce the
*equality* phrasing directly, since it is the conclusion of "the two
generic fibres of a proper holomorphic map between compact Riemann
surfaces have the same multiplicity-weighted cardinality".

## What is real-proof here

* `meromorphicDegreeAtZero`, `meromorphicDegreeAtInfty` — genuine
  `noncomputable def`s, sums over the principal divisor's support.
* `meromorphicDegreeAtZero_eq_zeroCount`,
  `meromorphicDegreeAtInfty_eq_poleCount` — **definitional `rfl`**
  identifications with the `ResidueViaTopologicalDegree` counts.
* `degree_eq_zero_iff_meromorphicDegrees_eq` — the headline
  reformulation: the residue-theorem conclusion
  `(principalDivisorMap f).degree = 0` is **iff**
  `meromorphicDegreeAtZero f = meromorphicDegreeAtInfty f`.
* `global_sum_zero_of_meromorphicDegrees_eq` — the easy direction,
  feeding straight into `ResidueTheorem`.

## Honest framing

* No `axiom`, no `sorry`.
* No existing definition signature is changed; nothing in
  `Basic.lean` is touched.
* This file *cannot* discharge the residue theorem on its own —
  `meromorphicDegreeAtZero f = meromorphicDegreeAtInfty f` is the
  same `Prop` as `zeroCount f = poleCount f`, which is the named
  gap of `TopologicalDegreeFibreBalance_hypothesis`. What this file
  *does* is rename that gap into the shape produced by the
  topological-degree theorem for proper holomorphic maps. -/

noncomputable section

open scoped Manifold Topology ContDiff BigOperators

namespace JacobianChallenge

namespace MeromorphicDegreeFiberSum

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## The two fibre-degree integers (real defs) -/

/-- **Multiplicity-weighted fibre count over `0 ∈ S²`.**

The integer `meromorphicDegreeAtZero f` is the sum of orders of `f`
over the support points of strictly positive order — i.e. the zeros
of `f`, each counted with multiplicity. On the topological-degree
side this is the cardinality (with multiplicity) of the fibre
`f̃⁻¹{0}` of the pole-extension `f̃ : X → S²`.

By `principalDivisorMap_apply`, the integer
`(principalDivisorMap f : X → ℤ) x` is `(mmeromorphicOrderAt
𝓘(ℂ,ℂ) f.toFun x).untop₀`, so this sum equals the more usually
written form
`∑_{x : ord_x f > 0}  ord_x f`. -/
noncomputable def meromorphicDegreeAtZero (f : MeromorphicNonzero X) : ℤ :=
  ∑ x ∈ ((principalDivisorMap f).supportFinset).filter
            (fun x => 0 < (principalDivisorMap f : X → ℤ) x),
      (principalDivisorMap f : X → ℤ) x

/-- **Multiplicity-weighted fibre count over `∞ ∈ S²`.**

The integer `meromorphicDegreeAtInfty f` is the sum of `-ord_x f`
over the support points of non-positive order — i.e. the poles of
`f`, each counted with absolute multiplicity. On the topological-
degree side this is the cardinality (with multiplicity) of the fibre
`f̃⁻¹{∞}` of the pole-extension `f̃ : X → S²`.

(Support points with order `0` are excluded from `supportFinset` by
construction, so the filter `¬ 0 < ord` reduces in practice to
strict negativity on the support; we phrase the predicate as
`¬ 0 < ord` so that the partition `{0 < ord} ⊔ {¬ 0 < ord}` is
exhaustive on the nose.) -/
noncomputable def meromorphicDegreeAtInfty (f : MeromorphicNonzero X) : ℤ :=
  ∑ x ∈ ((principalDivisorMap f).supportFinset).filter
            (fun x => ¬ 0 < (principalDivisorMap f : X → ℤ) x),
      - (principalDivisorMap f : X → ℤ) x

/-! ## Identification with the `ResidueViaTopologicalDegree` counts -/

/-- **`meromorphicDegreeAtZero` is exactly `zeroCount`.**

The two are equal by definition (same Finset, same summand). This
lemma exposes the bridge as a named API entry point. -/
@[simp] lemma meromorphicDegreeAtZero_eq_zeroCount
    (f : MeromorphicNonzero X) :
    meromorphicDegreeAtZero f
      = JacobianChallenge.ResidueViaTopologicalDegree.zeroCount f := rfl

/-- **`meromorphicDegreeAtInfty` is exactly `poleCount`.**

The two are equal by definition (same Finset, same summand). This
lemma exposes the bridge as a named API entry point. -/
@[simp] lemma meromorphicDegreeAtInfty_eq_poleCount
    (f : MeromorphicNonzero X) :
    meromorphicDegreeAtInfty f
      = JacobianChallenge.ResidueViaTopologicalDegree.poleCount f := rfl

/-! ## Headline reformulation -/

/-- **Signed-multiplicity decomposition through the fibre integers.**

`(principalDivisorMap f).degree
  = meromorphicDegreeAtZero f - meromorphicDegreeAtInfty f`.

This is a direct repackaging of
`ResidueViaTopologicalDegree.signedMult_eq_zeroCount_sub_poleCount`
through the definitional identifications above. -/
lemma degree_eq_meromorphicDegreeAtZero_sub_meromorphicDegreeAtInfty
    (f : MeromorphicNonzero X) :
    (principalDivisorMap f).degree
      = meromorphicDegreeAtZero f - meromorphicDegreeAtInfty f := by
  simpa [meromorphicDegreeAtZero_eq_zeroCount,
         meromorphicDegreeAtInfty_eq_poleCount] using
    JacobianChallenge.ResidueViaTopologicalDegree
      .signedMult_eq_zeroCount_sub_poleCount (f := f)

/-- **Headline reformulation of the residue theorem.**

The residue-theorem conclusion `(principalDivisorMap f).degree = 0`
is equivalent to the equality of the two multiplicity-weighted
fibre integers. This is `sub_eq_zero` applied to the decomposition
above. -/
theorem degree_eq_zero_iff_meromorphicDegrees_eq
    (f : MeromorphicNonzero X) :
    (principalDivisorMap f).degree = 0
      ↔ meromorphicDegreeAtZero f = meromorphicDegreeAtInfty f := by
  rw [degree_eq_meromorphicDegreeAtZero_sub_meromorphicDegreeAtInfty,
      sub_eq_zero]

/-- **From the fibre-equality to `degree = 0`.** Easy direction. -/
lemma global_sum_zero_of_meromorphicDegrees_eq
    {f : MeromorphicNonzero X}
    (h : meromorphicDegreeAtZero f = meromorphicDegreeAtInfty f) :
    (principalDivisorMap f).degree = 0 :=
  (degree_eq_zero_iff_meromorphicDegrees_eq f).2 h

/-- **From `degree = 0` to the fibre-equality.** Reverse direction. -/
lemma meromorphicDegrees_eq_of_degree_zero
    {f : MeromorphicNonzero X}
    (h : (principalDivisorMap f).degree = 0) :
    meromorphicDegreeAtZero f = meromorphicDegreeAtInfty f :=
  (degree_eq_zero_iff_meromorphicDegrees_eq f).1 h

/-! ## Bridging the `ResidueViaTopologicalDegree` bundle -/

/-- **Bundle-shaped reformulation.**

If for every `f` the two fibre integers agree, then the residue
theorem holds on `X`. This is the same statement as
`ResidueTheorem_holds_of_topologicalDegreeFibreBalance`, but the
hypothesis is phrased as a fibre equality rather than a `zeroCount =
poleCount` equality (the two are definitionally the same Prop, but
the fibre-equality form is the conclusion that a topological-degree
API for proper holomorphic maps to `S²` would deliver). -/
theorem ResidueTheorem_holds_of_meromorphicDegrees_eq
    (H : ∀ f : MeromorphicNonzero X,
            meromorphicDegreeAtZero f = meromorphicDegreeAtInfty f) :
    JacobianChallenge.ResidueTheorem X :=
  fun f => global_sum_zero_of_meromorphicDegrees_eq (H f)

end MeromorphicDegreeFiberSum

end JacobianChallenge

end
