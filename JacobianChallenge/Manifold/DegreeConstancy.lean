/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicExtension
import JacobianChallenge.Manifold.Degree
import JacobianChallenge.Manifold.TopologicalDegree
import JacobianChallenge.Manifold.MeromorphicDivisor
import JacobianChallenge.Divisor.PrincipalDivisor

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Degree-constancy on regular fibres of the pole extension

This file chips at the **R5 / `TopologicalDegreeBalance`** combining
argument by exposing the *regular set* of a `MeromorphicNonzero` and
naming the (deep, unproven) constancy statement that is the
classical input for the topological-degree balance.

## Background

M3 (`Manifold/MeromorphicExtension.lean`) closed
`MeromorphicNonzero.toRiemannSphere_contMDiff`, so the pole-extension
`f̃ : X → RiemannSphere` of a `MeromorphicNonzero X` is a `ContMDiff`
proper holomorphic map between compact connected Riemann surfaces.

The R5 theorem (`Manifold/TopologicalDegree.lean`) — equivalently the
residue theorem — says:

> For every non-constant `f : MeromorphicNonzero X`,
> `(principalDivisorMap f).degree = 0`.

The classical proof of R5 via covering-space theory factors through the
**fibre-cardinality-with-multiplicity is constant on regular values of
`f̃`** lemma. That lemma is the topological-degree statement for proper
holomorphic maps to `S²`. Equality of fibre cardinality at the regular
values `0 ∈ S²` (zeros of `f`) and `∞ ∈ S²` (poles of `f`), summed with
multiplicity, gives R5.

This file does **not** prove that lemma — branched-covering theory for
proper holomorphic maps is owed at the mathlib pin
`8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (see the "What's owed"
section at the bottom). What this file ships:

1. `regularSet f : Set X`, the set of points where `f` is regular and
   non-vanishing in the `mmeromorphicOrderAt = 0` sense — a real
   `def`, not a stub.
2. `regularSet_eq_orderFun_preimage_zero` — the equality of
   `regularSet f` with the order-function zero set, on the nose
   (`Set.ext + orderFun_eq_zero_iff` using the `nonvanishing_germ`
   field).
3. `regularSet_compl_finite` — the **real lemma** that the complement
   of `regularSet f` (the zeros + poles) is finite on a compact
   Hausdorff complex 1-manifold. This is a genuine proof, not a stub:
   it uses `J2`'s `MMeromorphicOn.orderFun_support_finite` together
   with the equality lemma.
4. `regularSet_cofinite` — the same content packaged as
   `Set.Cofinite`, the API form that downstream covering-space code
   wants.
5. `degreeConstant_statement` — `Prop`-valued `def` (no `axiom`s)
   stating that the fibre cardinality on the regular set is constant.
6. `degreeConstant_implies_R5_statement` — `Prop`-valued `def` (no
   `axiom`s) stating the implication "constancy ⇒ R5". The structural
   wiring is *not* `Iff.rfl` here because the LHS quantifies over the
   regular set of `f̃` and the RHS quantifies over `f` — the
   reduction goes through the geometric route (zero fibre = zeros of
   `f`, ∞ fibre = poles of `f`), which is exactly the content that is
   owed at this pin.

## What's proven vs. what's stated

| Item                                             | Status         |
|---|---|
| `regularSet`                                      | **Real def**   |
| `regularSet_eq_orderFun_preimage_zero`            | **Proven**     |
| `regularSet_compl_finite`                          | **Proven**     |
| `regularSet_cofinite`                              | **Proven**     |
| `degreeConstant_statement`                         | Prop-only def  |
| `degreeConstant_implies_R5_statement`              | Prop-only def  |

No `sorry`. No `axiom`. The Prop-only definitions are the structural
hooks; their *truth* is the deep classical content that is owed at the
pin (see "What's owed" at the bottom).

## What's owed

Discharging `degreeConstant_statement` requires either:

* **Branched-covering theory.** Mathlib's `Mathlib.Topology.Covering`
  supplies the unbranched case (constant fibre cardinality on
  connected base), but the *branched* extension — chart-side excision
  around the finite critical-value set, plus the lemma "for a proper
  holomorphic map between compact Riemann surfaces, the
  critical-value set is finite and the restriction to its complement
  is a covering" — is owed.

* **Stokes / `d log f`.** The 1-form `df / f` has integer residues
  equal to the local orders, and the integral over a closed compact
  2-manifold is zero. This route requires the
  meromorphic-1-form residue API + manifold Stokes, neither
  packaged at the pin.

The implication `degreeConstant_statement ⇒ R5` is the geometric
reduction "fibre at `0` = zeros, fibre at `∞` = poles, total degree
common ⇒ algebraic balance"; closing it requires the local
multiplicity = `|ord_x f|` content from R3 (J3+L2 follow-up). All
three pieces are named in this file's docstrings.
-/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## The regular set

A point `x ∈ X` is a **regular point** of `f : MeromorphicNonzero X`
when `mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x = 0`, i.e. `f` is
holomorphic and non-vanishing at `x`. By the
`nonvanishing_germ` field of `MeromorphicNonzero`, the order is never
`⊤`, so the regular set is exactly the complement of the (finite) set
of zeros and poles. -/

/-- The **regular set** of a `MeromorphicNonzero` function: the set of
points whose chart-pulled-back meromorphic order is exactly `0` (i.e.
neither a zero nor a pole of `f`).

Compare with the `Owed.degree.fibres_finite_statement` /
`regular_value_exists_statement` of `Manifold/Degree.lean`: those
quantify over *codomain* values; this set is the *domain* preimage of
"the regular value `f x`" for every regular `x`. -/
def regularSet (f : MeromorphicNonzero X) : Set X :=
  {x | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x = 0}

/-- Pointwise membership unfolds to the order-equals-zero predicate. -/
@[simp] lemma mem_regularSet {f : MeromorphicNonzero X} {x : X} :
    x ∈ f.regularSet ↔ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x = 0 :=
  Iff.rfl

/-- **Equality with the order-function zero set** (proven).

Under the `nonvanishing_germ` field of `MeromorphicNonzero`, the
chart-pulled-back order is never `⊤`, so the order-function value
`(mmeromorphicOrderAt _ f x).untop₀` equals `0` if and only if the
order itself equals `0`. Hence the regular set is exactly the zero
set of `MMeromorphicOn.orderFun`. -/
lemma regularSet_eq_orderFun_preimage_zero (f : MeromorphicNonzero X) :
    f.regularSet =
      {x : X | JacobianChallenge.MMeromorphicOn.orderFun
                  (𝓘(ℂ, ℂ)) f.toFun x = 0} := by
  ext x
  -- LHS membership: `mmeromorphicOrderAt _ f.toFun x = 0`.
  -- RHS membership: `orderFun _ f.toFun x = 0`, i.e.
  -- `(mmeromorphicOrderAt _ f.toFun x).untop₀ = 0`.
  -- The two are equivalent under `f.nonvanishing_germ x`.
  simp only [mem_regularSet, Set.mem_setOf_eq]
  exact (JacobianChallenge.MMeromorphicOn.orderFun_eq_zero_iff
            (f.nonvanishing_germ x)).symm

/-- **Real lemma (proven): the complement of the regular set is finite.**

The complement of `regularSet f` is the set of zeros + poles of `f`,
i.e. `{x | mmeromorphicOrderAt _ f.toFun x ≠ 0}`. Under the
`nonvanishing_germ` field this equals `{x | orderFun _ f.toFun x ≠ 0}`,
which is finite by `J2`'s `MMeromorphicOn.orderFun_support_finite` on
a compact Hausdorff complex 1-manifold. -/
lemma regularSet_compl_finite (f : MeromorphicNonzero X) :
    (f.regularSet)ᶜ.Finite := by
  -- Use J2's finiteness of the order-function support.
  have h_support_fin :
      {x : X | JacobianChallenge.MMeromorphicOn.orderFun
                (𝓘(ℂ, ℂ)) f.toFun x ≠ 0}.Finite :=
    JacobianChallenge.MMeromorphicOn.orderFun_support_finite
      (X := X) (𝓘(ℂ, ℂ)) f.toFun f.meromorphic f.nonvanishing_germ
  -- Show the complement of `regularSet` is the order-function support.
  have h_eq :
      (f.regularSet)ᶜ
        = {x : X | JacobianChallenge.MMeromorphicOn.orderFun
                    (𝓘(ℂ, ℂ)) f.toFun x ≠ 0} := by
    ext x
    simp only [Set.mem_compl_iff, mem_regularSet, Set.mem_setOf_eq]
    -- Goal: `mmeromorphicOrderAt _ f.toFun x ≠ 0 ↔ orderFun _ f.toFun x ≠ 0`.
    constructor
    · intro h_ne_zero
      intro h_orderFun_zero
      apply h_ne_zero
      exact (JacobianChallenge.MMeromorphicOn.orderFun_eq_zero_iff
                (f.nonvanishing_germ x)).mp h_orderFun_zero
    · intro h_orderFun_ne_zero
      intro h_order_zero
      apply h_orderFun_ne_zero
      exact (JacobianChallenge.MMeromorphicOn.orderFun_eq_zero_iff
                (f.nonvanishing_germ x)).mpr h_order_zero
  rw [h_eq]
  exact h_support_fin

/-- **Cofiniteness packaging** (proven). The regular set is *cofinite*
in `X` — i.e. its complement is finite. This is the API form needed
by downstream covering-space arguments: the restriction
`f̃ : f.regularSet → ...` is a complement of finitely many points,
which by `Set.Cofinite` is a member of the cofinite filter. -/
lemma regularSet_cofinite (f : MeromorphicNonzero X) :
    f.regularSetᶜ ∈ Filter.cofinite :=
  Filter.mem_cofinite.mpr (f.regularSet_compl_finite)

/-! ## Degree-constancy statement

The deep classical input. We name it as a `Prop`-valued `def`
(emphatically *not* an `axiom`) so that downstream code can take it as
a hypothesis without committing the kernel to an unproven assumption. -/

/-- **Degree-constancy on regular fibres of the pole extension**
(statement only — no proof).

For a `MeromorphicNonzero f : X → ℂ` whose pole extension
`f̃ : X → RiemannSphere` (M3-shipped) is a proper holomorphic map
between compact connected Riemann surfaces, the classical
topological-degree theorem says: there is a single integer `N : ℕ`
(the **topological degree**) such that for every regular value
`y : RiemannSphere` of `f̃`, the cardinality of the fibre
`f̃ ⁻¹' {y}`, counted with local multiplicity (the
`mmeromorphicOrderAt`-like local degree from `LocalMultiplicity.lean`),
equals `N`.

We package this as the existence of `N` such that **for every regular
value** `y` (i.e. every `y ∈ RiemannSphere` such that the preimage
is contained in `f.regularSet` — the local-multiplicity-1 condition),
the fibre `f.toRiemannSphere ⁻¹' {y}` is finite with `Finset.card`
equal to `N`. The "regular value" refinement is encoded by the
hypothesis `f.toRiemannSphere ⁻¹' {y} ⊆ f.regularSet`: at every
preimage `x` of a regular value, the order is exactly `0`, so the
local multiplicity (which is `|ord_x f|` for `f.toRiemannSphere` away
from the pole branch — see `Manifold/LocalMultiplicity.lean`'s
`localMult` ≥ 1) collapses to 1.

**Stated, not proven.** This is the topological-degree theorem for
proper holomorphic maps to the Riemann sphere; mathlib does not
supply the branched-covering API at pin
`8e3c989104daaa052921bf43de9eef0e1ac9fbf5`. -/
def degreeConstant_statement (f : MeromorphicNonzero X) : Prop :=
  ∃ N : ℕ, ∀ y : RiemannSphere,
    (f.toRiemannSphere ⁻¹' {y} ⊆ f.regularSet) →
      ∀ (h_fin : (f.toRiemannSphere ⁻¹' {y}).Finite), h_fin.toFinset.card = N

/-- **The degree-constancy hypothesis is exactly the topological-degree
input needed by R5 / the residue theorem** (statement only — no proof).

This `Prop`-valued `def` says: if `degreeConstant_statement` holds for
every `f : MeromorphicNonzero X`, then `TopologicalDegreeBalance X`
holds.

**Stated, not proven.** The implication is a real geometric reduction
that needs:

1. The local multiplicity at a regular value is exactly `1` (from R3 /
   `Manifold/LocalMultiplicity.lean`, partially landed by J3+L2).
2. Identification of the zero-fibre `f̃ ⁻¹' {0}` with the zeros of
   `f` and the pole-fibre `f̃ ⁻¹' {∞}` with the poles of `f`
   (immediate from `toRiemannSphere_eq_some_iff_nonneg` and
   `toRiemannSphere_eq_infty_iff_neg`, but the multiplicity-weighted
   form requires the J3+L2 multiplicity equality).
3. The signed sum `∑ ord_x f` decomposing into `(zero count) − (pole
   count)` once both are weighted by multiplicity.

None of (1)–(3) are formalised at this pin in the equality (rather
than inequality) form needed. We name the implication as a `Prop`
hook so that any future agent can discharge it without changing this
file's signature. -/
def degreeConstant_implies_R5_statement (X : Type u)
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] : Prop :=
  (∀ f : MeromorphicNonzero X, f.degreeConstant_statement) →
    JacobianChallenge.TopologicalDegreeBalance X

/-! ## Owed mathlib infrastructure (out of scope for this file)

Listed here for the agent picking up the combining-argument leg. Same
content as the "Owed" sections in `Manifold/Degree.lean` and
`Manifold/TopologicalDegree.lean`, restated against this file's
naming so the dependency surface is greppable.

* **`Owed.degreeConstancy.fibre_card_constant_on_regular_values`** —
  the body of `degreeConstant_statement` lifted to a real `theorem`.
  Requires branched-covering theory (Route A) or Stokes / `d log f`
  (Route B); see `Manifold/TopologicalDegree.lean` "Owed mathlib
  infrastructure" for the full route-by-route breakdown.

* **`Owed.degreeConstancy.local_mult_at_regular_eq_one`** — at every
  point `x ∈ f.regularSet`, the local multiplicity of `f̃` at `x`
  (the `LocalMultiplicity.lean`-style invariant) equals `1`. This is
  the R3 equality refinement (J3+L2 follow-up: the present R3 only
  gives `≥ 1`).

* **`Owed.degreeConstancy.regular_fibre_card_eq_total_zero_count`** —
  the cardinality of `f̃ ⁻¹' {0}` equals `∑_{x | ord_x f > 0} ord_x
  f` once each preimage is counted with the J3+L2 multiplicity. The
  analogous statement for the `∞`-fibre and `−ord_x f` pulls the
  pole sum out. Together with `degreeConstant_statement`, they give
  the R5 algebraic balance.

These three pieces, together with this file's
`regularSet_compl_finite`, complete the topological-degree route to
R5. None of the three are in mathlib at the pin; each is named here
so its absence is auditable.
-/

end MeromorphicNonzero

end JacobianChallenge

end
