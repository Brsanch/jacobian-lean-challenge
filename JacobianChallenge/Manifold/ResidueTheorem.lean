/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor
import JacobianChallenge.Divisor.PrincipalDivisor
import JacobianChallenge.Manifold.Degree
import JacobianChallenge.Manifold.MeromorphicAt
import JacobianChallenge.Manifold.MeromorphicDivisor
import JacobianChallenge.Manifold.RiemannSphere

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # The residue theorem on a compact connected Riemann surface

This file declares the **named structural statements** (`R1`–`R5`) of the
Route A proof of the residue theorem, and the conditional discharge
`residue_theorem_of_routeA`.

> For every `f : MeromorphicNonzero X` on a compact connected Riemann surface
> `X`, the principal divisor `(f) := principalDivisorMap f` has degree zero
> in `Div X`.

Equivalently, `∑_{x ∈ X} ord_x(f) = 0` (the orders at zeros sum to the orders
at poles). Together with the (already-landed) `principalDivisorMap` of
`Divisor/PrincipalDivisor.lean`, this is the analytic input needed for an
honest `PrincDiv X` and the strict-bar route for items 15, 19, 20.

## Status (post-`ResidueTheoremUnconditional.lean`)

R1–R5 are all **unconditionally discharged in-tree**:

| Statement | Discharge |
|---|---|
| `R1_poleExtension_statement` | `ResidueTheoremFromRsum.R1_poleExtension_statement_holds` (via `Manifold/MeromorphicExtension.lean`) |
| `R2_fibres_finite_statement` | `ResidueTheoremFromRsum.R2_fibres_finite_statement_holds` |
| `R3_localMultiplicity_statement` | `ResidueTheoremFromRsum.R3_localMultiplicity_statement_holds` |
| `R4_fibreSum_balance_statement` | `R4FibreSumBalance.R4_fibreSum_balance_statement_holds` |
| `R5_principal_degree_zero_statement` | `R5Unconditional.R5_principal_degree_zero_statement_holds` |

The headline `JacobianChallenge.residue_theorem` lives in
`Manifold/ResidueTheoremUnconditional.lean` as a one-line composition.
This file contains no `sorry`s.

## Two classical proof routes

**Route A — Topological degree.** A non-zero meromorphic `f : X → ℂ` extends
canonically to a holomorphic map `f̃ : X → RiemannSphere = ℂ ∪ {∞}`. The
*topological degree* of `f̃` (counted with multiplicity) is the same on every
fibre; in particular over `0 ∈ S²` the multiplicities sum to `∑_{f(x)=0} ord_x f`,
while over `∞ ∈ S²` they sum to `∑_{f(x)=∞} (-ord_x f)`. Equality of the two
fibre-degrees gives `∑_{f(x)=0} ord_x f + ∑_{f(x)=∞} ord_x f = 0`, i.e.
`∑_x ord_x f = 0`. **This is the route implemented in-tree.**

**Route B — Stokes / contour integration.** The 1-form `df / f` is meromorphic
on `X` with simple poles at `supp (f)` and integer residues equal to the local
orders. By Stokes on a small-disk-complement plus residue theorem in each
chart, `∑_x Res_x(df/f) = 0` on a closed compact 2-manifold. Sketched at the
end of this file; not implemented.

## What this file actually compiles

1. Five **named Prop-valued statements** `R1`–`R5` (the structural pieces of
   Route A). Each is a `def ... : Prop`. Their discharges live in the files
   listed above.
2. `theorem residue_theorem_of_routeA` — conditionally discharges the
   residue-theorem conclusion from `R5`. Useful for callers that want to
   thread an explicit `R5` hypothesis (e.g. for an alternative discharge
   route). No `sorry`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set OnePoint

namespace JacobianChallenge

universe u

namespace ResidueTheorem

/-! ## The five named owed statements

Each of these is a `Prop` whose proof is the corresponding classical
input. We record them as `def ... : Prop` (statements), not as `axiom`s
(which would persist in the kernel forever). The `residue_theorem` proof
below uses each as a `sorry` with a comment naming which classical theorem
discharges it. -/

variable (X : Type u)
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **(R1) Pole-extension.** Every non-zero meromorphic function
`f : MeromorphicNonzero X` admits a canonical holomorphic extension
`f̃ : X → RiemannSphere` to the Riemann sphere, sending poles of `f` to
`∞ : RiemannSphere` and otherwise agreeing with `↑(f x) : OnePoint ℂ`.
The extension is `ContMDiff` (analytic) and its `∞`-fibre is exactly the
pole set of `f`.

**Status:** discharged unconditionally by
`ResidueTheoremFromRsum.R1_poleExtension_statement_holds`, via
`MeromorphicNonzero.toRiemannSphere` and
`MeromorphicNonzero.toRiemannSphere_contMDiff` in
`Manifold/MeromorphicExtension.lean`. -/
def R1_poleExtension_statement : Prop :=
  ∀ (f : MeromorphicNonzero X),
    ∃ fTilde : X → RiemannSphere,
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ) ω fTilde ∧
      (∀ x : X, fTilde x = (OnePoint.infty : RiemannSphere) ↔
        (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ < 0) ∧
      (∀ x : X, (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ ≥ 0 →
        fTilde x = ((f.toFun x : ℂ) : RiemannSphere))

/-- **(R2) Zero and pole fibres are finite.** For every `f`, the sets
`{x | (mmeromorphicOrderAt I f x).untop₀ > 0}` (zeros) and
`{x | (mmeromorphicOrderAt I f x).untop₀ < 0}` (poles) are both finite.

**Status:** discharged unconditionally by
`ResidueTheoremFromRsum.R2_fibres_finite_statement_holds`, via
`MMeromorphicOn.zeros_finite` / `MMeromorphicOn.poles_finite` (in
`Manifold/MeromorphicDivisor.lean`) combined with compactness of `X` and
the `untop₀ ↔ WithTop ℤ` translation lemmas. -/
def R2_fibres_finite_statement : Prop :=
  ∀ (f : MeromorphicNonzero X),
    {x : X | (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ > 0}.Finite ∧
    {x : X | (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ < 0}.Finite

/-- **(R3) Multiplicity = local order.** For the canonical extension
`f̃ : X → RiemannSphere` (whose existence is `R1`), the *local multiplicity*
of `f̃` at `x` (in the sense of `LocalMultiplicity`) equals
`(mmeromorphicOrderAt I f x).untop₀.natAbs`. This is the standard local
normal form `z ↦ z^k` for an analytic map at a point, applied with `k =
ord_x(f)`.

**Status:** discharged unconditionally by
`ResidueTheoremFromRsum.R3_localMultiplicity_statement_holds`. The coarse
"multiplicity ≥ 1" form used here reduces to integer arithmetic
(`Int.natAbs ≠ 0 ↔ value ≠ 0`); the precise local-normal-form input enters
only in R4. -/
def R3_localMultiplicity_statement : Prop :=
  ∀ (f : MeromorphicNonzero X),
    ∀ (x : X),
      (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ ≠ 0 →
        (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀.natAbs ≥ 1

/-- **(R4) Topological-degree fibre-sum equality (the heart of Route A).**
Let `f̃ : X → RiemannSphere` be the canonical extension of `f`. Then the sum
of local multiplicities over the zero-fibre `{x | f x = 0}` (i.e.
`∑_{ord > 0} ord_x f`) equals the sum over the pole-fibre `{x | f x = ∞}`
(i.e. `∑_{ord < 0} -ord_x f`). Equivalently:

  `∑_{x : ord_x f > 0} ord_x f  +  ∑_{x : ord_x f < 0} ord_x f  =  0`

(both summed over the corresponding finite sets from `R2`).

This is the classical fact that the topological degree of a proper holomorphic
map between connected compact Riemann surfaces is constant across regular
values, applied to the two values `0` and `∞`.

**Status:** discharged unconditionally by
`R4FibreSumBalance.R4_fibreSum_balance_statement_holds`. This is the
classical fibre-sum balance for the Riemann-sphere extension of a
non-constant meromorphic function; the discharge composes the in-tree
topological-degree, chart-integral, and ramification-sum chips. -/
def R4_fibreSum_balance_statement : Prop :=
  ∀ (f : MeromorphicNonzero X)
    (hZ : {x : X | (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ > 0}.Finite)
    (hP : {x : X | (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ < 0}.Finite),
    (∑ x ∈ hZ.toFinset, (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀) +
      (∑ x ∈ hP.toFinset, (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀) = 0

/-- **(R5) Combined output of (R1)–(R4): the residue theorem in repackaged
form.** For every non-zero meromorphic `f`, the principal divisor `(f)` has
degree zero. This *is* the residue theorem; we factor it out as a named
statement so the headline `residue_theorem` is a one-liner against `R5`,
and so future replacement of `R5` (by a real proof routing through
R1+R2+R3+R4 or via Route B) immediately closes everything.

**Status:** discharged unconditionally by
`R5Unconditional.R5_principal_degree_zero_statement_holds`, composing R4
with `ResidueTheoremFromRsum.R5_principal_degree_zero_statement_of_R4`. -/
def R5_principal_degree_zero_statement : Prop :=
  ∀ (f : MeromorphicNonzero X), (principalDivisorMap f).degree = 0

end ResidueTheorem

/-! ### The residue theorem (the headline)

The headline `JacobianChallenge.residue_theorem` now lives in
`Manifold/ResidueTheoremUnconditional.lean`, as a one-line discharge
composing the in-tree R1+R2+R3+R4 chain through
`R5_principal_degree_zero_statement_holds`. It is no longer a skeleton:
R1, R2, R3, R4 are all unconditionally discharged in-tree
(`ResidueTheoremFromRsum.lean`, `R4FibreSumBalance.lean`).

The conditional discharge `residue_theorem_of_routeA` below remains as
a structural skeleton for callers that want to thread an explicit `R5`
hypothesis (e.g. for an alternative route, Stokes-based or otherwise). -/

/-! ### Conditional discharge

The lemma below shows that, given the named statement `R5`, the residue
theorem follows immediately. `R5` is discharged unconditionally by
`R5Unconditional.R5_principal_degree_zero_statement_holds`; this lemma is
retained for callers that want to thread an explicit `R5` hypothesis
(e.g. when replacing the in-tree R4 discharge with an alternative
Route B / Stokes proof). -/

theorem residue_theorem_of_routeA
    {X : Type u}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (hR5 : ResidueTheorem.R5_principal_degree_zero_statement X)
    (f : MeromorphicNonzero X) :
    (principalDivisorMap f).degree = 0 :=
  hR5 f

/-! ### Sketch of Route B (Stokes / contour integration)

For reference, here is the alternative route. We do *not* attempt it here
because none of the input infrastructure exists at the pin:

1. **Meromorphic 1-form `df / f`.** Construct the meromorphic 1-form
   `ω := df / f` on `X`. At a regular point, this is a holomorphic 1-form;
   at a zero / pole of `f` of order `k`, this is a 1-form with simple pole
   and residue `k` (resp. `-k`).

   *Owed from:* a meromorphic-1-form package on top of
   `Manifold/HolomorphicOneForm.lean`. Not at the pin.

2. **Residue at a pole of a meromorphic 1-form.** For each `x ∈ supp f`,
   define `Res_x(ω) ∈ ℂ` (the chart-independent residue of `ω` at `x`).

   *Owed from:* `Mathlib.Analysis.MeromorphicAt.Residue` (residue at a single
   point) plus chart-independence (analogous to
   `mmeromorphicOrderAt_eq_of_isManifold`). Not at the pin.

3. **Identification.** `Res_x(df/f) = ord_x(f)` for every `x` (in particular,
   the residue is an integer).

   *Owed from:* the local logarithmic-derivative formula
   `Res_z₀ ((f' / f) dz) = ord_{z₀}(f)`. This is in `Mathlib.Analysis.Complex`
   in some form but not packaged manifold-style at the pin.

4. **Stokes / global residue identity.** On a compact 2-manifold without
   boundary, the sum of all residues of a meromorphic 1-form is zero.

   *Owed from:* Stokes' theorem for compactly supported smooth 1-forms
   (`Mathlib.Geometry.Manifold.Stokes` exists in some form but does not yet
   package the residue version at the pin), or directly the
   `∮ ω = 0` over the boundary of `X \ {small disks around supp ω}`.

5. **Conclude.** Combine (3) and (4) to get `∑_x ord_x f = 0`.

The Stokes route is mathematically more direct but worse-supported by
mathlib at this commit; we record it here so that whoever picks up the
residue-theorem leg has both options to cost.
-/

end JacobianChallenge

end
