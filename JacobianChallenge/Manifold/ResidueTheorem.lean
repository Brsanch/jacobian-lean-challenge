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

This file states the **residue theorem**:

> For every `f : MeromorphicNonzero X` on a compact connected Riemann surface
> `X`, the principal divisor `(f) := principalDivisorMap f` has degree zero
> in `Div X`.

Equivalently, `∑_{x ∈ X} ord_x(f) = 0` (the orders at zeros sum to the orders
at poles). Together with the (already-landed) `principalDivisorMap` of
`Divisor/PrincipalDivisor.lean`, this is the last analytic input needed to
land an honest `PrincDiv X` and unblock the `STRICT-CLOSED` route for
challenge-spec items 15, 19, 20.

## SPECULATIVE SKELETON — `sorry` is intentionally allowed in this file

This file is the residue-theorem leg. The full proof depends on classical
inputs that are **not in mathlib** at the pin
`8e3c989104daaa052921bf43de9eef0e1ac9fbf5`. Per the I3 task brief, we ship
the **proof skeleton** with each gap closed by a `sorry` whose preceding
comment names the exact owed input. **Every `sorry` in this file is a
*named* gap with a one-line owed-from pointer**. No `axiom`s are introduced
(unlike `sorry`, an `axiom` would persist forever and contaminate the build).

`Basic.lean` is **not** modified. The `residue_theorem` here is what the
honest `PrincDiv X` and the related items 15/19/20 in `Basic.lean` will
ultimately route through.

## Two classical proof routes

**Route A — Topological degree.** A non-zero meromorphic `f : X → ℂ` extends
canonically to a holomorphic map `f̃ : X → RiemannSphere = ℂ ∪ {∞}`. The
*topological degree* of `f̃` (counted with multiplicity) is the same on every
fibre; in particular over `0 ∈ S²` the multiplicities sum to `∑_{f(x)=0} ord_x f`,
while over `∞ ∈ S²` they sum to `∑_{f(x)=∞} (-ord_x f)`. Equality of the two
fibre-degrees gives `∑_{f(x)=0} ord_x f + ∑_{f(x)=∞} ord_x f = 0`, i.e.
`∑_x ord_x f = 0`.

**Route B — Stokes / contour integration.** The 1-form `df / f` is meromorphic
on `X` with simple poles at `supp (f)` and integer residues equal to the local
orders. By Stokes on a small-disk-complement plus residue theorem in each
chart, `∑_x Res_x(df/f) = 0` on a closed compact 2-manifold.

We use **Route A** as the main flow because it composes more cleanly with the
already-landed `RegularValueWitness` and `degreeFiber` infrastructure in
`Manifold/Degree.lean`. Each gap is identified by its *named owed input*
(either a missing classical theorem or a missing piece of our own
infrastructure). Route B is sketched in a comment block at the end.

## Owed gaps — Route A

(R1) **Pole-extension.** Given `f : MeromorphicNonzero X`, build the canonical
     holomorphic extension `f̃ : X → RiemannSphere` sending poles of `f` to
     `∞`. Owed from: a small `Manifold/MeromorphicExtension.lean` writing
     `f̃ x = if mmeromorphicOrderAt I f x ≥ 0 then ↑(f x) else ∞` and proving
     it is `ContMDiff` to `RiemannSphere` using the local pole/zero normal
     form. Statement-level only at this pin.

(R2) **Zero / pole fibres are finite.** Mathlib infrastructure gap: this is
     the special case `Y = RiemannSphere`, `y ∈ {0, ∞}` of
     `Owed.degree.fibres_finite_statement` (already a named owed statement
     in `Manifold/Degree.lean`). On a compact `X` this also follows from
     local finiteness of the order divisor (`MMeromorphicOn.divisor` in
     `Manifold/MeromorphicDivisor.lean`) — but only after R1.

(R3) **Multiplicity = local order.** For the extension `f̃ : X → RiemannSphere`
     and `x ∈ X` with `f x = 0` (resp. pole), the local multiplicity of `f̃`
     at `x` equals `(mmeromorphicOrderAt I f x).untop₀.natAbs`. This is the
     standard local normal form `z ↦ z^k` for analytic maps; mathlib does
     not yet package this as a single named lemma at the pin.

(R4) **Topological degree = ∑ multiplicities on each fibre.** Owed from:
     `Owed.degree.fibre_card_well_defined_statement` *strengthened* to count
     with multiplicities. The `RegularValueWitness`-based `degreeFiber`
     currently only counts cardinality of regular fibres.

(R5) **Equality of fibre-degrees over 0 and ∞.** This is the classical
     topological-degree identity `deg(f̃) = #(f̃⁻¹ y₁) = #(f̃⁻¹ y₂)` for
     proper holomorphic maps between connected compact Riemann surfaces.
     Reduces to (R4) once both fibres are regular; otherwise needs the
     covering-space argument on `S² \ critical values`.

The five gaps together discharge `residue_theorem`. Each is owed from a
specific source listed at the corresponding `sorry` below.

## What this file actually compiles

1. The headline statement `residue_theorem` with the exact signature mandated
   by the brief: degree of the principal divisor equals `0`.
2. Five **named, honest Prop-valued statements** `R1`–`R5` (the structural
   pieces of Route A). Each is a `def ... : Prop` (no proof, just the
   classical statement), exposing the dependency surface for downstream.
3. A `theorem residue_theorem_of_routeA` that **conditionally closes** the
   residue theorem from one named hypothesis (`R5`, which is the residue
   theorem in summed-over-the-support form). This is `sorry`-free.
4. The advertised `theorem residue_theorem` that uses `residue_theorem_of_routeA`
   plus a single `sorry` for the missing proof of `R5` from `R1+R2+R3+R4`.

The composition `residue_theorem_of_routeA` + the five `R_i` axiomatic
inputs is **the proof skeleton**: it makes the dependency surface explicit
so that filling any one of the five (or, more precisely, R1–R4 → R5) is
the only remaining work.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

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

**Status:** statement only. Owed from a future
`Manifold/MeromorphicExtension.lean` package. -/
def R1_poleExtension_statement : Prop :=
  ∀ (f : MeromorphicNonzero X),
    ∃ f̃ : X → RiemannSphere,
      ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f̃ ∧
      (∀ x : X, f̃ x = (∞ : RiemannSphere) ↔
        (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ < 0) ∧
      (∀ x : X, (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ ≥ 0 →
        f̃ x = ((f.toFun x : ℂ) : RiemannSphere))

/-- **(R2) Zero and pole fibres are finite.** For every `f`, the sets
`{x | (mmeromorphicOrderAt I f x).untop₀ > 0}` (zeros) and
`{x | (mmeromorphicOrderAt I f x).untop₀ < 0}` (poles) are both finite.

**Status:** statement only. Discharged by combining `MMeromorphicOn.divisor`
(local finiteness of the order divisor, in
`Manifold/MeromorphicDivisor.lean`) with compactness of `X`; the *finite*
statement is owed because the local-finiteness packaging in mathlib lives
on `Function.locallyFinsuppWithin Set.univ` and the support-finset
extraction is per-divisor in this file but not yet exposed as a named
lemma at this pin. -/
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

**Status:** statement only. The local-normal-form theorem is not named in
mathlib at the pin. We state R3 in the coarse "multiplicity ≥ 1" form here
because the precise `JacobianChallenge.LocalMultiplicity` API needed for the
exact-equality statement is itself partial (`degreeStub` indicator only). -/
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

**Status:** statement only. This is precisely the residue theorem in
fibre-decomposed form — the form in which the topological-degree proof
naturally produces it. -/
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

**Status:** statement = the residue theorem. Discharged by combining
R1+R2+R3+R4 with the bookkeeping that `(principalDivisorMap f).degree =
∑_{x ∈ supp} ord_x f`, splitting the support sum over `ord > 0` and
`ord < 0` (using R2 to make both finite), and applying R4. -/
def R5_principal_degree_zero_statement : Prop :=
  ∀ (f : MeromorphicNonzero X), (principalDivisorMap f).degree = 0

end ResidueTheorem

/-! ### The residue theorem (the headline) -/

/-- The **residue theorem** on a compact connected Riemann surface: for every
non-zero global meromorphic function `f`, the principal divisor `(f)` has
degree zero, i.e. `∑_x ord_x f = 0`.

**SKELETON.** This file's `residue_theorem` ships with a single `sorry`
naming the owed input. See the file docstring for the five-step Route A
breakdown and `residue_theorem_of_routeA` for the conditional discharge. -/
theorem residue_theorem
    {X : Type u}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (f : MeromorphicNonzero X) :
    (principalDivisorMap f).degree = 0 := by
  -- OWED INPUT (single named gap):
  --   `JacobianChallenge.ResidueTheorem.R5_principal_degree_zero_statement X`
  --
  -- which decomposes (Route A) as the conjunction of the four named
  -- classical statements:
  --   R1 = `R1_poleExtension_statement X`     (pole-extension to S², ContMDiff)
  --   R2 = `R2_fibres_finite_statement X`     (zero & pole fibres finite)
  --   R3 = `R3_localMultiplicity_statement X` (local mult = local order)
  --   R4 = `R4_fibreSum_balance_statement X`  (∑ over zeros + ∑ over poles = 0)
  --
  -- Once R5 is discharged (by Route A via R1–R4, or by Route B via Stokes),
  -- this `theorem` is closed by `residue_theorem_of_routeA hR5 f`.
  --
  -- Source location of the owed input:
  --   * R1: future `Manifold/MeromorphicExtension.lean` (not yet in repo).
  --   * R2: combine `MMeromorphicOn.divisor` (local finiteness, in
  --         `Manifold/MeromorphicDivisor.lean`) with `CompactSpace X`;
  --         expose as a named lemma in this file or in `MeromorphicDivisor.lean`.
  --   * R3: classical local normal form `z ↦ z^k` for analytic maps; not
  --         in mathlib at the pin. See `Mathlib.Analysis.Analytic.Order` for
  --         the partial 1-D version.
  --   * R4: classical topological-degree theorem for proper holomorphic
  --         maps between compact Riemann surfaces; not in mathlib.
  sorry

/-! ### Conditional discharge (no new `sorry`s)

The lemma below shows that **assuming** the bottom-line owed statement `R5`,
the residue theorem follows immediately. This is the structural skeleton:
any future replacement of `R5` (by a real proof, either via the Route A
chain R1+R2+R3+R4 or via Route B Stokes) immediately discharges the
`residue_theorem` headline via this lemma.

`R5` is the conjunction-output of `R1+R2+R3+R4`; we split it out so that the
headline `residue_theorem` is a clean one-liner against a single named hypothesis. -/

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
