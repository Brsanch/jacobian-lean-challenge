/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor
import JacobianChallenge.Divisor.PrincipalDivisor
import JacobianChallenge.Divisor.PrincipalDivisorRange
import JacobianChallenge.Divisor.FiberPullback
import JacobianChallenge.Manifold.MeromorphicExtension
import JacobianChallenge.Manifold.ResidueTheorem
import JacobianChallenge.Manifold.RiemannSphere

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Topological-degree balance for the pole extension

This file packages the **R5** named gap of `Manifold/ResidueTheorem.lean`
as a single, named topological-degree statement:

> For every non-constant `f : MeromorphicNonzero X` on a compact connected
> Riemann surface `X`, the algebraic count of zeros equals the algebraic
> count of poles:
>
>   `∑_{x | ord_x f > 0} ord_x f  =  ∑_{x | ord_x f < 0} (-ord_x f)`.
>
> Equivalently, `(principalDivisorMap f).degree = 0`.

This is the *topological-degree theorem for proper holomorphic maps to the
Riemann sphere*: the canonical pole-extension `f̃ : X → RiemannSphere`
(M3-shipped as `MeromorphicNonzero.toRiemannSphere_contMDiff` in
`Manifold/MeromorphicExtension.lean`) is a proper holomorphic map between
compact connected Riemann surfaces. For such maps, the algebraic *degree*
counted with multiplicity is constant on regular values, and the two
particular values `0 ∈ S²` and `∞ ∈ S²` give the zero-fibre and pole-fibre
sums respectively. Equality of these two fibre-sums *is* the residue-theorem
identity `(principalDivisorMap f).degree = 0`.

## Why this file exists

The `Manifold/ResidueTheorem.lean` file decomposes the residue theorem into
the named gaps R1–R5. R1 (pole extension) is **CLOSED** by M3 in
`Manifold/MeromorphicExtension.lean`. R2 (finite fibres) is **CLOSED** by
J2. R3 (multiplicity = local order) is **partially closed** by J3 and L2.
The missing link, R4–R5 (degree-balance: combining the local pieces into a
global identity), is the *combining argument* — and that combining argument
is exactly what this file's `TopologicalDegreeBalance` names.

The structural point: `TopologicalDegreeBalance X` and `ResidueTheorem X`
are **the same `Prop`**. Both unfold to
`∀ f : MeromorphicNonzero X, (principalDivisorMap f).degree = 0`. The
difference is purely *narrative*: the residue-theorem name foregrounds the
contour-integral / Stokes route, while the topological-degree-balance name
foregrounds the covering-space / branched-covering route. The
`Iff.rfl` lemma below records this identification at compile time.

## What this file does **not** do

It does **not** prove `TopologicalDegreeBalance`. The actual proof requires
either:

1. **Covering-space theory.** `f̃ : X → S²` is a branched covering. Off the
   (finite) set of critical values, `f̃` restricts to a covering map of
   constant degree `d`, and at every regular value the fibre cardinality
   equals `d`. Equality at the two regular values `0` and `∞` gives the
   degree-balance identity. Mathlib's `Mathlib.Topology.Covering` does not
   yet supply the *branched*-covering API at the pin
   `8e3c989104daaa052921bf43de9eef0e1ac9fbf5`; the unbranched part exists,
   but the chart-side excision around the critical values is owed.

2. **Stokes / `d log f`.** The 1-form `df / f` has integer residues equal to
   the local orders, and the integral over a closed compact 2-manifold is
   zero. Mathlib has `Mathlib.Geometry.Manifold.IntegralOverSubmanifold` in
   skeletal form at the pin but does not package the residue version of
   Stokes' theorem; a meromorphic-1-form residue API is also owed (see the
   sketch in the Route B comment of `Manifold/ResidueTheorem.lean`).

Neither of these is in mathlib at the pin. **No proof of
`TopologicalDegreeBalance` is attempted here.** What this file ships:

* The structural definition `TopologicalDegreeBalance` (a `Prop`-valued
  `def`, **not** an `axiom`).
* The equivalence `topologicalDegreeBalance_iff_residueTheorem`
  (`Iff.rfl`, since both sides unfold to the same `Prop`).
* Documentation of the missing mathlib infrastructure with named pointers
  to the routes that would discharge it.

No `sorry`. No `axiom`. Strictly statement-level packaging.

## Relation to the rest of the residue-theorem skeleton

Three named identifications all unfold to the same `Prop`:

* `JacobianChallenge.ResidueTheorem`
  (in `Divisor/PrincipalDivisorRange.lean`) — the *contour-integral* name.
* `JacobianChallenge.R4_signedMult_zero_statement`
  (in `Manifold/FibreBalance.lean`) — the *signed-multiplicity sum* name.
* `JacobianChallenge.TopologicalDegreeBalance`
  (this file) — the *covering-space degree* name.

All three are the same `Prop`-valued statement. Each name makes a different
proof route conspicuous: contour-integral, signed-multiplicity bookkeeping,
or topological-degree-of-a-branched-covering. Discharging any one of them
discharges all three (and `residue_theorem` in
`Manifold/ResidueTheorem.lean`) by `Iff.rfl` substitution.
-/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Topological degree balance for the pole extension** (statement only).

For every non-constant `f : MeromorphicNonzero X` on a compact connected
Riemann surface, the algebraic count of zeros equals the algebraic count
of poles:

  `∑_{x | ord_x f > 0} ord_x f  =  ∑_{x | ord_x f < 0} (-ord_x f)`.

Equivalently, `(principalDivisorMap f).degree = 0` (the divisor degree
sums *signed* multiplicities, so the equality `(zero sum) = (pole sum)`
is equivalent to the signed sum being zero).

**Stated, not proven.** This is the topological-degree theorem for proper
holomorphic maps to the Riemann sphere: on the M3-side, the canonical
pole-extension `f̃ : X → RiemannSphere`
(`MeromorphicNonzero.toRiemannSphere_contMDiff`) is a `ContMDiff` proper
holomorphic map, and the classical statement is that `f̃` has *constant
fibre cardinality* (counted with multiplicity) on regular values. Mathlib
does not yet supply the branched-covering / topological-degree API for
this at pin `8e3c989104daaa052921bf43de9eef0e1ac9fbf5`.

This is a `Prop`-valued `def`, **not an `axiom`**: the body is the actual
mathematical statement (the residue-theorem identity), recorded so that
downstream code can take it as a hypothesis without committing the kernel
to an unproven assumption. -/
def TopologicalDegreeBalance (X : Type u)
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] : Prop :=
  ∀ f : MeromorphicNonzero X, (principalDivisorMap f).degree = 0

/-- **The topological-degree balance is *exactly* the residue theorem.**

Both `TopologicalDegreeBalance X` and `ResidueTheorem X` (the latter from
`Divisor/PrincipalDivisorRange.lean`) unfold to the same `Prop`:

  `∀ f : MeromorphicNonzero X, (principalDivisorMap f).degree = 0`.

* `TopologicalDegreeBalance X` (this file) names the statement after the
  *covering-space* / topological-degree route to the proof: `f̃ : X → S²`
  is a branched covering, regular fibres have constant cardinality counted
  with multiplicity, and the equality at the two regular values `0`, `∞`
  gives the identity.
* `ResidueTheorem X` (in `Divisor/PrincipalDivisorRange.lean`) names the
  same statement after the *contour-integral* / Stokes route: the residue
  of `df / f` at a zero/pole equals the local order, and Stokes on a
  compact 2-manifold without boundary gives zero total residue.

This `Iff.rfl` is the load-bearing structural fact: the topological-degree
identity *is* the residue theorem (and is also `R4_signedMult_zero_statement`
of `Manifold/FibreBalance.lean`, and `R5_principal_degree_zero_statement`
of `Manifold/ResidueTheorem.lean`). Discharging any one of the four named
versions discharges all four by `Iff.rfl` substitution.

The proof is `Iff.rfl` because both sides are *definitionally* the same
universal statement over `MeromorphicNonzero X`. -/
lemma topologicalDegreeBalance_iff_residueTheorem :
    TopologicalDegreeBalance X ↔ ResidueTheorem X := Iff.rfl

/-- **The topological-degree balance is *exactly* the R5 statement** of
`Manifold/ResidueTheorem.lean`'s named-gap decomposition.

This is the dual of `topologicalDegreeBalance_iff_residueTheorem` against
the R5 name: any proof of either name immediately discharges the
`residue_theorem` skeleton's last `sorry` via
`residue_theorem_of_routeA`.

Both sides unfold to
`∀ f : MeromorphicNonzero X, (principalDivisorMap f).degree = 0`, so the
`Iff` is `Iff.rfl`. -/
lemma topologicalDegreeBalance_iff_R5 :
    TopologicalDegreeBalance X
      ↔ ResidueTheorem.R5_principal_degree_zero_statement X :=
  Iff.rfl

/-! ### Owed mathlib infrastructure for a real proof

Listed here for the next agent picking up the combining-argument leg.
Neither route is in mathlib at the pin
`8e3c989104daaa052921bf43de9eef0e1ac9fbf5`; the missing pieces are named
explicitly so that the discharge work is auditable.

**Route A (covering-space / branched-covering).**

The pole-extension `f̃ : X → RiemannSphere` is a proper holomorphic map
between compact connected Riemann surfaces (M3 closed `f̃` is `ContMDiff`,
and `X` and `RiemannSphere` are both compact). The classical theorem says
`f̃` is a *branched covering*: there is a finite set `C ⊆ RiemannSphere`
of critical values such that `f̃ : X \ f̃⁻¹ C → RiemannSphere \ C` is an
ordinary covering map, of finite degree `d`, and over each critical value
the fibre-sum-with-multiplicity also equals `d`.

Owed mathlib pieces:

* `Mathlib.Topology.Covering` (already exists) gives unbranched coverings
  and constant fibre cardinality on connected base.
* The *branched* covering API is owed: chart-side excision around
  critical values, plus the lemma "for a proper holomorphic map between
  compact Riemann surfaces, the critical-value set is finite and the
  restriction to its complement is a covering."
* The lemma "fibre-sum counted with local multiplicity equals the
  topological degree" — this is the multiplicity-strengthened form of
  `J2`'s constant-cardinality result. The cardinality form is in
  `Manifold/Degree.lean` (`degreeFiber`) but the multiplicity-weighted
  form is owed.
* On the J3 / L2 side, the *equality* of local multiplicity with
  `|ord_x f|` (not just the inequality `≥ 1` of R3 in
  `Manifold/ResidueTheorem.lean`) is partially landed; promoting this to
  the equality form is the J3+L2 follow-up that closes R3.

**Route B (Stokes / `d log f`).**

The meromorphic 1-form `ω := df / f` has simple poles at `supp f` with
integer residues equal to the local orders. Stokes / Cauchy on a closed
compact 2-manifold gives `∑_x Res_x ω = 0`. This route's owed pieces:

* A meromorphic-1-form package on top of
  `Manifold/HolomorphicOneForm.lean`. Not at the pin.
* Manifold-style residue at a single point of a meromorphic 1-form
  (mathlib has `Mathlib.Analysis.MeromorphicAt.Residue` for the planar
  case; chart-independence via the analogue of
  `mmeromorphicOrderAt_eq_of_isManifold` is owed).
* The local logarithmic-derivative identity `Res_z₀ ((f' / f) dz)
  = ord_{z₀}(f)`. This is in `Mathlib.Analysis.Complex` for the planar
  case but is not packaged manifold-style at the pin.
* Stokes for compactly-supported smooth 1-forms on a compact 2-manifold
  (`Mathlib.Geometry.Manifold.Stokes` is partial at the pin).

Either route closes the same `Prop`. The choice is a costing question for
the next agent.
-/

end JacobianChallenge

end
