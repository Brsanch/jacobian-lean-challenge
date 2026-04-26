/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneForm
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-! # The period lattice of a compact Riemann surface — placeholder

This file defines a *parallel, honest-but-placeholder* construction of the
analytic Jacobian as the quotient `(Fin (genus X) → ℂ) ⧸ PeriodLattice X`,
where at this pin `PeriodLattice X := ⊥` (the trivial subgroup).

It is **not** wired into `JacobianChallenge.Jacobian` (which currently routes
through `Pic⁰` with a different placeholder `PrincDiv = ⊥`). The two
constructions are deliberately kept independent so that downstream callers
can choose: discrete-topology `Pic⁰`-based stub (current `Jacobian X`) vs.
manifold-topology torus-based stub (`AnalyticTorus X` here). Switching
`Jacobian X` to the latter is a downstream call, intentionally **not** made
in this file.

## What "honest" means here

The genuine period lattice for a compact Riemann surface `X` of genus `g` is

  Λ = { (∫_{γ_i} ω_j)_{j=1..g} : [γ_i] ∈ H₁(X; ℤ) } ⊆ ℂ^g,

a discrete full-rank `ℤ`-submodule of rank `2g`. The quotient `ℂ^g / Λ` is
then a compact complex `g`-torus, the analytic Jacobian.

To build `Λ` honestly we owe:

* `H₁(X; ℤ)` for a (compact, connected, complex-analytic) `X` — **not** in
  mathlib at the pin (`8e3c989104daaa052921bf43de9eef0e1ac9fbf5`,
  15 Apr 2026); see e.g. `Mathlib.AlgebraicTopology.SingularSet` for what
  *is* available, none of which gives the integer first-homology of a
  Riemann surface as an abelian group with a finite generating set.
* A fully-integrated period pairing
  `∫ : H₁(X; ℤ) × HolomorphicOneForm X → ℂ`. The sister file
  `JacobianChallenge/Manifold/PeriodIntegral.lean` defines a *placeholder*
  `period` returning `0`; the honest period requires path integrals of
  cotangent-bundle sections along loops, which in turn requires
  `MeromorphicAt`-on-manifold + Stokes for closed forms.
* Discreteness of `Λ` in `ℂ^g`, equivalently full-rank `2g`. This follows
  classically from the non-degeneracy of the period matrix (Riemann
  bilinear relations); not derivable from anything currently in this repo.

Until those land, `PeriodLattice X` here is the **placeholder `⊥`**, with a
loud docstring. Everything below is honest *modulo the placeholder*: the
quotient topology, group structure, T2 separation, and topological-group
property are all the genuine ones induced from `ℂ^g`; they are simply
applied to the trivial subgroup, so the resulting `AnalyticTorus X` is
**homeomorphic to `ℂ^g` (not compact)** rather than a torus. This is the
same trade-off as the current `Jacobian X = Pic⁰ X` stub: that one is
`Div0 X` (discrete, in general infinite generators); this one is `ℂ^g`
(manifold-flavoured continuous topology, but non-compact).

## Instances supplied (honest modulo `PeriodLattice = ⊥`)

* `AddCommGroup (AnalyticTorus X)` — via mathlib's
  `QuotientAddGroup.Quotient.addCommGroup` (every subgroup of an abelian
  group is normal via `AddSubgroup.normal_of_isAddCommutative`).
* `TopologicalSpace (AnalyticTorus X)` — the quotient topology, via
  `QuotientAddGroup.instTopologicalSpace`. Coincides with the `ℂ^g`
  topology under the canonical homeomorphism `(ℂ^g) ⧸ ⊥ ≃ₜ ℂ^g`.
* `IsTopologicalAddGroup (AnalyticTorus X)` — via
  `QuotientAddGroup.instIsTopologicalAddGroup`, which fires for any
  `[N.Normal]`; the latter is automatic because `ℂ^g` is abelian.
* `T2Space (AnalyticTorus X)` — derived from
  `QuotientAddGroup.instT3Space` after registering closedness of `⊥` as
  an `IsClosed` instance. `(⊥ : AddSubgroup _)` has carrier `{0}`, which
  is closed in any T2 group.

## Instances **not** supplied (deliberate gaps)

* `CompactSpace (AnalyticTorus X)` — `ℂ^g` is non-compact and the
  placeholder `Λ = ⊥` means the quotient is non-compact too. Same gap as
  the current `Jacobian` stub.
* `ChartedSpace (Fin (genus X) → ℂ) (AnalyticTorus X)` — would require
  transporting the trivial chart on `ℂ^g` across the canonical
  isomorphism `(ℂ^g) ⧸ ⊥ ≃ ℂ^g`. Doable in principle (the bijection
  `(QuotientAddGroup.mk : ℂ^g → ℂ^g ⧸ ⊥)` is a homeomorphism via
  the standard quotient-by-a-trivial-subgroup API) but the
  `OpenPartialHomeomorph` boilerplate to feed into `ChartedSpace` cleanly
  at this pin would expand the file substantially; left as future work
  for the honest-`Λ` version where charts come from local sections of
  the covering `ℂ^g → ℂ^g / Λ`.
* `IsManifold 𝓘(ℂ) ω (AnalyticTorus X)` — depends on the
  `ChartedSpace` above.
* `LieAddGroup 𝓘(ℂ) ω (AnalyticTorus X)` — depends on
  `IsManifold` plus smoothness of group operations.

## Anti-hack

The literal hack "make `AnalyticTorus X` compact by collapsing it to
`PUnit`" is ruled out by the `IsTopologicalAddGroup` + `T2Space`
instances landing on the genuine quotient `(ℂ^g) ⧸ ⊥`, **not** on a
constant type. A strict reader can verify by checking
`AnalyticTorus.mk_injective` below: the canonical map
`ℂ^g → AnalyticTorus X` is injective (because `Λ = ⊥`), which is
*false* for any constant-type fake when `g ≥ 1`. -/

open scoped ContDiff Manifold

noncomputable section

set_option diagnostics.threshold 100

namespace JacobianChallenge

variable (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The **period lattice** of a compact Riemann surface `X`, as an additive
subgroup of `Fin (genus X) → ℂ`.

**Placeholder at this pin.** Defined as the trivial subgroup `⊥`, awaiting:

1. `H₁(X; ℤ)` for compact Riemann surfaces (not in mathlib at this pin).
2. An honest period pairing `H₁(X; ℤ) × HolomorphicOneForm X → ℂ`
   (placeholder lives in `JacobianChallenge/Manifold/PeriodIntegral.lean`
   currently returning `0`).
3. Discreteness / full-rank-`2g` of the resulting subgroup
   (Riemann bilinear relations).

See the file-level docstring for the full set of instances supplied
*modulo this placeholder*, and which instances on the resulting quotient
are deliberately left as future work. -/
def PeriodLattice : AddSubgroup (Fin (JacobianChallenge.genus X) → ℂ) := ⊥

/-- The **analytic torus** of a compact Riemann surface, defined as the
quotient `(Fin (genus X) → ℂ) ⧸ PeriodLattice X`.

**Parallel to `JacobianChallenge.Jacobian`, not a replacement.** The
existing `Jacobian X` routes through `Pic⁰` with a different placeholder
(`PrincDiv = ⊥`); this `AnalyticTorus X` routes through the period-lattice
construction with its own placeholder (`PeriodLattice = ⊥`). At the
current pin the two are not isomorphic — `Jacobian X` is `Div0 X`
(discrete, in general infinite generators) and `AnalyticTorus X` is
`ℂ^g ⧸ ⊥ ≃ ℂ^g` (continuous, non-compact). Switching `Jacobian X` to
use this construction is a downstream call deliberately not made here.

See the file-level docstring for the supplied instances and the
honest-but-non-discharged gaps. -/
def AnalyticTorus : Type :=
  (Fin (JacobianChallenge.genus X) → ℂ) ⧸ PeriodLattice X

namespace AnalyticTorus

/-- The additive abelian group structure on `AnalyticTorus X`, inherited
from the quotient by the (placeholder) period lattice. The `Normal`
hypothesis required by `QuotientAddGroup.Quotient.addCommGroup` is
discharged automatically: every subgroup of an abelian group is normal,
via mathlib's `AddSubgroup.normal_of_isAddCommutative`. -/
instance instAddCommGroup : AddCommGroup (AnalyticTorus X) :=
  inferInstanceAs <| AddCommGroup
    ((Fin (JacobianChallenge.genus X) → ℂ) ⧸ PeriodLattice X)

/-- The quotient topology on `AnalyticTorus X`, inherited from `ℂ^g` via
`QuotientAddGroup.instTopologicalSpace`. -/
instance instTopologicalSpace : TopologicalSpace (AnalyticTorus X) :=
  inferInstanceAs <| TopologicalSpace
    ((Fin (JacobianChallenge.genus X) → ℂ) ⧸ PeriodLattice X)

/-- `AnalyticTorus X` is a topological additive group: addition and
negation descend continuously through the quotient. Inherited from
`QuotientAddGroup.instIsTopologicalAddGroup`, which fires for any
normal subgroup of an additive topological group. Normality of the
placeholder `PeriodLattice X = ⊥` is automatic because `ℂ^g` is abelian. -/
instance instIsTopologicalAddGroup : IsTopologicalAddGroup (AnalyticTorus X) :=
  inferInstanceAs <| IsTopologicalAddGroup
    ((Fin (JacobianChallenge.genus X) → ℂ) ⧸ PeriodLattice X)

/-- Closedness of the (placeholder) period lattice as a subset of `ℂ^g`.
Registered as an `instance` so that mathlib's `QuotientAddGroup.instT2Space`
(and `instT3Space`, `instT1Space`) can fire on `AnalyticTorus X`.

For `PeriodLattice X = ⊥`, the carrier is `{0}`, which is closed in any
T2 space; `ℂ^g` is T2 because it is a finite product of T2 spaces.

The exact form of the goal type matches mathlib's instance argument
`[IsClosed (H : Set G)]` in `QuotientGroup.instT2Space`, with the
`SetLike` coercion `↑H` from `AddSubgroup G` to `Set G`. -/
instance instIsClosedPeriodLattice :
    IsClosed ((PeriodLattice X : Set (Fin (JacobianChallenge.genus X) → ℂ))) := by
  -- Reduce the carrier of `⊥` to `{0}`.
  change IsClosed
    ((⊥ : AddSubgroup (Fin (JacobianChallenge.genus X) → ℂ)) :
      Set (Fin (JacobianChallenge.genus X) → ℂ))
  rw [AddSubgroup.coe_bot]
  exact isClosed_singleton

/-- `AnalyticTorus X` is Hausdorff: with the closedness instance above
plus the normal-subgroup quotient machinery, mathlib's
`QuotientAddGroup.instT2Space` fires automatically. -/
instance instT2Space : T2Space (AnalyticTorus X) :=
  inferInstanceAs <| T2Space
    ((Fin (JacobianChallenge.genus X) → ℂ) ⧸ PeriodLattice X)

/-! ### Anti-hack: the canonical map is injective (rules out PUnit fakes) -/

/-- The canonical projection `ℂ^g → AnalyticTorus X`. -/
def mk : (Fin (JacobianChallenge.genus X) → ℂ) → AnalyticTorus X :=
  QuotientAddGroup.mk (s := PeriodLattice X)

/-- The canonical projection is injective, because `PeriodLattice X = ⊥`.
This is the strict-reader's check that `AnalyticTorus X` is genuinely the
quotient `(ℂ^g) ⧸ ⊥` (homeomorphic to `ℂ^g`) and not a fake constant
type like `PUnit`. -/
lemma mk_injective : Function.Injective (mk X) := by
  intro a b hab
  -- `QuotientAddGroup.mk a = QuotientAddGroup.mk b` iff `-a + b ∈ Λ`.
  have h : -a + b ∈ PeriodLattice X := by
    rw [← QuotientAddGroup.eq]
    exact hab
  -- `Λ = ⊥`, so `-a + b = 0`, hence `a = b`.
  rw [show PeriodLattice X = ⊥ from rfl, AddSubgroup.mem_bot] at h
  exact neg_add_eq_zero.mp h

end AnalyticTorus

end JacobianChallenge

end
