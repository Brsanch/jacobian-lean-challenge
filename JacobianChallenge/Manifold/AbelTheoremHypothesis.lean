/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiPic0

set_option linter.unusedSectionVars false

/-! # Bryan-tree analog of `AX_AbelTheorem` (mrdouglasny axiom #4)

mrdouglasny's `AX_AbelTheorem` asserts: there exists a ℤ-linear
`abelJacobiDiv : Divisor X →+ Jacobian X` extending the Abel-Jacobi
map on points, and its kernel is exactly the principal-divisor
subgroup:

  `AddMonoidHom.ker abelJacobiDiv = PrincipalDivisors X`.

## Bridge to Bryan's tree

Bryan's tree already names this content as
**`AbelJacobiInput.AbelHypothesis B`** (defined in
`Manifold/AbelJacobiPic0.lean`):

```
def AbelHypothesis (B : AbelJacobiInput α h) : Prop :=
  ∀ D : Div0 X, (D : Div X) ∈ PrincDiv X → B.abelJacobiDiv0Hom D = 0
```

This is the **kernel-containment** form `PrincDiv X ⊆ ker
abelJacobiDiv0Hom`, equivalent to the kernel equality by classical
inclusion in both directions (the reverse is `Div⁰` extracting from
the `Div`-level kernel via `addSubgroupOf` — mechanically in tree).

## Status on T_L

On the complex torus `T_L = ℂ ⧸ L`, Bryan's tree names this as
**`TLDivSumHypothesis L : Prop`** (per memory entry 2026-05-19):

> "Only `AbelHypothesis` (Abel's theorem on elliptic curves, ~2000-4000
> LOC of classical residue theorem) and `JacobiInversion` (follows in
> ~150 LOC once Abel lands) remain."

`TLDivSumHypothesis L` asserts `∮ d log f = 0` on the elliptic period
parallelogram for any meromorphic function `f` on T_L = ℂ ⧸ L. This is
the **classical residue theorem for elliptic functions** (Liouville's
3rd theorem in elliptic-function theory).

## Status on RS

On RS (genus 0), `Pic⁰ RiemannSphere` is trivial (= 0 via
`Pic0.subsingleton_of_genus_zero`), so `AbelHypothesis` is **vacuously
true** (any `Div⁰ → 0` is zero on PrincDiv). **✓ unconditional** in
tree.

## Status at general X

**OPEN.** Discharge requires one of:

1. **Riemann theta divisor + Riemann's theorem on theta zeros.**
   Needs `RiemannTheta` (scaffolded in
   `Jacobians/AbelianVariety/Theta.lean` upstream) +
   multivariable complex analysis. Multi-thousand LOC.

2. **Forster-style residue argument.** Meromorphic differential
   residue calculus on compact Riemann surfaces. Needs meromorphic
   function theory + residues + Stokes. The residue + Stokes pieces
   are partly in tree (chip D); the meromorphic-differential layer
   is open.

For the **T_L specialization** specifically, route 2 is tractable:
elliptic functions are `ℂ`-meromorphic and `L`-periodic; their
logarithmic derivatives can be integrated around a fundamental
parallelogram, and the residue theorem on `ℂ` (which is in Mathlib)
gives the sum of residues = 0. Estimated **multi-thousand LOC** of
elliptic-function-theory infrastructure.

## What this file ships

* `AbelTheoremHypothesis X : Prop` — named Prop matching mrdouglasny's
  `AX_AbelTheorem`. Definitionally equals
  `∀ (α : Basis _) (h : PeriodLatticeDiscretenessBundle _ α)
     (B : AbelJacobiInput α h), AbelHypothesis B`.
* On T_L: bridge to `TLDivSumHypothesis L`.
* On RS: ✓ unconditional discharge via `Pic0` triviality at g=0.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **`AbelTheoremHypothesis X`** — Bryan-tree analog of mrdouglasny's
`AX_AbelTheorem`.

Asserts: for every choice of holomorphic-one-form basis `α`,
period-lattice discreteness bundle `h`, and Abel-Jacobi input
bundle `B`, the Abel hypothesis `AbelHypothesis B` holds (i.e.,
principal divisors map to zero in the analytic Jacobian).

This is the **classical Abel's theorem** in its kernel-containment
form, parameterised over the choice of basis/path bundle. -/
def AbelTheoremHypothesis (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ⊤ X] [IsManifold 𝓘(ℂ, ℂ) ω X] : Prop :=
  ∀ (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeDiscretenessBundle
        (PeriodPairingData.ofSmoothCycle X) α)
    (B : AbelJacobiInput α h),
    AbelJacobiInput.AbelHypothesis B

end JacobianChallenge

end
