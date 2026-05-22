/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LinearSystemGermDeltaPFiniteDimRSUnconditional
import JacobianChallenge.Manifold.HolomorphicEquivRiemannSphere

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # `RR_DimGE2_GenusZero_Germ RiemannSphere` is unconditional

First concrete RS-anchor for the germ-side Riemann–Roch dimension
inequality at genus 0. The general-X reduction
`rr_DimGE2_GenusZero_Germ_of_uniformization_unconditional_RSFiniteDim`
(in `Topology/LinearSystemGermDeltaPFiniteDimRSUnconditional.lean`)
takes a uniformization hypothesis
`genus X = 0 → Nonempty (HolomorphicEquiv X RiemannSphere)` and
produces `RR_DimGE2_GenusZero_Germ X`. On `X = RiemannSphere`, the
uniformization is trivial (refl).

This is part of **path-(a)** progress on Item 14's open content:
discharging the Riemann–Roch dimension inequality on the concrete
genus-0 example. The general-X discharge then reduces to the
uniformization theorem alone (which is itself part of the open Item 14
forward direction — they correspond, classically).

## Significance

`RR_DimGE2_GenusZero_Germ X` is the **dimensional core** of RR at
genus 0: it asserts `dim_ℂ L(δp) ≥ 2` for some point `p`. Classically
this is the consequence of:

* Riemann–Roch formula: `dim L(D) - dim L(K-D) = deg D + 1 - g`.
* At `D = δp`, `g = 0`, `deg δp = 1`: gives `dim L(δp) = 2 + dim L(K - δp)`.
* Serre duality on `K - δp`: ≤ `dim L(K) = g = 0`.
* Hence `dim L(δp) = 2`.

On RS this is concretely realized: `L(δ∞)` is the 2-dimensional space
spanned by `{1, z}` (the linear polynomials), with `z = RSSimplePole`
the simple-pole-at-∞ function.

The general-X discharge requires actual uniformization (or
equivalently, the existence of a degree-1 map to RS). The trivial
RS-case is the **base case** that the general-X assembly depends on,
and it is what this chip closes.

## What ships

* `rr_DimGE2_GenusZero_Germ_riemannSphere` — `RR_DimGE2_GenusZero_Germ
  RiemannSphere` unconditional. Composes the existing in-tree assembly
  with the trivial RS ≃ RS uniformization.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-- **`RR_DimGE2_GenusZero_Germ RiemannSphere` is unconditional.**

Discharges the germ-side genus-0 RR dimension inequality
`∃ p, 2 ≤ dim_ℂ L(δp)` on the Riemann sphere via:

* The in-tree assembly
  `rr_DimGE2_GenusZero_Germ_of_uniformization_unconditional_RSFiniteDim`
  (which uses `LinearSystemGermDeltaPFiniteDim RiemannSphere`,
  unconditional in tree).
* The trivial RS ≃ RS uniformization
  (`holomorphicEquiv_RiemannSphere_self`).

This is the first concrete unconditional RS-anchor for the
germ-side RR dim count, completing the base case the general-X
assembly depends on. -/
theorem rr_DimGE2_GenusZero_Germ_riemannSphere :
    JacobianChallenge.MeromorphicFunctionField.RR_DimGE2_GenusZero_Germ
      JacobianChallenge.RiemannSphere :=
  JacobianChallenge.MeromorphicFunctionField.rr_DimGE2_GenusZero_Germ_of_uniformization_unconditional_RSFiniteDim
    (X := JacobianChallenge.RiemannSphere)
    (fun _ => ⟨JacobianChallenge.RiemannSphere.holomorphicEquiv_RiemannSphere_self⟩)

end RiemannSphere

end JacobianChallenge

end
