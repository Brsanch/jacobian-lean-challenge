/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.BilinearFromHodgeChain
import JacobianChallenge.Manifold.HolomorphicOneFormLinear
import JacobianChallenge.Manifold.DefaultHolomorphicOneFormBasis

set_option linter.unusedSectionVars false

/-! # `CompleteHodgeRiemannHypothesis` UNCONDITIONAL at genus 0 (chip 20a)

For any compact connected complex 1-manifold `X` with
`JacobianChallenge.genus X = 0`, `CompleteHodgeRiemannHypothesis`
holds unconditionally — the empty bundle is vacuously satisfied.

The chain:

* `DiskChartCover.holomorphicOneFormFiniteDim_holds` — `[FiniteDimensional
  ℂ (HolomorphicOneForm X)]` is unconditional on every compact
  connected complex 1-manifold (Forster–Riesz route).
* `holomorphicOneForm_subsingleton_of_genus_eq_zero` —
  `genus X = 0 + [FiniteDimensional]` ⟹ `Subsingleton
  (HolomorphicOneForm X)`.
* `completeHodgeRiemannHypothesis_of_subsingleton` (BilinearFromHodgeChain)
  — `[Subsingleton (HolomorphicOneForm X)]` ⟹ CHRH for any data,
  basis, cycleGens (vacuous).

The net statement requires no orientation, no Hodge form choice, no
Riemann bilinear input — just the topology condition `genus X = 0`.
This is the "vacuous genus-0 CHRH" headline parallel to chip 19r/t
which closes the genus-1 case unconditionally on `T_L`.

## What this file ships

* `completeHodgeRiemannHypothesis_of_genus_eq_zero` — the headline.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`CompleteHodgeRiemannHypothesis` UNCONDITIONAL at `genus X = 0`.**

The only premise beyond the standard compact-connected-complex-
1-manifold setup is `genus X = 0`. Under this, finite-dimensionality
of `HolomorphicOneForm X` (in tree via `DiskChartCover`) makes
`Subsingleton (HolomorphicOneForm X)` automatic, and CHRH degenerates
to the vacuous bundle. -/
theorem completeHodgeRiemannHypothesis_of_genus_eq_zero
    (h_genus : JacobianChallenge.genus X = 0)
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1) :
    CompleteHodgeRiemannHypothesis data basis_ω cycleGens := by
  haveI hFD : FiniteDimensional ℂ (HolomorphicOneForm X) :=
    finiteDimensional_of_HolomorphicOneFormFiniteDim
      (DiskChartCover.holomorphicOneFormFiniteDim_holds (X := X))
  haveI hSub : Subsingleton (HolomorphicOneForm X) :=
    holomorphicOneForm_subsingleton_of_genus_eq_zero X h_genus
  exact completeHodgeRiemannHypothesis_of_subsingleton data basis_ω cycleGens

end JacobianChallenge

end
