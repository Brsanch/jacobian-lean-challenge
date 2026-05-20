/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothHomologyDataPackageClass
import JacobianChallenge.Manifold.BasedSmoothLoopsBound
import JacobianChallenge.Manifold.DiskChartCoverFiniteDim

set_option linter.unusedSectionVars false

/-! # `SmoothHomologyDataPackage` discharge under `Subsingleton ω`

When `HolomorphicOneForm X` is subsingleton on a compact connected
complex 1-manifold `X`, the genus is `0` (by
`Module.finrank_zero_of_subsingleton`), making every period-lattice
atom vacuous on the `Fin (2 * genus X) = Fin 0` index. This file
ships:

* `smoothHomologyDataPackage_of_subsingleton_holomorphic_one_form` —
  concrete unconditional inhabitant on Subsingleton-ω X (after picking
  a base point + an additional weaker named hypothesis to obtain a
  BasedSmoothLoopsBoundHypothesis discharge).
* Actually NO — even simpler than the above: at Subsingleton ω, the
  symplecticBasis is empty AND the Hurewicz hypothesis on the empty
  basis reduces to the *unconditional* statement `single γ - 0 ∈
  stokesBoundaries` for every loop γ ∈ X. Without a discharge of
  this, the package is NOT unconditional on Subsingleton-ω X. We
  surface that the only remaining content is exactly
  `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀` at the chosen
  base point.

## What this file ships

* `smoothHomologyDataPackage_of_subsingleton_and_BSLB` — concrete
  `SmoothHomologyDataPackage basis_ω` on any compact connected complex
  1-manifold with `Subsingleton (HolomorphicOneForm X)` +
  `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀`.
* `nonempty_smoothHomologyDataPackage_of_subsingleton_and_BSLB` —
  `Nonempty` form.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Module Submodule

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`SmoothHomologyDataPackage basis_ω` from `Subsingleton ω` +
`BasedSmoothLoopsBoundHypothesis` at a chosen base point.**

Under `[Subsingleton (HolomorphicOneForm X)]`, the genus is `0` (via
`Module.finrank_zero_of_subsingleton`), so the symplectic-basis tuple
is empty (`Fin (2 * 0) = Fin 0`), and:

* `bilinear` is vacuously satisfied (`linearIndependent_empty_type`).
* `hurewicz` collapses to: every smooth based loop at `basePoint` is
  in `stokesBoundaries` — which is precisely
  `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X basePoint`. -/
noncomputable def smoothHomologyDataPackage_of_subsingleton_and_BSLB
    [Subsingleton (HolomorphicOneForm X)]
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (basePoint : X)
    (h_BSLB : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X basePoint) :
    SmoothHomologyDataPackage basis_ω := by
  -- `Subsingleton (HolomorphicOneForm X)` + finite-dim ⇒ finrank = 0,
  -- hence `Fin (2 * genus X) = Fin 0` is empty.
  haveI : FiniteDimensional ℂ (HolomorphicOneForm X) :=
    DiskChartCover.holomorphicOneFormFiniteDim_holds (X := X)
  have hrank_zero : Module.finrank ℂ (HolomorphicOneForm X) = 0 :=
    Module.finrank_zero_of_subsingleton
  haveI hempty : IsEmpty (Fin (2 * JacobianChallenge.genus X)) := by
    show IsEmpty (Fin (2 * Module.finrank ℂ (HolomorphicOneForm X)))
    rw [hrank_zero, Nat.mul_zero]
    infer_instance
  refine
    { basePoint := basePoint
      symplecticBasis :=
        { basis := hempty.elim
          basis_src := hempty.elim
          basis_tgt := hempty.elim }
      hurewicz := ?_
      bilinear := linearIndependent_empty_type }
  -- The Hurewicz hypothesis on the empty basis: every smooth based
  -- loop has its `single` cycle in `stokesBoundaries`. The empty sum
  -- is zero, and the remaining content is `BasedSmoothLoopsBoundHypothesis`.
  intro γ h_src h_tgt
  refine ⟨hempty.elim, ?_⟩
  have h_sum_zero :
      (∑ i : Fin (2 * JacobianChallenge.genus X),
        (hempty.elim i : ℤ) •
          ({ basis := hempty.elim, basis_src := hempty.elim,
              basis_tgt := hempty.elim } :
            SmoothSymplecticBasis 𝓘(ℝ, ℂ) X basePoint
              (JacobianChallenge.genus X)).cycleGens i)
        = (0 : SmoothCycle 𝓘(ℝ, ℂ) X) :=
    Finset.sum_of_isEmpty _
  rw [h_sum_zero, sub_zero]
  exact h_BSLB γ h_src h_tgt

/-- **Nonempty form: `Nonempty (SmoothHomologyDataPackage basis_ω)`
under `Subsingleton ω` + `BasedSmoothLoopsBoundHypothesis`.** -/
theorem nonempty_smoothHomologyDataPackage_of_subsingleton_and_BSLB
    [Subsingleton (HolomorphicOneForm X)]
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (basePoint : X)
    (h_BSLB : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X basePoint) :
    Nonempty (SmoothHomologyDataPackage basis_ω) :=
  ⟨smoothHomologyDataPackage_of_subsingleton_and_BSLB
    basis_ω basePoint h_BSLB⟩

end JacobianChallenge

end
