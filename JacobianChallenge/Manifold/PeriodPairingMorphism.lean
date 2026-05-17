/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodPairingDefinition
import JacobianChallenge.Manifold.PeriodLatticeFromPairing
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackGeneral
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackMatrix

set_option linter.unusedSectionVars false

/-! # Period-pairing morphisms induced by curve maps

For a smooth curve map `f : X → Y` between compact connected complex
1-manifolds, the **period-pairing adjunction**

  `∫_{f_*γ} τ = ∫_γ (f^* τ)`     for `γ ∈ H₁(X;ℤ)`, `τ ∈ HolomorphicOneForm Y`

induces, given `PeriodPairingData X` and `PeriodPairingData Y`, a
**morphism of period-pairings**: an `AddMonoidHom` from `data_X.H1`
to `data_Y.H1` (the cycle pushforward) that satisfies the adjunction.

This file packages that morphism as a **named-hypothesis bundle**.
Downstream callers supply a concrete `f`, the cycle pushforward, and
the adjunction certificate; we derive:

* **Lattice match for `pushforwardLinearLift`** — periodLatticeImage of
  X is carried by `pushforwardLinearLift αX αY f hf` into
  periodLatticeImage of Y.

* Companion lemmas tying the period morphism's existence to the
  `JacobianAnalyticPushforwardLift.ofCurveMap` constructor.

## Why this is a named hypothesis

The cycle pushforward `f_* : H₁(X;ℤ) → H₁(Y;ℤ)` is a classical
construction: send a loop `γ : S¹ → X` to `f ∘ γ : S¹ → Y`. The
adjunction `∫_{f_*γ} τ = ∫_γ f^* τ` is a standard change-of-variables
argument for line integrals.

Neither of these is in mathlib at the pin for arbitrary smooth maps
between abstract complex manifolds. We surface them as a single bundle
rather than fabricate.
-/

open scoped ContDiff Manifold
open Submodule Module

noncomputable section

namespace JacobianChallenge

universe v

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-- **Period-pairing morphism induced by a curve map.**

A bundle carrying the data and the adjunction:

* `f : X → Y` (the curve map);
* `contMDiff_f : ContMDiff ω f` (smoothness);
* `cyclePush : data_X.H1 →+ data_Y.H1` (cycle pushforward);
* `adjunction γ τ : data_Y.pairing (cyclePush γ) τ
                   = data_X.pairing γ (HolomorphicOneForm.pullback f contMDiff_f τ)`
  (the classical adjunction `∫_{f_*γ} τ = ∫_γ f^* τ`).
-/
structure PeriodPairingMorphism
    (data_X : PeriodPairingData X)
    (data_Y : PeriodPairingData Y) where
  /-- The underlying curve map. -/
  f : X → Y
  /-- Holomorphicity of `f`. -/
  contMDiff_f : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f
  /-- The cycle pushforward `f_* : H₁(X;ℤ) → H₁(Y;ℤ)`. -/
  cyclePush : data_X.H1 →+ data_Y.H1
  /-- The period-pairing adjunction. -/
  adjunction :
    ∀ (γ : data_X.H1) (τ : HolomorphicOneForm Y),
      data_Y.pairing (cyclePush γ) τ
        = data_X.pairing γ (HolomorphicOneForm.pullback f contMDiff_f τ)

namespace PeriodPairingMorphism

variable {data_X : PeriodPairingData X} {data_Y : PeriodPairingData Y}

/-- The image of `periodVector data_X αX γ` under the pushforward lift
equals the period vector of `cyclePush γ` against `αY`.

This is the **period-transform identity** that underwrites the lattice
match. Stated in coordinates:
  `pushforwardLinearLift αX αY f hf (periodVector γ αX) j
   = periodVector (cyclePush γ) αY j`. -/
theorem pushforwardLinearLift_periodVector
    (morph : PeriodPairingMorphism data_X data_Y)
    (αX : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (αY : Basis (Fin (JacobianChallenge.genus Y)) ℂ (HolomorphicOneForm Y))
    (γ : data_X.H1) (j : Fin (JacobianChallenge.genus Y)) :
    HolomorphicOneForm.pushforwardLinearLift αX αY morph.f morph.contMDiff_f
        (periodVector data_X αX γ) j
      = periodVector data_Y αY (morph.cyclePush γ) j := by
  -- LHS: ∑ i, M_{i,j} * periodVector_i(γ)
  --    = ∑ i, αX.repr (pullback f hf (αY j)) i * data_X.pairing γ (αX i)
  --    = data_X.pairing γ (∑ i, (αX.repr (pullback f hf (αY j)) i) • αX i)
  --      [by ℂ-linearity of pairing γ]
  --    = data_X.pairing γ (pullback f hf (αY j))
  --      [by Basis.sum_repr]
  -- RHS: periodVector data_Y αY (cyclePush γ) j
  --    = data_Y.pairing (cyclePush γ) (αY j)
  --    = data_X.pairing γ (pullback f hf (αY j))   [by adjunction].
  -- Hence LHS = RHS.
  rw [HolomorphicOneForm.pushforwardLinearLift_apply]
  -- ∑ i, M_{i,j} * v_i with v := periodVector data_X αX γ.
  show ∑ i, HolomorphicOneForm.pullbackMatrix αX αY morph.f morph.contMDiff_f i j
      * periodVector data_X αX γ i = _
  -- periodVector data_X αX γ i = data_X.pairing γ (αX i).
  simp_rw [show ∀ i, periodVector data_X αX γ i = data_X.pairing γ (αX i)
            from fun i => rfl]
  -- Now: ∑ i, M_{i,j} * data_X.pairing γ (αX i).
  --    = data_X.pairing γ (∑ i, M_{i,j} • αX i)   [linearity]
  --    = data_X.pairing γ (pullback f hf (αY j))   [pullbackMatrix_spec].
  have h_pull_sum : HolomorphicOneForm.pullbackLinearMap morph.f morph.contMDiff_f (αY j)
      = ∑ i, HolomorphicOneForm.pullbackMatrix αX αY morph.f morph.contMDiff_f i j • αX i :=
    HolomorphicOneForm.pullbackMatrix_spec αX αY morph.f morph.contMDiff_f j
  -- data_X.pairing γ : HolomorphicOneForm X →ₗ[ℂ] ℂ is ℂ-linear.
  -- Apply it to the sum.
  have h_lhs : ∑ i, HolomorphicOneForm.pullbackMatrix αX αY morph.f morph.contMDiff_f i j
        * data_X.pairing γ (αX i)
      = data_X.pairing γ (HolomorphicOneForm.pullbackLinearMap morph.f morph.contMDiff_f
          (αY j)) := by
    rw [h_pull_sum]
    rw [map_sum]
    simp_rw [map_smul, smul_eq_mul]
  rw [h_lhs]
  -- pullbackLinearMap _ _ (αY j) = pullback f hf (αY j) by defn.
  rw [HolomorphicOneForm.pullbackLinearMap_apply]
  -- RHS: periodVector data_Y αY (cyclePush γ) j = data_Y.pairing (cyclePush γ) (αY j).
  show data_X.pairing γ (HolomorphicOneForm.pullback morph.f morph.contMDiff_f (αY j))
    = data_Y.pairing (morph.cyclePush γ) (αY j)
  -- By the adjunction.
  exact (morph.adjunction γ (αY j)).symm

/-- **Lattice match for the canonical pushforward lift.** Given a
period-pairing morphism, the canonical `pushforwardLinearLift` carries
`periodLatticeImage data_X αX` into `periodLatticeImage data_Y αY`. -/
theorem lattice_match
    (morph : PeriodPairingMorphism data_X data_Y)
    (αX : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (αY : Basis (Fin (JacobianChallenge.genus Y)) ℂ (HolomorphicOneForm Y))
    (v : Fin (JacobianChallenge.genus X) → ℂ)
    (hv : v ∈ periodLatticeImage data_X αX) :
    HolomorphicOneForm.pushforwardLinearLift αX αY morph.f morph.contMDiff_f v
      ∈ periodLatticeImage data_Y αY := by
  obtain ⟨γ, hγ⟩ := (mem_periodLatticeImage_iff data_X αX v).mp hv
  refine (mem_periodLatticeImage_iff data_Y αY _).mpr ⟨morph.cyclePush γ, ?_⟩
  -- Vector equality: components.
  funext j
  rw [show periodVector data_Y αY (morph.cyclePush γ) j
        = HolomorphicOneForm.pushforwardLinearLift αX αY morph.f morph.contMDiff_f
            (periodVector data_X αX γ) j from
      (pushforwardLinearLift_periodVector morph αX αY γ j).symm]
  rw [hγ]

end PeriodPairingMorphism

end JacobianChallenge

end
