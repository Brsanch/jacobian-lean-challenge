/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusCoveringMap
import JacobianChallenge.Manifold.Smooth2Simplex
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

set_option linter.unusedSectionVars false

/-! # Global continuous lift of a smooth 2-simplex `σ` on `T_L = ℂ ⧸ L`

The domain `(Fin 2 → ℝ)` of a `Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)` is a
real topological vector space, hence (a) contractible, (b)
locally path-connected, and (c) simply connected. By mathlib's
`IsCoveringMap.existsUnique_continuousMap_lifts`, the smooth (hence
continuous) map `σ.toFun : (Fin 2 → ℝ) → ℂ ⧸ L` admits a unique
continuous lift through `mkQ : ℂ → ℂ ⧸ L` starting from any chosen
preimage of `σ.toFun v₀`.

We package this lift as

```
ComplexTorus.globalSimplexContLift σ : C((Fin 2 → ℝ), ℂ)
```

with the chosen base value `(σ.toFun Smooth2Simplex.v0).out`. It
satisfies

* `L.mkQ ∘ globalSimplexContLift σ = σ.toFun` (lift identity).
* `globalSimplexContLift σ Smooth2Simplex.v0 = (σ.toFun v0).out`.

Smoothness of the lift is established in a follow-up chip.

## What this file ships

* `ComplexTorus.globalSimplexContLift` — the continuous global lift.
* `ComplexTorus.globalSimplexContLift_lifts` — the lift identity.
* `ComplexTorus.globalSimplexContLift_at_v0` — value at `v0`.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff Topology

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Existence + uniqueness of continuous lift -/

/-- **The unique continuous global lift of `σ.toFun` starting at the
chosen preimage `(σ.toFun v0).out`.**

Defined via `IsCoveringMap.existsUnique_continuousMap_lifts` on the
simply-connected, locally path-connected domain `(Fin 2 → ℝ)`. -/
noncomputable def globalSimplexContLift
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    C((Fin 2 → ℝ), ℂ) := by
  -- Bundle `σ.toFun` as a `ContinuousMap`.
  let f : C((Fin 2 → ℝ), ℂ ⧸ L) := ⟨σ.toFun, σ.smooth.continuous⟩
  -- Chosen lift of `σ.toFun v0`.
  let e₀ : ℂ := (σ.toFun Smooth2Simplex.v0).out
  -- Verify `mkQ e₀ = σ.toFun v0`.
  have he : (L.mkQ : ℂ → ℂ ⧸ L) e₀ = f Smooth2Simplex.v0 := by
    show L.mkQ (σ.toFun Smooth2Simplex.v0).out = σ.toFun Smooth2Simplex.v0
    exact Quotient.out_eq _
  -- Existence + uniqueness via the simply-connected lifting theorem.
  exact ((mkQ_isCoveringMap L).existsUnique_continuousMap_lifts
    f Smooth2Simplex.v0 e₀ he).exists.choose

/-! ## Properties of the global continuous lift -/

private lemma globalSimplexContLift_spec
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    (globalSimplexContLift L σ) Smooth2Simplex.v0
        = (σ.toFun Smooth2Simplex.v0).out ∧
      (L.mkQ : ℂ → ℂ ⧸ L) ∘ globalSimplexContLift L σ
        = (⟨σ.toFun, σ.smooth.continuous⟩ : C((Fin 2 → ℝ), ℂ ⧸ L)) := by
  -- Unfold definition.
  unfold globalSimplexContLift
  let f : C((Fin 2 → ℝ), ℂ ⧸ L) := ⟨σ.toFun, σ.smooth.continuous⟩
  let e₀ : ℂ := (σ.toFun Smooth2Simplex.v0).out
  have he : (L.mkQ : ℂ → ℂ ⧸ L) e₀ = f Smooth2Simplex.v0 := by
    show L.mkQ (σ.toFun Smooth2Simplex.v0).out = σ.toFun Smooth2Simplex.v0
    exact Quotient.out_eq _
  exact ((mkQ_isCoveringMap L).existsUnique_continuousMap_lifts
    f Smooth2Simplex.v0 e₀ he).exists.choose_spec

/-- **The global continuous lift takes the chosen value at `v0`.** -/
theorem globalSimplexContLift_at_v0
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    (globalSimplexContLift L σ) Smooth2Simplex.v0
      = (σ.toFun Smooth2Simplex.v0).out :=
  (globalSimplexContLift_spec L σ).1

/-- **`mkQ ∘ globalSimplexContLift σ = σ.toFun` pointwise.** -/
theorem globalSimplexContLift_lifts
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L))
    (p : Fin 2 → ℝ) :
    L.mkQ (globalSimplexContLift L σ p) = σ.toFun p := by
  have h := (globalSimplexContLift_spec L σ).2
  -- h : L.mkQ ∘ globalSimplexContLift L σ = (⟨σ.toFun, _⟩ : C(_, _)).
  -- The RHS as a function is σ.toFun.
  have hp := congrFun h p
  -- hp : L.mkQ (globalSimplexContLift L σ p) = σ.toFun p
  exact hp

/-- **`mkQ ∘ globalSimplexContLift σ = σ.toFun` as functions.** -/
theorem globalSimplexContLift_lifts_funext
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    (L.mkQ : ℂ → ℂ ⧸ L) ∘ (globalSimplexContLift L σ) = σ.toFun := by
  funext p
  exact globalSimplexContLift_lifts L σ p

/-! ## Continuity (inherited from `ContinuousMap`) -/

/-- **Continuity of the global lift.** Direct from the `ContinuousMap`
structure. -/
theorem globalSimplexContLift_continuous
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    Continuous (globalSimplexContLift L σ) :=
  (globalSimplexContLift L σ).continuous

end ComplexTorus

end JacobianChallenge

end
