/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusCoveringMap
import Mathlib.Topology.Homotopy.Lifting

set_option linter.unusedSectionVars false

/-! # Continuous path lift through `mkQ : ℂ → ℂ ⧸ L`

Applies `IsCoveringMap.liftPath` from mathlib to our `mkQ_isCoveringMap`
to lift a continuous path on the complex torus to a continuous path on `ℂ`.

For a path `γ : Path (0 : ℂ ⧸ L) q` and a chosen lift `e₀ : ℂ` of the
start point `0` (i.e., `mkQ e₀ = 0`), the lifted continuous path
`Γ : C(I, ℂ)` satisfies `mkQ ∘ Γ = γ` and `Γ 0 = e₀`.

In particular, for a loop `γ : Path 0 0`, the lift `Γ` ends at some
`Γ 1 ∈ ℂ` with `mkQ (Γ 1) = 0`, i.e., `Γ 1 ∈ L`.

## What this file ships

* `ComplexTorus.contLift γ e₀ h_zero` — the continuous lift.
* `ComplexTorus.contLift_zero` — `Γ 0 = e₀`.
* `ComplexTorus.contLift_lifts` — `mkQ ∘ Γ = γ`.
* `ComplexTorus.contLift_endpoint_mem_L` — for a loop `γ` at `0`
  and `e₀ := 0`, the endpoint `Γ 1 ∈ L`.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff Topology

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Continuous lift -/

/-- **Continuous path lift through `mkQ`.** For any continuous path
`γ : Path (q₀ : ℂ ⧸ L) q₁` on the torus, with `e₀ : ℂ` a chosen
preimage of `q₀` (i.e., `mkQ e₀ = q₀`), there is a continuous lift
`Γ : C(I, ℂ)` with `Γ 0 = e₀` and `mkQ ∘ Γ = γ`. -/
noncomputable def contLift {q₀ q₁ : ℂ ⧸ L}
    (γ : Path q₀ q₁) (e₀ : ℂ) (h_zero : γ.toContinuousMap 0 = L.mkQ e₀) :
    C(unitInterval, ℂ) :=
  (mkQ_isCoveringMap L).liftPath γ.toContinuousMap e₀ h_zero

@[simp] lemma contLift_zero {q₀ q₁ : ℂ ⧸ L}
    (γ : Path q₀ q₁) (e₀ : ℂ) (h_zero : γ.toContinuousMap 0 = L.mkQ e₀) :
    contLift L γ e₀ h_zero 0 = e₀ :=
  (mkQ_isCoveringMap L).liftPath_zero γ.toContinuousMap e₀ h_zero

lemma contLift_lifts {q₀ q₁ : ℂ ⧸ L}
    (γ : Path q₀ q₁) (e₀ : ℂ) (h_zero : γ.toContinuousMap 0 = L.mkQ e₀) :
    L.mkQ ∘ contLift L γ e₀ h_zero = γ.toContinuousMap :=
  (mkQ_isCoveringMap L).liftPath_lifts γ.toContinuousMap e₀ h_zero

/-! ## Endpoint of the lift -/

/-- **The lift's endpoint lies in `L`** when γ is a based loop at
`0 : ℂ ⧸ L` and `e₀ := 0`. By `contLift_lifts`, `mkQ (Γ 1) = γ 1 = 0`,
which means `Γ 1 ∈ L`. -/
theorem contLift_endpoint_mem_L (γ : Path (0 : ℂ ⧸ L) 0) :
    contLift L γ 0 (by simp) 1 ∈ L := by
  -- mkQ (Γ 1) = γ 1 = 0.
  have h_lifts : L.mkQ ∘ contLift L γ 0 (by simp) = γ.toContinuousMap :=
    contLift_lifts L γ 0 (by simp)
  have h_end : L.mkQ (contLift L γ 0 (by simp) 1) = γ 1 := by
    have := congrFun h_lifts 1
    exact this
  -- γ 1 = 0 (loop ends at basepoint).
  have h_target : γ 1 = 0 := γ.target
  rw [h_target] at h_end
  -- mkQ x = 0 → x ∈ L (kernel of mkQ).
  exact (Submodule.Quotient.mk_eq_zero L).mp h_end

end ComplexTorus

end JacobianChallenge

end
