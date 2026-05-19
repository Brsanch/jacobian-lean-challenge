/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusBasisLoop

/-! # Smooth path-connectedness data for the complex torus `ℂ ⧸ L`

For every `x : ℂ ⧸ L`, we pick a representative `x.out : ℂ` and
construct the smooth path `t ↦ π((t : ℂ) * x.out)` from `0` to `x`.
Bundled into a family `α : (ℂ ⧸ L) → SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)` with
`(α x).src = 0` and `(α x).tgt = x` for every `x`.

This discharges the smooth-path-connectedness ingredient
`(α, h_α_src, h_α_tgt)` of `GenericGenusPeriodLatticeInputs.ofBasedLoopHomology`
unconditionally on the torus, using only the
`ChartedSpace ℂ (ℂ ⧸ L)` + `IsManifold` infrastructure already in tree
plus `Submodule.Quotient.out_eq`.

## What this file ships

* `ComplexTorus.α L x` — for `x : ℂ ⧸ L`, the smooth path from `0`
  to `x` via the chosen representative.
* `ComplexTorus.α_src`, `α_tgt` — endpoint identities.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## The path family -/

/-- **Smooth path from `0` to `x`** on `ℂ ⧸ L` via the projection of the
straight line from `0` to a chosen representative of `x`.

`α L x` parameterises `t ↦ π((t : ℂ) * x.out)` for `t ∈ [0, 1]`, where
`x.out : ℂ` is a Choice-chosen representative of `x`. Note `π((0 : ℂ)
* x.out) = π(0) = 0` and `π((1 : ℂ) * x.out) = π(x.out) = x` (by
`Submodule.Quotient.mk_out`). -/
noncomputable def α (x : ℂ ⧸ L) : SmoothPath (𝓘(ℝ, ℂ)) (ℂ ⧸ L) where
  src := 0
  tgt := x
  toPath := {
    toFun := fun t : unitInterval => L.mkQ ((t.val : ℂ) * x.out)
    continuous_toFun := by
      have h_mul : Continuous (fun t : ℝ => (t : ℂ) * (x.out : ℂ)) :=
        Complex.continuous_ofReal.mul continuous_const
      have h_mkQ : Continuous (L.mkQ : ℂ → ℂ ⧸ L) :=
        (L.isOpenQuotientMap_mkQ).continuous
      exact (h_mkQ.comp h_mul).comp continuous_subtype_val
    source' := by
      change L.mkQ (((0 : unitInterval).val : ℂ) * x.out) = 0
      have h0 : (((0 : unitInterval).val : ℝ) : ℂ) = 0 := by
        change ((0 : ℝ) : ℂ) = 0
        exact Complex.ofReal_zero
      rw [h0, zero_mul]
      exact map_zero L.mkQ
    target' := by
      change L.mkQ (((1 : unitInterval).val : ℂ) * x.out) = x
      have h1 : (((1 : unitInterval).val : ℝ) : ℂ) = 1 := by
        change ((1 : ℝ) : ℂ) = 1
        exact Complex.ofReal_one
      rw [h1, one_mul]
      -- `L.mkQ x.out = x` via Quotient.out_eq.
      change (Quotient.mk'' (Quotient.out x) : ℂ ⧸ L) = x
      exact Quotient.out_eq x
  }
  smooth := by
    refine ⟨fun t : ℝ => L.mkQ ((t : ℂ) * x.out), ?_, ?_⟩
    · have h_ofReal : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((↑) : ℝ → ℂ) :=
        Complex.ofRealCLM.contDiff
      have h_mul : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) ∞
          (fun t : ℝ => (t : ℂ) * x.out) :=
        (h_ofReal.mul contDiff_const).contMDiff
      have h_mkQ := mkQ_contMDiff_real L ∞
      exact h_mkQ.comp h_mul
    · intro t
      rfl

@[simp] lemma α_src (x : ℂ ⧸ L) : (α L x).src = (0 : ℂ ⧸ L) := rfl

@[simp] lemma α_tgt (x : ℂ ⧸ L) : (α L x).tgt = x := rfl

end ComplexTorus

end JacobianChallenge

end
