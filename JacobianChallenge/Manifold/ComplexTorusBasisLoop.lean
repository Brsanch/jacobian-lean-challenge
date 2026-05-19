/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorus
import JacobianChallenge.Manifold.SmoothChain
import JacobianChallenge.Manifold.SmoothPathConst

/-! # Torus basis loops on the complex torus `T_L = ℂ ⧸ L`

For a discrete full-rank `ℤ`-lattice `L ≤ ℂ` and a lattice element
`lam ∈ L`, the **torus basis loop** at `0 : ℂ ⧸ L` parameterised by
`lam` is the smooth path

```
γ_lam(t) := L.mkQ ((t : ℂ) * lam) = π((t : ℂ) · lam)
```

for `t ∈ ℝ`. Since `(0 : ℂ) * lam = 0 ∈ L` (so `π(0) = 0`) and
`(1 : ℂ) * lam = lam ∈ L` (so `π(lam) = 0`), this is a based loop at
the zero class.

We use complex multiplication via `Complex.ofReal` rather than the
real-scalar action to keep typeclass resolution simple and to make the
later identification with holomorphic-form periods clean
(holomorphic-form periods are stated in terms of complex scalar
multiplication on the cotangent fibre).

This is the central geometric construction for the complex torus: each
lattice element gives a closed loop on `T_L`, and for any `ℤ`-basis
`(lam₁, lam₂)` of `L` the two loops `γ_{lam₁}, γ_{lam₂}` are the
**symplectic basis** (`a`- and `b`-cycles) generating `H₁(T_L; ℤ) ≅ ℤ²`.

## What this file ships

* `ComplexTorus.torusBasisLoop L lam hlam` — for `lam ∈ L`, the
  `SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)` from `0` to `0` parameterised by `lam`.
* `ComplexTorus.torusBasisLoop_src/_tgt` — endpoint identities.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Smoothness of `t ↦ (t : ℂ) * lam` on `ℂ` -/

/-- The scaling map `ℝ → ℂ`, `t ↦ (t : ℂ) * lam`, is smooth for any
`lam : ℂ`. -/
private lemma contMDiff_ofReal_mul_const (lam : ℂ) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) ∞
      (fun t : ℝ => (t : ℂ) * lam) := by
  have h_ofReal : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((↑) : ℝ → ℂ) :=
    Complex.ofRealCLM.contDiff
  have h_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => (t : ℂ) * lam) :=
    h_ofReal.mul contDiff_const
  exact h_cd.contMDiff

/-- Continuity version of the above. -/
private lemma continuous_ofReal_mul_const (lam : ℂ) :
    Continuous (fun t : ℝ => (t : ℂ) * lam) :=
  Complex.continuous_ofReal.mul continuous_const

/-! ## The torus basis loop -/

variable {L}

/-- **Torus basis loop on `ℂ ⧸ L`.** For a lattice element `lam ∈ L`,
the smooth path `γ_lam : [0,1] → ℂ ⧸ L` defined by
`γ_lam(t) := π((t : ℂ) * lam)`, with both endpoints at the zero class. -/
noncomputable def torusBasisLoop (lam : ℂ) (hlam : lam ∈ L) :
    SmoothPath (𝓘(ℝ, ℂ)) (ℂ ⧸ L) where
  src := 0
  tgt := 0
  toPath := {
    toFun := fun t : unitInterval => L.mkQ ((t.val : ℂ) * lam)
    continuous_toFun := by
      have h_mul := continuous_ofReal_mul_const lam
      have h_mkQ : Continuous (L.mkQ : ℂ → ℂ ⧸ L) :=
        (L.isOpenQuotientMap_mkQ).continuous
      exact (h_mkQ.comp h_mul).comp continuous_subtype_val
    source' := by
      -- t = 0: π((0 : ℂ) * lam) = π(0) = 0.
      change L.mkQ (((0 : unitInterval).val : ℂ) * lam) = 0
      have h0 : (((0 : unitInterval).val : ℝ) : ℂ) = 0 := by
        change ((0 : ℝ) : ℂ) = 0
        exact Complex.ofReal_zero
      rw [h0, zero_mul]
      exact map_zero L.mkQ
    target' := by
      -- t = 1: π((1 : ℂ) * lam) = π(lam) = 0 since lam ∈ L.
      change L.mkQ (((1 : unitInterval).val : ℂ) * lam) = 0
      have h1 : (((1 : unitInterval).val : ℝ) : ℂ) = 1 := by
        change ((1 : ℝ) : ℂ) = 1
        exact Complex.ofReal_one
      rw [h1, one_mul]
      exact (Submodule.Quotient.mk_eq_zero L).mpr hlam
  }
  smooth := by
    refine ⟨fun t : ℝ => L.mkQ ((t : ℂ) * lam), ?_, ?_⟩
    · have h_mul := contMDiff_ofReal_mul_const lam
      have h_mkQ := mkQ_contMDiff_real L ∞
      exact h_mkQ.comp h_mul
    · intro t
      rfl

@[simp] lemma torusBasisLoop_src (lam : ℂ) (hlam : lam ∈ L) :
    (torusBasisLoop lam hlam).src = (0 : ℂ ⧸ L) := rfl

@[simp] lemma torusBasisLoop_tgt (lam : ℂ) (hlam : lam ∈ L) :
    (torusBasisLoop lam hlam).tgt = (0 : ℂ ⧸ L) := rfl

end ComplexTorus

end JacobianChallenge

end
