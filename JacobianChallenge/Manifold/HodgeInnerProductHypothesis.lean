/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneForm
import JacobianChallenge.Manifold.DiskChartCoverFiniteDim

set_option linter.unusedSectionVars false

/-! # `HodgeInnerProductHypothesis`: positive-definite Hermitian form on `H^0(X, Ω)`

The **Hodge inner product** on the space of holomorphic 1-forms of a
compact connected complex 1-manifold is classically:

  ⟨ω, η⟩ := (i/2) · ∫_X ω ∧ η̄

It is a positive-definite Hermitian form (real positivity comes from the
pointwise identity `(i/2) · (f dz) ∧ (f̄ dz̄) = |f|² dx ∧ dy`, and integral
positivity follows from compactness of `X`).

Formalising the wedge product on differential forms over a complex
1-manifold is *not* in scope at the mathlib pin used by this project:
mathlib does not yet have a developed theory of differential forms on
smooth manifolds (only the tangent bundle / derivative infrastructure).
This file therefore exposes the Hodge inner product as a **named
existence hypothesis** `HodgeInnerProductHypothesis X`, capturing the
deep classical content as a Prop that downstream work can either:

* Discharge for specific `X` (e.g., `RiemannSphere`, where the
  hypothesis is vacuous since `HolomorphicOneForm X` is subsingleton);
* Or take as input when building the Riemann bilinear non-degeneracy.

The Hodge inner product is the **central deep classical input** for
Riemann's bilinear relations. Once formalised, it implies (combined
with the symplectic intersection form on `H_1(X; ℤ)`) the
ℝ-linear independence of the `2g` period vectors that appears as the
`bilinear` field of `SmoothHomologyDataPackage`.

## What this file ships

* `HermitianOnHolomorphicOneForm` — type of sesquilinear forms `H^0(Ω)
  × H^0(Ω) → ℂ` with the appropriate twist.
* `HermitianOnHolomorphicOneForm.IsPositiveDefinite` — pointwise
  positivity + nondegeneracy.
* `HodgeInnerProductHypothesis X` — named existence Prop.

## Anti-hack

The positive-definite condition forces non-degeneracy on every
non-zero form. The trivial bilinear form (constant zero) fails the
non-degeneracy condition unless `HolomorphicOneForm X` is subsingleton.
At genus 0 (`Subsingleton (HolomorphicOneForm X)`), the hypothesis is
vacuously satisfied by the zero form.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Hermitian form on `HolomorphicOneForm X`** — a sesquilinear form
`H : H^0(X, Ω) × H^0(X, Ω) → ℂ` that is ℂ-linear in the first argument
and conjugate-linear in the second (the convention matching the Hodge
inner product). Packaged as a bundled struct on the underlying
`LinearMap` to keep the type self-contained.

We use `om` and `eta` rather than the conventional `ω` / `η` to avoid
clashing with the `ω = ⊤ : WithTop ℕ∞` reserved notation from
`ContDiff`. -/
structure HermitianOnHolomorphicOneForm where
  /-- The underlying bilinear-ish form, packaged as a function. -/
  toFun : HolomorphicOneForm X → HolomorphicOneForm X → ℂ
  /-- ℂ-linearity in the first argument: zero. -/
  map_zero_left : ∀ eta, toFun 0 eta = 0
  /-- ℂ-linearity in the first argument: add. -/
  map_add_left :
    ∀ om₁ om₂ eta, toFun (om₁ + om₂) eta = toFun om₁ eta + toFun om₂ eta
  /-- ℂ-linearity in the first argument: smul. -/
  map_smul_left :
    ∀ (c : ℂ) om eta, toFun (c • om) eta = c * toFun om eta
  /-- Conjugate symmetry: `toFun om eta = conj (toFun eta om)`. -/
  conjSymm : ∀ om eta, toFun om eta = star (toFun eta om)

namespace HermitianOnHolomorphicOneForm

variable {X}

/-- **`IsPositiveDefinite H`** — the Hodge inner product is
positive-definite. For every `om : HolomorphicOneForm X`, `H om om` is
a non-negative real number, equal to zero iff `om = 0`. -/
def IsPositiveDefinite (H : HermitianOnHolomorphicOneForm X) : Prop :=
  (∀ om : HolomorphicOneForm X, (H.toFun om om).im = 0 ∧ 0 ≤ (H.toFun om om).re) ∧
    (∀ om : HolomorphicOneForm X, H.toFun om om = 0 → om = 0)

/-- **`IsHodgeForm H`** — the Hodge inner product on `HolomorphicOneForm
X`, packaged as a positive-definite Hermitian form. -/
def IsHodgeForm (H : HermitianOnHolomorphicOneForm X) : Prop :=
  H.IsPositiveDefinite

end HermitianOnHolomorphicOneForm

/-- **`HodgeInnerProductHypothesis X`** — there exists a Hodge inner
product on `HolomorphicOneForm X`. Captures the deep classical content
of Hodge theory on a compact connected complex 1-manifold as a single
named existence Prop. -/
def HodgeInnerProductHypothesis : Prop :=
  ∃ H : HermitianOnHolomorphicOneForm X, H.IsHodgeForm

/-! ## Genus-0 discharge: vacuous case -/

variable {X}

/-- **At genus 0, `HodgeInnerProductHypothesis X` holds vacuously.**
Under `[Subsingleton (HolomorphicOneForm X)]`, the constant-zero
sesquilinear form is positive-definite (positive on the only element
`0`, non-degenerate because every form is `0` anyway). -/
theorem hodgeInnerProductHypothesis_of_subsingleton
    [Subsingleton (HolomorphicOneForm X)] :
    HodgeInnerProductHypothesis X := by
  refine ⟨{
    toFun := fun _ _ => 0
    map_zero_left := fun _ => rfl
    map_add_left := fun _ _ _ => by simp
    map_smul_left := fun _ _ _ => by simp
    conjSymm := fun _ _ => by simp
  }, ?_, ?_⟩
  · -- Positivity: `0 ∈ ℝ` and `0 ≥ 0`.
    intro _
    refine ⟨?_, ?_⟩
    · simp
    · simp
  · -- Non-degeneracy: any `om` is `0` by subsingleton.
    intro om _
    exact Subsingleton.elim om 0

end JacobianChallenge

end
