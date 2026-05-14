/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LinearSystemDivisor

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Constants embedding `ℂ →ₗ[ℂ] linearSystemDivisor D` for effective divisors

The first dim-bound layer over `linearSystemDivisor`: every constant
`c : ℂ` lifts to the germ `algebraMapC c : MeromorphicFunctionGerm X`,
which is holomorphic everywhere (order `⊤` if `c = 0`, `0` otherwise),
hence lies in `linearSystemDivisor D` whenever `D` is **effective**
(`∀ y, 0 ≤ D(y)`). Packaging this as a `ℂ →ₗ[ℂ]` linear map gives the
canonical map

  `Algebra.linearMap ℂ (MeromorphicFunctionGerm X) : ℂ →ₗ[ℂ] _`

restricted to land in `linearSystemDivisor D`. Composing with mathlib's
`RingHom.injective` (for ring homs out of a field into a `Nontrivial`
target — available under `ConnectedSpace X` via the `Field` instance on
`MeromorphicFunctionGerm X`) gives that the embedding is injective:
distinct complex numbers produce distinct germs.

The injective embedding provides the trivial lower bound `1 ≤ dim_ℂ L(D)`
for effective `D`; the non-trivial Riemann-Roch content (`2 ≤ dim_ℂ
L(δp)` at genus 0) lives downstream and needs an existence input like
`ExistsSimplePoleGermAtSomePoint`.

## Contents

* `IsBoundedByDivisor.const_of_effective` — membership of a constant
  germ in `L(D)` for effective `D`.
* `constantsToLinearSystemDivisor D hD : ℂ →ₗ[ℂ] linearSystemDivisor D` —
  the bundled embedding.
* `constantsToLinearSystemDivisor_apply_coe` — its underlying map is the
  algebra map at `MeromorphicFunctionGerm X`.
* `constantsToLinearSystemDivisor_injective` — injectivity, conditional
  on `ConnectedSpace X` (so that `MeromorphicFunctionGerm X` is a
  non-trivial field).

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace JacobianChallenge.MeromorphicFunctionField

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Order of a constant germ at every point -/

/-- The order of a constant germ at every point: `⊤` if the constant is
zero, `0` otherwise. Proved by reducing through `algebraMapC c = mk
(MMer.const c)` and the chart pullback `(MMer.const c).toFun ∘ chart.symm
= fun _ => c`. -/
lemma orderAt_algebraMapC (c : ℂ) (y : X) :
    MeromorphicFunctionGerm.orderAt y (algebraMapC c)
      = if c = 0 then (⊤ : WithTop ℤ) else (0 : WithTop ℤ) := by
  -- `algebraMapC c = mk (MMer.const c)`.
  show MeromorphicFunctionGerm.orderAt y
        (MeromorphicFunctionGerm.mk (MMer.const c : MMer X)) = _
  rw [MeromorphicFunctionGerm.orderAt_mk]
  -- Chart pullback of `MMer.const c` is `fun _ => c`.
  show meromorphicOrderAt
      ((MMer.const c : MMer X).toFun ∘ (chartAt ℂ y).symm)
      ((chartAt ℂ y) y) = _
  have h_unf :
      ((MMer.const c : MMer X).toFun ∘ (chartAt ℂ y).symm)
        = (fun _ : ℂ => c) := rfl
  rw [h_unf, meromorphicOrderAt_const ((chartAt ℂ y) y) c]

/-- A constant germ is always of order `≥ 0`. -/
lemma orderAt_algebraMapC_nonneg (c : ℂ) (y : X) :
    0 ≤ MeromorphicFunctionGerm.orderAt y (algebraMapC c) := by
  rw [orderAt_algebraMapC]
  by_cases hc : c = 0
  · simp [hc]
  · simp [hc]

/-! ## Constant germs lie in `L(D)` for effective `D` -/

/-- **Constants are in `L(D)` for effective `D`.** Every constant germ
has order `≥ 0` everywhere; if `D ≥ 0` then `-D(y) ≤ 0 ≤ ord_y` for
every `y`. -/
lemma IsBoundedByDivisor.const_of_effective
    {D : JacobianChallenge.Div X} (hD : ∀ y, 0 ≤ D y) (c : ℂ) :
    IsBoundedByDivisor D (algebraMapC c) := by
  intro y
  -- `-D y ≤ 0 ≤ ord_y algebraMapC c`.
  have h_ord : (0 : WithTop ℤ)
        ≤ MeromorphicFunctionGerm.orderAt y (algebraMapC c) :=
    orderAt_algebraMapC_nonneg c y
  -- `-D y ≤ 0` since `D y ≥ 0` (D effective).
  have h_int : (-(D y) : ℤ) ≤ (0 : ℤ) := by
    have := hD y
    omega
  have h_neg : ((-(D y) : ℤ) : WithTop ℤ) ≤ (0 : WithTop ℤ) := by
    have h_cast : ((-(D y) : ℤ) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ) := by
      exact_mod_cast h_int
    simpa using h_cast
  exact h_neg.trans h_ord

/-- `algebraMapC c ∈ linearSystemDivisor D` for effective `D`. -/
lemma algebraMapC_mem_linearSystemDivisor
    {D : JacobianChallenge.Div X} (hD : ∀ y, 0 ≤ D y) (c : ℂ) :
    algebraMapC c ∈ linearSystemDivisor D :=
  IsBoundedByDivisor.const_of_effective hD c

/-! ## The bundled ℂ-linear embedding -/

/-- **The constants embedding `ℂ → L(D)` for effective `D`**, as a
`ℂ →ₗ[ℂ]` linear map.

Built by `codRestrict`ing `Algebra.linearMap ℂ (MeromorphicFunctionGerm
X)` to the subspace `linearSystemDivisor D`, with the membership proof
supplied by `algebraMapC_mem_linearSystemDivisor`. -/
def constantsToLinearSystemDivisor
    (D : JacobianChallenge.Div X) (hD : ∀ y, 0 ≤ D y) :
    ℂ →ₗ[ℂ] linearSystemDivisor D :=
  (Algebra.linearMap ℂ (MeromorphicFunctionGerm X)).codRestrict
    (linearSystemDivisor D) (fun c => algebraMapC_mem_linearSystemDivisor hD c)

/-- The underlying map of `constantsToLinearSystemDivisor`. -/
@[simp] lemma constantsToLinearSystemDivisor_apply_coe
    (D : JacobianChallenge.Div X) (hD : ∀ y, 0 ≤ D y) (c : ℂ) :
    (constantsToLinearSystemDivisor D hD c : MeromorphicFunctionGerm X)
      = algebraMapC c := rfl

end JacobianChallenge.MeromorphicFunctionField

/-! ## Injectivity of the constants embedding

Under `ConnectedSpace X`, `MeromorphicFunctionGerm X` is a `Field` (and in
particular `Nontrivial`). Mathlib's `RingHom.injective` for ring homs out
of a field into a non-trivial target then gives that `algebraMapC : ℂ
→+* MeromorphicFunctionGerm X` is injective. The composition with
`Subtype.val_injective` for the codomain restriction yields injectivity
of `constantsToLinearSystemDivisor`. -/

namespace JacobianChallenge.MeromorphicFunctionField

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- `algebraMapC : ℂ →+* MeromorphicFunctionGerm X` is injective on a
connected complex 1-manifold. -/
lemma algebraMapC_injective :
    Function.Injective (algebraMapC : ℂ →+* MeromorphicFunctionGerm X) :=
  algebraMapC.injective

/-- The constants embedding is injective for effective `D`. -/
lemma constantsToLinearSystemDivisor_injective
    (D : JacobianChallenge.Div X) (hD : ∀ y, 0 ≤ D y) :
    Function.Injective (constantsToLinearSystemDivisor D hD) := by
  intro c₁ c₂ h
  -- Unwrap the Subtype equality on `linearSystemDivisor D`.
  have h_germ : (constantsToLinearSystemDivisor D hD c₁
                  : MeromorphicFunctionGerm X)
                = (constantsToLinearSystemDivisor D hD c₂
                    : MeromorphicFunctionGerm X) :=
    congrArg Subtype.val h
  rw [constantsToLinearSystemDivisor_apply_coe,
      constantsToLinearSystemDivisor_apply_coe] at h_germ
  exact algebraMapC_injective h_germ

end JacobianChallenge.MeromorphicFunctionField

end
