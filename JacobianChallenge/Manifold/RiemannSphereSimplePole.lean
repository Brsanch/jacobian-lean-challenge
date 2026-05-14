/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphere
import JacobianChallenge.Topology.LinearSystemGermDeltaP
import JacobianChallenge.Topology.RRStrictLtFromSimplePole

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # A simple-pole germ on the Riemann sphere

This file constructs an explicit germ in
`MeromorphicFunctionGerm RiemannSphere` with a **simple pole at `∞`**
and holomorphic elsewhere. As a direct consequence,
`ExistsSimplePoleGermAtSomePoint RiemannSphere` is **unconditional**.

## Construction

`RSSimplePole : RiemannSphere → ℂ` is the function
`some z ↦ z`, `∞ ↦ 0` (the value at `∞` is a junk value — it does not
affect the germ).

* In a chart at any finite point `some z₀`, the canonical chart is
  `RiemannSphere.chartN` and the chart pullback `RSSimplePole ∘ RiemannSphere.chartN.symm` is the
  identity `id : ℂ → ℂ`. So the order at `some z₀` is `0` (the value
  `z₀` is nonzero unless `z₀ = 0`, in which case order is `1` — finite
  and `≥ 0` either way).

* In a chart at `∞`, the canonical chart is `RiemannSphere.chartS` and the chart
  pullback agrees with `w ↦ w⁻¹` on a punctured neighborhood of `0`
  (`RiemannSphere.chartS.symm w = some w⁻¹` for `w ≠ 0`). The order at `0` of `inv`
  on `ℂ` is `-1` (a simple pole at the origin), so the manifold-level
  order at `∞` is `-1`.

The germ membership in `linearSystemGermDeltaP ∞` follows since the
order is `≥ 0` everywhere off `∞` and `≥ -1` at `∞`.

## Significance

This is the **base case** for the genus-0 Riemann-Roch existence side:
on the Riemann sphere itself, the simple-pole-germ existence
`ExistsSimplePoleGermAtSomePoint RiemannSphere` is unconditional. The
general statement for a compact connected complex 1-manifold `X` then
reduces (via uniformization at genus 0) to a `HolomorphicEquiv X
RiemannSphere`, which transports the construction. That transport is a
separate (substantially harder) chip; this file does the base case.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set OnePoint

namespace JacobianChallenge

/-! ## The simple-pole function `RSSimplePole : RiemannSphere → ℂ` -/

/-- The Riemann-sphere function `some z ↦ z`, `∞ ↦ 0`. Holomorphic at
every finite point, with a simple pole at `∞`. -/
noncomputable def RSSimplePole : RiemannSphere → ℂ :=
  fun x => OnePoint.rec 0 id x

@[simp] lemma RSSimplePole_infty : RSSimplePole (∞ : RiemannSphere) = 0 := rfl

@[simp] lemma RSSimplePole_coe (z : ℂ) :
    RSSimplePole ((z : RiemannSphere)) = z := rfl

/-! ## Chart-pullback computations -/

/-- The chart pullback `RSSimplePole ∘ chartN.symm` is the identity on
all of `chartN.target = Set.univ`. -/
lemma RSSimplePole_comp_chartN_symm :
    RSSimplePole ∘ RiemannSphere.chartN.symm = (id : ℂ → ℂ) := by
  funext w
  show RSSimplePole (RiemannSphere.chartN.symm w) = w
  rw [RiemannSphere.chartN_symm_apply]
  rfl

/-- The chart pullback `RSSimplePole ∘ chartS.symm` equals `w ↦ w⁻¹`
on all of `ℂ`. The two functions differ only at `w = 0`, where the LHS
is `RSSimplePole ∞ = 0` and the RHS is `0⁻¹ = 0` — they agree at every
`w` (this is the mathematical reason the pointwise value at `∞`
doesn't matter). -/
lemma RSSimplePole_comp_chartS_symm_eq :
    RSSimplePole ∘ RiemannSphere.chartS.symm = (fun w : ℂ => w⁻¹) := by
  funext w
  show RSSimplePole (RiemannSphere.chartS.symm w) = w⁻¹
  by_cases hw : w = 0
  · subst hw
    rw [RiemannSphere.chartS_symm_apply_zero, RSSimplePole_infty, inv_zero]
  · rw [RiemannSphere.chartS_symm_apply_of_ne hw, RSSimplePole_coe]

/-! ## `RSSimplePole` is meromorphic everywhere -/

/-- `RSSimplePole` is `MMeromorphicAt` at every finite point `some z`. -/
lemma RSSimplePole_mmeromorphicAt_coe (z : ℂ) :
    MMeromorphicAt 𝓘(ℂ, ℂ) RSSimplePole ((z : RiemannSphere)) := by
  -- The canonical chart at `some z` is `RiemannSphere.chartN`.
  show MeromorphicAt
      (RSSimplePole ∘ (chartAt ℂ ((z : RiemannSphere))).symm)
      ((chartAt ℂ ((z : RiemannSphere))) ((z : RiemannSphere)))
  -- `chartAt ℂ (some z) = RiemannSphere.chartN`.
  have h_chart : (chartAt ℂ ((z : RiemannSphere)) : OpenPartialHomeomorph RiemannSphere ℂ)
        = RiemannSphere.chartN := rfl
  rw [h_chart]
  -- `RSSimplePole ∘ RiemannSphere.chartN.symm = id`.
  rw [RSSimplePole_comp_chartN_symm]
  -- `RiemannSphere.chartN (some z) = z`.
  rw [RiemannSphere.chartN_apply_coe]
  -- `MeromorphicAt id z` follows from analyticity of `id`.
  exact (analyticAt_id (𝕜 := ℂ) (z := z)).meromorphicAt

/-- `RSSimplePole` is `MMeromorphicAt` at `∞`. -/
lemma RSSimplePole_mmeromorphicAt_infty :
    MMeromorphicAt 𝓘(ℂ, ℂ) RSSimplePole (∞ : RiemannSphere) := by
  -- The canonical chart at `∞` is `RiemannSphere.chartS`.
  show MeromorphicAt
      (RSSimplePole ∘ (chartAt ℂ (∞ : RiemannSphere)).symm)
      ((chartAt ℂ (∞ : RiemannSphere)) ∞)
  have h_chart : (chartAt ℂ (∞ : RiemannSphere) : OpenPartialHomeomorph RiemannSphere ℂ)
        = RiemannSphere.chartS := rfl
  rw [h_chart]
  -- `RSSimplePole ∘ RiemannSphere.chartS.symm = (w ↦ w⁻¹)`.
  rw [RSSimplePole_comp_chartS_symm_eq]
  -- `RiemannSphere.chartS ∞ = 0`.
  rw [RiemannSphere.chartS_apply_infty]
  -- `MeromorphicAt inv 0`.
  exact (analyticAt_id (𝕜 := ℂ) (z := (0 : ℂ))).meromorphicAt.inv

/-- `RSSimplePole` is `MMeromorphicOn` on `Set.univ`. -/
lemma RSSimplePole_mmeromorphicOn :
    MMeromorphicOn 𝓘(ℂ, ℂ) RSSimplePole Set.univ := by
  intro x _
  induction x using OnePoint.rec with
  | infty => exact RSSimplePole_mmeromorphicAt_infty
  | coe z => exact RSSimplePole_mmeromorphicAt_coe z

/-! ## Order computations -/

/-- `mmeromorphicOrderAt 𝓘(ℂ,ℂ) RSSimplePole ∞ = -1`: simple pole at `∞`. -/
lemma RSSimplePole_orderAt_infty :
    mmeromorphicOrderAt 𝓘(ℂ, ℂ) RSSimplePole (∞ : RiemannSphere)
      = ((-1 : ℤ) : WithTop ℤ) := by
  show meromorphicOrderAt (RSSimplePole ∘ (chartAt ℂ (∞ : RiemannSphere)).symm)
      ((chartAt ℂ (∞ : RiemannSphere)) ∞) = _
  have h_chart : (chartAt ℂ (∞ : RiemannSphere) : OpenPartialHomeomorph RiemannSphere ℂ)
        = RiemannSphere.chartS := rfl
  rw [h_chart, RSSimplePole_comp_chartS_symm_eq, RiemannSphere.chartS_apply_infty]
  -- `meromorphicOrderAt (fun w => w⁻¹) 0 = -1`.
  -- `(fun w => w⁻¹) = (id : ℂ → ℂ)⁻¹` definitionally (Pi.inv).
  have h_inv_eq : (fun w : ℂ => w⁻¹) = ((id : ℂ → ℂ))⁻¹ := by
    funext w; rfl
  rw [h_inv_eq, meromorphicOrderAt_inv, meromorphicOrderAt_id]
  rfl

/-- `mmeromorphicOrderAt 𝓘(ℂ,ℂ) RSSimplePole (some z₀) ≥ 0`: holomorphic
at finite points. -/
lemma RSSimplePole_orderAt_coe_nonneg (z₀ : ℂ) :
    0 ≤ mmeromorphicOrderAt 𝓘(ℂ, ℂ) RSSimplePole ((z₀ : RiemannSphere)) := by
  show 0 ≤ meromorphicOrderAt
      (RSSimplePole ∘ (chartAt ℂ ((z₀ : RiemannSphere))).symm)
      ((chartAt ℂ ((z₀ : RiemannSphere))) ((z₀ : RiemannSphere)))
  have h_chart : (chartAt ℂ ((z₀ : RiemannSphere)) : OpenPartialHomeomorph RiemannSphere ℂ)
        = RiemannSphere.chartN := rfl
  rw [h_chart, RSSimplePole_comp_chartN_symm, RiemannSphere.chartN_apply_coe]
  -- `meromorphicOrderAt id z₀ ≥ 0` since `id` is analytic at `z₀`.
  exact (analyticAt_id (𝕜 := ℂ) (z := z₀)).meromorphicOrderAt_nonneg

end JacobianChallenge

/-! ## Packaging as `MMer RiemannSphere` and `MeromorphicFunctionGerm` -/

namespace JacobianChallenge.MeromorphicFunctionField

open JacobianChallenge

/-- The bundled `MMer RiemannSphere` for the simple-pole function. -/
noncomputable def RSSimplePoleMMer : MMer RiemannSphere where
  toFun := RSSimplePole
  mmero := RSSimplePole_mmeromorphicOn

@[simp] lemma RSSimplePoleMMer_toFun :
    (RSSimplePoleMMer : MMer RiemannSphere).toFun = RSSimplePole := rfl

/-- The germ in `MeromorphicFunctionGerm RiemannSphere` of the
simple-pole function. -/
noncomputable def RSSimplePoleGerm : MeromorphicFunctionGerm RiemannSphere :=
  MeromorphicFunctionGerm.mk RSSimplePoleMMer

/-- The germ has order `-1` at `∞`. -/
lemma RSSimplePoleGerm_orderAt_infty :
    RSSimplePoleGerm.orderAt (∞ : RiemannSphere)
      = ((-1 : ℤ) : WithTop ℤ) :=
  RSSimplePole_orderAt_infty

/-- The germ has order `≥ 0` at every finite point. -/
lemma RSSimplePoleGerm_orderAt_coe_nonneg (z₀ : ℂ) :
    0 ≤ RSSimplePoleGerm.orderAt ((z₀ : RiemannSphere)) :=
  RSSimplePole_orderAt_coe_nonneg z₀

/-- **The germ sits in `linearSystemGermDeltaP ∞`**: holomorphic off
`∞`, simple pole at `∞`. -/
theorem RSSimplePoleGerm_mem_linearSystemGermDeltaP_infty :
    RSSimplePoleGerm ∈ linearSystemGermDeltaP (∞ : RiemannSphere) := by
  rw [mem_linearSystemGermDeltaP]
  refine ⟨?_, ?_⟩
  · -- Order at `∞` ≥ -1.
    rw [RSSimplePoleGerm_orderAt_infty]
  · -- Order off `∞` ≥ 0.
    intro y hy_ne_infty
    induction y using OnePoint.rec with
    | infty => exact absurd rfl hy_ne_infty
    | coe z₀ => exact RSSimplePoleGerm_orderAt_coe_nonneg z₀

/-- **`ExistsSimplePoleGermAtSomePoint RiemannSphere`**: the existence
of a simple-pole germ on the Riemann sphere is unconditional. -/
theorem existsSimplePoleGermAtSomePoint_RiemannSphere :
    ExistsSimplePoleGermAtSomePoint RiemannSphere :=
  ⟨(∞ : RiemannSphere), RSSimplePoleGerm,
    RSSimplePoleGerm_mem_linearSystemGermDeltaP_infty,
    RSSimplePoleGerm_orderAt_infty⟩

end JacobianChallenge.MeromorphicFunctionField

end
