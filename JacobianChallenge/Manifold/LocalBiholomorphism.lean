/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Local biholomorphism witness from a nonvanishing analytic derivative

If `ψ : ℂ → ℂ` is analytic at `x₀` with `deriv ψ x₀ ≠ 0`, the inverse
function theorem packages `ψ` as an `OpenPartialHomeomorph`, and the
analytic-IFT (`AnalyticAt.analyticAt_localInverse`) shows the inverse is
analytic at `ψ x₀`. This file packages those mathlib lemmas into a
self-contained "local biholomorphism" witness with `MapsTo` /
`LeftInvOn` / `RightInvOn` data and analyticity of the inverse.

This is the residual flagged by ZZ151 (file
`AnalyticLocalNormalForm.lean`): the normal-form theorem produces such a
`ψ` together with `deriv ψ x₀ ≠ 0`, and downstream uses need to cash
that nonvanishing-derivative hypothesis into an honest local inverse.

## Idiom

We follow the pattern already used in
`MMeromorphicAt.localMultiplicity_one_locally_injective`
(`JacobianChallenge/Manifold/LocalNormalForm.lean`): lift `AnalyticAt`
to `HasStrictDerivAt` via `AnalyticAt.hasStrictDerivAt`, repackage with
nonvanishing derivative as `HasStrictFDerivAt` via
`HasStrictDerivAt.hasStrictFDerivAt_equiv`, and apply
`HasStrictFDerivAt.toOpenPartialHomeomorph`. The new ingredient here is
analyticity of the inverse, supplied by
`AnalyticAt.analyticAt_localInverse`.

## Anti-cheat

* No `axiom`, no `sorry`.
* No signature change to any pre-existing definition or theorem.
* Adds one new theorem in a new file, imported into the manifest.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace JacobianChallenge
namespace Manifold

/-- **Local biholomorphism from a nonvanishing analytic derivative.**

If `ψ : ℂ → ℂ` is analytic at `x₀` and `deriv ψ x₀ ≠ 0`, there exist
open neighborhoods `U` of `x₀` and `V` of `ψ x₀` and a local inverse
`φ_inv : ℂ → ℂ` with the four package conditions

* `MapsTo ψ U V`,
* `MapsTo φ_inv V U`,
* `LeftInvOn φ_inv ψ U`,
* `RightInvOn φ_inv ψ V`,

and with `φ_inv` analytic at `ψ x₀`. This is the local-biholomorphism
witness consumed by Hurwitz / branched-cover arguments. -/
theorem AnalyticAt.exists_local_biholomorphism
    {ψ : ℂ → ℂ} {x₀ : ℂ}
    (h_analytic : _root_.AnalyticAt ℂ ψ x₀) (h_deriv : deriv ψ x₀ ≠ 0) :
    ∃ (U : Set ℂ), U ∈ 𝓝 x₀ ∧ ∃ (V : Set ℂ), V ∈ 𝓝 (ψ x₀) ∧
      ∃ (φ_inv : ℂ → ℂ),
        Set.MapsTo ψ U V ∧
        Set.MapsTo φ_inv V U ∧
        Set.LeftInvOn φ_inv ψ U ∧
        Set.RightInvOn φ_inv ψ V ∧
        _root_.AnalyticAt ℂ φ_inv (ψ x₀) := by
  -- Step 1: Lift to `HasStrictDerivAt` via the analytic-derivative bridge.
  have hsd : HasStrictDerivAt ψ (deriv ψ x₀) x₀ := h_analytic.hasStrictDerivAt
  -- Step 2: Repackage as `HasStrictFDerivAt` with a `ContinuousLinearEquiv`
  -- (so the inverse function theorem applies).
  have hsfd :
      HasStrictFDerivAt ψ
        (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv ψ x₀) h_deriv) :
          ℂ →L[ℂ] ℂ) x₀ :=
    hsd.hasStrictFDerivAt_equiv h_deriv
  -- Step 3: Apply the inverse function theorem to get an `OpenPartialHomeomorph`.
  set φ : OpenPartialHomeomorph ℂ ℂ := hsfd.toOpenPartialHomeomorph ψ with hφ_def
  have hx₀_src : x₀ ∈ φ.source := hsfd.mem_toOpenPartialHomeomorph_source
  have h_coe : (φ : ℂ → ℂ) = ψ := hsfd.toOpenPartialHomeomorph_coe
  have hψx₀_tgt : ψ x₀ ∈ φ.target := by
    have := hsfd.image_mem_toOpenPartialHomeomorph_target
    exact this
  -- Sources/targets are open neighborhoods of the chosen points.
  have h_src_nhds : φ.source ∈ 𝓝 x₀ := φ.open_source.mem_nhds hx₀_src
  have h_tgt_nhds : φ.target ∈ 𝓝 (ψ x₀) := φ.open_target.mem_nhds hψx₀_tgt
  -- Step 4: Analyticity of the inverse via `AnalyticAt.analyticAt_localInverse`.
  -- The mathlib statement gives analyticity of `hf.hasStrictDerivAt.localInverse _ _ _ hf'`
  -- at `ψ x₀`. That `localInverse` is, by `localInverse_def`, equal to
  -- `(hsfd.toOpenPartialHomeomorph ψ).symm`, i.e. `φ.symm`.
  have h_inv_analytic_raw :
      _root_.AnalyticAt ℂ
        (h_analytic.hasStrictDerivAt.localInverse ψ (deriv ψ x₀) x₀ h_deriv)
        (ψ x₀) :=
    h_analytic.analyticAt_localInverse h_deriv
  -- Provide the witness `φ_inv := φ.symm`.
  refine ⟨φ.source, h_src_nhds, φ.target, h_tgt_nhds, (φ.symm : ℂ → ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · -- MapsTo ψ φ.source φ.target
    intro x hx
    have : φ x ∈ φ.target := φ.map_source hx
    -- Rewrite `(φ : ℂ → ℂ) x = ψ x` via `h_coe`.
    have hx' : ψ x ∈ φ.target := by
      have : (φ : ℂ → ℂ) x = ψ x := by rw [h_coe]
      exact this ▸ φ.map_source hx
    exact hx'
  · -- MapsTo φ.symm φ.target φ.source
    intro y hy
    exact φ.map_target hy
  · -- LeftInvOn φ.symm ψ φ.source
    intro x hx
    -- φ.symm (ψ x) = φ.symm (φ x) = x
    have h1 : (φ : ℂ → ℂ) x = ψ x := by rw [h_coe]
    calc (φ.symm : ℂ → ℂ) (ψ x)
        = (φ.symm : ℂ → ℂ) ((φ : ℂ → ℂ) x) := by rw [h1]
      _ = x := φ.left_inv hx
  · -- RightInvOn φ.symm ψ φ.target
    intro y hy
    have h1 : (φ : ℂ → ℂ) ((φ.symm : ℂ → ℂ) y) = ψ ((φ.symm : ℂ → ℂ) y) := by
      rw [h_coe]
    -- ψ (φ.symm y) = φ (φ.symm y) = y
    calc ψ ((φ.symm : ℂ → ℂ) y)
        = (φ : ℂ → ℂ) ((φ.symm : ℂ → ℂ) y) := h1.symm
      _ = y := φ.right_inv hy
  · -- AnalyticAt ℂ (φ.symm : ℂ → ℂ) (ψ x₀)
    -- The mathlib `localInverse` is definitionally `φ.symm`, so we can transport.
    have h_eq :
        h_analytic.hasStrictDerivAt.localInverse ψ (deriv ψ x₀) x₀ h_deriv
          = (φ.symm : ℂ → ℂ) := by
      -- `HasStrictDerivAt.localInverse` is defined via `hasStrictFDerivAt_equiv`,
      -- and `hsfd` is exactly that. Both unfold to
      -- `(hsfd.toOpenPartialHomeomorph ψ).symm`.
      rfl
    rw [h_eq] at h_inv_analytic_raw
    exact h_inv_analytic_raw

end Manifold
end JacobianChallenge

end
