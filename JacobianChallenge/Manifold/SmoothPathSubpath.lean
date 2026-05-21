/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothChain
import JacobianChallenge.Manifold.SmoothPathIntegral
import JacobianChallenge.Manifold.SmoothPathExt
import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option linter.unusedSectionVars false

/-! # `SmoothPath.subpath` — affine restriction to a sub-interval

Given a `SmoothPath γ : SmoothPath IM X` and two real numbers `0 ≤ a ≤ b ≤ 1`,
constructs the `SmoothPath` from `γ.ambient a` to `γ.ambient b` via the
affine reparameterisation `t ↦ γ.ambient (a + t·(b-a))` on `[0, 1]`.

This is the foundational primitive for chart-cover Lebesgue subdivision
of a smooth loop: the loop γ decomposes (at the chain level, modulo
stokesBoundaries) into a sum of `γ.subpath t_n t_{n+1}` for the
partition points produced by `lebesgueSubdivision_of_chartCover`.

## What this file ships

* `SmoothPath.subpathAmbient γ a b t := γ.ambient (a + t·(b-a))` — the
  ambient `ℝ → X` map.
* `SmoothPath.subpath γ a b ha hab hb : SmoothPath IM X` — packaged
  SmoothPath with src `γ.ambient a` and tgt `γ.ambient b`.
* Endpoint identifications + smoothness.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff unitInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {IM : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold IM ⊤ X]

namespace SmoothPath

/-- The ambient `ℝ → X` map for the subpath: affine reparam of γ.ambient. -/
def subpathAmbient (γ : SmoothPath IM X) (a b : ℝ) (t : ℝ) : X :=
  γ.ambient (a + t * (b - a))

lemma subpathAmbient_zero (γ : SmoothPath IM X) (a b : ℝ) :
    γ.subpathAmbient a b 0 = γ.ambient a := by
  unfold subpathAmbient
  norm_num

lemma subpathAmbient_one (γ : SmoothPath IM X) (a b : ℝ) :
    γ.subpathAmbient a b 1 = γ.ambient b := by
  unfold subpathAmbient
  ring_nf

/-- Smoothness of the subpath's ambient: composition of γ.ambient (smooth)
with the affine reparam (smooth). -/
lemma contMDiff_subpathAmbient (γ : SmoothPath IM X) (a b : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) IM ∞ (γ.subpathAmbient a b) := by
  unfold subpathAmbient
  -- Affine reparam `t ↦ a + t * (b - a)` is C∞.
  have h_affine : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t : ℝ => a + t * (b - a)) := by
    have h_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => a + t * (b - a)) := by
      have h_id : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun t : ℝ => t) := contDiff_id
      exact contDiff_const.add (h_id.mul contDiff_const)
    exact h_cd.contMDiff
  -- γ.ambient is C^∞ (smoothness witness of γ).
  exact γ.ambient_contMDiff.comp h_affine

/-- **The subpath** as a `SmoothPath IM X`, for `a, b ∈ [0, 1]` with
`a ≤ b`. -/
noncomputable def subpath (γ : SmoothPath IM X) (a b : ℝ)
    (_ha : 0 ≤ a) (_hab : a ≤ b) (_hb : b ≤ 1) :
    SmoothPath IM X where
  src := γ.ambient a
  tgt := γ.ambient b
  toPath := {
    toContinuousMap :=
      ⟨fun t : unitInterval => γ.subpathAmbient a b t.val,
        ((γ.contMDiff_subpathAmbient a b).continuous).comp
          continuous_subtype_val⟩
    source' := by
      show γ.subpathAmbient a b (0 : unitInterval).val = γ.ambient a
      change γ.subpathAmbient a b (0 : ℝ) = γ.ambient a
      exact γ.subpathAmbient_zero a b
    target' := by
      show γ.subpathAmbient a b (1 : unitInterval).val = γ.ambient b
      change γ.subpathAmbient a b (1 : ℝ) = γ.ambient b
      exact γ.subpathAmbient_one a b
  }
  smooth := by
    refine ⟨γ.subpathAmbient a b, γ.contMDiff_subpathAmbient a b, ?_⟩
    intro t
    rfl

@[simp] lemma subpath_src (γ : SmoothPath IM X) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (γ.subpath a b ha hab hb).src = γ.ambient a := rfl

@[simp] lemma subpath_tgt (γ : SmoothPath IM X) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (γ.subpath a b ha hab hb).tgt = γ.ambient b := rfl

end SmoothPath

end
