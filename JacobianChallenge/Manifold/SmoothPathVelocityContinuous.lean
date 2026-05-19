/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathIntegral
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option linter.unusedSectionVars false

/-! # Continuity of `SmoothPath.velocity`

For a smooth path `γ : SmoothPath 𝓘(ℝ, E) Y` (with `Y` modeled
trivially on `E`), the velocity function `t ↦ γ.velocity t : ℝ → E`
is continuous (in fact `C^∞`).

The argument:
* `γ.ambient : ℝ → Y` is `C^∞` (by `SmoothPath.smooth`).
* For `Y = E` (trivial-model case), `ContMDiff ↔ ContDiff` gives
  `ContDiff ℝ ∞ γ.ambient`.
* `ContDiff.continuous_fderiv` gives continuity of `fderiv ℝ γ.ambient`.
* The application at `1 ∈ ℝ` (giving velocity) is continuous via the
  bounded-bilinear-map structure of CLM application.

For our use on `T² = ℂ ⧸ L`, the codomain is the manifold ℂ ⧸ L,
which is NOT a vector space. The lemma here is stated for the case
where the codomain is a normed space; we use it on the lifted
construction in `ℂ`.

For `γ.ambient : ℝ → ℂ⧸L` (manifold codomain), velocity continuity
requires manifold-level results, not covered by this chip.

## What this file ships

* `SmoothPath.velocity_continuous_of_ambient_contDiff_E` — velocity
  continuity when γ.ambient is `ContDiff ℝ ∞` and the codomain is `E`
  (a normed space). For `SmoothPath` on `Y = E`, this follows from
  the underlying `ContMDiff ↔ ContDiff`.

No `sorry`, no `axiom`. -/

open scoped Manifold ContDiff Topology

noncomputable section

namespace JacobianChallenge

namespace SmoothPath

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Velocity continuity for a SmoothPath into a normed space.**
For `γ : SmoothPath 𝓘(ℝ, E) E` (trivial-model codomain), velocity is
continuous. Specifically, `velocity γ t = fderiv ℝ γ.ambient t 1` and
`fderiv` of a `C^∞` function is continuous. -/
theorem velocity_continuous_of_vector_space
    (γ : SmoothPath 𝓘(ℝ, E) E) :
    Continuous γ.velocity := by
  -- γ.ambient is ContMDiff at ∞.
  have h_amb_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ.ambient :=
    γ.ambient_contMDiff
  -- Bridge to ContDiff via trivial-model identification.
  have h_amb_cd : ContDiff ℝ ∞ γ.ambient :=
    (contMDiff_iff_contDiff (f := γ.ambient) (n := ∞)).mp h_amb_smooth
  -- fderiv is continuous (for ContDiff at level ≥ 1).
  have h_fderiv_cont : Continuous (fderiv ℝ γ.ambient) := by
    apply h_amb_cd.continuous_fderiv
    -- ∞ ≠ 0 in WithTop ℕ∞.
    intro h
    -- ∞ : WithTop ℕ∞ equals 0 should be False.
    -- ∞ = ⊤; (0 : WithTop ℕ∞) = ⊥. They're not equal.
    have : (∞ : WithTop ℕ∞) = 0 := h
    -- ∞ > 0 derives contradiction.
    exact absurd this (by decide)
  -- velocity γ t = (fderiv ℝ γ.ambient t) 1.
  -- Use that mfderiv = fderiv (trivial model) and CLM apply at constant is continuous.
  have h_velocity_eq : ∀ t : ℝ, γ.velocity t = (fderiv ℝ γ.ambient t) (1 : ℝ) := by
    intro t
    show (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ.ambient t : ℝ →L[ℝ] _) (1 : ℝ)
        = (fderiv ℝ γ.ambient t) (1 : ℝ)
    congr 1
    exact mfderiv_eq_fderiv (f := γ.ambient) (x := t)
  rw [show γ.velocity = (fun t : ℝ => (fderiv ℝ γ.ambient t) (1 : ℝ)) from by
    funext t; exact h_velocity_eq t]
  -- Now: continuity of (fun t => (fderiv ℝ γ.ambient t) 1).
  -- The eval-at-1 CLM Hom.evalAt is continuous (it's a continuous linear map itself).
  have h_eval_cont : Continuous (fun L : ℝ →L[ℝ] E => L (1 : ℝ)) := by
    exact (ContinuousLinearMap.apply ℝ E (1 : ℝ)).continuous
  exact h_eval_cont.comp h_fderiv_cont

end SmoothPath

end JacobianChallenge

end
