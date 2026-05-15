/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import JacobianChallenge.Manifold.MeromorphicNonzeroSmoothLocalLift

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Chain rule for `mfderiv (sheet.g ∘ β ∘ σ)`

For the per-fiber-point integrand identification (chip from
`SourceFiberPathAmbientSheetEq.lean`), the right-hand side contains
`mfderiv (sheet.g ∘ β ∘ σ) t (1)`. The chain rule decomposes this as

```
mfderiv (sheet.g ∘ β ∘ σ) t (1)
  = mfderiv sheet.g (β(σ t)) (mfderiv β (σ t) (mfderiv σ t (1)))
```

via two applications of `mfderiv_comp_apply`.

The hypotheses required are smoothness of each factor at the relevant
point, in the real-model form `𝓘(ℝ, ℝ)`-on-ℝ, `𝓘(ℝ, ℂ)`-on-RiemannSphere,
`𝓘(ℝ, ℂ)`-on-X (so models compose). For the X side this uses
`contMDiffAt_localSheet_g_at_basePoint` realified via
`ContMDiffAt.complex_to_real` (same idiom as
`contMDiffAt_local_lift_at_basepoint`).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Two-fold composition: `mfderiv (β ∘ σ)` -/

/-- **`mfderiv` of `β ∘ σ`** via `mfderiv_comp_apply`. -/
lemma mfderiv_beta_sigma_comp
    {β : ℝ → RiemannSphere} {σ : ℝ → ℝ} {t : ℝ}
    (hβ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β (σ t))
    (hσ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ σ t) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (fun u : ℝ => β (σ u)) t (1 : ℝ)
      = (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (σ t) :
          ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (β (σ t)))
          ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) σ t : ℝ →L[ℝ] ℝ) (1 : ℝ)) := by
  have h_β_diff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (σ t) :=
    hβ.mdifferentiableAt (by decide)
  have h_σ_diff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) σ t :=
    hσ.mdifferentiableAt (by decide)
  exact mfderiv_comp_apply t h_β_diff h_σ_diff (1 : ℝ)

/-! ## Three-fold composition: `mfderiv (sheet.g ∘ β ∘ σ)` -/

/-- **`mfderiv` of `sheet.g ∘ β ∘ σ` decomposes via two chain-rule
applications.** Smoothness hypotheses are in the realified model
`𝓘(ℝ, ·)` so they can all compose; `sheet.g`'s analytic regularity is
realified via `ContMDiffAt.complex_to_real`. -/
theorem mfderiv_sheet_g_beta_sigma_chain
    {g : RiemannSphere → X} {β : ℝ → RiemannSphere} {σ : ℝ → ℝ} {t : ℝ}
    (hg : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ g (β (σ t)))
    (hβ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β (σ t))
    (hσ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ σ t) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (fun u : ℝ => g (β (σ u))) t (1 : ℝ)
      = (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g (β (σ t)) :
          TangentSpace 𝓘(ℝ, ℂ) (β (σ t)) →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (g (β (σ t))))
          ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (σ t) :
              ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (β (σ t)))
            ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) σ t : ℝ →L[ℝ] ℝ) (1 : ℝ))) := by
  -- Differentiability of each factor.
  have h_g_diff : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g (β (σ t)) :=
    hg.mdifferentiableAt (by decide)
  have h_βσ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (fun u : ℝ => β (σ u)) t :=
    hβ.comp t hσ
  have h_βσ_diff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (fun u : ℝ => β (σ u)) t :=
    h_βσ.mdifferentiableAt (by decide)
  -- Chain rule for the outer composition: `g ∘ (β ∘ σ)` at `t`.
  have h_outer : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (fun u : ℝ => g (β (σ u))) t (1 : ℝ)
      = (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g (β (σ t)))
          ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (fun u : ℝ => β (σ u)) t) (1 : ℝ)) :=
    mfderiv_comp_apply t h_g_diff h_βσ_diff (1 : ℝ)
  rw [h_outer]
  -- Inner chain rule: `β ∘ σ` at `t`.
  rw [mfderiv_beta_sigma_comp hβ hσ]

/-! ## Specialised to `localSheetData_at_regular`'s `sheet.g` -/

/-- **Chain rule for the manifold-level local sheet's `g` composed with
`β ∘ σ`.** The realified smoothness of `sheet.g` at the base value
comes from `contMDiffAt_localSheet_g_at_basePoint` + `complex_to_real`. -/
theorem mfderiv_localSheet_g_beta_sigma_chain_at_base
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {x₀ : X} (hx₀_reg : x₀ ∈ f.regularSet)
    {β : ℝ → RiemannSphere} {σ : ℝ → ℝ} {t : ℝ}
    (hβ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β (σ t))
    (hσ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ σ t)
    (hbase : β (σ t) = f.toRiemannSphere x₀) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
        (fun u : ℝ => (f.localSheetData_at_regular hnc hx₀_reg).g (β (σ u))) t
        (1 : ℝ)
      = (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (f.localSheetData_at_regular hnc hx₀_reg).g
            (β (σ t)) :
          TangentSpace 𝓘(ℝ, ℂ) (β (σ t))
            →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
              ((f.localSheetData_at_regular hnc hx₀_reg).g (β (σ t))))
          ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (σ t) :
              ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (β (σ t)))
            ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) σ t : ℝ →L[ℝ] ℝ) (1 : ℝ))) := by
  -- Realified smoothness of sheet.g at β (σ t) = f.toRiemannSphere x₀.
  have h_sheet_g_omega : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (f.localSheetData_at_regular hnc hx₀_reg).g (f.toRiemannSphere x₀) :=
    f.contMDiffAt_localSheet_g_at_basePoint hnc hx₀_reg
  have h_sheet_g_real_base : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (f.localSheetData_at_regular hnc hx₀_reg).g (f.toRiemannSphere x₀) :=
    ContMDiffAt.complex_to_real h_sheet_g_omega
  have h_sheet_g_real : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (f.localSheetData_at_regular hnc hx₀_reg).g (β (σ t)) := by
    rw [hbase]; exact h_sheet_g_real_base
  exact mfderiv_sheet_g_beta_sigma_chain h_sheet_g_real hβ hσ

end MeromorphicNonzero

end JacobianChallenge

end
