/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PairingContinuityBetaLocal
import JacobianChallenge.Manifold.SourceSheetSumEqTraceAt
import JacobianChallenge.Manifold.CotangentPullbackAtApply
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalSheetSmoothOn
import JacobianChallenge.Manifold.RiemannSphereRealManifold
import JacobianChallenge.Manifold.ComplexManifoldRealification
import Mathlib.Geometry.Manifold.MFDeriv.Basic

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Per-sheet cotangent-pullback pairing continuity along `β`

For a non-constant `f : MeromorphicNonzero X`, a regular fibre point
`x₀ ∈ f.regularSet`, a smooth `β : ℝ → RiemannSphere`, and an open
neighbourhood `u` of `β s₀` on which the local sheet inverse
`sheet.g := (localSheetData_at_regular hnc hx₀_reg).g` is real-smooth
(`ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ sheet.g u`), the pairing

  `s ↦ applyCotangent (sheetCotPullback hnc hx₀_reg (β s) om) (mfderiv β s 1)`

is `ContinuousAt s₀`.

The proof is a chain-rule reduction: on the open nbhd `β ⁻¹' u` of `s₀`,
the LHS rewrites (via `applyCotangent_cotangentPullbackAt` +
`mfderiv_comp_apply`) to the form

  `applyCotangent (om ((sheet.g ∘ β) s)) (mfderiv (sheet.g ∘ β) s 1)`

which is the pairing of `om` along the composed smooth path
`γ := sheet.g ∘ β : ℝ → X`. Continuity at `s₀` then follows from
`continuousAt_pairing_smoothOneForm_beta_local` (chip 14) applied with
`ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ γ s₀` (compose `β`-smoothness at `s₀`
with `sheet.g`-smoothness at `β s₀`).

The smoothness witness `hu_smooth_g` is the realified form of
`exists_contMDiffOn_localSheet_g_near_basePoint` (in tree); callers
will instantiate it via `ContMDiffOn.complex_to_real_of_isOpen`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Per-sheet pairing continuity at `s₀`.**

For `β` smooth and a regular fibre point `x₀`, given an open
neighbourhood `u` of `β s₀` on which the sheet inverse `sheet.g`
is real-smooth (`ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞`), the per-sheet
cotangent-pullback pairing is `ContinuousAt s₀`. -/
theorem continuousAt_sheetCotPullback_pairing
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {x₀ : X} (hx₀_reg : x₀ ∈ f.regularSet)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    {s₀ : ℝ} {u : Set RiemannSphere}
    (hu_open : IsOpen u) (hβs₀_in_u : β s₀ ∈ u)
    (hu_smooth_g : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (f.localSheetData_at_regular hnc hx₀_reg).g u) :
    ContinuousAt
      (fun s => SmoothPath.applyCotangent
        (f.sheetCotPullback hnc hx₀_reg (β s) om)
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s) (1 : ℝ))) s₀ := by
  -- Abbreviate the sheet inverse and the composed path.
  set sheetg : RiemannSphere → X :=
    (f.localSheetData_at_regular hnc hx₀_reg).g with hsheetg_def
  set γ : ℝ → X := fun s => sheetg (β s) with hγ_def
  -- `sheet.g` is `ContMDiffAt ∞` at `β s₀` (real model) via `ContMDiffOn`.
  have h_sheetg_at_βs₀ : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ sheetg (β s₀) :=
    hu_smooth_g.contMDiffAt (hu_open.mem_nhds hβs₀_in_u)
  -- `β` is `ContMDiffAt ∞` at `s₀`.
  have hβ_at_s₀ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β s₀ := hβ_smooth s₀
  -- Composed path `γ = sheetg ∘ β` is `ContMDiffAt ∞` at `s₀`.
  have hγ_at_s₀ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ γ s₀ :=
    h_sheetg_at_βs₀.comp s₀ hβ_at_s₀
  -- Apply local chip 12 (`continuousAt_pairing_smoothOneForm_beta_local`)
  -- to the composed path γ + om: gives ContinuousAt of the γ-pairing.
  have h_γ_pair_cont : ContinuousAt
      (fun s => SmoothPath.applyCotangent (om (γ s))
                  ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ s) (1 : ℝ))) s₀ :=
    continuousAt_pairing_smoothOneForm_beta_local (I := 𝓘(ℝ, ℂ)) hγ_at_s₀ om
  -- EqOn on the open nbhd `β ⁻¹' u` of `s₀`: LHS = γ-pairing.
  have h_W_open : IsOpen (β ⁻¹' u) := hu_open.preimage hβ_smooth.continuous
  have h_s₀_in_W : s₀ ∈ β ⁻¹' u := hβs₀_in_u
  have h_eq : (β ⁻¹' u).EqOn
      (fun s => SmoothPath.applyCotangent
        (f.sheetCotPullback hnc hx₀_reg (β s) om)
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s) (1 : ℝ)))
      (fun s => SmoothPath.applyCotangent (om (γ s))
                  ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ s) (1 : ℝ))) := by
    intro s hs
    -- `sheetg` is `ContMDiffAt ∞` at `β s` (since β s ∈ u).
    have h_sheetg_at_βs : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ sheetg (β s) :=
      hu_smooth_g.contMDiffAt (hu_open.mem_nhds hs)
    -- `β` is `ContMDiffAt ∞` at `s`.
    have hβ_at_s : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β s := hβ_smooth s
    -- MDifferentiableAt witnesses.
    have h_sheetg_mdiff : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) sheetg (β s) :=
      h_sheetg_at_βs.mdifferentiableAt (by decide)
    have hβ_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s :=
      hβ_at_s.mdifferentiableAt (by decide)
    -- Unfold sheetCotPullback to cotangentPullbackAt.
    show SmoothPath.applyCotangent
          (cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
            sheetg (β s) om)
          ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s) (1 : ℝ))
        = SmoothPath.applyCotangent (om (γ s))
            ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ s) (1 : ℝ))
    -- Step 1: applyCotangent_cotangentPullbackAt.
    rw [applyCotangent_cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
          sheetg (β s) om
          ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s) (1 : ℝ))]
    -- Now LHS: applyCotangent (om (sheetg (β s)))
    --   (mfderiv sheetg (β s) (mfderiv β s 1))
    -- RHS: applyCotangent (om (γ s)) (mfderiv γ s 1)
    -- γ s = sheetg (β s) on the nose by definition of γ.
    -- Need: mfderiv sheetg (β s) (mfderiv β s 1) = mfderiv γ s 1.
    -- Use chain rule mfderiv_comp_apply.
    have h_chain :
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ s : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (γ s))
            (1 : ℝ)
          = (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) sheetg (β s) :
                TangentSpace 𝓘(ℝ, ℂ) (β s) →L[ℝ]
                  TangentSpace 𝓘(ℝ, ℂ) (sheetg (β s)))
              ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s :
                  ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (β s)) (1 : ℝ)) := by
      show (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (sheetg ∘ β) s) (1 : ℝ)
          = (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) sheetg (β s))
              ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β s) (1 : ℝ))
      exact mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℂ)) (I'' := 𝓘(ℝ, ℂ))
        (x := s) (f := β) (g := sheetg) h_sheetg_mdiff hβ_mdiff (1 : ℝ)
    rw [← h_chain]
  -- EqOn on open nbhd → EventuallyEq → ContinuousAt.congr.
  refine h_γ_pair_cont.congr ?_
  exact (h_eq.eventuallyEq_of_mem (h_W_open.mem_nhds h_s₀_in_W)).symm

end MeromorphicNonzero

end JacobianChallenge

end
