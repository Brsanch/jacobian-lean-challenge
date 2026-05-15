/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SourceFiberPathIntegrandLocalSheetGAtT
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalSheetSmoothOn
import JacobianChallenge.Manifold.CotangentPullbackAtApply

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Chain-rule unfolding of per-fibre integrand at general `t₀`

Building on `sourceFiberPath_integrand_eq_local_at_lifted_sheet`,
unfolds the inner `mfderiv (sheet_q.g ∘ β ∘ σ) u 1` via the chain rule
into

```
mfderiv sheet_q.g (β(σ u)) ((mfderiv β (σ u)) ((mfderiv σ u) 1))
```

then converts the resulting `applyCotangent (ω (sheet_q.g(β(σ u))))
(mfderiv sheet_q.g … w)` into `applyCotangent (cotangentPullbackAt
sheet_q.g (β(σ u)) ω) w` via `applyCotangent_cotangentPullbackAt`.

Headline (per-fibre, at general `t₀`):

```
∃ a b ∈ [0, 1], a ≤ t₀ ≤ b, ∀ u ∈ Ioo a b,
  (sourceFiberPath p).integrand om u
    = applyCotangent (cotangentPullbackAt sheet_q.g (β(σ u)) om)
        ((mfderiv β (σ u)) ((mfderiv σ u) 1))
```

Crucially, `sheet_q.V` automatically contains `β(σ t₀)` (as a nbhd
of its base value), so by continuity it contains `β(σ u)` for `u`
near `t₀`. This means the differentiability of `sheet_q.g` at
`β(σ u)` is dischargeable on the sub-interval — in contrast to the
β 0-centered version, where this only worked near `t = 0`.

## What ships

* `MeromorphicNonzero.sourceFiberPath_integrand_chain_at_lifted_sheet`
  — the headline chain-rule-unfolded per-fibre integrand identity
  at general `t₀`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Chain-rule-unfolded per-fibre integrand at general `t₀` via the
lifted-point sheet.** -/
theorem sourceFiberPath_integrand_chain_at_lifted_sheet
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet)
    {x : X} (hx : f.toRiemannSphere x = β 0)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) :
    let γ := (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath.extend
    let q := γ t₀
    let hβσt₀_reg : β (Real.smoothTransition t₀) ∈ f.regularValueSet :=
      hβ_reg (Real.smoothTransition t₀)
        ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
    let hq_lift : f.toRiemannSphere q = β (Real.smoothTransition t₀) := by
      show f.toRiemannSphere
        ((f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath.extend t₀)
        = β (Real.smoothTransition t₀)
      rw [Path.extend_extends'
        (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath ⟨t₀, ht₀⟩]
      exact f.sourceFiberPath_toPath_lifts hnc hβ_smooth hβ_reg hx ⟨t₀, ht₀⟩
    let hq_reg : q ∈ f.regularSet :=
      f.mem_regularSet_of_preimage_regularValue hβσt₀_reg hq_lift
    let sheet_q := f.localSheetData_at_regular hnc hq_reg
    ∃ a b : ℝ, a ∈ Icc (0 : ℝ) 1 ∧ b ∈ Icc (0 : ℝ) 1 ∧ a ≤ t₀ ∧ t₀ ≤ b ∧
      (0 < t₀ → a < t₀) ∧ (t₀ < 1 → t₀ < b) ∧
      ∀ u ∈ Ioo a b,
        (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).integrand om u
          = SmoothPath.applyCotangent
              (cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
                sheet_q.g (β (Real.smoothTransition u)) om)
              ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (Real.smoothTransition u) :
                  ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
                    (β (Real.smoothTransition u)))
                ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.smoothTransition u :
                    ℝ →L[ℝ] ℝ) (1 : ℝ))) := by
  classical
  intro γ q hβσt₀_reg hq_lift hq_reg sheet_q
  -- Get sheet.g realified ContMDiffOn near β(σ t₀) (which equals f.toRiemannSphere q).
  obtain ⟨u_nbhd, hu_nbhd, hu_smooth⟩ :=
    f.exists_contMDiffOn_localSheet_g_near_basePoint hnc hq_reg
  -- u_nbhd ∋ f.toRiemannSphere q, hence ∋ β(σ t₀) via hq_lift.
  obtain ⟨u_o, hu_o_sub, hu_o_open, hu_o_mem⟩ := mem_nhds_iff.mp hu_nbhd
  have hβσt₀_in_u_o : β (Real.smoothTransition t₀) ∈ u_o := by
    have h_mem : f.toRiemannSphere q ∈ u_o := hu_o_mem
    exact Eq.subst (motive := fun w => w ∈ u_o) hq_lift h_mem
  -- Continuity of β ∘ σ.
  have hβσ_cont : Continuous (fun u : ℝ => β (Real.smoothTransition u)) :=
    hβ_smooth.continuous.comp Real.smoothTransition.continuous
  -- (β ∘ σ) ⁻¹' u_o ∈ 𝓝 t₀.
  have h_pre_u_o_open : IsOpen ((fun u : ℝ => β (Real.smoothTransition u))
      ⁻¹' u_o) :=
    hβσ_cont.isOpen_preimage _ hu_o_open
  have ht₀_in_pre : t₀ ∈ (fun u : ℝ => β (Real.smoothTransition u)) ⁻¹' u_o :=
    hβσt₀_in_u_o
  -- Get the local identification interval (a, b).
  obtain ⟨a, b, ha_mem, hb_mem, ha_le_t₀, ht₀_le_b, ha_lt_t₀, ht₀_lt_b, h_local⟩ :=
    f.sourceFiberPath_integrand_eq_local_at_lifted_sheet hnc hβ_smooth hβ_reg hx
      om ht₀
  -- We may need to shrink (a, b) to ensure (β ∘ σ)(u) ∈ u_o on it.
  -- Pick ε > 0 with Metric.ball t₀ ε ⊆ (β ∘ σ) ⁻¹' u_o, then intersect.
  obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.mem_nhds_iff.mp
    (h_pre_u_o_open.mem_nhds ht₀_in_pre)
  set a' : ℝ := max a (t₀ - ε / 2) with ha'_def
  set b' : ℝ := min b (t₀ + ε / 2) with hb'_def
  have ha'_le_t₀ : a' ≤ t₀ := max_le ha_le_t₀ (by linarith)
  have ht₀_le_b' : t₀ ≤ b' := le_min ht₀_le_b (by linarith)
  have ha'_mem : a' ∈ Icc (0 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · exact le_max_of_le_left ha_mem.1
    · exact le_trans ha'_le_t₀ ht₀.2
  have hb'_mem : b' ∈ Icc (0 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · exact le_trans ht₀.1 ht₀_le_b'
    · exact min_le_of_left_le hb_mem.2
  have ha'_lt_t₀ : 0 < t₀ → a' < t₀ := by
    intro ht₀_pos
    refine max_lt (ha_lt_t₀ ht₀_pos) ?_
    linarith
  have ht₀_lt_b' : t₀ < 1 → t₀ < b' := by
    intro ht₀_lt_one
    refine lt_min (ht₀_lt_b ht₀_lt_one) ?_
    linarith
  refine ⟨a', b', ha'_mem, hb'_mem, ha'_le_t₀, ht₀_le_b', ha'_lt_t₀, ht₀_lt_b', ?_⟩
  intro u ⟨hau, hub⟩
  -- u ∈ Ioo a b (from a' ≥ a, b' ≤ b).
  have hu_in_ab : u ∈ Ioo a b := by
    refine ⟨lt_of_le_of_lt (le_max_left _ _) hau,
      lt_of_lt_of_le hub (min_le_left _ _)⟩
  -- (β ∘ σ)(u) ∈ u_o (from u ∈ Metric.ball t₀ ε).
  have hu_in_ball : u ∈ Metric.ball t₀ ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · have : t₀ - ε / 2 ≤ u :=
        le_trans (le_max_right _ _) (le_of_lt hau)
      linarith
    · have : u ≤ t₀ + ε / 2 :=
        le_trans (le_of_lt hub) (min_le_right _ _)
      linarith
  have h_βσu_in_u_o : β (Real.smoothTransition u) ∈ u_o := hε_sub hu_in_ball
  have h_βσu_in_u_nbhd : β (Real.smoothTransition u) ∈ u_nbhd :=
    hu_o_sub h_βσu_in_u_o
  -- sheet_q.g is ContMDiffAt ω at β(σ u) (via hu_smooth + open hood).
  have h_sheet_g_omega : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω sheet_q.g
      (β (Real.smoothTransition u)) :=
    hu_smooth.contMDiffAt
      (mem_of_superset (hu_o_open.mem_nhds h_βσu_in_u_o) hu_o_sub)
  -- Realify.
  have h_sheet_g_real : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ sheet_q.g
      (β (Real.smoothTransition u)) :=
    ContMDiffAt.complex_to_real h_sheet_g_omega
  -- β is ContMDiffAt at σ u.
  have hβ_at : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β (Real.smoothTransition u) :=
    hβ_smooth (Real.smoothTransition u)
  -- σ is ContMDiffAt at u (real ℝ → ℝ smooth).
  have hσ_at : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.smoothTransition u :=
    Real.smoothTransition.contDiff.contMDiff u
  -- MDifferentiableAt's.
  have h_sheet_g_mdiff : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) sheet_q.g
      (β (Real.smoothTransition u)) :=
    h_sheet_g_real.mdifferentiableAt (by decide)
  have hβ_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (Real.smoothTransition u) :=
    hβ_at.mdifferentiableAt (by decide)
  have hσ_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.smoothTransition u :=
    hσ_at.mdifferentiableAt (by decide)
  -- Apply local-sheet integrand chip.
  have h_local_u := h_local u hu_in_ab
  -- Now unfold the mfderiv via chain rule:
  --   mfderiv (sheet_q.g ∘ β ∘ σ) u 1
  --     = mfderiv sheet_q.g (β(σ u)) (mfderiv β (σ u) (mfderiv σ u 1))
  -- Use mfderiv_comp_apply twice.
  set f_pull : ℝ → X := fun v => sheet_q.g (β (Real.smoothTransition v))
    with hf_pull_def
  -- f_pull = sheet_q.g ∘ (β ∘ σ).
  set βσ : ℝ → RiemannSphere := fun v => β (Real.smoothTransition v) with hβσ_def
  have hf_pull_unfold : f_pull = sheet_q.g ∘ βσ := rfl
  have hβσ_unfold : βσ = β ∘ Real.smoothTransition := rfl
  -- mfderiv (sheet_q.g ∘ βσ) u 1 = mfderiv sheet_q.g (βσ u) (mfderiv βσ u 1).
  have hβσ_mdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) βσ u := by
    rw [hβσ_unfold]
    exact hβ_mdiff.comp u hσ_mdiff
  have h_step1 :
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) f_pull u :
          ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (f_pull u)) (1 : ℝ)
      = (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) sheet_q.g (βσ u) :
            TangentSpace 𝓘(ℝ, ℂ) (βσ u) →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
              (sheet_q.g (βσ u)))
          ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) βσ u :
              ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (βσ u)) (1 : ℝ)) := by
    rw [hf_pull_unfold]
    exact mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℂ)) (I'' := 𝓘(ℝ, ℂ))
      (x := u) (f := βσ) (g := sheet_q.g) h_sheet_g_mdiff hβσ_mdiff (1 : ℝ)
  -- mfderiv βσ u 1 = mfderiv β (σ u) (mfderiv σ u 1).
  have h_step2 :
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) βσ u : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (βσ u))
        (1 : ℝ)
      = (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (Real.smoothTransition u) :
          ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (β (Real.smoothTransition u)))
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.smoothTransition u :
            ℝ →L[ℝ] ℝ) (1 : ℝ)) := by
    rw [hβσ_unfold]
    exact mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, ℂ))
      (x := u) (f := Real.smoothTransition) (g := β) hβ_mdiff hσ_mdiff (1 : ℝ)
  -- Substitute.
  rw [h_local_u]
  rw [h_step1, h_step2]
  -- The RHS is now applyCotangent (om(sheet.g(β(σu))))
  --   (mfderiv sheet_q.g (β(σ u)) (mfderiv β (σ u) (mfderiv σ u 1))).
  -- Use applyCotangent_cotangentPullbackAt to package as cotangentPullbackAt.
  exact (applyCotangent_cotangentPullbackAt
    (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
    sheet_q.g (β (Real.smoothTransition u)) om
    ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β (Real.smoothTransition u))
      ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.smoothTransition u) (1 : ℝ)))).symm

end MeromorphicNonzero

end JacobianChallenge

end
