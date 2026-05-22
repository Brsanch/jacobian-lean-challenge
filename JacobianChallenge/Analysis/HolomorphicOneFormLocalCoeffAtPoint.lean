/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.HolomorphicOneFormLocalCoeffAtBase

/-! # `localCoeff om y` at the chart-image of an arbitrary point of the chart source

Extends chip E.1 (`localCoeff_at_chartAt_self`) from `x = y` to any
`x ∈ (chartAt ℂ y).source`. The connection is via the cotangent
bundle's coord-change between charts `achart ℂ x` and `achart ℂ y`,
evaluated at the common base point `x`.

The key technical fact: the coord-change CLM `cotangentBundleCore.
coordChange (achart ℂ x) (achart ℂ y) x` is **invertible** (a
`VectorBundleCore`'s `coordChange` always satisfies a composition
identity making it an iso between fibers), hence sends a nonzero
input to a nonzero output. Applying the result CLM to `1 : ℂ` then
preserves non-vanishing (a nonzero `ℂ →L[ℂ] ℂ` map sends `1` to a
nonzero value).

Headline:

```
theorem localCoeff_at_chart_image_ne_zero_of_eval_ne_zero
    (om : HolomorphicOneForm X) {y : X} {x : X}
    (hx_source : x ∈ (chartAt ℂ y).source)
    (h_eval : om.eval x ≠ 0) :
    localCoeff om y ((chartAt ℂ y) x) ≠ 0
```

This is chip E.1.5 of the L²-positivity arc — the building block
chip E.4 uses to find a chart `y` (with `f.toFun y x > 0`) at which
`localCoeff om y ((chartAt ℂ y) x)` is nonzero.

No `sorry`, no `axiom`. -/

set_option linter.unusedSectionVars false

noncomputable section

open scoped Manifold ContDiff Topology
open Bundle

namespace HolomorphicOneForm

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Coord-change is injective on the fiber.**

For the cotangent bundle of a `ChartedSpace ℂ X` and any two atlas
charts `achart ℂ y₁`, `achart ℂ y₂` and base point `x` in both
chart-sources, the linear map `coordChange (achart ℂ y₁) (achart ℂ y₂) x`
is injective. Derived from `coordChange_comp` + `coordChange_self`. -/
private lemma cotangentBundleCore_coordChange_injective
    {y₁ y₂ : X} {x : X}
    (hx₁ : x ∈ (chartAt ℂ y₁).source) (hx₂ : x ∈ (chartAt ℂ y₂).source) :
    Function.Injective
      (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y₁) (achart ℂ y₂) x : (ℂ →L[ℂ] ℂ) → (ℂ →L[ℂ] ℂ)) ) := by
  -- Use that coordChange y₂ y₁ x ∘ coordChange y₁ y₂ x = coordChange y₁ y₁ x = id.
  intro a b hab
  -- baseSet of `achart ℂ y` is `(chartAt ℂ y).source`. Confirm membership.
  have h_in₁ : x ∈ (cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ y₁) := hx₁
  have h_in₂ : x ∈ (cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ y₂) := hx₂
  have h_comp_a := (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange_comp
    (achart ℂ y₁) (achart ℂ y₂) (achart ℂ y₁) x ⟨⟨h_in₁, h_in₂⟩, h_in₁⟩ a
  have h_comp_b := (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange_comp
    (achart ℂ y₁) (achart ℂ y₂) (achart ℂ y₁) x ⟨⟨h_in₁, h_in₂⟩, h_in₁⟩ b
  -- h_comp_a : coordChange y₂ y₁ x (coordChange y₁ y₂ x a) = coordChange y₁ y₁ x a = a.
  rw [(cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange_self
        (achart ℂ y₁) x h_in₁ a] at h_comp_a
  rw [(cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange_self
        (achart ℂ y₁) x h_in₁ b] at h_comp_b
  rw [hab] at h_comp_a
  exact h_comp_a.symm.trans h_comp_b

/-- **`localCoeff om y` at the chart image of an arbitrary point `x ∈
(chartAt ℂ y).source`**, expressed via the cotangent bundle's
coord-change applied to `om.eval x`.

The expansion of the `localCoeff` definition at `z := (chartAt ℂ y) x`
unfolds to the coord-change between the trivializations at `achart ℂ x`
and `achart ℂ y`, evaluated at the base point `x`, applied to
`om.eval x`, then evaluated at `1 : ℂ`. -/
private lemma localCoeff_at_chart_image_eq
    (om : HolomorphicOneForm X) {y x : X}
    (hx_source : x ∈ (chartAt ℂ y).source) :
    localCoeff om y ((chartAt ℂ y) x)
      = (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
            (achart ℂ x) (achart ℂ y) x) (om.eval x)) 1 := by
  have h_symm : (chartAt ℂ y).symm ((chartAt ℂ y) x) = x :=
    (chartAt ℂ y).left_inv hx_source
  -- Unfold localCoeff at z := (chartAt ℂ y) x.
  unfold localCoeff
  rw [h_symm]
  rfl

/-- **Headline: `localCoeff om y ((chartAt ℂ y) x)` is nonzero whenever
`x ∈ (chartAt ℂ y).source` and `om.eval x ≠ 0`.**

Composes:
* `localCoeff_at_chart_image_eq` to expand `localCoeff` to a
  coord-change applied to `om.eval x` then evaluated at `1`;
* `cotangentBundleCore_coordChange_injective` to show the coord-change
  preserves non-vanishing;
* the elementary fact that a nonzero `ℂ →L[ℂ] ℂ` map sends `1` to a
  nonzero value (by 1-dimensionality). -/
theorem localCoeff_at_chart_image_ne_zero_of_eval_ne_zero
    (om : HolomorphicOneForm X) {y x : X}
    (hx_source : x ∈ (chartAt ℂ y).source)
    (h_eval : om.eval x ≠ 0) :
    localCoeff om y ((chartAt ℂ y) x) ≠ 0 := by
  rw [localCoeff_at_chart_image_eq om hx_source]
  -- Goal: (coordChange (achart ℂ x) (achart ℂ y) x (om.eval x)) 1 ≠ 0.
  -- Step 1: coordChange (achart ℂ x) (achart ℂ y) x (om.eval x) ≠ 0,
  --   via injectivity at x.
  have hx_self : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have h_inj := cotangentBundleCore_coordChange_injective (y₁ := x) (y₂ := y)
    (x := x) hx_self hx_source
  have h_zero_eq : (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ x) (achart ℂ y) x 0 = 0 := by
    simp [ContinuousLinearMap.map_zero]
  have h_coord_ne : (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ x) (achart ℂ y) x (om.eval x) ≠ 0 := by
    intro h_zero
    apply h_eval
    have : (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ x) (achart ℂ y) x (om.eval x)
        = (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
            (achart ℂ x) (achart ℂ y) x 0 := by
      rw [h_zero, h_zero_eq]
    exact h_inj this
  -- Step 2: a nonzero CLM ℂ →L[ℂ] ℂ sends 1 to a nonzero ℂ.
  intro h_apply_one_zero
  apply h_coord_ne
  refine ContinuousLinearMap.ext (fun c => ?_)
  have : ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
            (achart ℂ x) (achart ℂ y) x (om.eval x)) c
        = c • ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
            (achart ℂ x) (achart ℂ y) x (om.eval x)) 1 := by
    have h_smul : c = c • (1 : ℂ) := by simp
    nth_rewrite 1 [h_smul]
    exact ContinuousLinearMap.map_smul _ c 1
  rw [this, h_apply_one_zero, smul_zero]
  rfl

end HolomorphicOneForm

end
