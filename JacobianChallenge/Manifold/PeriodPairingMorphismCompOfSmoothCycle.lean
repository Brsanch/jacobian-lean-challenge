/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodPairingMorphismOfSmoothCycle
import JacobianChallenge.Manifold.PeriodPairingMorphismComp
import JacobianChallenge.Manifold.SmoothCyclePushComp
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackComp

set_option linter.unusedSectionVars false

/-! # `comp_ofSmoothCycle` — composition specialised to the `ofSmoothCycle` form

For two holomorphic curve maps `f : X → Y` and `g : Y → Z` with period
adjunctions for the canonical `SmoothCycle.pushHom` cycle pushforward,
the composite morphism is built with the canonical `pushHom (g ∘ f)`
form (NOT the bare functorial `pushHom g . pushHom f` that the generic
`comp` would deliver).

The chain:
* the composite adjunction is discharged from `adj_f`, `adj_g`,
  `SmoothCycle.pushHom_comp` (cycle-pushforward composition), and
  `HolomorphicOneForm.pullback_comp` (1-form-pullback composition);
* `ContMDiff` is a `Prop`, so the smoothness witness threading is by
  proof-irrelevance.

Sister to `PeriodPairingMorphism.id'_ofSmoothCycle` on the identity
side; the `(id_ofSmoothCycle, comp_ofSmoothCycle)` pair completes the
functoriality interface for the canonical-cycle-pushforward bundle.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X Y Z : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
  [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ, ℂ) ω Z]

/-- **Composition of `ofSmoothCycle`-style period-pairing morphisms.**

Given two holomorphic curve maps `f : X → Y`, `g : Y → Z` and period
adjunctions for the canonical `SmoothCycle.pushHom` cyclePush on each
side, produce the composite morphism with cyclePush
`SmoothCycle.pushHom (g ∘ f) _` (the canonical form on
`ofSmoothCycle X → ofSmoothCycle Z`). -/
noncomputable def PeriodPairingMorphism.comp_ofSmoothCycle
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g)
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (adj_f :
      ∀ (γ : SmoothCycle 𝓘(ℝ, ℂ) X) (τ : HolomorphicOneForm Y),
        complexPeriod
          (SmoothCycle.pushHom f (ContMDiff.complex_to_real hf) γ) τ
          = complexPeriod γ (HolomorphicOneForm.pullback f hf τ))
    (adj_g :
      ∀ (γ : SmoothCycle 𝓘(ℝ, ℂ) Y) (τ : HolomorphicOneForm Z),
        complexPeriod
          (SmoothCycle.pushHom g (ContMDiff.complex_to_real hg) γ) τ
          = complexPeriod γ (HolomorphicOneForm.pullback g hg τ)) :
    PeriodPairingMorphism (PeriodPairingData.ofSmoothCycle X)
                          (PeriodPairingData.ofSmoothCycle Z) :=
  PeriodPairingMorphism.ofSmoothCycle (g ∘ f) (hg.comp hf) (by
    intro γ τ
    -- Reduce LHS via `SmoothCycle.pushHom_comp`; then chain `adj_g`,
    -- `adj_f`, `HolomorphicOneForm.pullback_comp`. `ContMDiff` is a
    -- `Prop`, so `ContMDiff.complex_to_real (hg.comp hf)` and
    -- `(complex_to_real hg).comp (complex_to_real hf)` are equal by
    -- proof-irrelevance.
    have h_pushHom_comp :
        SmoothCycle.pushHom (g ∘ f)
            (ContMDiff.complex_to_real (hg.comp hf)) γ
          = SmoothCycle.pushHom g (ContMDiff.complex_to_real hg)
              (SmoothCycle.pushHom f
                (ContMDiff.complex_to_real hf) γ) := by
      have h_eq :
          SmoothCycle.pushHom (g ∘ f)
              ((ContMDiff.complex_to_real hg).comp
                (ContMDiff.complex_to_real hf))
            = (SmoothCycle.pushHom g (ContMDiff.complex_to_real hg)).comp
                (SmoothCycle.pushHom f
                  (ContMDiff.complex_to_real hf)) :=
        SmoothCycle.pushHom_comp g (ContMDiff.complex_to_real hg)
          f (ContMDiff.complex_to_real hf)
      -- `ContMDiff` is `Prop`; the two smoothness arguments to
      -- `pushHom (g ∘ f)` are equal by proof-irrelevance, so we can
      -- rewrite and then apply `h_eq` componentwise.
      have :
          SmoothCycle.pushHom (g ∘ f)
              (ContMDiff.complex_to_real (hg.comp hf))
            = SmoothCycle.pushHom (g ∘ f)
                ((ContMDiff.complex_to_real hg).comp
                  (ContMDiff.complex_to_real hf)) := by
        rfl
      rw [this, h_eq]
      rfl
    rw [h_pushHom_comp]
    rw [adj_g (SmoothCycle.pushHom f
                (ContMDiff.complex_to_real hf) γ) τ]
    rw [adj_f γ (HolomorphicOneForm.pullback g hg τ)]
    rw [HolomorphicOneForm.pullback_comp g hg f hf τ])

end JacobianChallenge

end
