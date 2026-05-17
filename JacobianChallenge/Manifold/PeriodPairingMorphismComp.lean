/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodPairingMorphism
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackComp

set_option linter.unusedSectionVars false

/-! # Composition functoriality of `PeriodPairingMorphism`

For three compact connected complex 1-manifolds `X`, `Y`, `Z` with
period-pairing data, the composition of two `PeriodPairingMorphism`s
is again a `PeriodPairingMorphism`:

  `PeriodPairingMorphism data_Y data_Z → PeriodPairingMorphism data_X data_Y`
    `→ PeriodPairingMorphism data_X data_Z`

Curve map composes as `g ∘ f`; cycle pushforward composes as
`AddMonoidHom.comp`. The adjunction
`∫_{f_*γ} τ = ∫_γ (f^* τ)` composes via the dual `pullback_comp`:

  `pairing_Z ((cyclePush_g.comp cyclePush_f) γ) τ`
  `= pairing_Y (cyclePush_f γ) (pullback g τ)`           [adj_g]
  `= pairing_X γ (pullback f (pullback g τ))`             [adj_f]
  `= pairing_X γ (pullback (g ∘ f) τ)`                    [pullback_comp]

This is the sister statement to `PeriodPairingMorphism.id` (identity
functoriality) and underwrites every subsequent composition of
period-adjunction bundles in the Jacobian pullback/pushforward arc.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X Y Z : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
  [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ, ℂ) ω Z]

/-- **Composition of period-pairing morphisms.** Given
`morph_g : PeriodPairingMorphism data_Y data_Z` and
`morph_f : PeriodPairingMorphism data_X data_Y`, produce
`morph_gf : PeriodPairingMorphism data_X data_Z` with the curve map
`g ∘ f` and cycle pushforward `cyclePush_g.comp cyclePush_f`. -/
noncomputable def PeriodPairingMorphism.comp
    {data_X : PeriodPairingData X}
    {data_Y : PeriodPairingData Y}
    {data_Z : PeriodPairingData Z}
    (morph_g : PeriodPairingMorphism data_Y data_Z)
    (morph_f : PeriodPairingMorphism data_X data_Y) :
    PeriodPairingMorphism data_X data_Z where
  f := morph_g.f ∘ morph_f.f
  contMDiff_f := morph_g.contMDiff_f.comp morph_f.contMDiff_f
  cyclePush := morph_g.cyclePush.comp morph_f.cyclePush
  adjunction := by
    intro γ τ
    -- LHS: data_Z.pairing (cyclePush_g (cyclePush_f γ)) τ.
    show data_Z.pairing (morph_g.cyclePush (morph_f.cyclePush γ)) τ
      = data_X.pairing γ
          (HolomorphicOneForm.pullback (morph_g.f ∘ morph_f.f)
            (morph_g.contMDiff_f.comp morph_f.contMDiff_f) τ)
    -- Apply `morph_g`'s adjunction: pairing_Z on `cyclePush_g · ` becomes
    -- pairing_Y on the pullback under `g`.
    rw [morph_g.adjunction (morph_f.cyclePush γ) τ]
    -- Apply `morph_f`'s adjunction: pairing_Y on `cyclePush_f γ` becomes
    -- pairing_X on the pullback under `f`.
    rw [morph_f.adjunction γ
          (HolomorphicOneForm.pullback morph_g.f morph_g.contMDiff_f τ)]
    -- Combine the two pullbacks via `pullback_comp`.
    rw [HolomorphicOneForm.pullback_comp morph_g.f morph_g.contMDiff_f
          morph_f.f morph_f.contMDiff_f τ]

@[simp] theorem PeriodPairingMorphism.comp_f
    {data_X : PeriodPairingData X}
    {data_Y : PeriodPairingData Y}
    {data_Z : PeriodPairingData Z}
    (morph_g : PeriodPairingMorphism data_Y data_Z)
    (morph_f : PeriodPairingMorphism data_X data_Y) :
    (morph_g.comp morph_f).f = morph_g.f ∘ morph_f.f := rfl

@[simp] theorem PeriodPairingMorphism.comp_cyclePush
    {data_X : PeriodPairingData X}
    {data_Y : PeriodPairingData Y}
    {data_Z : PeriodPairingData Z}
    (morph_g : PeriodPairingMorphism data_Y data_Z)
    (morph_f : PeriodPairingMorphism data_X data_Y) :
    (morph_g.comp morph_f).cyclePush
      = morph_g.cyclePush.comp morph_f.cyclePush := rfl

end JacobianChallenge

end
