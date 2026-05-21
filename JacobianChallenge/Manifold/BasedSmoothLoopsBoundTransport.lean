/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.BasedSmoothLoopsBound
import JacobianChallenge.Manifold.HolomorphicEquiv
import JacobianChallenge.Manifold.ContMDiffRealification
import JacobianChallenge.Manifold.SmoothCyclePushComp
import JacobianChallenge.Manifold.SmoothCyclePushId
import JacobianChallenge.Manifold.Smooth2SimplexPush

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # `BasedSmoothLoopsBoundHypothesis` transports across a biholomorphism

For a biholomorphism `φ : HolomorphicEquiv X Y` (analytic in both
directions) and a base point `p₀ ∈ X`, the hypothesis

  `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X p₀`

transports to

  `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) Y (φ p₀)`.

Strategy:

1. **Realification**: `HolomorphicEquiv` gives `ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ)
   ω` smoothness on both directions. The `ContMDiff.complex_to_real`
   bridge upgrades each to `ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞`.
2. **Pull a Y-loop back to X**: given `γ : SmoothPath 𝓘(ℝ,ℂ) Y` based
   at `φ p₀`, pull it back via `SmoothPath.push (φ.symm) ...` to a
   `γ_X : SmoothPath 𝓘(ℝ,ℂ) X` based at `p₀` (using
   `Equiv.symm_apply_apply p₀ : φ.symm (φ p₀) = p₀`).
3. **Apply BSLB on X**: `single γ_X ∈ stokesBoundaries X`.
4. **Push the cycle forward via φ**: `SmoothCycle.pushHom φ` sends
   stokesBoundaries to stokesBoundaries (`stokesBoundaries_push`).
5. **Round-trip identity**: the pushed cycle equals `single γ`. Use
   `SmoothCycle.pushHom_comp` to combine the two pushes into
   `SmoothCycle.pushHom (φ ∘ φ.symm) = SmoothCycle.pushHom id`
   (`Equiv.self_comp_symm`) `= AddMonoidHom.id` (`SmoothCycle.pushHom_id`).

Net contribution: substantive uniformization-adjacent transport
content. Combined with chip 26's `SurfaceClassificationData.ofGenusZero`,
gives `HSCD Y` (and hence the C3 umbrella on Y) for any Y biholomorphic
to RS, conditional on the biholomorphism. The uniformization theorem
at genus 0 (any compact connected complex 1-manifold of genus 0 is
biholomorphic to RS) remains the open named atom — but this chip
factors it as the *single* missing piece.

## What this file ships

* `basedSmoothLoopsBoundHypothesis_pushforward_biholomorphism` —
  BSLB transport across a `HolomorphicEquiv`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

/-- **BSLB transports across a biholomorphism.**

For a biholomorphism `φ : HolomorphicEquiv X Y` and base point
`p₀ : X`, if every smooth based loop at `p₀` on `X` lies in
`stokesBoundaries`, then every smooth based loop at `φ p₀` on `Y`
also lies in `stokesBoundaries`. -/
theorem basedSmoothLoopsBoundHypothesis_pushforward_biholomorphism
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    (φ : HolomorphicEquiv X Y) (p₀ : X)
    (h_bslb : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X p₀) :
    BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) Y (φ.toEquiv p₀) := by
  -- Real-smooth witnesses for φ and φ.symm via the complex-to-real bridge.
  have h_φ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (φ.toEquiv : X → Y) :=
    ContMDiff.complex_to_real φ.contMDiff_forward
  have h_φsymm : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (φ.toEquiv.symm : Y → X) :=
    ContMDiff.complex_to_real φ.contMDiff_inverse
  intro γ h_src h_tgt
  -- Pull γ back to X via φ.symm.
  set γ_X : SmoothPath 𝓘(ℝ, ℂ) X :=
    SmoothPath.push (φ.toEquiv.symm : Y → X) h_φsymm γ with hγ_X_def
  -- γ_X is based at p₀ (since φ.symm (φ p₀) = p₀).
  have h_γX_src : γ_X.src = p₀ := by
    show (φ.toEquiv.symm : Y → X) γ.src = p₀
    rw [h_src]
    exact φ.toEquiv.symm_apply_apply p₀
  have h_γX_tgt : γ_X.tgt = p₀ := by
    show (φ.toEquiv.symm : Y → X) γ.tgt = p₀
    rw [h_tgt]
    exact φ.toEquiv.symm_apply_apply p₀
  -- Apply BSLB on X to γ_X.
  have h_X :
      single_smoothLoop_smoothCycle γ_X (h_γX_src.trans h_γX_tgt.symm)
        ∈ stokesBoundaries 𝓘(ℝ, ℂ) X :=
    h_bslb γ_X h_γX_src h_γX_tgt
  -- Push the X-cycle forward via φ.
  have h_pushed :
      SmoothCycle.pushHom (φ.toEquiv : X → Y) h_φ
          (single_smoothLoop_smoothCycle γ_X
            (h_γX_src.trans h_γX_tgt.symm))
        ∈ stokesBoundaries 𝓘(ℝ, ℂ) Y :=
    stokesBoundaries_push (φ.toEquiv : X → Y) h_φ _ h_X
  -- Round-trip identity at the path level:
  -- `SmoothPath.push φ (SmoothPath.push φ.symm γ) = γ`.
  have h_path :
      SmoothPath.push (φ.toEquiv : X → Y) h_φ γ_X = γ := by
    rw [hγ_X_def]
    rw [← SmoothPath.push_comp (φ.toEquiv : X → Y) h_φ
        (φ.toEquiv.symm : Y → X) h_φsymm γ]
    have h_comp_eq :
        ((φ.toEquiv : X → Y) ∘ (φ.toEquiv.symm : Y → X)) = (id : Y → Y) := by
      funext y
      exact φ.toEquiv.apply_symm_apply y
    -- Use `congr` to replace the composition with `id` via `h_comp_eq`.
    -- Smoothness witnesses are propositional (`ContMDiff` is a `Prop`),
    -- so `Subsingleton.elim` closes the witness side.
    have h_push_eq :
        SmoothPath.push ((φ.toEquiv : X → Y) ∘ (φ.toEquiv.symm : Y → X))
            (h_φ.comp h_φsymm) γ
          = SmoothPath.push (id : Y → Y) contMDiff_id γ := by
      congr 1
    rw [h_push_eq, SmoothPath.push_id γ]
  -- Cycle-level identity: the pushed cycle equals `single γ`.
  have h_eq :
      SmoothCycle.pushHom (φ.toEquiv : X → Y) h_φ
          (single_smoothLoop_smoothCycle γ_X
            (h_γX_src.trans h_γX_tgt.symm))
        = single_smoothLoop_smoothCycle γ (h_src.trans h_tgt.symm) := by
    apply Subtype.ext
    change SmoothChain.push (φ.toEquiv : X → Y) h_φ
            (single_smoothLoop_smoothCycle γ_X
              (h_γX_src.trans h_γX_tgt.symm) : SmoothChain 𝓘(ℝ, ℂ) X)
        = (single_smoothLoop_smoothCycle γ (h_src.trans h_tgt.symm)
            : SmoothChain 𝓘(ℝ, ℂ) Y)
    rw [single_smoothLoop_smoothCycle_coe γ_X
          (h_γX_src.trans h_γX_tgt.symm),
        single_smoothLoop_smoothCycle_coe γ (h_src.trans h_tgt.symm),
        SmoothChain.push_single, h_path]
  rw [h_eq] at h_pushed
  exact h_pushed

end JacobianChallenge

end
