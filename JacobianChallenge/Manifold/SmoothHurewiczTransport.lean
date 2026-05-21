/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothHurewiczHypothesis
import JacobianChallenge.Manifold.HolomorphicEquiv
import JacobianChallenge.Manifold.ContMDiffRealification
import JacobianChallenge.Manifold.SmoothCyclePushComp
import JacobianChallenge.Manifold.SmoothCyclePushId
import JacobianChallenge.Manifold.Smooth2SimplexPush

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # `SmoothHurewiczHypothesis` transports across a biholomorphism

For a biholomorphism `φ : HolomorphicEquiv X Y` and a smooth
symplectic basis `sb_X : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ g`,
define the pushed symplectic basis

  `sb_X.push φ : SmoothSymplecticBasis 𝓘(ℝ, ℂ) Y (φ p₀) g`

by pushing each basis path via `SmoothPath.push φ`. Then
`SmoothHurewiczHypothesis sb_X` transports to
`SmoothHurewiczHypothesis (sb_X.push φ)`.

Strategy mirrors chip 28's BSLB transport but operates at the
genus-`g` level — the ℤ-combination structure transports because
`SmoothCycle.pushHom φ` is an `AddMonoidHom` (linearity over `ℤ`).

## What this file ships

* `SmoothSymplecticBasis.push` — pushed symplectic basis (definition).
* `SmoothSymplecticBasis.push_cycleGens` — cycleGens functoriality.
* `smoothHurewiczHypothesis_pushforward_biholomorphism` — transport
  theorem.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u v

namespace SmoothSymplecticBasis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type u} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]
  {Y : Type v} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ⊤ Y]

/-- **Pushforward of a smooth symplectic basis along a smooth map.**
For `f : X → Y` smooth and `sb : SmoothSymplecticBasis I X p₀ g`, the
pushed basis `sb.push f hf : SmoothSymplecticBasis I Y (f p₀) g` has
each loop pushed via `SmoothPath.push`. -/
noncomputable def push {p₀ : X} {g : ℕ}
    (f : X → Y) (hf : ContMDiff I I ∞ f)
    (sb : SmoothSymplecticBasis I X p₀ g) :
    SmoothSymplecticBasis I Y (f p₀) g where
  basis := fun i => SmoothPath.push f hf (sb.basis i)
  basis_src := fun i => by
    rw [SmoothPath.push_src]
    exact congrArg f (sb.basis_src i)
  basis_tgt := fun i => by
    rw [SmoothPath.push_tgt]
    exact congrArg f (sb.basis_tgt i)

/-- **Functoriality of `cycleGens` under `push`.** The cycle generators
of the pushed symplectic basis are the pushforward of the original
cycle generators. -/
theorem push_cycleGens {p₀ : X} {g : ℕ}
    (f : X → Y) (hf : ContMDiff I I ∞ f)
    (sb : SmoothSymplecticBasis I X p₀ g) (i : Fin (2 * g)) :
    (sb.push f hf).cycleGens i
      = SmoothCycle.pushHom f hf (sb.cycleGens i) := by
  apply Subtype.ext
  change SmoothChain.single (SmoothPath.push f hf (sb.basis i))
      = SmoothChain.push f hf
          (single_smoothLoop_smoothCycle (sb.basis i)
            (sb.basis_is_loop i) : SmoothChain I X)
  rw [single_smoothLoop_smoothCycle_coe, SmoothChain.push_single]

end SmoothSymplecticBasis

/-- **SmoothHurewicz transports across a biholomorphism.**

For a biholomorphism `φ : HolomorphicEquiv X Y`, a smooth symplectic
basis `sb_X` on X at p₀, and `SmoothHurewiczHypothesis sb_X`, the
transported hypothesis `SmoothHurewiczHypothesis (sb_X.push φ)` holds
on Y at `φ p₀`. -/
theorem smoothHurewiczHypothesis_pushforward_biholomorphism
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    (φ : HolomorphicEquiv X Y)
    {p₀ : X} {g : ℕ}
    (sb_X : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ g)
    (h_hurewicz : SmoothHurewiczHypothesis sb_X) :
    SmoothHurewiczHypothesis
      (sb_X.push (φ.toEquiv : X → Y)
        (ContMDiff.complex_to_real φ.contMDiff_forward)) := by
  have h_φ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (φ.toEquiv : X → Y) :=
    ContMDiff.complex_to_real φ.contMDiff_forward
  have h_φsymm : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (φ.toEquiv.symm : Y → X) :=
    ContMDiff.complex_to_real φ.contMDiff_inverse
  intro γ h_src h_tgt
  -- Pull γ back to X via φ.symm.
  set γ_X : SmoothPath 𝓘(ℝ, ℂ) X :=
    SmoothPath.push (φ.toEquiv.symm : Y → X) h_φsymm γ with hγ_X_def
  -- γ_X is based at p₀.
  have h_γX_src : γ_X.src = p₀ := by
    show (φ.toEquiv.symm : Y → X) γ.src = p₀
    rw [h_src]
    exact φ.toEquiv.symm_apply_apply p₀
  have h_γX_tgt : γ_X.tgt = p₀ := by
    show (φ.toEquiv.symm : Y → X) γ.tgt = p₀
    rw [h_tgt]
    exact φ.toEquiv.symm_apply_apply p₀
  -- Apply SmoothHurewicz on X.
  obtain ⟨n, h_X⟩ := h_hurewicz γ_X h_γX_src h_γX_tgt
  -- Same integer coefficients for the Y-side.
  refine ⟨n, ?_⟩
  -- Push the entire X-side cycle (single γ_X - ∑ n_i • cycleGens_X i)
  -- forward via φ. AddMonoidHom-linearity propagates the ℤ-combination.
  have h_pushed :
      SmoothCycle.pushHom (φ.toEquiv : X → Y) h_φ
          (single_smoothLoop_smoothCycle γ_X
            (h_γX_src.trans h_γX_tgt.symm) - ∑ i, n i • sb_X.cycleGens i)
        ∈ stokesBoundaries 𝓘(ℝ, ℂ) Y :=
    stokesBoundaries_push (φ.toEquiv : X → Y) h_φ _ h_X
  -- Identify the pushed cycle on the Y side.
  -- Step 1: round-trip path identity.
  have h_path :
      SmoothPath.push (φ.toEquiv : X → Y) h_φ γ_X = γ := by
    rw [hγ_X_def]
    rw [← SmoothPath.push_comp (φ.toEquiv : X → Y) h_φ
        (φ.toEquiv.symm : Y → X) h_φsymm γ]
    have h_comp_eq :
        ((φ.toEquiv : X → Y) ∘ (φ.toEquiv.symm : Y → X)) = (id : Y → Y) := by
      funext y
      exact φ.toEquiv.apply_symm_apply y
    have h_push_eq :
        SmoothPath.push ((φ.toEquiv : X → Y) ∘ (φ.toEquiv.symm : Y → X))
            (h_φ.comp h_φsymm) γ
          = SmoothPath.push (id : Y → Y) contMDiff_id γ := by
      congr 1
    rw [h_push_eq, SmoothPath.push_id γ]
  -- Step 2: cycle-level identity for the single loop.
  have h_single_eq :
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
  -- Step 3: linearity — push of subtraction = subtraction of pushes,
  -- push of finset sum = finset sum of pushes, push of zsmul = zsmul of push.
  have h_sum_eq :
      SmoothCycle.pushHom (φ.toEquiv : X → Y) h_φ
          (∑ i, n i • sb_X.cycleGens i)
        = ∑ i, n i •
          (sb_X.push (φ.toEquiv : X → Y) h_φ).cycleGens i := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_zsmul, SmoothSymplecticBasis.push_cycleGens]
  rw [map_sub, h_single_eq, h_sum_eq] at h_pushed
  exact h_pushed

end JacobianChallenge

end
