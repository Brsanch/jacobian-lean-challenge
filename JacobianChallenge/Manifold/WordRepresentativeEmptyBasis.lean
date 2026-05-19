/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothBordismAndWordRepresentative
import JacobianChallenge.Manifold.SmoothHurewiczHypothesisRiemannSphere
import JacobianChallenge.Manifold.BasedSmoothLoopsBound

set_option linter.unusedSectionVars false

/-! # `WordRepresentativeHypothesis` for the empty basis (genus 0)

At genus `g = 0`, a `SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ 0` has the
empty tuple `Fin (2*0) = Fin 0 → SmoothPath I X` as `basis`, and the
canonical product loop `basisProductLoop sb n` for any
`n : Fin 0 → ℤ` reduces to `SmoothPath.const I X p₀` (the empty `wordLoop`
is `const p₀`).

Word-representability at the empty basis then says: *every smooth based
loop `γ` at `p₀` is `SmoothBordant` to `const p₀`* — equivalently,
`γ.singleCycle - (const p₀).singleCycle ∈ stokesBoundaries`.

Both terms are in `stokesBoundaries` individually:
* `(const p₀).singleCycle ∈ stokesBoundaries` (existing chip
  `single_smoothPath_const_smoothCycle_mem_stokesBoundaries`).
* `γ.singleCycle ∈ stokesBoundaries` is the conclusion of
  `BasedSmoothLoopsBoundHypothesis I X p₀` applied to `γ`.

Their difference therefore lies in `stokesBoundaries`, discharging
word-representability at the empty basis.

## What this file ships

* `wordRepresentativeHypothesis_emptyBasis_of_basedSmoothLoopsBound` —
  for any compact connected complex 1-manifold X with
  `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X p₀`, the
  `WordRepresentativeHypothesis` on the empty symplectic basis holds.
* `wordRepresentativeHypothesis_RiemannSphere_emptyBasis_holds` —
  `RiemannSphere` corollary, unconditional via
  `basedSmoothLoopsBoundHypothesis_RS_holds`.
* `smoothHurewiczHypothesis_RiemannSphere_via_wordRep` — parallel
  route to `smoothHurewiczHypothesis_RiemannSphere_holds`, going
  through the new bordism+word-rep factoring rather than the direct
  empty-basis discharge.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-! ## Empty-basis `basisProductLoop` is `const p₀` -/

/-- For an empty symplectic basis and any (vacuous) tuple
`n : Fin (2*0) → ℤ`, the canonical product loop is the constant loop
at `p₀`. -/
lemma basisProductLoop_emptyBasis (p₀ : X)
    (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ 0) (n : Fin (2 * 0) → ℤ) :
    (basisProductLoop sb n).toPath = SmoothPath.const 𝓘(ℝ, ℂ) X p₀ := by
  -- `basisProductLoop sb n = wordLoop p₀ (List.ofFn (fun i => ...))`
  -- with `Fin (2*0) = Fin 0` empty, so `List.ofFn = []` and
  -- `wordLoop p₀ [] = const p₀` by definition.
  show (wordLoop p₀
        (List.ofFn (fun i : Fin (2 * 0) => (n i, BasedLoopAt.ofBasis sb i)))).toPath
      = SmoothPath.const 𝓘(ℝ, ℂ) X p₀
  have h_empty : (List.ofFn (fun i : Fin (2 * 0) =>
        (n i, BasedLoopAt.ofBasis sb i))) = [] := by
    rw [List.ofFn_eq_nil_iff]
  rw [h_empty]
  rfl

/-! ## `(const p₀).singleCycle` as a `BasedLoopAt.singleCycle` -/

/-- Wrap `SmoothPath.const I X p₀` as a `BasedLoopAt`. -/
noncomputable def constBasedLoopAt (p₀ : X) : BasedLoopAt 𝓘(ℝ, ℂ) X p₀ :=
  ⟨SmoothPath.const 𝓘(ℝ, ℂ) X p₀,
    ⟨SmoothPath.const_src p₀, SmoothPath.const_tgt p₀⟩⟩

@[simp] lemma constBasedLoopAt_toPath (p₀ : X) :
    (constBasedLoopAt p₀).toPath = SmoothPath.const 𝓘(ℝ, ℂ) X p₀ := rfl

/-- The `singleCycle` of `constBasedLoopAt p₀` equals
`single_smoothPath_const_smoothCycle p₀`. -/
lemma constBasedLoopAt_singleCycle (p₀ : X) :
    (constBasedLoopAt p₀).singleCycle
      = single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := X) p₀ := by
  apply Subtype.ext
  rw [BasedLoopAt.singleCycle_coe, single_smoothPath_const_smoothCycle_coe]
  rfl

/-! ## Empty-basis word-representative discharge -/

/-- **Empty-basis `WordRepresentativeHypothesis` from
`BasedSmoothLoopsBoundHypothesis`.** -/
theorem wordRepresentativeHypothesis_emptyBasis_of_basedSmoothLoopsBound
    (p₀ : X) (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ 0)
    (h_bound : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X p₀) :
    WordRepresentativeHypothesis sb := by
  intro γ h_src h_tgt
  -- Vacuous `n : Fin 0 → ℤ`.
  haveI : IsEmpty (Fin (2 * 0)) := by rw [Nat.mul_zero]; infer_instance
  refine ⟨Fin.elim0, ?_⟩
  -- Need: SmoothBordant ⟨γ, _⟩ (basisProductLoop sb Fin.elim0)
  -- Equivalently: γ.singleCycle - (basisProductLoop sb Fin.elim0).singleCycle ∈ stokes.
  -- (basisProductLoop sb Fin.elim0).toPath = const p₀ (by basisProductLoop_emptyBasis).
  -- So (basisProductLoop sb Fin.elim0).singleCycle = single_smoothPath_const_smoothCycle p₀.
  unfold SmoothBordant
  -- Step 1: identify (basisProductLoop sb Fin.elim0).singleCycle with const_smoothCycle.
  have h_bpl_sing :
      (basisProductLoop sb Fin.elim0).singleCycle
        = single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := X) p₀ := by
    apply Subtype.ext
    rw [BasedLoopAt.singleCycle_coe, single_smoothPath_const_smoothCycle_coe]
    rw [basisProductLoop_emptyBasis p₀ sb Fin.elim0]
  rw [h_bpl_sing]
  -- Step 2: γ_bl.singleCycle = single_smoothLoop_smoothCycle γ (...).
  let γ_bl : BasedLoopAt 𝓘(ℝ, ℂ) X p₀ := ⟨γ, ⟨h_src, h_tgt⟩⟩
  show γ_bl.singleCycle - single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) p₀
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) X
  have h_γ_sing :
      γ_bl.singleCycle
        = single_smoothLoop_smoothCycle γ (h_src.trans h_tgt.symm) := by
    apply Subtype.ext
    rw [BasedLoopAt.singleCycle_coe, single_smoothLoop_smoothCycle_coe]
    rfl
  rw [h_γ_sing]
  -- Step 3: both single_smoothLoop_smoothCycle γ ∈ stokes (from h_bound)
  -- and single_smoothPath_const_smoothCycle p₀ ∈ stokes (existing).
  have h_γ_in : single_smoothLoop_smoothCycle γ (h_src.trans h_tgt.symm)
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) X :=
    h_bound γ h_src h_tgt
  have h_const_in :
      single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := X) p₀
        ∈ stokesBoundaries 𝓘(ℝ, ℂ) X :=
    single_smoothPath_const_smoothCycle_mem_stokesBoundaries p₀
  exact AddSubgroup.sub_mem _ h_γ_in h_const_in

/-! ## `RiemannSphere` discharge: unconditional -/

namespace RiemannSphere

/-- **Empty-basis `WordRepresentativeHypothesis` on `RiemannSphere`,
unconditional.** Composes the generic discharge with the unconditional
`basedSmoothLoopsBoundHypothesis_RS_holds`. -/
theorem wordRepresentativeHypothesis_emptyBasis_RiemannSphere_holds
    (p₀ : RiemannSphere) :
    WordRepresentativeHypothesis (emptySymplecticBasis p₀) :=
  wordRepresentativeHypothesis_emptyBasis_of_basedSmoothLoopsBound p₀
    (emptySymplecticBasis p₀) (basedSmoothLoopsBoundHypothesis_RS_holds p₀)

/-- **`SmoothHurewiczHypothesis` on `RiemannSphere` via the new
bordism + word-rep factoring (parallel route).** Composes
`smoothHurewiczHypothesis_of_wordRepresentative` with the
empty-basis word-rep discharge. -/
theorem smoothHurewiczHypothesis_RiemannSphere_via_wordRep
    (p₀ : RiemannSphere) :
    SmoothHurewiczHypothesis (emptySymplecticBasis p₀) :=
  smoothHurewiczHypothesis_of_wordRepresentative
    (wordRepresentativeHypothesis_emptyBasis_RiemannSphere_holds p₀)

end RiemannSphere

end JacobianChallenge

end
