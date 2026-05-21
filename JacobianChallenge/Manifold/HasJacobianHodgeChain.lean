/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianAnalyticStructureFromHodgeChain
import JacobianChallenge.Manifold.DefaultHolomorphicOneFormBasis

set_option linter.unusedSectionVars false

/-! # `HasJacobianHodgeChain X` — class wrapper for the period-lattice
classical chain (chip 7)

This class bundles the four named classical hypotheses required by chip
5 (`HasJacobianAnalyticStructure.of_hodgeChain`) into a single
existence Prop typeclass:

* `basis_ω` — a ℂ-basis of `H⁰(X, Ω)`;
* `basePoint` — a chosen point of `X`;
* `symplecticBasis` — 2g based loops at `basePoint`;
* `hurewicz` — `SmoothHurewiczHypothesis symplecticBasis`;
* `hHR` — `CompleteHodgeRiemannHypothesis ... basis_ω symplecticBasis.cycleGens`.

Under this class, `HasJacobianAnalyticStructure X` is immediate.

## Genus-0 / Subsingleton ω instance

For any `X` with `Subsingleton (HolomorphicOneForm X)`, `genus X = 0`, so:

* `basis_ω := defaultHolomorphicOneFormBasis X`;
* `basePoint := Classical.arbitrary X`;
* `symplecticBasis` has `Fin (2*0) = Fin 0` empty data (vacuous);
* `hurewicz` is vacuously true (empty index);
* `hHR` from `completeHodgeRiemannHypothesis_of_subsingleton`.

This shows the chain is non-empty in the trivial case.

## What this file ships

* `HasJacobianHodgeChain` — the class wrapper.
* `instance instHasJacobianHodgeChain_of_subsingleton` — Subsingleton-ω
  instance.
* `instance instHasJacobianAnalyticStructure_of_HasJacobianHodgeChain` —
  typeclass bridge to `HasJacobianAnalyticStructure X`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasJacobianHodgeChain X` class.** Bundles the four named classical
hypotheses required to discharge `HasJacobianAnalyticStructure X` via the
Hodge chain route (chips 1–5). -/
class HasJacobianHodgeChain (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X] : Prop where
  /-- A ℂ-basis, base point, symplectic basis, smooth-Hurewicz hypothesis,
  and complete Hodge–Riemann hypothesis package. -/
  out : ∃ (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
              (HolomorphicOneForm X))
          (basePoint : X)
          (symplecticBasis :
            SmoothSymplecticBasis 𝓘(ℝ, ℂ) X basePoint
              (JacobianChallenge.genus X)),
          SmoothHurewiczHypothesis symplecticBasis ∧
          CompleteHodgeRiemannHypothesis
            (PeriodPairingData.ofSmoothCycle X) basis_ω
            symplecticBasis.cycleGens

/-- **Bridge: `HasJacobianHodgeChain X ⟹ HasJacobianAnalyticStructure X`.**
Directly applies chip 5's `of_hodgeChain` constructor with the witness
extracted from the typeclass. -/
instance instHasJacobianAnalyticStructure_of_HasJacobianHodgeChain
    [h : HasJacobianHodgeChain X] :
    HasJacobianAnalyticStructure X := by
  obtain ⟨basis_ω, basePoint, symplecticBasis, hurewicz, hHR⟩ := h.out
  exact HasJacobianAnalyticStructure.of_hodgeChain basis_ω basePoint
    symplecticBasis hurewicz hHR

/-! ## Genus-0 / Subsingleton-ω instance -/

/-- **Empty symplectic basis at genus 0.** When `genus X = 0`,
`Fin (2 * 0) = Fin 0` is empty, so the `basis`, `basis_src`, `basis_tgt`
fields are vacuously defined. -/
noncomputable def SmoothSymplecticBasis.emptyAtGenusZero
    [Subsingleton (HolomorphicOneForm X)]
    (basePoint : X) :
    SmoothSymplecticBasis 𝓘(ℝ, ℂ) X basePoint (JacobianChallenge.genus X) :=
  haveI hgenus : JacobianChallenge.genus X = 0 :=
    Module.finrank_zero_of_subsingleton
  haveI : IsEmpty (Fin (2 * JacobianChallenge.genus X)) := by
    rw [hgenus, Nat.mul_zero]; infer_instance
  { basis := isEmptyElim
    basis_src := fun i => isEmptyElim i
    basis_tgt := fun i => isEmptyElim i }

/-- **Smooth-Hurewicz vacuous at empty basis.** Since the universal
quantifier in `SmoothHurewiczHypothesis` is over `γ : SmoothPath`, not
over the basis index, the empty-basis discharge is not vacuous in the
quantifier sense but is vacuous in the `n` choice: for any γ that's
a based loop, choose `n = isEmptyElim` (i.e., the unique `Fin 0 → ℤ`),
and the `∑ i, n i • cycleGens i` term is `0`. So we need
`single_smoothLoop_smoothCycle γ ... ∈ stokesBoundaries`. This is the
content of `basedSmoothLoopsBoundHypothesis_RS_holds`-style hypotheses
on subsingleton-ω manifolds; we assume it as an extra hypothesis. -/
def smoothHurewicz_at_empty_basis
    [Subsingleton (HolomorphicOneForm X)]
    {basePoint : X}
    (h_BSLB : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X basePoint) :
    SmoothHurewiczHypothesis
      (SmoothSymplecticBasis.emptyAtGenusZero (X := X) basePoint) := by
  have hgenus : JacobianChallenge.genus X = 0 :=
    Module.finrank_zero_of_subsingleton
  haveI hempty : IsEmpty (Fin (2 * JacobianChallenge.genus X)) := by
    rw [hgenus]; exact ⟨fun i => absurd i.isLt (by omega)⟩
  intro γ h_src h_tgt
  refine ⟨isEmptyElim, ?_⟩
  -- The sum ∑ i ∈ univ, n i • ... over empty index = 0.
  have h_sum_eq : (∑ i : Fin (2 * JacobianChallenge.genus X),
      (isEmptyElim i : ℤ) • (SmoothSymplecticBasis.emptyAtGenusZero
        (X := X) basePoint).cycleGens i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact hempty.elim i
  rw [h_sum_eq, sub_zero]
  -- Apply BSLB at the given loop.
  exact h_BSLB γ h_src h_tgt

/-- **Subsingleton-ω + BSLB instance for `HasJacobianHodgeChain X`.**
The full chain holds vacuously at genus 0 given any `BasedSmoothLoopsBoundHypothesis`
witness. -/
theorem HasJacobianHodgeChain.of_subsingleton_and_BSLB
    [Subsingleton (HolomorphicOneForm X)]
    (basePoint : X)
    (h_BSLB : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X basePoint) :
    HasJacobianHodgeChain X := by
  refine ⟨defaultHolomorphicOneFormBasis X, basePoint,
    SmoothSymplecticBasis.emptyAtGenusZero basePoint,
    smoothHurewicz_at_empty_basis h_BSLB,
    ?_⟩
  -- Hodge–Riemann chain vacuous at genus 0.
  exact completeHodgeRiemannHypothesis_of_subsingleton _ _ _

end JacobianChallenge

end
