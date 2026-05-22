/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianClassicalContent
import JacobianChallenge.Manifold.SurfaceClassificationDataGenusZero
import JacobianChallenge.Manifold.DefaultHolomorphicOneFormBasis
import JacobianChallenge.Manifold.BasedSmoothLoopsBound

set_option linter.unusedSectionVars false

/-! # `HasJacobianClassicalContent X` under `Subsingleton ω + BSLB`

Generalizes the unconditional `RiemannSphere` HJCC instance to any
compact connected complex 1-manifold `X` with:

* `[Subsingleton (HolomorphicOneForm X)]` — i.e., `genus X = 0`;
* a `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X p₀` witness at some
  base point.

Discharge:
* `genus X = 0` ⟹ both g²-scalar families are vacuous on empty `Fin 0`.
* SCD at genus 0 comes from `SurfaceClassificationData.ofGenusZero
  p₀ (Module.finrank_zero_of_subsingleton) h_bslb`.
* Basis is the `defaultHolomorphicOneFormBasis X` (empty at genus 0).

Applies to any X with the two named hypotheses. RS is the canonical
example; any X with a uniformization `HolomorphicEquiv X RS` plus the
transported BSLB also qualifies.

## What ships

* `HasJacobianClassicalContent.of_subsingleton_and_BSLB` — the route.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasJacobianClassicalContent X` from `Subsingleton ω` + a BSLB
witness.** -/
theorem HasJacobianClassicalContent.of_subsingleton_and_BSLB
    [Subsingleton (HolomorphicOneForm X)]
    (basePoint : X)
    (h_BSLB : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X basePoint) :
    HasJacobianClassicalContent X := by
  have h_genus : JacobianChallenge.genus X = 0 :=
    Module.finrank_zero_of_subsingleton
  haveI : IsEmpty (Fin (JacobianChallenge.genus X)) := by
    rw [h_genus]; exact Fin.isEmpty
  refine ⟨⟨SurfaceClassificationData.ofGenusZero basePoint h_genus h_BSLB,
          defaultHolomorphicOneFormBasis X, ?_, ?_⟩⟩
  · intro i _ _; exact isEmptyElim i
  · intro i _ _; exact isEmptyElim i

end JacobianChallenge

end
