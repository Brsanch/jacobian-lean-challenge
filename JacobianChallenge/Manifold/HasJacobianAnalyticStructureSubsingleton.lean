/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianAnalyticStructure
import JacobianChallenge.Manifold.SmoothHomologyDataPackageSubsingleton

set_option linter.unusedSectionVars false

/-! # `HasJacobianAnalyticStructure X` under `Subsingleton ω + BSLB`

Generalizes the `RiemannSphere` instance of
`HasJacobianAnalyticStructure` to any compact connected complex
1-manifold `X` with:

* `[Subsingleton (HolomorphicOneForm X)]` — i.e., `genus X = 0`.
* A `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X p₀` witness at some
  base point `p₀`.

Under these hypotheses, the `SmoothHomologyDataPackage` is produced via
`smoothHomologyDataPackage_of_subsingleton_and_BSLB`, and the
existential introduction gives `HasJacobianAnalyticStructure X`.

This is the *non-RiemannSphere* genus-0 route — applies to any X with
the two named hypotheses, not just RS. RS is the canonical example;
other examples would be any X with a uniformization theorem
(`HolomorphicEquiv X RS`) plus the RS instance transported along.

## What this file ships

* `HasJacobianAnalyticStructure.of_subsingleton_and_BSLB` — the route.
* No `instance` is registered (the BSLB witness is data, not a class).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasJacobianAnalyticStructure X` from `Subsingleton ω` + a BSLB
witness.** Any compact connected complex 1-manifold with subsingleton
holomorphic one-forms and a `BasedSmoothLoopsBoundHypothesis` at some
base point has the analytic-Jacobian structure.

Generalizes the `RiemannSphere` discharge — applies to any X meeting
both named hypotheses. -/
theorem HasJacobianAnalyticStructure.of_subsingleton_and_BSLB
    [Subsingleton (HolomorphicOneForm X)]
    (basePoint : X)
    (h_BSLB : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X basePoint) :
    HasJacobianAnalyticStructure X := by
  refine ⟨⟨defaultHolomorphicOneFormBasis X, ?_⟩⟩
  exact ⟨smoothHomologyDataPackage_of_subsingleton_and_BSLB
    (defaultHolomorphicOneFormBasis X) basePoint h_BSLB⟩

end JacobianChallenge

end
