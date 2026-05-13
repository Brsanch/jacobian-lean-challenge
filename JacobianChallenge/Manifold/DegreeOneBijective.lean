/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DegreeOneInjective
import JacobianChallenge.Manifold.DegreeOneSurjective

set_option diagnostics.threshold 100

/-! # `degreeFiber f = 1` ⇒ `f` is bijective (conditional)

Composes zz327's injectivity + zz328's surjectivity into a bijection
statement. Both halves are conditional on their respective named open
inputs; this file just merges them.

  bijective_of_degreeFiber_eq_one :
    ramificationSumEqualsDegree_statement X Y →
    Surjective_of_NonConstant_Analytic_Manifold X Y →
    ContMDiff ω f → ¬ IsConstantMap f →
    degreeFiber f hf = 1 →
    Function.Bijective f

This is the bijection content of zz325's DegreeOneIsBiholomorphic_RS.
The remaining step is "bijective + ω-smooth ⇒ ω-smooth inverse"
(inverse function theorem at ramification index 1).

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-- **Bijection from degreeFiber = 1.** Conditional on
`ramificationSumEqualsDegree_statement` (injectivity content from
zz327) + `Surjective_of_NonConstant_Analytic_Manifold` (surjectivity
content from zz328). -/
theorem bijective_of_degreeFiber_eq_one
    (h_RS : JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_statement X Y)
    (h_surj : Surjective_of_NonConstant_Analytic_Manifold X Y)
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f)
    (h_deg : JacobianChallenge.ContMDiff.degreeFiber f hf = 1) :
    Function.Bijective f :=
  ⟨injective_of_degreeFiber_eq_one h_RS hf hnc h_deg, h_surj f hf hnc⟩

end JacobianChallenge

end
