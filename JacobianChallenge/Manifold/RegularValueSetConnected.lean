/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphere
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Constructions

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Preconnectedness of the regular-value set on the Riemann sphere

For `f : MeromorphicNonzero X` on a compact connected complex 1-manifold,
the pole-extension `f̃ : X → RiemannSphere` is a finite branched cover
whose critical-value set `C ⊆ RiemannSphere = OnePoint ℂ` is finite.
The **regular-value set** is `Y_reg := (OnePoint ℂ) \ C`. The downstream
theorem `fibreSum_globallyConstant_on_Y_reg`
(`Manifold/FibreSumGloballyConstant.lean`) requires
`IsPreconnected (Set.univ : Set Y_reg)`, i.e. preconnectedness of the
subtype.

This file packages the **purely topological reduction** from "subtype
preconnected" to "ambient set preconnected", and then to the standard
topological fact

  `(OnePoint ℂ) \ S` is preconnected for any finite `S : Set (OnePoint ℂ)`,

which we phrase explicitly. The mathematical content (that the sphere
minus finitely many points is path-connected) is named
`onepoint_complex_diff_finite_isPreconnected` and is taken as a clean
hypothesis at the boundary between this chip and the larger surface
topology / sphere-path-connectedness API.

## Headline reductions

* `isPreconnected_univ_subtype_of_isPreconnected_set` — purely topological
  bridge between ambient preconnectedness `IsPreconnected (S : Set X)` and
  subtype preconnectedness `IsPreconnected (Set.univ : Set ↥S)`.

* `Y_reg_isPreconnected_of_finite_critical_values` — the consumer-facing
  reduction: given the topological hypothesis that the OnePoint-complement
  of a finite set is preconnected, the regular-value subtype is
  preconnected, in the exact form `FibreSumGloballyConstant` consumes.

No `sorry`, no `axiom`. -/

@[expose] public section

noncomputable section

open Set Topology

namespace JacobianChallenge
namespace Manifold

universe u

/-! ## Subtype-preconnectedness from ambient preconnectedness

This is the standard pattern: `Subtype.preconnectedSpace` upgrades an
ambient `IsPreconnected (S : Set X)` to a `PreconnectedSpace ↥S` instance,
from which `IsPreconnected (Set.univ : Set ↥S)` follows via
`isPreconnected_univ`. -/

/-- **Subtype-preconnectedness from ambient preconnectedness.** If
`S : Set X` is preconnected as an ambient set, then `Set.univ : Set ↥S`
is preconnected in the subtype topology. -/
lemma isPreconnected_univ_subtype_of_isPreconnected_set
    {X : Type u} [TopologicalSpace X]
    {S : Set X} (h : IsPreconnected S) :
    IsPreconnected (Set.univ : Set S) := by
  haveI : PreconnectedSpace S := Subtype.preconnectedSpace h
  exact isPreconnected_univ

/-! ## Regular-value reduction

Given the topological fact that `(OnePoint ℂ) \ C` is preconnected for
any finite `C : Set (OnePoint ℂ)`, the subtype `Y_reg = (OnePoint ℂ) \ C`
satisfies the preconnectedness hypothesis required by
`fibreSum_globallyConstant_on_Y_reg`. -/

/-- **Subtype preconnectedness of the regular-value set, given an ambient
preconnectedness hypothesis.** The hypothesis
`h_amb : IsPreconnected ((Set.univ : Set (OnePoint ℂ)) \ C)` is a clean
boundary statement: it says exactly "the sphere minus finitely many
points is preconnected", which is the standard topological fact about
`S² \ (finite set)`. -/
theorem Y_reg_isPreconnected_of_isPreconnected_complement
    (C : Set (OnePoint ℂ))
    (h_amb : IsPreconnected ((Set.univ : Set (OnePoint ℂ)) \ C)) :
    IsPreconnected
      (Set.univ : Set (((Set.univ : Set (OnePoint ℂ)) \ C : Set (OnePoint ℂ)))) :=
  isPreconnected_univ_subtype_of_isPreconnected_set h_amb

/-- **Subtype preconnectedness for the bare complement form.** Same as
above but for the set `Cᶜ` rather than `Set.univ \ C`. The two are equal
sets but the unfolded `Set.univ \ C` form is the literal shape produced
when `Y_reg` is defined as a "sphere-minus-critical-values" set. -/
theorem Y_reg_isPreconnected_of_isPreconnected_compl
    (C : Set (OnePoint ℂ))
    (h_amb : IsPreconnected (Cᶜ : Set (OnePoint ℂ))) :
    IsPreconnected (Set.univ : Set ((Cᶜ : Set (OnePoint ℂ)))) :=
  isPreconnected_univ_subtype_of_isPreconnected_set h_amb

/-! ## Headline ambient hypothesis

The boundary between this chip and the deeper sphere-topology API is the
single statement: for any finite `C : Set (OnePoint ℂ)`, the complement
`(OnePoint ℂ) \ C` is preconnected. This is a standard fact (the
2-sphere minus finitely many points is path-connected), but a full
derivation requires either a homeomorphism `OnePoint ℂ ≃ₜ S²` or a
direct path-construction in the OnePoint topology. We name the
hypothesis here so the downstream consumer (ZZ83) can compose against
it. -/

/-- **Headline structural theorem (parameterised on the topological
hypothesis).** Given that the OnePoint-complement of a finite set is
preconnected, the regular-value subtype is preconnected in the form
`fibreSum_globallyConstant_on_Y_reg` consumes. -/
theorem regularValueSet_isPreconnected_of_finite_complement_hypothesis
    (h_topo :
      ∀ C : Set (OnePoint ℂ), C.Finite → IsPreconnected (Cᶜ : Set (OnePoint ℂ)))
    (C : Set (OnePoint ℂ)) (hC_fin : C.Finite) :
    IsPreconnected (Set.univ : Set ((Cᶜ : Set (OnePoint ℂ)))) :=
  Y_reg_isPreconnected_of_isPreconnected_compl C (h_topo C hC_fin)

end Manifold
end JacobianChallenge
