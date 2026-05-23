/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.JacobianItemsFromAnalyticEquivSubsingletonSmoke
import JacobianChallenge.Manifold.HJChainFromBiholomorphismRSSmoke
import JacobianChallenge.Manifold.PullbackLinearEquiv

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-! # Smoke: items 5/11/12/13 instances under `[Nonempty (HolomorphicEquiv X RS)]`

Composes the session's auto-instance chain with the in-tree
`JacobianItemsFromAnalyticEquivSubsingletonSmoke`:

* `[Nonempty (HolomorphicEquiv X RS)]` ⟹
  `[Subsingleton (HolomorphicOneForm X)]` (this session) ⟹
  `[UniformizationGenus0Hypothesis X]` (in tree) ⟹
  `[HasPic0AnalyticEquiv X]` (this session) ⟹
  items 5/11/12/13 on `Jacobian X` (in tree).

A single biholomorphism witness now unlocks all four data/instance
items on `Jacobian X` through `inferInstance`. Items remain OPEN in
Basic.lean (no typeclass hypothesis there), but the conditional
discharge is unconditional under a biholomorphism witness.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [Nonempty (HolomorphicEquiv X RiemannSphere)]

/-- **Item 5 — CompactSpace (Jacobian X) — fires via inferInstance under
biholomorphism to RS.** -/
example : CompactSpace (JacobianChallenge.Jacobian X) := inferInstance

/-- **Item 11 — ChartedSpace ... (Jacobian X).** -/
example :
    ChartedSpace (Fin (JacobianChallenge.genus X) → ℂ)
      (JacobianChallenge.Jacobian X) := inferInstance

/-- **Item 12 — IsManifold.** -/
example :
    @IsManifold ℂ _
      (Fin (JacobianChallenge.genus X) → ℂ) _ _
      (Fin (JacobianChallenge.genus X) → ℂ) _
      (modelWithCornersSelf ℂ
        (Fin (JacobianChallenge.genus X) → ℂ)) ω
      (JacobianChallenge.Jacobian X) _ inferInstance := inferInstance

/-- **Item 13 — LieAddGroup ω (Jacobian X) under biholomorphism.**

Composes:
* `[Nonempty (HolomorphicEquiv X RS)]` ⟹ `Subsingleton (Pic0 X)`.
* The genus-0-auto chips supply `ChartedSpace` + `IsManifold`.
* `instLieAddGroup_Jacobian_of_subsingleton` finishes. -/
noncomputable example :
    @LieAddGroup ℂ _
      (Fin (JacobianChallenge.genus X) → ℂ) _
      (Fin (JacobianChallenge.genus X) → ℂ) _ _
      (modelWithCornersSelf ℂ
        (Fin (JacobianChallenge.genus X) → ℂ)) ω
      (JacobianChallenge.Jacobian X) _ _ inferInstance :=
  letI := instChartedSpace_Jacobian_of_subsingleton_omega (X := X)
  letI := instIsManifold_Jacobian_of_subsingleton_omega (X := X)
  haveI : Subsingleton (JacobianChallenge.Jacobian X) :=
    inferInstanceAs (Subsingleton (Pic0 X))
  instLieAddGroup_Jacobian_of_subsingleton (X := X)

/-! ## Item 14 — `genus_eq_zero_iff_homeo` under biholomorphism

Existing in-tree `genus_eq_zero_iff_homeo_of_HolomorphicEquiv_RiemannSphere`
closes item 14 conditionally on a biholomorphism. -/

example :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) :=
  genus_eq_zero_iff_homeo_of_HolomorphicEquiv_RiemannSphere
    (Classical.choice (inferInstance : Nonempty (HolomorphicEquiv X RiemannSphere)))

/-! ## Item 15 — `ofCurve_contMDiff` under biholomorphism

`ofCurve P : X → Jacobian X` into subsingleton target is constant
hence ContMDiff. -/

example (P : X) :
    ContMDiff (𝓘(ℂ, ℂ))
      (modelWithCornersSelf ℂ (Fin (JacobianChallenge.genus X) → ℂ)) ω
      (JacobianChallenge.Jacobian.ofCurve P :
        X → JacobianChallenge.Jacobian X) := by
  letI := instChartedSpace_Jacobian_of_subsingleton_omega (X := X)
  letI := instIsManifold_Jacobian_of_subsingleton_omega (X := X)
  haveI : Subsingleton (JacobianChallenge.Jacobian X) :=
    inferInstanceAs (Subsingleton (Pic0 X))
  exact contMDiff_of_subsingleton

/-! ## Items 17 / 21 — ContMDiff of pushforward / pullback into subsingleton Jacobian -/

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]
  [Nonempty (HolomorphicEquiv Y RiemannSphere)]

/-- **Item 17 (pushforward_contMDiff)** under biholomorphism-to-RS on
both source and target: Jacobian X and Jacobian Y are subsingleton, so
any AddMonoidHom between them is constant hence ContMDiff. -/
example
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (JacobianChallenge.genus X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (JacobianChallenge.genus Y) → ℂ)) ω
      (JacobianChallenge.Jacobian.pushforward hf) := by
  letI := instChartedSpace_Jacobian_of_subsingleton_omega (X := X)
  letI := instIsManifold_Jacobian_of_subsingleton_omega (X := X)
  letI := instChartedSpace_Jacobian_of_subsingleton_omega (X := Y)
  letI := instIsManifold_Jacobian_of_subsingleton_omega (X := Y)
  haveI : Subsingleton (JacobianChallenge.Jacobian Y) :=
    inferInstanceAs (Subsingleton (Pic0 Y))
  exact contMDiff_of_subsingleton

/-- **Item 21 (pullback_contMDiff)** under biholomorphism-to-RS on
both source and target — variant requiring `[DecidableEq X]`. -/
example [DecidableEq X]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (JacobianChallenge.genus Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (JacobianChallenge.genus X) → ℂ)) ω
      (JacobianChallenge.Jacobian.pullbackHonest_of_rsum
        (JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_holds_unconditional
          X Y) f hf) := by
  letI := instChartedSpace_Jacobian_of_subsingleton_omega (X := X)
  letI := instIsManifold_Jacobian_of_subsingleton_omega (X := X)
  letI := instChartedSpace_Jacobian_of_subsingleton_omega (X := Y)
  letI := instIsManifold_Jacobian_of_subsingleton_omega (X := Y)
  haveI : Subsingleton (JacobianChallenge.Jacobian X) :=
    inferInstanceAs (Subsingleton (Pic0 X))
  exact contMDiff_of_subsingleton

end JacobianChallenge

end
