/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Pic0SubsingletonInstanceFromAnalyticEquivSubsingletonOmega
import JacobianChallenge.Manifold.JacobianGenusZeroInstancesAuto
import JacobianChallenge.Manifold.JacobianSubsingletonInstances

set_option linter.unusedSectionVars false

/-! # Smoke tests: items 5/11/12/13 instances from `[HasPic0AnalyticEquiv X] + [Subsingleton ω]`

Validates the full chain:

* `[HasPic0AnalyticEquiv X] + [Subsingleton ω]` →
  `Subsingleton (Pic0 X)` (via this session's chip).
* `[Subsingleton ω] + [Subsingleton (Pic0 X)]` → items 5/11/12 via
  `JacobianGenusZeroInstancesAuto`'s instances.
* `[Subsingleton (Pic0 X)]` → LieAddGroup (item 13) via the
  in-tree subsingleton-Jacobian instance.

End result: under [HasPic0AnalyticEquiv X] + [Subsingleton ω], all
four data/instance items 5/11/12/13 on `Jacobian X` fire via
inferInstance.

## What ships

* Four `example` regression guards (one per item).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [HasPic0AnalyticEquiv X] [Subsingleton (HolomorphicOneForm X)]

/-- **Item 5 — CompactSpace (Jacobian X) — fires via inferInstance.** -/
example : CompactSpace (JacobianChallenge.Jacobian X) := inferInstance

/-- **Item 11 — ChartedSpace ... (Jacobian X) — fires via inferInstance.** -/
example :
    ChartedSpace (Fin (JacobianChallenge.genus X) → ℂ)
      (JacobianChallenge.Jacobian X) := inferInstance

/-- **Item 12 — IsManifold ... ω (Jacobian X) — fires via inferInstance.** -/
example :
    @IsManifold ℂ _
      (Fin (JacobianChallenge.genus X) → ℂ) _ _
      (Fin (JacobianChallenge.genus X) → ℂ) _
      (modelWithCornersSelf ℂ
        (Fin (JacobianChallenge.genus X) → ℂ)) ω
      (JacobianChallenge.Jacobian X) _ inferInstance := inferInstance

/-- **Item 13 — LieAddGroup ... ω (Jacobian X)** — fires via
\`instLieAddGroup_Jacobian_of_subsingleton\` directly, taking the
\`Subsingleton (Pic0 X)\` instance + the \`ChartedSpace\` / \`IsManifold\`
instances supplied via the genus-0-auto chips. -/
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

end JacobianChallenge

end
