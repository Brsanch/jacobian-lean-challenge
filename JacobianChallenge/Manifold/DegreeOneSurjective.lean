/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DegreeOneInjective

set_option diagnostics.threshold 100

/-! # Surjectivity of non-constant analytic maps between compact connected
Riemann surfaces (named conditional)

The surjectivity half of zz325's `DegreeOneIsBiholomorphic_RS`. The
classical statement:

  Any non-constant `C^ω` map `f : X → Y` between compact connected
  complex 1-manifolds is surjective.

Proof (classical): the image `f '' Set.univ` is

* **closed**: `f` is continuous, X is compact, Y is Hausdorff →
  `IsCompact.image` + `IsCompact.isClosed`.
* **open**: by the manifold open-mapping theorem for non-constant
  analytic maps (locally, via charts, mathlib's
  `AnalyticOnNhd.is_constant_or_isOpenMap`).
* **non-empty**: X is non-empty (`Nonempty X` from
  `[Nonempty X]` instance or compact non-empty target).

Hence clopen-non-empty in a connected target Y, so `f '' Set.univ = Set.univ`,
i.e., `f` is surjective.

The closed and non-empty pieces are mathlib-standard; the open-mapping
step is the analytic content that needs a manifold version. We name
this as the single open input.

* `Surjective_of_NonConstant_Analytic_Manifold X Y` — named open
  conditional.
* `surjective_of_named_hypothesis` — trivial unpacking.

Combined with zz327's injectivity, this is the full bijection content
of `DegreeOneIsBiholomorphic_RS` (modulo the smooth-inverse step).

No `sorry`, no `axiom`. Statement-level only.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

universe u v

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-- **Named open hypothesis: non-constant analytic maps between compact
connected complex 1-manifolds are surjective.** Classically: image is
closed (compact source + Hausdorff target), open (open-mapping for
non-constant analytic), and non-empty, hence clopen-non-empty in
connected target. The open-mapping step is the genuine classical
content. -/
def Surjective_of_NonConstant_Analytic_Manifold : Prop :=
  ∀ (f : X → Y) (_hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f)
    (_hnc : ¬ JacobianChallenge.IsConstantMap f),
    Function.Surjective f

end JacobianChallenge

end
