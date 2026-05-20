/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Item14FromHSPBSLBAndAdmissibility
import JacobianChallenge.Manifold.HasAdmissibleChartCoverClass
import JacobianChallenge.Manifold.RiemannSphereSimplePole
import JacobianChallenge.Manifold.StokesBoundariesTopRiemannSphere

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Class-driven 2-input item 14 biconditional

With `[HasAdmissibleChartCover X]` in scope, the per-basis admissibility
hypothesis of `genus_eq_zero_iff_homeo_from_hSP_bslb_and_admissibility`
becomes automatic, leaving only:

* `hSP : ExistsSimplePoleGermAtSomePoint X` (forward leg);
* `h_bslb : SimplyConnectedSpace X → BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀`
  (reverse leg).

For `X = RiemannSphere`, the typeclass is unconditional in tree, so
this **2-input chip** delivers item 14 from `hSP_RS` + `h_bslb_RS`
alone on RS.

## What this file ships

* `s2ImpliesGenus0_of_bslb_and_HasAdmissibleChartCover` — class-driven
  S2ImpliesGenus0 from h_bslb alone.
* `genus_eq_zero_iff_homeo_from_hSP_and_h_bslb_HasAdmissibleChartCover`
  — class-driven 2-input item 14 biconditional.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **S2ImpliesGenus0 from `h_bslb` alone, under
`[HasAdmissibleChartCover X]`.** The per-basis admissibility hypothesis
becomes automatic via the typeclass. -/
theorem s2ImpliesGenus0_of_bslb_and_HasAdmissibleChartCover
    [HasAdmissibleChartCover X]
    (x₀ : X) {ι : Type*}
    (b : Basis ι ℂ (HolomorphicOneForm X))
    (h_bslb : SimplyConnectedSpace X →
      BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀) :
    S2ImpliesGenus0 X :=
  s2ImpliesGenus0_of_bslb_and_admissibleChartCover x₀ b h_bslb
    (fun _ i => HasAdmissibleChartCover.admit (b i))

/-- **Item 14 biconditional from `hSP` + `h_bslb`, under
`[HasAdmissibleChartCover X]`.** Class-driven 2-input version: the
analytic reverse-leg content (per-basis admissibility) is automatic
via the typeclass, leaving only the classical RR-existence input
(forward) and the period-lattice / smooth-Hurewicz input (reverse). -/
theorem genus_eq_zero_iff_homeo_from_hSP_and_h_bslb_HasAdmissibleChartCover
    [HasAdmissibleChartCover X]
    (x₀ : X) {ι : Type*}
    (b : Basis ι ℂ (HolomorphicOneForm X))
    (hSP : MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X)
    (h_bslb : SimplyConnectedSpace X →
      BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) :=
  genus_eq_zero_iff_homeo_from_hSP_bslb_and_admissibility x₀ b hSP h_bslb
    (fun _ i => HasAdmissibleChartCover.admit (b i))

/-! ## End-to-end RS check (typeclass already in tree) -/

/-- **Item 14 biconditional on `RiemannSphere` via the typeclass +
unconditional `hSP_RS` + `h_bslb_RS`.** The typeclass
`HasAdmissibleChartCover RiemannSphere` is an in-tree instance, so
only the two classical inputs need supplying — and both are
unconditional in tree. -/
theorem genus_eq_zero_iff_homeo_RiemannSphere_classDriven
    (x₀ : RiemannSphere) {ι : Type*}
    (b : Basis ι ℂ (HolomorphicOneForm RiemannSphere)) :
    JacobianChallenge.genus RiemannSphere = 0 ↔
      Nonempty (RiemannSphere ≃ₜ StandardS2) :=
  genus_eq_zero_iff_homeo_from_hSP_and_h_bslb_HasAdmissibleChartCover x₀ b
    MeromorphicFunctionField.existsSimplePoleGermAtSomePoint_RiemannSphere
    (fun _ => RiemannSphere.basedSmoothLoopsBoundHypothesis_RS_holds x₀)

end JacobianChallenge

end
