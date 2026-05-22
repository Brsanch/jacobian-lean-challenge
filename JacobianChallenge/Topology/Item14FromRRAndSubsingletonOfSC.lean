/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Item14From2MinimalClassicalInputs
import JacobianChallenge.Topology.S2ImpliesGenus0FromSimplyConnected
import JacobianChallenge.Topology.SimplyConnectedS2Unconditional
import JacobianChallenge.Manifold.HolomorphicEquivRiemannSphere

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Item 14 biconditional from RR + holomorphic-1-form subsingleton-of-SC

Audit-driven tightening of `Item14From2MinimalClassicalInputs`. The
existing 2-input form takes:

* `hRR  : RiemannRochGenusZero X`            — forward (RR-style).
* `h_top: X ≃ₜ S² → Nonempty (HolomorphicEquiv X RS)` — reverse (full
  Riemann-mapping-theorem-for-the-sphere statement).

The reverse `h_top` is **strictly stronger** than necessary at the
current pin. The repository now has, all unconditional in tree:

* `simplyConnectedS2_holds : SimplyConnectedS2` —
  `Topology/SimplyConnectedS2Unconditional.lean`, polygonal-approx
  capstone (chip 4j ⇒ 4e ⇒ 3 ⇒ 1).
* `s2ImpliesGenus0_from_simplyConnected` —
  `Topology/S2ImpliesGenus0FromSimplyConnected.lean`, splitting
  `S2ImpliesGenus0 X` through simple-connectedness.

So `Nonempty (X ≃ₜ S²) → genus X = 0` already discharges from
`HolomorphicOneFormSubsingletonOfSimplyConnected X` alone (the
`SimplyConnectedS2` premise of that splitter is absorbed
unconditionally).

For the forward direction (`genus X = 0 → Nonempty (X ≃ₜ S²)`),
`hRR` plus the three in-tree unconditional inputs
(`ramificationSumEqualsDegree_holds_unconditional`,
`surjective_of_NonConstant_Analytic_Manifold_holds`,
`bijectiveAnalyticIsBiholomorphism_holds`) compose into a
biholomorphism `HolomorphicEquiv X RS`, downgraded to `X ≃ₜ S²` via
`homeoStandardS2_of_holomorphicEquiv_RiemannSphere`
(`Manifold/HolomorphicEquivRiemannSphere.lean`).

The resulting 2-input form takes:

* `hRR   : RiemannRochGenusZero X` (same as before).
* `h_sub : HolomorphicOneFormSubsingletonOfSimplyConnected X`
  (strictly weaker than the previous `h_top` — local analytic
  vanishing, not full Riemann mapping).

## Why this is a meaningful reduction

`h_top` requires *producing a biholomorphism* from a topological-sphere
witness — that is the Riemann mapping theorem for the sphere, which
can only be proved via the RR-style chain we are *already* assuming
via `hRR`. The previous formulation thus had a hidden duplicated
"produce-a-map" obligation in `h_top`. By routing the reverse leg
through `simplyConnectedS2_holds + h_sub` (which only needs the
*subsingleton* of holomorphic 1-forms on a simply-connected `X` —
classical Liouville + Poincaré-primitive content), we factor out the
"produce-a-map" obligation entirely. The forward leg's `hRR` is the
*unique* place where map-construction happens.

The strict-closure of item 14 is now exactly two unrelated open
classical pieces:

1. **`hRR`** (Riemann–Roch / Serre duality at genus 0).
2. **`h_sub`** (Poincaré primitive on a simply-connected Riemann
   surface ⇒ Liouville).

Both are individually citable. Neither is in mathlib at the pinned
commit. This file is the structural-reduction capstone — no item
flips, but the open content for item 14 is now **maximally factored**.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Item 14 biconditional from the two genuinely-open classical
inputs.**

* `hRR`  : Riemann–Roch produces a degree-1 holomorphic map `X → RS`
  on a genus-0 compact connected Riemann surface.
* `h_sub`: On a simply-connected compact connected Riemann surface,
  every holomorphic 1-form is the zero form.

The other classical inputs needed by Item 14
(`ramificationSumEqualsDegree`, `surjective_of_NonConstant_Analytic`,
`bijectiveAnalyticIsBiholomorphism`, `SimplyConnectedS2`) are all
unconditional in tree. -/
theorem genus_eq_zero_iff_homeo_from_RR_and_subsingletonOfSC
    (hRR : RiemannRochGenusZero X)
    (h_sub : HolomorphicOneFormSubsingletonOfSimplyConnected X) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) := by
  refine ⟨?_, ?_⟩
  · -- Forward direction: genus = 0 → Nonempty (X ≃ₜ S²).
    -- Uses hRR plus 3 unconditional inputs to build HolomorphicEquiv X RS,
    -- then composes with RiemannSphere.toSphereHomeo.
    intro hg
    have hDeg1 : DegreeOneIsBiholomorphic_RS X :=
      degreeOneIsBiholomorphic_RS_of_conditionals
        (JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_holds_unconditional
          X JacobianChallenge.RiemannSphere)
        (surjective_of_NonConstant_Analytic_Manifold_holds
          (X := X) (Y := JacobianChallenge.RiemannSphere))
        (bijectiveAnalyticIsBiholomorphism_holds.{u, 0} X)
    have h_holEquiv :
        Nonempty (HolomorphicEquiv X JacobianChallenge.RiemannSphere) :=
      uniformizationToRiemannSphere_genus_zero_branch_from_RR X hRR hDeg1 hg
    obtain ⟨e⟩ := h_holEquiv
    exact nonempty_homeo_standardS2_of_holomorphicEquiv_RiemannSphere e
  · -- Reverse direction: Nonempty (X ≃ₜ S²) → genus = 0.
    -- Uses simplyConnectedS2_holds (unconditional in tree) + h_sub.
    intro h
    exact s2ImpliesGenus0_from_simplyConnected X simplyConnectedS2_holds h_sub h

end JacobianChallenge

end
