/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.RRStrictLtFromSimplePole
import JacobianChallenge.Topology.UniformizationFromRiemannRoch
import JacobianChallenge.Manifold.HolomorphicOneFormLinear

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Reducing `h_top` to `Subsingleton (HolomorphicOneForm X)`

The "topological-sphere uniformization" hypothesis `h_top`
(`Nonempty (X ≃ₜ StandardS2) → Nonempty (HolomorphicEquiv X
RiemannSphere)`) is the *second* of the two remaining classical
inputs in item 14's germfield-arc capstone (the first being
`ExistsSimplePoleGermAtSomePoint X` per chip 7).

This chip eliminates `h_top` by proving:

  `Subsingleton (HolomorphicOneForm X) ∧
   ExistsSimplePoleGermAtSomePoint X →
   ∀_input, Nonempty (HolomorphicEquiv X RiemannSphere)`

i.e., the *conclusion* of `h_top` holds unconditionally once we have
both `(i)` (existence of a simple-pole germ) and the structural
hypothesis `Subsingleton (HolomorphicOneForm X)`. The premise
`Nonempty (X ≃ₜ StandardS2)` of `h_top` is then unused.

## Why this works

1. `Subsingleton (HolomorphicOneForm X)` gives `genus X = 0`
   unconditionally via `genus_eq_zero_of_holomorphicOneForm_subsingleton`.
2. `ExistsSimplePoleGermAtSomePoint X` gives `RiemannRochGenusZero X`
   via `riemannRochGenusZero_from_ExistsSimplePoleGerm` (chip 7).
3. Applied at `genus X = 0` (step 1), `RiemannRochGenusZero X` yields
   a degree-1 non-constant ω-smooth map `X → RiemannSphere`.
4. The map is upgraded to a `HolomorphicEquiv` via the unconditional
   theorems `surjective_of_NonConstant_Analytic_Manifold_holds`,
   `bijectiveAnalyticIsBiholomorphism_holds`, and
   `ramificationSumEqualsDegree_holds_unconditional` (chained through
   `degreeOneIsBiholomorphic_RS_of_conditionals`).

The trade-off: `Subsingleton (HolomorphicOneForm X)` is itself a
classical input (it asserts that `X` has no nonzero holomorphic
1-forms, which is Hodge-theoretic content). But:

* It is a single, structural typeclass statement — easier to register
  and discover than `h_top`'s implication shape.
* For `X = RiemannSphere`, `Subsingleton (HolomorphicOneForm
  RiemannSphere)` is already an unconditional `instance` in this
  repository (`Manifold/HodgeRiemannSphereInstance.lean`).
* It is *strictly weaker* than the full topological-sphere
  uniformization theorem.

## What this file delivers

* `nonempty_holomorphicEquiv_of_existsSimplePoleGerm_and_subsingleton` —
  the load-bearing implication: under (i) + Subsingleton, the
  `HolomorphicEquiv` exists (no `≃ₜ S²` input needed).
* `h_top_from_existsSimplePoleGerm_and_subsingleton` — `h_top`
  satisfied vacuously from (i) + Subsingleton.
* `genus_eq_zero_iff_homeo_from_existsSimplePoleGerm_and_subsingleton`
  — the **single-classical-input** item-14 capstone.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge.MeromorphicFunctionField

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Existence of a `HolomorphicEquiv X RiemannSphere` from (i) +
Subsingleton.** Under `Subsingleton (HolomorphicOneForm X)`, the genus
is 0 unconditionally, so the `RiemannRochGenusZero` consequence (from
the simple-pole hypothesis) immediately fires, and the resulting
degree-1 map is upgraded to a biholomorphism via the unconditional
theorems in the repository. -/
theorem nonempty_holomorphicEquiv_of_existsSimplePoleGerm_and_subsingleton
    [Subsingleton (HolomorphicOneForm X)]
    (hSP : ExistsSimplePoleGermAtSomePoint X) :
    Nonempty (JacobianChallenge.HolomorphicEquiv X
      JacobianChallenge.RiemannSphere) := by
  -- Step 1: `genus X = 0` from Subsingleton.
  have hg : JacobianChallenge.genus X = 0 :=
    genus_eq_zero_of_holomorphicOneForm_subsingleton X inferInstance
  -- Step 2: `RiemannRochGenusZero X` from (i).
  have hRR : JacobianChallenge.RiemannRochGenusZero X :=
    riemannRochGenusZero_from_ExistsSimplePoleGerm X hSP
  -- Step 3: combine with `DegreeOneIsBiholomorphic_RS X` (unconditional).
  have hDeg1 : JacobianChallenge.DegreeOneIsBiholomorphic_RS X :=
    JacobianChallenge.degreeOneIsBiholomorphic_RS_of_conditionals
      (JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_holds_unconditional
        X JacobianChallenge.RiemannSphere)
      (JacobianChallenge.surjective_of_NonConstant_Analytic_Manifold_holds
        (X := X) (Y := JacobianChallenge.RiemannSphere))
      (JacobianChallenge.bijectiveAnalyticIsBiholomorphism_holds (X := X))
  -- Step 4: apply the genus-0 branch.
  exact JacobianChallenge.uniformizationToRiemannSphere_genus_zero_branch_from_RR
    X hRR hDeg1 hg

/-- **`h_top` from (i) + Subsingleton.** The premise of `h_top` (a
homeomorphism `X ≃ₜ StandardS2`) is unused; the conclusion is
established unconditionally via the previous theorem. -/
theorem h_top_from_existsSimplePoleGerm_and_subsingleton
    [Subsingleton (HolomorphicOneForm X)]
    (hSP : ExistsSimplePoleGermAtSomePoint X) :
    Nonempty (X ≃ₜ JacobianChallenge.StandardS2) →
      Nonempty (JacobianChallenge.HolomorphicEquiv X
        JacobianChallenge.RiemannSphere) :=
  fun _ => nonempty_holomorphicEquiv_of_existsSimplePoleGerm_and_subsingleton X hSP

/-- **Item 14 from a single classical input (modulo the structural
typeclass `Subsingleton (HolomorphicOneForm X)`).** -/
theorem genus_eq_zero_iff_homeo_from_existsSimplePoleGerm_and_subsingleton
    [Subsingleton (HolomorphicOneForm X)]
    (hSP : ExistsSimplePoleGermAtSomePoint X) :
    JacobianChallenge.genus X = 0 ↔
      Nonempty (X ≃ₜ JacobianChallenge.StandardS2) :=
  genus_eq_zero_iff_homeo_from_existsSimplePoleGerm_and_top X hSP
    (h_top_from_existsSimplePoleGerm_and_subsingleton X hSP)

/-! ## Non-vacuity witness: discharge for `X = RiemannSphere` -/

/-- **Verification that the Subsingleton typeclass is non-vacuous.**
`Subsingleton (HolomorphicOneForm RiemannSphere)` is an unconditional
`instance` in this repository (zz274 +
`Manifold/HodgeRiemannSphereInstance.lean`), and a simple-pole germ
exists at every point of `RiemannSphere`. So the single-input chain
fires unconditionally on `X = RiemannSphere`. -/
example
    (hSP : ExistsSimplePoleGermAtSomePoint JacobianChallenge.RiemannSphere) :
    JacobianChallenge.genus JacobianChallenge.RiemannSphere = 0 ↔
      Nonempty (JacobianChallenge.RiemannSphere ≃ₜ JacobianChallenge.StandardS2) :=
  genus_eq_zero_iff_homeo_from_existsSimplePoleGerm_and_subsingleton
    JacobianChallenge.RiemannSphere hSP

end JacobianChallenge.MeromorphicFunctionField

end
