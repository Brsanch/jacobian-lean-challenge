/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Item14FromRRAndSubsingletonOfSC
import JacobianChallenge.Topology.SubsingletonFromPrimitiveExistence

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Item 14 biconditional from RR + primitive existence on simply-connected X

Follow-up to `Item14FromRRAndSubsingletonOfSC.lean`. The previous chip
reduced Item 14's open content to:

* `hRR  : RiemannRochGenusZero X` (forward, Riemann–Roch at genus 0).
* `h_sub: HolomorphicOneFormSubsingletonOfSimplyConnected X`
  (reverse, "simply-connected ⇒ holomorphic 1-forms vanish").

The reverse `h_sub` further reduces (already in tree, via
`Topology/SubsingletonFromPrimitiveExistence.lean`'s
`holomorphicOneFormSubsingletonOfSimplyConnected_of_primitiveExistence`)
into a **primitive-existence** hypothesis plus the in-tree
unconditional Liouville (`contMDiff_omega_isConstant`).

This file ships the headline composition: Item 14 closes from `hRR`
plus the **primitive-existence atom**, which is the genuinely atomic
classical content (the path-integral construction
`F x := ∫_γ ω` on a simply-connected manifold, well-defined by
homotopy-Stokes / monodromy theorem). All Liouville-side content is
absorbed.

## Why this is a sharper reduction than the prior chip

`h_sub : SimplyConnectedSpace X → Subsingleton (HolomorphicOneForm X)`
bundles two separable pieces:

1. The Liouville observation (constant holomorphic ⇒ zero derivative ⇒
   zero 1-form). **Already unconditional in tree.**
2. The primitive-existence theorem (closed 1-form on SC ⇒ ∃ primitive).
   **The genuine open content.**

This file separates them: `h_primitive_exists` is the *isolated*
classical content; Liouville is auto-absorbed.

## What ships

* `genus_eq_zero_iff_homeo_from_RR_and_primitiveExistence` — Item 14
  biconditional from `RR + primitive existence on SC`. Strictly tighter
  reduction than the prior 2-input form (the Liouville piece of `h_sub`
  is no longer named).

## Status

Item 14 still OPEN at general X in Basic.lean. The open classical
content is now in its **maximally atomic** form:

* `hRR` — Riemann–Roch / Serre duality at genus 0 (forward).
* `h_primitive_exists` — Poincaré/path-integral primitive on
  simply-connected compact Riemann surface (reverse).

Both are independent textbook items. Neither is in mathlib at the
pinned commit.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Item 14 biconditional from `RR + primitive existence on SC`.**

Strictly tighter than
`genus_eq_zero_iff_homeo_from_RR_and_subsingletonOfSC`: the previous
chip's `h_sub` premise bundles a Liouville claim that is already
unconditional in tree; this form names only the genuinely atomic
primitive-existence content.

* `hRR`: Riemann–Roch / Serre duality at genus 0. Same as in the prior
  chip.
* `h_primitive_exists`: on a simply-connected compact connected complex
  1-manifold, every holomorphic 1-form admits a smooth primitive
  (the path-integral construction). -/
theorem genus_eq_zero_iff_homeo_from_RR_and_primitiveExistence
    (hRR : RiemannRochGenusZero X)
    (h_primitive_exists : SimplyConnectedSpace X →
        ∀ om : HolomorphicOneForm X,
          ∃ F : X → ℂ,
            ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F ∧
              ∀ x : X, om.eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) F x) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) :=
  genus_eq_zero_iff_homeo_from_RR_and_subsingletonOfSC hRR
    (holomorphicOneFormSubsingletonOfSimplyConnected_of_primitiveExistence
      h_primitive_exists)

end JacobianChallenge

end
