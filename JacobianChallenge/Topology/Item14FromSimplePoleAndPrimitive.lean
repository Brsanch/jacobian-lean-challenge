/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Item14FromRRAndPrimitiveExistence
import JacobianChallenge.Topology.RRStrictLtFromSimplePole

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Item 14 from simple-pole germ + primitive existence — maximally atomic

The tightest 2-input reduction of Item 14 achievable from in-tree
infrastructure. Composes:

* Forward chain: `hSP : ExistsSimplePoleGermAtSomePoint X`
  ⇒ `riemannRochGenusZero_from_ExistsSimplePoleGerm`
  ⇒ `RiemannRochGenusZero X`
  ⇒ (Item-14 forward leg via the in-tree biholomorphism chain).

* Reverse chain: `h_primitive_exists`
  ⇒ `holomorphicOneFormSubsingletonOfSimplyConnected_of_primitiveExistence`
  ⇒ `HolomorphicOneFormSubsingletonOfSimplyConnected X`
  ⇒ (Item-14 reverse leg via `simplyConnectedS2_holds` +
     `s2ImpliesGenus0_from_simplyConnected`).

Both inputs are individually citable textbook items, both correspond
to genuine classical content not in mathlib at the pinned commit, and
neither contains the embedded redundancy of the earlier forms (the
prior `h_top` had a hidden RR-style "produce-a-map" obligation; the
prior `h_sub` had a Liouville-side observation that's already in tree).

## The two atomic inputs

1. **`hSP : ExistsSimplePoleGermAtSomePoint X`** — the explicit "(a)
   piece" of RR at genus 0: at some point `p ∈ X` there exists a
   meromorphic function on `X` with order `-1` at `p` (simple pole)
   and holomorphic elsewhere. Classical textbook content: the
   non-trivial part of `dim H⁰(O(P)) ≥ 2`.

2. **`h_primitive_exists`** — for every holomorphic 1-form `om` on a
   simply-connected compact connected complex 1-manifold, there exists
   a smooth primitive `F : X → ℂ` with `om.eval x = mfderiv F x` for
   all `x`. The path-integral construction:
   `F x := ∫_γ om` along a smooth path `γ` from a basepoint, with
   well-definedness from homotopy-Stokes / monodromy theorem on the
   simply-connected `X`.

## Why this is maximally atomic

Every other Item-14 input previously named in tree decomposes:

* `RiemannRochGenusZero X` ⊇ `ExistsSimplePoleGermAtSomePoint X` (this
  file's hSP) via `riemannRochGenusZero_from_ExistsSimplePoleGerm`.
* `HolomorphicOneFormSubsingletonOfSimplyConnected X` ⊇
  `primitive existence` + unconditional Liouville
  (`Topology/SubsingletonFromPrimitiveExistence.lean`).
* `h_top` (full Riemann-mapping for sphere) ⊇ RR + RS ≃ₜ S² bridge
  (covered by hSP + in-tree unconditional discharges).
* `SimplyConnectedS2` — absorbed unconditionally
  (`simplyConnectedS2_holds`).

No further factoring of either hSP or h_primitive_exists is available
in tree at this pin without descending into the sheaf-cohomology /
path-integral construction itself.

## Status

Item 14 still OPEN at general X in Basic.lean. The structural reduction
is at its **floor**: any further reduction requires *discharging* one
of the two atomic inputs, not factoring them.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Item 14 biconditional from the two maximally atomic inputs.**

The tightest in-tree reduction of Item 14 at this pin. Both `hSP` and
`h_primitive_exists` are atomic — they cannot be further factored into
tree-internal pieces without invoking content equivalent to themselves
elsewhere. -/
theorem genus_eq_zero_iff_homeo_from_simplePoleGerm_and_primitiveExistence
    (hSP : JacobianChallenge.MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X)
    (h_primitive_exists : SimplyConnectedSpace X →
        ∀ om : HolomorphicOneForm X,
          ∃ F : X → ℂ,
            ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F ∧
              ∀ x : X, om.eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) F x) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) :=
  genus_eq_zero_iff_homeo_from_RR_and_primitiveExistence
    (JacobianChallenge.MeromorphicFunctionField.riemannRochGenusZero_from_ExistsSimplePoleGerm
      X hSP)
    h_primitive_exists

end JacobianChallenge

end
