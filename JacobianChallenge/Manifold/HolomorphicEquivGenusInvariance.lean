/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PullbackLinearEquiv
import JacobianChallenge.Topology.S2ImpliesGenus0Discharge

set_option diagnostics.threshold 100

/-! # Genus is a biholomorphic invariant

This file packages the immediate consequence of zz308's
`HolomorphicEquiv.pullbackLinearEquiv` and zz278's
`genus_eq_of_holomorphicOneForm_linearEquiv`: the geometric genus
(`JacobianChallenge.genus`) is invariant under biholomorphisms.

## What is honestly proven here

* `HolomorphicEquiv.genus_eq` — `HolomorphicEquiv X Y → genus X = genus Y`.
  Closure-grade: routes through the `ℂ`-linear equivalence of
  holomorphic-1-form spaces (zz308) followed by mathlib's
  `LinearEquiv.finrank_eq`.

* `HolomorphicEquiv.genus_eq_zero_iff` — biholomorphisms transport the
  predicate `genus · = 0`.

* `HolomorphicEquiv.subsingleton_holomorphicOneForm_iff` — packaging at
  the `Subsingleton` level for the holomorphic-1-form space.

No `sorry`, no `axiom`.

## Why this is useful

Several downstream chips need to transport genus or subsingleton
hypotheses through biholomorphisms (e.g. when normalising via
uniformization, when reducing item-14 inputs, or when proving
`genus`-equality from concrete model isomorphisms). Before this chip
each callsite had to inline the LinearEquiv detour through zz308 plus
the finrank-transfer; this file extracts that as a single named lemma.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-- **Genus is a biholomorphic invariant.** A biholomorphism
`e : HolomorphicEquiv X Y` between complex 1-manifolds forces the two
geometric genera to coincide.

Proof: `e.pullbackLinearEquiv` (zz308) is a `ℂ`-linear equivalence
`HolomorphicOneForm Y ≃ₗ[ℂ] HolomorphicOneForm X`; combined with
`genus_eq_of_holomorphicOneForm_linearEquiv` (zz278) — which is the
finrank-transfer of `JacobianChallenge.genus` — the two genera are
equal. -/
theorem HolomorphicEquiv.genus_eq (e : HolomorphicEquiv X Y) :
    JacobianChallenge.genus X = JacobianChallenge.genus Y :=
  genus_eq_of_holomorphicOneForm_linearEquiv e.pullbackLinearEquiv.symm

/-- **`genus = 0` transports through a biholomorphism.** -/
theorem HolomorphicEquiv.genus_eq_zero_iff (e : HolomorphicEquiv X Y) :
    JacobianChallenge.genus X = 0 ↔ JacobianChallenge.genus Y = 0 := by
  rw [e.genus_eq]

/-- **`Subsingleton (HolomorphicOneForm ·)` transports through a
biholomorphism.** The 1-form pullback `e.pullbackLinearEquiv` is a
`ℂ`-linear equivalence, so it transports `Subsingleton` between the
two 1-form spaces in either direction. -/
theorem HolomorphicEquiv.subsingleton_holomorphicOneForm_iff
    (e : HolomorphicEquiv X Y) :
    Subsingleton (HolomorphicOneForm X) ↔
      Subsingleton (HolomorphicOneForm Y) :=
  e.pullbackLinearEquiv.symm.toEquiv.subsingleton_congr

/-- **Genus equality (Nonempty wrapper).** Convenience form for callers
that hold a `Nonempty (HolomorphicEquiv X Y)` instead of a direct
biholomorphism. -/
theorem genus_eq_of_nonempty_holomorphicEquiv
    (h : Nonempty (HolomorphicEquiv X Y)) :
    JacobianChallenge.genus X = JacobianChallenge.genus Y :=
  h.elim HolomorphicEquiv.genus_eq

end JacobianChallenge

end
