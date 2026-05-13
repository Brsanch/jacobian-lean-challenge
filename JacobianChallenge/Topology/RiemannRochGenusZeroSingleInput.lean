/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.MeroSinglePoleBridgeConditional
import JacobianChallenge.Manifold.ChartPullbackDerivSimplePoleDischarge

set_option diagnostics.threshold 100

/-! # `RiemannRochGenusZero X` from a single named classical input

Composing zz337 (decomposition), zz341 (degreeFiber = 1 given the
regularity certificate), zz342 (universal-regularity wrapper), and
zz344 (unconditional `UniformSimplePoleRegularity X`), the named
conditional `RiemannRochGenusZero X` reduces to a **single** named
classical input:

  `ExistsMeroSimplePole_GenusZero X` —
    under `genus X = 0`, ∃ p, ∃ f : MeromorphicNonzero X with a
    single simple pole at p, holomorphic elsewhere, non-constant.

This is precisely the **Forster Theorem 16.9 existence statement**,
proved classically via Riemann-Roch (`dim L(δp) = 2 - g`) plus Serre
duality (`dim L(K - δp) = 0` at genus 0).

At the project mathlib pin neither Riemann-Roch nor Serre duality is
formalised. Discharging `ExistsMeroSimplePole_GenusZero X` therefore
remains a multi-thousand-LOC L²-Hodge / sheaf-cohomology
formalisation project. But the *Lean architecture* around it is now
fully closed: any future discharge plugs directly into
`riemannRochGenusZero_from_existence` to flip
`RiemannRochGenusZero X` STRICT-CLOSED.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **`RiemannRochGenusZero X` from a single named classical input.**

The analytic bridge half (`UniformSimplePoleRegularity X`) is now a
theorem (zz344); the only remaining open input is the Forster Thm 16.9
existence statement. -/
theorem riemannRochGenusZero_from_existence
    (h_exists : ExistsMeroSimplePole_GenusZero X) :
    RiemannRochGenusZero X :=
  riemannRochGenusZero_of_existence_and_uniformRegularity X
    h_exists (uniformSimplePoleRegularity_holds X)

end JacobianChallenge

end
