/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Item14FromSingleUniformization
import JacobianChallenge.Manifold.Degree
import JacobianChallenge.Manifold.IsConstantMapAux

set_option diagnostics.threshold 100

/-! # Uniformization via Riemann-Roch (statement of the missing classical input)

This file names the open classical analytic hypothesis that would close
`UniformizationToRiemannSphere X` (zz309) — and hence challenge item 14
strict-closure — via the **Forster-style** route through Riemann-Roch:

  RiemannRochGenusZero X :=
    JacobianChallenge.genus X = 0 →
      ∃ (f : X → JacobianChallenge.RiemannSphere)
        (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f),
        ¬ JacobianChallenge.IsConstantMap f ∧
        JacobianChallenge.ContMDiff.degreeFiber f hf = 1

This is the **degree-1-meromorphic-function-from-genus-0** statement:
on a compact connected Riemann surface of genus 0, there exists a
non-constant analytic map to the Riemann sphere of degree 1. Classically
this follows from the Riemann-Roch theorem applied to the divisor
`δp` for any chosen point `p ∈ X`: the dimension of
`H⁰(X, O(δp))` is `1 + 1 - 0 + dim H¹(X, O(δp))` (Riemann-Roch), with
`H¹(X, O(δp)) = H⁰(X, Ω(-δp))*` (Serre duality), and for genus 0 we have
`H⁰(X, Ω) = 0` so `H⁰(X, Ω(-δp)) ⊆ H⁰(X, Ω) = 0`. So `H⁰(X, O(δp))` is
2-dimensional, contains the constants, and has a non-constant
element `f` with at most a simple pole at `p`. That `f` has degree 1.

Neither Riemann-Roch nor Serre duality is in mathlib at the pinned
commit. This file does NOT discharge the hypothesis; it names it
explicitly so that a future chip (or external classical-mathematics
formalization) can plug it into the existing closure chain.

## How `RiemannRochGenusZero X` closes item 14

The closure is conditional but explicit:

* `RiemannRochGenusZero X` → degree-1 holomorphic map `f : X → RS`.
* (Open) degree-1 holomorphic map is biholomorphic — classical result
  via injectivity (sum of ramification indices = 1 forces fibre = 1
  point with index 1, so f is injective) + open-mapping theorem +
  inverse-function-theorem for the smooth inverse.
* Once we have `HolomorphicEquiv X RS`, zz309's
  `UniformizationToRiemannSphere X` discharges via the `genus = 0`
  disjunct.

The full chain remains an open multi-thousand-LOC formalization
project. This file is the first explicit waypoint.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Open classical hypothesis: Riemann-Roch on a genus-0 compact
connected Riemann surface produces a degree-1 holomorphic map to the
Riemann sphere.** -/
def RiemannRochGenusZero : Prop :=
  JacobianChallenge.genus X = 0 →
    ∃ (f : X → JacobianChallenge.RiemannSphere)
      (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f),
      ¬ JacobianChallenge.IsConstantMap f ∧
        JacobianChallenge.ContMDiff.degreeFiber f hf = 1

/-- **Open classical hypothesis (specialised to `Y = RiemannSphere`):
a degree-1 holomorphic map `X → RS` is biholomorphic.** -/
def DegreeOneIsBiholomorphic_RS : Prop :=
  ∀ (f : X → JacobianChallenge.RiemannSphere)
    (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f),
    ¬ JacobianChallenge.IsConstantMap f →
    JacobianChallenge.ContMDiff.degreeFiber f hf = 1 →
    Nonempty (HolomorphicEquiv X JacobianChallenge.RiemannSphere)

/-- **Composition: the two named hypotheses close
`UniformizationToRiemannSphere X` on the forward (genus = 0)
disjunct.** Once the topological-sphere disjunct route is also
provided, item 14 strict-closure follows. -/
theorem uniformizationToRiemannSphere_genus_zero_branch_from_RR
    (hRR : RiemannRochGenusZero X)
    (hDeg1 : DegreeOneIsBiholomorphic_RS X) :
    JacobianChallenge.genus X = 0 →
      Nonempty (HolomorphicEquiv X JacobianChallenge.RiemannSphere) := by
  intro hg
  obtain ⟨f, hf, hnc, h_deg⟩ := hRR hg
  exact hDeg1 f hf hnc h_deg

end JacobianChallenge

end
