/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.UniformizationFromRiemannRoch
import JacobianChallenge.Divisor.PrincipalDivisor
import JacobianChallenge.Manifold.MeromorphicAt
import JacobianChallenge.Manifold.IsConstantMapAux
import JacobianChallenge.Manifold.RiemannSphere
import JacobianChallenge.Manifold.Degree

set_option diagnostics.threshold 100

/-! # Forster-route decomposition of `RiemannRochGenusZero X`

This file factors the open conditional `RiemannRochGenusZero X`
(from `UniformizationFromRiemannRoch.lean`) into two precise classical
sub-hypotheses, following the standard route in Forster's
*Lectures on Riemann Surfaces* (Theorem 16.9):

1. **`ExistsMeroSimplePole_GenusZero X`** — under `genus X = 0`, there
   exists a point `p : X` and a function `f : MeromorphicNonzero X`
   that has a simple pole at `p`, is holomorphic everywhere else, and
   is non-constant. This is the Riemann-Roch + Serre-duality
   consequence (`dim L(δp) ≥ 2 - g = 2` at `g = 0`, modulo constants
   gives a non-constant element with at most a simple pole at `p`).
   The classical proof requires both Riemann-Roch and Serre duality on
   compact Riemann surfaces; neither is in mathlib at the project pin.

2. **`MeroSinglePoleExtendsToDeg1Map X`** — given any `MeromorphicNonzero X`
   with a single simple pole at one point `p` and holomorphic elsewhere,
   it extends to an ω-smooth map `F : X → RiemannSphere` of degree
   exactly 1 (the simple pole gives `F⁻¹{∞} = {p}` with ramification
   index 1; degree-1 then follows from `ramificationSumEqualsDegree`).

The composition theorem `riemannRochGenusZero_of_inputs` then chains
these two into `RiemannRochGenusZero X`.

This is a Tier-2 reduction in the same pattern as
`Item14FinalComposition.lean`: it does *not* close
`RiemannRochGenusZero X`. It names the classical inputs precisely so
that subsequent chips can attack each one independently. Component (2)
is bounded by the existing analytic infrastructure
(`MeromorphicNonzero`, `mmeromorphicOrderAt`, `RiemannSphere` charts,
`ContMDiff.degreeFiber`, `RamificationIndex`); component (1) requires
either L²-Hodge theory or sheaf cohomology, neither of which is in
the pinned mathlib.

## Why this decomposition is honest

Both sub-hypotheses are explicit classical theorems with standard
references:

* Component (1) is the content of Forster Theorem 16.9 (degree-1
  meromorphic function on a genus-0 Riemann surface), which is proved
  there via the Riemann-Roch theorem (Forster Thm 16.4) and the
  identification `dim L(K-p) = dim H⁰(Ω) = g = 0` (Forster Cor 17.10
  for Serre duality, specialized to genus 0).

* Component (2) is the standard "single simple pole gives a degree-1
  Riemann-sphere map" step (Forster §1.4 + §3.4 on the pole extension
  to the Riemann sphere, plus the Hurwitz degree formula
  `∑ multiplicity = deg(f)`).

Neither uses any mathematical content that is not classical.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Component (1): existence of a meromorphic function with a single
simple pole on a genus-0 surface.**

Under `genus X = 0`, there is a point `p : X` and a function
`f : MeromorphicNonzero X` with
* a *simple pole* at `p` (`mmeromorphicOrderAt _ f.toFun p = (-1 : ℤ)`),
* *holomorphic* everywhere else (`0 ≤ mmeromorphicOrderAt _ f.toFun x`
  for `x ≠ p`), and
* *non-constant* (`¬ IsConstantMap f.toFun`).

Classically this is **Forster Theorem 16.9**: on a compact connected
Riemann surface of genus 0, the linear system `L(δp)` has dimension 2.
Constants give a 1-dimensional subspace, so the orthogonal direction
provides a non-constant element of `L(δp)`, which is precisely a
function with the three properties above.

The proof requires Riemann-Roch (Forster Thm 16.4) plus Serre duality
to identify `L(K-p)` with `H⁰(Ω(-p)) ⊆ H⁰(Ω) = 0` at genus 0
(Forster Cor 17.10). Neither is in the project's mathlib pin. -/
def ExistsMeroSimplePole_GenusZero : Prop :=
  JacobianChallenge.genus X = 0 →
  ∃ (p : X) (f : MeromorphicNonzero X),
    mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p = ((-1 : ℤ) : WithTop ℤ) ∧
    (∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) ∧
    ¬ JacobianChallenge.IsConstantMap f.toFun

/-- **Component (2): analytic bridge from a single simple pole to a
degree-1 map to the Riemann sphere.**

Given a `MeromorphicNonzero X` function with
* a simple pole at one point `p`,
* holomorphic elsewhere, and
* non-constant,

there is an ω-smooth map `F : X → RiemannSphere` that
* is non-constant, and
* has `degreeFiber F = 1`.

Classically this is the pole-extension construction (Forster §1.4):
near `p` send `f(x) = 1/φ(x)` to the south chart of the Riemann sphere
(`∞`), and away from `p` send `f(x)` to the north chart (`ℂ`). The
resulting map is ω-smooth. Then the fibre `F⁻¹{∞} = {p}` (because the
pole is simple, hence unique) with ramification index 1, so
`ramificationSumEqualsDegree` gives `degreeFiber F = 1`.

This is bounded by existing analytic infrastructure in the repo and
is the smaller of the two components; the next-chip work attacks
this one. -/
def MeroSinglePoleExtendsToDeg1Map : Prop :=
  ∀ (p : X) (f : MeromorphicNonzero X),
    mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun p = ((-1 : ℤ) : WithTop ℤ) →
    (∀ x, x ≠ p → 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) →
    ¬ JacobianChallenge.IsConstantMap f.toFun →
    ∃ (F : X → JacobianChallenge.RiemannSphere)
      (hF : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F),
      ¬ JacobianChallenge.IsConstantMap F ∧
        JacobianChallenge.ContMDiff.degreeFiber F hF = 1

/-- **Composition of components (1) and (2) gives `RiemannRochGenusZero X`.**

This is the mechanical glue: existence of `f : MeromorphicNonzero X`
with a single simple pole + the analytic bridge to a degree-1 map
immediately give the conclusion of `RiemannRochGenusZero X`. -/
theorem riemannRochGenusZero_of_inputs
    (h_exists : ExistsMeroSimplePole_GenusZero X)
    (h_bridge : MeroSinglePoleExtendsToDeg1Map X) :
    RiemannRochGenusZero X := by
  intro hg
  obtain ⟨p, f, h_pole, h_holo, h_nonconst⟩ := h_exists hg
  exact h_bridge p f h_pole h_holo h_nonconst

/-- **Combined named hypothesis form**: under the conjunction of both
components, `RiemannRochGenusZero X` follows. This is just the pair
form of `riemannRochGenusZero_of_inputs`, exposed for downstream
consumers who'd rather take a single hypothesis bundle. -/
theorem riemannRochGenusZero_of_combined
    (h : ExistsMeroSimplePole_GenusZero X ∧ MeroSinglePoleExtendsToDeg1Map X) :
    RiemannRochGenusZero X :=
  riemannRochGenusZero_of_inputs X h.1 h.2

end JacobianChallenge

end
