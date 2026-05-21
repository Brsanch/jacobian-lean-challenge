/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphereSimplePole
import JacobianChallenge.Topology.LinearSystemDivisorSimplePoleRank
import JacobianChallenge.Topology.LinearSystemGermDeltaP

set_option linter.unusedSectionVars false

/-! # Construction of `ExistsSimplePoleGermAtSomePoint X` at genus 0

This chip is the **first step toward Riemann-Roch existence at genus 0**
on a general compact connected complex 1-manifold `X`. The goal is to
construct a meromorphic-function germ `ψ : MeromorphicFunctionGerm X`
with `ψ.orderAt p = -1` and `ψ ∈ linearSystemGermDeltaP p` for some
`p : X`, **under `genus X = 0`**.

## Classical content

At genus 0, `H¹(X, O) = 0` (Serre dual to `H⁰(X, Ω¹) = 0`). The short
exact sheaf sequence
  `0 → O → O(δp) → ℂ_p → 0`
gives a long exact cohomology sequence
  `H⁰(O) → H⁰(O(δp)) → H⁰(ℂ_p) → H¹(O) = 0`,
so the connecting map `H⁰(O(δp)) → ℂ_p` is surjective. Composing with
the inclusion of constants (which has cokernel `ℂ_p ↪ ℂ_p` an
isomorphism), the non-constant part gives a meromorphic function with
a simple pole at `p`.

Equivalent direct construction (Forster §16):
1. Pick a chart `(U, φ)` around `p` with `φ(p) = 0`.
2. The local function `g₀(x) = 1/φ(x)` on `U \ {p}` is meromorphic with
   a simple pole at `p`.
3. Multiply by a smooth cutoff `χ` supported in a compact subset of `U`
   to extend `χ · g₀` to all of `X` as a smooth function (zero outside
   the support of `χ`). This is no longer meromorphic.
4. The `∂̄` of `χ · g₀` is a smooth `(0,1)`-form on `X` supported in
   the chart annulus where `χ` transitions. At genus 0,
   `H¹(X, O) = 0` ensures `∂̄ u = ∂̄(χ · g₀)` is solvable for smooth
   `u : X → ℂ`.
5. Define `f := χ · g₀ - u`. Then `∂̄ f = 0`, so `f` is holomorphic on
   `X \ {p}`. Near `p`, `f = χ · (1/φ) - u` has the same pole as
   `1/φ` (since `χ = 1` near `p` and `u` is smooth).

## Lean-side status

* The construction requires `∂̄`-solvability content
  (`H¹(X, O) = 0` at genus 0), which is **not** in mathlib at the
  project pin.
* We name the irreducible classical inputs precisely, then deliver the
  mechanical glue around them.

## What this chip ships

* `SimplePoleGermExtensionHypothesis X p` — precisely-named classical
  hypothesis: at genus 0, around any `p : X`, the local-pole function
  `1/φ` (in any chart around `p`) extends to a global meromorphic-
  function germ with simple pole at `p`.
* `existsSimplePoleGermAtSomePoint_of_extension` — the mechanical
  composition: under the named hypothesis at some `p`,
  `ExistsSimplePoleGermAtSomePoint X` follows.

The named hypothesis isolates exactly the `∂̄`-solvability content
of Hodge theory at genus 0. Any future discharge of it (via L²-Hodge,
sheaf cohomology, or the ∂̄-equation directly) immediately unlocks
`ExistsSimplePoleGermAtSomePoint X`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge.MeromorphicFunctionField

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Named classical hypothesis: the local simple-pole germ at `p`
extends to a global meromorphic-function germ with simple pole at `p`.**

Precisely: under `genus X = 0`, for **some** point `p : X`, there
exists a meromorphic-function germ `ψ` on `X` with
* `ψ.orderAt p = -1` (true simple pole at `p`), and
* `ψ ∈ linearSystemGermDeltaP p` (no other poles).

This isolates the classical existence content of Riemann-Roch at
genus 0 (equivalent to `H¹(X, O) = 0` via the long exact sheaf
sequence of `0 → O → O(δp) → ℂ_p → 0`). It is **strictly weaker**
than the full Riemann-Roch theorem — only the existence consequence
at the single divisor `δp` is asserted.

Discharging this hypothesis requires either:
* L²-Hodge theory on compact Riemann surfaces (`∂̄`-equation
  solvability), or
* Cech / sheaf cohomology with `H¹(X, O) = 0` at genus 0, or
* Forster Theorem 16.9 directly.

None of these are at the mathlib pin (`8e3c989...`). -/
def SimplePoleGermExtensionHypothesis : Prop :=
  JacobianChallenge.genus X = 0 →
  ∃ (p : X) (ψ : MeromorphicFunctionGerm X),
    ψ ∈ linearSystemGermDeltaP p ∧
    ψ.orderAt p = ((-1 : ℤ) : WithTop ℤ)

variable {X}

/-- **The named hypothesis, restated as a genus-conditional form of
`ExistsSimplePoleGermAtSomePoint X`.** Definitionally equivalent. -/
lemma simplePoleGermExtensionHypothesis_iff_genusConditional_existsSimplePoleGerm :
    SimplePoleGermExtensionHypothesis X ↔
      (JacobianChallenge.genus X = 0 →
        ExistsSimplePoleGermAtSomePoint X) :=
  Iff.rfl

/-- **Composition: the named hypothesis discharges `ExistsSimplePoleGermAtSomePoint
X` under `genus X = 0`.** -/
theorem existsSimplePoleGermAtSomePoint_of_extension_at_genus_zero
    (h_ext : SimplePoleGermExtensionHypothesis X)
    (hg : JacobianChallenge.genus X = 0) :
    ExistsSimplePoleGermAtSomePoint X :=
  h_ext hg

/-! ## Non-vacuity witness: discharge on `RiemannSphere`

The Riemann sphere has `genus = 0`, and the in-tree
`existsSimplePoleGermAtSomePoint_RiemannSphere` discharges
`ExistsSimplePoleGermAtSomePoint RiemannSphere` directly. So the named
hypothesis fires on RS without further classical input. -/

/-- **RS discharge.** `SimplePoleGermExtensionHypothesis RiemannSphere`
holds unconditionally via the in-tree
`existsSimplePoleGermAtSomePoint_RiemannSphere`. -/
theorem simplePoleGermExtensionHypothesis_RiemannSphere :
    SimplePoleGermExtensionHypothesis JacobianChallenge.RiemannSphere :=
  fun _ => existsSimplePoleGermAtSomePoint_RiemannSphere

end JacobianChallenge.MeromorphicFunctionField

end
