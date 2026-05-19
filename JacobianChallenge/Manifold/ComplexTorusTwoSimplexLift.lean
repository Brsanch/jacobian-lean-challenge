/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusSmooth2SimplexPartial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # 2D smooth lift of a `Smooth2Simplex` on `T_L = ℂ ⧸ L`

For `σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)` we define the
**horizontal-then-vertical lift**

```
twoSimplexLift σ (p : Fin 2 → ℝ) : ℂ :=
  ∫ s in 0..p 0, partial1 σ (![s, 0])
  + ∫ t in 0..p 1, partial2 σ (![p 0, t])
```

Mathematical role. The candidate equality `mkQ ∘ twoSimplexLift σ = σ.toFun`
(modulo lattice shifts) is the 2D analogue of the 1D
`mkQ ∘ smoothLift = γ.ambient` used in
`ComplexTorusSmoothPathLift.lean`. Combined with `mkQ.mfderiv = id`
(proved in `ComplexTorusMkQMfderiv.lean`), this lets us replace
`σ.toFun`-based boundary integrals on `T_L` with ℂ-valued
horizontal-then-vertical integrals, so that the boundary of every smooth
2-simplex telescopes around the three faces. That, in turn, discharges
`RealImagDzInCanonicalClosed L` (declared in
`ComplexTorusDzComponentsClosed.lean`).

## What this file ships

* `ComplexTorus.twoSimplexLift σ : (Fin 2 → ℝ) → ℂ` — the
  horizontal-then-vertical 2D lift.
* `ComplexTorus.twoSimplexLift_at_origin` — the lift vanishes at the
  origin `(0, 0)`.
* `ComplexTorus.twoSimplexLift_apply` — the explicit unfolding
  identity, for downstream callers.

## What is intentionally NOT in this file

The smoothness of `twoSimplexLift σ` and the identification
`mfderiv (twoSimplexLift σ) p = mfderiv σ.toFun p` (after the
manifold↔Euclidean bridge) require *three* independent pieces of
genuine analytic content that are not at the mathlib pin in this repo:

1. **Smoothness of the per-coordinate partials**
   `p ↦ partial1 σ p`, `p ↦ partial2 σ p` as functions
   `(Fin 2 → ℝ) → ℂ`. The codomain `ℂ ⧸ L` is a *manifold* (not a
   vector space), so the standard `contMDiff_iff_contDiff +
   ContDiff.continuous_fderiv` route used for
   `SmoothPath.velocity_continuous_of_vector_space` does not apply
   directly. See `JacobianChallenge.SmoothPath.velocity_continuous_of_vector_space`
   (in `SmoothPathVelocityContinuous.lean`) — the same comment there
   flags this as out-of-scope for the vector-space chip.

2. **Differentiation under the interval integral** (parametric
   integral). Mathlib's `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
   gives the FTC-with-parameter result; the application here needs (1)
   first.

3. **Schwarz / mixed-partials symmetry** to identify
   `∂/∂x ∫₀^y partial2 σ (x, t) dt = partial1 σ (x, y) - partial1 σ (x, 0)`
   (this is the substantive cross-derivative identity that makes the
   horizontal-then-vertical lift agree with `σ` on both basis
   directions, not just the second). Mathlib's
   `second_derivative_symmetric` provides the Schwarz step.

Each of (1)–(3) is a chip in its own right; carrying them all in this
file would (a) blow past the ≤ 150-line per-commit guideline in
`DEVELOPMENT.md`, and (b) accumulate genuine open content under a
single header. They are scheduled to follow as
`ComplexTorusTwoSimplexLiftSmooth.lean`,
`ComplexTorusTwoSimplexLiftMfderiv1.lean`,
`ComplexTorusTwoSimplexLiftMfderiv2.lean` (the latter being the Schwarz
chip).

No `sorry`, no `axiom`. -/

open scoped Manifold ContDiff Topology
open MeasureTheory

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## The horizontal-then-vertical 2D lift -/

/-- **Horizontal-then-vertical 2D lift** of a smooth 2-simplex
`σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)`, as a function
`(Fin 2 → ℝ) → ℂ`. By construction,

```
twoSimplexLift σ p :=
  ∫ s in 0..p 0, partial1 σ (![s, 0])
  + ∫ t in 0..p 1, partial2 σ (![p 0, t]).
```

Reading the second summand: the inner integration variable is `t`,
ranging from `0` to `p 1`; the *first* coordinate is held fixed at
`p 0`. This is the standard "go horizontally to `(x, 0)`, then
vertically to `(x, y)`" construction. -/
def twoSimplexLift (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L))
    (p : Fin 2 → ℝ) : ℂ :=
  (∫ s in (0 : ℝ)..(p 0), partial1 L σ (![s, 0]))
    + (∫ t in (0 : ℝ)..(p 1), partial2 L σ (![p 0, t]))

/-- Explicit unfolding identity for `twoSimplexLift`, for downstream
callers that want to reduce to the two interval integrals without
`unfold`. -/
lemma twoSimplexLift_apply
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (p : Fin 2 → ℝ) :
    twoSimplexLift L σ p
      = (∫ s in (0 : ℝ)..(p 0), partial1 L σ (![s, 0]))
          + (∫ t in (0 : ℝ)..(p 1), partial2 L σ (![p 0, t])) := rfl

/-- **The lift vanishes at the origin `(0, 0)`.** Both interval
integrals reduce to `∫_0^0 = 0` by `intervalIntegral.integral_same`. -/
@[simp] lemma twoSimplexLift_at_origin
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    twoSimplexLift L σ (Smooth2Simplex.v0) = 0 := by
  -- v0 = ![0, 0]; both upper limits are 0.
  unfold twoSimplexLift
  -- v0 0 = 0 and v0 1 = 0.
  have h0 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 0 = 0 := by
    simp [Smooth2Simplex.v0]
  have h1 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 1 = 0 := by
    simp [Smooth2Simplex.v0]
  rw [h0, h1, intervalIntegral.integral_same, intervalIntegral.integral_same,
    add_zero]

end ComplexTorus

end JacobianChallenge

end
