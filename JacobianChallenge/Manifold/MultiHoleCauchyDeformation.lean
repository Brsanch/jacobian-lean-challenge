/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import JacobianChallenge.Manifold.PlanarAnnulusCircleIntegral

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Multi-hole Cauchy deformation lemma (ZZ60)

The headline target named by ZZ59 is: for `c : ℂ`, `R > 0`, and a
finite family `{ball x_i ε_i}_{i ∈ S}` of pairwise-disjoint open balls
contained in `ball c R`, if `g : ℂ → ℂ` is differentiable on the
multi-holed closed disc

  `closedBall c R \ ⋃_{i ∈ S} ball x_i ε_i`

(and continuous on its closure), then

  `∮_{|z-c|=R} g(z) dz  =  ∑_{i ∈ S} ∮_{|z-x_i|=ε_i} g(z) dz.`

## Status at the current mathlib pin

The full statement requires either a multi-component planar Stokes
theorem, or a *non-concentric* single-hole annulus deformation
(`closedBall c R \ ball x₀ ε₀` with `x₀ ≠ c`), neither of which is
present in mathlib at this pin. Mathlib provides only the
**concentric** annulus deformation
(`Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`,
wrapped here as
`JacobianChallenge.PlanarAnnulus.circleIntegral_eq_of_holomorphic_on_annulus`).

This file ships the two unconditional building blocks for the headline
theorem, and names the genuinely missing mathlib lemma in a comment.
No `axiom`, no `sorry`.

## What is proved

* `multiHoleCauchyDeformation_empty` — the **`|S| = 0`** base case.
  If `g` is differentiable on an open neighbourhood of `closedBall c R`
  then `∮_{|z-c|=R} g = 0`. The empty sum on the right is
  `(0 : ℂ)` definitionally; the equality is the standard Cauchy
  vanishing theorem on the closed disc, applied through
  `DiffContOnCl.circleIntegral_eq_zero`.

* `multiHoleCauchyDeformation_singleConcentric` — the **`|S| = 1` and
  `x₀ = c`** case. If `g` is differentiable on the closed concentric
  annulus `closedBall c R \ ball c ε`, then
  `∮_{|z-c|=R} g = ∮_{|z-c|=ε} g`. This is just the planar-annulus
  wrapper, restated as the singleton-`Finset` form for slot-in use in
  the general induction.

## What is *not* proved

The general inductive step requires peeling one **non-concentric**
hole `(x₀, ε₀)` (with `x₀ ≠ c`). Mathlib's annulus deformation is
concentric only. The honest inductive step needs one of:

  (a) A non-concentric single-hole deformation lemma, e.g.
      `Complex.circleIntegral_sub_circleIntegral_of_differentiable_on_diff_balls`
      — **not present at this pin**.
  (b) A planar Stokes theorem on a multi-holed compact domain
      (a 2-chain whose boundary is one outer + finitely many inner
      circles) — **not present at this pin**.
  (c) A direct cut argument: connect each inner ball to the outer
      circle by a slit, integrate over the resulting simply-connected
      region, and verify cancellation along the slits via a Lipschitz
      integrand and `intervalIntegral` symmetry. Doable in principle
      but several hundred lines of slit/parameterisation bookkeeping
      with no mathlib infrastructure.

The remaining-mathlib name to look for at future pins (in priority
order) is

  `Complex.circleIntegral_sub_circleIntegral_of_differentiable_on_diff_balls`
  `Complex.circleIntegral_eq_circleIntegral_of_differentiable_off_balls`

Either lemma would let `multiHoleCauchyDeformation_inductive_step`
peel one hole, and the full theorem would follow by `Finset.induction`.

## Anti-cheat

* No `axiom`, no `sorry`.
* No existing definition or signature is changed.
* Both exported theorems are proved end-to-end against mathlib at the
  current pin via existing wrappers.
-/

noncomputable section

open Complex MeasureTheory Set Metric Filter Topology

namespace JacobianChallenge

namespace MultiHoleCauchy

/-- **Multi-hole Cauchy deformation, base case (`|S| = 0`).**

If `g : ℂ → ℂ` is differentiable on an open set `U` containing the
closed disc `closedBall c R`, then the boundary circle integral of
`g` vanishes:

    `∮_{|z-c|=R} g(z) dz = 0`.

This is the empty-`Finset` instance of the multi-hole deformation
lemma: with no holes, the right-hand sum is the empty sum `0`, and the
identity reduces to the holomorphic-disc vanishing theorem. -/
theorem multiHoleCauchyDeformation_empty
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R) {g : ℂ → ℂ} {U : Set ℂ}
    (hUopen : IsOpen U) (hUsub : closedBall c R ⊆ U)
    (hg : DifferentiableOn ℂ g U) :
    (∮ z in C(c, R), g z) = 0 := by
  -- `g` is differentiable on the open ball.
  have hball_subset_closed : ball c R ⊆ closedBall c R := Metric.ball_subset_closedBall
  have hg_open : DifferentiableOn ℂ g (ball c R) :=
    hg.mono (fun z hz => hUsub (hball_subset_closed hz))
  -- `g` is continuous on the closure of the ball (which lies in the closed disc, then in `U`).
  have hg_cont_closed : ContinuousOn g (closedBall c R) :=
    (hg.continuousOn).mono hUsub
  have hg_cont_clos : ContinuousOn g (closure (ball c R)) :=
    hg_cont_closed.mono Metric.closure_ball_subset_closedBall
  have hg_dcoc : DiffContOnCl ℂ g (ball c R) := ⟨hg_open, hg_cont_clos⟩
  exact hg_dcoc.circleIntegral_eq_zero hR

/-- **Multi-hole Cauchy deformation, single concentric hole.**

If `0 < ε ≤ R` and `g : ℂ → ℂ` is differentiable on the closed
concentric annulus `closedBall c R \ ball c ε`, then

    `∮_{|z-c|=R} g(z) dz = ∮_{|z-c|=ε} g(z) dz`.

This is the singleton-hole instance of the multi-hole deformation
lemma in the **concentric** case `x₀ = c`, restated for slot-in use
inside a future `Finset.induction` on the hole set. The proof is a
direct application of the planar-annulus wrapper
`PlanarAnnulus.circleIntegral_eq_of_holomorphic_on_annulus`.

The non-concentric variant (`x₀ ≠ c`) is the missing piece named in
the file-level docstring; see comments there. -/
theorem multiHoleCauchyDeformation_singleConcentric
    {c : ℂ} {R ε : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (closedBall c R \ ball c ε)) :
    (∮ z in C(c, R), g z) = ∮ z in C(c, ε), g z :=
  PlanarAnnulus.circleIntegral_eq_of_holomorphic_on_annulus hε hεR hg

/-- **Multi-hole Cauchy deformation, single concentric hole — sum form.**

Same as `multiHoleCauchyDeformation_singleConcentric`, but the
right-hand side is written as `∑ i ∈ ({0} : Finset ℕ), ...` so it
matches the shape of the headline theorem's right-hand side after
specialising to a singleton index set. This is the form used inside
the future induction's base step. -/
theorem multiHoleCauchyDeformation_singleConcentric_sum
    {c : ℂ} {R ε : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (closedBall c R \ ball c ε)) :
    (∮ z in C(c, R), g z)
      = ∑ _i ∈ ({0} : Finset ℕ), ∮ z in C(c, ε), g z := by
  rw [Finset.sum_singleton]
  exact multiHoleCauchyDeformation_singleConcentric hε hεR hg

end MultiHoleCauchy

end JacobianChallenge

end
