/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphereChartSymmSmooth
import JacobianChallenge.Manifold.BasedSmoothLoopsBoundFromFactorisation

set_option linter.unusedSectionVars false

/-! # Structural reduction of `LoopFactorsThroughVectorSpaceHypothesis ℂ RS p₀`

This file packages the structural pipeline for discharging the full
`LoopFactorsThroughVectorSpaceHypothesis ℂ RiemannSphere p₀` predicate
(the load-bearing classical input for `stokesBoundaries 𝓘(ℝ, ℂ) RS = ⊤`).

The reduction decomposes the predicate into two named hypotheses:

* **`SmoothLoopAvoidsInftyHypothesis p₀`** — every smooth loop on `RS`
  based at `p₀` has image avoiding `∞`, i.e., `γ([0, 1]) ⊆ chartN.source`.
  *Note*: this is **not literally true** for every smooth loop (loops
  can wind through `∞`), but it can be ARRANGED by post-composing with
  a Möbius transformation `T : RS → RS` sending some non-image point
  `q ∉ γ([0, 1])` to `∞`. So a refined version would say "every smooth
  loop is homologous to one missing `∞` via a Möbius pre-composition".
  Discharging that refinement requires (a) the missed-point existence
  (a Sard / Lipschitz-image-has-measure-zero argument) and (b) the
  Möbius pushforward preserves `stokesBoundaries` (which follows from
  `stokesBoundaries_push`).

* **`SmoothLoopChartNPullbackExistsHypothesis p₀`** — every smooth
  loop `γ` on `RS` based at `p₀` with image in `chartN.source` has a
  smooth pullback `γ' : SmoothPath 𝓘(ℝ, ℂ) ℂ` (i.e., a smooth loop in `ℂ`
  with `γ = SmoothPath.push chartN.symm chartN_symm_contMDiff γ'`).

The conjunction of these two hypotheses directly discharges
`LoopFactorsThroughVectorSpaceHypothesis ℂ RS p₀`. The first hypothesis
is genuinely-new analytical content (measure-zero of smooth-curve images
+ smooth-loop deformation under Möbius); the second is a smooth-extension
argument using `ContDiffBump` / smooth tubular neighborhoods.

## What this file ships

* `SmoothLoopAvoidsInftyHypothesis p₀ : Prop` — the avoid-`∞` predicate.
* `SmoothLoopChartNPullbackExistsHypothesis p₀ : Prop` — the chart-N
  pullback existence predicate.
* `loopFactorsThroughVectorSpaceHypothesis_of_avoidInfty_and_chartNPullback` —
  the structural reduction headline.

No `sorry`, no `axiom`. -/

open Set
open scoped Manifold Topology Bundle ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-! ## The two named hypotheses -/

/-- **`SmoothLoopAvoidsInftyHypothesis p₀`** — every smooth loop on
`RS` based at `p₀` has image avoiding `∞`. -/
def SmoothLoopAvoidsInftyHypothesis (p₀ : RiemannSphere) : Prop :=
  ∀ γ : SmoothPath 𝓘(ℝ, ℂ) RiemannSphere,
    γ.src = p₀ → γ.tgt = p₀ →
    ∀ t : unitInterval, γ.toPath t ≠ (OnePoint.infty : RiemannSphere)

/-- **`SmoothLoopChartNPullbackExistsHypothesis p₀`** — every smooth
loop on `RS` based at `p₀` with image in `chartN.source` has a smooth
pullback `γ' : SmoothPath 𝓘(ℝ, ℂ) ℂ` (a smooth loop in `ℂ`) such that
`γ = push chartN.symm chartN_symm_contMDiff γ'`. -/
def SmoothLoopChartNPullbackExistsHypothesis (p₀ : RiemannSphere) : Prop :=
  ∀ γ : SmoothPath 𝓘(ℝ, ℂ) RiemannSphere,
    γ.src = p₀ → γ.tgt = p₀ →
    (∀ t : unitInterval, γ.toPath t ∈ chartN.source) →
    ∃ γ' : SmoothPath 𝓘(ℝ, ℂ) ℂ,
      γ'.src = γ'.tgt ∧
      γ = SmoothPath.push chartN.symm (chartN_symm_contMDiff.of_le (le_top)) γ'

/-! ## The structural reduction -/

/-- **`SmoothLoopAvoidsInftyHypothesis + SmoothLoopChartNPullbackExistsHypothesis`
discharges `LoopFactorsThroughVectorSpaceHypothesis ℂ RS p₀`.**

For each smooth loop γ at p₀:
1. By avoid-∞, γ misses `∞`, hence γ([0, 1]) ⊆ chartN.source.
2. By chart-N pullback existence, there's γ' : SmoothPath 𝓘(ℝ, ℂ) ℂ
   with γ = push chartN.symm γ' and γ' a smooth loop.
3. Take `f := chartN.symm`, `hf := (chartN_symm_contMDiff.of_le (le_top))`,
   `γ' = γ'`. This is the factorisation. -/
theorem loopFactorsThroughVectorSpaceHypothesis_of_avoidInfty_and_chartNPullback
    (p₀ : RiemannSphere)
    (h_avoid : SmoothLoopAvoidsInftyHypothesis p₀)
    (h_pullback : SmoothLoopChartNPullbackExistsHypothesis p₀) :
    JacobianChallenge.LoopFactorsThroughVectorSpaceHypothesis
      ℂ RiemannSphere p₀ := by
  intro γ h_src h_tgt
  -- Step 1: γ([0, 1]) ⊆ chartN.source via avoid-∞.
  have h_in_chartN : ∀ t : unitInterval, γ.toPath t ∈ chartN.source := by
    intro t
    rw [chartN_source]
    exact h_avoid γ h_src h_tgt t
  -- Step 2: pullback existence.
  obtain ⟨γ', h_γ'_loop, h_γ_eq⟩ := h_pullback γ h_src h_tgt h_in_chartN
  -- Step 3: package the factorisation.
  exact ⟨chartN.symm, (chartN_symm_contMDiff.of_le (le_top)), γ', h_γ'_loop, h_γ_eq⟩

/-! ## Discussion

The conjunction of the two named hypotheses suffices to discharge
`LoopFactorsThroughVectorSpaceHypothesis ℂ RS p₀`, which in turn (via
`basedSmoothLoopsBoundHypothesis_of_factorisation` and the structural
results in earlier chips) gives `stokesBoundaries 𝓘(ℝ, ℂ) RS = ⊤`.

**`SmoothLoopAvoidsInftyHypothesis p₀`** is FALSE as stated (a loop
can pass through `∞`), but the REFINED version "every smooth loop is
homologous mod stokesBoundaries to a loop missing `∞`" IS true, via:
* A Sard-style argument that smooth curves have measure-zero image in
  the 2-manifold `RS`, hence miss some point `q`.
* A Möbius transformation `T : RS → RS` sending `q` to `∞`,
  smooth (hence preserving stokesBoundaries via push).
* Argue [γ] = [T(γ)] in canonical H₁ (Möbius is a homeo, so its push
  is a stokesBoundary-respecting automorphism).

**`SmoothLoopChartNPullbackExistsHypothesis p₀`** is constructively
true via:
* `γ` has image in open `chartN.source`, hence γ.ambient maps an open
  neighborhood `(-δ, 1+δ)` of `[0, 1]` into `chartN.source` (compactness +
  continuity).
* `chartN` is smooth on `chartN.source`, so `chartN ∘ γ.ambient` is
  smooth on `(-δ, 1+δ)`.
* Multiply by a smooth bump function `ρ` with `ρ = 1` on `[0, 1]` and
  `supp ρ ⊆ (-δ, 1+δ)` (mathlib `ContDiffBump`); extend by 0 outside.
* The resulting `g' : ℝ → ℂ` is smooth globally, agrees with `chartN ∘
  γ.ambient` on `[0, 1]`, and `g'(0) = chartN(γ.src) = chartN(γ.tgt) = g'(1)`,
  so `γ' := ⟨chartN(γ.src), chartN(γ.tgt), Path.cast chartN ∘ γ.toPath, ⟨g', smoothness, agreement⟩⟩`
  is the desired smooth pullback.

Both discharges are substantial multi-chip arcs and remain as future
work. The current file packages the structural reduction. -/

end RiemannSphere

end JacobianChallenge
