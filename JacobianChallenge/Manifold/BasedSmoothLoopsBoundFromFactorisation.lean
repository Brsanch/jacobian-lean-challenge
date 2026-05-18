/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothLoopBoundsViaChart

set_option linter.unusedSectionVars false

/-! # Discharging `BasedSmoothLoopsBoundHypothesis` from a chart-factorisation hypothesis

**Headline.** For a smooth manifold `X` modelled on a normed vector
space `V` (i.e., `ChartedSpace V X` + `IsManifold 𝓘(ℝ, V) ⊤ X`), if
every smooth loop based at `p₀ : X` factors through `V` via some
smooth map `f : V → X` (the "chart-factorisation hypothesis"),
then `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, V) X p₀` holds.

This isolates the genuinely-new classical content as the
chart-factorisation predicate — a clean atomic input. On the
Riemann sphere, the discharge of this predicate is constructive via
stereographic projection from a missed point `q ∉ γ([0, 1])` (with
the smoothness of φ⁻¹ : ℂ → RS being the standard manifold structure).

## What this file ships

* `LoopFactorsThroughVectorSpaceHypothesis I V X p₀ : Prop` — the
  chart-factorisation hypothesis.
* `basedSmoothLoopsBoundHypothesis_of_factorisation` — derives
  `BasedSmoothLoopsBoundHypothesis` from the factorisation.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
  (X : Type*) [TopologicalSpace X] [ChartedSpace V X]
  [IsManifold 𝓘(ℝ, V) ⊤ X]
  (p₀ : X)

/-- **`LoopFactorsThroughVectorSpaceHypothesis V X p₀`**.

Says: for every smooth loop `γ : SmoothPath 𝓘(ℝ, V) X` based at `p₀`
(i.e., `γ.src = γ.tgt = p₀`), there exists a smooth map `f : V → X`,
a smoothness proof, and a smooth loop `γ' : SmoothPath 𝓘(ℝ, V) V`
in `V` such that `γ = SmoothPath.push f hf γ'`.

This is the chart-factorisation hypothesis: every based smooth loop
on `X` arises as the pushforward of a loop in a chart space `V` via
some smooth (perhaps chart-inverse) map `f`. -/
def LoopFactorsThroughVectorSpaceHypothesis : Prop :=
  ∀ γ : SmoothPath 𝓘(ℝ, V) X, γ.src = p₀ → γ.tgt = p₀ →
    ∃ (f : V → X) (hf : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, V) ∞ f)
      (γ' : SmoothPath 𝓘(ℝ, V) V),
      γ'.src = γ'.tgt ∧
      γ = SmoothPath.push f hf γ'

/-- **From `LoopFactorsThroughVectorSpaceHypothesis V X p₀`,
discharge `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, V) X p₀`.**

Proof: for any smooth loop `γ` at `p₀`, get the factorisation
`γ = push f γ'` from the hypothesis. Apply
`single_pushSmoothLoop_in_stokesBoundaries_of_vectorSpaceSource` (which
combines V-loop-bounds with `stokesBoundaries_push`) to get
`single (push f γ') ∈ stokesBoundaries`. Substituting back, this is
`single γ ∈ stokesBoundaries`. -/
theorem basedSmoothLoopsBoundHypothesis_of_factorisation
    (h_factor : LoopFactorsThroughVectorSpaceHypothesis V X p₀) :
    BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, V) X p₀ := by
  intro γ h_src h_tgt
  -- Extract the factorisation.
  obtain ⟨f, hf, γ', h_γ'_loop, h_γ_eq⟩ := h_factor γ h_src h_tgt
  -- Get the bound for the pushed loop in V.
  have h_pushed :=
    single_pushSmoothLoop_in_stokesBoundaries_of_vectorSpaceSource
      γ' h_γ'_loop f hf
  -- Show that the SmoothCycle membership transfers across the
  -- factorisation `γ = SmoothPath.push f hf γ'`.
  have h_eq :
      single_smoothLoop_smoothCycle (SmoothPath.push f hf γ') (by
        simp [h_γ'_loop])
        = single_smoothLoop_smoothCycle γ (h_src.trans h_tgt.symm) := by
    apply Subtype.ext
    rw [single_smoothLoop_smoothCycle_coe (SmoothPath.push f hf γ') _,
        single_smoothLoop_smoothCycle_coe γ (h_src.trans h_tgt.symm)]
    rw [← h_γ_eq]
  rw [← h_eq]
  exact h_pushed

/-! ## Headline applied to RS

The path forward for `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) RS p₀`:

1. Define `LoopFactorsThroughVectorSpaceHypothesis ℂ RS p₀`
   (this file's predicate, instantiated with V = ℂ).
2. Discharge it via stereographic projection (future arc):
   for any smooth loop `γ` on RS at `p₀`, find `q ∉ γ([0, 1])` (measure
   argument since `γ` has 1-D image in 2-D RS), use the stereographic
   chart from `q` to identify `RS \ {q} ≅ ℂ`, and let `f := φ⁻¹` (the
   chart inverse, smooth on all of `ℂ` as a total map into `RS`).
3. Apply `basedSmoothLoopsBoundHypothesis_of_factorisation` to conclude
   `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) RS p₀`.

This is the structural pipeline. The genuinely-new classical content
(missing-point + stereographic chart smoothness) is now packaged into
a single predicate. -/

end JacobianChallenge

end
