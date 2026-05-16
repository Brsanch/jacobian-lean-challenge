/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Complex.RemovableSingularity

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Removable singularity adapter (scalar `ℂ → ℂ`)

This file packages mathlib's `Complex.differentiableOn_update_limUnder_of_bddAbove`
into the calling form needed for the `HolomorphicTraceExtension X`
globalize step: a scalar holomorphic function on a punctured
neighbourhood that is **bounded** there extends to a holomorphic
function on the whole neighbourhood, with an explicit value at the
puncture (`limUnder (𝓝[≠] c) g`).

Downstream (next chip arc) will compose this with the chart-pulldown
of `f.fStarOmegaHolOn hnc α` at a critical value, using the n-th-root
cancellation argument to supply the boundedness hypothesis.

## What this file ships

* `holomorphic_extend_of_bounded_on_punctured_nhd` —
  given a scalar `g : ℂ → ℂ`, a nbhd `U` of `c`, and the hypotheses
  `DifferentiableOn ℂ g (U \ {c})` and `∃ M, ∀ z ∈ U \ {c}, ‖g z‖ ≤ M`,
  produces an explicit extension `g' : ℂ → ℂ` (concretely
  `Function.update g c (limUnder (𝓝[≠] c) g)`) that is
  `DifferentiableOn ℂ g' U`, agrees with `g` off `{c}`, and whose
  value at `c` is `limUnder (𝓝[≠] c) g`.

* `removable_extension` — the named extension function
  `Function.update g c (limUnder (𝓝[≠] c) g)`, for downstream use.

* `removable_extension_eqOn_compl` and `removable_extension_value` —
  the two apply lemmas: equality off `{c}` and value at `c`.

* `removable_extension_differentiableOn` — the mathlib lemma re-stated
  in our `removable_extension` form.

* `removable_extension_analyticAt` — corollary: the extension is
  `AnalyticAt ℂ` at `c` (immediate from differentiability on an open
  nbhd via mathlib's `DifferentiableOn.analyticAt`).

No `sorry`, no `axiom`. -/

open Set Filter Topology Function

namespace JacobianChallenge

/-- The canonical "removable-singularity extension" of `g : ℂ → ℂ`
across the puncture `c`: equal to `g` away from `c`, equal to
`limUnder (𝓝[≠] c) g` at `c`. Defined unconditionally; only
differentiable when the source hypotheses hold. -/
noncomputable def removable_extension (g : ℂ → ℂ) (c : ℂ) : ℂ → ℂ :=
  Function.update g c (limUnder (𝓝[≠] c) g)

@[simp] lemma removable_extension_value (g : ℂ → ℂ) (c : ℂ) :
    removable_extension g c c = limUnder (𝓝[≠] c) g := by
  unfold removable_extension
  exact Function.update_self c (limUnder (𝓝[≠] c) g) g

lemma removable_extension_apply_of_ne (g : ℂ → ℂ) (c : ℂ) {z : ℂ} (hz : z ≠ c) :
    removable_extension g c z = g z :=
  Function.update_of_ne hz _ g

lemma removable_extension_eqOn_compl (g : ℂ → ℂ) (c : ℂ) :
    Set.EqOn (removable_extension g c) g ({c}ᶜ) := by
  intro z hz
  exact removable_extension_apply_of_ne g c (by simpa [Set.mem_compl_iff] using hz)

/-- **Removable singularity adapter (bounded form).** A scalar `g : ℂ → ℂ`
that is complex differentiable on a punctured neighbourhood of `c` and
bounded there extends to a complex-differentiable function on the full
neighbourhood. The explicit extension is
`Function.update g c (limUnder (𝓝[≠] c) g)`. -/
theorem removable_extension_differentiableOn {g : ℂ → ℂ} {c : ℂ} {U : Set ℂ}
    (hU : U ∈ 𝓝 c)
    (hd : DifferentiableOn ℂ g (U \ {c}))
    (hb : ∃ M : ℝ, ∀ z ∈ U \ {c}, ‖g z‖ ≤ M) :
    DifferentiableOn ℂ (removable_extension g c) U := by
  obtain ⟨M, hM⟩ := hb
  have hbdd : BddAbove ((norm ∘ g) '' (U \ {c})) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hM z hz
  -- Mathlib delivers `DifferentiableOn ℂ (update g c (limUnder ...)) U`.
  simpa [removable_extension] using
    Complex.differentiableOn_update_limUnder_of_bddAbove hU hd hbdd

/-- **Packaged form.** Given a punctured-nbhd bounded holomorphic `g`,
there is a holomorphic extension to the full nbhd that agrees with `g`
off the puncture and whose value at the puncture is the limit. The
extension is the explicit `removable_extension g c`. -/
theorem holomorphic_extend_of_bounded_on_punctured_nhd {g : ℂ → ℂ} {c : ℂ} {U : Set ℂ}
    (hU : U ∈ 𝓝 c)
    (hd : DifferentiableOn ℂ g (U \ {c}))
    (hb : ∃ M : ℝ, ∀ z ∈ U \ {c}, ‖g z‖ ≤ M) :
    ∃ g' : ℂ → ℂ,
      DifferentiableOn ℂ g' U ∧
      Set.EqOn g' g (U \ {c}) ∧
      g' c = limUnder (𝓝[≠] c) g := by
  refine ⟨removable_extension g c, ?_, ?_, ?_⟩
  · exact removable_extension_differentiableOn hU hd hb
  · intro z hz
    exact removable_extension_apply_of_ne g c hz.2
  · exact removable_extension_value g c

/-- **AnalyticAt corollary.** The removable extension is `AnalyticAt ℂ`
at the puncture `c` (and in fact on every interior point of `U`, but
the puncture is the case we need). -/
theorem removable_extension_analyticAt {g : ℂ → ℂ} {c : ℂ} {U : Set ℂ}
    (hU : U ∈ 𝓝 c)
    (hd : DifferentiableOn ℂ g (U \ {c}))
    (hb : ∃ M : ℝ, ∀ z ∈ U \ {c}, ‖g z‖ ≤ M) :
    AnalyticAt ℂ (removable_extension g c) c := by
  have hdiff : DifferentiableOn ℂ (removable_extension g c) U :=
    removable_extension_differentiableOn hU hd hb
  exact hdiff.analyticAt hU

end JacobianChallenge
