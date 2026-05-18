/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothSymplecticBasis

set_option linter.unusedSectionVars false

/-! # `SmoothHurewiczHypothesis`: every smooth based loop is a
ℤ-combination of symplectic-basis loops modulo Stokes-boundary

For a smooth symplectic basis
`sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ g`, the
`SmoothHurewiczHypothesis sb` says:

> *For every smooth based loop `γ` at `p₀`, there exist integers
> `n : Fin (2g) → ℤ` such that `single γ - ∑ᵢ nᵢ • single (sb.basis i)
> ∈ stokesBoundaries`.*

This is the **smooth-Hurewicz content** on a genus-`g` surface:
classically, the abelianization of `π₁^{smooth}(X, p₀)` is
`H₁(X; ℤ) ≅ ℤ^{2g}` with the chosen symplectic basis as ℤ-generators,
and "differs by Stokes-boundary" is the smooth-singular-homology
equivalence relation.

At the current mathlib pin, formalising smooth homotopy /
cellular-homology / abelianization-of-π₁ as an inhabited Lean theory is
out of scope (multi-thousand LOC of foundational topology). This file
surfaces the hypothesis as a single named Prop and shows the
*identity reduction* to `BasedLoopHomologyDecompositionHypothesis`
when the `cycleGens` come from `sb.cycleGens`. Downstream chips can
then build on the per-loop hypothesis without having to thread the
specific basis.

## What this file ships

* `SmoothHurewiczHypothesis sb` — the named Prop.
* `basedLoopHomology_of_smoothHurewicz` — identity reduction.
* `smoothHurewicz_of_basedLoopHomology` — reverse direction (the two
  predicates are extensionally equal).
* `smoothHurewicz_iff_basedLoopHomology` — biconditional.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **`SmoothHurewiczHypothesis sb`** — smooth-Hurewicz on a
genus-`g` surface with chosen symplectic basis.

For every smooth based loop `γ` at `p₀ = sb.basePoint`, there exist
integers `n : Fin (2g) → ℤ` such that the cycle difference
`single γ - ∑ᵢ nᵢ • single (sb.basis i)` is a Stokes-boundary
(i.e., the boundary of some smooth 2-chain).

Classically: the abelianisation map `π₁^{smooth}(X, p₀) → H₁(X; ℤ)`
is surjective with the chosen symplectic basis as ℤ-generators of
`H₁(X; ℤ) ≅ ℤ^{2g}`, and "differs by Stokes-boundary" is the
smooth-singular-homology relation. -/
def SmoothHurewiczHypothesis
    {p₀ : X} {g : ℕ} (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ g) : Prop :=
  ∀ γ : SmoothPath 𝓘(ℝ, ℂ) X, ∀ h_src : γ.src = p₀, ∀ h_tgt : γ.tgt = p₀,
    ∃ n : Fin (2 * g) → ℤ,
      single_smoothLoop_smoothCycle γ (h_src.trans h_tgt.symm)
        - ∑ i, n i • sb.cycleGens i
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) X

namespace SmoothHurewiczHypothesis

variable {p₀ : X} {g : ℕ} {sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ g}

/-- **From smooth-Hurewicz to the per-loop homology hypothesis on
`sb.cycleGens`.** Identity reduction: the two predicates are stated
identically up to substitution of `cycleGens := sb.cycleGens`. -/
theorem basedLoopHomology_of_smoothHurewicz
    (h : SmoothHurewiczHypothesis sb) :
    BasedLoopHomologyDecompositionHypothesis sb.cycleGens p₀ := h

/-- **Reverse direction.** The two predicates are extensionally equal. -/
theorem smoothHurewicz_of_basedLoopHomology
    (h : BasedLoopHomologyDecompositionHypothesis sb.cycleGens p₀) :
    SmoothHurewiczHypothesis sb := h

end SmoothHurewiczHypothesis

/-- **The two predicates are equivalent.** -/
theorem smoothHurewicz_iff_basedLoopHomology
    {p₀ : X} {g : ℕ} (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ g) :
    SmoothHurewiczHypothesis sb
      ↔ BasedLoopHomologyDecompositionHypothesis sb.cycleGens p₀ :=
  ⟨SmoothHurewiczHypothesis.basedLoopHomology_of_smoothHurewicz,
    SmoothHurewiczHypothesis.smoothHurewicz_of_basedLoopHomology⟩

end JacobianChallenge

end
