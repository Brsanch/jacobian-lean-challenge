/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CommutatorOfBasedLoopsNullHomologous
import JacobianChallenge.Manifold.SmoothSymplecticBasis

set_option linter.unusedSectionVars false

/-! # `∑_k single([αₖ, βₖ]) ∈ stokesBoundaries` at general genus

Extends chip 18's `single_commutatorLoop_mem_stokesBoundaries` (the
single-commutator-null-homologous fact) to genus-`g` symplectic bases:
the **sum** over `k : Fin g` of the individual commutators
`single ([αₖ, βₖ])` lies in `stokesBoundaries`.

Classically, this is the cycle-level shadow of the 4g-gon relation
`∏ₖ [αₖ, βₖ] = 1` in `π₁(X, p₀)` for a genus-`g` surface. The
*concatenation* product becomes a *sum* at the cycle level (since
`single (γ ⋆ δ) ≡ single γ + single δ` modulo Stokes-boundaries via
`concat_additive_in_stokesBoundaries`).

This is the **cycle-level analog of the fundamental polygon** —
provable in tree purely from `submodule` closure of `stokesBoundaries`
without needing the geometric 2-chain construction.

The classical Stokes-on-fundamental-polygon argument for Riemann's
first bilinear relation `Q(ω_i, ω_j) = 0` at general genus then
factors as:
1. **This chip** (cycle-level commutator sum null-homologous).
2. **Period-integration evaluation** of `∮_{∑[αₖ,βₖ]} (ω · ∫ω')` —
   equals `2·Q(ω, ω')` by the standard expansion of commutator
   integrals (`∮_{[α,β]} ω·∫ω' = (∫_α ω)(∫_β ω') - (∫_β ω)(∫_α ω')`).
3. **Stokes** (chip D `holomorphicStokesHypothesis_holds_unconditional`)
   says the integral around any Stokes-boundary vanishes — gives `0`.

Steps 2 and 3 are the remaining open content. This chip closes step 1.

## What this file ships

* `sum_commutator_cycles_in_stokesBoundaries` — for any smooth
  symplectic basis `sb : SmoothSymplecticBasis I X p₀ g`, the sum
  `∑ k : Fin g, single ([αₖ, βₖ])` is in `stokesBoundaries`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology Bundle ContDiff

namespace JacobianChallenge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

/-- **The `α`-cycle index embedding** `Fin g → Fin (2g)`, `i ↦ i`. -/
@[reducible] def αIndex {g : ℕ} (i : Fin g) : Fin (2 * g) :=
  ⟨i.val, by have := i.isLt; omega⟩

/-- **The `β`-cycle index embedding** `Fin g → Fin (2g)`, `i ↦ g + i`. -/
@[reducible] def βIndex {g : ℕ} (i : Fin g) : Fin (2 * g) :=
  ⟨g + i.val, by have := i.isLt; omega⟩

/-- **`∑ k, single([αₖ, βₖ]) ∈ stokesBoundaries`** at general genus.

The cycle-level form of the 4g-gon relation for a symplectic basis. -/
theorem sum_commutator_cycles_in_stokesBoundaries
    {p₀ : X} {g : ℕ} (sb : SmoothSymplecticBasis I X p₀ g) :
    (∑ k : Fin g,
      (single_smoothLoop_smoothCycle
        (commutatorLoop p₀ (sb.basis (αIndex k)) (sb.basis (βIndex k))
          (sb.basis_src (αIndex k)) (sb.basis_tgt (αIndex k))
          (sb.basis_src (βIndex k)) (sb.basis_tgt (βIndex k)))
        (commutatorLoop_is_loop p₀ (sb.basis (αIndex k)) (sb.basis (βIndex k))
          (sb.basis_src (αIndex k)) (sb.basis_tgt (αIndex k))
          (sb.basis_src (βIndex k)) (sb.basis_tgt (βIndex k)))))
      ∈ stokesBoundaries I X := by
  -- Each summand is in stokesBoundaries (chip 18).
  -- Sum is in stokesBoundaries by submodule closure.
  refine AddSubgroup.sum_mem _ ?_
  intro k _
  exact single_commutatorLoop_mem_stokesBoundaries (I := I) (X := X) p₀
    (sb.basis (αIndex k)) (sb.basis (βIndex k))
    (sb.basis_src (αIndex k)) (sb.basis_tgt (αIndex k))
    (sb.basis_src (βIndex k)) (sb.basis_tgt (βIndex k))

end JacobianChallenge

end
