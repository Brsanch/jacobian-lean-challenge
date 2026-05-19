/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothHurewiczHypothesis

set_option linter.unusedSectionVars false

/-! # Reindexing `SmoothSymplecticBasis` and `SmoothHurewiczHypothesis`
across an equality of genera

Given `sb : SmoothSymplecticBasis I X p₀ n` and `h : m = n`, we
construct `sb.reindex h : SmoothSymplecticBasis I X p₀ m` whose loops
are `sb`'s loops reindexed through `Fin.cast` on the `2 * _` index.

Then `(sb.reindex h).basis i = sb.basis (Fin.cast _ i)` and
`(sb.reindex h).cycleGens i = sb.cycleGens (Fin.cast _ i)`
**definitionally**, so downstream consumers can transport without
opaque `Eq.mpr` artifacts.

We also transport `SmoothHurewiczHypothesis sb` to
`SmoothHurewiczHypothesis (sb.reindex h)` via the finite-sum
reindexing equivalence.

## Why this file exists

`SmoothSymplecticBasis I X p₀ g` is indexed by a single `g : ℕ`,
with `basis : Fin (2 * g) → SmoothPath I X`. Downstream consumers
(`nonempty_periodLatticeSymplecticBundle_ofSmoothHurewicz`) want a
`SmoothSymplecticBasis I X p₀ (JacobianChallenge.genus X)` — i.e. the
`g` parameter must be the *analytic* genus. For the complex torus
`T_L = ℂ ⧸ L`, the natural construction (`symplecticBasis L lam₁
lam₂`) lives at the fixed `g = 1`. To plug it in we need
`g = genus T_L`; we have `genus_eq_one : genus T_L = 1`, so we
reindex the genus-1 bundle along `genus_eq_one.symm`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace SmoothSymplecticBasis

variable {p₀ : X} {n m : ℕ}

/-- Transport a `SmoothSymplecticBasis I X p₀ n` along an equality
`h : m = n` to get a `SmoothSymplecticBasis I X p₀ m`. The loops are
just `sb`'s loops reindexed through `Fin.cast` on the doubled index.

This dodges the `Eq.mpr` opaque term produced by tactic-mode `rw [h];
exact …` style transports, so downstream `.basis` and `.cycleGens`
accessors are `rfl`. -/
noncomputable def reindex
    (sb : SmoothSymplecticBasis I X p₀ n) (h : m = n) :
    SmoothSymplecticBasis I X p₀ m where
  basis := fun i => sb.basis (Fin.cast (by rw [h]) i)
  basis_src := fun i => sb.basis_src _
  basis_tgt := fun i => sb.basis_tgt _

@[simp] lemma reindex_basis_apply
    (sb : SmoothSymplecticBasis I X p₀ n) (h : m = n)
    (i : Fin (2 * m)) :
    (sb.reindex h).basis i = sb.basis (Fin.cast (by rw [h]) i) := rfl

@[simp] lemma reindex_cycleGens_apply
    (sb : SmoothSymplecticBasis I X p₀ n) (h : m = n)
    (i : Fin (2 * m)) :
    (sb.reindex h).cycleGens i = sb.cycleGens (Fin.cast (by rw [h]) i) := rfl

/-- Reflexivity of `reindex`. -/
@[simp] lemma reindex_self
    (sb : SmoothSymplecticBasis I X p₀ n) :
    sb.reindex (rfl : n = n) = sb := by
  cases sb
  rfl

end SmoothSymplecticBasis

/-! ## Transport of `SmoothHurewiczHypothesis` across `reindex` -/

section SmoothHurewiczReindex

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-- **`SmoothHurewiczHypothesis` transports across `reindex`.**

If every smooth based loop is a ℤ-combination of `sb.cycleGens` modulo
Stokes-boundary, then the same holds for `(sb.reindex h).cycleGens`,
since the latter is just a reindexing of the former by `Fin.cast`. -/
theorem SmoothHurewiczHypothesis.reindex
    {p₀ : Y} {n m : ℕ} (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) Y p₀ n)
    (h : m = n) (hyp : SmoothHurewiczHypothesis sb) :
    SmoothHurewiczHypothesis (sb.reindex h) := by
  intro γ h_src h_tgt
  -- Get the witness for the n-indexed Hurewicz hypothesis.
  obtain ⟨c, hc⟩ := hyp γ h_src h_tgt
  -- Transport the coefficients along `Fin.cast h.symm : Fin (2*n) → Fin (2*m)`.
  -- Equivalent: take `c' := c ∘ Fin.cast (by rw [h]) : Fin (2*m) → ℤ`.
  refine ⟨fun i => c (Fin.cast (by rw [h]) i), ?_⟩
  -- The sum reindexes via the `finCongr` equivalence.
  have h_double : 2 * m = 2 * n := by rw [h]
  have h_sum :
      (∑ i : Fin (2 * m), c (Fin.cast h_double i) •
          (sb.reindex h).cycleGens i)
        = ∑ j : Fin (2 * n), c j • sb.cycleGens j := by
    -- Reindex the LHS by `finCongr h_double : Fin (2*m) ≃ Fin (2*n)`.
    -- Use `Finset.sum_equiv` with that equiv.
    have :=
      (finCongr h_double).sum_comp
        (g := fun j : Fin (2 * n) => c j • sb.cycleGens j)
    -- `Fintype.sum_equiv` reformulation: `∑ i, f (e i) = ∑ j, f j`.
    simp only [SmoothSymplecticBasis.reindex_cycleGens_apply]
    -- Rewrite `Fin.cast h_double i = finCongr h_double i` via `finCongr_eq_equivCast`.
    -- Use `Fintype.sum_equiv` directly.
    rw [← Fintype.sum_equiv (finCongr h_double)
      (fun i : Fin (2 * m) =>
        c (Fin.cast h_double i) • sb.cycleGens (Fin.cast h_double i))
      (fun j : Fin (2 * n) => c j • sb.cycleGens j)
      (fun _ => rfl)]
  rw [h_sum]
  exact hc

end SmoothHurewiczReindex

end JacobianChallenge

end
