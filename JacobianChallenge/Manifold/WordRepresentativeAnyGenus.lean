/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothBordismAndWordRepresentative
import JacobianChallenge.Manifold.WordRepresentativeEmptyBasis
import JacobianChallenge.Manifold.BasedSmoothLoopsBoundC
import JacobianChallenge.Manifold.SmoothHurewiczHypothesisRiemannSphere
import JacobianChallenge.Manifold.SmoothBordantCongruence

set_option linter.unusedSectionVars false

/-! # `WordRepresentativeHypothesis` at genus ≥ 1

The hypothesis `WordRepresentativeHypothesis sb` is parameterized over
the symplectic basis `sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ g`.

This file ships a discharge of `WordRepresentativeHypothesis sb` at
**any genus `g`** (including `g ≥ 1`) by choosing `sb := constSymplecticBasis
p₀ g` (the basis with every loop equal to the constant loop at `p₀`)
and showing that on any `X` with `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ)
X p₀`, the hypothesis discharges via `n := fun _ => 0`.

## Honest mathematical caveat

This discharges the **syntactic Prop** `WordRepresentativeHypothesis
sb` for `g ≥ 1` on any `X` with based-loops-bound, but it does **not**
capture the genuine genus-≥1 smooth-Hurewicz content (which would
require a basis whose `cycleGens` are H₁-non-trivial, hence a manifold
where `BasedSmoothLoopsBoundHypothesis` *fails*).

The choice `constSymplecticBasis` makes every basis-loop's
`singleCycle` zero in `H₁` (it equals
`single_smoothPath_const_smoothCycle p₀`, which is in
`stokesBoundaries`). So the basis represents the trivial subgroup of
`H₁`, and `basisProductLoop sb n` is always null-homologous for any
`n`. The "discharge" of `WordRepresentativeHypothesis` then reduces to:
*every loop is null-homologous*, i.e., `BasedSmoothLoopsBoundHypothesis`.

For genus ≥ 1 in the **mathematical** sense (Riemann surface with
non-trivial `H₁`), the basis loops must represent the actual symplectic
basis classes; that requires manifolds like `T² = ℂ/Λ` not currently
in tree.

## What this file ships

* `constSymplecticBasis p₀ g` — the all-constant symplectic basis at
  any genus `g`.
* `wordRepresentativeHypothesis_constSymplecticBasis_of_basedSmoothLoopsBound`
  — discharge of `WordRepresentativeHypothesis (constSymplecticBasis
  p₀ g)` for any `g`, conditional on
  `BasedSmoothLoopsBoundHypothesis`.
* `wordRepresentativeHypothesis_constSymplecticBasis_RS_holds` — RS
  corollary, unconditional at any `g`.
* `wordRepresentativeHypothesis_constSymplecticBasis_C_holds` — ℂ
  corollary, unconditional at any `g`.
* `smoothHurewiczHypothesis_constSymplecticBasis_RS_holds`,
  `smoothHurewiczHypothesis_constSymplecticBasis_C_holds` — composed
  with `smoothHurewiczHypothesis_of_wordRepresentative`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-! ## The all-constant symplectic basis -/

/-- **All-constant symplectic basis at any genus `g`.** Every basis loop
is `SmoothPath.const 𝓘(ℝ, ℂ) X p₀`. The src/tgt endpoint identities are
inherited from `SmoothPath.const_src` and `SmoothPath.const_tgt`. -/
noncomputable def constSymplecticBasis (p₀ : X) (g : ℕ) :
    SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ g where
  basis := fun _ => SmoothPath.const 𝓘(ℝ, ℂ) X p₀
  basis_src := fun _ => SmoothPath.const_src p₀
  basis_tgt := fun _ => SmoothPath.const_tgt p₀

@[simp] lemma constSymplecticBasis_basis (p₀ : X) (g : ℕ) (i : Fin (2 * g)) :
    (constSymplecticBasis p₀ g).basis i = SmoothPath.const 𝓘(ℝ, ℂ) X p₀ := rfl

/-! ## `basisProductLoop` is null-bordant for `constSymplecticBasis` -/

/-- **`(basisProductLoop (constSymplecticBasis p₀ g) n).singleCycle ∈
stokesBoundaries`** for any tuple `n : Fin (2g) → ℤ`.

The basisProductLoop is a `wordLoop` over the basis indexed by `Fin (2g)`,
with each entry being a power of `constBasedLoopAt p₀`. By the
`wordLoop` ℤ-combination identity, its singleCycle differs from
`∑ᵢ nᵢ • (constSymplecticBasis _).cycleGens i` by a Stokes-boundary.
Each `cycleGens i` equals `single_smoothPath_const_smoothCycle p₀
∈ stokesBoundaries`, so the sum is also in `stokesBoundaries`. -/
lemma basisProductLoop_constSymplecticBasis_singleCycle_mem_stokesBoundaries
    (p₀ : X) (g : ℕ) (n : Fin (2 * g) → ℤ) :
    (basisProductLoop (constSymplecticBasis p₀ g) n).singleCycle
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) X := by
  -- (basisProductLoop sb n).singleCycle - ∑ nᵢ • sb.cycleGens i ∈ stokes (existing).
  have h_id :=
    single_basisProductLoop_sub_sum_zsmul_singles_mem_stokesBoundaries
      (constSymplecticBasis p₀ g) n
  -- ∑ nᵢ • sb.cycleGens i ∈ stokes (since each sb.cycleGens i ∈ stokes).
  have h_sum_in : (∑ i, n i • (constSymplecticBasis p₀ g).cycleGens i)
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) X := by
    apply sum_mem
    intro i _
    apply AddSubgroup.zsmul_mem
    -- (constSymplecticBasis p₀ g).cycleGens i = single_smoothPath_const_smoothCycle p₀.
    have h_eq :
        (constSymplecticBasis p₀ g).cycleGens i
          = single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := X) p₀ := by
      apply Subtype.ext
      rw [SmoothSymplecticBasis.cycleGens_coe,
          single_smoothPath_const_smoothCycle_coe]
      rfl
    rw [h_eq]
    exact single_smoothPath_const_smoothCycle_mem_stokesBoundaries p₀
  -- (basisProductLoop sb n).singleCycle
  --   = ((basisProductLoop sb n).singleCycle - ∑ nᵢ • sb.cycleGens i)
  --     + ∑ nᵢ • sb.cycleGens i ∈ stokes.
  have h_sum : ((basisProductLoop (constSymplecticBasis p₀ g) n).singleCycle
        - ∑ i, n i • (constSymplecticBasis p₀ g).cycleGens i)
        + (∑ i, n i • (constSymplecticBasis p₀ g).cycleGens i)
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) X :=
    AddSubgroup.add_mem _ h_id h_sum_in
  have h_eq : ((basisProductLoop (constSymplecticBasis p₀ g) n).singleCycle
        - ∑ i, n i • (constSymplecticBasis p₀ g).cycleGens i)
        + (∑ i, n i • (constSymplecticBasis p₀ g).cycleGens i)
      = (basisProductLoop (constSymplecticBasis p₀ g) n).singleCycle := by abel
  rw [h_eq] at h_sum
  exact h_sum

/-! ## Discharge of `WordRepresentativeHypothesis` -/

/-- **`WordRepresentativeHypothesis (constSymplecticBasis p₀ g)` from
`BasedSmoothLoopsBoundHypothesis`.** At any genus `g` (including `g ≥
1`), choosing the all-constant basis discharges the hypothesis on any
`X` with based-loops-bound. -/
theorem wordRepresentativeHypothesis_constSymplecticBasis_of_basedSmoothLoopsBound
    (p₀ : X) (g : ℕ)
    (h_bound : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X p₀) :
    WordRepresentativeHypothesis (constSymplecticBasis p₀ g) := by
  intro γ h_src h_tgt
  -- Take n := fun _ => 0; need SmoothBordant ⟨γ, _⟩ (basisProductLoop sb 0).
  refine ⟨fun _ => 0, ?_⟩
  let γ_bl : BasedLoopAt 𝓘(ℝ, ℂ) X p₀ := ⟨γ, ⟨h_src, h_tgt⟩⟩
  -- SmoothBordant γ_bl (basisProductLoop sb 0) iff
  -- γ_bl.singleCycle - (basisProductLoop sb 0).singleCycle ∈ stokes.
  unfold SmoothBordant
  -- (basisProductLoop sb 0).singleCycle ∈ stokes (existing helper).
  have h_bpl_in : (basisProductLoop (constSymplecticBasis p₀ g) (fun _ => 0)).singleCycle
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) X :=
    basisProductLoop_constSymplecticBasis_singleCycle_mem_stokesBoundaries p₀ g _
  -- γ_bl.singleCycle ∈ stokes (from based-loops-bound).
  have h_γ_in : γ_bl.singleCycle ∈ stokesBoundaries 𝓘(ℝ, ℂ) X := by
    have h_γ_sing :
        γ_bl.singleCycle
          = single_smoothLoop_smoothCycle γ (h_src.trans h_tgt.symm) := by
      apply Subtype.ext
      rw [BasedLoopAt.singleCycle_coe, single_smoothLoop_smoothCycle_coe]
      rfl
    rw [h_γ_sing]
    exact h_bound γ h_src h_tgt
  -- Subtract.
  exact AddSubgroup.sub_mem _ h_γ_in h_bpl_in

/-! ## `RiemannSphere` corollary (unconditional at any genus) -/

namespace RiemannSphere

/-- **`WordRepresentativeHypothesis (constSymplecticBasis p₀ g)` on
`RiemannSphere`, unconditional at any `g`.** -/
theorem wordRepresentativeHypothesis_constSymplecticBasis_RS_holds
    (p₀ : RiemannSphere) (g : ℕ) :
    WordRepresentativeHypothesis (constSymplecticBasis p₀ g) :=
  wordRepresentativeHypothesis_constSymplecticBasis_of_basedSmoothLoopsBound p₀ g
    (basedSmoothLoopsBoundHypothesis_RS_holds p₀)

/-- **`SmoothHurewiczHypothesis (constSymplecticBasis p₀ g)` on
`RiemannSphere`, unconditional at any `g`.** Composes the word-rep
discharge with `smoothHurewiczHypothesis_of_wordRepresentative`. -/
theorem smoothHurewiczHypothesis_constSymplecticBasis_RS_holds
    (p₀ : RiemannSphere) (g : ℕ) :
    SmoothHurewiczHypothesis (constSymplecticBasis p₀ g) :=
  smoothHurewiczHypothesis_of_wordRepresentative
    (wordRepresentativeHypothesis_constSymplecticBasis_RS_holds p₀ g)

end RiemannSphere

/-! ## `ℂ` corollary (unconditional at any genus) -/

/-- **`WordRepresentativeHypothesis (constSymplecticBasis p₀ g)` on
`ℂ`, unconditional at any `g`.** -/
theorem wordRepresentativeHypothesis_constSymplecticBasis_C_holds
    (p₀ : ℂ) (g : ℕ) :
    WordRepresentativeHypothesis (constSymplecticBasis p₀ g) :=
  wordRepresentativeHypothesis_constSymplecticBasis_of_basedSmoothLoopsBound p₀ g
    (basedSmoothLoopsBoundHypothesis_C_holds p₀)

/-- **`SmoothHurewiczHypothesis (constSymplecticBasis p₀ g)` on `ℂ`,
unconditional at any `g`.** -/
theorem smoothHurewiczHypothesis_constSymplecticBasis_C_holds
    (p₀ : ℂ) (g : ℕ) :
    SmoothHurewiczHypothesis (constSymplecticBasis p₀ g) :=
  smoothHurewiczHypothesis_of_wordRepresentative
    (wordRepresentativeHypothesis_constSymplecticBasis_C_holds p₀ g)

end JacobianChallenge

end
