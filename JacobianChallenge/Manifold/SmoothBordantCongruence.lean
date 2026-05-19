/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothBordismAndWordRepresentative
import JacobianChallenge.Manifold.WordLoopHomology
import JacobianChallenge.Manifold.ZPowerBasedLoopHomology

set_option linter.unusedSectionVars false

/-! # `SmoothBordant` is congruent under loop operations

For the smooth-Hurewicz framework, `SmoothBordant γ₀ γ₁` is the
equivalence relation on `BasedLoopAt 𝓘(ℝ, ℂ) X p₀` given by
`γ₀.singleCycle - γ₁.singleCycle ∈ stokesBoundaries`. This file proves
that the relation is preserved by the three basic loop operations:

* **Concat:** `SmoothBordant γ₀ γ₀' ∧ SmoothBordant γ₁ γ₁'
              ⟹ SmoothBordant (γ₀.concat γ₁) (γ₀'.concat γ₁')`.
* **Zpow:**   `SmoothBordant γ γ' ⟹ SmoothBordant (γ.zpow n) (γ'.zpow n)` for any `n : ℤ`.
* **Reverse:** No direct `BasedLoopAt`-level reverse, but the
              underlying-path reverse satisfies a bordism-style identity
              via the existing reverse-pair lemma.

These are **algebraic congruences** — no homotopy needed, just the
existing chain identities (concat-additivity, ℤ-power identity,
reverse-pair identity) combined via abelian-group manipulation in
`stokesBoundaries`.

## Significance

Bordism congruence is the basic tool for constructing bordism witnesses
piecewise: if we know individual loops are bordant to their
basis-representatives, we can combine them via concat/zpow to get
bordism for compound expressions. This is one of the foundational
properties needed for the smooth-Hurewicz arc beyond what
`smoothBordant_of_smoothHomotopy` (geometric) and the algebraic loop
identities (`commutator`, `power`, `wordLoop`) provide individually.

## What this file ships

* `SmoothBordant.concat` — bordism is preserved by `BasedLoopAt.concat`.
* `SmoothBordant.zpow` — bordism is preserved by `BasedLoopAt.zpow`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

namespace SmoothBordant

variable {p₀ : X}

/-- **Bordism is preserved by `BasedLoopAt.concat`.**

If `γ₀ ~ γ₀'` and `γ₁ ~ γ₁'` (smoothly bordant), then
`γ₀ ⋆ γ₁ ~ γ₀' ⋆ γ₁'`.

Proof: concat-additivity in `H₁` gives
`single (γ₀ ⋆ γ₁) ≡ single γ₀ + single γ₁ (mod stokes)`
and likewise for the primed. Subtracting:
`single (γ₀ ⋆ γ₁) - single (γ₀' ⋆ γ₁')
  ≡ (single γ₀ - single γ₀') + (single γ₁ - single γ₁')  (mod stokes)`.
Both summands are in `stokesBoundaries` by hypothesis. -/
theorem concat
    {γ₀ γ₀' γ₁ γ₁' : BasedLoopAt 𝓘(ℝ, ℂ) X p₀}
    (h₀ : SmoothBordant γ₀ γ₀') (h₁ : SmoothBordant γ₁ γ₁') :
    SmoothBordant (γ₀.concat γ₁) (γ₀'.concat γ₁') := by
  -- Unfold SmoothBordant: γ.singleCycle - γ'.singleCycle ∈ stokesBoundaries.
  unfold SmoothBordant
  unfold SmoothBordant at h₀ h₁
  -- Endpoint-compat hypotheses for the two concats.
  have h_compat : γ₀.toPath.tgt = γ₁.toPath.src := by
    rw [γ₀.toPath_tgt, γ₁.toPath_src]
  have h_compat' : γ₀'.toPath.tgt = γ₁'.toPath.src := by
    rw [γ₀'.toPath_tgt, γ₁'.toPath_src]
  -- Concat-additivity for both pairs.
  have h_add :=
    BasedLoopAt.singleCycle_concat_sub_singleCycle_sub_singleCycle_mem_stokesBoundaries
      γ₀ γ₁
  have h_add' :=
    BasedLoopAt.singleCycle_concat_sub_singleCycle_sub_singleCycle_mem_stokesBoundaries
      γ₀' γ₁'
  -- Combine: (h_add - h_add') + h₀ + h₁ gives the target identity in stokes.
  have h_neg_add' : -((γ₀'.concat γ₁').singleCycle
      - γ₀'.singleCycle - γ₁'.singleCycle) ∈ stokesBoundaries 𝓘(ℝ, ℂ) X :=
    AddSubgroup.neg_mem _ h_add'
  -- Sum the four memberships.
  have h_sum : (((γ₀.concat γ₁).singleCycle - γ₀.singleCycle - γ₁.singleCycle)
      + (-((γ₀'.concat γ₁').singleCycle - γ₀'.singleCycle - γ₁'.singleCycle))
      + (γ₀.singleCycle - γ₀'.singleCycle)
      + (γ₁.singleCycle - γ₁'.singleCycle))
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) X :=
    AddSubgroup.add_mem _
      (AddSubgroup.add_mem _
        (AddSubgroup.add_mem _ h_add h_neg_add') h₀) h₁
  -- The sum simplifies (via abel) to (γ₀.concat γ₁).singleCycle - (γ₀'.concat γ₁').singleCycle.
  set A := (γ₀.concat γ₁).singleCycle with hA_def
  set A' := (γ₀'.concat γ₁').singleCycle with hA'_def
  set B := γ₀.singleCycle with hB_def
  set B' := γ₀'.singleCycle with hB'_def
  set C := γ₁.singleCycle with hC_def
  set C' := γ₁'.singleCycle with hC'_def
  have h_eq : ((A - B - C) + (-(A' - B' - C')) + (B - B') + (C - C')) = A - A' := by abel
  rw [h_eq] at h_sum
  exact h_sum

/-- **Bordism is preserved by `BasedLoopAt.zpow`.**

If `γ ~ γ'`, then `γⁿ ~ γ'ⁿ` for any `n : ℤ`.

Proof: the ℤ-power identity gives
`single (γⁿ) ≡ n • single γ (mod stokes)` and likewise for γ'.
Subtracting:
`single (γⁿ) - single (γ'ⁿ) ≡ n • (single γ - single γ')  (mod stokes)`.
The RHS is `n • h` for `h ∈ stokesBoundaries`, hence in `stokesBoundaries`. -/
theorem zpow
    {γ γ' : BasedLoopAt 𝓘(ℝ, ℂ) X p₀} (n : ℤ)
    (h : SmoothBordant γ γ') :
    SmoothBordant (γ.zpow n) (γ'.zpow n) := by
  unfold SmoothBordant
  unfold SmoothBordant at h
  -- ℤ-power identity for both γ and γ'.
  have h_pow :=
    BasedLoopAt.singleCycle_zpow_sub_zsmul_mem_stokesBoundaries γ n
  have h_pow' :=
    BasedLoopAt.singleCycle_zpow_sub_zsmul_mem_stokesBoundaries γ' n
  -- n • (γ.singleCycle - γ'.singleCycle) ∈ stokesBoundaries.
  have h_n_smul : n • (γ.singleCycle - γ'.singleCycle)
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) X :=
    AddSubgroup.zsmul_mem _ h n
  -- Sum: h_pow - h_pow' + h_n_smul gives the target.
  have h_neg_pow' : -((γ'.zpow n).singleCycle - n • γ'.singleCycle)
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) X :=
    AddSubgroup.neg_mem _ h_pow'
  have h_sum : (((γ.zpow n).singleCycle - n • γ.singleCycle)
      + (-((γ'.zpow n).singleCycle - n • γ'.singleCycle))
      + n • (γ.singleCycle - γ'.singleCycle))
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) X :=
    AddSubgroup.add_mem _ (AddSubgroup.add_mem _ h_pow h_neg_pow') h_n_smul
  -- Simplify the sum via abel: (P - nG) + (-(P' - nG')) + n(G - G')
  --   = P - P' - nG + nG' + nG - nG'
  --   = P - P'
  set P := (γ.zpow n).singleCycle with hP_def
  set P' := (γ'.zpow n).singleCycle with hP'_def
  set G := γ.singleCycle with hG_def
  set G' := γ'.singleCycle with hG'_def
  have h_eq : ((P - n • G) + (-(P' - n • G')) + n • (G - G')) = P - P' := by
    have h_smul_sub : n • (G - G') = n • G - n • G' := smul_sub _ _ _
    rw [h_smul_sub]
    abel
  rw [h_eq] at h_sum
  exact h_sum

end SmoothBordant

end JacobianChallenge

end
