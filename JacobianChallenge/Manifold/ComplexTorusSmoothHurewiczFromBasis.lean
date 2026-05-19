/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusProjBordism
import JacobianChallenge.Manifold.ComplexTorusBasisLoopZSpan
import JacobianChallenge.Manifold.ComplexTorusPeriodLatticeInputs
import JacobianChallenge.Manifold.SmoothPathLiftTorusHolds

set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000

/-! # `SmoothHurewiczHypothesisTorus L lam₁ lam₂ _ _` holds under a
ZLattice-basis hypothesis

Ties together the three chips:

* **`single_γ_sub_single_torusBasisLoop_mem_stokesBoundaries`** (Chip B):
  `single γ - single (torusBasisLoop λ) ∈ stokesBoundaries`, where `λ =
  Γ(1) ∈ L` from the smooth lift.

* **`basisLoopAdditive_stokesBoundaries`** (Chip C): additivity
  `γ_{a + b}.cycle - γ_a.cycle - γ_b.cycle ∈ stokesBoundaries`.

* **`basisLoopZSpan_stokesBoundaries`** (Chip D): homogeneity
  `γ_{n·a}.cycle - n • γ_a.cycle ∈ stokesBoundaries` for any `n : ℤ`.

The proof composes Chip B with the homological identity
`γ_{m₁·lam₁ + m₂·lam₂}.cycle ~ m₁ • γ_{lam₁}.cycle + m₂ • γ_{lam₂}.cycle`
(via Chips C and D), where `Γ(1) = m₁ • lam₁ + m₂ • lam₂` by the
ZLattice-basis hypothesis.

## What this file ships

* `ComplexTorus.IsZBasisOfL` — the ZLattice-basis hypothesis.
* `ComplexTorus.smoothHurewiczHypothesisTorus_holds_of_basis` — the
  unconditional discharge under the hypothesis.

No `sorry`, no `axiom`. -/

open Set
open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **ZLattice-basis hypothesis** on `(lam₁, lam₂)`: every element of
`L` is a ℤ-combination of `lam₁` and `lam₂`. (`lam₁, lam₂ ∈ L` is
expected separately.) -/
def IsZBasisOfL (lam₁ lam₂ : ℂ) : Prop :=
  ∀ z : ℂ, z ∈ L → ∃ m₁ m₂ : ℤ, z = m₁ • lam₁ + m₂ • lam₂

/-! ## Helper: `γ_{m₁·lam₁ + m₂·lam₂}.cycle ~ m₁ • γ_{lam₁}.cycle
+ m₂ • γ_{lam₂}.cycle` modulo `stokesBoundaries` -/

variable {L} in
/-- **The "basis decomposition" homological identity.**
For any lam₁, lam₂ ∈ L and integers m₁, m₂:

```
γ_{m₁·lam₁ + m₂·lam₂}.cycle - m₁ • γ_{lam₁}.cycle - m₂ • γ_{lam₂}.cycle
   ∈ stokesBoundaries.
```
-/
theorem torusBasisLoop_zlatticeDecomp_mem_stokesBoundaries
    (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L)
    (m₁ m₂ : ℤ) :
    torusBasisLoop_cycle (m₁ • lam₁ + m₂ • lam₂)
        (L.add_mem (L.smul_mem m₁ hlam₁) (L.smul_mem m₂ hlam₂))
      - m₁ • torusBasisLoop_cycle lam₁ hlam₁
      - m₂ • torusBasisLoop_cycle lam₂ hlam₂
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) (ℂ ⧸ L) := by
  -- Step 1: Additivity for (m₁•lam₁, m₂•lam₂).
  have h_add := torusBasisLoop_cycle_add_sub_mem_stokesBoundaries
    (m₁ • lam₁) (m₂ • lam₂) (L.smul_mem m₁ hlam₁) (L.smul_mem m₂ hlam₂)
  -- h_add : γ_{m₁•lam₁ + m₂•lam₂}.cycle - γ_{m₁•lam₁}.cycle
  --                                     - γ_{m₂•lam₂}.cycle ∈ S.
  -- Step 2: Homogeneity for m₁ on lam₁.
  have h_homo₁ := basisLoopZSpan_stokesBoundaries lam₁ hlam₁ m₁
  -- h_homo₁ : γ_{m₁•lam₁}.cycle - m₁ • γ_{lam₁}.cycle ∈ S.
  -- Step 3: Homogeneity for m₂ on lam₂.
  have h_homo₂ := basisLoopZSpan_stokesBoundaries lam₂ hlam₂ m₂
  -- h_homo₂ : γ_{m₂•lam₂}.cycle - m₂ • γ_{lam₂}.cycle ∈ S.
  -- Step 4: Sum all three.
  have h_sum := AddSubgroup.add_mem _ (AddSubgroup.add_mem _ h_add h_homo₁) h_homo₂
  -- h_sum : (γ_{m₁•lam₁ + m₂•lam₂}.cycle - γ_{m₁•lam₁}.cycle - γ_{m₂•lam₂}.cycle)
  --       + (γ_{m₁•lam₁}.cycle - m₁ • γ_{lam₁}.cycle)
  --       + (γ_{m₂•lam₂}.cycle - m₂ • γ_{lam₂}.cycle) ∈ S.
  -- Simplify: γ_{m₁•lam₁ + m₂•lam₂}.cycle - m₁ • γ_{lam₁}.cycle - m₂ • γ_{lam₂}.cycle.
  have h_simp :
      (torusBasisLoop_cycle (m₁ • lam₁ + m₂ • lam₂)
          (L.add_mem (L.smul_mem m₁ hlam₁) (L.smul_mem m₂ hlam₂))
        - torusBasisLoop_cycle (m₁ • lam₁) (L.smul_mem m₁ hlam₁)
        - torusBasisLoop_cycle (m₂ • lam₂) (L.smul_mem m₂ hlam₂))
      + (torusBasisLoop_cycle (m₁ • lam₁) (L.smul_mem m₁ hlam₁)
          - m₁ • torusBasisLoop_cycle lam₁ hlam₁)
      + (torusBasisLoop_cycle (m₂ • lam₂) (L.smul_mem m₂ hlam₂)
          - m₂ • torusBasisLoop_cycle lam₂ hlam₂)
      = torusBasisLoop_cycle (m₁ • lam₁ + m₂ • lam₂)
          (L.add_mem (L.smul_mem m₁ hlam₁) (L.smul_mem m₂ hlam₂))
        - m₁ • torusBasisLoop_cycle lam₁ hlam₁
        - m₂ • torusBasisLoop_cycle lam₂ hlam₂ := by abel
  rw [h_simp] at h_sum
  exact h_sum

/-! ## Headline: `SmoothHurewiczHypothesisTorus` under the basis hypothesis -/

variable {L} in
/-- **`SmoothHurewiczHypothesisTorus L lam₁ lam₂ hlam₁ hlam₂` holds
unconditionally given that `(lam₁, lam₂)` is a ZLattice basis of `L`.**

This combines:

* the unconditional `smoothPathLiftHypothesisTorus_holds` (smooth lift
  of every smooth based loop with endpoint in `L`),
* the bordism `single γ - single (torusBasisLoop Γ(1)) ∈ S`
  (Chip B),
* the homological decomposition
  `γ_{m₁·lam₁ + m₂·lam₂}.cycle ~ m₁ • γ_{lam₁}.cycle + m₂ • γ_{lam₂}.cycle`
  (Chips C + D),
* the basis hypothesis `IsZBasisOfL L lam₁ lam₂` (every Γ(1) ∈ L
  decomposes as `m₁ • lam₁ + m₂ • lam₂` for integers `m₁, m₂`).

The result is the named atom `SmoothHurewiczHypothesisTorus L lam₁ lam₂
hlam₁ hlam₂` — the smooth-Hurewicz bordism on the complex torus
`ℂ ⧸ L`. -/
theorem smoothHurewiczHypothesisTorus_holds_of_basis
    (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L)
    (h_basis : IsZBasisOfL L lam₁ lam₂) :
    SmoothHurewiczHypothesisTorus L lam₁ lam₂ hlam₁ hlam₂ := by
  -- Unfold SmoothHurewiczHypothesisTorus.
  -- = SmoothHurewiczHypothesis (symplecticBasis L lam₁ lam₂ hlam₁ hlam₂)
  -- = ∀ γ ∀ h_src h_tgt, ∃ n : Fin 2 → ℤ,
  --     single_smoothLoop_smoothCycle γ _ - ∑ i, n i • sb.cycleGens i
  --     ∈ stokesBoundaries.
  intro γ h_src h_tgt
  -- Step 1: Apply smoothPathLiftHypothesisTorus_holds to get the lift Γ.
  obtain ⟨lift, h_lift_smooth, h_lift_zero, h_lift_agrees⟩ :=
    smoothPathLiftHypothesisTorus_holds L γ h_src
  -- Step 2: Γ(1) ∈ L (since mkQ(Γ(1)) = γ.ambient 1 = γ.tgt = 0).
  have h_lift_one_mem : lift 1 ∈ L := by
    have h_at_one := h_lift_agrees 1 (by constructor <;> norm_num)
    -- h_at_one : L.mkQ (lift 1) = γ.ambient 1.
    have h_amb_1 : γ.ambient 1 = γ.tgt := by
      have h := γ.ambient_eq_on_unitInterval
        (⟨1, by constructor <;> norm_num⟩ : unitInterval)
      have hval : ((⟨1, by constructor <;> norm_num⟩ : unitInterval).val : ℝ) = 1 := rfl
      rw [hval] at h
      rw [h]
      exact γ.toPath.target
    rw [h_amb_1, h_tgt] at h_at_one
    exact (Submodule.Quotient.mk_eq_zero L).mp h_at_one
  -- Step 3: Decompose lift 1 via the basis hypothesis.
  obtain ⟨m₁, m₂, h_lift_decomp⟩ := h_basis (lift 1) h_lift_one_mem
  -- Step 4: Choose n : Fin 2 → ℤ.
  refine ⟨fun i => if i.val = 0 then m₁ else m₂, ?_⟩
  -- We need to show:
  --   single γ.cycle - ∑ᵢ (if i.val = 0 then m₁ else m₂) • sb.cycleGens i
  --   ∈ stokesBoundaries.
  -- The sum over Fin 2 unfolds to:
  --   m₁ • sb.cycleGens 0 + m₂ • sb.cycleGens 1
  --   = m₁ • γ_{lam₁}.cycle + m₂ • γ_{lam₂}.cycle.
  -- Goal-rewrite: replace the sum with the explicit pair.
  -- (Note: i.val = 0 picks m₁ at i=0, m₂ at i=1.)
  -- Step 5: Apply Chip B to get γ.cycle - γ_{lift 1}.cycle ∈ S.
  have h_chipB := single_γ_sub_single_torusBasisLoop_mem_stokesBoundaries
    γ lift (lift 1) h_lift_smooth h_lift_zero rfl h_lift_one_mem
    h_src h_tgt h_lift_agrees
  -- h_chipB : single_smoothLoop_smoothCycle γ _ -
  --           single_smoothLoop_smoothCycle (torusBasisLoop (lift 1) h_lift_one_mem) _
  --         ∈ stokesBoundaries.
  -- Reframe in terms of torusBasisLoop_cycle.
  have h_chipB' : single_smoothLoop_smoothCycle γ (h_src.trans h_tgt.symm)
        - torusBasisLoop_cycle (lift 1) h_lift_one_mem
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) (ℂ ⧸ L) := h_chipB
  -- Step 6: Apply the decomposition: γ_{lift 1}.cycle ~ m₁ • γ_{lam₁}.cycle + m₂ • γ_{lam₂}.cycle.
  -- First, rewrite γ_{lift 1}.cycle to γ_{m₁ • lam₁ + m₂ • lam₂}.cycle.
  have h_rewrite : torusBasisLoop_cycle (lift 1) h_lift_one_mem
      = torusBasisLoop_cycle (m₁ • lam₁ + m₂ • lam₂)
          (L.add_mem (L.smul_mem m₁ hlam₁) (L.smul_mem m₂ hlam₂)) :=
    torusBasisLoop_cycle_eq_of_eq h_lift_decomp _ _
  rw [h_rewrite] at h_chipB'
  -- Now: γ.cycle - γ_{m₁•lam₁ + m₂•lam₂}.cycle ∈ S.
  -- Combine with the decomposition.
  have h_decomp := torusBasisLoop_zlatticeDecomp_mem_stokesBoundaries
    lam₁ lam₂ hlam₁ hlam₂ m₁ m₂
  -- h_decomp : γ_{m₁•lam₁ + m₂•lam₂}.cycle - m₁ • γ_{lam₁}.cycle - m₂ • γ_{lam₂}.cycle ∈ S.
  -- Sum h_chipB' + h_decomp:
  --   (γ.cycle - γ_{m₁•lam₁ + m₂•lam₂}.cycle)
  --   + (γ_{m₁•lam₁ + m₂•lam₂}.cycle - m₁ • γ_{lam₁}.cycle - m₂ • γ_{lam₂}.cycle)
  --   = γ.cycle - m₁ • γ_{lam₁}.cycle - m₂ • γ_{lam₂}.cycle.
  have h_sum := AddSubgroup.add_mem _ h_chipB' h_decomp
  have h_decomp_mem : m₁ • lam₁ + m₂ • lam₂ ∈ L :=
    L.add_mem (L.smul_mem m₁ hlam₁) (L.smul_mem m₂ hlam₂)
  have h_simp : (single_smoothLoop_smoothCycle γ (h_src.trans h_tgt.symm)
          - torusBasisLoop_cycle (m₁ • lam₁ + m₂ • lam₂) h_decomp_mem)
        + (torusBasisLoop_cycle (m₁ • lam₁ + m₂ • lam₂) h_decomp_mem
            - m₁ • torusBasisLoop_cycle lam₁ hlam₁
            - m₂ • torusBasisLoop_cycle lam₂ hlam₂)
      = single_smoothLoop_smoothCycle γ (h_src.trans h_tgt.symm)
        - (m₁ • torusBasisLoop_cycle lam₁ hlam₁
            + m₂ • torusBasisLoop_cycle lam₂ hlam₂) := by abel
  rw [h_simp] at h_sum
  -- h_sum : γ.cycle - (m₁ • γ_{lam₁}.cycle + m₂ • γ_{lam₂}.cycle) ∈ S.
  -- Now we need to rewrite the goal's `∑ i, n i • sb.cycleGens i` to match.
  -- The symplectic basis on T_L has cycleGens 0 = γ_{lam₁}.cycle, cycleGens 1 = γ_{lam₂}.cycle.
  -- The sum over Fin 2 with our chosen n unfolds to m₁ • cycleGens 0 + m₂ • cycleGens 1.
  -- We need to compute this and match.
  -- Use `Fin.sum_univ_two`.
  -- Step 7: Unfold the sum and discharge.
  have h_sum_unfold :
      (∑ i : Fin 2, (fun i : Fin 2 => if (i : Fin 2).val = 0 then m₁ else m₂) i
          • (symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens i)
        = m₁ • (symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens ⟨0, by decide⟩
          + m₂ • (symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens ⟨1, by decide⟩ := by
    rw [Fin.sum_univ_two]
    simp
  rw [h_sum_unfold]
  -- Now rewrite cycleGens ⟨0,_⟩ = γ_{lam₁}.cycle via symplecticBasis_basis_zero.
  have h_cycleGens0 :
      (symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens ⟨0, by decide⟩
        = torusBasisLoop_cycle lam₁ hlam₁ := by
    unfold SmoothSymplecticBasis.cycleGens
    apply Subtype.ext
    rw [single_smoothLoop_smoothCycle_coe]
    show SmoothChain.single ((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).basis ⟨0, by decide⟩)
      = (torusBasisLoop_cycle lam₁ hlam₁ : SmoothChain 𝓘(ℝ, ℂ) (ℂ ⧸ L))
    rw [symplecticBasis_basis_zero L lam₁ lam₂ hlam₁ hlam₂]
    unfold torusBasisLoop_cycle
    rw [single_smoothLoop_smoothCycle_coe]
  have h_cycleGens1 :
      (symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).cycleGens ⟨1, by decide⟩
        = torusBasisLoop_cycle lam₂ hlam₂ := by
    unfold SmoothSymplecticBasis.cycleGens
    apply Subtype.ext
    rw [single_smoothLoop_smoothCycle_coe]
    show SmoothChain.single ((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).basis ⟨1, by decide⟩)
      = (torusBasisLoop_cycle lam₂ hlam₂ : SmoothChain 𝓘(ℝ, ℂ) (ℂ ⧸ L))
    rw [symplecticBasis_basis_one L lam₁ lam₂ hlam₁ hlam₂]
    unfold torusBasisLoop_cycle
    rw [single_smoothLoop_smoothCycle_coe]
  rw [h_cycleGens0, h_cycleGens1]
  exact h_sum

end ComplexTorus

end JacobianChallenge

end
