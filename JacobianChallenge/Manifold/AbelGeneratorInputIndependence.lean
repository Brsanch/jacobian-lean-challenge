/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelGeneratorDischargedSet
import JacobianChallenge.Manifold.ResidueTheoremUnconditional

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `AbelGeneratorPeriodCondition` is independent of the `AbelJacobiInput` choice

`AbelGeneratorPeriodCondition B` says: for every
`f : MeromorphicNonzero X`,

```
complexChainPeriodVector α (B.principalDivisorAJChain (principalDivisorMap f))
  ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α.
```

Two different `AbelJacobiInput` values `B B' : AbelJacobiInput α h`
differ in their `basePoint : X` and their `pathFromBase : X → SmoothPath`.
For a fixed divisor `D : Div X`, the chain-level difference

```
B.principalDivisorAJChain D - B'.principalDivisorAJChain D
  = ∑ x ∈ D.supportFinset,
      D x • (SmoothChain.single (B.pathFromBase x)
             - SmoothChain.single (B'.pathFromBase x))
```

has boundary `D.degree • (δ_{B'.basePoint} - δ_{B.basePoint})` (target
contributions cancel because both `B.pathFromBase x` and
`B'.pathFromBase x` end at `x`; source contributions sum to a multiple of
`δ_{B'.basePoint} - δ_{B.basePoint}` with weight `Σ D(x) = D.degree`).

For a **principal** divisor `D = principalDivisorMap f`,
`residue_theorem` gives `D.degree = 0`, so the difference is a smooth
cycle. Its period vector then lies in
`periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α` by definition
(image of `periodVectorHom` on smooth cycles).

Hence `dischargedGenerators B = dischargedGenerators B'` and
`AbelGeneratorPeriodCondition B ↔ AbelGeneratorPeriodCondition B'`.

The substantive consequence: a future Stokes-style discharge of
`AbelGeneratorPeriodCondition` can fix one convenient `AbelJacobiInput`
(say, the one whose `basePoint` is the chosen `regularLevelSetChain`'s
source fiber) without loss of generality.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Submodule Module Finset

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

namespace AbelJacobiInput

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α}

/-! ## Chain-level difference as a `Finset` sum -/

/-- **Explicit `Finset` sum for the AJ-chain difference.** The difference
of two `principalDivisorAJChain D` values (for the same divisor `D` and
two `AbelJacobiInput` values) is the Finset sum of single-path
differences weighted by `D x`. -/
lemma principalDivisorAJChain_sub_eq_sum
    (B B' : AbelJacobiInput α h) (D : Div X) :
    B.principalDivisorAJChain D - B'.principalDivisorAJChain D
      = ∑ x ∈ D.supportFinset,
          ((D : X → ℤ) x) • (SmoothChain.single (B.pathFromBase x)
                             - SmoothChain.single (B'.pathFromBase x)) := by
  classical
  unfold principalDivisorAJChain
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _
  exact (smul_sub _ _ _).symm

/-! ## Boundary of a single-path difference -/

/-- **Boundary of a single-path difference when targets coincide.** If
`γ.tgt = γ'.tgt`, the boundary of `single γ - single γ'` equals
`δ_{γ'.src} - δ_{γ.src}` (target contributions cancel). -/
lemma boundary_single_sub_single_of_tgt_eq
    {γ γ' : SmoothPath 𝓘(ℝ, ℂ) X}
    (htgt : γ.tgt = γ'.tgt) :
    SmoothChain.boundary (SmoothChain.single γ - SmoothChain.single γ')
      = Finsupp.single γ'.src 1 - Finsupp.single γ.src 1 := by
  rw [map_sub, SmoothChain.boundary_single, SmoothChain.boundary_single]
  show SmoothChain.boundarySingle γ - SmoothChain.boundarySingle γ'
      = Finsupp.single γ'.src 1 - Finsupp.single γ.src 1
  unfold SmoothChain.boundarySingle
  rw [htgt]
  abel

/-- **Boundary of a single-`pathFromBase` difference.** Targets are both
`x`, so the boundary is `δ_{B'.basePoint} - δ_{B.basePoint}` regardless
of `x`. -/
lemma boundary_single_pathFromBase_sub
    (B B' : AbelJacobiInput α h) (x : X) :
    SmoothChain.boundary
        (SmoothChain.single (B.pathFromBase x)
          - SmoothChain.single (B'.pathFromBase x))
      = Finsupp.single B'.basePoint 1 - Finsupp.single B.basePoint 1 := by
  have htgt : (B.pathFromBase x).tgt = (B'.pathFromBase x).tgt := by
    rw [B.tgt_eq, B'.tgt_eq]
  rw [boundary_single_sub_single_of_tgt_eq htgt, B.src_eq, B'.src_eq]

/-! ## Boundary of the full AJ-chain difference -/

/-- **Boundary of the AJ-chain difference factors through `D.degree`.**
For two `AbelJacobiInput` values and any divisor `D`,

```
∂ (B.principalDivisorAJChain D - B'.principalDivisorAJChain D)
  = D.degree • (δ_{B'.basePoint} - δ_{B.basePoint}).
```

Each summand's boundary is `D x • (δ_{B'.basePoint} - δ_{B.basePoint})`
by `boundary_single_pathFromBase_sub`; factoring the constant point
contribution out of the sum gives `(Σ D x) = D.degree` times that
common increment. -/
lemma boundary_principalDivisorAJChain_sub
    (B B' : AbelJacobiInput α h) (D : Div X) :
    SmoothChain.boundary
        (B.principalDivisorAJChain D - B'.principalDivisorAJChain D)
      = D.degree • (Finsupp.single B'.basePoint 1 - Finsupp.single B.basePoint 1) := by
  classical
  rw [B.principalDivisorAJChain_sub_eq_sum B' D, map_sum]
  -- Goal:
  --   ∑ x ∈ D.supportFinset,
  --       boundary (D x • (single (B.pathFromBase x) - single (B'.pathFromBase x)))
  --     = D.degree • (δ_{B'.basePoint} - δ_{B.basePoint})
  -- Pull `D x • ·` through the boundary (`LinearMap` over `ℤ`).
  have hsum :
      (∑ x ∈ D.supportFinset,
          SmoothChain.boundary
            (((D : X → ℤ) x) • (SmoothChain.single (B.pathFromBase x)
                                - SmoothChain.single (B'.pathFromBase x))))
        = ∑ x ∈ D.supportFinset,
            ((D : X → ℤ) x) •
              (Finsupp.single B'.basePoint 1 - Finsupp.single B.basePoint 1) := by
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [map_smul, boundary_single_pathFromBase_sub]
  rw [hsum]
  -- Factor the common increment out:
  --   ∑ x ∈ S, (D x) • v = (∑ x ∈ S, D x) • v
  rw [← Finset.sum_smul]
  -- And `∑ x ∈ D.supportFinset, D x = D.degree` by definition of `degree`.
  rfl

/-! ## Cycle property of the AJ-chain difference -/

/-- **AJ-chain difference is a smooth cycle when the divisor has degree
zero.** Direct consequence of `boundary_principalDivisorAJChain_sub`:
the boundary's `D.degree` coefficient kills the `δ_{B'.basePoint} -
δ_{B.basePoint}` increment. -/
lemma principalDivisorAJChain_sub_mem_smoothCycle_of_degree_zero
    (B B' : AbelJacobiInput α h) {D : Div X} (hDeg : D.degree = 0) :
    B.principalDivisorAJChain D - B'.principalDivisorAJChain D
      ∈ SmoothCycle 𝓘(ℝ, ℂ) X := by
  rw [SmoothCycle.mem_iff]
  rw [boundary_principalDivisorAJChain_sub, hDeg, zero_smul]

/-- **AJ-chain difference for a principal divisor is a smooth cycle.**
Specialises `principalDivisorAJChain_sub_mem_smoothCycle_of_degree_zero`
through `residue_theorem` (`(principalDivisorMap f).degree = 0`). -/
lemma principalDivisorAJChain_principalDivisorMap_sub_mem_smoothCycle
    (B B' : AbelJacobiInput α h) (f : MeromorphicNonzero X) :
    B.principalDivisorAJChain (principalDivisorMap f)
      - B'.principalDivisorAJChain (principalDivisorMap f)
      ∈ SmoothCycle 𝓘(ℝ, ℂ) X :=
  principalDivisorAJChain_sub_mem_smoothCycle_of_degree_zero B B'
    (JacobianChallenge.residue_theorem f)

/-! ## Period-vector difference lies in `periodLatticeImage` -/

/-- **The chain-level period-vector difference lies in the period
lattice image.** For two `AbelJacobiInput` values and any
`f : MeromorphicNonzero X`,

```
complexChainPeriodVector α (B.principalDivisorAJChain (principalDivisorMap f))
  - complexChainPeriodVector α (B'.principalDivisorAJChain (principalDivisorMap f))
  ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α.
```

Proof: the difference of the chains is a smooth cycle (degree of
`principalDivisorMap f` is zero by `residue_theorem`); the period
vector of a cycle is exactly `periodVector` evaluated on the cycle,
hence lies in the period lattice image by definition. -/
theorem complexChainPeriodVector_principalDivisorAJChain_principalDivisorMap_sub_mem
    (B B' : AbelJacobiInput α h) (f : MeromorphicNonzero X) :
    complexChainPeriodVector α
        (B.principalDivisorAJChain (principalDivisorMap f))
      - complexChainPeriodVector α
          (B'.principalDivisorAJChain (principalDivisorMap f))
      ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α := by
  -- Combine the chain-side subtraction with the cycle witness.
  rw [← complexChainPeriodVector_sub α]
  -- Package the chain difference as a smooth cycle.
  set Z : SmoothCycle 𝓘(ℝ, ℂ) X :=
    ⟨B.principalDivisorAJChain (principalDivisorMap f)
        - B'.principalDivisorAJChain (principalDivisorMap f),
      principalDivisorAJChain_principalDivisorMap_sub_mem_smoothCycle B B' f⟩
    with hZ
  have hZ_coe : (Z : SmoothChain 𝓘(ℝ, ℂ) X)
      = B.principalDivisorAJChain (principalDivisorMap f)
        - B'.principalDivisorAJChain (principalDivisorMap f) := rfl
  rw [← hZ_coe]
  -- The chain-period of a cycle equals `periodVector` evaluated on it.
  rw [complexChainPeriodVector_of_cycle_eq_periodVector]
  -- And `periodVector data α c` is in `periodLatticeImage` by definition.
  exact ⟨Z, rfl⟩

/-! ## Path-choice independence of `dischargedGenerators` -/

/-- **`dischargedGenerators` is independent of the `AbelJacobiInput`
choice.** Two `AbelJacobiInput` values `B B' : AbelJacobiInput α h`
(over the same basis and discreteness bundle) yield the same set of
discharged generators. -/
theorem dischargedGenerators_eq
    (B B' : AbelJacobiInput α h) :
    B.dischargedGenerators = B'.dischargedGenerators := by
  ext f
  refine ⟨fun hB => ?_, fun hB' => ?_⟩
  · -- f ∈ B.dischargedGenerators ⇒ f ∈ B'.dischargedGenerators.
    show complexChainPeriodVector α
          (B'.principalDivisorAJChain (principalDivisorMap f))
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α
    have hdiff :
        complexChainPeriodVector α
            (B.principalDivisorAJChain (principalDivisorMap f))
          - complexChainPeriodVector α
              (B'.principalDivisorAJChain (principalDivisorMap f))
          ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α :=
      complexChainPeriodVector_principalDivisorAJChain_principalDivisorMap_sub_mem B B' f
    have heq :
        complexChainPeriodVector α
            (B'.principalDivisorAJChain (principalDivisorMap f))
          = complexChainPeriodVector α
              (B.principalDivisorAJChain (principalDivisorMap f))
            - (complexChainPeriodVector α
                  (B.principalDivisorAJChain (principalDivisorMap f))
                - complexChainPeriodVector α
                    (B'.principalDivisorAJChain (principalDivisorMap f))) := by
      abel
    rw [heq]
    exact sub_mem hB hdiff
  · -- f ∈ B'.dischargedGenerators ⇒ f ∈ B.dischargedGenerators (symmetric).
    show complexChainPeriodVector α
          (B.principalDivisorAJChain (principalDivisorMap f))
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α
    have hdiff :
        complexChainPeriodVector α
            (B.principalDivisorAJChain (principalDivisorMap f))
          - complexChainPeriodVector α
              (B'.principalDivisorAJChain (principalDivisorMap f))
          ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α :=
      complexChainPeriodVector_principalDivisorAJChain_principalDivisorMap_sub_mem B B' f
    have heq :
        complexChainPeriodVector α
            (B.principalDivisorAJChain (principalDivisorMap f))
          = complexChainPeriodVector α
              (B'.principalDivisorAJChain (principalDivisorMap f))
            + (complexChainPeriodVector α
                  (B.principalDivisorAJChain (principalDivisorMap f))
                - complexChainPeriodVector α
                    (B'.principalDivisorAJChain (principalDivisorMap f))) := by
      abel
    rw [heq]
    exact add_mem hB' hdiff

/-! ## Path-choice independence of `AbelGeneratorPeriodCondition` -/

/-- **`AbelGeneratorPeriodCondition` is independent of the
`AbelJacobiInput` choice.** Direct corollary of `dischargedGenerators_eq`
through the universal-discharge characterisation. -/
theorem abelGeneratorPeriodCondition_iff_of_inputs
    (B B' : AbelJacobiInput α h) :
    AbelGeneratorPeriodCondition B ↔ AbelGeneratorPeriodCondition B' := by
  rw [B.abelGeneratorPeriodCondition_iff_dischargedGenerators_eq_univ,
      B'.abelGeneratorPeriodCondition_iff_dischargedGenerators_eq_univ,
      dischargedGenerators_eq B B']

/-- **`AbelHypothesis` from `AbelGeneratorPeriodCondition` on a witness
`AbelJacobiInput`.** Given `AbelGeneratorPeriodCondition B'` for any
witness `B'`, the universal-quantifier transport via
`abelGeneratorPeriodCondition_iff_of_inputs` yields the per-generator
condition for `B`, hence `AbelHypothesis B`. -/
theorem abelHypothesis_of_abelGeneratorPeriodCondition_witness
    (B B' : AbelJacobiInput α h)
    (hGen : AbelGeneratorPeriodCondition B') :
    AbelHypothesis B :=
  abelHypothesis_of_abelGeneratorPeriodCondition B
    ((abelGeneratorPeriodCondition_iff_of_inputs B B').mpr hGen)

end AbelJacobiInput

end JacobianChallenge

end
