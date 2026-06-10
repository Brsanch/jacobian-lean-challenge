/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.TorusChordRelations
import JacobianChallenge.Manifold.JacobiInversionInjectiveComplexTorus

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Abel's converse on the torus from forward Abel:
`TLAbelConverseHypothesis ⟸ TLDivSumHypothesis`

**Headline**: `tlAbelConverseHypothesis_of_tlDivSum` discharges the named
hypothesis `TLAbelConverseHypothesis L` (Abel's converse: every balanced
degree-0 divisor on `T_L` is principal) **given only**
`TLDivSumHypothesis L` (forward Abel). The handoff had priced this
hypothesis as a standalone Weierstrass-σ construction (`~500–800` LOC of
new product-expansion analysis); instead the chord-and-tangent route
through mathlib's `℘` closes it from the *other* named hypothesis, which
the C3 consumer requires anyway.

Argument: the chord relation (`TorusChordRelations.lean`) makes

  `ψ : u ↦ [ [u] − [0] ] : (ℂ ⧸ L) →+ Div (ℂ ⧸ L) ⧸ PrincDiv (ℂ ⧸ L)`

an additive homomorphism. A degree-0 divisor `D = ∑ n_x·[x]` satisfies
`D = ∑ n_x·([x] − [0])` (the `[0]`-corrections cancel by degree 0), so
`[D] = ψ(∑ n_x • x) = ψ(evalSum D)`. The balance condition
`evalSum D = 0` then gives `[D] = 0`, i.e. `D ∈ PrincDiv`.

**Consequence** (`nonempty_C3FullInputExtSymp_complexTorus_of_TLDivSum`):
the full C3 closure on `T_L` is now conditional on the SINGLE named
hypothesis `TLDivSumHypothesis L`, halving the named-hypothesis pile of
`nonempty_C3FullInputExtSymp_complexTorus_of_two_named_hypotheses`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Set

namespace JacobianChallenge

namespace ComplexTorus

/-! ## Divisors as sums of singles -/

/-- A divisor on a compact Hausdorff space is the sum of its single-point
components over its support. -/
lemma div_eq_sum_single {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [DecidableEq X] (D : Div X) :
    D = ∑ x ∈ D.supportFinset, ((D : X → ℤ) x) • Div.single x := by
  ext q
  have hcoe : ((∑ x ∈ D.supportFinset,
      ((D : X → ℤ) x) • Div.single x : Div X) : X → ℤ) q
      = ∑ x ∈ D.supportFinset, ((D : X → ℤ) x) * (if q = x then 1 else 0) := by
    rw [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply,
      Div.single_apply, smul_eq_mul]
  rw [hcoe]
  have hite : ∀ x ∈ D.supportFinset,
      ((D : X → ℤ) x) * (if q = x then 1 else 0)
        = if q = x then (D : X → ℤ) x else 0 := by
    intro x _
    by_cases h : q = x
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [Finset.sum_congr rfl hite, Finset.sum_ite_eq]
  by_cases hq : q ∈ D.supportFinset
  · rw [if_pos hq]
  · rw [if_neg hq, Div.apply_eq_zero_of_notMem_supportFinset hq]

variable (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- We fix the `DecidableEq (ℂ ⧸ L)` instance to `Classical.decEq` (the
repo-standard choice) so `Div.single` statements elaborate. -/
noncomputable local instance : DecidableEq (ℂ ⧸ L) := Classical.decEq _

/-! ## The headline -/

/-- **Abel's converse on `T_L` from forward Abel.** Every degree-zero
divisor on the complex torus whose support-weighted sum vanishes is
principal, given `TLDivSumHypothesis L` alone. The Weierstrass-σ
construction is not needed: the chord relation supplies the group law,
and the `[0]`-corrections cancel by the degree-0 constraint. -/
theorem tlAbelConverseHypothesis_of_tlDivSum (hTL : TLDivSumHypothesis L) :
    TLAbelConverseHypothesis L := by
  intro D hsum
  classical
  set Dd : Div (ℂ ⧸ L) := (D : Div (ℂ ⧸ L)) with hDd
  -- Degree zero, from `Div0` membership.
  have hdeg : Dd.degree = 0 := by
    have hker := D.2
    exact hker
  -- The quotient by the principal subgroup.
  set P : AddSubgroup (Div (ℂ ⧸ L)) := PrincDiv (ℂ ⧸ L) with hP
  set π : Div (ℂ ⧸ L) →+ Div (ℂ ⧸ L) ⧸ P := QuotientAddGroup.mk' P with hπ
  -- `u ↦ π([u] − [0])` is additive, by the chord relation.
  have hψadd : ∀ u v : ℂ ⧸ L,
      π (Div.single (u + v) - Div.single 0)
        = π (Div.single u - Div.single 0)
          + π (Div.single v - Div.single 0) := by
    intro u v
    rw [← map_add]
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    have heq : (Div.single (u + v) - Div.single 0)
        - (Div.single u - Div.single 0 + (Div.single v - Div.single 0))
        = -(Div.single u + Div.single v - Div.single (u + v)
            - Div.single 0) := by
      abel
    rw [heq]
    exact neg_mem (chord_relation L hTL u v)
  set ψ : (ℂ ⧸ L) →+ Div (ℂ ⧸ L) ⧸ P :=
    AddMonoidHom.mk' (fun u => π (Div.single u - Div.single 0))
      (fun u v => hψadd u v) with hψ
  -- The degree-0 decomposition into `[x] − [0]` blocks.
  have hDd_sum : (∑ x ∈ Dd.supportFinset,
      ((Dd : (ℂ ⧸ L) → ℤ) x) • (Div.single x - Div.single 0)) = Dd := by
    have hsplit : ∀ x ∈ Dd.supportFinset,
        ((Dd : (ℂ ⧸ L) → ℤ) x) • (Div.single x - Div.single 0)
          = ((Dd : (ℂ ⧸ L) → ℤ) x) • Div.single x
            - ((Dd : (ℂ ⧸ L) → ℤ) x) • Div.single (0 : ℂ ⧸ L) :=
      fun x _ => smul_sub _ _ _
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib,
      ← Finset.sum_smul]
    have hdeg' : (∑ x ∈ Dd.supportFinset, (Dd : (ℂ ⧸ L) → ℤ) x) = 0 := hdeg
    rw [hdeg', zero_smul, sub_zero, ← div_eq_sum_single Dd]
  -- Push through the quotient.
  have hπD : π Dd = 0 := by
    rw [← hDd_sum, map_sum]
    have hterm : ∀ x ∈ Dd.supportFinset,
        π (((Dd : (ℂ ⧸ L) → ℤ) x) • (Div.single x - Div.single 0))
          = ((Dd : (ℂ ⧸ L) → ℤ) x) • ψ x := by
      intro x _
      rw [map_zsmul]
      rfl
    rw [Finset.sum_congr rfl hterm]
    have hsum_hom : (∑ x ∈ Dd.supportFinset, ((Dd : (ℂ ⧸ L) → ℤ) x) • ψ x)
        = ψ (∑ x ∈ Dd.supportFinset, ((Dd : (ℂ ⧸ L) → ℤ) x) • x) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [map_zsmul]
    rw [hsum_hom, hsum, map_zero]
  -- Membership.
  exact (QuotientAddGroup.eq_zero_iff Dd).mp hπD

/-! ## Consequence: the T_L C3 closure needs only forward Abel -/

/-- **Full closure of the challenge for `T_L` from ONE named hypothesis.**
`Nonempty (C3FullInputExtSymp (ℂ ⧸ L))` from `TLDivSumHypothesis L`
alone — `TLAbelConverseHypothesis L` (formerly priced as a standalone
Weierstrass-σ arc) is now a theorem given forward Abel. -/
theorem nonempty_C3FullInputExtSymp_complexTorus_of_TLDivSum
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L))
    (hTL : TLDivSumHypothesis L) :
    Nonempty (JacobianChallenge.C3FullInputExtSymp (ℂ ⧸ L)) :=
  nonempty_C3FullInputExtSymp_complexTorus_of_two_named_hypotheses L h hTL
    (tlAbelConverseHypothesis_of_tlDivSum L hTL)

end ComplexTorus

end JacobianChallenge

end
