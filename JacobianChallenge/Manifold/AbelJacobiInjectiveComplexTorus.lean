/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodLatticeImageComplexTorusReverse
import JacobianChallenge.Manifold.C3FullInputExtSymp

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # `AbelJacobiInjectiveSymp` on T_L, unconditional

Closes one of the four open classical hypotheses on `T_L = ℂ ⧸ L`.
The canonical `AbelJacobiInputSymp` on T_L has its AJ point map
equal to `Q ↦ [fun _ => Q.out] mod periodLatticeImage` (from
`canonicalAbelJacobiInputSymp_abelJacobiPoint`). Combined with the
characterization `periodLatticeImage ≅ L` (from
`PeriodLatticeImageComplexTorusReverse`), injectivity reduces to:

  `Q₁.out - Q₂.out ∈ L → Q₁ = Q₂` (on T_L = ℂ ⧸ L).

This is just `Quotient.out_eq` + closure of `mk` under cosets.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## AJ-point injectivity on the canonical input -/

/-- **The canonical AJ input on T_L has injective AJ-point map.**

Proof structure:
1. `abelJacobiPoint Q = [fun _ => Q.out]` by
   `canonicalAbelJacobiInputSymp_abelJacobiPoint`.
2. Equality of two quotient classes ↔ difference in periodLatticeImage
   (via `QuotientAddGroup.eq`).
3. By `exists_const_of_mem_periodLatticeImage`, the constant function
   has its value in `L`.
4. Hence `Q₂.out - Q₁.out ∈ L`, so `Q₂.out = Q₁.out + z` with `z ∈ L`,
   and `π(Q₂.out) = π(Q₁.out + z) = π(Q₁.out)`, i.e., `Q₂ = Q₁`. -/
theorem abelJacobiInjective_complexTorus
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L)) :
    AbelJacobiInjectiveSymp (canonicalAbelJacobiInputSymp L h) := by
  intro _hpos Q₁ Q₂ hQ
  -- hQ : (canonicalAbelJacobiInputSymp L h).abelJacobiPoint Q₁
  --        = (canonicalAbelJacobiInputSymp L h).abelJacobiPoint Q₂
  -- Rewrite both sides using the explicit formula.
  rw [canonicalAbelJacobiInputSymp_abelJacobiPoint,
      canonicalAbelJacobiInputSymp_abelJacobiPoint] at hQ
  -- hQ : QuotientAddGroup.mk (fun _ => Q₁.out) = QuotientAddGroup.mk (fun _ => Q₂.out)
  -- (mod (PeriodLatticeOfRankTwoG.ofSymplectic ... h).lattice).
  have hMem :
      -(fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => Q₁.out)
        + (fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => Q₂.out)
      ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
          (basis_g_dz L) := by
    have := QuotientAddGroup.eq.mp hQ
    rwa [PeriodLatticeOfRankTwoG.ofSymplectic_lattice] at this
  -- Compute the lhs as `fun _ => -Q₁.out + Q₂.out`.
  have h_pt :
      (-(fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => Q₁.out)
        + (fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => Q₂.out))
        = fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => -Q₁.out + Q₂.out := by
    funext j
    show -Q₁.out + Q₂.out = -Q₁.out + Q₂.out
    rfl
  rw [h_pt] at hMem
  -- By the characterization, ∃ z ∈ L, the vec = fun _ => z.
  obtain ⟨z, hzL, hz_eq⟩ :=
    exists_const_of_mem_periodLatticeImage L hMem
  -- z = -Q₁.out + Q₂.out and z ∈ L.
  -- Need: Q₂.out = Q₁.out + z (mod L), then π(Q₂.out) = π(Q₁.out).
  have h_val : -Q₁.out + Q₂.out = z := by
    have := congrFun hz_eq.symm (⟨0, by rw [genus_eq_one L]; exact Nat.zero_lt_one⟩ :
        Fin (JacobianChallenge.genus (ℂ ⧸ L)))
    exact this.symm
  -- So Q₂.out - Q₁.out = z ∈ L.
  -- Conclude Q₂ = Q₁ via π(Q₁.out) = Q₁ + π Q₂.out = Q₂.
  have h_in_L : Q₂.out - Q₁.out ∈ L := by
    have : Q₂.out - Q₁.out = z := by linear_combination h_val
    rw [this]; exact hzL
  -- π(Q₂.out - Q₁.out) = 0 in T_L (since the diff is in L).
  have h_pi_diff_zero : L.mkQ (Q₂.out - Q₁.out) = 0 := by
    rw [Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero L).mpr h_in_L
  -- L.mkQ (Q₂.out) - L.mkQ (Q₁.out) = 0, hence L.mkQ Q₂.out = L.mkQ Q₁.out.
  have h_mkQ_eq : L.mkQ Q₂.out = L.mkQ Q₁.out := by
    have h_sub : L.mkQ (Q₂.out - Q₁.out) = L.mkQ Q₂.out - L.mkQ Q₁.out :=
      map_sub L.mkQ _ _
    rw [h_pi_diff_zero] at h_sub
    exact sub_eq_zero.mp h_sub.symm
  -- L.mkQ Q.out = Q for any Q : ℂ ⧸ L (by Quotient.out_eq).
  have h_Q₁ : L.mkQ Q₁.out = Q₁ := by
    show (Quotient.mk'' Q₁.out : ℂ ⧸ L) = Q₁
    exact Quotient.out_eq Q₁
  have h_Q₂ : L.mkQ Q₂.out = Q₂ := by
    show (Quotient.mk'' Q₂.out : ℂ ⧸ L) = Q₂
    exact Quotient.out_eq Q₂
  rw [h_Q₁, h_Q₂] at h_mkQ_eq
  exact h_mkQ_eq.symm

end ComplexTorus

end JacobianChallenge

end
