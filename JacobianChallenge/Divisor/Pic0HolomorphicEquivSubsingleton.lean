/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.MeromorphicNonzeroHolomorphicEquivTransport

set_option linter.unusedSectionVars false

/-! # `Subsingleton (Pic0 X)` transports along a biholomorphism

If `Y` has `Subsingleton (Pic0 Y)` and there is a biholomorphism
`e : X ≃ω Y`, then `Subsingleton (Pic0 X)`.

This closes the keystone gap in
`HasPic0AnalyticEquivSubsingletonOmegaRS.lean`: HJAE X from a
biholomorphism `X ≃ω RS` previously required `[Subsingleton (Pic0 X)]`
as an extra hypothesis on top of the biholomorphism; with this chip
the assumption is automatic from `[Subsingleton (Pic0 RS)]` (which is
already unconditional in tree).

## What this file ships

* `subsingleton_pic0_of_holomorphicEquiv` — Subsingleton (Pic0 X) from a
  biholomorphism `X ≃ω Y` + Subsingleton (Pic0 Y).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u v

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable {Y : Type v}
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [T2Space Y] [CompactSpace Y]
  [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-- **Key lemma**: the underlying `Div X` of any `D : Div0 X` is in
`PrincDiv X` provided `Pic0 Y` is subsingleton. -/
private theorem Div0_val_mem_PrincDiv_of_pic0Y_subsingleton
    [hY : Subsingleton (Pic0 Y)] (e : HolomorphicEquiv X Y) (D : Div0 X) :
    (D : Div X) ∈ PrincDiv X := by
  -- Push D to a divisor on Y via comap of the symm homeomorphism.
  let φ : X ≃ₜ Y := e.toHomeomorph
  set D' : Div Y := Div.comap φ.symm (D : Div X) with hD'_def
  -- D' has degree zero (degree preserved under comap).
  have hD'_deg : D' ∈ Div0 Y := by
    show Div.degreeHom D' = 0
    show Div.degree D' = 0
    rw [hD'_def]
    rw [Div.degree_comap]
    have hD : (D : Div X) ∈ Div0 X := D.2
    exact hD
  -- Subsingleton (Pic0 Y) implies every degree-zero divisor on Y is principal.
  have hD'_princ : D' ∈ PrincDiv Y := by
    -- The quotient class of ⟨D', hD'_deg⟩ in Pic0 Y equals 0.
    have h0_eq :
        (⟨D', hD'_deg⟩ : Div0 Y) - 0 ∈ (PrincDiv Y).addSubgroupOf (Div0 Y) := by
      have :
          (QuotientAddGroup.mk (s := (PrincDiv Y).addSubgroupOf (Div0 Y))
              ⟨D', hD'_deg⟩ : Pic0 Y)
          = QuotientAddGroup.mk (s := (PrincDiv Y).addSubgroupOf (Div0 Y))
              (0 : Div0 Y) := hY.elim _ _
      rw [QuotientAddGroup.eq] at this
      -- this : -⟨D', hD'_deg⟩ + 0 ∈ ...
      have h_neg :
          - (⟨D', hD'_deg⟩ : Div0 Y) ∈ (PrincDiv Y).addSubgroupOf (Div0 Y) := by
        simpa using this
      -- D' - 0 = D' = -(-D').
      have :
          (⟨D', hD'_deg⟩ : Div0 Y)
            ∈ (PrincDiv Y).addSubgroupOf (Div0 Y) := by
        have := neg_mem h_neg
        simpa using this
      simpa using this
    -- Underlying Div Y of ⟨D', hD'_deg⟩ - 0 = D'.
    have h_underlying : (⟨D', hD'_deg⟩ : Div0 Y).val = D' := rfl
    -- addSubgroupOf membership iff val membership in PrincDiv Y.
    have : (⟨D', hD'_deg⟩ : Div0 Y).val ∈ PrincDiv Y := by
      have := h0_eq
      simp at this
      exact this
    rw [h_underlying] at this
    exact this
  -- Now pull back to X: comap φ maps PrincDiv Y into PrincDiv X.
  have h_pullback : Div.comap φ D' ∈ PrincDiv X := by
    have h_in_image : Div.comap φ D' ∈
        (PrincDiv Y).map (Div.comap φ) :=
      AddSubgroup.mem_map.mpr ⟨D', hD'_princ, rfl⟩
    exact Div.comap_PrincDiv_le e h_in_image
  -- Identify: comap φ D' = (D : Div X).
  have h_round : Div.comap φ D' = (D : Div X) := by
    rw [hD'_def]
    apply Function.locallyFinsuppWithin.ext
    intro x
    rw [Div.comap_apply, Div.comap_apply]
    show (D : Div X) (φ.symm (φ x)) = (D : Div X) x
    rw [φ.symm_apply_apply x]
  rw [← h_round]
  exact h_pullback

/-- **Subsingleton (Pic0 X) from a biholomorphism `X ≃ω Y` and
Subsingleton (Pic0 Y).** -/
theorem subsingleton_pic0_of_holomorphicEquiv
    [Subsingleton (Pic0 Y)] (e : HolomorphicEquiv X Y) :
    Subsingleton (Pic0 X) := by
  refine ⟨?_⟩
  intro α β
  -- Suffices: any two quotient classes are equal, equivalently every class
  -- equals 0 (i.e., underlying Div X is in PrincDiv X).
  induction α using QuotientAddGroup.induction_on with
  | H D =>
    induction β using QuotientAddGroup.induction_on with
    | H D' =>
      -- Goal: ⟦D⟧ = ⟦D'⟧ in Pic0 X.
      show (QuotientAddGroup.mk (s := (PrincDiv X).addSubgroupOf (Div0 X)) D : Pic0 X)
          = QuotientAddGroup.mk (s := (PrincDiv X).addSubgroupOf (Div0 X)) D'
      rw [QuotientAddGroup.eq]
      -- Goal: -D + D' ∈ (PrincDiv X).addSubgroupOf (Div0 X)
      -- Reduce to underlying Div X membership in PrincDiv X.
      show (-D + D' : Div0 X).val ∈ PrincDiv X
      exact Div0_val_mem_PrincDiv_of_pic0Y_subsingleton e (-D + D')

end JacobianChallenge

end
