/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.MeromorphicNonzeroHolomorphicEquivTransport

set_option linter.unusedSectionVars false

/-! # `Pic0 X ≃+ Pic0 Y` along a biholomorphism

A `HolomorphicEquiv X Y` induces an isomorphism of Picard groups of
degree-zero divisors. Built by descending `comap0Equiv` through the
quotient via `QuotientAddGroup.congr`, with subgroup-image identity
coming from `Div.comap_PrincDiv_le` applied to `e` and `e.symm`.

## What this file ships

* `pic0_subgroup_image_eq` — image of `(PrincDiv X).addSubgroupOf (Div0 X)`
  under the comap0Equiv coincides with `(PrincDiv Y).addSubgroupOf (Div0 Y)`.
* `pic0_holomorphicEquivCongr` — `Pic0 X ≃+ Pic0 Y`.

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

/-- **PrincDiv-respecting:** the image under `comap0Equiv e.toHomeomorph`
of `(PrincDiv X).addSubgroupOf (Div0 X)` equals
`(PrincDiv Y).addSubgroupOf (Div0 Y)`. -/
theorem pic0_subgroup_image_eq (e : HolomorphicEquiv X Y) :
    ((PrincDiv X).addSubgroupOf (Div0 X)).map
        (Div.comap0Equiv e.toHomeomorph : Div0 X →+ Div0 Y)
      = (PrincDiv Y).addSubgroupOf (Div0 Y) := by
  apply le_antisymm
  · -- Forward inclusion: comap0Equiv sends X-principal divisors to
    -- Y-principal divisors.
    rw [AddSubgroup.map_le_iff_le_comap]
    intro D hD
    -- hD : D.val ∈ PrincDiv X
    show ((Div.comap0Equiv e.toHomeomorph D).val) ∈ PrincDiv Y
    -- (comap0Equiv e.toHomeomorph D).val = Div.comap e.toHomeomorph.symm D.val
    show Div.comap e.toHomeomorph.symm (D : Div X) ∈ PrincDiv Y
    have h_mem_image : Div.comap e.toHomeomorph.symm (D : Div X)
        ∈ (PrincDiv X).map (Div.comap e.symm.toHomeomorph) := by
      have : e.toHomeomorph.symm = e.symm.toHomeomorph := rfl
      rw [this]
      exact AddSubgroup.mem_map.mpr ⟨(D : Div X), hD, rfl⟩
    exact Div.comap_PrincDiv_le e.symm h_mem_image
  · -- Backward inclusion: every PrincDiv Y element comes from a PrincDiv X
    -- element via comap0Equiv.
    intro E hE
    -- hE : E.val ∈ PrincDiv Y
    refine AddSubgroup.mem_map.mpr ⟨(Div.comap0Equiv e.toHomeomorph).symm E, ?_, ?_⟩
    · -- (comap0Equiv.symm E).val = Div.comap e.toHomeomorph E.val ∈ PrincDiv X
      show ((Div.comap0Equiv e.toHomeomorph).symm E).val ∈ PrincDiv X
      show Div.comap e.toHomeomorph (E : Div Y) ∈ PrincDiv X
      have h_mem_image : Div.comap e.toHomeomorph (E : Div Y)
          ∈ (PrincDiv Y).map (Div.comap e.toHomeomorph) :=
        AddSubgroup.mem_map.mpr ⟨(E : Div Y), hE, rfl⟩
      exact Div.comap_PrincDiv_le e h_mem_image
    · exact (Div.comap0Equiv e.toHomeomorph).apply_symm_apply E

/-- **`Pic0 X ≃+ Pic0 Y` along a biholomorphism.** -/
noncomputable def pic0_holomorphicEquivCongr (e : HolomorphicEquiv X Y) :
    Pic0 X ≃+ Pic0 Y :=
  QuotientAddGroup.congr (G' := (PrincDiv X).addSubgroupOf (Div0 X))
    (H' := (PrincDiv Y).addSubgroupOf (Div0 Y))
    (Div.comap0Equiv e.toHomeomorph)
    (pic0_subgroup_image_eq e)

/-! ### Functoriality: refl/symm/trans -/

/-- `Subsingleton (Pic0 X)` is *equivalent* under biholomorphism. -/
theorem subsingleton_pic0_iff_of_holomorphicEquiv (e : HolomorphicEquiv X Y) :
    Subsingleton (Pic0 X) ↔ Subsingleton (Pic0 Y) :=
  Equiv.subsingleton_congr (pic0_holomorphicEquivCongr e).toEquiv

end JacobianChallenge

end
