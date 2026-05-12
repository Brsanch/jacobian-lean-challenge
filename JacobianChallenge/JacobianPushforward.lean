/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Jacobian
import JacobianChallenge.Manifold.NormFMContinuity
import JacobianChallenge.Manifold.LocalMultiplicity

set_option diagnostics.threshold 100

/-! # Honest `Pic0.pushforward` and `Jacobian.pushforward`

ZZ256/ZZ257 (2026-05-11). The honest pushforward
`Pic0 X →+ Pic0 Y` for `f : X → Y` holomorphic and either constant or
non-constant. Combines:

* P1.4 (`PrincDivHonestCandidate_addSubgroupOf_Div0_le_comap_divPushforward`
  in `Manifold/NormFMContinuity.lean`) for non-constant `f`: pushforward of
  a principal divisor on `X` lands in `PrincDiv Y`.
* For constant `f`: `divPushforward` sends every `Div0 X` element to `0`
  in `Div0 Y` (sum tracking), and `0 ∈ PrincDiv Y` trivially.

This file lives downstream of `NormFMContinuity` because of the P1.4
dependency, which the upstream `Jacobian.lean` cannot reach without an
import cycle.
-/

noncomputable section

open scoped ContDiff Manifold

namespace JacobianChallenge

namespace Pic0

variable {X Y Z : Type*}
variable [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
variable [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
variable [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]
variable [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
variable [ChartedSpace ℂ Z] [IsManifold (𝓘(ℂ, ℂ)) ω Z]

/-- Descent lemma packaging the constant + non-constant cases together.

For `f : X → Y` smooth holomorphic, the divisor pushforward
`divPushforward f` sends `PrincDiv X ∩ Div0 X` into `PrincDiv Y ∩ Div0 Y`.

* Constant `f`: image lands at the singleton `{c}`, and degree preservation
  (already known: `divPushforwardHom_mem_Div0`) forces the image divisor
  to be `0`, which lies in any subgroup.
* Non-constant `f`: P1.4
  `PrincDivHonestCandidate_addSubgroupOf_Div0_le_comap_divPushforward`. -/
lemma princDiv_addSubgroupOf_Div0_le_comap_divPushforward
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f) :
    (PrincDiv X).addSubgroupOf (Div0 X) ≤
      ((PrincDiv Y).addSubgroupOf (Div0 Y)).comap (divPushforward f) := by
  classical
  -- `PrincDiv := PrincDivHonestCandidate` definitionally; unfold to expose
  -- the P1.4-compatible statement.
  show (PrincDivHonestCandidate X).addSubgroupOf (Div0 X) ≤
        ((PrincDivHonestCandidate Y).addSubgroupOf (Div0 Y)).comap (divPushforward f)
  by_cases hnc : JacobianChallenge.IsConstantMap f
  · -- Constant `f`: divPushforward sends Div0 X to 0.
    intro D hD
    rw [AddSubgroup.mem_comap]
    -- Show `divPushforward f D ∈ (PrincDiv Y).addSubgroupOf (Div0 Y)`.
    -- It suffices to show the underlying Div0 Y element is 0.
    have hD0 : divPushforward f (D : Div0 X) = 0 := by
      -- divPushforward of constant f: image lands at a single singleton with
      -- weight = degree of D = 0.
      apply Subtype.ext
      show (divPushforward f (D : Div0 X) : Div Y) = (0 : Div Y)
      rw [divPushforward_coe]
      -- divPushforwardHom of constant f sends D to (degree D) · single c = 0.
      obtain ⟨c, hc⟩ := hnc
      -- `hc : ∀ x, f x = c`.
      letI : DecidableEq Y := Classical.decEq Y
      show (Div.singletonMap (Y := Y) f (D : Div X) : Div Y) = (0 : Div Y)
      -- The singletonMap of a constant f sends D to (degD) • single c.
      ext y
      simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
      show ((Div.singletonMap (Y := Y) f (D : Div X) : Div Y) : Y → ℤ) y = 0
      change ((Div.singletonMapFun (Y := Y) f (D : Div X) : Div Y) : Y → ℤ) y = 0
      rw [Div.singletonMapFun_apply]
      -- Factor every term to depend only on `y = c` rather than `y = f x`.
      have hDegSum :
          (∑ x ∈ (D : Div X).supportFinset, (D : Div X) x) = 0 := by
        show Div.degree (D : Div X) = 0
        exact (JacobianChallenge.mem_Div0_iff (D : Div X)).mp D.2
      have hRewrite :
          ∀ x ∈ (D : Div X).supportFinset,
            (D : Div X) x * (if y = f x then (1 : ℤ) else 0)
              = (D : Div X) x * (if y = c then (1 : ℤ) else 0) := by
        intro x _
        rw [hc x]
      rw [Finset.sum_congr rfl hRewrite, ← Finset.sum_mul, hDegSum, zero_mul]
    rw [hD0]
    exact AddSubgroup.zero_mem _
  · -- Non-constant `f`: invoke P1.4 directly.
    exact JacobianChallenge.Manifold.PrincDivHonestCandidate_addSubgroupOf_Div0_le_comap_divPushforward
      hf hnc

/-- The honest pushforward `Pic0 X →+ Pic0 Y` for `f : X → Y` smooth
holomorphic. Descent through `princDiv_addSubgroupOf_Div0_le_comap_divPushforward`. -/
noncomputable def pushforward {f : X → Y}
    (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f) :
    Pic0 X →+ Pic0 Y :=
  QuotientAddGroup.map
    ((PrincDiv X).addSubgroupOf (Div0 X))
    ((PrincDiv Y).addSubgroupOf (Div0 Y))
    (divPushforward f)
    (princDiv_addSubgroupOf_Div0_le_comap_divPushforward hf)

@[simp] lemma pushforward_mk {f : X → Y}
    (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f) (D : Div0 X) :
    pushforward hf (QuotientAddGroup.mk D : Pic0 X)
      = (QuotientAddGroup.mk (divPushforward f D) : Pic0 Y) := rfl

/-- Identity functoriality on `Pic0`. -/
lemma pushforward_id (P : Pic0 X) :
    pushforward (X := X) (Y := X) (f := id) contMDiff_id P = P := by
  refine QuotientAddGroup.induction_on P ?_
  intro D
  rw [pushforward_mk]
  have hDiv : (divPushforward (id : X → X) D : Div X) = (D : Div X) := by
    rw [divPushforward_coe, divPushforwardHom_id_apply]
  have h : divPushforward (id : X → X) D = D := Subtype.ext hDiv
  rw [h]

/-- Composition functoriality on `Pic0`. -/
lemma pushforward_comp
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    {g : Y → Z} (hg : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω g)
    (P : Pic0 X) :
    pushforward (hg.comp hf) P = pushforward hg (pushforward hf P) := by
  refine QuotientAddGroup.induction_on P ?_
  intro D
  rw [pushforward_mk, pushforward_mk, pushforward_mk]
  have hDiv : (divPushforward (g ∘ f) D : Div Z)
      = (divPushforward g (divPushforward f D) : Div Z) := by
    rw [divPushforward_coe, divPushforward_coe, divPushforward_coe,
        divPushforwardHom_comp_apply]
  have h : divPushforward (g ∘ f) D = divPushforward g (divPushforward f D) :=
    Subtype.ext hDiv
  rw [h]

end Pic0

namespace Jacobian

variable {X Y Z : Type*}
variable [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
variable [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
variable [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]
variable [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
variable [ChartedSpace ℂ Z] [IsManifold (𝓘(ℂ, ℂ)) ω Z]

/-- The pushforward `Jacobian X →ₜ+ Jacobian Y` induced by a smooth
holomorphic `f : X → Y`. Continuity is automatic from the discrete topology
on `Jacobian Y`. -/
noncomputable def pushforward {f : X → Y}
    (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f) :
    Jacobian X →ₜ+ Jacobian Y where
  toAddMonoidHom := Pic0.pushforward (X := X) (Y := Y) hf
  continuous_toFun := continuous_of_discreteTopology

/-- Identity functoriality on `Jacobian`. -/
lemma pushforward_id_apply (P : Jacobian X) :
    pushforward (X := X) (Y := X) (f := id) contMDiff_id P = P := by
  change Pic0.pushforward (X := X) (Y := X) (f := id) contMDiff_id P = P
  exact Pic0.pushforward_id P

/-- Composition functoriality on `Jacobian`. -/
lemma pushforward_comp_apply
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    {g : Y → Z} (hg : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω g)
    (P : Jacobian X) :
    pushforward (hg.comp hf) P = pushforward hg (pushforward hf P) := by
  change Pic0.pushforward (hg.comp hf) P
      = Pic0.pushforward hg (Pic0.pushforward hf P)
  exact Pic0.pushforward_comp hf hg P

end Jacobian

end JacobianChallenge

end
