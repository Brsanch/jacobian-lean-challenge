/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor
import Mathlib.Topology.Homeomorph.Defs

set_option linter.unusedSectionVars false

/-! # Divisor transport along a homeomorphism

For a homeomorphism `φ : X ≃ₜ Y` between topological spaces, pulling
back a divisor `D : Div Y` by `φ` gives a divisor on `X`:

* As a function: `x ↦ D (φ x)`.
* Support: `(D ∘ φ).support = φ ⁻¹ D.support`. Locally finite, because
  `φ` is continuous and injective.

Pushing forward by `φ` is the same construction applied to `φ.symm`.
The two are inverses on the level of `AddMonoidHom`s, giving an
`AddEquiv Div X ≃+ Div Y`.

## What this file ships

* `Div.comap φ : Div Y →+ Div X` — pullback along a homeomorphism.
* `Div.comapEquiv φ : Div X ≃+ Div Y` — pair of pullbacks as an
  additive isomorphism.
* `Div.comap_apply` — definitional unfolding.

No `sorry`, no `axiom`. -/

namespace JacobianChallenge

namespace Div

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Pullback of a divisor along a homeomorphism.**

Given a homeomorphism `φ : X ≃ₜ Y` and a divisor `D : Div Y`, builds
the divisor on `X` with underlying function `x ↦ D (φ x)`. -/
noncomputable def comapFun (φ : X ≃ₜ Y) (D : Div Y) : Div X where
  toFun := fun x => D (φ x)
  supportWithinDomain' := by intro _ _; trivial
  supportLocallyFiniteWithinDomain' := by
    intro x _
    -- Use the local finiteness of `D.support` at `φ x ∈ Y`.
    obtain ⟨t, ht_nhds, ht_finite⟩ :=
      D.supportLocallyFiniteWithinDomain (φ x) (Set.mem_univ _)
    refine ⟨φ ⁻¹' t, φ.continuous.continuousAt ht_nhds, ?_⟩
    -- `(φ ⁻¹' t) ∩ (fun x => D (φ x)).support = φ ⁻¹' (t ∩ D.support)`.
    have h_supp :
        (φ ⁻¹' t) ∩ ((fun x => D (φ x))).support
          = φ ⁻¹' (t ∩ D.support) := by
      ext z
      constructor
      · rintro ⟨hzt, hzs⟩
        exact ⟨hzt, hzs⟩
      · rintro ⟨hzt, hzs⟩
        exact ⟨hzt, hzs⟩
    rw [h_supp]
    exact ht_finite.preimage φ.injective.injOn

/-- Pointwise evaluation of `comapFun`. -/
@[simp] lemma comapFun_apply (φ : X ≃ₜ Y) (D : Div Y) (x : X) :
    (comapFun φ D) x = D (φ x) := rfl

/-- `comapFun` of `0` is `0`. -/
@[simp] lemma comapFun_zero (φ : X ≃ₜ Y) :
    comapFun φ (0 : Div Y) = 0 := by
  ext x
  show (0 : Div Y) (φ x) = (0 : Div X) x
  simp

/-- `comapFun` is additive. -/
lemma comapFun_add (φ : X ≃ₜ Y) (D₁ D₂ : Div Y) :
    comapFun φ (D₁ + D₂) = comapFun φ D₁ + comapFun φ D₂ := by
  ext x
  show (D₁ + D₂) (φ x) = comapFun φ D₁ x + comapFun φ D₂ x
  rw [Function.locallyFinsuppWithin.coe_add]
  rfl

/-- **`Div.comap φ`** — pullback of divisors as an `AddMonoidHom`. -/
noncomputable def comap (φ : X ≃ₜ Y) : Div Y →+ Div X where
  toFun := comapFun φ
  map_zero' := comapFun_zero φ
  map_add' := comapFun_add φ

@[simp] lemma comap_apply (φ : X ≃ₜ Y) (D : Div Y) (x : X) :
    (comap φ D) x = D (φ x) := rfl

@[simp] lemma comap_refl (D : Div X) :
    comap (Homeomorph.refl X) D = D := by
  ext x
  show D ((Homeomorph.refl X) x) = D x
  rfl

@[simp] lemma comap_trans (φ : X ≃ₜ Y) {Z : Type*} [TopologicalSpace Z]
    (ψ : Y ≃ₜ Z) (D : Div Z) :
    comap (φ.trans ψ) D = comap φ (comap ψ D) := by
  ext x
  rfl

/-- **`Div.comapEquiv φ`** — the divisor groups of homeomorphic spaces
are canonically isomorphic. -/
noncomputable def comapEquiv (φ : X ≃ₜ Y) : Div X ≃+ Div Y where
  toFun := comap φ.symm
  invFun := comap φ
  left_inv D := by
    ext x
    show D (φ.symm (φ x)) = D x
    rw [Homeomorph.symm_apply_apply]
  right_inv D := by
    ext y
    show D (φ (φ.symm y)) = D y
    rw [Homeomorph.apply_symm_apply]
  map_add' D₁ D₂ := (comap φ.symm).map_add D₁ D₂

@[simp] lemma comapEquiv_apply (φ : X ≃ₜ Y) (D : Div X) (y : Y) :
    (comapEquiv φ D) y = D (φ.symm y) := rfl

@[simp] lemma comapEquiv_symm_apply (φ : X ≃ₜ Y) (D : Div Y) (x : X) :
    ((comapEquiv φ).symm D) x = D (φ x) := rfl

/-! ### Degree preservation under `comap`

For homeomorphic compact Hausdorff spaces, the divisor pullback preserves
the degree. -/

variable [T2Space X] [T2Space Y] [CompactSpace X] [CompactSpace Y]

open Classical in
/-- The supportFinset of `comap φ D` is the φ-preimage of `D.supportFinset`. -/
lemma supportFinset_comap (φ : X ≃ₜ Y) (D : Div Y) :
    (comap φ D).supportFinset = D.supportFinset.image φ.symm := by
  ext x
  rw [mem_supportFinset, Finset.mem_image]
  constructor
  · intro hx
    refine ⟨φ x, ?_, ?_⟩
    · rw [mem_supportFinset]
      simpa using hx
    · exact φ.symm_apply_apply x
  · rintro ⟨y, hy, hyx⟩
    rw [mem_supportFinset] at hy
    have heq : x = φ.symm y := hyx.symm
    subst heq
    show (comap φ D) (φ.symm y) ≠ 0
    rw [comap_apply, φ.apply_symm_apply]
    exact hy

open Classical in
/-- **Degree preservation under `comap`.** For a homeomorphism `φ : X ≃ₜ Y`
between compact Hausdorff spaces, the divisor pullback by `φ` preserves
the integer degree. -/
@[simp] lemma degree_comap (φ : X ≃ₜ Y) (D : Div Y) :
    Div.degree (comap φ D) = Div.degree D := by
  unfold Div.degree
  rw [supportFinset_comap]
  rw [Finset.sum_image
        (fun y₁ _ y₂ _ h => φ.symm.injective h)]
  refine Finset.sum_congr rfl ?_
  intro y _
  show (comap φ D) (φ.symm y) = D y
  rw [comap_apply, φ.apply_symm_apply]

/-- `comap φ` sends `Div0 Y` into `Div0 X`. -/
lemma comap_mem_Div0 (φ : X ≃ₜ Y) {D : Div Y} (hD : D ∈ Div0 Y) :
    comap φ D ∈ Div0 X := by
  have hD' : Div.degree D = 0 := hD
  show Div.degree (comap φ D) = 0
  rw [degree_comap]
  exact hD'

/-- **`Div.comap` restricted to degree-zero divisors.** -/
noncomputable def comap0 (φ : X ≃ₜ Y) : Div0 Y →+ Div0 X :=
  ((comap φ).restrict (Div0 Y)).codRestrict (Div0 X) <| by
    rintro ⟨D, hD⟩
    exact comap_mem_Div0 φ hD

@[simp] lemma comap0_coe (φ : X ≃ₜ Y) (D : Div0 Y) :
    ((comap0 φ D : Div0 X) : Div X) = comap φ (D : Div Y) := rfl

/-- **`Div.comap0Equiv`** — degree-zero divisor groups of homeomorphic
spaces are canonically isomorphic. -/
noncomputable def comap0Equiv (φ : X ≃ₜ Y) : Div0 X ≃+ Div0 Y where
  toFun := comap0 φ.symm
  invFun := comap0 φ
  left_inv := by
    rintro ⟨D, hD⟩
    apply Subtype.ext
    show comap φ (comap φ.symm D) = D
    ext x
    show D (φ.symm (φ x)) = D x
    rw [Homeomorph.symm_apply_apply]
  right_inv := by
    rintro ⟨D, hD⟩
    apply Subtype.ext
    show comap φ.symm (comap φ D) = D
    ext y
    show D (φ (φ.symm y)) = D y
    rw [Homeomorph.apply_symm_apply]
  map_add' D₁ D₂ := (comap0 φ.symm).map_add D₁ D₂

end Div

end JacobianChallenge
