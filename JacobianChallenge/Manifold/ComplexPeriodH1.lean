/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexPeriodSmulRight

/-! # Complex period pairing factored through `H₁` (PL-3e follow-up)

Given a `StokesBoundaryInvariance 𝓘(ℝ, ℂ) X` (the named-hypothesis bundle
carrying a chosen Stokes-boundary subgroup and a chosen submodule of
"closed" real 1-forms), this file delivers the **complex-valued**
analogue of the real `periodPairing : H₁ × closedForms → ℝ` already in
`H1SmoothMod.lean`.

The complex pairing factors through `H₁` against a chosen submodule of
holomorphic 1-forms whose *real and imaginary components* both lie in the
Stokes-closed real submodule. Concretely:

* `closedHolomorphicForms S : Submodule ℂ (HolomorphicOneForm X)` — the
  holomorphic forms `ω` such that `realComponent ω ∈ S.closedForms` and
  `imagComponent ω ∈ S.closedForms`. Closed under ℂ-scalar
  multiplication because `realComponent (z • ω) = Re z • realComponent ω
  − Im z • imagComponent ω` is a ℝ-linear combination of two elements of
  `S.closedForms`, hence still in `S.closedForms` (and similarly for the
  imaginary component).

* `complexPeriodH1 S : S.H1 →+ closedHolomorphicForms S →ₗ[ℂ] ℂ` — the
  factored complex-valued pairing. The H₁-quotient descent uses the real
  `StokesBoundaryInvariance.pairing_vanishes_on_boundaries` applied
  separately to the real and imaginary components.

Compatibility lemmas: this complex pairing agrees with `complexPeriod`
on representatives, and with `complexPeriodBilinear` after composing with
the quotient projection.

## Why this matters

The "period map" `H₁(X; ℤ) → HolomorphicOneForm X →ₗ[ℂ] ℂ` is the
Abel-Jacobi map's domain side. PL-4 (the proper Abel-Jacobi map
`Pic⁰ X ≃ AnalyticTorus X`) is built by composing this homomorphism
with: dualisation, choice of basis of `HolomorphicOneForm X`, and the
quotient by the period lattice image. PL-4 itself is multi-thousand-LOC
classical surface theory and remains blocked; this file delivers the
*algebraic-and-functorial* H₁ side that PL-4 will plug into.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

namespace StokesBoundaryInvariance

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

variable (S : StokesBoundaryInvariance 𝓘(ℝ, ℂ) X)

/-! ## `closedHolomorphicForms` -/

/-- The submodule of holomorphic 1-forms whose real and imaginary
components both lie in `S.closedForms`. Closed under ℂ-scaling via the
identity `realComponent (z • ω) = Re z • realComponent ω − Im z •
imagComponent ω` (and the corresponding identity for `imagComponent`),
which expresses `realComponent (z • ω)` as a ℝ-linear combination of two
already-closed forms. -/
def closedHolomorphicForms : Submodule ℂ (HolomorphicOneForm X) where
  carrier := { om | realComponent om ∈ S.closedForms ∧
                    imagComponent om ∈ S.closedForms }
  zero_mem' := by
    refine ⟨?_, ?_⟩
    · -- `realComponent 0 = 0`.
      have h_zero : realComponent (0 : HolomorphicOneForm X)
          = (0 : SmoothOneForm 𝓘(ℝ, ℂ) X) := by
        refine ContMDiffSection.coe_inj ?_
        funext x
        exact HolomorphicOneForm.realPart_zero x
      rw [h_zero]
      exact S.closedForms.zero_mem
    · have h_zero : imagComponent (0 : HolomorphicOneForm X)
          = (0 : SmoothOneForm 𝓘(ℝ, ℂ) X) := by
        refine ContMDiffSection.coe_inj ?_
        funext x
        exact HolomorphicOneForm.imagPart_zero x
      rw [h_zero]
      exact S.closedForms.zero_mem
  add_mem' := by
    rintro om₁ om₂ ⟨h_re₁, h_im₁⟩ ⟨h_re₂, h_im₂⟩
    refine ⟨?_, ?_⟩
    · rw [realComponent_add]; exact S.closedForms.add_mem h_re₁ h_re₂
    · rw [imagComponent_add]; exact S.closedForms.add_mem h_im₁ h_im₂
  smul_mem' := by
    rintro z om ⟨h_re, h_im⟩
    refine ⟨?_, ?_⟩
    · -- `realComponent (z • om) = z.re • realComponent om - z.im • imagComponent om`.
      rw [realComponent_smul]
      exact S.closedForms.sub_mem (S.closedForms.smul_mem _ h_re)
        (S.closedForms.smul_mem _ h_im)
    · rw [imagComponent_smul]
      exact S.closedForms.add_mem (S.closedForms.smul_mem _ h_im)
        (S.closedForms.smul_mem _ h_re)

@[simp] lemma mem_closedHolomorphicForms {om : HolomorphicOneForm X} :
    om ∈ S.closedHolomorphicForms
      ↔ realComponent om ∈ S.closedForms ∧ imagComponent om ∈ S.closedForms :=
  Iff.rfl

/-! ## Vanishing of `complexPeriod` on boundary × closed-holomorphic -/

lemma complexPeriod_eq_zero_of_boundary
    {c : SmoothCycle 𝓘(ℝ, ℂ) X} (hc : c ∈ S.boundaries)
    {om : HolomorphicOneForm X} (hom : om ∈ S.closedHolomorphicForms) :
    complexPeriod c om = 0 := by
  obtain ⟨h_re, h_im⟩ := hom
  have h_re_zero : SmoothCycle.integrate c (realComponent om) = 0 :=
    S.pairing_vanishes_on_boundaries c hc _ h_re
  have h_im_zero : SmoothCycle.integrate c (imagComponent om) = 0 :=
    S.pairing_vanishes_on_boundaries c hc _ h_im
  unfold complexPeriod
  rw [h_re_zero, h_im_zero]
  push_cast
  ring

lemma complexPeriod_eq_of_sub_mem_boundaries
    {c₁ c₂ : SmoothCycle 𝓘(ℝ, ℂ) X}
    (h : c₁ - c₂ ∈ S.boundaries)
    {om : HolomorphicOneForm X} (hom : om ∈ S.closedHolomorphicForms) :
    complexPeriod c₁ om = complexPeriod c₂ om := by
  have hzero : complexPeriod (c₁ - c₂) om = 0 :=
    S.complexPeriod_eq_zero_of_boundary h hom
  -- Use `complexPeriodHom om : SmoothCycle →+ ℂ` (additive in cycle arg).
  have h_sub : complexPeriod (c₁ - c₂) om
      = complexPeriod c₁ om - complexPeriod c₂ om :=
    (complexPeriodHom om).map_sub c₁ c₂
  rw [h_sub] at hzero
  exact sub_eq_zero.mp hzero

/-! ## Factored complex pairing on `H₁ × closedHolomorphicForms` -/

/-- The auxiliary cycle-level complex pairing, restricted to closed
holomorphic forms. -/
def complexPeriodAux (c : SmoothCycle 𝓘(ℝ, ℂ) X)
    (omCl : S.closedHolomorphicForms) : ℂ :=
  complexPeriod c (omCl : HolomorphicOneForm X)

lemma complexPeriodAux_well_defined
    (c₁ c₂ : SmoothCycle 𝓘(ℝ, ℂ) X) (hcc : c₁ - c₂ ∈ S.boundaries)
    (omCl : S.closedHolomorphicForms) :
    S.complexPeriodAux c₁ omCl = S.complexPeriodAux c₂ omCl := by
  unfold complexPeriodAux
  exact S.complexPeriod_eq_of_sub_mem_boundaries hcc omCl.property

/-- The factored complex pairing `H₁ → closedHolomorphicForms → ℂ`. -/
def complexPeriodH1 : S.H1 → S.closedHolomorphicForms → ℂ := by
  intro hclass omCl
  refine Quotient.liftOn' hclass (fun c => S.complexPeriodAux c omCl) ?_
  intro c₁ c₂ hcc
  have hmem : -c₁ + c₂ ∈ S.boundaries :=
    QuotientAddGroup.leftRel_apply.mp hcc
  have hmem' : c₂ - c₁ ∈ S.boundaries := by
    have : (-c₁ + c₂) = c₂ - c₁ := by abel
    rwa [this] at hmem
  symm
  exact S.complexPeriodAux_well_defined c₂ c₁ hmem' omCl

@[simp] lemma complexPeriodH1_mk
    (c : SmoothCycle 𝓘(ℝ, ℂ) X) (omCl : S.closedHolomorphicForms) :
    S.complexPeriodH1 (S.proj c) omCl
      = complexPeriod c (omCl : HolomorphicOneForm X) := rfl

/-! ## Linearity of the factored complex pairing -/

@[simp] lemma complexPeriodH1_zero_left (omCl : S.closedHolomorphicForms) :
    S.complexPeriodH1 (0 : S.H1) omCl = 0 := by
  show S.complexPeriodH1 (S.proj 0) omCl = 0
  rw [complexPeriodH1_mk]
  exact complexPeriod_zero_left (omCl : HolomorphicOneForm X)

lemma complexPeriodH1_add_left (h₁ h₂ : S.H1) (omCl : S.closedHolomorphicForms) :
    S.complexPeriodH1 (h₁ + h₂) omCl
      = S.complexPeriodH1 h₁ omCl + S.complexPeriodH1 h₂ omCl := by
  refine Quotient.inductionOn₂' h₁ h₂ ?_
  intro c₁ c₂
  have h_add : S.proj c₁ + S.proj c₂ = S.proj (c₁ + c₂) := by
    rw [← map_add S.proj]
  show S.complexPeriodH1 (S.proj c₁ + S.proj c₂) omCl
      = S.complexPeriodH1 (S.proj c₁) omCl + S.complexPeriodH1 (S.proj c₂) omCl
  rw [h_add, complexPeriodH1_mk, complexPeriodH1_mk, complexPeriodH1_mk]
  exact complexPeriod_add_left c₁ c₂ (omCl : HolomorphicOneForm X)

@[simp] lemma complexPeriodH1_zero_right (h : S.H1) :
    S.complexPeriodH1 h (0 : S.closedHolomorphicForms) = 0 := by
  refine Quotient.inductionOn' h ?_
  intro c
  show S.complexPeriodH1 (S.proj c) (0 : S.closedHolomorphicForms) = 0
  rw [complexPeriodH1_mk]
  -- `((0 : closedHolomorphicForms) : HolomorphicOneForm X) = 0`.
  show complexPeriod c ((0 : S.closedHolomorphicForms) : HolomorphicOneForm X) = 0
  have h0 : ((0 : S.closedHolomorphicForms) : HolomorphicOneForm X) = 0 := rfl
  rw [h0]
  -- `complexPeriod c 0 = 0` via the bundled `complexPeriodLinearMap c`.
  exact (complexPeriodLinearMap c).map_zero

lemma complexPeriodH1_add_right (h : S.H1)
    (omCl₁ omCl₂ : S.closedHolomorphicForms) :
    S.complexPeriodH1 h (omCl₁ + omCl₂)
      = S.complexPeriodH1 h omCl₁ + S.complexPeriodH1 h omCl₂ := by
  refine Quotient.inductionOn' h ?_
  intro c
  show S.complexPeriodH1 (S.proj c) (omCl₁ + omCl₂)
      = S.complexPeriodH1 (S.proj c) omCl₁ + S.complexPeriodH1 (S.proj c) omCl₂
  rw [complexPeriodH1_mk, complexPeriodH1_mk, complexPeriodH1_mk]
  have h_add : ((omCl₁ + omCl₂ : S.closedHolomorphicForms) : HolomorphicOneForm X)
      = (omCl₁ : HolomorphicOneForm X) + (omCl₂ : HolomorphicOneForm X) := rfl
  rw [h_add]
  exact complexPeriod_add_right c _ _

lemma complexPeriodH1_smul_right (h : S.H1) (z : ℂ)
    (omCl : S.closedHolomorphicForms) :
    S.complexPeriodH1 h (z • omCl)
      = z * S.complexPeriodH1 h omCl := by
  refine Quotient.inductionOn' h ?_
  intro c
  show S.complexPeriodH1 (S.proj c) (z • omCl) = z * S.complexPeriodH1 (S.proj c) omCl
  rw [complexPeriodH1_mk, complexPeriodH1_mk]
  have h_smul : ((z • omCl : S.closedHolomorphicForms) : HolomorphicOneForm X)
      = z • (omCl : HolomorphicOneForm X) := rfl
  rw [h_smul]
  exact complexPeriod_smul_right c z _

/-! ## Bundled `S.H1 →+ S.closedHolomorphicForms →ₗ[ℂ] ℂ` -/

/-- The factored complex pairing, fully bundled: an additive hom from
`H₁` to ℂ-linear functionals on closed holomorphic forms. -/
def complexPeriodH1Bilinear :
    S.H1 →+ (S.closedHolomorphicForms →ₗ[ℂ] ℂ) where
  toFun h :=
    { toFun := fun omCl => S.complexPeriodH1 h omCl
      map_add' := fun omCl₁ omCl₂ => S.complexPeriodH1_add_right h omCl₁ omCl₂
      map_smul' := fun z omCl => by
        change S.complexPeriodH1 h (z • omCl) = z • S.complexPeriodH1 h omCl
        rw [S.complexPeriodH1_smul_right, smul_eq_mul] }
  map_zero' := by
    refine LinearMap.ext fun omCl => ?_
    exact S.complexPeriodH1_zero_left omCl
  map_add' h₁ h₂ := by
    refine LinearMap.ext fun omCl => ?_
    exact S.complexPeriodH1_add_left h₁ h₂ omCl

@[simp] lemma complexPeriodH1Bilinear_apply (h : S.H1)
    (omCl : S.closedHolomorphicForms) :
    (S.complexPeriodH1Bilinear h) omCl = S.complexPeriodH1 h omCl := rfl

@[simp] lemma complexPeriodH1Bilinear_mk
    (c : SmoothCycle 𝓘(ℝ, ℂ) X) (omCl : S.closedHolomorphicForms) :
    (S.complexPeriodH1Bilinear (S.proj c)) omCl
      = complexPeriod c (omCl : HolomorphicOneForm X) := by
  rw [complexPeriodH1Bilinear_apply, complexPeriodH1_mk]

end StokesBoundaryInvariance

end JacobianChallenge

end
