/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Pic0RiemannSphereTrivial
import JacobianChallenge.Manifold.AbelJacobiEquivRiemannSphere
import JacobianChallenge.Manifold.DivisorAlgebra

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `Subsingleton (Pic0 RiemannSphere)` — final discharge -/

noncomputable section

open scoped Classical Manifold ContDiff Topology
open Filter Set OnePoint

namespace JacobianChallenge

/-! ## Pointwise eval of `Finset.sum` on `Div` -/

/-- Pointwise eval of `Finset.sum` on `Div RS`. -/
lemma Div.finset_sum_apply {ι : Type*} (s : Finset ι) (F : ι → Div RiemannSphere)
    (y : RiemannSphere) :
    (∑ n ∈ s, F n : Div RiemannSphere) y = ∑ n ∈ s, F n y := by
  classical
  induction s using Finset.induction with
  | empty => show (0 : Div RiemannSphere) y = 0; rfl
  | @insert a s h ih =>
    rw [Finset.sum_insert h, Finset.sum_insert h]
    show (_ : Div RiemannSphere) y + (_ : Div RiemannSphere) y = _
    rw [ih]

/-! ## Elementary divisor membership in `PrincDiv` -/

lemma single_sub_infty_mem_PrincDiv {x : RiemannSphere}
    (hx : x ≠ (∞ : RiemannSphere)) :
    ((Div.single x : Div RiemannSphere) - Div.single (∞ : RiemannSphere))
      ∈ PrincDiv RiemannSphere := by
  induction x using OnePoint.rec with
  | infty => exact absurd rfl hx
  | coe a => exact elementaryDivisor_mem_PrincDiv a

/-! ## Reconstruction sum equals `D` pointwise -/

/-- For `D : Div0 RS`, the reconstruction sum equals `D`. -/
lemma sum_elementary_eq_div0 (D : Div0 RiemannSphere) (y : RiemannSphere) :
    (∑ x ∈ (D : Div RiemannSphere).supportFinset.filter
            (· ≠ (∞ : RiemannSphere)),
      ((D : Div RiemannSphere) x) •
        ((Div.single x : Div RiemannSphere) - Div.single (∞ : RiemannSphere)) :
      Div RiemannSphere) y = (D : Div RiemannSphere) y := by
  rw [Div.finset_sum_apply]
  -- Each summand: D(x) • (Div.single x y - Div.single ∞ y).
  have h_summand : ∀ x ∈ (D : Div RiemannSphere).supportFinset.filter
                          (· ≠ (∞ : RiemannSphere)),
      ((D : Div RiemannSphere) x •
        ((Div.single x : Div RiemannSphere) - Div.single (∞ : RiemannSphere))) y
        = ((D : Div RiemannSphere) x) •
          ((if y = x then (1 : ℤ) else 0)
            - (if y = (∞ : RiemannSphere) then 1 else 0)) := by
    intro x _
    rw [Div.zsmul_apply, Div.sub_apply, Div.single_apply, Div.single_apply]
    rfl
  rw [Finset.sum_congr rfl h_summand]
  by_cases hy : y = (∞ : RiemannSphere)
  · subst hy
    rw [show (∑ x ∈ (D : Div RiemannSphere).supportFinset.filter
                (· ≠ (∞ : RiemannSphere)),
            ((D : Div RiemannSphere) x) •
              ((if (∞ : RiemannSphere) = x then (1 : ℤ) else 0)
                - if (∞ : RiemannSphere) = (∞ : RiemannSphere) then 1 else 0))
            = ∑ x ∈ (D : Div RiemannSphere).supportFinset.filter
                  (· ≠ (∞ : RiemannSphere)),
              - ((D : Div RiemannSphere) x) from by
      refine Finset.sum_congr rfl ?_
      intro x hx
      rw [Finset.mem_filter] at hx
      have h_inf_ne_x : (∞ : RiemannSphere) ≠ x := fun h => hx.2 h.symm
      rw [if_neg h_inf_ne_x, if_pos rfl]
      ring]
    rw [Finset.sum_neg_distrib]
    have h_deg : (D : Div RiemannSphere).degree = 0 := D.2
    have h_deg_unfold : (D : Div RiemannSphere).degree
        = ∑ x ∈ (D : Div RiemannSphere).supportFinset, ((D : Div RiemannSphere) x) := rfl
    rw [h_deg_unfold] at h_deg
    -- Split supp into the filter and its complement.
    have h_split :
        ∑ x ∈ (D : Div RiemannSphere).supportFinset, ((D : Div RiemannSphere) x) =
          (∑ x ∈ (D : Div RiemannSphere).supportFinset.filter
                  (· ≠ (∞ : RiemannSphere)),
            ((D : Div RiemannSphere) x)) +
          (∑ x ∈ (D : Div RiemannSphere).supportFinset.filter
                  (· = (∞ : RiemannSphere)),
            ((D : Div RiemannSphere) x)) := by
      have h_eq_filter :
          (D : Div RiemannSphere).supportFinset.filter (· ≠ (∞ : RiemannSphere))
            = (D : Div RiemannSphere).supportFinset.filter
                (fun x => ¬ x = (∞ : RiemannSphere)) := rfl
      rw [h_eq_filter,
          ← Finset.sum_filter_add_sum_filter_not _ (· = (∞ : RiemannSphere))]
      ring
    have h_inf_sum :
        ∑ x ∈ (D : Div RiemannSphere).supportFinset.filter (· = (∞ : RiemannSphere)),
          ((D : Div RiemannSphere) x) = (D : Div RiemannSphere) ∞ := by
      by_cases h_inf_in : (∞ : RiemannSphere) ∈ (D : Div RiemannSphere).supportFinset
      · have h_filter_eq :
            (D : Div RiemannSphere).supportFinset.filter (· = (∞ : RiemannSphere))
              = {(∞ : RiemannSphere)} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨_, h⟩; exact h
          · intro h; subst h; exact ⟨h_inf_in, rfl⟩
        rw [h_filter_eq, Finset.sum_singleton]
      · have h_filter_empty :
            (D : Div RiemannSphere).supportFinset.filter (· = (∞ : RiemannSphere))
              = ∅ := by
          ext x
          simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro hx h_eq; subst h_eq; exact h_inf_in hx
        rw [h_filter_empty, Finset.sum_empty]
        exact (Div.apply_eq_zero_of_notMem_supportFinset h_inf_in).symm
    rw [h_split, h_inf_sum] at h_deg
    linarith
  · rw [show (∑ x ∈ (D : Div RiemannSphere).supportFinset.filter
                (· ≠ (∞ : RiemannSphere)),
            ((D : Div RiemannSphere) x) •
              ((if y = x then (1 : ℤ) else 0)
                - if y = (∞ : RiemannSphere) then 1 else 0))
            = ∑ x ∈ (D : Div RiemannSphere).supportFinset.filter
                  (· ≠ (∞ : RiemannSphere)),
              ((D : Div RiemannSphere) x) • (if y = x then (1 : ℤ) else 0) from by
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [if_neg hy]
      ring]
    by_cases hy_supp : y ∈ (D : Div RiemannSphere).supportFinset
    · have hy_filter : y ∈ (D : Div RiemannSphere).supportFinset.filter
            (· ≠ (∞ : RiemannSphere)) :=
        Finset.mem_filter.mpr ⟨hy_supp, hy⟩
      rw [Finset.sum_eq_single_of_mem y hy_filter]
      · rw [if_pos rfl]; ring
      · intro x _ hxy
        rw [if_neg (fun h => hxy h.symm)]; ring
    · have hDy : (D : Div RiemannSphere) y = 0 :=
        Div.apply_eq_zero_of_notMem_supportFinset hy_supp
      rw [hDy]
      refine Finset.sum_eq_zero ?_
      intro x hx
      rw [Finset.mem_filter] at hx
      by_cases hyx : y = x
      · subst hyx
        exfalso
        exact (Div.mem_supportFinset.mp hx.1) hDy
      · rw [if_neg hyx]; ring

/-! ## Final discharge -/

/-- **Pic⁰(ℙ¹) = 0 — unconditional.** -/
theorem subsingleton_pic0_RiemannSphere :
    Subsingleton (Pic0 RiemannSphere) := by
  apply subsingleton_pic0_of_every_div0_principal
  intro D
  have h_eq : (D : Div RiemannSphere) =
      ∑ x ∈ (D : Div RiemannSphere).supportFinset.filter
              (· ≠ (∞ : RiemannSphere)),
        ((D : Div RiemannSphere) x) •
          ((Div.single x : Div RiemannSphere) - Div.single (∞ : RiemannSphere)) := by
    ext y
    rw [(sum_elementary_eq_div0 D y).symm]
  rw [h_eq]
  refine AddSubgroup.sum_mem _ ?_
  intro x hx
  rw [Finset.mem_filter] at hx
  exact AddSubgroup.zsmul_mem _ (single_sub_infty_mem_PrincDiv hx.2) _

/-! ## Unconditional Abel-Jacobi iso on `RiemannSphere` -/

/-- **The Abel-Jacobi iso `Pic0 RS ≃+ AnalyticJacobian` on RS,
unconditional.** -/
noncomputable def AbelJacobiInput.abelJacobiEquiv_of_RiemannSphere_unconditional
    {α : Module.Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
          (HolomorphicOneForm RiemannSphere)}
    {h : PeriodLatticeDiscretenessBundle
      (PeriodPairingData.ofSmoothCycle RiemannSphere) α}
    (B : AbelJacobiInput α h) :
    Pic0 RiemannSphere ≃+
      AnalyticJacobian
        (PeriodPairingData.ofSmoothCycle RiemannSphere) α h :=
  B.abelJacobiEquiv_of_RiemannSphere subsingleton_pic0_RiemannSphere

end JacobianChallenge

end
