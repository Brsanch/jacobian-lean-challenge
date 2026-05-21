/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HodgeRiemannBridge

set_option linter.unusedSectionVars false

/-! # Composing the Hodge-Riemann bridge with Hodge positivity

The Hermitian half of the bridge composition lives in `HodgeRiemannBridge.lean`
(`hodgeRiemann_lhs_isHermitian`). This file finishes the composition by
proving the **positivity half**: under the bridge identity
`i · Π^T · J · Π̄ = H.toMatrix basis_ω`, positive-definiteness of `H` transfers
to the quadratic form `x ↦ xᴴ · (i Π^T J Π̄) · x`, yielding the full
`RiemannBilinearSecondRelation`.

The argument is pure linear algebra modulo the sesquilinearity fields of
`HermitianOnHolomorphicOneForm`:

1. Expand `xᴴ · H.toMatrix · x` as `H(v, v)` where
   `v := ∑ i, star (x i) • basis_ω i` (using bilinearity + conjugate symmetry).
2. `x ≠ 0` ⟹ `v ≠ 0` via `basis_ω.linearIndependent`.
3. `H.IsPositiveDefinite` ⟹ `H(v, v) ≠ 0`, `(H(v,v)).im = 0`, `0 ≤ (H(v,v)).re`.
4. A complex number with zero imaginary part and non-negative real part that
   is not zero has strictly positive real part.

## What this file ships

* Conjugate-symmetric versions of the sesquilinearity fields on the **second**
  argument of `HermitianOnHolomorphicOneForm` (zero / add / smul / sum).
* `HermitianOnHolomorphicOneForm.toMatrix_quadratic_form` — the identity
  `xᴴ · H.toMatrix · x = H(v, v)` with `v := ∑ i, star (x i) • basis_ω i`.
* `HermitianOnHolomorphicOneForm.toMatrix_quadratic_form_re_pos_of_PD` — the
  pointwise positivity from `IsPositiveDefinite`.
* `RiemannBilinearSecondRelation_of_HodgeBridge` — the full composition.
* `RiemannBilinearRelations_of_HodgeBridge_and_first` — bundling with the
  first relation (separately supplied; the bridge does not constrain the
  first relation).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace HermitianOnHolomorphicOneForm

/-! ## Sesquilinearity on the second argument

These are not direct fields of the structure; they are derived from
`conjSymm` plus the (ℂ-linear) fields on the first argument. -/

variable (H : HermitianOnHolomorphicOneForm X)

lemma map_zero_right (om : HolomorphicOneForm X) :
    H.toFun om 0 = 0 := by
  rw [H.conjSymm om 0, H.map_zero_left, star_zero]

lemma map_add_right (om eta1 eta2 : HolomorphicOneForm X) :
    H.toFun om (eta1 + eta2) = H.toFun om eta1 + H.toFun om eta2 := by
  rw [H.conjSymm om (eta1 + eta2), H.map_add_left, star_add,
      ← H.conjSymm om eta1, ← H.conjSymm om eta2]

lemma map_smul_right (c : ℂ) (om eta : HolomorphicOneForm X) :
    H.toFun om (c • eta) = star c * H.toFun om eta := by
  rw [H.conjSymm om (c • eta), H.map_smul_left, H.conjSymm eta om]
  rw [show (c : ℂ) * star (H.toFun om eta) = star (H.toFun om eta) * c from
        by ring]
  rw [StarMul.star_mul, star_star]

lemma map_sum_left {ι : Type*} (s : Finset ι)
    (f : ι → HolomorphicOneForm X) (eta : HolomorphicOneForm X) :
    H.toFun (∑ i ∈ s, f i) eta = ∑ i ∈ s, H.toFun (f i) eta := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [H.map_zero_left]
  · intros i s' hi ih
    rw [Finset.sum_insert hi, H.map_add_left, ih, Finset.sum_insert hi]

lemma map_sum_right {ι : Type*} (s : Finset ι)
    (f : ι → HolomorphicOneForm X) (om : HolomorphicOneForm X) :
    H.toFun om (∑ i ∈ s, f i) = ∑ i ∈ s, H.toFun om (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [H.map_zero_right]
  · intros i s' hi ih
    rw [Finset.sum_insert hi, H.map_add_right, ih, Finset.sum_insert hi]

/-! ## The quadratic form identity -/

/-- **The quadratic form on the matrix equals the Hodge form on the
canonical sum.** For any `x : Fin g → ℂ`, the matrix-level quadratic form
`xᴴ · H.toMatrix basis_ω · x` equals `H(v, v)` where
`v := ∑ i, star (x i) • basis_ω i`. -/
theorem toMatrix_quadratic_form
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (x : Fin (JacobianChallenge.genus X) → ℂ) :
    star x ⬝ᵥ (H.toMatrix basis_ω *ᵥ x)
      = H.toFun (∑ i, star (x i) • basis_ω i)
                (∑ j, star (x j) • basis_ω j) := by
  -- Expand the RHS using sesquilinearity:
  -- H(∑ star(x i) • basis_ω i, ∑ star(x j) • basis_ω j)
  --   = ∑ i, star(x i) * H(basis_ω i, ∑ star(x j) • basis_ω j)
  --   = ∑ i, star(x i) * ∑ j, star(star(x j)) * H(basis_ω i, basis_ω j)
  --   = ∑ i, star(x i) * ∑ j, x j * H(basis_ω i, basis_ω j)
  -- LHS:
  -- star x ⬝ᵥ (H.toMatrix *ᵥ x) = ∑ i, star(x i) * ∑ j, H(basis_ω i, basis_ω j) * x j
  -- These agree by `mul_comm`.
  rw [H.map_sum_left]
  -- Now RHS: ∑ i, H.toFun (star (x i) • basis_ω i) (∑ j, star (x j) • basis_ω j)
  simp_rw [H.map_smul_left, H.map_sum_right, H.map_smul_right, star_star]
  -- RHS: ∑ i, star (x i) * ∑ j, x j * H.toFun (basis_ω i) (basis_ω j)
  -- LHS: star x ⬝ᵥ (H.toMatrix basis_ω *ᵥ x)
  show ∑ i, star (x i) * ((H.toMatrix basis_ω *ᵥ x) i)
       = ∑ i, star (x i) * ∑ j, x j * H.toFun (basis_ω i) (basis_ω j)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  show (H.toMatrix basis_ω *ᵥ x) i = ∑ j, x j * H.toFun (basis_ω i) (basis_ω j)
  show ∑ j, H.toMatrix basis_ω i j * x j
       = ∑ j, x j * H.toFun (basis_ω i) (basis_ω j)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [toMatrix_apply]
  ring

/-! ## Positivity from `IsPositiveDefinite` -/

/-- **The Hodge form is real-valued on the diagonal of a non-trivial sum.**
Under `H.IsPositiveDefinite`, the diagonal value `H(v, v)` is a real number
(its imaginary part vanishes). -/
lemma toMatrix_quadratic_form_im_eq_zero_of_PD
    (hH : H.IsPositiveDefinite)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (x : Fin (JacobianChallenge.genus X) → ℂ) :
    (star x ⬝ᵥ (H.toMatrix basis_ω *ᵥ x)).im = 0 := by
  rw [H.toMatrix_quadratic_form basis_ω x]
  exact (hH.1 _).1

/-- **Strict positivity on non-zero `x`.** The quadratic form is strictly
positive on every non-zero `x : Fin g → ℂ`, given the Hodge form is
positive definite and the basis is linearly independent (which it is, by
being a basis). -/
lemma toMatrix_quadratic_form_re_pos_of_PD
    (hH : H.IsPositiveDefinite)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    {x : Fin (JacobianChallenge.genus X) → ℂ} (hx : x ≠ 0) :
    0 < (star x ⬝ᵥ (H.toMatrix basis_ω *ᵥ x)).re := by
  -- Set v := ∑ i, star (x i) • basis_ω i. By LI of basis_ω, v ≠ 0.
  set v : HolomorphicOneForm X :=
    ∑ i, star (x i) • basis_ω i with hv_def
  have hv_ne : v ≠ 0 := by
    intro hv
    -- `v = 0` ⟹ `∀ i, star (x i) = 0` ⟹ `x = 0`, contradicting `hx`.
    have hli :=
      (Fintype.linearIndependent_iff (R := ℂ) (M := HolomorphicOneForm X)
        (v := fun i => basis_ω i)).mp basis_ω.linearIndependent
    have hzero : ∀ i, star (x i) = 0 := hli (fun i => star (x i)) hv
    apply hx
    funext i
    have hi : star (x i) = 0 := hzero i
    have : x i = star (star (x i)) := (star_star _).symm
    rw [this, hi]
    simp
  -- Now translate `(H.toFun v v).re > 0`.
  have hH_im : (H.toFun v v).im = 0 := (hH.1 v).1
  have hH_re_nonneg : 0 ≤ (H.toFun v v).re := (hH.1 v).2
  -- Positive definiteness: H(v, v) = 0 ⟹ v = 0; contrapositive gives ≠ 0.
  have hH_ne : H.toFun v v ≠ 0 := fun h => hv_ne (hH.2 v h)
  -- A complex with zero imaginary part is purely real; if ≠ 0, then re ≠ 0.
  have hH_re_ne : (H.toFun v v).re ≠ 0 := by
    intro h0
    apply hH_ne
    apply Complex.ext
    · exact h0
    · exact hH_im
  have hH_re_pos : 0 < (H.toFun v v).re :=
    lt_of_le_of_ne hH_re_nonneg (Ne.symm hH_re_ne)
  -- Now bridge: LHS = H.toFun v v by toMatrix_quadratic_form.
  rw [H.toMatrix_quadratic_form basis_ω x]
  exact hH_re_pos

end HermitianOnHolomorphicOneForm

/-! ## Bridge composition: `Hodge inner product + bridge ⟹ second relation` -/

/-- **The full Hodge-Riemann composition.** Given:

* `H : HermitianOnHolomorphicOneForm X` with `H.IsPositiveDefinite`
  (the Hodge inner product on `H^0(X, Ω)`),
* `hBridge : i Π^T J Π̄ = H.toMatrix basis_ω`
  (the matrix identity bridging Hodge form ↔ period matrix),

we conclude `RiemannBilinearSecondRelation data basis_ω cycleGens J`: the
matrix `i Π^T J Π̄` is positive-definite Hermitian.

This is the bridge composition completing the chain
`HodgeInnerProductHypothesis + HodgeRiemannBridgeHypothesis ⟹ RiemannBilinearSecondRelation`. -/
theorem RiemannBilinearSecondRelation_of_HodgeBridge
    {data : PeriodPairingData X}
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    {cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1}
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    {H : HermitianOnHolomorphicOneForm X}
    (hPD : H.IsPositiveDefinite)
    (hBridge : HodgeRiemannBridgeHypothesis data basis_ω cycleGens J H) :
    RiemannBilinearSecondRelation data basis_ω cycleGens J := by
  refine ⟨?_, ?_⟩
  · -- Hermitian half: already in `hodgeRiemann_lhs_isHermitian`.
    exact hodgeRiemann_lhs_isHermitian hBridge
  · -- Positivity half: transfer through the bridge identity.
    intro x hx
    -- The bridge says the matrix equals `H.toMatrix basis_ω`, so the
    -- quadratic form equals the Hodge form's quadratic form, which is
    -- strictly positive on non-zero `x`.
    have hM_eq : (Complex.I : ℂ) •
      ((periodMatrix data basis_ω cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)
        * (periodMatrix data basis_ω cycleGens).map star)
        = H.toMatrix basis_ω := hBridge
    refine ⟨?_, ?_⟩
    · rw [hM_eq]; exact H.toMatrix_quadratic_form_im_eq_zero_of_PD hPD basis_ω x
    · rw [hM_eq]; exact H.toMatrix_quadratic_form_re_pos_of_PD hPD basis_ω hx

/-- **Bundled bridge composition.** Combines the bridge composition for the
second relation with a separately-supplied first-relation witness to produce
the full `RiemannBilinearRelations` existence statement. -/
theorem RiemannBilinearRelations_of_HodgeBridge_and_first
    {data : PeriodPairingData X}
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    {cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1}
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    {H : HermitianOnHolomorphicOneForm X}
    (hPD : H.IsPositiveDefinite)
    (hBridge : HodgeRiemannBridgeHypothesis data basis_ω cycleGens J H)
    (hFirst : RiemannBilinearFirstRelation data basis_ω cycleGens J) :
    RiemannBilinearRelations data basis_ω cycleGens :=
  ⟨J, hFirst, RiemannBilinearSecondRelation_of_HodgeBridge hPD hBridge⟩

end JacobianChallenge

end
