/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannFirstBilinearRelationNamed

set_option linter.unusedSectionVars false

/-! # `RiemannFirstBilinearRelation` from strict-upper-triangular `Q` scalars

At general genus, `HolomorphicOneForm X` has a chosen basis
`α : Basis (Fin g) ℂ`. Bilinear expansion of `Q J cycleGens ω₀ ω₁`
against this basis gives

  `Q J cycleGens ω₀ ω₁ = ∑ i j, c₀ᵢ · c₁ⱼ · Q J cycleGens (α i) (α j)`

where `cₖᵢ = α.repr ωₖ i`. Under antisymmetric `J`:

* Diagonal terms `Q J cycleGens (α i) (α i) = 0` (chip 7).
* `Q J cycleGens (α j) (α i) = - Q J cycleGens (α i) (α j)` (chip 6).

So `Q J cycleGens ω₀ ω₁ ≡ 0` for all `ω₀, ω₁` iff
`Q J cycleGens (α i) (α j) = 0` for all `i < j`.

This is the chip 9 named-hypothesis form of chip 20g
(`riemannBilinearFirstRelation_iff_strictUpperTriangular_zero_of_antisymm`).

## What this file ships

* `riemannBilinearPeriodForm_zero_left` /
  `riemannBilinearPeriodForm_zero_right` — Q vanishes on zero input.
* `riemannBilinearPeriodForm_sum_smul_left` — left-sum expansion.
* `riemannBilinearPeriodForm_sum_smul_right` — right-sum expansion.
* `riemannBilinearPeriodForm_basis_expansion` — full bilinear
  expansion against a basis.
* `riemannFirstBilinearRelation_of_strictUpperTriangular_Q_zero` —
  RFBR from `Jᵀ = -J` + strict-upper-triangular zero on the basis.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module BigOperators

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`Q J cycleGens 0 ω₁ = 0`.** From smul-left with scalar `0`. -/
theorem riemannBilinearPeriodForm_zero_left
    {data : PeriodPairingData X}
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ)
    (ω₁ : HolomorphicOneForm X) :
    riemannBilinearPeriodForm cycleGens J 0 ω₁ = 0 := by
  have h0 : (0 : HolomorphicOneForm X) = (0 : ℂ) • 0 := by rw [zero_smul]
  rw [h0, riemannBilinearPeriodForm_smul_left]
  ring

/-- **`Q J cycleGens ω₀ 0 = 0`.** -/
theorem riemannBilinearPeriodForm_zero_right
    {data : PeriodPairingData X}
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ)
    (ω₀ : HolomorphicOneForm X) :
    riemannBilinearPeriodForm cycleGens J ω₀ 0 = 0 := by
  have h0 : (0 : HolomorphicOneForm X) = (0 : ℂ) • 0 := by rw [zero_smul]
  rw [h0, riemannBilinearPeriodForm_smul_right]
  ring

/-- **Left-sum expansion: `Q J (∑ i ∈ s, fᵢ • vᵢ) ω₁ = ∑ i ∈ s, fᵢ · Q J vᵢ ω₁`.** -/
theorem riemannBilinearPeriodForm_sum_smul_left
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {data : PeriodPairingData X}
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ)
    (f : ι → ℂ) (v : ι → HolomorphicOneForm X) (ω₁ : HolomorphicOneForm X) :
    riemannBilinearPeriodForm cycleGens J (∑ i ∈ s, f i • v i) ω₁
      = ∑ i ∈ s, f i * riemannBilinearPeriodForm cycleGens J (v i) ω₁ := by
  induction s using Finset.induction_on with
  | empty =>
    simp [Finset.sum_empty]
    exact riemannBilinearPeriodForm_zero_left cycleGens J ω₁
  | insert i s his ih =>
    rw [Finset.sum_insert his, Finset.sum_insert his,
        riemannBilinearPeriodForm_add_left,
        riemannBilinearPeriodForm_smul_left, ih]

/-- **Right-sum expansion: `Q J ω₀ (∑ j ∈ s, gⱼ • wⱼ) = ∑ j ∈ s, gⱼ · Q J ω₀ wⱼ`.** -/
theorem riemannBilinearPeriodForm_sum_smul_right
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {data : PeriodPairingData X}
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ)
    (g : ι → ℂ) (w : ι → HolomorphicOneForm X) (ω₀ : HolomorphicOneForm X) :
    riemannBilinearPeriodForm cycleGens J ω₀ (∑ j ∈ s, g j • w j)
      = ∑ j ∈ s, g j * riemannBilinearPeriodForm cycleGens J ω₀ (w j) := by
  induction s using Finset.induction_on with
  | empty =>
    simp [Finset.sum_empty]
    exact riemannBilinearPeriodForm_zero_right cycleGens J ω₀
  | insert j s hjs ih =>
    rw [Finset.sum_insert hjs, Finset.sum_insert hjs,
        riemannBilinearPeriodForm_add_right,
        riemannBilinearPeriodForm_smul_right, ih]

/-- **Full bilinear expansion against a basis.** -/
theorem riemannBilinearPeriodForm_basis_expansion
    (α₀ : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    {data : PeriodPairingData X}
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ)
    (ω₀ ω₁ : HolomorphicOneForm X) :
    riemannBilinearPeriodForm cycleGens J ω₀ ω₁
      = ∑ i, ∑ j,
          (α₀.repr ω₀ i) * (α₀.repr ω₁ j)
            * riemannBilinearPeriodForm cycleGens J (α₀ i) (α₀ j) := by
  classical
  have h_ω₀ : ω₀ = ∑ i, (α₀.repr ω₀ i) • α₀ i := (α₀.sum_repr ω₀).symm
  have h_ω₁ : ω₁ = ∑ j, (α₀.repr ω₁ j) • α₀ j := (α₀.sum_repr ω₁).symm
  conv_lhs => rw [h_ω₀, h_ω₁]
  rw [riemannBilinearPeriodForm_sum_smul_left]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [riemannBilinearPeriodForm_sum_smul_right]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- **`RiemannFirstBilinearRelation` from the strict-upper-triangular
`Q (α i) (α j) = 0` for `i < j` + antisymmetric `J`.**

Lifts chip 20g to the chip 9 named-hypothesis form. -/
theorem riemannFirstBilinearRelation_of_strictUpperTriangular_Q_zero
    (α₀ : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    {data : PeriodPairingData X}
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    (hJ : Jᵀ = -J)
    (h_strict :
      ∀ i j : Fin (JacobianChallenge.genus X), i < j →
        riemannBilinearPeriodForm cycleGens J (α₀ i) (α₀ j) = 0) :
    RiemannFirstBilinearRelation cycleGens J := by
  intro ω₀ ω₁
  rw [riemannBilinearPeriodForm_basis_expansion α₀ cycleGens J ω₀ ω₁]
  -- For each (i, j), the term is 0:
  -- - i = j: diagonal vanishes via chip 7.
  -- - i < j: by h_strict.
  -- - i > j: by antisymmetry + h_strict.
  refine Finset.sum_eq_zero (fun i _ => ?_)
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rcases lt_trichotomy i j with hij | hij | hij
  · -- i < j: h_strict
    rw [h_strict i j hij]
    ring
  · -- i = j: diagonal via chip 7
    rw [hij, riemannBilinearPeriodForm_self_eq_zero cycleGens hJ (α₀ j)]
    ring
  · -- i > j: use antisymmetry, then h_strict on (j, i)
    rw [riemannBilinearPeriodForm_antisymm cycleGens hJ (α₀ i) (α₀ j),
        h_strict j i hij]
    ring

end JacobianChallenge

end
