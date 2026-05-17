/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodLatticeMkQContMDiff

/-! # Smoothness of ℂ-linear maps descended to lattice quotients

Given `ℤ`-lattices `L ⊆ (Fin g₁ → ℂ)` and `L' ⊆ (Fin g₂ → ℂ)`, and a
ℂ-linear map `T : (Fin g₁ → ℂ) →L[ℂ] (Fin g₂ → ℂ)` carrying `L` into
`L'`, the induced quotient map
`T̃ : (Fin g₁ → ℂ) ⧸ L → (Fin g₂ → ℂ) ⧸ L'`
is `ContMDiff` for the complex models.

This is the **building block for OPEN.md items 18 and 21** (pushforward
and pullback smoothness). Both `pushforward` and `pullback` on
`Pic⁰ X ≃+ AnalyticJacobian X` are induced, via Abel-Jacobi, by
ℂ-linear maps on the period covers — pushforward of holomorphic 1-forms
for items 18, and the multiplicity-weighted contravariant lift for
item 21. Once C3 supplies the Abel-Jacobi isomorphism, the smoothness
of these maps on `Jacobian X` reduces directly to the present lemma.

## Proof structure

Locally near any `q : G₁ := (Fin g₁ → ℂ) ⧸ L`:

* `chartAt q : G₁ → (Fin g₁ → ℂ)` is `ContMDiffOn` on its source
  (`contMDiffOn_chart`).
* `T : (Fin g₁ → ℂ) →L[ℂ] (Fin g₂ → ℂ)` is `ContDiff ℂ ω`, hence
  `ContMDiff` on the `chartedSpaceSelf` structures.
* `L'.mkQ : (Fin g₂ → ℂ) → G₂ := (Fin g₂ → ℂ) ⧸ L'` is `ContMDiff` by
  `mkQ_contMDiff_complex`.

The composition `L'.mkQ ∘ T ∘ chartAt q` equals `T̃` on the source of
`chartAt q` (because `L.mkQ ∘ chartAt q = id` and `T̃ ∘ L.mkQ = L'.mkQ ∘ T`).

The lemma carries `T̃` as an explicit `(Fin g₁ → ℂ) ⧸ L → (Fin g₂ → ℂ) ⧸ L'`
factor (built from `Submodule.mapQ` or the underlying `QuotientAddGroup.lift`
machinery).
-/

open Set

open scoped Manifold ContDiff

set_option diagnostics.threshold 100

namespace JacobianChallenge

variable {g₁ g₂ : ℕ}
variable (L : Submodule ℤ (Fin g₁ → ℂ))
  [DiscreteTopology L] [IsZLattice ℝ L]
variable (L' : Submodule ℤ (Fin g₂ → ℂ))
  [DiscreteTopology L'] [IsZLattice ℝ L']

/-! ### Induced map on `ℤ`-quotients -/

/-- A ℂ-linear `T : E₁ →L[ℂ] E₂` satisfying `T '' L ⊆ L'` descends to a
quotient map `(Fin g₁ → ℂ) ⧸ L → (Fin g₂ → ℂ) ⧸ L'`.

The map is built from `Submodule.mapQ` applied to `T.toLinearMap` viewed
as a ℤ-linear map (`T.restrictScalars ℤ` for the ℤ-action through `ℂ`).
We package the construction here for convenient downstream use. -/
noncomputable def quotientLinearMap
    (T : (Fin g₁ → ℂ) →L[ℂ] (Fin g₂ → ℂ))
    (hT : ∀ x ∈ L, T x ∈ L') :
    (Fin g₁ → ℂ) ⧸ L → (Fin g₂ → ℂ) ⧸ L' :=
  L.mapQ L' (T.toLinearMap.restrictScalars ℤ) hT

/-- Defining identity: the quotient-linear map composed with `L.mkQ`
equals `L'.mkQ ∘ T`. -/
private lemma quotientLinearMap_apply_mkQ
    (T : (Fin g₁ → ℂ) →L[ℂ] (Fin g₂ → ℂ))
    (hT : ∀ x ∈ L, T x ∈ L') (x : Fin g₁ → ℂ) :
    quotientLinearMap L L' T hT (L.mkQ x) = L'.mkQ (T x) := by
  -- `Submodule.mapQ_apply` is the standard identity.
  simp [quotientLinearMap, Submodule.mapQ_apply]

/-! ### Local agreement with the lifted form -/

private lemma quotientLinearMap_eqOn_local
    (T : (Fin g₁ → ℂ) →L[ℂ] (Fin g₂ → ℂ))
    (hT : ∀ x ∈ L, T x ∈ L')
    (q : (Fin g₁ → ℂ) ⧸ L) :
    Set.EqOn (quotientLinearMap L L' T hT)
      (fun a : (Fin g₁ → ℂ) ⧸ L =>
        L'.mkQ (T ((chartAt (Fin g₁ → ℂ) q) a)))
      (chartAt (Fin g₁ → ℂ) q).source := by
  intro a ha
  -- chart-at q is a local right-inverse of L.mkQ.
  have h_left :
      (L.mkQ : (Fin g₁ → ℂ) → (Fin g₁ → ℂ) ⧸ L)
          ((chartAt (Fin g₁ → ℂ) q) a) = a := by
    -- Reuse the proof template from `mkQ_chartAt_apply`
    -- (PeriodLatticeLieGroupAdd.lean).
    have h := (chartAt (Fin g₁ → ℂ) q).left_inv ha
    show L.mkQ ((chartAt (Fin g₁ → ℂ) q) a) = a
    have h1 : (chartAt (Fin g₁ → ℂ) q) a ∈
        (chartAt (Fin g₁ → ℂ) q).target :=
      (chartAt (Fin g₁ → ℂ) q).map_source ha
    have h2 :
        (chartAt (Fin g₁ → ℂ) q).target =
          (localChart L (discRadius_separates L) q.out).source :=
      rfl
    rw [h2] at h1
    have h3 :
        (chartAt (Fin g₁ → ℂ) q).symm =
          localChart L (discRadius_separates L) q.out :=
      OpenPartialHomeomorph.symm_symm _
    rw [h3] at h
    exact h
  -- Now apply quotientLinearMap_apply_mkQ.
  show quotientLinearMap L L' T hT a =
    L'.mkQ (T ((chartAt (Fin g₁ → ℂ) q) a))
  -- Replace `a` by `L.mkQ (chartAt _ q a)` on the LHS, then unfold.
  conv_lhs => rw [← h_left]
  exact quotientLinearMap_apply_mkQ L L' T hT _

/-! ### Smoothness of the lifted form -/

private lemma contMDiffOn_lifted_quotientLinearMap
    (n : WithTop ℕ∞)
    (T : (Fin g₁ → ℂ) →L[ℂ] (Fin g₂ → ℂ))
    (hT : ∀ x ∈ L, T x ∈ L')
    (q : (Fin g₁ → ℂ) ⧸ L) :
    ContMDiffOn (𝓘(ℂ, Fin g₁ → ℂ)) (𝓘(ℂ, Fin g₂ → ℂ)) n
      (fun a : (Fin g₁ → ℂ) ⧸ L =>
        L'.mkQ (T ((chartAt (Fin g₁ → ℂ) q) a)))
      (chartAt (Fin g₁ → ℂ) q).source := by
  have h_chart :
      ContMDiffOn (𝓘(ℂ, Fin g₁ → ℂ)) (𝓘(ℂ, Fin g₁ → ℂ)) n
        ((chartAt (Fin g₁ → ℂ) q) :
          ((Fin g₁ → ℂ) ⧸ L) → (Fin g₁ → ℂ))
        (chartAt (Fin g₁ → ℂ) q).source :=
    contMDiffOn_chart (I := 𝓘(ℂ, Fin g₁ → ℂ)) (n := n) (x := q)
  -- `T` is `ContDiff ℂ ω` and hence `ContMDiff` on the
  -- `chartedSpaceSelf` structure on `Fin g_i → ℂ`.
  have hT_diff : ContDiff ℂ n (T : (Fin g₁ → ℂ) → (Fin g₂ → ℂ)) :=
    T.contDiff.of_le le_top
  have hT_mdiff :
      ContMDiff (𝓘(ℂ, Fin g₁ → ℂ)) (𝓘(ℂ, Fin g₂ → ℂ)) n
        (T : (Fin g₁ → ℂ) → (Fin g₂ → ℂ)) :=
    hT_diff.contMDiff
  have h_compose1 :
      ContMDiffOn (𝓘(ℂ, Fin g₁ → ℂ)) (𝓘(ℂ, Fin g₂ → ℂ)) n
        (fun a : (Fin g₁ → ℂ) ⧸ L => T ((chartAt (Fin g₁ → ℂ) q) a))
        (chartAt (Fin g₁ → ℂ) q).source :=
    hT_mdiff.comp_contMDiffOn h_chart
  have h_mkQ' :
      ContMDiff (𝓘(ℂ, Fin g₂ → ℂ)) (𝓘(ℂ, Fin g₂ → ℂ)) n
        (L'.mkQ : (Fin g₂ → ℂ) → (Fin g₂ → ℂ) ⧸ L') :=
    mkQ_contMDiff_complex L' n
  exact h_mkQ'.comp_contMDiffOn h_compose1

/-! ### Smoothness of `quotientLinearMap` -/

/-- The quotient-linear map induced by a ℂ-linear `T : E₁ →L[ℂ] E₂` (with
`T '' L ⊆ L'`) is `ContMDiff` for the complex models on the lattice
quotients. -/
theorem quotientLinearMap_contMDiff
    (n : WithTop ℕ∞)
    (T : (Fin g₁ → ℂ) →L[ℂ] (Fin g₂ → ℂ))
    (hT : ∀ x ∈ L, T x ∈ L') :
    ContMDiff (𝓘(ℂ, Fin g₁ → ℂ)) (𝓘(ℂ, Fin g₂ → ℂ)) n
      (quotientLinearMap L L' T hT) := by
  intro q
  have hopen : IsOpen (chartAt (Fin g₁ → ℂ) q).source :=
    (chartAt (Fin g₁ → ℂ) q).open_source
  have hmem : q ∈ (chartAt (Fin g₁ → ℂ) q).source := mem_chart_source _ _
  have h_lifted := contMDiffOn_lifted_quotientLinearMap L L' n T hT q
  have h_eq := quotientLinearMap_eqOn_local L L' T hT q
  have h_qlm :
      ContMDiffOn (𝓘(ℂ, Fin g₁ → ℂ)) (𝓘(ℂ, Fin g₂ → ℂ)) n
        (quotientLinearMap L L' T hT)
        (chartAt (Fin g₁ → ℂ) q).source :=
    h_lifted.congr h_eq
  exact h_qlm.contMDiffAt (hopen.mem_nhds hmem)

end JacobianChallenge
