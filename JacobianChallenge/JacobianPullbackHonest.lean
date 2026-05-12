/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.JacobianPullbackWeighted
import JacobianChallenge.JacobianPullback
import JacobianChallenge.Manifold.HNTotalFromRamificationSum
import JacobianChallenge.Manifold.FibresFiniteUnconditional
import JacobianChallenge.Manifold.IsConstantMapAux
import JacobianChallenge.Divisor.FiberSumWeightedComp
import JacobianChallenge.Manifold.RamificationIndexCompUnconditional
import JacobianChallenge.Manifold.FibreCardClopenReduction

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Honest `Jacobian.pullback` conditional on the named obligation (ZZ179g)

Final structural composer in the multiplicity-weighted pullback chain.
Given `Owed.degree.ramificationSumEqualsDegree_statement X Y` as a
hypothesis (the single named analytic obligation, owed at the mathlib
pin and discharged by the Riemann-Hurwitz argument in a follow-up
chip), produces the honest `Jacobian Y →ₜ+ Jacobian X` that
`Basic.lean.Jacobian.pullback` will swap its zero-stub body for.

## Cases

* **Constant `f`**: returns the zero `→ₜ+`. This matches the natural
  classical convention (constant maps have zero pullback on Pic⁰; the
  fibre cardinality formula degenerates).
* **Non-constant `f`**: derives `hf_finite_fibres` from ZZ48
  (`fibres_finite_statement_holds_unconditional`), derives `hN_total`
  from `h_rsum` via the ZZ179e bridge with `e :=
  manifoldRamificationIndex f` and `N := degreeFiber f hf`, and
  delegates to `Jacobian.pullbackWeighted` (ZZ179f).

## What is proved

The composer itself is purely structural — it is type-correct and
discharges by `Classical.byCases` on `IsConstantMap`. No analytic
content lives here. The single open obligation is `h_rsum`, owed in
`Manifold/RamificationSumEqualsDegree.lean`.

When `h_rsum` is discharged, the body swap in `Basic.lean` becomes a
one-line edit, and OPEN.md items 8, 13, 21, 22, 24 unblock together.

This file additionally provides the contravariant **composition
identity** `pullbackHonest_of_rsum_comp`, which discharges the
`Jacobian.pullback` functoriality lemma `pullback_comp_apply` in
`Basic.lean` once the `pullback` body is the honest one.

No `sorry`, no `axiom`. -/

@[expose] public section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace Jacobian

universe u v w

/-- **Honest pullback conditional on the Riemann-Hurwitz total-weight
identity.** Cases on `IsConstantMap f`: constant ⇒ zero, non-constant ⇒
`Jacobian.pullbackWeighted` with the `e := manifoldRamificationIndex f`
weight and `N := degreeFiber f hf`. -/
noncomputable def pullbackHonest_of_rsum
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [DecidableEq X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_rsum : JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_statement X Y)
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian Y →ₜ+ Jacobian X :=
  open Classical in
  if hc : JacobianChallenge.IsConstantMap f then 0
  else
    Jacobian.pullbackWeighted f
      (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional
        f hf hc)
      (JacobianChallenge.Manifold.manifoldRamificationIndex f)
      (JacobianChallenge.ContMDiff.degreeFiber f hf)
      (fun y => h_rsum f hf hc y)
      (Pic0.divPullbackWeighted_descent_of_smooth hf hc _ _ _)

/-- Equation lemma: when `f` is constant, the honest pullback collapses
to the zero topological hom. -/
lemma pullbackHonest_of_rsum_eq_zero_of_const
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [DecidableEq X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_rsum : JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_statement X Y)
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hc : JacobianChallenge.IsConstantMap f) :
    pullbackHonest_of_rsum h_rsum f hf = 0 := by
  classical
  unfold pullbackHonest_of_rsum
  exact dif_pos hc

/-- Equation lemma: when `f` is non-constant, the honest pullback is the
multiplicity-weighted pullback `Jacobian.pullbackWeighted` with the
analytic data carried by `h_rsum`. -/
lemma pullbackHonest_of_rsum_eq_pullbackWeighted_of_not_const
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [DecidableEq X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_rsum : JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_statement X Y)
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) :
    pullbackHonest_of_rsum h_rsum f hf =
      Jacobian.pullbackWeighted f
        (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional
          f hf hnc)
        (JacobianChallenge.Manifold.manifoldRamificationIndex f)
        (JacobianChallenge.ContMDiff.degreeFiber f hf)
        (fun y => h_rsum f hf hnc y)
        (Pic0.divPullbackWeighted_descent_of_smooth hf hnc _ _ _) := by
  classical
  unfold pullbackHonest_of_rsum
  exact dif_neg hnc

/-! ### Auxiliary: composition of non-constant ContMDiff maps stays non-constant

If `f : X → Y` and `g : Y → Z` are both non-constant `ContMDiff` maps
between compact connected complex 1-manifolds, then `g ∘ f` is also
non-constant.

The argument uses only the *fibre-finiteness* consequence of `g` being
non-constant analytic — namely `fibres_finite_statement_holds_unconditional`
applied to `g`. If `g ∘ f` were constant with value `z₀`, the image of
`f` would lie inside the finite set `g ⁻¹' {z₀}`. Each fibre `f ⁻¹' {y}`
of `f` (`y ∈ g ⁻¹' {z₀}`) is the preimage of a clopen singleton in the
finite (and hence discrete) subspace `g ⁻¹' {z₀}` of the Hausdorff
manifold `Y`. Hence each fibre is clopen in `X`. Connectedness of `X`
then forces all but one to be empty, contradicting non-constancy of
`f`.

The proof reduces to topology: continuity of `f` (from `hf : ContMDiff
… ω f`), `T2Space Y`, `ConnectedSpace X`, and finiteness of
`g ⁻¹' {z₀}`. No analytic content is used beyond what is already
discharged unconditionally upstream. -/

/-- **`g ∘ f` is non-constant when `f` is non-constant continuous on a
connected source and the relevant `g`-fibre is finite in a T2 target.**
Used to discharge the case-split sub-case "both non-constant, but
composition somehow constant" in `pullbackHonest_of_rsum_comp`. -/
lemma not_isConstantMap_comp_of_finite_fibre_target
    {X : Type u} [TopologicalSpace X] [ConnectedSpace X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    {Z : Type w}
    {f : X → Y} {g : Y → Z}
    (hf_cont : Continuous f)
    (hg_finite_fibre : ∀ z : Z, (g ⁻¹' {z}).Finite)
    (hf_nc : ¬ JacobianChallenge.IsConstantMap f) :
    ¬ JacobianChallenge.IsConstantMap (g ∘ f) := by
  classical
  intro hgfc
  obtain ⟨z₀, hz₀⟩ := hgfc
  -- `f x ∈ g ⁻¹' {z₀}` for every `x`.
  have hfx_mem : ∀ x, f x ∈ g ⁻¹' {z₀} := fun x => hz₀ x
  -- `Set.range f ⊆ g ⁻¹' {z₀}`, finite.
  have hrange_fin : (Set.range f).Finite :=
    (hg_finite_fibre z₀).subset (Set.range_subset_iff.mpr hfx_mem)
  -- Use non-constancy of `f` to obtain `x₁, x₂` with `f x₁ ≠ f x₂`.
  haveI : Nonempty X := inferInstance
  obtain ⟨x₁, x₂, hne⟩ :=
    (JacobianChallenge.not_isConstantMap_iff_exists_pair).mp hf_nc
  -- Show `f ⁻¹' {f x₁}` is clopen in `X`. Closedness uses `T2Space Y`;
  -- openness uses that the singleton `{f x₁}` equals
  -- `(Set.range f) \ ((Set.range f) \ {f x₁})`, so its preimage under
  -- `f` is `X \ f ⁻¹' ((Set.range f) \ {f x₁})`. The set
  -- `(Set.range f) \ {f x₁}` is finite (subset of a finite set), hence
  -- closed in `Y` (finite union of T2-closed singletons), hence its
  -- preimage is closed, hence its complement is open.
  have hclosed : IsClosed (f ⁻¹' {f x₁}) :=
    isClosed_singleton.preimage hf_cont
  -- The "other values" set in `Y`.
  set S₀ : Set Y := (Set.range f) \ {f x₁} with hS₀_def
  have hS₀_fin : S₀.Finite := hrange_fin.subset (Set.diff_subset)
  have hS₀_closed : IsClosed S₀ := hS₀_fin.isClosed
  -- `f ⁻¹' S₀` is closed.
  have hpre_closed : IsClosed (f ⁻¹' S₀) := hS₀_closed.preimage hf_cont
  -- `f ⁻¹' {f x₁} = (f ⁻¹' S₀)ᶜ`.
  have hkey : f ⁻¹' ({f x₁} : Set Y) = (f ⁻¹' S₀)ᶜ := by
    ext x
    constructor
    · intro hx
      have hfx : f x = f x₁ := hx
      intro hxS
      obtain ⟨_, hfx_ne⟩ := hxS
      exact hfx_ne hfx
    · intro hx
      -- `f x ∈ Set.range f` always.
      have hfx_in : f x ∈ Set.range f := ⟨x, rfl⟩
      -- Deny the alternative: `f x ≠ f x₁`. Then `f x ∈ S₀`, contradicting `hx`.
      by_contra hne'
      apply hx
      refine ⟨hfx_in, ?_⟩
      intro h
      exact hne' h
  have hopen : IsOpen (f ⁻¹' ({f x₁} : Set Y)) := by
    rw [hkey]
    exact hpre_closed.isOpen_compl
  -- The set `f ⁻¹' {f x₁}` is clopen, contains `x₁`, but does NOT contain
  -- `x₂` (else `f x₂ = f x₁`, contradicting `hne`). Connectedness then
  -- forces it to be `∅` or `Set.univ`, contradiction either way.
  have hclopen : IsClopen (f ⁻¹' ({f x₁} : Set Y)) := ⟨hclosed, hopen⟩
  have hx₁_mem : x₁ ∈ f ⁻¹' ({f x₁} : Set Y) := rfl
  have hx₂_notMem : x₂ ∉ f ⁻¹' ({f x₁} : Set Y) := by
    intro h
    have : f x₂ = f x₁ := h
    exact hne this.symm
  -- Apply the local helper `preconnected_clopen_eq_univ` from
  -- `Manifold/FibreCardClopenReduction.lean`. (We use the `Set α`
  -- version on `α := X`, with `h_pre := isPreconnected_univ` from
  -- `ConnectedSpace X`.)
  have hL_nonempty : (f ⁻¹' ({f x₁} : Set Y)).Nonempty := ⟨x₁, hx₁_mem⟩
  have hL_univ : f ⁻¹' ({f x₁} : Set Y) = Set.univ :=
    JacobianChallenge.ContMDiff.Owed.degree.preconnected_clopen_eq_univ
      hclopen hL_nonempty isPreconnected_univ
  exact hx₂_notMem (hL_univ ▸ Set.mem_univ x₂)

/-! ### Composition (contravariant functoriality) -/

/-- **Composition identity for `pullbackHonest_of_rsum`.** Given the
Riemann-Hurwitz total-weight obligation discharged for each pair
`(X, Y)`, `(Y, Z)`, `(X, Z)`, the honest pullback respects composition:
`(g ∘ f)^* = f^* ∘ g^*`.

The proof case-splits on `IsConstantMap` for `f` and `g`. Three of the
four resulting cases collapse to the zero hom on both sides. The
"both-non-constant" case reduces to the divisor-level chain rule
`Div.fiberSumWeighted_comp_apply` with weights given by the manifold
ramification index, whose multiplicativity is the unconditional chain
rule `manifoldRamificationIndex_comp_unconditional`. -/
theorem pullbackHonest_of_rsum_comp
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [DecidableEq X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] [DecidableEq Y]
    {Z : Type w} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
    [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (h_rsum_XY : JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_statement X Y)
    (h_rsum_YZ : JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_statement Y Z)
    (h_rsum_XZ : JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_statement X Z)
    (f : X → Y) (g : Y → Z)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (P : Jacobian Z) :
    pullbackHonest_of_rsum h_rsum_XZ (g ∘ f) (hg.comp hf) P =
      pullbackHonest_of_rsum h_rsum_XY f hf
        (pullbackHonest_of_rsum h_rsum_YZ g hg P) := by
  classical
  -- Case split on `IsConstantMap g` first, then on `IsConstantMap f`.
  by_cases hgc : JacobianChallenge.IsConstantMap g
  · -- `g` constant ⇒ `pullbackHonest g = 0`, so RHS = `pullback f 0 = 0`.
    -- Also `g ∘ f` is constant (by `IsConstantMap.comp_left`), so LHS = 0.
    have hgfc : JacobianChallenge.IsConstantMap (g ∘ f) := hgc.comp_right f
    have hLHS :
        pullbackHonest_of_rsum h_rsum_XZ (g ∘ f) (hg.comp hf) P = 0 := by
      rw [pullbackHonest_of_rsum_eq_zero_of_const h_rsum_XZ (g ∘ f)
        (hg.comp hf) hgfc]
      rfl
    have hgP_zero :
        pullbackHonest_of_rsum h_rsum_YZ g hg P = 0 := by
      rw [pullbackHonest_of_rsum_eq_zero_of_const h_rsum_YZ g hg hgc]
      rfl
    rw [hLHS, hgP_zero, map_zero]
  · -- `g` non-constant.
    by_cases hfc : JacobianChallenge.IsConstantMap f
    · -- `f` constant ⇒ outer `pullbackHonest f = 0`, so RHS = 0.
      -- Also `g ∘ f` is constant (by `IsConstantMap.comp_left`), so LHS = 0.
      have hgfc : JacobianChallenge.IsConstantMap (g ∘ f) := by
        -- `f` constant, so `g ∘ f` is constant via `comp_left`.
        exact hfc.comp_left g
      have hLHS :
          pullbackHonest_of_rsum h_rsum_XZ (g ∘ f) (hg.comp hf) P = 0 := by
        rw [pullbackHonest_of_rsum_eq_zero_of_const h_rsum_XZ (g ∘ f)
          (hg.comp hf) hgfc]
        rfl
      have hRHS :
          pullbackHonest_of_rsum h_rsum_XY f hf
            (pullbackHonest_of_rsum h_rsum_YZ g hg P) = 0 := by
        rw [pullbackHonest_of_rsum_eq_zero_of_const h_rsum_XY f hf hfc]
        rfl
      rw [hLHS, hRHS]
    · -- Both `f` and `g` non-constant. Then `g ∘ f` is non-constant by
      -- the auxiliary lemma above (uses fibre-finiteness of `g`).
      have hg_fin :
          ∀ z : Z, (g ⁻¹' {z}).Finite :=
        JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional
          g hg hgc
      have hgfc : ¬ JacobianChallenge.IsConstantMap (g ∘ f) :=
        not_isConstantMap_comp_of_finite_fibre_target
          (X := X) (Y := Y) (Z := Z)
          hf.continuous hg_fin hfc
      -- Unfold all three pullbackHonest occurrences via the
      -- non-constant equation lemma.
      rw [pullbackHonest_of_rsum_eq_pullbackWeighted_of_not_const h_rsum_XZ
            (g ∘ f) (hg.comp hf) hgfc,
          pullbackHonest_of_rsum_eq_pullbackWeighted_of_not_const h_rsum_YZ
            g hg hgc,
          pullbackHonest_of_rsum_eq_pullbackWeighted_of_not_const h_rsum_XY
            f hf hfc]
      -- Both sides are now `Jacobian.pullbackWeighted` applications.
      -- The underlying additive map is `Pic0.pullbackWeighted`,
      -- agreeing with the topological-hom application definitionally
      -- (the `→ₜ+` structure literal sets `toAddMonoidHom :=
      -- Pic0.pullbackWeighted ...`).
      -- Reduce `P : Jacobian Z = Pic0 Z` to a quotient class.
      refine QuotientAddGroup.induction_on (P : Pic0 Z) ?_
      intro D
      -- The `Jacobian.pullbackWeighted ... (mk D)` form is definitionally
      -- the `Pic0.pullbackWeighted ... (mk D)` form via the `→ₜ+`'s
      -- `toAddMonoidHom` field. Rewrite via `Pic0.pullbackWeighted_mk`
      -- on each of the three occurrences.
      show (Pic0.pullbackWeighted (g ∘ f)
              (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional
                (g ∘ f) (hg.comp hf) hgfc)
              (JacobianChallenge.Manifold.manifoldRamificationIndex (g ∘ f))
              (JacobianChallenge.ContMDiff.degreeFiber (g ∘ f) (hg.comp hf))
              (fun y => h_rsum_XZ (g ∘ f) (hg.comp hf) hgfc y)
              (Pic0.divPullbackWeighted_descent_of_smooth (hg.comp hf) hgfc _ _ _) :
                Pic0 Z →+ Pic0 X) (QuotientAddGroup.mk D)
          = (Pic0.pullbackWeighted f
              (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional
                f hf hfc)
              (JacobianChallenge.Manifold.manifoldRamificationIndex f)
              (JacobianChallenge.ContMDiff.degreeFiber f hf)
              (fun y => h_rsum_XY f hf hfc y)
              (Pic0.divPullbackWeighted_descent_of_smooth hf hfc _ _ _) :
                Pic0 Y →+ Pic0 X)
              ((Pic0.pullbackWeighted g
                (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional
                  g hg hgc)
                (JacobianChallenge.Manifold.manifoldRamificationIndex g)
                (JacobianChallenge.ContMDiff.degreeFiber g hg)
                (fun y => h_rsum_YZ g hg hgc y)
                (Pic0.divPullbackWeighted_descent_of_smooth hg hgc _ _ _) :
                  Pic0 Z →+ Pic0 Y) (QuotientAddGroup.mk D))
      rw [Pic0.pullbackWeighted_mk g _ _ _ _ _ D]
      rw [Pic0.pullbackWeighted_mk (g ∘ f) _ _ _ _ _ D]
      rw [Pic0.pullbackWeighted_mk f _ _ _ _ _
            (Pic0.divPullbackWeighted g _ _ _ _ D)]
      -- Reduce `(QuotientAddGroup.mk d₁ : Pic0 X) = QuotientAddGroup.mk d₂`
      -- to `d₁ = d₂` in `Div0 X`.
      apply congrArg (QuotientAddGroup.mk : Div0 X → Pic0 X)
      -- Reduce `Div0 X` equality to underlying `Div X` equality.
      apply Subtype.ext
      simp only [Pic0.divPullbackWeighted_coe]
      -- Goal: `Div.fiberSumWeighted (g ∘ f) hgf_fin e_{g∘f} (D : Div Z)
      --       = Div.fiberSumWeighted f hf_fin e_f
      --           (Div.fiberSumWeighted g hg_fin e_g (D : Div Z))`.
      -- Apply the divisor chain rule with multiplicative weights.
      refine JacobianChallenge.Div.fiberSumWeighted_comp_apply
        (X := X) (Y := Y) (Z := Z) f g
        (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional
          f hf hfc)
        (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional
          g hg hgc)
        (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional
          (g ∘ f) (hg.comp hf) hgfc)
        (JacobianChallenge.Manifold.manifoldRamificationIndex f)
        (JacobianChallenge.Manifold.manifoldRamificationIndex g)
        (JacobianChallenge.Manifold.manifoldRamificationIndex (g ∘ f))
        ?_ (D : Div Z)
      -- Multiplicativity of `manifoldRamificationIndex` under composition.
      intro x
      exact JacobianChallenge.Manifold.manifoldRamificationIndex_comp_unconditional
        f g hf hg hfc hgc x

/-! ### `pushforward ∘ pullback` is multiplication by degree (challenge item 24)

The headline degree formula at the `Jacobian` level. Cases on
`IsConstantMap f`:
* **Constant `f`**: both sides are `0` — LHS via `pullbackHonest = 0` and
  `pushforward 0 = 0`; RHS via `degreeFiber f hf = 0` (constant case).
* **Non-constant `f`**: reduces to the divisor-level
  `Pic0.pushforward_pullbackWeighted` with `N := degreeFiber f hf` and the
  `hN_total` certificate carried by `h_rsum`. -/

theorem pushforward_pullbackHonest_of_rsum
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [DecidableEq X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] [DecidableEq Y]
    (h_rsum : JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_statement X Y)
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (P : Jacobian Y) :
    Jacobian.pushforward hf
        (pullbackHonest_of_rsum h_rsum f hf P)
      = (JacobianChallenge.ContMDiff.degreeFiber f hf : ℤ) • P := by
  classical
  by_cases hc : JacobianChallenge.IsConstantMap f
  · -- Constant case: LHS = pushforward f 0 = 0; RHS = 0 • P = 0.
    have hpb_zero : pullbackHonest_of_rsum h_rsum f hf = 0 :=
      pullbackHonest_of_rsum_eq_zero_of_const h_rsum f hf hc
    have hpb_zero_apply :
        pullbackHonest_of_rsum h_rsum f hf P = 0 := by
      rw [hpb_zero]; rfl
    rw [hpb_zero_apply, map_zero]
    -- RHS: `(degreeFiber f hf : ℤ) • P = 0 • P = 0`.
    -- Constant `f` ⇒ `degreeFiber f hf = 0`. Use `IsConstantMap.elim` to
    -- get a constant value `c` and `hf_eq : f = fun _ => c`, then apply
    -- `degreeFiber_const`.
    obtain ⟨c, hc_eq⟩ := hc
    have hf_fun : f = (fun _ : X => c) := funext hc_eq
    have hdeg : JacobianChallenge.ContMDiff.degreeFiber f hf = 0 := by
      subst hf_fun
      exact JacobianChallenge.ContMDiff.degreeFiber_const c hf
    rw [hdeg]
    exact (zero_smul ℤ P).symm
  · -- Non-constant case: rewrite both sides through their `Pic0` form.
    rw [pullbackHonest_of_rsum_eq_pullbackWeighted_of_not_const
          h_rsum f hf hc]
    -- Now: `Jacobian.pushforward f (Jacobian.pullbackWeighted f ... P)
    --        = (degreeFiber f hf : ℤ) • P`.
    -- Both `Jacobian.pushforward` and `Jacobian.pullbackWeighted` carry
    -- `Pic0`-level additive maps via their `→ₜ+` `toAddMonoidHom` field,
    -- so the goal reduces to a `Pic0` statement.
    show (Pic0.pushforward (X := X) (Y := Y) hf
            ((Pic0.pullbackWeighted f
              (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional
                f hf hc)
              (JacobianChallenge.Manifold.manifoldRamificationIndex f)
              (JacobianChallenge.ContMDiff.degreeFiber f hf)
              (fun y => h_rsum f hf hc y)
              (Pic0.divPullbackWeighted_descent_of_smooth hf hc _ _ _) :
                Pic0 Y →+ Pic0 X) (P : Pic0 Y)) : Pic0 Y)
        = (JacobianChallenge.ContMDiff.degreeFiber f hf : ℤ) • (P : Pic0 Y)
    exact Pic0.pushforward_pullbackWeighted (X := X) (Y := Y) hf
      (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional
        f hf hc)
      (JacobianChallenge.Manifold.manifoldRamificationIndex f)
      (JacobianChallenge.ContMDiff.degreeFiber f hf)
      (fun y => h_rsum f hf hc y)
      (Pic0.divPullbackWeighted_descent_of_smooth hf hc _ _ _) P

/-! ### Identity case: `pullbackHonest_of_rsum h_rsum id contMDiff_id P = P`

Two regimes, dispatched by `Classical.byCases` on `IsConstantMap (id : X → X)`.

* **Constant `id`**: this forces `Subsingleton X` (every point equals the
  constant value). Then every divisor of degree zero is `0` (single
  potential support point with vanishing coefficient by the degree-zero
  hypothesis), so `Pic0 X` is subsingleton, so `0 = P` for any `P`.
* **Non-constant `id`**: the divisor-pullback machinery activates with
  fibres `id ⁻¹' {y} = {y}` (singletons) and weights
  `manifoldRamificationIndex id y = 1`. The weighted fibre-sum collapses
  pointwise to the identity on `Div X`, descending to the identity on
  `Pic0 X`.

Both branches are unconditional once `manifoldRamificationIndex id y = 1`
is established (proved inline via `analyticOrderAt_congr` and
`AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero`). -/

/-- The chart-pullback of `id` at `x` agrees eventually with the identity
on a neighborhood of `(chartAt ℂ x) x`. This collapses
`F z := (chartAt ℂ x) ((chartAt ℂ x).symm z)` to `z` near `z₀`. -/
private lemma chart_pullback_id_eventuallyEq
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] (x : X) :
    (fun z : ℂ => (chartAt ℂ x) ((chartAt ℂ x).symm z))
      =ᶠ[nhds ((chartAt ℂ x) x)] id := by
  filter_upwards [chart_target_mem_nhds (H := ℂ) x] with z hz
  exact (chartAt ℂ x).right_inv hz

/-- **`manifoldRamificationIndex id x = 1`** at every point `x : X` of a
charted space modelled on `ℂ`. The chart-pullback of `id` is locally the
identity, so `F z - F z₀ = z - z₀` near `z₀`, whose analytic order is `1`
(zero of multiplicity one with non-vanishing derivative). -/
lemma manifoldRamificationIndex_id
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] (x : X) :
    JacobianChallenge.Manifold.manifoldRamificationIndex (id : X → X) x = 1 := by
  classical
  rw [JacobianChallenge.Manifold.manifoldRamificationIndex_eq]
  -- Goal:
  --   `(analyticOrderAt (fun z => F z - F z₀) z₀).toNat = 1`
  -- where `z₀ := (chartAt ℂ x) x` and
  -- `F z := (chartAt ℂ (id x)) (id ((chartAt ℂ x).symm z))`.
  -- Compute the order is exactly 1 in `ℕ∞`.
  have hev : (fun z : ℂ => (chartAt ℂ x) ((chartAt ℂ x).symm z))
                =ᶠ[nhds ((chartAt ℂ x) x)] id := chart_pullback_id_eventuallyEq x
  have hF_z₀ :
      ((chartAt ℂ ((id : X → X) x)) ∘ (id : X → X) ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) = (chartAt ℂ x) x := by
    change (chartAt ℂ x) ((chartAt ℂ x).symm ((chartAt ℂ x) x)) = (chartAt ℂ x) x
    exact (chartAt ℂ x).right_inv (mem_chart_target (H := ℂ) x)
  have hF_eq :
      (fun z : ℂ =>
          ((chartAt ℂ ((id : X → X) x)) ∘ (id : X → X) ∘ (chartAt ℂ x).symm) z -
          ((chartAt ℂ ((id : X → X) x)) ∘ (id : X → X) ∘ (chartAt ℂ x).symm)
            ((chartAt ℂ x) x))
        =ᶠ[nhds ((chartAt ℂ x) x)] (fun z : ℂ => z - (chartAt ℂ x) x) := by
    filter_upwards [hev] with z hz
    change (chartAt ℂ x) ((chartAt ℂ x).symm z) -
            ((chartAt ℂ ((id : X → X) x)) ∘ (id : X → X) ∘ (chartAt ℂ x).symm)
              ((chartAt ℂ x) x)
        = z - (chartAt ℂ x) x
    rw [hF_z₀]
    have hz' : (chartAt ℂ x) ((chartAt ℂ x).symm z) = z := hz
    rw [hz']
  rw [analyticOrderAt_congr hF_eq]
  -- Now: `(analyticOrderAt (· - z₀) z₀).toNat = 1` where `z₀ = (chartAt ℂ x) x`.
  have h_an : AnalyticAt ℂ (fun z : ℂ => z - (chartAt ℂ x) x) ((chartAt ℂ x) x) :=
    analyticAt_id.sub analyticAt_const
  have h_zero : (fun z : ℂ => z - (chartAt ℂ x) x) ((chartAt ℂ x) x) = 0 :=
    sub_self _
  have h_deriv : deriv (fun z : ℂ => z - (chartAt ℂ x) x) ((chartAt ℂ x) x) ≠ 0 := by
    rw [deriv_sub_const]
    simp
  rw [h_an.analyticOrderAt_eq_one_of_zero_deriv_ne_zero h_zero h_deriv]
  rfl

/-- **`Subsingleton X` ⇒ `Subsingleton (Pic0 X)`.**

If `X` has at most one point, every divisor in `Div X` is determined by
its value at the unique point (or empty), and the degree-zero
constraint forces that value to be `0`. Hence `Div0 X = {0}` and
`Pic0 X` is subsingleton. -/
private lemma pic0_subsingleton_of_subsingleton
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    [Subsingleton X] : Subsingleton (Pic0 X) := by
  classical
  -- It suffices to show every `D₁ D₂ : Div0 X` agree, then descend.
  have hDiv0 : ∀ D₁ D₂ : Div0 X, D₁ = D₂ := by
    intro D₁ D₂
    -- Reduce to `(D₁ : Div X) = (D₂ : Div X)`.
    apply Subtype.ext
    -- Reduce to pointwise equality via the `ext` lemma on `locallyFinsuppWithin`.
    apply Function.locallyFinsuppWithin.ext
    intro y
    -- Both `D₁ y` and `D₂ y` equal the degree, which is `0`.
    have hDeg₁ : (D₁ : Div X).degree = 0 :=
      (JacobianChallenge.mem_Div0_iff (D₁ : Div X)).mp D₁.2
    have hDeg₂ : (D₂ : Div X).degree = 0 :=
      (JacobianChallenge.mem_Div0_iff (D₂ : Div X)).mp D₂.2
    -- For Subsingleton X, the support is contained in `{y}`, so the degree
    -- equals `(D : Div X) y`. We give the support-based argument.
    have hkey : ∀ (D : Div X), (D : Div X) y = D.degree := by
      intro D
      classical
      -- `D.degree = ∑ x ∈ D.supportFinset, D x`. By `Subsingleton X`, every
      -- `x ∈ D.supportFinset` equals `y`, so the sum collapses.
      by_cases hy : (D : X → ℤ) y = 0
      · -- `y ∉ D.supportFinset`. By Subsingleton, every `x ∈ supp` equals `y`,
        -- but `y ∉ supp`, so supp is empty.
        have hsupp_empty : D.supportFinset = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro x hx
          have hxy : x = y := Subsingleton.elim x y
          have hxD : (D : X → ℤ) x ≠ 0 := Div.mem_supportFinset.mp hx
          rw [hxy] at hxD
          exact hxD hy
        rw [hy]
        change (0 : ℤ) = D.degree
        unfold Div.degree
        rw [hsupp_empty, Finset.sum_empty]
      · -- `y ∈ D.supportFinset`, and supportFinset = {y}.
        have hy_mem : y ∈ D.supportFinset := Div.mem_supportFinset.mpr hy
        have hsupp_eq : D.supportFinset = {y} := by
          apply Finset.eq_singleton_iff_unique_mem.mpr
          refine ⟨hy_mem, ?_⟩
          intro x _
          exact Subsingleton.elim x y
        unfold Div.degree
        rw [hsupp_eq, Finset.sum_singleton]
    rw [hkey (D₁ : Div X), hkey (D₂ : Div X), hDeg₁, hDeg₂]
  -- Descend to the quotient.
  refine ⟨fun P Q => ?_⟩
  refine QuotientAddGroup.induction_on P ?_
  intro D₁
  refine QuotientAddGroup.induction_on Q ?_
  intro D₂
  rw [hDiv0 D₁ D₂]

/-- The image of `Pic0.divPullbackWeighted id _ _ _ _ D` agrees with `D`
on the divisor side, when each fibre `id ⁻¹' {y} = {y}` and the weights
`e y = 1` everywhere. The proof reduces to pointwise equality, then
follows the same shape as `Div.fiberSum_id_apply`. -/
private lemma divPullbackWeighted_id_apply
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    [DecidableEq X]
    (hf : ∀ y, ((id : X → X) ⁻¹' {y}).Finite) (e : X → ℕ)
    (he : ∀ x, e x = 1) (N : ℕ)
    (hN_total : ∀ y, (∑ x ∈ (hf y).toFinset, e x) = N) (D : Div0 X) :
    Pic0.divPullbackWeighted (id : X → X) hf e N hN_total D = D := by
  classical
  -- Reduce to underlying-`Div X` equality.
  apply Subtype.ext
  rw [Pic0.divPullbackWeighted_coe]
  -- Goal: `Div.fiberSumWeighted id hf e (D : Div X) = (D : Div X)`.
  rw [Div.fiberSumWeighted_apply]
  -- Reduce to pointwise equality (`DFunLike.ext`).
  refine DFunLike.ext _ _ ?_
  intro z
  -- Helper: each fibre `id ⁻¹' {y} = {y}`, hence `(hf y).toFinset = {y}`.
  have hfin_eq : ∀ y : X, (hf y).toFinset = ({y} : Finset X) := by
    intro y
    have h1 : (id : X → X) ⁻¹' {y} = ({y} : Set X) := Set.preimage_id
    apply Finset.ext
    intro a
    rw [Set.Finite.mem_toFinset, h1, Finset.mem_singleton, Set.mem_singleton_iff]
  -- The inner sum collapses to `Div.single y`.
  have hinner : ∀ y : X,
      (∑ z ∈ (hf y).toFinset, (e z : ℤ) • Div.single (X := X) z : Div X)
        = Div.single y := by
    intro y
    rw [hfin_eq y, Finset.sum_singleton, he y]
    show ((1 : ℤ) • Div.single (X := X) y : Div X) = _
    rw [one_smul]
  -- Rewrite the outer sum using `hinner`, reducing to the standard
  -- support-decomposition `∑ y ∈ supp D, D y • Div.single y = D`.
  unfold Div.fiberSumWeightedFun
  have hLHS_eq :
      (∑ y ∈ (D : Div X).supportFinset,
          ((D : Div X) y) •
            (∑ z ∈ (hf y).toFinset, (e z : ℤ) • Div.single (X := X) z) : Div X)
        = ∑ y ∈ (D : Div X).supportFinset,
            ((D : Div X) y) • Div.single (X := X) y := by
    refine Finset.sum_congr rfl ?_
    intro y _
    exact congrArg (((D : Div X) y) • ·) (hinner y)
  rw [hLHS_eq]
  -- Now prove `(∑ y ∈ supp D, D y • Div.single y) z = D z`.
  rw [Function.locallyFinsuppWithin.coe_sum]
  simp only [Finset.sum_apply]
  have hpt : ∀ y ∈ (D : Div X).supportFinset,
      ((((D : Div X) y) • Div.single (X := X) y : Div X) : X → ℤ) z
        = ((D : Div X) y) * (if z = y then 1 else 0) := by
    intro y _
    rw [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply,
        Div.single_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl hpt]
  -- Sum collapses: at most one term (`y = z`) contributes.
  by_cases hz : z ∈ (D : Div X).supportFinset
  · rw [Finset.sum_eq_single z]
    · simp
    · intro y _ hyz
      have hzy : ¬ z = y := fun h => hyz h.symm
      simp [hzy]
    · intro h
      exact (h hz).elim
  · -- `z` not in support: `D z = 0`, and every summand vanishes.
    have hDz : ((D : Div X) : X → ℤ) z = 0 :=
      Div.apply_eq_zero_of_notMem_supportFinset hz
    rw [hDz]
    refine Finset.sum_eq_zero ?_
    intro y hy
    by_cases hzy : z = y
    · -- `z = y` and `y ∈ supp`, so `z ∈ supp`, contradicting `hz`.
      exact absurd (hzy ▸ hy) hz
    · simp [hzy]

/-- **Identity equation for the honest pullback.** When `f = id`, the
honest pullback is the identity on `Jacobian X`. -/
theorem pullbackHonest_of_rsum_id
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [DecidableEq X]
    (h_rsum : JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_statement X X)
    (P : Jacobian X) :
    pullbackHonest_of_rsum h_rsum (id : X → X) contMDiff_id P = P := by
  classical
  by_cases hc : JacobianChallenge.IsConstantMap (id : X → X)
  · -- Constant `id` ⇒ `Subsingleton X` ⇒ `Subsingleton (Pic0 X) = Subsingleton (Jacobian X)`.
    haveI hsub : Subsingleton X := by
      obtain ⟨y, hy⟩ := hc
      refine ⟨fun a b => ?_⟩
      have ha : a = y := hy a
      have hb : b = y := hy b
      exact ha.trans hb.symm
    haveI hPic : Subsingleton (Pic0 X) := pic0_subsingleton_of_subsingleton
    -- `Jacobian X` is defined as `Pic0 X`, so `Subsingleton` transfers.
    haveI hJac : Subsingleton (JacobianChallenge.Jacobian X) := hPic
    exact Subsingleton.elim _ _
  · -- Non-constant. Unfold via `pullbackHonest_of_rsum_eq_pullbackWeighted_of_not_const`.
    rw [pullbackHonest_of_rsum_eq_pullbackWeighted_of_not_const h_rsum
          (id : X → X) contMDiff_id hc]
    -- Reduce `P : Jacobian X = Pic0 X` to a quotient class.
    refine QuotientAddGroup.induction_on (P : Pic0 X) ?_
    intro D
    -- The `Jacobian.pullbackWeighted ... (mk D)` form is definitionally
    -- the `Pic0.pullbackWeighted ... (mk D)` via the `→ₜ+`'s
    -- `toAddMonoidHom` field. Rewrite via `Pic0.pullbackWeighted_mk`.
    show (Pic0.pullbackWeighted (id : X → X)
            (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional
              (id : X → X) contMDiff_id hc)
            (JacobianChallenge.Manifold.manifoldRamificationIndex (id : X → X))
            (JacobianChallenge.ContMDiff.degreeFiber (id : X → X) contMDiff_id)
            (fun y => h_rsum (id : X → X) contMDiff_id hc y)
            (Pic0.divPullbackWeighted_descent_of_smooth contMDiff_id hc _ _ _) :
              Pic0 X →+ Pic0 X) (QuotientAddGroup.mk D)
        = (QuotientAddGroup.mk D : Pic0 X)
    rw [Pic0.pullbackWeighted_mk (id : X → X) _ _ _ _ _ D]
    -- Reduce the quotient equality to `divPullbackWeighted_id_apply`.
    apply congrArg (QuotientAddGroup.mk : Div0 X → Pic0 X)
    apply divPullbackWeighted_id_apply
    intro x
    exact manifoldRamificationIndex_id x

end Jacobian

end JacobianChallenge
