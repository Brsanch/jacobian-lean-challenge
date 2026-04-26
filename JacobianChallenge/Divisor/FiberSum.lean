/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor
import JacobianChallenge.Divisor.Single

set_option diagnostics.threshold 100

/-! # Divisor pullback along a finite-fiber map

This file constructs the divisor-level **pullback** of a divisor along a map
`f : X → Y` whose every fiber `f⁻¹ {y}` is finite. The construction is the
unique `ℤ`-linear extension of

  `Div.single y ↦ ∑_{x ∈ f⁻¹ {y}} Div.single x`

to all of `Div Y`. It is the load-bearing input for an honest
`Jacobian.pullback`: a continuous holomorphic map `f : X → Y` of compact
complex curves has finite fibers, and `fiberSum f` realises `f^* : Div Y →+
Div X` as a group homomorphism on divisors. (Once `PrincDiv` is wired up
honestly the descent to `Pic⁰` will require an additional content step;
that is owed downstream and not in scope here.)

## What's in this file

* `Div.fiberSumFun f hf D` — the underlying function `Div Y → Div X`,
  defined as `∑ y ∈ D.supportFinset, D y • (∑ x ∈ (hf y).toFinset, Div.single x)`.
* `Div.fiberSumFun_eq_sum` — the value can be computed by summing over any
  finset of `Y` containing `D.supportFinset` (terms outside the support
  contribute zero).
* `Div.fiberSumFun_zero` / `Div.fiberSumFun_add` — the underlying function
  is `0`-preserving and additive.
* `Div.fiberSum f hf : Div Y →+ Div X` — packaged as an `AddMonoidHom`.
* `Div.fiberSum_apply` — `fiberSum f hf D = fiberSumFun f hf D` (definitional
  unfolding for the bundled hom).
* `Div.fiberSum_single` — sends `Div.single y` to the fiber sum
  `∑ x ∈ (hf y).toFinset, Div.single x`.
* `Div.fiberSum_id_apply` — the identity case: `fiberSum id _ D = D`.

The hypothesis `hf : ∀ y, (f ⁻¹' {y}).Finite` is taken as an honest
finite-fiber hypothesis (no typeclass shortcut). It is used directly to
materialise each fiber as a `Finset X` via `Set.Finite.toFinset`.

The `[DecidableEq X]` hypothesis is required by `Div.single`
(via `Function.locallyFinsuppWithin.single`, which uses `Pi.single`).
The `[T2Space Y] [CompactSpace Y]` hypotheses are required to make
`D.supportFinset : Finset Y` available for `D : Div Y` (via the existing
`Div.supportFinset` API on a compact Hausdorff space).
-/

namespace JacobianChallenge

namespace Div

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [DecidableEq X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]

/-! ### The underlying function `Div Y → Div X` -/

/-- The *fiber-sum function* `Div.fiberSumFun f hf D` sends a divisor `D` on
`Y` to the divisor on `X` obtained by replacing each basis element
`Div.single y` (with multiplicity `D y`) by the sum of the basis elements
`Div.single x` over the (finite) fiber `f⁻¹ {y}`:

  `fiberSumFun f hf D := ∑ y ∈ D.supportFinset, D y • (∑ x ∈ (hf y).toFinset, Div.single x)`.

The packaging as an `AddMonoidHom` is `Div.fiberSum` below. -/
noncomputable def fiberSumFun (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite)
    (D : Div Y) : Div X :=
  ∑ y ∈ D.supportFinset, D y • (∑ x ∈ (hf y).toFinset, Div.single x)

/-- The fiber-sum function agrees with the finset sum over any finset of `Y`
containing the support of `D`. Values of `D` outside the support are zero,
so the additional terms contribute zero. -/
lemma fiberSumFun_eq_sum (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite)
    (D : Div Y) (S : Finset Y) (hS : D.supportFinset ⊆ S) :
    fiberSumFun f hf D
      = ∑ y ∈ S, D y • (∑ x ∈ (hf y).toFinset, Div.single x) := by
  -- Unfold the LHS to make the support-sum visible.
  change (∑ y ∈ D.supportFinset, D y • (∑ x ∈ (hf y).toFinset, Div.single x) : Div X)
        = ∑ y ∈ S, D y • (∑ x ∈ (hf y).toFinset, Div.single x)
  -- `Finset.sum_subset hS h` lets us extend the sum to `S`.
  refine Finset.sum_subset hS ?_
  intro y _ hyS
  -- Need: `D y • (∑ x ∈ (hf y).toFinset, Div.single x) = (0 : Div X)`.
  -- `D y = 0` outside the support, so `0 • _ = 0`.
  have hy : (D : Div Y) y = 0 := apply_eq_zero_of_notMem_supportFinset hyS
  rw [hy, zero_smul]

/-- The fiber-sum function sends `0` to `0`. -/
lemma fiberSumFun_zero (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) :
    fiberSumFun f hf (0 : Div Y) = 0 := by
  classical
  -- Unfold the definition: sum over `(0 : Div Y).supportFinset`.
  unfold fiberSumFun
  -- The support of `0 : Div Y` is empty, so the sum is empty, hence `0`.
  -- `degree_zero` proves the supportFinset is empty by the same argument;
  -- we replicate the relevant step here.
  have hempty : (0 : Div Y).supportFinset = (∅ : Finset Y) := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro y hy
    -- `mem_supportFinset` gives `(0 : Div Y) y ≠ 0`, contradiction.
    rw [mem_supportFinset] at hy
    apply hy
    show ((0 : Div Y) : Y → ℤ) y = 0
    rw [Function.locallyFinsuppWithin.coe_zero]
    rfl
  rw [hempty, Finset.sum_empty]

/-- Additivity of the fiber-sum function. -/
lemma fiberSumFun_add (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite)
    (D₁ D₂ : Div Y) :
    fiberSumFun f hf (D₁ + D₂) = fiberSumFun f hf D₁ + fiberSumFun f hf D₂ := by
  classical
  -- Use the common finset `S := supp(D₁+D₂) ∪ supp D₁ ∪ supp D₂`.
  set S : Finset Y :=
    (D₁ + D₂).supportFinset ∪ D₁.supportFinset ∪ D₂.supportFinset with hS_def
  have h12 : (D₁ + D₂).supportFinset ⊆ S := by
    intro y hy
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hy)
  have h1 : D₁.supportFinset ⊆ S := by
    intro y hy
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hy)
  have h2 : D₂.supportFinset ⊆ S := by
    intro y hy
    exact Finset.mem_union_right _ hy
  rw [fiberSumFun_eq_sum f hf (D₁ + D₂) S h12,
      fiberSumFun_eq_sum f hf D₁ S h1,
      fiberSumFun_eq_sum f hf D₂ S h2]
  -- Now distribute over the common finset and use `add_smul`.
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro y _
  -- `(D₁ + D₂) y = D₁ y + D₂ y`, then `add_smul`.
  have hpt : ((D₁ + D₂ : Div Y) : Y → ℤ) y = (D₁ : Y → ℤ) y + (D₂ : Y → ℤ) y := by
    simp [Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
  rw [hpt, add_smul]

/-! ### Packaged as an `AddMonoidHom` -/

/-- The divisor pullback `Div Y →+ Div X` along a continuous map `f : X → Y`
whose fibers `f⁻¹ {y}` are all finite. Sends `single y` to
`∑_{x ∈ f⁻¹ {y}} single x`, extended `ℤ`-linearly to all of `Div Y`. -/
noncomputable def fiberSum (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) :
    Div Y →+ Div X where
  toFun := fiberSumFun f hf
  map_zero' := fiberSumFun_zero f hf
  map_add' := fiberSumFun_add f hf

@[simp] lemma fiberSum_apply (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite)
    (D : Div Y) : fiberSum f hf D = fiberSumFun f hf D := rfl

/-! ### Behaviour on `Div.single` -/

/-- `fiberSum` sends `Div.single y` to the sum over the fiber `f⁻¹ {y}`. -/
lemma fiberSum_single [DecidableEq Y] (f : X → Y)
    (hf : ∀ y, (f ⁻¹' {y}).Finite) (y : Y) :
    fiberSum f hf (Div.single y)
      = ∑ x ∈ (hf y).toFinset, Div.single x := by
  classical
  show fiberSumFun f hf (Div.single y) = ∑ x ∈ (hf y).toFinset, Div.single x
  -- Use that `(Div.single y).supportFinset = {y}` and `(Div.single y) y = 1`.
  have hsub : (Div.single y : Div Y).supportFinset ⊆ ({y} : Finset Y) := by
    intro z hz
    rw [supportFinset_single] at hz
    exact hz
  rw [fiberSumFun_eq_sum f hf (Div.single y) ({y} : Finset Y) hsub,
      Finset.sum_singleton]
  -- `(Div.single y) y = 1`, so `1 • _ = _`.
  rw [single_apply, if_pos rfl, one_smul]

/-! ### Identity behaviour -/

/-- `fiberSum` for the identity map (with the singleton-fiber proof) is the
identity hom on `Div X`. The honest proof goes pointwise: at any `z : X`,
the identity-fiber sum `∑ x ∈ {z}, Div.single x` evaluated at `z` is `1`,
matched against `D z` via the support sum. -/
lemma fiberSum_id_apply (D : Div X) :
    fiberSum (id : X → X) (fun _ => Set.finite_singleton _) D = D := by
  classical
  -- Reduce to pointwise equality.
  refine DFunLike.ext _ _ ?_
  intro z
  -- Unfold `fiberSum` to `fiberSumFun`.
  show (fiberSumFun (id : X → X) (fun _ => Set.finite_singleton _) D : Div X) z
        = (D : Div X) z
  -- Compute LHS pointwise. The fiber of `id` at `y : X` is `{y}` as a set,
  -- and `(Set.finite_singleton y).toFinset = {y}` as a finset. Its sum is
  -- `Div.single y`. So `fiberSumFun id _ D = ∑ y ∈ supp D, D y • Div.single y`.
  have hfiber : ∀ y : X,
      (∑ x ∈ ((Set.finite_singleton y).toFinset : Finset X), Div.single x : Div X)
        = Div.single y := by
    intro y
    have htf : (Set.finite_singleton y).toFinset = ({y} : Finset X) := by
      ext x
      simp
    rw [htf, Finset.sum_singleton]
  -- Rewrite the inner sums using `hfiber`.
  have hLHS_eq : (fiberSumFun (id : X → X) (fun _ => Set.finite_singleton _) D : Div X)
      = ∑ y ∈ D.supportFinset, D y • Div.single y := by
    unfold fiberSumFun
    refine Finset.sum_congr rfl ?_
    intro y _
    -- `hfiber y : ∑ x ∈ (Set.finite_singleton y).toFinset, Div.single x = Div.single y`.
    -- Wrap with `congr_arg (D y • ·)` to lift through the smul.
    exact congrArg (D y • ·) (hfiber y)
  rw [hLHS_eq]
  -- Now prove `(∑ y ∈ supp D, D y • Div.single y) z = D z` pointwise.
  -- Use `coe_sum` to push the FunLike app through the sum.
  rw [Function.locallyFinsuppWithin.coe_sum]
  simp only [Finset.sum_apply]
  -- Each summand is `D y * (if z = y then 1 else 0)` via `zsmul_single_apply`.
  have hpt : ∀ y ∈ D.supportFinset,
      ((D y • Div.single y : Div X) : X → ℤ) z
        = D y * (if z = y then 1 else 0) := by
    intro y _
    -- Inline `zsmul_single_apply` (which lives in `Jacobian.lean`,
    -- a downstream file) so we keep this file's imports minimal.
    rw [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, single_apply,
        smul_eq_mul]
  rw [Finset.sum_congr rfl hpt]
  -- The sum collapses: at most one term (`y = z`) contributes.
  by_cases hz : z ∈ D.supportFinset
  · rw [Finset.sum_eq_single z]
    · simp
    · intro y _ hyz
      have hzy : ¬ z = y := fun h => hyz h.symm
      simp [hzy]
    · intro h
      exact (h hz).elim
  · -- `z` not in support: `D z = 0`, and every summand vanishes.
    have hDz : (D : Div X) z = 0 := apply_eq_zero_of_notMem_supportFinset hz
    rw [hDz]
    -- Every summand `D y * (if z = y then 1 else 0)` is zero: if `z = y`
    -- then `y = z ∈ supp` contradicting `hz`; otherwise the indicator is `0`.
    refine Finset.sum_eq_zero ?_
    intro y hy
    by_cases hzy : z = y
    · -- `z = y` and `y ∈ supp`, so `z ∈ supp`, contradicting `hz`.
      exact absurd (hzy ▸ hy) hz
    · simp [hzy]

/-! ### Contravariant composition -/

/-- The set-level decomposition behind contravariant functoriality:
the fiber of `g ∘ f` over `z` is the (disjoint) union, over `y ∈ g⁻¹{z}`,
of the fibers `f⁻¹{y}`. -/
lemma preimage_comp_singleton {X Y Z : Type*} (f : X → Y) (g : Y → Z) (z : Z) :
    (g ∘ f) ⁻¹' {z} = ⋃ y ∈ g ⁻¹' {z}, f ⁻¹' {y} := by
  ext x
  simp [Set.mem_preimage, Set.mem_iUnion, Function.comp_apply]

/-- Finite-fiber hypothesis for `g ∘ f` is implied by finite-fiber hypotheses
for `f` and `g`: each `(g ∘ f)⁻¹{z}` is a finite (in `g⁻¹{z}`) union of finite
sets `f⁻¹{y}`. -/
lemma finite_fiber_comp {X Y Z : Type*} (f : X → Y) (g : Y → Z)
    (hf : ∀ y, (f ⁻¹' {y}).Finite) (hg : ∀ z, (g ⁻¹' {z}).Finite) :
    ∀ z, ((g ∘ f) ⁻¹' {z}).Finite := by
  intro z
  rw [preimage_comp_singleton]
  exact (hg z).biUnion (fun y _ => hf y)

variable {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
  [DecidableEq Y]

/-- Contravariant composition: `fiberSum (g ∘ f) = fiberSum f ∘ fiberSum g`
on each divisor. The combinatorial fact behind this is the disjoint
decomposition `(g ∘ f)⁻¹{z} = ⋃_{y ∈ g⁻¹{z}} f⁻¹{y}` (see
`preimage_comp_singleton`); the `hgf` hypothesis is in fact implied by
`hf` and `hg` (see `finite_fiber_comp`), but we keep it as a parameter so
the statement matches the natural pullback signature without forcing the
caller to thread the derivation. -/
lemma fiberSum_comp_apply
    (f : X → Y) (g : Y → Z)
    (hf : ∀ y, (f ⁻¹' {y}).Finite)
    (hg : ∀ z, (g ⁻¹' {z}).Finite)
    (hgf : ∀ z, ((g ∘ f) ⁻¹' {z}).Finite)
    (D : Div Z) :
    fiberSum (g ∘ f) hgf D = fiberSum f hf (fiberSum g hg D) := by
  classical
  -- LHS expands to ∑ z ∈ supp D, D z • (∑ x ∈ ((g∘f)⁻¹{z}).toFinset, single x).
  -- RHS = fiberSum f hf (∑ z ∈ supp D, D z • (∑ y ∈ (g⁻¹{z}).toFinset, single y)).
  -- Push fiberSum f hf through the outer sum and ℤ-smul, then through each
  -- inner sum, and apply fiberSum_single twice.
  -- Step 1: rewrite the inner `fiberSum g hg D` as its finset-sum form.
  have hg_eq : fiberSum g hg D
      = ∑ z ∈ D.supportFinset, D z • ∑ y ∈ (hg z).toFinset, Div.single y := by
    show fiberSumFun g hg D = _
    rfl
  -- Step 2: rewrite the LHS `fiberSum (g∘f) hgf D` similarly.
  have hLHS : fiberSum (g ∘ f) hgf D
      = ∑ z ∈ D.supportFinset, D z •
          ∑ x ∈ (hgf z).toFinset, (Div.single x : Div X) := by
    show fiberSumFun (g ∘ f) hgf D = _
    rfl
  rw [hLHS, hg_eq, map_sum (fiberSum f hf)]
  refine Finset.sum_congr rfl ?_
  intro z _
  -- For each `z`, push through the ℤ-smul and the inner sum.
  rw [map_zsmul, map_sum (fiberSum f hf)]
  -- Strip the common ℤ-smul `D z • ·` and reduce to a sum equality.
  congr 1
  -- Goal:
  --   ∑ x ∈ (hgf z).toFinset, single x
  --     = ∑ y ∈ (hg z).toFinset, fiberSum f hf (single y)
  -- Step A: rewrite each RHS summand using `fiberSum_single`.
  -- Step B: identify the resulting double sum with the LHS via
  --         `Finset.sum_biUnion` on the disjoint decomposition
  --         `(hgf z).toFinset = (hg z).toFinset.biUnion (...)`.
  -- Disjointness of the fibre family.
  have hdisj : ((hg z).toFinset : Set Y).PairwiseDisjoint
      (fun y => (hf y).toFinset) := by
    intro y₁ _ y₂ _ hne
    -- `PairwiseDisjoint` here unfolds to `Disjoint ((hf y₁).toFinset) ((hf y₂).toFinset)`
    -- via `Function.onFun`. We prove this via `Finset.disjoint_left`.
    show Disjoint ((hf y₁).toFinset) ((hf y₂).toFinset)
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    rw [Set.Finite.mem_toFinset] at hx₁ hx₂
    -- `hx₁ : x ∈ f ⁻¹' {y₁}`, i.e. `f x = y₁`; same for `hx₂`.
    have e1 : f x = y₁ := hx₁
    have e2 : f x = y₂ := hx₂
    exact hne (e1.symm.trans e2)
  -- The finset equality `(hgf z).toFinset = (hg z).toFinset.biUnion (...)`.
  have hset_eq : (hgf z).toFinset
      = (hg z).toFinset.biUnion (fun y => (hf y).toFinset) := by
    ext x
    rw [Finset.mem_biUnion, Set.Finite.mem_toFinset]
    constructor
    · intro hx
      -- `hx : x ∈ (g ∘ f) ⁻¹' {z}`, i.e., `g (f x) = z`.
      have hgfx : g (f x) = z := hx
      refine ⟨f x, ?_, ?_⟩
      · rw [Set.Finite.mem_toFinset]
        -- Need: `f x ∈ g ⁻¹' {z}`, i.e., `g (f x) = z`.
        exact hgfx
      · rw [Set.Finite.mem_toFinset]
        -- Need: `x ∈ f ⁻¹' {f x}`, i.e., `f x = f x`.
        rfl
    · rintro ⟨y, hy, hxy⟩
      rw [Set.Finite.mem_toFinset] at hy hxy
      -- `hy : g y = z`, `hxy : f x = y`, so `g (f x) = z`.
      have e : f x = y := hxy
      show g (f x) = z
      rw [e]; exact hy
  -- Now rewrite the LHS using the biUnion decomposition.
  rw [hset_eq, Finset.sum_biUnion hdisj]
  -- Goal:
  --   ∑ y ∈ (hg z).toFinset, ∑ x ∈ (hf y).toFinset, single x
  --     = ∑ y ∈ (hg z).toFinset, fiberSum f hf (single y)
  refine Finset.sum_congr rfl ?_
  intro y _
  -- `fiberSum f hf (single y) = ∑ x ∈ (hf y).toFinset, single x`.
  exact (fiberSum_single f hf y).symm

end Div

end JacobianChallenge
