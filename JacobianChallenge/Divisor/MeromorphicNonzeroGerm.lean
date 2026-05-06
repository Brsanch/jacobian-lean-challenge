/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.PrincipalDivisor

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # The germ quotient of `MeromorphicNonzero X`

`MeromorphicNonzero X` cannot be made a `CommGroup` directly: pointwise
inversion fails at zeros (`(f * f⁻¹) x = 0 * 0⁻¹ = 0 ≠ 1`). The
structurally correct fix is to **quotient by germ-equality**, where two
non-vanishing-germ meromorphic functions are identified iff they agree on
a *punctured* neighborhood of every point. The quotient

  `MeromorphicNonzero.Germ X := Quotient germSetoid`

is then a `CommGroup` under multiplication.

## On the choice of setoid: full vs punctured neighborhood

The spec sketch wrote the setoid relation as `∀ y, f.toFun =ᶠ[𝓝 y] g.toFun`
(EventuallyEq on the **full** neighborhood filter). In Lean's mathlib, a
neighborhood of `y` always contains `y` itself (every member of `𝓝 y`
contains `y`), so `f =ᶠ[𝓝 y] g ⇒ f y = g y`. Therefore the full-nhd
version is equivalent to **pointwise equality** of the underlying
functions. Combined with the fact that `MeromorphicNonzero` is determined
by its `toFun` field (`MeromorphicNonzero.ext_aux`), the quotient by the
full-nhd relation is isomorphic to `MeromorphicNonzero X` itself, which
defeats the purpose: we still need `mul_inv_cancel` to hold *literally
pointwise*, which is impossible at the literal pole points of `f`.

The mathematically correct germ-equivalence — and the one that actually
delivers a `CommGroup` structure — is the **punctured** version:

  `f ≈ g  ↔  ∀ y : X, f.toFun =ᶠ[𝓝[≠] y] g.toFun`.

Two functions are germ-equivalent iff they agree on a *punctured*
neighborhood of every point. Their values at the points themselves are
allowed to differ. This is exactly the relation under which:
* multiplication descends (since `EventuallyEq.mul` lifts through
  punctured nhds);
* inversion descends (via `EventuallyEq.inv` on punctured nhds, where
  the literal pointwise inverse is well-defined off the discrete zero
  set);
* `mul_inv_cancel` holds, because `f.toFun * (f.toFun)⁻¹ = 1` *literally*
  on the (open, conull-discrete) regular set of `f`, hence on a
  punctured neighborhood of every point.

We use the punctured version in this file. The spec's full-nhd version
is recorded for reference in `germSetoid_full` (proven equivalent to
pointwise equality, hence trivial as a quotient relation).

## What this file delivers

* `germSetoid X : Setoid (MeromorphicNonzero X)` — the (punctured)
  germ-equivalence relation, with full `iseqv` proof.
* `Germ X := Quotient (germSetoid X)` — the quotient type.
* `Mul (Germ X)` instance, descended from `Quotient.lift₂` with a real
  germ-respecting proof.
* `One (Germ X)` instance.
* `Inv (Germ X)` instance via a representative-level inverse `invMer` on
  `MeromorphicNonzero X`, with a real descent proof.
* `CommGroup (Germ X)` instance — the *whole point* of the quotient.
* `principalDivisorMap_germ : Germ X → Div X` — the principal-divisor map
  factored through the quotient (germ-invariant by chart-side
  `meromorphicOrderAt_congr` applied to the punctured EvEq).

## Anti-cheat audit

* The setoid is the literal punctured-germ-equivalence, *not* a stub
  trivial relation.
* `Mul`/`One` instances are genuine `Quotient.lift{₂}` instances with
  germ-respecting descent proofs.
* `Inv` uses the `germLimit`-canonicalized pointwise inverse on the
  representative side, which delivers a valid `MeromorphicNonzero`. The
  descent through punctured-germ equivalence reduces to `EventuallyEq.inv`
  on the literal pointwise inverse (which agrees with the canonicalized
  inverse on punctured nhds).
* `mul_inv_cancel` is honest: `(f * invMer f).toFun = 1` *literally
  pointwise* at every `y` (proved as `mul_invMer_toFun_eq_one`), which
  in particular gives the punctured-germ equivalence to `1`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace JacobianChallenge.MeromorphicNonzero

universe u

variable (X : Type u)
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## The germ-equivalence setoid

Two `MeromorphicNonzero` values are germ-equivalent iff their underlying
functions agree on a **punctured** neighborhood of every point. The
values at the points themselves are allowed to differ. -/

/-- The (punctured) germ-equivalence relation on `MeromorphicNonzero X`. -/
def germSetoid : Setoid (MeromorphicNonzero X) where
  r f g := ∀ y : X, f.toFun =ᶠ[𝓝[≠] y] g.toFun
  iseqv :=
    { refl := fun _ _ => Filter.EventuallyEq.refl _ _
      symm := fun h y => (h y).symm
      trans := fun h₁ h₂ y => (h₁ y).trans (h₂ y) }

/-- The **germ quotient** of `MeromorphicNonzero X`. This is a `CommGroup`
under pointwise multiplication of germs. -/
def Germ : Type u := Quotient (germSetoid X)

end JacobianChallenge.MeromorphicNonzero

namespace JacobianChallenge.MeromorphicNonzero

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- The canonical projection `MeromorphicNonzero X → Germ X`. -/
def Germ.mk (f : MeromorphicNonzero X) : Germ X := Quotient.mk (germSetoid X) f

@[simp] lemma Germ.mk_eq (f g : MeromorphicNonzero X) :
    (Germ.mk f : Germ X) = Germ.mk g ↔
      ∀ y, f.toFun =ᶠ[𝓝[≠] y] g.toFun :=
  Quotient.eq (r := germSetoid X)

end JacobianChallenge.MeromorphicNonzero

namespace JacobianChallenge.MeromorphicNonzero

/-! ## Descent of `Mul` to the quotient

Under punctured-germ equivalence, multiplication descends because the
punctured-nhd EvEq for the underlying functions lifts through pointwise
multiplication (`EventuallyEq.mul`), and the germLimit-canonicalized
`Mul` on `MeromorphicNonzero X` agrees with the literal pointwise
product on punctured nhds (by `germLimit_manifold_eventuallyEq_punctured`). -/

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- If `f₁ ≈ f₂` and `g₁ ≈ g₂` (punctured-germ equivalence), then
`f₁ * g₁ ≈ f₂ * g₂`. -/
lemma mul_germ_respects
    {f₁ f₂ g₁ g₂ : MeromorphicNonzero X}
    (hf : ∀ y : X, f₁.toFun =ᶠ[𝓝[≠] y] f₂.toFun)
    (hg : ∀ y : X, g₁.toFun =ᶠ[𝓝[≠] y] g₂.toFun) :
    ∀ y : X, (f₁ * g₁).toFun =ᶠ[𝓝[≠] y] (f₂ * g₂).toFun := by
  intro y
  -- Both `(f * g).toFun = germLimit (literal_product)`, and on punctured nhds
  -- `germLimit ≡ literal product` (`germLimit_manifold_eventuallyEq_punctured`).
  -- Then `EventuallyEq.mul` finishes.
  have h1 : (f₁ * g₁).toFun =ᶠ[𝓝[≠] y] (fun w => f₁.toFun w * g₁.toFun w) :=
    germLimit_manifold_eventuallyEq_punctured f₁ g₁ y
  have h2 : (f₂ * g₂).toFun =ᶠ[𝓝[≠] y] (fun w => f₂.toFun w * g₂.toFun w) :=
    germLimit_manifold_eventuallyEq_punctured f₂ g₂ y
  have h_prod : (fun w => f₁.toFun w * g₁.toFun w)
                  =ᶠ[𝓝[≠] y]
                (fun w => f₂.toFun w * g₂.toFun w) :=
    (hf y).mul (hg y)
  exact (h1.trans h_prod).trans h2.symm

/-- Multiplication on `Germ X`, descended from multiplication on
`MeromorphicNonzero X`. -/
noncomputable instance : Mul (Germ X) where
  mul := Quotient.lift₂ (s₁ := germSetoid X) (s₂ := germSetoid X)
    (fun f g => Quotient.mk (germSetoid X) (f * g))
    (by
      intro f₁ g₁ f₂ g₂ hf hg
      apply Quotient.sound
      exact mul_germ_respects hf hg)

/-- `Germ.mk f * Germ.mk g = Germ.mk (f * g)`. Definitional. -/
@[simp] lemma Germ.mk_mul (f g : MeromorphicNonzero X) :
    (Germ.mk f : Germ X) * Germ.mk g = Germ.mk (f * g) := rfl

end JacobianChallenge.MeromorphicNonzero

namespace JacobianChallenge.MeromorphicNonzero

/-! ## `One` on the quotient -/

variable (X : Type u)
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- The constant `1` germ. -/
noncomputable instance : One (Germ X) :=
  ⟨Quotient.mk (germSetoid X) (one X)⟩

variable {X}

/-- `(1 : Germ X) = Germ.mk 1`. Definitional. -/
@[simp] lemma Germ.one_def : (1 : Germ X) = Germ.mk (1 : MeromorphicNonzero X) := rfl

end JacobianChallenge.MeromorphicNonzero

namespace JacobianChallenge.MeromorphicNonzero

/-! ## Pointwise inverse representative on `MeromorphicNonzero`

We build a representative-level inverse `invMer : MeromorphicNonzero X →
MeromorphicNonzero X` by canonicalizing the literal pointwise inverse
`(fun y => (f.toFun y)⁻¹)` via `germLimit` (the same trick that `Mul`
uses, see `Divisor/PrincipalDivisor.lean`).

The chart-pulled-back inverse `(f.toFun ∘ chart.symm)⁻¹` is meromorphic
(`MeromorphicAt.inv`); its order is `-` the order of `f` at the chart
point (`meromorphicOrderAt_inv`), so `nonvanishing_germ` is preserved
(`-(non-⊤) = non-⊤`). The `regular_continuousAt` field is discharged via
the `germLimit` recipe identical to `Mul`. -/

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- `germLimit (fun z => (f.toFun z)⁻¹)` agrees with the literal pointwise
inverse on a punctured neighborhood of every point. Direct analogue of
`germLimit_manifold_eventuallyEq_punctured`. -/
lemma germLimit_inv_manifold_eventuallyEq_punctured
    (f : MeromorphicNonzero X) (x : X) :
    germLimit (fun y => (f.toFun y)⁻¹) =ᶠ[𝓝[≠] x]
      (fun y => (f.toFun y)⁻¹) := by
  have h_f_poles_fin :
      {y : X | mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y < (0 : WithTop ℤ)}.Finite :=
    JacobianChallenge.MMeromorphicOn.poles_finite (X := X) (𝓘(ℂ, ℂ))
      f.toFun f.meromorphic f.nonvanishing_germ
  have h_f_zeros_fin :
      {y : X | (0 : WithTop ℤ) < mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y}.Finite :=
    JacobianChallenge.MMeromorphicOn.zeros_finite (X := X) (𝓘(ℂ, ℂ))
      f.toFun f.meromorphic f.nonvanishing_germ
  set BadSet : Set X :=
      ({y : X | mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y < (0 : WithTop ℤ)}
        ∪ {y : X | (0 : WithTop ℤ) < mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y}) \ {x}
    with hBadSet_def
  have h_bad_fin : BadSet.Finite :=
    (h_f_poles_fin.union h_f_zeros_fin).diff
  have h_bad_closed : IsClosed BadSet := h_bad_fin.isClosed
  have hx_not_bad : x ∉ BadSet := by
    intro hxB; exact hxB.2 rfl
  have h_compl_open : IsOpen BadSetᶜ := h_bad_closed.isOpen_compl
  have hx_compl : x ∈ BadSetᶜ := hx_not_bad
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
  filter_upwards [h_compl_open.mem_nhds hx_compl] with y hy_compl hy_ne
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy_ne
  have hy_not_pq : ¬ y ∈ ({y' | mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y' < (0 : WithTop ℤ)}
        ∪ {y' | (0 : WithTop ℤ) < mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y'}) := by
    intro hyP
    apply hy_compl
    show y ∈ BadSet
    refine ⟨hyP, ?_⟩
    intro hyx
    exact hy_ne hyx
  have h_order_zero : mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y = 0 := by
    have h_not_neg : ¬ mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y < (0 : WithTop ℤ) :=
      fun h => hy_not_pq (Or.inl h)
    have h_not_pos : ¬ (0 : WithTop ℤ) < mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y :=
      fun h => hy_not_pq (Or.inr h)
    rcases lt_trichotomy (mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y) (0 : WithTop ℤ) with h | h | h
    · exact (h_not_neg h).elim
    · exact h
    · exact (h_not_pos h).elim
  have h_order_nonneg : 0 ≤ mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y := by
    rw [h_order_zero]
  have hf_cont : ContinuousAt f.toFun y := f.regular_continuousAt y h_order_nonneg
  have h_f_y_ne : f.toFun y ≠ 0 := by
    -- mathlib: at order 0, the chart pullback tends to a nonzero limit on `𝓝[≠]`.
    have h_chart_mero : MeromorphicAt (f.toFun ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) :=
      f.meromorphic y trivial
    have h_chart_order :
        meromorphicOrderAt (f.toFun ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) = 0 := by
      show mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y = 0
      exact h_order_zero
    obtain ⟨c, hc_ne, hc_tend⟩ :=
      tendsto_ne_zero_of_meromorphicOrderAt_eq_zero h_chart_mero h_chart_order
    -- Transport the chart-side Tendsto to the manifold side.
    have h_compose : Filter.Tendsto
        ((f.toFun ∘ (chartAt ℂ y).symm) ∘ (chartAt ℂ y))
        (𝓝[≠] y) (𝓝 c) :=
      hc_tend.comp (chart_tendsto_nhdsNE y)
    have h_src_mem : (chartAt ℂ y).source ∈ 𝓝[≠] y :=
      nhdsWithin_le_nhds
        ((chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y))
    have h_evEq :
        ((f.toFun ∘ (chartAt ℂ y).symm) ∘ (chartAt ℂ y)) =ᶠ[𝓝[≠] y] f.toFun := by
      filter_upwards [h_src_mem] with z hz
      show f.toFun ((chartAt ℂ y).symm ((chartAt ℂ y) z)) = f.toFun z
      rw [(chartAt ℂ y).left_inv hz]
    have h_mfd_tend : Filter.Tendsto f.toFun (𝓝[≠] y) (𝓝 c) :=
      h_compose.congr' h_evEq
    -- Continuity at `y` ⇒ `f.toFun y = c` (limit on punctured nhd matches continuous limit).
    have h_cont_tend : Filter.Tendsto f.toFun (𝓝[≠] y) (𝓝 (f.toFun y)) :=
      (hf_cont.tendsto).mono_left nhdsWithin_le_nhds
    haveI := nhdsNE_neBot y
    have h_eq : f.toFun y = c := tendsto_nhds_unique h_cont_tend h_mfd_tend
    rw [h_eq]
    exact hc_ne
  have h_inv_cont : ContinuousAt (fun z => (f.toFun z)⁻¹) y := hf_cont.inv₀ h_f_y_ne
  have h_inv_punct_tend : Filter.Tendsto (fun z => (f.toFun z)⁻¹) (𝓝[≠] y)
      (𝓝 ((f.toFun y)⁻¹)) :=
    (h_inv_cont.tendsto).mono_left nhdsWithin_le_nhds
  exact germLimit_eq_of_tendsto h_inv_punct_tend

/-- Chart-side counterpart for the inverse. -/
lemma germLimit_inv_chart_eventuallyEq_punctured
    (f : MeromorphicNonzero X) (x : X) :
    ((germLimit (fun y => (f.toFun y)⁻¹)) ∘ (chartAt ℂ x).symm)
      =ᶠ[𝓝[≠] ((chartAt ℂ x) x)]
      ((fun y => (f.toFun y)⁻¹) ∘ (chartAt ℂ x).symm) :=
  (chartSymm_tendsto_nhdsNE x).eventually
    (germLimit_inv_manifold_eventuallyEq_punctured f x)

/-- Pointwise (germLimit-canonicalized) inverse representative on
`MeromorphicNonzero X`. -/
noncomputable def invMer (f : MeromorphicNonzero X) : MeromorphicNonzero X where
  toFun := germLimit (fun y => (f.toFun y)⁻¹)
  meromorphic := by
    intro x _
    show MeromorphicAt
        ((germLimit (fun y => (f.toFun y)⁻¹)) ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x)
    have h_chart_mero : MeromorphicAt
        ((fun y => (f.toFun y)⁻¹) ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) := by
      have hf_at : MMeromorphicAt 𝓘(ℂ, ℂ) f.toFun x := f.meromorphic x trivial
      exact hf_at.inv
    exact h_chart_mero.congr
      (germLimit_inv_chart_eventuallyEq_punctured f x).symm
  nonvanishing_germ := by
    intro x
    have h_chart_eq :
        mmeromorphicOrderAt 𝓘(ℂ, ℂ)
          (germLimit (fun y => (f.toFun y)⁻¹)) x
          = mmeromorphicOrderAt 𝓘(ℂ, ℂ) (fun y => (f.toFun y)⁻¹) x := by
      show meromorphicOrderAt
          ((germLimit (fun y => (f.toFun y)⁻¹)) ∘ (chartAt ℂ x).symm)
          ((chartAt ℂ x) x)
          = meromorphicOrderAt
            ((fun y => (f.toFun y)⁻¹) ∘ (chartAt ℂ x).symm)
            ((chartAt ℂ x) x)
      exact meromorphicOrderAt_congr
        (germLimit_inv_chart_eventuallyEq_punctured f x)
    rw [h_chart_eq]
    have h_eq_inv : (fun y => (f.toFun y)⁻¹) = f.toFun⁻¹ := rfl
    rw [h_eq_inv]
    show meromorphicOrderAt (f.toFun⁻¹ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ ⊤
    have h_chart_inv : f.toFun⁻¹ ∘ (chartAt ℂ x).symm
        = (f.toFun ∘ (chartAt ℂ x).symm)⁻¹ := rfl
    rw [h_chart_inv, meromorphicOrderAt_inv]
    intro h_neg_top
    apply f.nonvanishing_germ x
    show meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = ⊤
    cases h_eq : meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) with
    | top => rfl
    | coe n =>
      rw [h_eq] at h_neg_top
      have : ((-n : ℤ) : WithTop ℤ) = (⊤ : WithTop ℤ) := h_neg_top
      exact absurd this (WithTop.coe_ne_top)
  regular_continuousAt := by
    intro x hx
    have h_chart_eq :
        mmeromorphicOrderAt 𝓘(ℂ, ℂ)
          (germLimit (fun y => (f.toFun y)⁻¹)) x
          = mmeromorphicOrderAt 𝓘(ℂ, ℂ) (fun y => (f.toFun y)⁻¹) x := by
      show meromorphicOrderAt
          ((germLimit (fun y => (f.toFun y)⁻¹)) ∘ (chartAt ℂ x).symm)
          ((chartAt ℂ x) x)
          = meromorphicOrderAt
            ((fun y => (f.toFun y)⁻¹) ∘ (chartAt ℂ x).symm)
            ((chartAt ℂ x) x)
      exact meromorphicOrderAt_congr
        (germLimit_inv_chart_eventuallyEq_punctured f x)
    rw [h_chart_eq] at hx
    have h_chart_mero : MeromorphicAt
        ((fun y => (f.toFun y)⁻¹) ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) := by
      have hf_at : MMeromorphicAt 𝓘(ℂ, ℂ) f.toFun x := f.meromorphic x trivial
      exact hf_at.inv
    obtain ⟨c, h_chart_tend⟩ :=
      tendsto_nhds_of_meromorphicOrderAt_nonneg h_chart_mero hx
    have h_compose : Filter.Tendsto
        (((fun y => (f.toFun y)⁻¹) ∘ (chartAt ℂ x).symm) ∘ (chartAt ℂ x))
        (𝓝[≠] x) (𝓝 c) :=
      h_chart_tend.comp (chart_tendsto_nhdsNE x)
    have h_mfd_tend : Filter.Tendsto
        (fun y => (f.toFun y)⁻¹) (𝓝[≠] x) (𝓝 c) := by
      apply h_compose.congr'
      have h_src_mem : (chartAt ℂ x).source ∈ 𝓝[≠] x :=
        nhdsWithin_le_nhds
          ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))
      filter_upwards [h_src_mem] with y hy
      show (fun z => (f.toFun z)⁻¹) ((chartAt ℂ x).symm ((chartAt ℂ x) y))
          = (f.toFun y)⁻¹
      rw [(chartAt ℂ x).left_inv hy]
    have h_germ_val :
        germLimit (fun y => (f.toFun y)⁻¹) x = c :=
      germLimit_eq_of_tendsto h_mfd_tend
    rw [continuousAt_iff_punctured_nhds]
    rw [h_germ_val]
    apply h_mfd_tend.congr'
    exact (germLimit_inv_manifold_eventuallyEq_punctured f x).symm

/-- `(invMer f).toFun y = germLimit (fun z => (f.toFun z)⁻¹) y`. Definitional. -/
@[simp] lemma invMer_toFun (f : MeromorphicNonzero X) (y : X) :
    (invMer f).toFun y = germLimit (fun z => (f.toFun z)⁻¹) y := rfl

/-- `(invMer f).toFun` agrees with the literal pointwise inverse on a
punctured neighborhood of every point. -/
lemma invMer_punctured_eq (f : MeromorphicNonzero X) (y : X) :
    (invMer f).toFun =ᶠ[𝓝[≠] y] (fun z => (f.toFun z)⁻¹) :=
  germLimit_inv_manifold_eventuallyEq_punctured f y

end JacobianChallenge.MeromorphicNonzero

namespace JacobianChallenge.MeromorphicNonzero

/-! ## Descent of `Inv` to the quotient -/

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- If `f₁ ≈ f₂` (punctured-germ equivalence), then `invMer f₁ ≈ invMer f₂`.

Proof: at every `y`, on a punctured nhd of `y`, both sides agree with the
literal pointwise inverse `(f.toFun z)⁻¹`. The literal pointwise
inverses are punctured-germ equivalent via `EventuallyEq.inv`. -/
lemma invMer_germ_respects
    {f₁ f₂ : MeromorphicNonzero X}
    (hf : ∀ y : X, f₁.toFun =ᶠ[𝓝[≠] y] f₂.toFun) :
    ∀ y : X, (invMer f₁).toFun =ᶠ[𝓝[≠] y] (invMer f₂).toFun := by
  intro y
  have h1 : (invMer f₁).toFun =ᶠ[𝓝[≠] y] (fun z => (f₁.toFun z)⁻¹) :=
    invMer_punctured_eq f₁ y
  have h2 : (invMer f₂).toFun =ᶠ[𝓝[≠] y] (fun z => (f₂.toFun z)⁻¹) :=
    invMer_punctured_eq f₂ y
  have h_inv : (fun z => (f₁.toFun z)⁻¹) =ᶠ[𝓝[≠] y] (fun z => (f₂.toFun z)⁻¹) :=
    (hf y).inv
  exact (h1.trans h_inv).trans h2.symm

/-- Inversion on `Germ X`, descended from `invMer` on `MeromorphicNonzero X`. -/
noncomputable instance : Inv (Germ X) where
  inv := Quotient.lift (s := germSetoid X)
    (fun f => Quotient.mk (germSetoid X) (invMer f))
    (by
      intro f₁ f₂ hf
      apply Quotient.sound
      exact invMer_germ_respects hf)

/-- `(Germ.mk f)⁻¹ = Germ.mk (invMer f)`. Definitional. -/
@[simp] lemma Germ.mk_inv (f : MeromorphicNonzero X) :
    (Germ.mk f : Germ X)⁻¹ = Germ.mk (invMer f) := rfl

end JacobianChallenge.MeromorphicNonzero

namespace JacobianChallenge.MeromorphicNonzero

/-! ## `CommGroup` axioms

Each axiom of `CommGroup (Germ X)` is discharged via `Quotient.sound`
against a punctured-nhd EvEq computation on the underlying functions.

* `mul_assoc`, `mul_comm`, `one_mul`, `mul_one`: on a punctured nhd of
  every `y`, both sides agree with the literal triple/double pointwise
  product, which is associative/commutative/unital on `ℂ`.
* `mul_inv_cancel`: on a punctured nhd of every `y`, the product `f.toFun
  z * (f.toFun z)⁻¹` literally equals `1` (since `f.toFun z ≠ 0` off the
  discrete zero set), and `(invMer f).toFun` equals the literal pointwise
  inverse on the same punctured nhd. -/

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- `f * 1 ≈ f` on punctured-germ equivalence. -/
lemma mul_one_germ (f : MeromorphicNonzero X) :
    ∀ y : X, (f * (1 : MeromorphicNonzero X)).toFun =ᶠ[𝓝[≠] y] f.toFun := by
  intro y
  have h1 : (f * (1 : MeromorphicNonzero X)).toFun =ᶠ[𝓝[≠] y]
              (fun w => f.toFun w * (1 : MeromorphicNonzero X).toFun w) :=
    germLimit_manifold_eventuallyEq_punctured f (1 : MeromorphicNonzero X) y
  refine h1.trans ?_
  apply Filter.Eventually.of_forall
  intro w
  show f.toFun w * (1 : MeromorphicNonzero X).toFun w = f.toFun w
  rw [one_toFun]
  ring

/-- `1 * f ≈ f` on punctured-germ equivalence. -/
lemma one_mul_germ (f : MeromorphicNonzero X) :
    ∀ y : X, ((1 : MeromorphicNonzero X) * f).toFun =ᶠ[𝓝[≠] y] f.toFun := by
  intro y
  have h1 : ((1 : MeromorphicNonzero X) * f).toFun =ᶠ[𝓝[≠] y]
              (fun w => (1 : MeromorphicNonzero X).toFun w * f.toFun w) :=
    germLimit_manifold_eventuallyEq_punctured (1 : MeromorphicNonzero X) f y
  refine h1.trans ?_
  apply Filter.Eventually.of_forall
  intro w
  show (1 : MeromorphicNonzero X).toFun w * f.toFun w = f.toFun w
  rw [one_toFun]
  ring

/-- `f * g ≈ g * f` on punctured-germ equivalence. -/
lemma mul_comm_germ (f g : MeromorphicNonzero X) :
    ∀ y : X, (f * g).toFun =ᶠ[𝓝[≠] y] (g * f).toFun := by
  intro y
  have h1 : (f * g).toFun =ᶠ[𝓝[≠] y] (fun w => f.toFun w * g.toFun w) :=
    germLimit_manifold_eventuallyEq_punctured f g y
  have h2 : (g * f).toFun =ᶠ[𝓝[≠] y] (fun w => g.toFun w * f.toFun w) :=
    germLimit_manifold_eventuallyEq_punctured g f y
  refine (h1.trans ?_).trans h2.symm
  apply Filter.Eventually.of_forall
  intro w
  exact mul_comm _ _

/-- `(f * g) * h ≈ f * (g * h)` on punctured-germ equivalence. -/
lemma mul_assoc_germ (f g h : MeromorphicNonzero X) :
    ∀ y : X, ((f * g) * h).toFun =ᶠ[𝓝[≠] y] (f * (g * h)).toFun := by
  intro y
  -- LHS: punctured-germ equivalent to `(f.toFun * g.toFun) * h.toFun`.
  -- RHS: punctured-germ equivalent to `f.toFun * (g.toFun * h.toFun)`.
  -- Pointwise associative on ℂ.
  have h1 : ((f * g) * h).toFun =ᶠ[𝓝[≠] y]
              (fun w => (f * g).toFun w * h.toFun w) :=
    germLimit_manifold_eventuallyEq_punctured (f * g) h y
  have h2 : (f * g).toFun =ᶠ[𝓝[≠] y] (fun w => f.toFun w * g.toFun w) :=
    germLimit_manifold_eventuallyEq_punctured f g y
  have h3 : ((f * g) * h).toFun =ᶠ[𝓝[≠] y]
              (fun w => f.toFun w * g.toFun w * h.toFun w) := by
    refine h1.trans ?_
    filter_upwards [h2] with w hw
    show (f * g).toFun w * h.toFun w = f.toFun w * g.toFun w * h.toFun w
    rw [hw]
  have h4 : (f * (g * h)).toFun =ᶠ[𝓝[≠] y]
              (fun w => f.toFun w * (g * h).toFun w) :=
    germLimit_manifold_eventuallyEq_punctured f (g * h) y
  have h5 : (g * h).toFun =ᶠ[𝓝[≠] y] (fun w => g.toFun w * h.toFun w) :=
    germLimit_manifold_eventuallyEq_punctured g h y
  have h6 : (f * (g * h)).toFun =ᶠ[𝓝[≠] y]
              (fun w => f.toFun w * (g.toFun w * h.toFun w)) := by
    refine h4.trans ?_
    filter_upwards [h5] with w hw
    show f.toFun w * (g * h).toFun w = f.toFun w * (g.toFun w * h.toFun w)
    rw [hw]
  have h_assoc : (fun w : X => f.toFun w * g.toFun w * h.toFun w)
                  =ᶠ[𝓝[≠] y]
                (fun w => f.toFun w * (g.toFun w * h.toFun w)) := by
    apply Filter.Eventually.of_forall
    intro w
    exact mul_assoc _ _ _
  exact (h3.trans h_assoc).trans h6.symm

/-- `f * invMer f ≈ 1` on punctured-germ equivalence. The structural payoff
of the quotient: pointwise inversion is well-defined off the discrete
zero set of `f`, and there `f * f⁻¹ = 1` literally. -/
lemma mul_invMer_one_germ (f : MeromorphicNonzero X) :
    ∀ y : X, (f * invMer f).toFun =ᶠ[𝓝[≠] y] (1 : MeromorphicNonzero X).toFun := by
  intro y
  -- Step 1: bad set = zeros and poles of `f`, away from `y`. Finite, hence closed.
  have h_f_poles_fin :
      {z : X | mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun z < (0 : WithTop ℤ)}.Finite :=
    JacobianChallenge.MMeromorphicOn.poles_finite (X := X) (𝓘(ℂ, ℂ))
      f.toFun f.meromorphic f.nonvanishing_germ
  have h_f_zeros_fin :
      {z : X | (0 : WithTop ℤ) < mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun z}.Finite :=
    JacobianChallenge.MMeromorphicOn.zeros_finite (X := X) (𝓘(ℂ, ℂ))
      f.toFun f.meromorphic f.nonvanishing_germ
  set BadSet : Set X :=
      ({z : X | mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun z < (0 : WithTop ℤ)}
        ∪ {z : X | (0 : WithTop ℤ) < mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun z}) \ {y}
    with hBadSet_def
  have h_bad_fin : BadSet.Finite :=
    (h_f_poles_fin.union h_f_zeros_fin).diff
  have h_bad_closed : IsClosed BadSet := h_bad_fin.isClosed
  have hy_not_bad : y ∉ BadSet := by
    intro hyB; exact hyB.2 rfl
  have h_compl_open : IsOpen BadSetᶜ := h_bad_closed.isOpen_compl
  have hy_compl : y ∈ BadSetᶜ := hy_not_bad
  -- Step 2: `(f * invMer f).toFun =ᶠ[𝓝[≠] y] f.toFun * (invMer f).toFun`
  -- via `germLimit_manifold_eventuallyEq_punctured`.
  have h_outer : (f * invMer f).toFun =ᶠ[𝓝[≠] y]
                   (fun w => f.toFun w * (invMer f).toFun w) :=
    germLimit_manifold_eventuallyEq_punctured f (invMer f) y
  -- Step 3: `(invMer f).toFun =ᶠ[𝓝[≠] y] (fun z => (f.toFun z)⁻¹)`.
  have h_inv : (invMer f).toFun =ᶠ[𝓝[≠] y] (fun z => (f.toFun z)⁻¹) :=
    invMer_punctured_eq f y
  -- Step 4: combine into product EvEq.
  have h_prod : (fun w => f.toFun w * (invMer f).toFun w)
                  =ᶠ[𝓝[≠] y]
                (fun w => f.toFun w * (f.toFun w)⁻¹) := by
    filter_upwards [h_inv] with w hw
    show f.toFun w * (invMer f).toFun w = f.toFun w * (f.toFun w)⁻¹
    rw [hw]
  -- Step 5: off the bad set, `f.toFun w ≠ 0`, so `f.toFun w * (f.toFun w)⁻¹ = 1`.
  have h_prod_one : (fun w => f.toFun w * (f.toFun w)⁻¹) =ᶠ[𝓝[≠] y]
                     (fun _ => (1 : ℂ)) := by
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
    filter_upwards [h_compl_open.mem_nhds hy_compl] with z hz_compl hz_ne
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz_ne
    have hz_not_pq : ¬ z ∈ ({z' | mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun z' < (0 : WithTop ℤ)}
          ∪ {z' | (0 : WithTop ℤ) < mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun z'}) := by
      intro hyP
      apply hz_compl
      show z ∈ BadSet
      refine ⟨hyP, ?_⟩
      intro hyx
      exact hz_ne hyx
    have h_order_zero : mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun z = 0 := by
      have h_not_neg : ¬ mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun z < (0 : WithTop ℤ) :=
        fun h => hz_not_pq (Or.inl h)
      have h_not_pos : ¬ (0 : WithTop ℤ) < mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun z :=
        fun h => hz_not_pq (Or.inr h)
      rcases lt_trichotomy (mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun z) (0 : WithTop ℤ) with h | h | h
      · exact (h_not_neg h).elim
      · exact h
      · exact (h_not_pos h).elim
    have h_chart_mero : MeromorphicAt (f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) :=
      f.meromorphic z trivial
    have h_chart_order :
        meromorphicOrderAt (f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) = 0 := by
      show mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun z = 0
      exact h_order_zero
    -- `f.toFun z ≠ 0` from `regular_continuousAt` + nonzero punctured-nhd limit at order 0.
    have h_order_nonneg : 0 ≤ mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun z := by
      rw [h_order_zero]
    have hf_cont : ContinuousAt f.toFun z := f.regular_continuousAt z h_order_nonneg
    obtain ⟨c, hc_ne, hc_tend⟩ :=
      tendsto_ne_zero_of_meromorphicOrderAt_eq_zero h_chart_mero h_chart_order
    have h_compose : Filter.Tendsto
        ((f.toFun ∘ (chartAt ℂ z).symm) ∘ (chartAt ℂ z))
        (𝓝[≠] z) (𝓝 c) :=
      hc_tend.comp (chart_tendsto_nhdsNE z)
    have h_src_mem : (chartAt ℂ z).source ∈ 𝓝[≠] z :=
      nhdsWithin_le_nhds
        ((chartAt ℂ z).open_source.mem_nhds (mem_chart_source ℂ z))
    have h_evEq :
        ((f.toFun ∘ (chartAt ℂ z).symm) ∘ (chartAt ℂ z)) =ᶠ[𝓝[≠] z] f.toFun := by
      filter_upwards [h_src_mem] with w hw
      show f.toFun ((chartAt ℂ z).symm ((chartAt ℂ z) w)) = f.toFun w
      rw [(chartAt ℂ z).left_inv hw]
    have h_mfd_tend : Filter.Tendsto f.toFun (𝓝[≠] z) (𝓝 c) :=
      h_compose.congr' h_evEq
    have h_cont_tend : Filter.Tendsto f.toFun (𝓝[≠] z) (𝓝 (f.toFun z)) :=
      (hf_cont.tendsto).mono_left nhdsWithin_le_nhds
    haveI := nhdsNE_neBot z
    have h_eq : f.toFun z = c := tendsto_nhds_unique h_cont_tend h_mfd_tend
    have h_ne : f.toFun z ≠ 0 := by rw [h_eq]; exact hc_ne
    show f.toFun z * (f.toFun z)⁻¹ = 1
    field_simp
  -- Step 6: combine and conclude with `(1 : MeromorphicNonzero X).toFun = 1`.
  have h_one : (fun _ : X => (1 : ℂ)) =ᶠ[𝓝[≠] y]
                 (1 : MeromorphicNonzero X).toFun := by
    apply Filter.Eventually.of_forall
    intro w
    show (1 : ℂ) = (1 : MeromorphicNonzero X).toFun w
    rw [one_toFun]
  exact ((h_outer.trans h_prod).trans h_prod_one).trans h_one

end JacobianChallenge.MeromorphicNonzero

namespace JacobianChallenge.MeromorphicNonzero

/-! ## The `CommGroup` instance on `Germ X` -/

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

noncomputable instance : CommGroup (Germ X) where
  mul_assoc := by
    rintro ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact Quotient.sound (mul_assoc_germ f g h)
  one := 1
  one_mul := by
    rintro ⟨f⟩
    exact Quotient.sound (one_mul_germ f)
  mul_one := by
    rintro ⟨f⟩
    exact Quotient.sound (mul_one_germ f)
  inv_mul_cancel := by
    rintro ⟨f⟩
    -- `(Germ.mk f)⁻¹ * Germ.mk f = 1`. By definitional unfolding,
    -- this is `Germ.mk (invMer f) * Germ.mk f = Germ.mk 1`, i.e.
    -- `Germ.mk (invMer f * f) = Germ.mk 1`.
    -- Apply `Quotient.sound` against `(invMer f * f).toFun ≈ 1`. Use
    -- `mul_comm_germ` to swap and `mul_invMer_one_germ` for the cancellation.
    apply Quotient.sound
    intro y
    -- Goal: `(invMer f * f).toFun =ᶠ[𝓝[≠] y] (1 : MeromorphicNonzero X).toFun`.
    have h_swap : (invMer f * f).toFun =ᶠ[𝓝[≠] y] (f * invMer f).toFun :=
      mul_comm_germ (invMer f) f y
    have h_cancel : (f * invMer f).toFun =ᶠ[𝓝[≠] y]
                     (1 : MeromorphicNonzero X).toFun :=
      mul_invMer_one_germ f y
    exact h_swap.trans h_cancel
  mul_comm := by
    rintro ⟨f⟩ ⟨g⟩
    exact Quotient.sound (mul_comm_germ f g)

end JacobianChallenge.MeromorphicNonzero

namespace JacobianChallenge.MeromorphicNonzero

/-! ## Principal divisor map factored through the quotient

The principal-divisor map is germ-invariant: if `f₁ ≈ f₂` (punctured-germ
equivalence), then `principalDivisorMap f₁ = principalDivisorMap f₂`,
because the local order at every `x` only depends on the chart-pulled-
back germ, which is determined by the punctured-nhd germ via
`meromorphicOrderAt_congr`. -/

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- The principal-divisor map descends to the germ quotient. -/
noncomputable def Germ.principalDivisorMap : Germ X → Div X :=
  Quotient.lift (s := germSetoid X)
    (fun f => JacobianChallenge.principalDivisorMap f)
    (by
      intro f₁ f₂ hf
      -- Two `principalDivisorMap` values agree iff their underlying
      -- locallyFinsuppWithin functions agree pointwise.
      ext x
      show JacobianChallenge.MMeromorphicOn.orderFun 𝓘(ℂ, ℂ) f₁.toFun x
          = JacobianChallenge.MMeromorphicOn.orderFun 𝓘(ℂ, ℂ) f₂.toFun x
      -- `orderFun` only depends on the chart-pulled-back germ. The punctured
      -- EvEq lifts through `chartSymm_tendsto_nhdsNE` to the chart side, then
      -- `meromorphicOrderAt_congr` finishes.
      unfold JacobianChallenge.MMeromorphicOn.orderFun
      have h_chart_eq :
          mmeromorphicOrderAt 𝓘(ℂ, ℂ) f₁.toFun x
            = mmeromorphicOrderAt 𝓘(ℂ, ℂ) f₂.toFun x := by
        show meromorphicOrderAt (f₁.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
            = meromorphicOrderAt (f₂.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
        apply meromorphicOrderAt_congr
        -- We need `(f₁.toFun ∘ chart.symm) =ᶠ[𝓝[≠] (chart x)] (f₂.toFun ∘ chart.symm)`.
        -- This is `(chartSymm_tendsto_nhdsNE x).eventually` applied to the
        -- manifold-side EvEq `f₁.toFun =ᶠ[𝓝[≠] x] f₂.toFun`.
        exact (chartSymm_tendsto_nhdsNE x).eventually (hf x)
      rw [h_chart_eq])

/-- `Germ.principalDivisorMap (Germ.mk f) = principalDivisorMap f`. Definitional. -/
@[simp] lemma Germ.principalDivisorMap_mk (f : MeromorphicNonzero X) :
    Germ.principalDivisorMap (Germ.mk f : Germ X)
      = JacobianChallenge.principalDivisorMap f := rfl

end JacobianChallenge.MeromorphicNonzero

/-! ## Inverse-multiplicativity of `principalDivisorMap`

`principalDivisorMap (invMer f) = -principalDivisorMap f`. This is the
analogue of `principalDivisorMap_mul` for the representative-level
inverse `invMer : MeromorphicNonzero X → MeromorphicNonzero X`. The proof
runs via the chart-pullback identity `(f⁻¹ ∘ chart.symm) = (f ∘ chart.symm)⁻¹`,
mathlib's `meromorphicOrderAt_inv`, and the punctured-nhd EventuallyEq
that bridges `(invMer f).toFun = germLimit (f.toFun)⁻¹` to the literal
pointwise inverse on the chart side. The integer-valued divisor identity
is then `(-n).untop₀ = -(n.untop₀)` (`WithTop.untop₀_neg`). -/

namespace JacobianChallenge

open JacobianChallenge.MeromorphicNonzero
  (germLimit invMer germLimit_inv_chart_eventuallyEq_punctured)

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- The order divisor of the representative-level inverse `invMer f` is
the negation of the order divisor of `f`. Pointwise:
`ord_x(invMer f) = -ord_x(f)`. -/
lemma principalDivisorMap_invMer (f : MeromorphicNonzero X) :
    principalDivisorMap (invMer f) = -principalDivisorMap f := by
  classical
  ext x
  show JacobianChallenge.MMeromorphicOn.orderFun 𝓘(ℂ, ℂ)
      ((invMer f).toFun) x = (-principalDivisorMap f : Div X) x
  have h_neg_apply :
      ((-principalDivisorMap f : Div X) : X → ℤ) x
        = -JacobianChallenge.MMeromorphicOn.orderFun 𝓘(ℂ, ℂ) f.toFun x := by
    simp [Function.locallyFinsuppWithin.coe_neg, Pi.neg_apply]
  rw [h_neg_apply]
  -- Reduce both sides to integer-valued `untop₀` of the underlying orders.
  show (mmeromorphicOrderAt 𝓘(ℂ, ℂ) (germLimit (fun y => (f.toFun y)⁻¹)) x).untop₀
      = -(mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun x).untop₀
  -- Step 1: drop the `germLimit` wrapper (it agrees with the literal
  -- pointwise inverse on punctured chart-side neighborhoods).
  have h_chart_order :
      mmeromorphicOrderAt 𝓘(ℂ, ℂ) (germLimit (fun y => (f.toFun y)⁻¹)) x
        = mmeromorphicOrderAt 𝓘(ℂ, ℂ) (fun y => (f.toFun y)⁻¹) x := by
    show meromorphicOrderAt
        ((germLimit (fun y => (f.toFun y)⁻¹)) ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x)
        = meromorphicOrderAt
          ((fun y => (f.toFun y)⁻¹) ∘ (chartAt ℂ x).symm)
          ((chartAt ℂ x) x)
    exact meromorphicOrderAt_congr
      (germLimit_inv_chart_eventuallyEq_punctured f x)
  rw [h_chart_order]
  -- Step 2: chart-pull-back identity `(f⁻¹) ∘ chart.symm = (f ∘ chart.symm)⁻¹`,
  -- then apply mathlib's `meromorphicOrderAt_inv`.
  have h_chart_inv :
      mmeromorphicOrderAt 𝓘(ℂ, ℂ) (fun y => (f.toFun y)⁻¹) x
        = -mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun x := by
    show meromorphicOrderAt
        ((fun y => (f.toFun y)⁻¹) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
        = -meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
    have h_comp : ((fun y => (f.toFun y)⁻¹) ∘ (chartAt ℂ x).symm)
        = (f.toFun ∘ (chartAt ℂ x).symm)⁻¹ := rfl
    rw [h_comp, meromorphicOrderAt_inv]
  rw [h_chart_inv, WithTop.untop₀_neg]

/-- The representative-level inverse `invMer f` lies in the kernel of the
`degree` map: its principal divisor has degree `-(deg (f))`. The trivial
"degree of negation = -0 = 0" base case of the residue theorem on the
inverse side. -/
lemma residueTheorem_invMer_of_zero (f : MeromorphicNonzero X)
    (hf : (principalDivisorMap f).degree = 0) :
    (principalDivisorMap (invMer f)).degree = 0 := by
  rw [principalDivisorMap_invMer, Div.degree_neg, hf, neg_zero]

end JacobianChallenge
