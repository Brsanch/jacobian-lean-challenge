/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LinearSystemGermDeltaP
import JacobianChallenge.Divisor.Single

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `linearSystemDivisor` — `L(D)` on the germ field for arbitrary divisors

This file generalises `linearSystemGermDeltaP` from the single-pole divisor
`D = δp` to an arbitrary divisor `D : Div X`. The honest Riemann–Roch
ambient is `MeromorphicFunctionGerm X`, the punctured-germ quotient of
globally meromorphic functions (`MMer X`) built in
`Manifold/MeromorphicFunctionField.lean`. Membership in `L(D)` is the
divisor-bound condition

  `∀ y : X, ord_y φ ≥ -D(y)`

on the lifted germ-level order
`MeromorphicFunctionGerm.orderAt y : MeromorphicFunctionGerm X → WithTop ℤ`
defined in `Topology/LinearSystemGermDeltaP.lean`. Closure under
addition follows from mathlib's `meromorphicOrderAt_add`
(`min(ord f) (ord g) ≤ ord(f+g)`) applied to the chart pullback; closure
under ℂ-scalar action uses `meromorphicOrderAt_smul` plus
`meromorphicOrderAt_const`.

The principal application is the genus-zero Riemann–Roch dimension count:
the architectural ambient for `dim_ℂ L(D) ≥ ...` is now a `Submodule ℂ`
of the germ field, which is honest (the pointwise "blip" pathology of
`Topology/LinearSystemDeltaP.lean` is dead in the germ quotient — see
`OPEN.md` *Architectural issue: RR-thread linear system*).

## Contents

* `IsBoundedByDivisor D φ` — the membership predicate.
* `IsBoundedByDivisor_mk_iff` — representative-level rewrite.
* `IsBoundedByDivisor.{zero, add, smul}` — closure lemmas.
* `linearSystemDivisor D : Submodule ℂ (MeromorphicFunctionGerm X)` — the
  packaged subspace.
* `mem_linearSystemDivisor` — membership in `linearSystemDivisor`.
* `IsBoundedByDivisor_zero_iff` — for `D = 0`, membership says "globally
  holomorphic germ".
* `IsBoundedByDivisor_single_iff` / `linearSystemDivisor_single_eq` —
  specialisation `D = Div.single p` recovers `linearSystemGermDeltaP p`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace JacobianChallenge.MeromorphicFunctionField

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## `IsBoundedByDivisor` predicate -/

/-- A meromorphic-function germ `φ` is **bounded by the divisor `D`** iff
`ord_y φ ≥ -D(y)` for every point `y : X`. -/
def IsBoundedByDivisor
    (D : JacobianChallenge.Div X) (φ : MeromorphicFunctionGerm X) : Prop :=
  ∀ y : X, ((-(D y) : ℤ) : WithTop ℤ) ≤ φ.orderAt y

/-- Representative-level rewrite. -/
lemma IsBoundedByDivisor_mk_iff
    (D : JacobianChallenge.Div X) (f : MMer X) :
    IsBoundedByDivisor D (MeromorphicFunctionGerm.mk f) ↔
      ∀ y : X, ((-(D y) : ℤ) : WithTop ℤ)
                ≤ mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y := Iff.rfl

/-! ## Closure under zero -/

/-- `0 ∈ L(D)` on the germ side: the zero germ has order `⊤` everywhere
(its chart pullback is `0 : ℂ → ℂ`, with `meromorphicOrderAt _ 0 = ⊤`). -/
lemma IsBoundedByDivisor.zero (D : JacobianChallenge.Div X) :
    IsBoundedByDivisor D (0 : MeromorphicFunctionGerm X) := by
  intro y
  -- Reduce to the chart pullback of the zero function.
  show ((-(D y) : ℤ) : WithTop ℤ)
        ≤ MeromorphicFunctionGerm.orderAt y (0 : MeromorphicFunctionGerm X)
  show ((-(D y) : ℤ) : WithTop ℤ)
        ≤ MeromorphicFunctionGerm.orderAt y
            (MeromorphicFunctionGerm.mk (0 : MMer X))
  rw [MeromorphicFunctionGerm.orderAt_mk]
  -- `(0 : MMer X).toFun ∘ (chartAt ℂ y).symm = (fun _ => 0)`.
  show ((-(D y) : ℤ) : WithTop ℤ)
        ≤ meromorphicOrderAt
            ((0 : MMer X).toFun ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y)
  have h_zero_comp :
      ((0 : MMer X).toFun ∘ (chartAt ℂ y).symm) = (fun _ : ℂ => (0 : ℂ)) := rfl
  rw [h_zero_comp, meromorphicOrderAt_const ((chartAt ℂ y) y) (0 : ℂ)]
  -- `if 0 = 0 then ⊤ else 0` reduces to `⊤`, and `⊤` dominates everything.
  simp

/-! ## Closure under addition

Reduce to representatives, then use `meromorphicOrderAt_add` on the
chart pullback. -/

/-- Sum closure on the germ side. -/
lemma IsBoundedByDivisor.add
    {D : JacobianChallenge.Div X} {φ ψ : MeromorphicFunctionGerm X}
    (hφ : IsBoundedByDivisor D φ) (hψ : IsBoundedByDivisor D ψ) :
    IsBoundedByDivisor D (φ + ψ) := by
  rcases φ with ⟨f⟩
  rcases ψ with ⟨g⟩
  -- `Quot.mk _ f = MeromorphicFunctionGerm.mk f` definitionally; the
  -- bound hypotheses `hφ y, hψ y` are already in chart-pullback form modulo
  -- the simp-lemma `orderAt_mk` (which is `rfl`).
  intro y
  -- Goal: `-D y ≤ (mk f + mk g).orderAt y`.
  show ((-(D y) : ℤ) : WithTop ℤ)
        ≤ MeromorphicFunctionGerm.orderAt y
            (MeromorphicFunctionGerm.mk f + MeromorphicFunctionGerm.mk g)
  rw [MeromorphicFunctionGerm.mk_add, MeromorphicFunctionGerm.orderAt_mk]
  -- `(f + g).toFun = f.toFun + g.toFun` definitionally.
  have h_unfold_toFun : (f + g).toFun = f.toFun + g.toFun := rfl
  rw [h_unfold_toFun]
  -- Drop to the chart pullback.
  show ((-(D y) : ℤ) : WithTop ℤ)
        ≤ meromorphicOrderAt
            ((f.toFun + g.toFun) ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y)
  have h_chart_unfold :
      (f.toFun + g.toFun) ∘ (chartAt ℂ y).symm
        = (f.toFun ∘ (chartAt ℂ y).symm)
            + (g.toFun ∘ (chartAt ℂ y).symm) := rfl
  rw [h_chart_unfold]
  -- Lemma: `min (ord f) (ord g) ≤ ord (f + g)`.
  have hxf : MMeromorphicAt (𝓘(ℂ, ℂ)) f.toFun y := f.mmero y (Set.mem_univ y)
  have hxg : MMeromorphicAt (𝓘(ℂ, ℂ)) g.toFun y := g.mmero y (Set.mem_univ y)
  have h_min :
      min (meromorphicOrderAt (f.toFun ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y))
          (meromorphicOrderAt (g.toFun ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y))
        ≤ meromorphicOrderAt
            ((f.toFun ∘ (chartAt ℂ y).symm)
              + (g.toFun ∘ (chartAt ℂ y).symm)) ((chartAt ℂ y) y) :=
    meromorphicOrderAt_add hxf hxg
  -- `hφ y` and `hψ y` are `-D y ≤ (mk _).orderAt y`, which is `rfl`-equal to
  -- the chart-pullback form needed below.
  have h_lb :
      ((-(D y) : ℤ) : WithTop ℤ)
        ≤ min (meromorphicOrderAt (f.toFun ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y))
              (meromorphicOrderAt (g.toFun ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y)) :=
    le_min (hφ y) (hψ y)
  exact h_lb.trans h_min

/-! ## Closure under ℂ-scalar action -/

/-- Scalar-multiplication closure. -/
lemma IsBoundedByDivisor.smul
    {D : JacobianChallenge.Div X} (c : ℂ)
    {φ : MeromorphicFunctionGerm X}
    (hφ : IsBoundedByDivisor D φ) :
    IsBoundedByDivisor D (c • φ) := by
  rcases φ with ⟨f⟩
  intro y
  show ((-(D y) : ℤ) : WithTop ℤ)
        ≤ MeromorphicFunctionGerm.orderAt y (c • MeromorphicFunctionGerm.mk f)
  rw [MeromorphicFunctionGerm.mk_smul, MeromorphicFunctionGerm.orderAt_mk]
  -- `(c • f).toFun = c • f.toFun` definitionally.
  have h_unfold_toFun : (c • f).toFun = c • f.toFun := rfl
  rw [h_unfold_toFun]
  show ((-(D y) : ℤ) : WithTop ℤ)
        ≤ meromorphicOrderAt
            ((c • f.toFun) ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y)
  by_cases hc : c = 0
  · -- `c = 0` ⇒ `c • f.toFun = 0` everywhere, order `⊤`.
    have h_eq : (c • f.toFun) = (0 : X → ℂ) := by
      ext x; simp [hc]
    rw [h_eq]
    have h_zero_comp :
        ((0 : X → ℂ) ∘ (chartAt ℂ y).symm) = (fun _ : ℂ => (0 : ℂ)) := rfl
    rw [h_zero_comp, meromorphicOrderAt_const ((chartAt ℂ y) y) (0 : ℂ)]
    simp
  · -- `c ≠ 0` ⇒ chart-pulled-back scalar reduces to const-times-original.
    have hxf : MMeromorphicAt (𝓘(ℂ, ℂ)) f.toFun y :=
      f.mmero y (Set.mem_univ y)
    have h_chart_unfold :
        (c • f.toFun) ∘ (chartAt ℂ y).symm
          = (fun _ : ℂ => c) • (f.toFun ∘ (chartAt ℂ y).symm) := by
      ext; simp [Pi.smul_apply]
    rw [h_chart_unfold,
        meromorphicOrderAt_smul (MeromorphicAt.const c _) hxf,
        meromorphicOrderAt_const _ c, if_neg hc, zero_add]
    -- `hφ y` is `-D y ≤ (mk f).orderAt y`, which is `rfl`-equal to the chart-pullback form.
    exact hφ y

/-! ## `L(D)` as a `Submodule ℂ` -/

/-- **`L(D)` packaged as a ℂ-vector subspace of `MeromorphicFunctionGerm X`.**

The honest Riemann–Roch ambient: standard linear-algebra dim machinery
(basis extension, `finrank`, dimension counting) now applies to `L(D)`
for any `D : Div X`. Replaces the pointwise-`X → ℂ` `linearSystemDeltaP`
of `Topology/LinearSystemDeltaP.lean` whose "blip" defect makes `finrank`
vacuously infinite (see `OPEN.md`). -/
def linearSystemDivisor (D : JacobianChallenge.Div X) :
    Submodule ℂ (MeromorphicFunctionGerm X) where
  carrier := {φ | IsBoundedByDivisor D φ}
  zero_mem' := IsBoundedByDivisor.zero D
  add_mem' := IsBoundedByDivisor.add
  smul_mem' c _φ hφ := IsBoundedByDivisor.smul c hφ

@[simp] lemma mem_linearSystemDivisor
    (D : JacobianChallenge.Div X) (φ : MeromorphicFunctionGerm X) :
    φ ∈ linearSystemDivisor D ↔ IsBoundedByDivisor D φ := Iff.rfl

end JacobianChallenge.MeromorphicFunctionField

/-! ## Specialisation: `D = 0` (zero divisor) — globally holomorphic germs -/

namespace JacobianChallenge.MeromorphicFunctionField

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- For `D = 0`, membership in `L(D)` says "the germ is holomorphic
everywhere" (`ord_y φ ≥ 0` for every `y`). -/
lemma IsBoundedByDivisor_zero_iff
    (φ : MeromorphicFunctionGerm X) :
    IsBoundedByDivisor (0 : JacobianChallenge.Div X) φ
      ↔ ∀ y : X, 0 ≤ φ.orderAt y := by
  unfold IsBoundedByDivisor
  constructor
  · intro h y
    have h_y := h y
    -- `(0 : Div X) y = 0`, so `-D y = 0` and the inequality becomes `0 ≤ ord_y φ`.
    rw [show ((0 : JacobianChallenge.Div X) y) = (0 : ℤ) from rfl] at h_y
    simpa using h_y
  · intro h y
    have h_y := h y
    rw [show ((0 : JacobianChallenge.Div X) y) = (0 : ℤ) from rfl]
    simpa using h_y

end JacobianChallenge.MeromorphicFunctionField

/-! ## Specialisation: `D = Div.single p` — recovers `linearSystemGermDeltaP` -/

namespace JacobianChallenge.MeromorphicFunctionField

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [DecidableEq X]

/-- For `D = Div.single p` (the singleton-indicator divisor at `p`),
the divisor-bound condition specialises to `ord_p φ ≥ -1` and
`ord_y φ ≥ 0` for `y ≠ p` — exactly `IsBoundedByDeltaPGerm p`. -/
lemma IsBoundedByDivisor_single_iff
    (p : X) (φ : MeromorphicFunctionGerm X) :
    IsBoundedByDivisor (JacobianChallenge.Div.single p) φ
      ↔ IsBoundedByDeltaPGerm p φ := by
  unfold IsBoundedByDivisor IsBoundedByDeltaPGerm
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · -- At `y = p`: `Div.single p p = 1`, so `-D p = -1`.
      have h_p := h p
      rw [JacobianChallenge.Div.single_apply, if_pos rfl] at h_p
      simpa using h_p
    · intro y hy
      have h_y := h y
      -- At `y ≠ p`: `Div.single p y = 0`, so `-D y = 0`.
      rw [JacobianChallenge.Div.single_apply, if_neg hy] at h_y
      simpa using h_y
  · rintro ⟨h_p, h_off⟩ y
    rw [JacobianChallenge.Div.single_apply]
    by_cases hy : y = p
    · subst hy
      simpa using h_p
    · simp only [if_neg hy, neg_zero]
      simpa using h_off y hy

/-- **`linearSystemDivisor (Div.single p) = linearSystemGermDeltaP p`.** -/
lemma linearSystemDivisor_single_eq (p : X) :
    linearSystemDivisor (JacobianChallenge.Div.single p)
      = linearSystemGermDeltaP p := by
  ext φ
  rw [mem_linearSystemDivisor, mem_linearSystemGermDeltaP]
  exact IsBoundedByDivisor_single_iff p φ

end JacobianChallenge.MeromorphicFunctionField

end
