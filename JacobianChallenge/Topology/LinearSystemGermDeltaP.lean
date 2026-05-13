/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicFunctionField
import JacobianChallenge.Topology.LinearSystemDeltaP

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `linearSystemGermDeltaP` — `L(δp)` as a `Submodule ℂ` of the germ field

The honest Riemann–Roch linear system `L(δp)` at a divisor `δp`, built
on top of `MeromorphicFunctionGerm X` (the punctured-germ quotient of
globally meromorphic functions). Replaces the pointwise-functions
ambient `linearSystemDeltaP p : Submodule ℂ (X → ℂ)` of
`Topology/LinearSystemDeltaP.lean`, which is broken by the "blip"
counterexample (see `OPEN.md` *Architectural issue: RR-thread linear
system*): pointwise `g(p₀) = 100, g elsewhere = 0` lives in
`linearSystemDeltaP` but collapses to `0` in the germ quotient.

## Construction

* `MeromorphicFunctionGerm.orderAt p (φ : MeromorphicFunctionGerm X) :
  WithTop ℤ` — the meromorphic order at `p`, descended through the
  germ quotient via `meromorphicOrderAt_congr` over the chart pullback.
* `IsBoundedByDeltaPGerm p (φ : MeromorphicFunctionGerm X) : Prop` —
  `φ` has order `≥ -1` at `p` and `≥ 0` everywhere else.
* `IsBoundedByDeltaPGerm.{zero, add, smul, const}` — closure lemmas,
  proved by `Quotient.inductionOn` down to the representative
  `IsBoundedByDeltaP` (which already has its closure lemmas).
* `linearSystemGermDeltaP p : Submodule ℂ (MeromorphicFunctionGerm X)` —
  the assembled subspace.

This chip does *not* yet provide a finrank bound; that's owed to a
follow-up (the analytic side of dim ≥ 2 at genus 0 requires the
existence of a meromorphic function with a simple pole at `p` and no
other poles, which is a Riemann–Roch consequence, not built in this
chip). What this chip *does* deliver is the honest ambient over which
the dimension question can be coherently posed — replacing the
vacuously-infinite `linearSystemDeltaP`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set
open JacobianChallenge.MeromorphicNonzero
  (chartSymm_tendsto_nhdsNE)

namespace JacobianChallenge.MeromorphicFunctionField

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Germ-invariant order

`mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun p` only depends on the punctured
germ of `f.toFun` at `p`: the chart-side `meromorphicOrderAt` is invariant
under chart-side `=ᶠ[𝓝[≠] (chart p)]`, and the manifold-side punctured
EvEq pushes through `chartSymm_tendsto_nhdsNE`. -/

/-- The order of a meromorphic-function germ at a point. Descended
through the quotient by `meromorphicOrderAt_congr` applied to the chart
pullback. -/
def MeromorphicFunctionGerm.orderAt
    (p : X) : MeromorphicFunctionGerm X → WithTop ℤ :=
  Quotient.lift (s := germSetoid X)
    (fun f : MMer X => mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun p)
    (by
      intro f g hfg
      -- `hfg : ∀ y, f.toFun =ᶠ[𝓝[≠] y] g.toFun`. At `y = p` we get
      -- chart-side `=ᶠ[𝓝[≠] (chart p)]` via `chartSymm_tendsto_nhdsNE`.
      show meromorphicOrderAt (f.toFun ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p)
          = meromorphicOrderAt (g.toFun ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p)
      apply meromorphicOrderAt_congr
      exact (chartSymm_tendsto_nhdsNE p).eventually (hfg p))

/-- `(mk f).orderAt p = mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun p`.
Definitional. -/
@[simp] lemma MeromorphicFunctionGerm.orderAt_mk
    (p : X) (f : MMer X) :
    (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm X).orderAt p
      = mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun p := rfl

end JacobianChallenge.MeromorphicFunctionField

namespace JacobianChallenge.MeromorphicFunctionField

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## `IsBoundedByDeltaPGerm` predicate -/

/-- A germ `φ` is **bounded by δp** if its order is `≥ -1` at `p` and
`≥ 0` everywhere else. This is the germ-quotient counterpart of
`JacobianChallenge.IsBoundedByDeltaP`, with the `MMeromorphicOn`
conjunct dropped (it is automatic for `MMer` representatives). -/
def IsBoundedByDeltaPGerm
    (p : X) (φ : MeromorphicFunctionGerm X) : Prop :=
  ((-1 : ℤ) : WithTop ℤ) ≤ φ.orderAt p ∧
  ∀ y, y ≠ p → 0 ≤ φ.orderAt y

/-- Membership at the representative level. -/
lemma IsBoundedByDeltaPGerm_mk_iff
    (p : X) (f : MMer X) :
    IsBoundedByDeltaPGerm p (MeromorphicFunctionGerm.mk f) ↔
      (((-1 : ℤ) : WithTop ℤ) ≤ mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun p ∧
       ∀ y, y ≠ p → 0 ≤ mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y) := by
  -- both sides have the same conjuncts after `orderAt_mk` unfolds
  rfl

/-- Bridge: a representative satisfying the pointwise `IsBoundedByDeltaP`
gives a germ satisfying `IsBoundedByDeltaPGerm`. -/
lemma IsBoundedByDeltaPGerm.of_isBoundedByDeltaP
    (p : X) (f : MMer X)
    (hf : JacobianChallenge.IsBoundedByDeltaP p f.toFun) :
    IsBoundedByDeltaPGerm p (MeromorphicFunctionGerm.mk f) := by
  obtain ⟨_, h_off, h_p⟩ := hf
  rw [IsBoundedByDeltaPGerm_mk_iff]
  exact ⟨h_p, h_off⟩

/-- Bridge in reverse: a germ-level membership at a representative `f`
extracts to the pointwise `IsBoundedByDeltaP` (the `MMeromorphicOn`
conjunct is supplied by `f.mmero`). -/
lemma IsBoundedByDeltaPGerm.to_isBoundedByDeltaP
    (p : X) (f : MMer X)
    (h : IsBoundedByDeltaPGerm p (MeromorphicFunctionGerm.mk f)) :
    JacobianChallenge.IsBoundedByDeltaP p f.toFun := by
  rw [IsBoundedByDeltaPGerm_mk_iff] at h
  exact ⟨f.mmero, h.2, h.1⟩

/-! ## Closure under zero, addition, and ℂ-scalar action

Each closure lemma reduces by `Quotient.inductionOn` to the
representative-level `JacobianChallenge.IsBoundedByDeltaP.{zero, add,
smul}`, which already lives in `Topology/LinearSystemDeltaP.lean`. -/

/-- `0 ∈ L(δp)` on the germ side. -/
lemma IsBoundedByDeltaPGerm.zero (p : X) :
    IsBoundedByDeltaPGerm p (0 : MeromorphicFunctionGerm X) := by
  show IsBoundedByDeltaPGerm p (MeromorphicFunctionGerm.mk (0 : MMer X))
  apply IsBoundedByDeltaPGerm.of_isBoundedByDeltaP
  -- `(0 : MMer X).toFun = (0 : X → ℂ)` definitionally
  exact JacobianChallenge.IsBoundedByDeltaP.zero p

/-- Sum closure on the germ side. -/
lemma IsBoundedByDeltaPGerm.add
    {p : X} {φ ψ : MeromorphicFunctionGerm X}
    (hφ : IsBoundedByDeltaPGerm p φ) (hψ : IsBoundedByDeltaPGerm p ψ) :
    IsBoundedByDeltaPGerm p (φ + ψ) := by
  rcases φ with ⟨f⟩
  rcases ψ with ⟨g⟩
  have hf : JacobianChallenge.IsBoundedByDeltaP p f.toFun :=
    IsBoundedByDeltaPGerm.to_isBoundedByDeltaP p f hφ
  have hg : JacobianChallenge.IsBoundedByDeltaP p g.toFun :=
    IsBoundedByDeltaPGerm.to_isBoundedByDeltaP p g hψ
  have hfg : JacobianChallenge.IsBoundedByDeltaP p (f.toFun + g.toFun) := hf.add hg
  -- `(f + g).toFun = f.toFun + g.toFun` definitionally.
  -- Reduce the germ-level sum to `mk (f + g)`:
  show IsBoundedByDeltaPGerm p
      (MeromorphicFunctionGerm.mk f + MeromorphicFunctionGerm.mk g)
  rw [MeromorphicFunctionGerm.mk_add]
  exact IsBoundedByDeltaPGerm.of_isBoundedByDeltaP p (f + g) hfg

/-- ℂ-scalar closure on the germ side. -/
lemma IsBoundedByDeltaPGerm.smul
    {p : X} (c : ℂ) {φ : MeromorphicFunctionGerm X}
    (hφ : IsBoundedByDeltaPGerm p φ) :
    IsBoundedByDeltaPGerm p (c • φ) := by
  rcases φ with ⟨f⟩
  have hf : JacobianChallenge.IsBoundedByDeltaP p f.toFun :=
    IsBoundedByDeltaPGerm.to_isBoundedByDeltaP p f hφ
  have hcf : JacobianChallenge.IsBoundedByDeltaP p (c • f.toFun) :=
    JacobianChallenge.IsBoundedByDeltaP.smul c hf
  show IsBoundedByDeltaPGerm p (c • MeromorphicFunctionGerm.mk f)
  rw [MeromorphicFunctionGerm.mk_smul]
  exact IsBoundedByDeltaPGerm.of_isBoundedByDeltaP p (c • f) hcf

/-- Constant-germ membership: every constant `c : ℂ` produces a germ in
`L(δp)`. In particular `1 ∈ L(δp)`. -/
lemma IsBoundedByDeltaPGerm.const
    (p : X) (c : ℂ) :
    IsBoundedByDeltaPGerm p
      (MeromorphicFunctionGerm.mk (MMer.const c : MMer X)) := by
  apply IsBoundedByDeltaPGerm.of_isBoundedByDeltaP
  -- `(MMer.const c).toFun = fun _ => c` definitionally.
  exact JacobianChallenge.IsBoundedByDeltaP.const p c

end JacobianChallenge.MeromorphicFunctionField

/-! ## `L(δp)` as a `Submodule ℂ` of the germ field -/

namespace JacobianChallenge.MeromorphicFunctionField

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`L(δp)` packaged as a `ℂ`-vector subspace of the germ field.** -/
def linearSystemGermDeltaP (p : X) :
    Submodule ℂ (MeromorphicFunctionGerm X) where
  carrier := {φ | IsBoundedByDeltaPGerm p φ}
  zero_mem' := IsBoundedByDeltaPGerm.zero p
  add_mem' := IsBoundedByDeltaPGerm.add
  smul_mem' c _φ hφ := IsBoundedByDeltaPGerm.smul c hφ

/-- Membership in `linearSystemGermDeltaP p` is by definition
`IsBoundedByDeltaPGerm p`. -/
@[simp] lemma mem_linearSystemGermDeltaP
    (p : X) (φ : MeromorphicFunctionGerm X) :
    φ ∈ linearSystemGermDeltaP p ↔ IsBoundedByDeltaPGerm p φ := Iff.rfl

/-- **`1 ∈ L(δp)`** on the germ side: the constant `1` is in the linear
system. This is the trivial "L(δp) contains constants" half of the
genus-zero RR argument `dim L(δp) ≥ 2`; the *non-trivial* second
generator (a function with a genuine simple pole at `p` and no other
poles) is owed to a follow-up chip and requires Riemann–Roch content. -/
lemma one_mem_linearSystemGermDeltaP (p : X) :
    (1 : MeromorphicFunctionGerm X) ∈ linearSystemGermDeltaP p := by
  rw [mem_linearSystemGermDeltaP]
  -- `(1 : MeromorphicFunctionGerm X) = mk (1 : MMer X) = mk (MMer.const 1)` definitionally.
  show IsBoundedByDeltaPGerm p (MeromorphicFunctionGerm.mk (1 : MMer X))
  apply IsBoundedByDeltaPGerm.of_isBoundedByDeltaP
  -- `(1 : MMer X).toFun = fun _ => 1` definitionally.
  show JacobianChallenge.IsBoundedByDeltaP p (fun _ : X => (1 : ℂ))
  exact JacobianChallenge.IsBoundedByDeltaP.const p (1 : ℂ)

end JacobianChallenge.MeromorphicFunctionField

end
