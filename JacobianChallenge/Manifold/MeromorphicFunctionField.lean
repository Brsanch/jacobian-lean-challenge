/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicAt
import JacobianChallenge.Divisor.PrincipalDivisor
import Mathlib.Analysis.Meromorphic.Order

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # The meromorphic function field `MeromorphicFunctionGerm X`

This file defines the **field of germs of meromorphic functions** on a
compact connected complex 1-manifold `X`. The field is the structurally
correct ambient for `L(D)` (the Riemann–Roch linear system associated to
a divisor `D`), replacing the ad-hoc `linearSystemDeltaP : Submodule ℂ
(X → ℂ)` used in the RR-genus-zero thread (`Topology/LinearSystemDeltaP.
lean`). The former has a known "blip" defect — see `OPEN.md`
*Architectural issue: RR-thread linear system* — because pointwise
equality at the pole `p` distinguishes essentially-equal meromorphic
functions, polluting the dimension count.

## Construction

* `MMer X` — bundled meromorphic function: `toFun : X → ℂ` together with
  `MMeromorphicOn 𝓘(ℂ,ℂ) toFun Set.univ`. Comes with pointwise
  algebraic operations.
* `germSetoid : Setoid (MMer X)` — punctured-nhd `EventuallyEq` at every
  point. Two meromorphic functions are identified iff they agree on a
  *punctured* neighborhood of every point, allowing their pointwise
  values at zeros/poles to differ.
* `MeromorphicFunctionGerm X := Quotient (germSetoid X)` — the quotient
  type.
* A `CommRing` instance, an `Algebra ℂ` instance, and (with
  `ConnectedSpace X`) a `Field` instance, built by descent of pointwise
  operations through `Filter.EventuallyEq.{add, mul, neg, inv, smul}`.

## Why this works where `linearSystemDeltaP` fails

The "blip" counterexample `g(p₀) = 100, g elsewhere = 0` becomes
identified with `0` in the germ quotient because both agree on every
punctured neighborhood. Therefore `[g] = [0]` in
`MeromorphicFunctionGerm X`, and pole-order arguments operate on the
true meromorphic germ, not the raw pointwise function.

## Identity theorem

The `Field` instance requires showing `[f] ≠ [0] → [f] * [f⁻¹] = [1]`
where `[f⁻¹]` is the germ of the pointwise inverse. The pointwise product
equals `1` off the zero/pole set of `f`. To conclude `=ᶠ[𝓝[≠] y] 1` at
every `y`, we need the zero/pole set to be locally finite near every
`y` — equivalently, `mmeromorphicOrderAt f y ≠ ⊤` for every `y`.

The hypothesis `[f] ≠ [0]` gives this *at some* `y`. The bridge is the
**identity theorem on a connected complex 1-manifold**: the set
`{y : mmeromorphicOrderAt f y = ⊤}` is clopen on `X`, hence empty or
everything. If non-empty, `[f] = [0]`. So `[f] ≠ [0]` forces emptiness,
i.e., `mmeromorphicOrderAt f y ≠ ⊤` for every `y`.

This is the manifold-side counterpart of mathlib's
`MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall` (chart-side,
on connected open `U ⊆ 𝕜`), and we prove it directly via the chart
pullback. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set
open JacobianChallenge.MeromorphicNonzero
  (chart_tendsto_nhdsNE chartSymm_tendsto_nhdsNE nhdsNE_neBot)

namespace JacobianChallenge.MeromorphicFunctionField

universe u

/-! ## The bundled type `MMer X` of meromorphic functions on `X`

`MMer X` packages a function `X → ℂ` together with a global
meromorphicity witness `MMeromorphicOn 𝓘(ℂ,ℂ) toFun Set.univ`. Pointwise
arithmetic on `X → ℂ` lifts directly via the closure lemmas in
`Manifold/MeromorphicAt.lean` (`MMeromorphicOn.{add, mul, neg, sub, inv,
zero, const}`). -/

variable (X : Type u)
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- A bundled global meromorphic function on `X`: the underlying
`toFun : X → ℂ` together with a proof that it is meromorphic at every
point of `X`. -/
structure MMer where
  /-- The underlying function. -/
  toFun : X → ℂ
  /-- Global meromorphicity (every point of `X` is in the meromorphic
  domain). -/
  mmero : MMeromorphicOn 𝓘(ℂ, ℂ) toFun Set.univ

end JacobianChallenge.MeromorphicFunctionField

namespace JacobianChallenge.MeromorphicFunctionField

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ### Coercion and extensionality -/

instance : CoeFun (MMer X) (fun _ => X → ℂ) := ⟨MMer.toFun⟩

@[ext]
lemma MMer.ext {f g : MMer X} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; congr

/-! ### Pointwise arithmetic on `MMer X`

Each algebraic operation on `MMer X` is built by combining pointwise
operations on the `toFun` field with the corresponding closure lemma on
`MMeromorphicOn`. The resulting `MMer X` is **not** a ring in the
algebraic sense (e.g. `f * f⁻¹` is `0` at zeros of `f`, not `1`), but the
pointwise operations are what descends cleanly to the germ quotient. -/

instance : Zero (MMer X) := ⟨⟨0, MMeromorphicOn.zero⟩⟩

instance : One (MMer X) := ⟨⟨fun _ => 1, MMeromorphicOn.const 1⟩⟩

@[simp] lemma MMer.zero_toFun : (0 : MMer X).toFun = 0 := rfl
@[simp] lemma MMer.one_toFun : (1 : MMer X).toFun = fun _ => 1 := rfl

instance : Add (MMer X) := ⟨fun f g => ⟨f.toFun + g.toFun, f.mmero.add g.mmero⟩⟩
instance : Mul (MMer X) := ⟨fun f g => ⟨f.toFun * g.toFun, f.mmero.mul g.mmero⟩⟩
instance : Neg (MMer X) := ⟨fun f => ⟨-f.toFun, f.mmero.neg⟩⟩
instance : Sub (MMer X) := ⟨fun f g => ⟨f.toFun - g.toFun, f.mmero.sub g.mmero⟩⟩
instance : Inv (MMer X) := ⟨fun f => ⟨f.toFun⁻¹, f.mmero.inv⟩⟩

@[simp] lemma MMer.add_toFun (f g : MMer X) : (f + g).toFun = f.toFun + g.toFun := rfl
@[simp] lemma MMer.mul_toFun (f g : MMer X) : (f * g).toFun = f.toFun * g.toFun := rfl
@[simp] lemma MMer.neg_toFun (f : MMer X) : (-f).toFun = -f.toFun := rfl
@[simp] lemma MMer.sub_toFun (f g : MMer X) : (f - g).toFun = f.toFun - g.toFun := rfl
@[simp] lemma MMer.inv_toFun (f : MMer X) : f⁻¹.toFun = f.toFun⁻¹ := rfl

/-- ℂ-scalar action by pointwise multiplication. -/
instance : SMul ℂ (MMer X) :=
  ⟨fun c f => ⟨c • f.toFun, by
    intro x _
    have h_eq : (c • f.toFun) = (fun _ : X => c) * f.toFun := by
      funext y; simp [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    rw [h_eq]
    exact (MMeromorphicAt.const (I := 𝓘(ℂ, ℂ)) (x := x) c).mul (f.mmero x trivial)⟩⟩

@[simp] lemma MMer.smul_toFun (c : ℂ) (f : MMer X) : (c • f).toFun = c • f.toFun := rfl

/-- The constant meromorphic function `fun _ => c`. -/
def MMer.const (c : ℂ) : MMer X := ⟨fun _ => c, MMeromorphicOn.const c⟩

@[simp] lemma MMer.const_toFun (c : ℂ) : (MMer.const c : MMer X).toFun = fun _ => c := rfl

end JacobianChallenge.MeromorphicFunctionField

namespace JacobianChallenge.MeromorphicFunctionField

/-! ## The germ-equivalence setoid

Two `MMer` values are identified iff their underlying functions agree on
a **punctured** neighborhood of every point. Their values at the points
themselves can differ; in particular, the "blip" function
`g(p₀) = 100, g elsewhere = 0` is identified with the zero function. -/

variable (X : Type u)
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- The (punctured) germ-equivalence relation on `MMer X`. -/
def germSetoid : Setoid (MMer X) where
  r f g := ∀ y : X, f.toFun =ᶠ[𝓝[≠] y] g.toFun
  iseqv :=
    { refl := fun _ _ => Filter.EventuallyEq.refl _ _
      symm := fun h y => (h y).symm
      trans := fun h₁ h₂ y => (h₁ y).trans (h₂ y) }

/-- The **field of meromorphic-function germs** on `X`. We will exhibit a
`Field` instance (under `ConnectedSpace X`). -/
def MeromorphicFunctionGerm : Type u := Quotient (germSetoid X)

end JacobianChallenge.MeromorphicFunctionField

namespace JacobianChallenge.MeromorphicFunctionField

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- The canonical projection `MMer X → MeromorphicFunctionGerm X`. -/
def MeromorphicFunctionGerm.mk (f : MMer X) : MeromorphicFunctionGerm X :=
  Quotient.mk (germSetoid X) f

@[simp] lemma MeromorphicFunctionGerm.mk_eq (f g : MMer X) :
    (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm X)
        = MeromorphicFunctionGerm.mk g ↔
      ∀ y, f.toFun =ᶠ[𝓝[≠] y] g.toFun :=
  Quotient.eq (r := germSetoid X)

end JacobianChallenge.MeromorphicFunctionField

/-! ## Descent of pointwise ring operations to the quotient -/

namespace JacobianChallenge.MeromorphicFunctionField

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ### Addition -/

lemma add_germ_respects
    {f₁ f₂ g₁ g₂ : MMer X}
    (hf : ∀ y : X, f₁.toFun =ᶠ[𝓝[≠] y] f₂.toFun)
    (hg : ∀ y : X, g₁.toFun =ᶠ[𝓝[≠] y] g₂.toFun) :
    ∀ y : X, (f₁ + g₁).toFun =ᶠ[𝓝[≠] y] (f₂ + g₂).toFun := by
  intro y
  show (f₁.toFun + g₁.toFun) =ᶠ[𝓝[≠] y] (f₂.toFun + g₂.toFun)
  exact (hf y).add (hg y)

noncomputable instance : Add (MeromorphicFunctionGerm X) where
  add := Quotient.lift₂ (s₁ := germSetoid X) (s₂ := germSetoid X)
    (fun f g => Quotient.mk (germSetoid X) (f + g))
    (by
      intro f₁ g₁ f₂ g₂ hf hg
      apply Quotient.sound
      exact add_germ_respects hf hg)

@[simp] lemma MeromorphicFunctionGerm.mk_add (f g : MMer X) :
    (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm X)
        + MeromorphicFunctionGerm.mk g
      = MeromorphicFunctionGerm.mk (f + g) := rfl

/-! ### Multiplication -/

lemma mul_germ_respects
    {f₁ f₂ g₁ g₂ : MMer X}
    (hf : ∀ y : X, f₁.toFun =ᶠ[𝓝[≠] y] f₂.toFun)
    (hg : ∀ y : X, g₁.toFun =ᶠ[𝓝[≠] y] g₂.toFun) :
    ∀ y : X, (f₁ * g₁).toFun =ᶠ[𝓝[≠] y] (f₂ * g₂).toFun := by
  intro y
  show (f₁.toFun * g₁.toFun) =ᶠ[𝓝[≠] y] (f₂.toFun * g₂.toFun)
  exact (hf y).mul (hg y)

noncomputable instance : Mul (MeromorphicFunctionGerm X) where
  mul := Quotient.lift₂ (s₁ := germSetoid X) (s₂ := germSetoid X)
    (fun f g => Quotient.mk (germSetoid X) (f * g))
    (by
      intro f₁ g₁ f₂ g₂ hf hg
      apply Quotient.sound
      exact mul_germ_respects hf hg)

@[simp] lemma MeromorphicFunctionGerm.mk_mul (f g : MMer X) :
    (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm X)
        * MeromorphicFunctionGerm.mk g
      = MeromorphicFunctionGerm.mk (f * g) := rfl

/-! ### Negation -/

lemma neg_germ_respects
    {f₁ f₂ : MMer X}
    (hf : ∀ y : X, f₁.toFun =ᶠ[𝓝[≠] y] f₂.toFun) :
    ∀ y : X, (-f₁).toFun =ᶠ[𝓝[≠] y] (-f₂).toFun := by
  intro y
  show (-f₁.toFun) =ᶠ[𝓝[≠] y] (-f₂.toFun)
  exact (hf y).neg

noncomputable instance : Neg (MeromorphicFunctionGerm X) where
  neg := Quotient.lift (s := germSetoid X)
    (fun f => Quotient.mk (germSetoid X) (-f))
    (by
      intro f₁ f₂ hf
      apply Quotient.sound
      exact neg_germ_respects hf)

@[simp] lemma MeromorphicFunctionGerm.mk_neg (f : MMer X) :
    -(MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm X)
      = MeromorphicFunctionGerm.mk (-f) := rfl

/-! ### Subtraction -/

lemma sub_germ_respects
    {f₁ f₂ g₁ g₂ : MMer X}
    (hf : ∀ y : X, f₁.toFun =ᶠ[𝓝[≠] y] f₂.toFun)
    (hg : ∀ y : X, g₁.toFun =ᶠ[𝓝[≠] y] g₂.toFun) :
    ∀ y : X, (f₁ - g₁).toFun =ᶠ[𝓝[≠] y] (f₂ - g₂).toFun := by
  intro y
  show (f₁.toFun - g₁.toFun) =ᶠ[𝓝[≠] y] (f₂.toFun - g₂.toFun)
  exact (hf y).sub (hg y)

noncomputable instance : Sub (MeromorphicFunctionGerm X) where
  sub := Quotient.lift₂ (s₁ := germSetoid X) (s₂ := germSetoid X)
    (fun f g => Quotient.mk (germSetoid X) (f - g))
    (by
      intro f₁ g₁ f₂ g₂ hf hg
      apply Quotient.sound
      exact sub_germ_respects hf hg)

@[simp] lemma MeromorphicFunctionGerm.mk_sub (f g : MMer X) :
    (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm X)
        - MeromorphicFunctionGerm.mk g
      = MeromorphicFunctionGerm.mk (f - g) := rfl

/-! ### Zero and One -/

noncomputable instance : Zero (MeromorphicFunctionGerm X) :=
  ⟨Quotient.mk (germSetoid X) (0 : MMer X)⟩

noncomputable instance : One (MeromorphicFunctionGerm X) :=
  ⟨Quotient.mk (germSetoid X) (1 : MMer X)⟩

@[simp] lemma MeromorphicFunctionGerm.zero_def :
    (0 : MeromorphicFunctionGerm X) = MeromorphicFunctionGerm.mk (0 : MMer X) := rfl

@[simp] lemma MeromorphicFunctionGerm.one_def :
    (1 : MeromorphicFunctionGerm X) = MeromorphicFunctionGerm.mk (1 : MMer X) := rfl

/-! ### ℂ-scalar action -/

lemma smul_germ_respects
    (c : ℂ) {f₁ f₂ : MMer X}
    (hf : ∀ y : X, f₁.toFun =ᶠ[𝓝[≠] y] f₂.toFun) :
    ∀ y : X, (c • f₁).toFun =ᶠ[𝓝[≠] y] (c • f₂).toFun := by
  intro y
  show (c • f₁.toFun) =ᶠ[𝓝[≠] y] (c • f₂.toFun)
  filter_upwards [hf y] with z hz
  show c • f₁.toFun z = c • f₂.toFun z
  rw [hz]

noncomputable instance : SMul ℂ (MeromorphicFunctionGerm X) where
  smul := fun c => Quotient.lift (s := germSetoid X)
    (fun f => Quotient.mk (germSetoid X) (c • f))
    (by
      intro f₁ f₂ hf
      apply Quotient.sound
      exact smul_germ_respects c hf)

@[simp] lemma MeromorphicFunctionGerm.mk_smul (c : ℂ) (f : MMer X) :
    c • (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm X)
      = MeromorphicFunctionGerm.mk (c • f) := rfl

/-! ### Pointwise inverse -/

lemma inv_germ_respects
    {f₁ f₂ : MMer X}
    (hf : ∀ y : X, f₁.toFun =ᶠ[𝓝[≠] y] f₂.toFun) :
    ∀ y : X, (f₁⁻¹).toFun =ᶠ[𝓝[≠] y] (f₂⁻¹).toFun := by
  intro y
  show (f₁.toFun⁻¹) =ᶠ[𝓝[≠] y] (f₂.toFun⁻¹)
  exact (hf y).inv

noncomputable instance : Inv (MeromorphicFunctionGerm X) where
  inv := Quotient.lift (s := germSetoid X)
    (fun f => Quotient.mk (germSetoid X) (f⁻¹))
    (by
      intro f₁ f₂ hf
      apply Quotient.sound
      exact inv_germ_respects hf)

@[simp] lemma MeromorphicFunctionGerm.mk_inv (f : MMer X) :
    (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm X)⁻¹
      = MeromorphicFunctionGerm.mk (f⁻¹) := rfl

end JacobianChallenge.MeromorphicFunctionField

/-! ## `CommRing` instance

Each ring axiom is discharged by `Quotient.sound` against a punctured-nhd
EvEq computation on the underlying pointwise functions, which is just
the corresponding ℂ-arithmetic identity. -/

namespace JacobianChallenge.MeromorphicFunctionField

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

private lemma pw_eventuallyEq_of_funext {F G : X → ℂ} (h : F = G) (y : X) :
    F =ᶠ[𝓝[≠] y] G := by rw [h]

private lemma forall_pw_eventuallyEq_of_funext {F G : X → ℂ} (h : F = G) :
    ∀ y : X, F =ᶠ[𝓝[≠] y] G := fun y => pw_eventuallyEq_of_funext h y

/-- Uniform "pointwise everywhere" tactic for descent through `Quotient.sound`.
Reduces the goal to a literal `(F z = G z)` for `F, G : X → ℂ` evaluated
pointwise at each `z`. -/
private lemma germ_eq_of_pointwise
    {f₁ f₂ : MMer X}
    (h : ∀ z, f₁.toFun z = f₂.toFun z) :
    (MeromorphicFunctionGerm.mk f₁ : MeromorphicFunctionGerm X)
      = MeromorphicFunctionGerm.mk f₂ := by
  apply Quotient.sound
  intro y
  exact Filter.Eventually.of_forall h

noncomputable instance : CommRing (MeromorphicFunctionGerm X) where
  add_assoc := by
    rintro ⟨f⟩ ⟨g⟩ ⟨h⟩
    apply germ_eq_of_pointwise
    intro z; show f.toFun z + g.toFun z + h.toFun z = f.toFun z + (g.toFun z + h.toFun z)
    ring
  zero_add := by
    rintro ⟨f⟩
    apply germ_eq_of_pointwise
    intro z; show (0 : ℂ) + f.toFun z = f.toFun z; ring
  add_zero := by
    rintro ⟨f⟩
    apply germ_eq_of_pointwise
    intro z; show f.toFun z + (0 : ℂ) = f.toFun z; ring
  add_comm := by
    rintro ⟨f⟩ ⟨g⟩
    apply germ_eq_of_pointwise
    intro z; show f.toFun z + g.toFun z = g.toFun z + f.toFun z; ring
  neg_add_cancel := by
    rintro ⟨f⟩
    apply germ_eq_of_pointwise
    intro z; show -f.toFun z + f.toFun z = (0 : ℂ); ring
  sub_eq_add_neg := by
    rintro ⟨f⟩ ⟨g⟩
    apply germ_eq_of_pointwise
    intro z; show f.toFun z - g.toFun z = f.toFun z + -g.toFun z; ring
  mul_assoc := by
    rintro ⟨f⟩ ⟨g⟩ ⟨h⟩
    apply germ_eq_of_pointwise
    intro z; show f.toFun z * g.toFun z * h.toFun z = f.toFun z * (g.toFun z * h.toFun z)
    ring
  one_mul := by
    rintro ⟨f⟩
    apply germ_eq_of_pointwise
    intro z; show (1 : ℂ) * f.toFun z = f.toFun z; ring
  mul_one := by
    rintro ⟨f⟩
    apply germ_eq_of_pointwise
    intro z; show f.toFun z * (1 : ℂ) = f.toFun z; ring
  zero_mul := by
    rintro ⟨f⟩
    apply germ_eq_of_pointwise
    intro z; show (0 : ℂ) * f.toFun z = (0 : ℂ); ring
  mul_zero := by
    rintro ⟨f⟩
    apply germ_eq_of_pointwise
    intro z; show f.toFun z * (0 : ℂ) = (0 : ℂ); ring
  left_distrib := by
    rintro ⟨f⟩ ⟨g⟩ ⟨h⟩
    apply germ_eq_of_pointwise
    intro z; show f.toFun z * (g.toFun z + h.toFun z)
        = f.toFun z * g.toFun z + f.toFun z * h.toFun z
    ring
  right_distrib := by
    rintro ⟨f⟩ ⟨g⟩ ⟨h⟩
    apply germ_eq_of_pointwise
    intro z; show (f.toFun z + g.toFun z) * h.toFun z
        = f.toFun z * h.toFun z + g.toFun z * h.toFun z
    ring
  mul_comm := by
    rintro ⟨f⟩ ⟨g⟩
    apply germ_eq_of_pointwise
    intro z; show f.toFun z * g.toFun z = g.toFun z * f.toFun z; ring
  nsmul := nsmulRec
  zsmul := zsmulRec

/-! ### `Algebra ℂ` instance via the constant embedding -/

/-- The algebra map `ℂ → MeromorphicFunctionGerm X`, sending `c` to the
class of the constant function `fun _ => c`. -/
noncomputable def algebraMapC : ℂ →+* MeromorphicFunctionGerm X where
  toFun c := MeromorphicFunctionGerm.mk (MMer.const c)
  map_one' := by
    apply germ_eq_of_pointwise; intro _; rfl
  map_mul' := by
    intro c d
    apply germ_eq_of_pointwise; intro _
    show c * d = c * d
    rfl
  map_zero' := by
    apply germ_eq_of_pointwise; intro _; rfl
  map_add' := by
    intro c d
    apply germ_eq_of_pointwise; intro _
    show c + d = c + d
    rfl

noncomputable instance : Algebra ℂ (MeromorphicFunctionGerm X) where
  smul c := fun φ => c • φ
  algebraMap := algebraMapC
  commutes' := by
    intro c φ
    induction φ using Quotient.inductionOn with
    | _ f =>
      apply germ_eq_of_pointwise; intro z
      show c * f.toFun z = f.toFun z * c
      ring
  smul_def' := by
    intro c φ
    induction φ using Quotient.inductionOn with
    | _ f =>
      apply germ_eq_of_pointwise; intro z
      show c • f.toFun z = c * f.toFun z
      rw [smul_eq_mul]

end JacobianChallenge.MeromorphicFunctionField

/-! ## Identity theorem on a connected complex 1-manifold

The "essentially-zero" set `S = {y : mmeromorphicOrderAt f y = ⊤}` is
clopen on `X`, hence on a connected `X` it is either empty or all of
`X`. We package this as `essentiallyZero_set_isClopen` and
`mmeromorphicOrderAt_ne_top_of_exists`. -/

namespace JacobianChallenge.MeromorphicFunctionField

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- `mmeromorphicOrderAt f y = ⊤` is equivalent to `f =ᶠ[𝓝[≠] y] 0` on
the manifold side. -/
lemma mmeromorphicOrderAt_eq_top_iff_eventually_eq_zero
    (f : X → ℂ) (hf : MMeromorphicOn 𝓘(ℂ, ℂ) f Set.univ) (y : X) :
    mmeromorphicOrderAt 𝓘(ℂ, ℂ) f y = ⊤ ↔ f =ᶠ[𝓝[≠] y] (fun _ => 0) := by
  -- Chart-side: `mmeromorphicOrderAt I f y = meromorphicOrderAt (f ∘ chart.symm) (chart y)`.
  -- `meromorphicOrderAt_eq_top_iff` gives the chart-side EvEq.
  -- Transport across `(chartAt ℂ y)` via the homeomorphism on the chart source.
  constructor
  · intro h_top
    have h_chart_top :
        meromorphicOrderAt (f ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) = ⊤ := h_top
    have h_chart_mero : MeromorphicAt (f ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) :=
      hf y trivial
    have h_chart_evEq : (f ∘ (chartAt ℂ y).symm) =ᶠ[𝓝[≠] ((chartAt ℂ y) y)] 0 :=
      meromorphicOrderAt_eq_top_iff.mp h_chart_top
    -- Pull back to manifold using `chart_tendsto_nhdsNE`.
    have h_compose : ((f ∘ (chartAt ℂ y).symm) ∘ (chartAt ℂ y)) =ᶠ[𝓝[≠] y]
        ((0 : ℂ → ℂ) ∘ (chartAt ℂ y)) :=
      (chart_tendsto_nhdsNE y).eventually h_chart_evEq
    have h_src_mem : (chartAt ℂ y).source ∈ 𝓝[≠] y :=
      nhdsWithin_le_nhds
        ((chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y))
    have h_left_inv :
        ((f ∘ (chartAt ℂ y).symm) ∘ (chartAt ℂ y)) =ᶠ[𝓝[≠] y] f := by
      filter_upwards [h_src_mem] with z hz
      show f ((chartAt ℂ y).symm ((chartAt ℂ y) z)) = f z
      rw [(chartAt ℂ y).left_inv hz]
    have h_zero_compose : ((0 : ℂ → ℂ) ∘ (chartAt ℂ y)) = (fun _ : X => (0 : ℂ)) := rfl
    refine h_left_inv.symm.trans ?_
    rw [show ((0 : ℂ → ℂ) ∘ (chartAt ℂ y)) = (fun _ : X => (0 : ℂ)) from rfl] at h_compose
    exact h_compose
  · intro h_mfd
    -- Reverse: `f =ᶠ[𝓝[≠] y] 0` on manifold ⇒ chart side ⇒ chart order = ⊤.
    have h_chart_mero : MeromorphicAt (f ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) :=
      hf y trivial
    -- Pull the manifold-side EvEq through `chart.symm` to the chart side.
    have h_chart_evEq : (f ∘ (chartAt ℂ y).symm) =ᶠ[𝓝[≠] ((chartAt ℂ y) y)]
        ((fun _ : X => (0 : ℂ)) ∘ (chartAt ℂ y).symm) :=
      (chartSymm_tendsto_nhdsNE y).eventually h_mfd
    have h_zero_unfold :
        ((fun _ : X => (0 : ℂ)) ∘ (chartAt ℂ y).symm) = (fun _ : ℂ => (0 : ℂ)) := rfl
    rw [h_zero_unfold] at h_chart_evEq
    show meromorphicOrderAt (f ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) = ⊤
    exact meromorphicOrderAt_eq_top_iff.mpr h_chart_evEq

/-- `mmeromorphicOrderAt f y ≠ ⊤` is equivalent to `f` being eventually
nonzero on a punctured neighborhood of `y` (manifold side). -/
lemma mmeromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (f : X → ℂ) (hf : MMeromorphicOn 𝓘(ℂ, ℂ) f Set.univ) (y : X) :
    mmeromorphicOrderAt 𝓘(ℂ, ℂ) f y ≠ ⊤ ↔ ∀ᶠ z in 𝓝[≠] y, f z ≠ 0 := by
  constructor
  · intro h_ne_top
    have h_chart_mero : MeromorphicAt (f ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) :=
      hf y trivial
    have h_chart_neZero : ∀ᶠ z in 𝓝[≠] ((chartAt ℂ y) y),
        (f ∘ (chartAt ℂ y).symm) z ≠ 0 :=
      (meromorphicOrderAt_ne_top_iff_eventually_ne_zero h_chart_mero).mp h_ne_top
    have h_compose : ∀ᶠ z in 𝓝[≠] y, (f ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) z) ≠ 0 :=
      (chart_tendsto_nhdsNE y).eventually h_chart_neZero
    have h_src_mem : (chartAt ℂ y).source ∈ 𝓝[≠] y :=
      nhdsWithin_le_nhds
        ((chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y))
    filter_upwards [h_compose, h_src_mem] with z hz hz_src
    show f z ≠ 0
    have h_inv : f ((chartAt ℂ y).symm ((chartAt ℂ y) z)) = f z := by
      rw [(chartAt ℂ y).left_inv hz_src]
    rw [← h_inv]; exact hz
  · intro h_evNeZero h_top
    have h_evZero : f =ᶠ[𝓝[≠] y] (fun _ => 0) :=
      (mmeromorphicOrderAt_eq_top_iff_eventually_eq_zero f hf y).mp h_top
    haveI := nhdsNE_neBot y
    rcases (h_evNeZero.and h_evZero).exists with ⟨_, hne, heq⟩
    exact hne heq

/-- **Openness** of the essentially-zero set. If `f` is essentially zero
at `y₀`, then on a full open neighborhood of `y₀` every point is also
essentially zero. -/
lemma essentiallyZero_set_isOpen
    (f : X → ℂ) (hf : MMeromorphicOn 𝓘(ℂ, ℂ) f Set.univ) :
    IsOpen {y : X | mmeromorphicOrderAt 𝓘(ℂ, ℂ) f y = ⊤} := by
  rw [isOpen_iff_mem_nhds]
  intro y₀ hy₀
  -- `hy₀ : mmeromorphicOrderAt f y₀ = ⊤`.
  have h_mfd_zero : f =ᶠ[𝓝[≠] y₀] (fun _ => 0) :=
    (mmeromorphicOrderAt_eq_top_iff_eventually_eq_zero f hf y₀).mp hy₀
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff] at h_mfd_zero
  -- `h_mfd_zero : ∀ᶠ z in 𝓝 y₀, z ∈ {y₀}ᶜ → f z = 0`.
  rcases mem_nhds_iff.mp h_mfd_zero with ⟨V, hV_sub, hV_open, hV_mem⟩
  -- `hV_sub : V ⊆ {z | z ≠ y₀ → f z = 0}`, `hV_open : IsOpen V`, `hV_mem : y₀ ∈ V`.
  apply Filter.mem_of_superset (hV_open.mem_nhds hV_mem)
  intro z hz
  by_cases hzy : z = y₀
  · -- z = y₀: hypothesis gives `mmeromorphicOrderAt f y₀ = ⊤`.
    rw [hzy]; exact hy₀
  · -- z ≠ y₀: f ≡ 0 on V \ {y₀}, which is an open nhd of z (since y₀ closed in T2).
    -- Build the punctured-nhd `=ᶠ 0` for z.
    have h_z_evZero : f =ᶠ[𝓝[≠] z] (fun _ : X => (0 : ℂ)) := by
      have h_V_minus_y_open : IsOpen (V \ {y₀}) := hV_open.sdiff isClosed_singleton
      have h_z_mem : z ∈ V \ {y₀} := ⟨hz, by simp [hzy]⟩
      have h_full : ∀ᶠ z' in 𝓝 z, f z' = 0 := by
        filter_upwards [h_V_minus_y_open.mem_nhds h_z_mem] with z' hz'
        exact hV_sub hz'.1 hz'.2
      exact h_full.filter_mono nhdsWithin_le_nhds
    show mmeromorphicOrderAt 𝓘(ℂ, ℂ) f z = ⊤
    exact (mmeromorphicOrderAt_eq_top_iff_eventually_eq_zero f hf z).mpr h_z_evZero

/-- **Closedness** of the essentially-zero set, i.e., openness of the
complement (the "essentially-nonzero" set). -/
lemma essentiallyZero_set_isClosed
    (f : X → ℂ) (hf : MMeromorphicOn 𝓘(ℂ, ℂ) f Set.univ) :
    IsClosed {y : X | mmeromorphicOrderAt 𝓘(ℂ, ℂ) f y = ⊤} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y₀ hy₀
  -- `hy₀ : y₀ ∉ S`, i.e. `mmeromorphicOrderAt f y₀ ≠ ⊤`.
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hy₀
  -- Eventually-nonzero punctured nhd at y₀.
  have h_evNeZero : ∀ᶠ z in 𝓝[≠] y₀, f z ≠ 0 :=
    (mmeromorphicOrderAt_ne_top_iff_eventually_ne_zero f hf y₀).mp hy₀
  rw [eventually_nhdsWithin_iff] at h_evNeZero
  rcases mem_nhds_iff.mp h_evNeZero with ⟨V, hV_sub, hV_open, hV_mem⟩
  -- `hV_sub : V ⊆ {z | z ≠ y₀ → f z ≠ 0}`.
  apply Filter.mem_of_superset (hV_open.mem_nhds hV_mem)
  intro z hz
  show z ∈ {y : X | mmeromorphicOrderAt 𝓘(ℂ, ℂ) f y = ⊤}ᶜ
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
  by_cases hzy : z = y₀
  · rw [hzy]; exact hy₀
  · -- z ≠ y₀: on V \ {y₀} (open nhd of z), f is nonzero. So f eventually ≠ 0 on 𝓝[≠] z.
    have h_z_evNeZero : ∀ᶠ z' in 𝓝[≠] z, f z' ≠ 0 := by
      have h_V_minus_y_open : IsOpen (V \ {y₀}) := hV_open.sdiff isClosed_singleton
      have h_z_mem : z ∈ V \ {y₀} := ⟨hz, by simp [hzy]⟩
      have h_full : ∀ᶠ z' in 𝓝 z, f z' ≠ 0 := by
        filter_upwards [h_V_minus_y_open.mem_nhds h_z_mem] with z' hz'
        exact hV_sub hz'.1 hz'.2
      exact h_full.filter_mono nhdsWithin_le_nhds
    exact (mmeromorphicOrderAt_ne_top_iff_eventually_ne_zero f hf z).mpr h_z_evNeZero

/-- **Identity theorem** on a connected complex 1-manifold: if a globally
meromorphic function `f` is not essentially zero at some point, then it
is not essentially zero at any point. -/
theorem mmeromorphicOrderAt_ne_top_forall
    [ConnectedSpace X]
    (f : X → ℂ) (hf : MMeromorphicOn 𝓘(ℂ, ℂ) f Set.univ)
    (h_exists : ∃ y, mmeromorphicOrderAt 𝓘(ℂ, ℂ) f y ≠ ⊤) :
    ∀ y, mmeromorphicOrderAt 𝓘(ℂ, ℂ) f y ≠ ⊤ := by
  set S : Set X := {y | mmeromorphicOrderAt 𝓘(ℂ, ℂ) f y = ⊤} with hS
  have h_open : IsOpen S := essentiallyZero_set_isOpen f hf
  have h_closed : IsClosed S := essentiallyZero_set_isClosed f hf
  have h_clopen : IsClopen S := ⟨h_closed, h_open⟩
  obtain ⟨y₀, hy₀⟩ := h_exists
  have hy₀_not : y₀ ∉ S := hy₀
  -- On a connected space, a clopen set is empty or universal.
  rcases isClopen_iff.mp h_clopen with h_empty | h_univ
  · intro y hy_in_S
    have h_yS : y ∈ S := hy_in_S
    rw [h_empty] at h_yS
    exact h_yS.elim
  · exfalso
    apply hy₀_not
    show y₀ ∈ S
    rw [h_univ]; trivial

end JacobianChallenge.MeromorphicFunctionField

/-! ## `Field` instance via `mul_inv_cancel`

Given `[f] ≠ [0]`, the identity theorem shows `mmeromorphicOrderAt f y
≠ ⊤` everywhere, hence the set of `y` where `f y = 0` or `f` has a pole
is locally finite. On a punctured nhd of every `y`, the pointwise product
`f * f⁻¹` is `1` (avoiding the locally finite bad set). This gives
`[f] * [f]⁻¹ = [1]` by descent. -/

namespace JacobianChallenge.MeromorphicFunctionField

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- Helper: under `[f] ≠ [0]`, there exists some `y` where
`mmeromorphicOrderAt f y ≠ ⊤`. -/
private lemma exists_ne_top_of_germ_ne_zero
    {f : MMer X}
    (h_ne : (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm X) ≠ 0) :
    ∃ y, mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y ≠ ⊤ := by
  by_contra h_all_top
  push_neg at h_all_top
  apply h_ne
  show (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm X)
      = MeromorphicFunctionGerm.mk (0 : MMer X)
  apply Quotient.sound
  intro y
  show f.toFun =ᶠ[𝓝[≠] y] (0 : MMer X).toFun
  have h_zero_unfold : (0 : MMer X).toFun = (fun _ : X => (0 : ℂ)) := rfl
  rw [h_zero_unfold]
  exact (mmeromorphicOrderAt_eq_top_iff_eventually_eq_zero f.toFun f.mmero y).mp
    (h_all_top y)

/-- On a punctured nhd of any `y`, the pointwise product `f * f⁻¹` is the
constant `1`, provided `f` is everywhere non-essentially-zero. -/
private lemma mul_inv_pointwise_eq_one_punctured
    {f : MMer X}
    (h_all_ne_top : ∀ y, mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y ≠ ⊤) (y : X) :
    (fun z => f.toFun z * (f.toFun z)⁻¹) =ᶠ[𝓝[≠] y] (fun _ => (1 : ℂ)) := by
  -- Eventually `f z ≠ 0` on `𝓝[≠] y` by `mmeromorphicOrderAt_ne_top_iff_eventually_ne_zero`.
  have h_evNeZero : ∀ᶠ z in 𝓝[≠] y, f.toFun z ≠ 0 :=
    (mmeromorphicOrderAt_ne_top_iff_eventually_ne_zero f.toFun f.mmero y).mp
      (h_all_ne_top y)
  filter_upwards [h_evNeZero] with z hz
  show f.toFun z * (f.toFun z)⁻¹ = 1
  field_simp

/-- `[f] * [f]⁻¹ = [1]` whenever `[f] ≠ [0]`. -/
private lemma mul_inv_cancel_germ
    {f : MMer X}
    (h_ne : (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm X) ≠ 0) :
    (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm X)
        * (MeromorphicFunctionGerm.mk f)⁻¹
      = 1 := by
  obtain ⟨_, h_exists⟩ := exists_ne_top_of_germ_ne_zero h_ne
  have h_all_ne_top : ∀ y, mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y ≠ ⊤ :=
    mmeromorphicOrderAt_ne_top_forall f.toFun f.mmero ⟨_, h_exists⟩
  show MeromorphicFunctionGerm.mk (f * f⁻¹) = MeromorphicFunctionGerm.mk (1 : MMer X)
  apply Quotient.sound
  intro y
  show (f.toFun * f.toFun⁻¹) =ᶠ[𝓝[≠] y] (1 : MMer X).toFun
  have h_one_unfold : (1 : MMer X).toFun = (fun _ : X => (1 : ℂ)) := rfl
  rw [h_one_unfold]
  -- `f.toFun * f.toFun⁻¹ = fun z => f.toFun z * (f.toFun z)⁻¹` (Pi.mul_apply + Pi.inv_apply).
  have h_pi : (f.toFun * f.toFun⁻¹) = (fun z => f.toFun z * (f.toFun z)⁻¹) := rfl
  rw [h_pi]
  exact mul_inv_pointwise_eq_one_punctured h_all_ne_top y

/-- `[0]⁻¹ = [0]`: definitional, since the pointwise inverse of the zero
function is the zero function (`0⁻¹ = 0` in `ℂ`). -/
private lemma inv_zero_germ :
    ((0 : MeromorphicFunctionGerm X)⁻¹) = 0 := by
  show MeromorphicFunctionGerm.mk ((0 : MMer X)⁻¹)
      = MeromorphicFunctionGerm.mk (0 : MMer X)
  apply Quotient.sound
  apply forall_pw_eventuallyEq_of_funext
  funext z
  show ((0 : MMer X).toFun z)⁻¹ = (0 : MMer X).toFun z
  show ((0 : X → ℂ) z)⁻¹ = (0 : X → ℂ) z
  simp

/-- Nontriviality: `[0] ≠ [1]`. -/
private lemma zero_ne_one_germ :
    (0 : MeromorphicFunctionGerm X) ≠ 1 := by
  intro h_eq
  -- From `[0] = [1]`, derive a contradiction via `Quotient.exact`.
  have h_rel := Quotient.exact (s := germSetoid X) h_eq
  -- `h_rel : ∀ y, (0 : MMer X).toFun =ᶠ[𝓝[≠] y] (1 : MMer X).toFun`.
  -- On any punctured nhd, `0 = 1` in ℂ — contradiction (provided nhdsNE is non-trivial).
  -- Pick any y (X is nonempty since ConnectedSpace ⇒ Nonempty).
  haveI : Nonempty X := inferInstance
  obtain ⟨y⟩ := ‹Nonempty X›
  have h_y : (0 : MMer X).toFun =ᶠ[𝓝[≠] y] (1 : MMer X).toFun := h_rel y
  haveI := nhdsNE_neBot y
  rcases h_y.exists with ⟨_, hz⟩
  exact zero_ne_one hz

/-- The full `Field` instance, descended from pointwise operations and
the identity-theorem-driven `mul_inv_cancel`. -/
noncomputable instance : Field (MeromorphicFunctionGerm X) where
  __ := (inferInstance : CommRing (MeromorphicFunctionGerm X))
  inv := Inv.inv
  mul_inv_cancel := by
    rintro ⟨f⟩ hf
    exact mul_inv_cancel_germ hf
  inv_zero := inv_zero_germ
  nnqsmul := _
  qsmul := _
  nnratCast_def := by intro q; rfl
  ratCast_def := by intro q; rfl
  exists_pair_ne := ⟨0, 1, zero_ne_one_germ⟩

end JacobianChallenge.MeromorphicFunctionField

end
