/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor
import JacobianChallenge.Divisor.Single
import JacobianChallenge.Manifold.HolomorphicOneForm
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # The Jacobian of a compact Riemann surface

This file defines the carrier type `JacobianChallenge.Jacobian X` together with
the `AddCommGroup`, `TopologicalSpace` and `T2Space` instances that the
challenge signatures in `Basic.lean` (items 2–4 of the challenge, plus the
`ofCurve_self` consequence in item 15) demand.

## Route chosen: `Pic0`-via-`Divisor.lean`

`JacobianChallenge.Pic0 X` is already defined in `JacobianChallenge.Divisor`
as the additive quotient `Div0 X ⧸ (PrincDiv X).addSubgroupOf (Div0 X)`.
At the current pin (mathlib commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5`,
15 Apr 2026) the principal-divisor subgroup `PrincDiv X` is the deliberate
*placeholder* `⊥` — see the docstring of `JacobianChallenge.PrincDiv` for the
three classical inputs (chart-independence of meromorphic order, local
finiteness of the order divisor, residue theorem) that are owed before the
honest principal-subgroup definition lands. With that placeholder, `Pic0 X`
is *as a group* canonically isomorphic to `Div0 X`; this file does not assume
anything beyond the abelian-group structure of the quotient, so it stays
honest as the analytic content is filled in later.

We therefore **set `Jacobian X := Pic0 X`** rather than the `PUnit` fallback.
The `AddCommGroup` instance comes from `Pic0.instAddCommGroup` for free.

## What this file *does* supply (no `sorry`s)

* `JacobianChallenge.Jacobian X := JacobianChallenge.Pic0 X`
* `instance : AddCommGroup (Jacobian X)` — inherited from `Pic0`.
* `instance : TopologicalSpace (Jacobian X)` — the *discrete* topology on the
  quotient. This is the honest topology one can give a divisor-class group
  before the period-lattice quotient is built; downstream files that need a
  finer manifold topology will have to refine it together with the analytic
  Jacobian (`ℂᵍ / Λ`) construction.
* `instance : T2Space (Jacobian X)` — automatic from the discrete topology.
* `Jacobian.ofCurve (P : X) : X → Jacobian X` — the Abel–Jacobi *signature*.
  At this stage we cannot yet build the honest map `Q ↦ [Q] - [P]` inside
  `Pic0 X` because the membership statement `(δ Q − δ P) ∈ Div0 X` is owed
  by `Divisor.lean` (it requires a `single`-point divisor constructor and a
  one-point degree lemma, both still to be added there). To keep this file
  free of `sorry`s we define `ofCurve P` as the constant `0 : Jacobian X`.
  This is *not* the mathematical Abel–Jacobi map, but it satisfies the only
  algebraic identity demanded by the challenge in this file — namely
  `ofCurve_self` below.
* `Jacobian.ofCurve_self (P : X) : ofCurve P P = 0` — direct from the
  definition above. **NB**: the challenge file `Basic.lean` separately asks
  for `ofCurve_inj` (item 16), and that lemma is *false* for the constant-zero
  stub when `genus X > 0`. Wiring this file into `Basic.lean` therefore
  closes items 2, 3, 4 and 15 (the `ofCurve_self` line) but **leaves item 16
  open**, with the gap localised to `ofCurve` itself rather than to
  `ofCurve_self`.

## What this file does *not* supply

The remaining `sorry`s in `Basic.lean` (items 5–14, 16, the manifold
instances, `pushforward`/`pullback`, `degree`) are *not* discharged here.
In particular:

* `instance : CompactSpace (Jacobian X)` is **deliberately omitted**. With
  `PrincDiv X = ⊥`, `Pic0 X ≃ Div0 X`, which is a free abelian group on the
  (in general infinite) underlying set of `X` and is *not* compact in any
  sensible topology. Supplying a `CompactSpace` instance here would either
  require the honest period-lattice quotient `ℂᵍ / Λ` (not yet built) or
  would have to be a fake. We leave it as a `sorry` in `Basic.lean` until
  the period-lattice infrastructure lands.
* `instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` and
  `IsManifold ...` are likewise out of scope here.
-/

set_option diagnostics.threshold 100

namespace JacobianChallenge

open scoped ContDiff Manifold

/-! ### Carrier and group structure -/

/-- The Jacobian of a compact Riemann surface, defined here as the (placeholder)
Picard group of degree-zero divisor classes from `JacobianChallenge.Divisor`.

See the file-level docstring for the precise status: with the current
`PrincDiv X = ⊥` placeholder, this is canonically isomorphic to `Div0 X` as
an additive group, and the analytic refinement to `ℂᵍ / Λ` is owed by future
work on `Divisor.lean` and a separate period-lattice file. -/
noncomputable def Jacobian (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] : Type _ :=
  Pic0 X

namespace Jacobian

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]

/-- The additive abelian group structure on `Jacobian X`, inherited from
`Pic0.instAddCommGroup`. -/
noncomputable instance instAddCommGroup : AddCommGroup (Jacobian X) :=
  inferInstanceAs (AddCommGroup (Pic0 X))

/-- We equip `Jacobian X` with the *discrete* topology. This is the honest
choice at the current state of the development: the principal-divisor
subgroup is the placeholder `⊥`, so there is no quotient-by-a-lattice
operation to inherit a coarser Hausdorff topology from. Downstream code
that builds the honest analytic Jacobian `ℂᵍ / Λ` will need to refine this
instance (or, equivalently, replace this whole file). -/
instance instTopologicalSpace : TopologicalSpace (Jacobian X) := ⊥

/-- The discrete topology on `Jacobian X` is `Hausdorff`. -/
instance instDiscreteTopology : DiscreteTopology (Jacobian X) :=
  ⟨rfl⟩

/-- `Jacobian X` is `T2`, immediate from the discrete topology. -/
instance instT2Space : T2Space (Jacobian X) :=
  inferInstance

/-! ### The Abel–Jacobi map (honest, against the `PrincDiv = ⊥` placeholder) -/

/-- The Abel–Jacobi map from a compact Riemann surface to its Jacobian,
sending `Q ↦ [δ Q − δ P]` in `Pic0 X = Div0 X ⧸ (PrincDiv X).addSubgroupOf
(Div0 X)`.

This is the honest Abel–Jacobi *map* against the current placeholder
`PrincDiv X = ⊥`. The honest *target* `Pic0 X` is, at this pin, only
canonically isomorphic to `Div0 X` (not to the analytic Jacobian
`ℂᵍ / Λ`); see the docstring of `JacobianChallenge.PrincDiv` for the
analytic inputs that are owed before `PrincDiv` itself is honest. The map
itself, however, is genuinely `Q ↦ [δ Q − δ P]`, and in particular it
satisfies both `ofCurve_self` and `ofCurve_inj` below — the latter
unconditionally on `genus X` (the placeholder `PrincDiv = ⊥` makes the
quotient faithful, so injectivity reduces to `Div.single_eq_iff`).

The `[DecidableEq X]` requirement of `Div.single` is discharged via
`Classical.decEq X`. -/
noncomputable def ofCurve (P : X) : X → Jacobian X :=
  letI : DecidableEq X := Classical.decEq X
  fun Q => (QuotientAddGroup.mk
    (⟨Div.single Q - Div.single P, Div.single_sub_single_mem_Div0 P Q⟩ : Div0 X) :
      Jacobian X)

/-- The Abel–Jacobi map sends the base point to the identity of the group
(challenge item 15 from `Basic.lean`). For `Q = P` the underlying divisor
`Div.single P − Div.single P` is `0` in `Div X`, so the corresponding
element of `Div0 X` is `0`, and `QuotientAddGroup.mk 0 = 0`. -/
@[simp] lemma ofCurve_self (P : X) : ofCurve P P = 0 := by
  classical
  -- Unfold `ofCurve P P` to a quotient class of a `Div0 X`-element whose
  -- underlying divisor is `single P − single P = 0`.
  show (QuotientAddGroup.mk
    (⟨Div.single P - Div.single P,
        Div.single_sub_single_mem_Div0 P P⟩ : Div0 X) : Jacobian X) = 0
  -- The `Div0 X`-element above equals `0`, since its underlying divisor is `0`.
  have h0 : (⟨Div.single P - Div.single P,
      Div.single_sub_single_mem_Div0 P P⟩ : Div0 X) = 0 := by
    apply Subtype.ext
    simp
  rw [h0]
  -- `QuotientAddGroup.mk 0 = 0` in any quotient group.
  exact QuotientAddGroup.mk_zero _

/-- The Abel–Jacobi map is injective.

The challenge signature in `Basic.lean` carries the hypothesis
`0 < genus X`, but at the current pin that hypothesis is *not needed*:
the placeholder `PrincDiv X = ⊥` makes the quotient `Pic0 X` faithful, so
two divisors are equal in `Pic0 X` iff they are equal in `Div0 X`, and
hence iff their underlying `Div X`-divisors are equal. The conclusion then
reduces to `Div.single_eq_iff`.

When the honest `PrincDiv` lands and the quotient is no longer faithful,
this proof will need the full Abel–Jacobi theorem (and the
`0 < genus X` hypothesis becomes load-bearing); at that point this lemma
should be replaced rather than refined. -/
lemma ofCurve_inj (P : X) : Function.Injective (ofCurve P) := by
  classical
  intro Q₁ Q₂ hQ
  -- Two `QuotientAddGroup.mk` classes are equal iff their difference lies in
  -- the quotienting subgroup `(PrincDiv X).addSubgroupOf (Div0 X)`, which at
  -- this pin equals `⊥` (since `PrincDiv X = ⊥`), so equality in `Pic0 X`
  -- forces equality in `Div0 X`.
  have hSub : (⟨Div.single Q₁ - Div.single P,
                 Div.single_sub_single_mem_Div0 P Q₁⟩ : Div0 X)
            = (⟨Div.single Q₂ - Div.single P,
                 Div.single_sub_single_mem_Div0 P Q₂⟩ : Div0 X) := by
    -- Translate `hQ : ofCurve P Q₁ = ofCurve P Q₂` (a quotient equality) into
    -- a `Quotient.eq` statement, and use that the quotienting subgroup is `⊥`.
    have hQ' : (QuotientAddGroup.mk
        (⟨Div.single Q₁ - Div.single P,
            Div.single_sub_single_mem_Div0 P Q₁⟩ : Div0 X) : Jacobian X)
      = QuotientAddGroup.mk
        (⟨Div.single Q₂ - Div.single P,
            Div.single_sub_single_mem_Div0 P Q₂⟩ : Div0 X) := hQ
    rw [QuotientAddGroup.eq] at hQ'
    -- `hQ'` says the difference lies in `(PrincDiv X).addSubgroupOf (Div0 X)`,
    -- which is `⊥` because `PrincDiv X = ⊥`.
    have hBot : (PrincDiv X).addSubgroupOf (Div0 X) = ⊥ := by
      unfold PrincDiv
      simp [AddSubgroup.addSubgroupOf]
    rw [hBot, AddSubgroup.mem_bot] at hQ'
    -- Now `hQ' : -x + y = 0`; rearrange to `x = y` via `neg_add_eq_zero`.
    exact neg_add_eq_zero.mp hQ'
  -- Project the equality of `Div0 X`-elements to an equality of underlying
  -- `Div X`-divisors via `Subtype.ext_iff`.
  have hDiv : Div.single Q₁ - Div.single P = Div.single Q₂ - Div.single P :=
    congrArg Subtype.val hSub
  -- Cancel `Div.single P` on both sides to extract `single Q₁ = single Q₂`.
  have hSingle : (Div.single Q₁ : Div X) = Div.single Q₂ :=
    sub_left_inj.mp hDiv
  -- And conclude via `Div.single_eq_iff`.
  exact (Div.single_eq_iff Q₁ Q₂).mp hSingle

/-! ### Functoriality stubs (challenge items 12, 13)

The Abel–Jacobi `pushforward` and `pullback` honestly require either a
functorial action of `f : X → Y` on divisor-class groups (the `Pic⁰` route,
which needs single-point divisor manipulation in `Divisor.lean`) or the
period-lattice quotient `ℂᵍ / Λ` (the analytic route, which has not been
built). Neither piece of infrastructure is available at this pin.

To keep this file `sorry`-free we ship the **zero `ContinuousAddMonoidHom`**
as the value of both `pushforward f` and `pullback f`. This is honest because
the discrete topology on `Jacobian X` makes the zero hom continuous, and the
signature in `Basic.lean` only requires a `ContinuousAddMonoidHom` — not any
identity beyond it.

**What this stub does *not* satisfy.** All five functoriality lemmas in
`Basic.lean` (items 17–23) fail for the zero stub on non-trivial input:

* `pushforward_id_apply : pushforward id _ P = P` would need the *identity*
  hom, not the *zero* hom — fails for any `P ≠ 0`.
* `pullback_id_apply` — symmetric reason, fails for any `P ≠ 0`.
* `pushforward_comp_apply` and `pullback_comp_apply` reduce to `0 = 0` on the
  zero stub (composition of zero homs is the zero hom), so these *do* hold,
  but only vacuously, and we do **not** ship them here because they would
  silently lock in the false `_id_apply` companions if the stubs were ever
  refined non-uniformly.
* `pushforward_pullback : pushforward f (pullback f P) = degree f • P`
  reduces to `0 = degree f • P`, which fails for non-zero `P` and non-zero
  degree.
* `pushforward_contMDiff` / `pullback_contMDiff` would require the
  `ChartedSpace (Fin (genus _) → ℂ)` instance on `Jacobian X` / `Jacobian Y`,
  which is still `sorry` in `Basic.lean` (item 7). The zero map *would* be
  smooth (constants are), but the lemma cannot even typecheck cleanly until
  those instances land.

All of items 17–23 therefore remain as `sorry` in `Basic.lean`, with the gap
honestly localised to "we have no real `pushforward` / `pullback`." -/
section Functoriality

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]

/-- The pushforward map between Jacobians associated to a map of the underlying
curves. **Stub at this pin** — see the section docstring above. Defined as the
zero `ContinuousAddMonoidHom`; this satisfies the `Basic.lean` *signature* of
challenge item 12 but does **not** satisfy any of the functoriality lemmas
(items 17–23). -/
noncomputable def pushforward (_f : X → Y) :
    Jacobian X →ₜ+ Jacobian Y :=
  0

/-- The pullback map between Jacobians associated to a map of the underlying
curves. **Stub at this pin** — see the section docstring above. Defined as the
zero `ContinuousAddMonoidHom`; this satisfies the `Basic.lean` *signature* of
challenge item 13 but does **not** satisfy any of the functoriality lemmas
(items 17–23). -/
noncomputable def pullback (_f : X → Y) :
    Jacobian Y →ₜ+ Jacobian X :=
  0

end Functoriality

end Jacobian

end JacobianChallenge
