/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicAt
import JacobianChallenge.Manifold.MeromorphicDivisor
import JacobianChallenge.Manifold.LocalMultiplicity
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.Order

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Local normal form for analytic / meromorphic maps and local multiplicity

This file lays the framework for the **(R3) local-multiplicity = local-order**
gap of `Manifold/ResidueTheorem.lean`. The classical statement is:

> Let `f : X → ℂ` be meromorphic at `x : X` on a complex manifold, and let
> `k := (mmeromorphicOrderAt I f x).untop₀` be the chart-pulled-back integer
> order. Then in any chart at `x`, the function `f ∘ chart⁻¹` admits the
> local normal form
>
>   `(f ∘ chart⁻¹)(z) = (z - chart x) ^ k • g(z)`
>
> for some analytic `g` with `g (chart x) ≠ 0` (interpreting `k < 0` as the
> meromorphic-power case `(z - chart x) ^ (k : ℤ)`).
>
> Consequently the *topological local multiplicity* of `f` at `x` (cardinality
> of `f⁻¹{w}` near `x` for `w` near `f x`, in the analytic case) equals
> `k.natAbs`.

## Status: framework + chart-coordinate proof

What is **proven** in this file:

1. `localOrder I f x : ℤ` — a structural rename of
   `MMeromorphicOn.orderFun I f x`. Definitionally equal; serves as the named
   replacement for the `degreeStub` indicator in `LocalMultiplicity.lean`.
2. `localOrder_eq_orderFun` — the structural identity.
3. `localOrder_eq_zero_iff` — under the no-germ-zero hypothesis, vanishing
   of `localOrder` matches vanishing of `mmeromorphicOrderAt`.
4. **`MMeromorphicAt.exists_local_normal_form`** — the *honest* local-form
   theorem in chart coordinates. For `f` meromorphic at `x` with finite
   order `k`, the chart representative `f ∘ chart⁻¹` admits the form
   `(z - chart x) ^ k • g(z)` for some analytic `g` with `g(chart x) ≠ 0`,
   on a punctured neighborhood. **Proof: direct application of the mathlib
   lemma `meromorphicOrderAt_eq_int_iff`.** Zero `sorry`.
5. **`MMeromorphicAt.exists_local_normal_form_of_nonneg`** — the analytic
   case (`k ≥ 0`) strengthens the punctured neighborhood to a full
   neighborhood (no zero-divisor singularity to remove).

What is **stated but not proven** here:

6. `localMultiplicity_eq_localOrder_statement` — the headline
   `Prop`-valued `def` matching the brief. It packages the connection between
   `localOrder` and the topological local multiplicity (cardinality of
   `f⁻¹{w}` near `x` for `w` near `f x`). Discharging this requires the
   Rouché-style argument that `(z - x₀) ^ k · u(z) = w` has exactly `k`
   solutions near `x₀` for `w` near `0` (when `u(x₀) ≠ 0`). That argument
   is not in mathlib at the pin; it is owed from a future
   `Mathlib.Analysis.SpecialFunctions.Complex.LocalMultiplicity` (does not
   exist).

The file is therefore **the rails for R3**: definitions, structural
identities, and the chart-coordinate local-form theorem, all proven; the
topological-multiplicity bridge stated as a `Prop`-valued `def` (NOT an
`axiom`) so future filling does not contaminate the kernel.

## Owed mathlib lemmas (catalogued for the next pass)

The following mathlib names are what the eventual filling will route through:

* `AnalyticAt.analyticOrderAt_eq_natCast`
  — `Mathlib/Analysis/Analytic/Order.lean`. The analytic local form
  `f z = (z - z₀) ^ n • g z` for analytic `f` with order `n : ℕ`.
* `meromorphicOrderAt_eq_int_iff`
  — `Mathlib/Analysis/Meromorphic/Order.lean`. The meromorphic local form
  `f z = (z - x) ^ n • g z` (with `n : ℤ`) on the punctured neighborhood.
* `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`
  — `Mathlib/Analysis/Analytic/IsolatedZeros.lean`. The existence side of
  the analytic decomposition (used in the proof of (4) above via
  `meromorphicOrderAt_eq_int_iff`).
* `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`
  — companion isolated-zeros lemma; not invoked here but useful for the
  topological-multiplicity discharge.

The topological-multiplicity discharge (Rouché-via-degree-theory) will need
an argument analogous to mathlib's
`Complex.exists_count_preimage_of_eq_pow` (does not exist at the pin) or
the Rouché theorem applied to `f(z) - w = (z - x₀)^k u(z) - w`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace JacobianChallenge

universe u

/-! ## The structural local-order definition

`localOrder I f x` is the integer-valued local order of `f` at `x`,
expressed as the chart-pulled-back `mmeromorphicOrderAt` cast through
`WithTop.untop₀` (positive at zeros, negative at poles, `0` at regular
nonzero points and at germ-zero points).

This is **definitionally equal** to `MMeromorphicOn.orderFun I f x` from
`Manifold/MeromorphicDivisor.lean` — we just give it the structural name
that `R3_localMultiplicity_statement` in `Manifold/ResidueTheorem.lean`
should ultimately route through. -/

/-- The **integer-valued local order** of `f : X → ℂ` at `x : X`, computed
via the chart-pullback `mmeromorphicOrderAt`. -/
def localOrder
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    (I : ModelWithCorners ℂ ℂ ℂ) (f : X → ℂ) (x : X) : ℤ :=
  MMeromorphicOn.orderFun I f x

/-- `localOrder` is exactly the underlying `orderFun` — structural identity. -/
@[simp] lemma localOrder_eq_orderFun
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    (I : ModelWithCorners ℂ ℂ ℂ) (f : X → ℂ) (x : X) :
    localOrder I f x = MMeromorphicOn.orderFun I f x := rfl

/-- Unfolded form: `localOrder` is the `WithTop.untop₀` of the meromorphic
order at `x`. -/
lemma localOrder_eq_untop₀
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    (I : ModelWithCorners ℂ ℂ ℂ) (f : X → ℂ) (x : X) :
    localOrder I f x = (mmeromorphicOrderAt I f x).untop₀ := rfl

/-- Under the no-germ-zero hypothesis, `localOrder I f x = 0` iff
`mmeromorphicOrderAt I f x = 0` (no spurious `⊤ ↦ 0` collapse).

Inlined (rather than delegated to `MMeromorphicOn.orderFun_eq_zero_iff`)
because the latter carries a spurious `[IsManifold ...]` dependency from
its enclosing `variable` block; the statement here is purely about
`WithTop ℤ.untop₀` and needs no manifold structure. -/
lemma localOrder_eq_zero_iff
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {I : ModelWithCorners ℂ ℂ ℂ} {f : X → ℂ} {x : X}
    (hf0 : mmeromorphicOrderAt I f x ≠ ⊤) :
    localOrder I f x = 0 ↔ mmeromorphicOrderAt I f x = 0 := by
  change (mmeromorphicOrderAt I f x).untop₀ = 0 ↔ _
  constructor
  · intro h
    rcases WithTop.untop₀_eq_zero.mp h with h0 | htop
    · exact h0
    · exact (hf0 htop).elim
  · intro h
    rw [h]; rfl

/-! ## The chart-coordinate local normal form

The honest content. We invoke the mathlib lemma `meromorphicOrderAt_eq_int_iff`
to extract the local form `f(z) = (z - x₀) ^ k • g(z)` on a punctured
neighborhood, with `g` analytic and `g(x₀) ≠ 0`. -/

namespace MMeromorphicAt

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {I : ModelWithCorners ℂ ℂ ℂ} {f : X → ℂ} {x : X}

/-- **Local normal form for a meromorphic function in chart coordinates.**

For `f : X → ℂ` meromorphic at `x : X` on a complex chart, with finite
chart-pullback order `k = (mmeromorphicOrderAt I f x).untop₀`, the chart
representative `f ∘ (chartAt ℂ x).symm` admits the local form

  `(f ∘ chart⁻¹)(z) = (z - (chartAt ℂ x) x) ^ k • g(z)`

for some analytic `g` with `g ((chartAt ℂ x) x) ≠ 0`, on a punctured
neighborhood of `(chartAt ℂ x) x`.

This is the **chart-coordinate** version of R3. The R3 statement in
`ResidueTheorem.lean` further requires extracting the *topological*
multiplicity (cardinality of preimages); that step is owed from a
mathlib-side Rouché argument and is captured as
`localMultiplicity_eq_localOrder_statement` below.

Proof: direct application of `meromorphicOrderAt_eq_int_iff`. -/
theorem exists_local_normal_form
    (hf : MMeromorphicAt I f x)
    (hf0 : mmeromorphicOrderAt I f x ≠ ⊤) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g ((chartAt ℂ x) x) ∧
      g ((chartAt ℂ x) x) ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] ((chartAt ℂ x) x),
        (f ∘ (chartAt ℂ x).symm) z = (z - (chartAt ℂ x) x) ^ localOrder I f x • g z := by
  -- Unfold `MMeromorphicAt` to the underlying flat-domain `MeromorphicAt`.
  have hf' : MeromorphicAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hf
  -- The flat-domain order equals our `localOrder` definitionally
  -- (`localOrder = (mmeromorphicOrderAt I f x).untop₀ = meromorphicOrderAt _ _.untop₀`).
  set k : ℤ := localOrder I f x with hk
  have h_order_ne_top :
      meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ ⊤ := hf0
  -- Express `meromorphicOrderAt _ _ = (k : ℤ)` so we can apply
  -- `meromorphicOrderAt_eq_int_iff`.
  have h_order_eq :
      meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = (k : WithTop ℤ) := by
    -- `k = (mmeromorphicOrderAt I f x).untop₀ = meromorphicOrderAt _ _.untop₀`,
    -- and a `WithTop ℤ` value `≠ ⊤` equals the cast of its `untop₀`.
    change meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) =
      ((meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)).untop₀ : WithTop ℤ)
    exact (WithTop.coe_untop₀_of_ne_top h_order_ne_top).symm
  -- Apply the mathlib characterization.
  exact (meromorphicOrderAt_eq_int_iff hf').mp h_order_eq

/-- **Local normal form for an analytic function in chart coordinates.**

Strengthening of `exists_local_normal_form` to a *full* neighborhood (not
just punctured) when `f` is analytic at the chart image, i.e. when the
order is `≥ 0`. This is the case relevant to `R3` for *zeros* (rather
than poles) of `f`.

Proof: combine the punctured-neighborhood form with continuity of the
right-hand side at `(chartAt ℂ x) x` (where `(z - x₀)^k` is continuous
for `k ≥ 0` and the value at `x₀` is `0` for `k > 0`, matching `f x`). -/
theorem exists_local_normal_form_of_nonneg
    (_hf : MMeromorphicAt I f x)
    (hf0 : mmeromorphicOrderAt I f x ≠ ⊤)
    (hk : 0 ≤ localOrder I f x)
    (hf_an : AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g ((chartAt ℂ x) x) ∧
      g ((chartAt ℂ x) x) ≠ 0 ∧
      ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
        (f ∘ (chartAt ℂ x).symm) z =
          (z - (chartAt ℂ x) x) ^ (localOrder I f x).toNat • g z := by
  -- Step 1: The analytic order equals `(localOrder I f x).toNat`.
  -- Use the analytic-order/meromorphic-order compatibility lemma.
  set k : ℤ := localOrder I f x with hk_def
  set n : ℕ := k.toNat with hn_def
  have h_kn : (k : WithTop ℤ) = ((n : ℤ) : WithTop ℤ) := by
    simp [hn_def, Int.toNat_of_nonneg hk]
  -- The analytic order (`ℕ∞`-valued) equals `n`.
  have h_an_order : analyticOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = (n : ℕ∞) := by
    -- From `AnalyticAt.meromorphicOrderAt_eq` we have
    -- `meromorphicOrderAt = (analyticOrderAt).map (↑)`. Combine with `h_order_eq` from the
    -- meromorphic side.
    have h_mero_eq : meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
        = (analyticOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)).map (↑· : ℕ → ℤ) :=
      hf_an.meromorphicOrderAt_eq
    have h_mero_int : meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
        = (k : WithTop ℤ) := by
      show meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = (k : WithTop ℤ)
      have h_ne_top :
          meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ ⊤ := hf0
      exact (WithTop.coe_untop₀_of_ne_top h_ne_top).symm
    -- Combine: `(analyticOrderAt _).map (↑) = (n : ℤ)` ⟹ `analyticOrderAt _ = n`.
    have h_combined :
        (analyticOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)).map (↑· : ℕ → ℤ)
          = ((n : ℤ) : WithTop ℤ) := by
      rw [← h_mero_eq, h_mero_int, h_kn]
    -- The map `Nat.cast : ℕ → ℤ` is injective on `WithTop`; extract `analyticOrderAt _ = n`.
    -- We do this by case analysis on `analyticOrderAt _`.
    cases h_top : analyticOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) with
    | top =>
      -- Then `(⊤).map _ = ⊤ ≠ ((n : ℤ) : WithTop ℤ)` — contradiction.
      rw [h_top] at h_combined
      exact absurd h_combined (by simp)
    | coe m =>
      rw [h_top] at h_combined
      -- `(m : ℕ).map _ = (m : ℤ)` and `((n : ℤ) : WithTop ℤ) = ((n : ℤ) : WithTop ℤ)`.
      simp only [ENat.map_coe] at h_combined
      -- `((m : ℤ) : WithTop ℤ) = ((n : ℤ) : WithTop ℤ)` ⟹ `m = n`.
      have h_eq : (m : ℤ) = (n : ℤ) := by exact_mod_cast h_combined
      have h_mn : m = n := by exact_mod_cast h_eq
      rw [h_mn]
  -- Step 2: Apply `analyticOrderAt_eq_natCast` to extract the local form.
  exact (hf_an.analyticOrderAt_eq_natCast).mp h_an_order

end MMeromorphicAt

/-! ## The headline R3 statement (Prop-valued, not axiom)

`localMultiplicity_eq_localOrder_statement` packages the bridge between the
chart-coordinate local form (proven above) and the topological local
multiplicity (cardinality of `f⁻¹{w}` near `x` for `w` near `f x`).

We state it as a `Prop`-valued `def` (per the brief): the statement is
*meaningful* and unambiguous, but the discharge requires Rouché-style
counting that is not in mathlib at the pin. -/

variable (X : Type u)
  [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) ω X]

/-- **Local multiplicity = local order.** For every meromorphic `f` and
every `x : X`, the chart-coordinate local form gives a unique `k = localOrder
I f x` with `f ∘ chart⁻¹ = (z - chart x)^k · g(z)` on a punctured neighborhood.
The classical assertion (R3) is that, when `k > 0`, the topological
multiplicity of `f` at `x` (cardinality of `f⁻¹ {w} ∩ U` for any sufficiently
small neighborhood `U` of `x` and any sufficiently close-to-`f x` value `w`)
equals `k.natAbs`.

We package this as the conjunction of:

* the chart-coordinate local form (proven above as
  `MMeromorphicAt.exists_local_normal_form`);
* the topological-multiplicity bridge (the actual count statement).

For the **bridge** we use the equivalent formulation: there exists an open
neighborhood `U` of `x` and a deleted neighborhood `V` of `f x` such that for
every `w ∈ V`, the set `{y ∈ U | f y = w}` has exactly `(localOrder I f x).natAbs`
elements (when the order is positive; the pole case is symmetric via
`f⁻¹`).

**Status.** Stated, not proven. The Rouché-side counting argument is owed
from a future mathlib `LocalMultiplicity` package. We state it in
`Prop`-valued form to preserve the dependency surface. -/
def localMultiplicity_eq_localOrder_statement : Prop :=
  ∀ (f : X → ℂ) (_ : MMeromorphicOn (modelWithCornersSelf ℂ ℂ) f Set.univ)
    (_ : ∀ x, mmeromorphicOrderAt (modelWithCornersSelf ℂ ℂ) f x ≠ ⊤)
    (x : X),
    -- Positive-order (zero) case: the topological multiplicity at `x` over
    -- nearby values `w` is the natural-number absolute value of the local order.
    -- We use `Set.ncard` (cardinality of a `Set`, `0` for infinite sets) so
    -- the statement does not need a separate finiteness hypothesis embedded in
    -- the type. The implicit content of "for sufficiently nearby `w`, the count
    -- equals `k`" includes the assertion that the preimage set is finite (and
    -- so `ncard` is the honest cardinality).
    0 < localOrder (modelWithCornersSelf ℂ ℂ) f x →
      ∃ (U : Set X) (V : Set ℂ),
        IsOpen U ∧ x ∈ U ∧
        IsOpen V ∧ f x ∈ V ∧
        ∀ w ∈ V, w ≠ f x →
          ({y ∈ U | f y = w} : Set X).ncard =
            (localOrder (modelWithCornersSelf ℂ ℂ) f x).natAbs

/-! ## Compatibility statement bridging `localOrder` to the existing
`R3_localMultiplicity_statement` in `ResidueTheorem.lean`

The R3 statement in `ResidueTheorem.lean` is the coarse "multiplicity ≥ 1"
form. We discharge it directly here, since it follows from the no-germ-zero
hypothesis and the fact that `Int.natAbs` of a nonzero integer is `≥ 1`. -/

/-- The coarse R3 statement (`R3_localMultiplicity_statement` in
`ResidueTheorem.lean`) is **unconditionally true** under the standing
hypothesis: if the integer order is nonzero, its absolute value is `≥ 1`.

This is the only piece of R3 that does not require classical analytic input;
it is purely arithmetic on `ℤ`. We prove it here so that `ResidueTheorem.lean`
can route through `localOrder` rather than hand-rolling the same statement. -/
theorem r3_natAbs_ge_one_of_ne_zero
    (k : ℤ) (hk : k ≠ 0) : k.natAbs ≥ 1 := by
  rcases Int.natAbs_pos.mpr hk with h
  exact h

end JacobianChallenge

end
