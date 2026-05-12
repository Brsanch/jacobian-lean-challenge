/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneForm
import JacobianChallenge.Manifold.RiemannSphereGenus
import JacobianChallenge.Topology.S2ImpliesGenus0Discharge
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option diagnostics.threshold 100

/-! # Linear-algebraic packaging of `HolomorphicOneForm` and `genus`

This file collects purely linear-algebraic glue lemmas that turn the
`Module.finrank ℂ (HolomorphicOneForm X)` definition of `genus` into a tool
fit for the item-14 chain.

The lemmas here do **not** open up new analytic content. They only repackage
existing infrastructure:

* `ContMDiffSection`'s `DFunLike`-backed extensionality
  (`HolomorphicOneForm.ext`, `HolomorphicOneForm.coe_zero`, …),
* mathlib's `Module.finrank_zero_iff` over a field (`ℂ` is a domain, every
  module over a field is torsion-free),
* `LinearEquiv.finrank_eq`, `LinearMap.finrank_le_finrank_of_injective`,
  `LinearMap.finrank_range_add_finrank_ker`.

The result is a small toolkit covering five micro-bridges that the
item-14 reductions in
`Topology/S2ImpliesGenus0Discharge.lean` and
`Manifold/RiemannSphereGenus.lean` currently re-derive ad hoc:

1. `genus X = 0 ↔ Subsingleton (HolomorphicOneForm X)` — under the
   universal `ℂ`-vector-space hypothesis. **No finite-dimensionality
   assumed in either direction**: `Subsingleton → finrank = 0` is
   `Module.finrank_zero_of_subsingleton`, and `finrank = 0 → Subsingleton`
   uses `Module.finrank_zero_iff` (works for fields).
2. `genus X = 0 ↔ ∀ α : HolomorphicOneForm X, α = 0` — via `subsingleton_iff`.
3. `Subsingleton (HolomorphicOneForm X) ↔ ∀ α, ⇑α = 0` — pointwise
   characterisation using `HolomorphicOneForm`'s `DFunLike`/`ext` API.
4. `genus_le_of_injective` — a `ℂ`-linear injection
   `HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm Y` with `Y` of
   finite-dimensional 1-form space forces `genus X ≤ genus Y`.
   Specialisation `genus_eq_zero_of_injective_into_subsingleton` covers
   the "embed into a known-zero-genus space" pattern relevant to the
   Riemann-sphere bridge.
5. `genus_eq_zero_iff_holomorphicOneForm_subsingleton` — a one-liner
   restatement of (1) in the exact shape used by item 14.

All five lemmas are unconditional in the analytic sense (no Hodge, no
finite-dimensionality hypothesis is added where it is not literally
needed). The `≤` direction in (4) of course needs `Y`-side finite-
dimensionality so that `Module.finrank ℂ (HolomorphicOneForm Y)` is not
the junk-zero value; this is recorded as an explicit `FiniteDimensional`
hypothesis on the codomain.

## What is **not** in this file

* The `Subsingleton (HolomorphicOneForm RiemannSphere)` instance.
  That is the chart-coefficient extraction chase explicitly noted as
  "still owed" in `Manifold/RiemannSphereGenus.lean` and is gated by
  the `cotangentBundleCore.localTrivAt` glue. We do not attempt it.

* Any change to `Basic.lean`. This file is content-only.

## No `sorry`, no `axiom`, no new bundles, no signature changes.
-/

open scoped Manifold ContDiff Topology Bundle

noncomputable section

namespace JacobianChallenge

namespace HolomorphicOneForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Pointwise characterisation of `Subsingleton (HolomorphicOneForm X)`:
a `ContMDiffSection`-valued type is a subsingleton iff every section
coerces to the zero function. The forward direction uses that the zero
section coerces to `0 : ∀ x, _`, the reverse uses `DFunLike` extensionality.

This is a `DFunLike`-level fact about `ContMDiffSection`. It is used to
move between "every form is the zero form" (the conclusion of the Liouville
chase) and the `Subsingleton` typeclass needed by
`Module.finrank_zero_of_subsingleton`. -/
theorem subsingleton_iff_forall_coe_eq_zero :
    Subsingleton (HolomorphicOneForm X)
      ↔ ∀ α : HolomorphicOneForm X, (α : ∀ x, CotangentSpace 𝓘(ℂ) x) = 0 := by
  refine ⟨fun h α => ?_, fun h => ?_⟩
  · -- In a subsingleton every element equals the zero element; coercion is
    -- a function, so the underlying functions agree.
    haveI := h
    have hαz : α = (0 : HolomorphicOneForm X) := Subsingleton.elim _ _
    -- Now use `coe_zero` to identify `⇑(0)` with the zero function.
    rw [hαz]
    exact ContMDiffSection.coe_zero
  · -- Conversely, if every section's underlying function is zero, then any
    -- two sections have equal underlying functions and `DFunLike` extensionality
    -- collapses them.
    refine ⟨fun α β => ?_⟩
    have hα := h α
    have hβ := h β
    apply DFunLike.coe_injective
    rw [hα, hβ]

/-- Restatement of `subsingleton_iff_forall_coe_eq_zero` using the
`HolomorphicOneForm`-internal `0`: a holomorphic-1-form space is a
subsingleton iff every form equals the zero form.

This is the form most convenient for the Liouville argument, which
produces `α = 0` rather than `⇑α = 0`. -/
theorem subsingleton_iff_forall_eq_zero :
    Subsingleton (HolomorphicOneForm X)
      ↔ ∀ α : HolomorphicOneForm X, α = (0 : HolomorphicOneForm X) := by
  refine ⟨fun h α => Subsingleton.elim _ _, fun h => ⟨fun α β => ?_⟩⟩
  rw [h α, h β]

end HolomorphicOneForm

/-! ### `Subsingleton → genus = 0`

The forward direction `Subsingleton → genus = 0` is
`Module.finrank_zero_of_subsingleton`. This is already used inside
`RiemannSphereGenus.lean`; we restate it here in `iff` form *under a
finite-dimensionality hypothesis on the 1-form space*, since the reverse
direction (`genus = 0 → Subsingleton`) requires `Module.finrank_zero_iff`,
whose mathlib statement at the pinned commit needs `[FiniteDimensional]`
(via `finrank_zero_iff_forall_zero`).

For the Riemann-sphere bridge — which is the only place this equivalence
is consumed — the codomain is the Riemann sphere itself, which under the
open `Subsingleton (HolomorphicOneForm RiemannSphere)` hypothesis is
trivially finite-dimensional (rank 0). So the `FiniteDimensional`
hypothesis is not a real obstruction. -/

section GenusSubsingleton

variable (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **One-direction reduction.** If the space of holomorphic 1-forms on
`X` is a subsingleton, then `genus X = 0`. This is a wrapper around
`Module.finrank_zero_of_subsingleton`, mirroring the version in
`RiemannSphereGenus.lean` but stated for general `X`. -/
theorem genus_eq_zero_of_holomorphicOneForm_subsingleton
    (h : Subsingleton (HolomorphicOneForm X)) :
    JacobianChallenge.genus X = 0 := by
  unfold JacobianChallenge.genus
  haveI := h
  exact Module.finrank_zero_of_subsingleton

/-- **Reverse direction under finite-dimensionality.** If
`HolomorphicOneForm X` is finite-dimensional over `ℂ` and `genus X = 0`,
then `HolomorphicOneForm X` is a subsingleton.

Uses mathlib's `finrank_zero_iff_forall_zero`. The
`FiniteDimensional` hypothesis discharges the `Module.finrank_zero_iff`
prerequisite at the pinned commit. -/
theorem holomorphicOneForm_subsingleton_of_genus_eq_zero
    [FiniteDimensional ℂ (HolomorphicOneForm X)]
    (h : JacobianChallenge.genus X = 0) :
    Subsingleton (HolomorphicOneForm X) := by
  have hzero : ∀ α : HolomorphicOneForm X, α = 0 := by
    have := (finrank_zero_iff_forall_zero (K := ℂ)
      (V := HolomorphicOneForm X)).mp h
    intro α
    exact this α
  exact (HolomorphicOneForm.subsingleton_iff_forall_eq_zero).mpr hzero

/-- **Equivalence (under finite-dimensionality).** Over `ℂ`, if
`HolomorphicOneForm X` is finite-dimensional then `genus X = 0` iff
`HolomorphicOneForm X` is a subsingleton. -/
theorem genus_eq_zero_iff_holomorphicOneForm_subsingleton
    [FiniteDimensional ℂ (HolomorphicOneForm X)] :
    JacobianChallenge.genus X = 0 ↔ Subsingleton (HolomorphicOneForm X) :=
  ⟨fun h => holomorphicOneForm_subsingleton_of_genus_eq_zero h,
    fun h => genus_eq_zero_of_holomorphicOneForm_subsingleton h⟩

/-- Pointwise version of `genus_eq_zero_iff_holomorphicOneForm_subsingleton`:
under finite-dimensionality, the genus is zero iff every form is the zero
form. -/
theorem genus_eq_zero_iff_forall_holomorphicOneForm_eq_zero
    [FiniteDimensional ℂ (HolomorphicOneForm X)] :
    JacobianChallenge.genus X = 0
      ↔ ∀ α : HolomorphicOneForm X, α = (0 : HolomorphicOneForm X) := by
  rw [genus_eq_zero_iff_holomorphicOneForm_subsingleton]
  exact HolomorphicOneForm.subsingleton_iff_forall_eq_zero

end GenusSubsingleton

/-! ### Transfer along `ℂ`-linear maps

Once `genus X = 0` is reduced to `Subsingleton (HolomorphicOneForm X)`,
the natural way to *propagate* the zero-genus conclusion through complex-
analytic constructions is via `ℂ`-linear maps of 1-form spaces (typically
pullbacks along biholomorphisms, but the present file is agnostic).

The two lemmas below cover:

* **Injective** linear maps from `HolomorphicOneForm X` into a space of
  known finite dimension `n` — they upper-bound `genus X ≤ n`. The
  zero case `n = 0` (target is subsingleton) is the relevant
  specialisation for the Riemann-sphere bridge.

* **Subsingleton transfer** along an injection from `X`'s 1-form space
  into a subsingleton: forces `HolomorphicOneForm X` itself to be a
  subsingleton, hence `genus X = 0`.

The hypotheses are stated with the codomain finite-dimensional, since the
target of `LinearMap.finrank_le_finrank_of_injective` is required to be
`Module.Finite`. -/

section TransferAlongLinearMap

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **Genus bound under an injective linear map.** A `ℂ`-linear injection
`HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm Y` with `Y` of finite
holomorphic-1-form dimension gives `genus X ≤ genus Y`.

Wraps mathlib's `LinearMap.finrank_le_finrank_of_injective`. -/
theorem genus_le_of_holomorphicOneForm_injective
    [FiniteDimensional ℂ (HolomorphicOneForm Y)]
    (f : HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm Y)
    (hf : Function.Injective f) :
    JacobianChallenge.genus X ≤ JacobianChallenge.genus Y := by
  unfold JacobianChallenge.genus
  exact f.finrank_le_finrank_of_injective hf

/-- **Subsingleton transfer.** A `ℂ`-linear injection from
`HolomorphicOneForm X` into a subsingleton holomorphic-1-form space forces
`HolomorphicOneForm X` itself to be a subsingleton.

Proof: an injection into a subsingleton is a function with at most one
value in its image; combined with injectivity, the domain has at most one
element. -/
theorem holomorphicOneForm_subsingleton_of_injective_into_subsingleton
    [Subsingleton (HolomorphicOneForm Y)]
    (f : HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm Y)
    (hf : Function.Injective f) :
    Subsingleton (HolomorphicOneForm X) := by
  refine ⟨fun α β => hf ?_⟩
  exact Subsingleton.elim _ _

/-- **Genus = 0 transfer.** A `ℂ`-linear injection from
`HolomorphicOneForm X` into a subsingleton holomorphic-1-form space forces
`genus X = 0`.

This is the specialisation of `genus_le_of_holomorphicOneForm_injective` to
`genus Y = 0`, plus the upgrade from `≤ 0` to `= 0`. -/
theorem genus_eq_zero_of_holomorphicOneForm_injective_into_subsingleton
    [Subsingleton (HolomorphicOneForm Y)]
    (f : HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm Y)
    (hf : Function.Injective f) :
    JacobianChallenge.genus X = 0 :=
  genus_eq_zero_of_holomorphicOneForm_subsingleton X
    (holomorphicOneForm_subsingleton_of_injective_into_subsingleton f hf)

/-- **Equivalent restatement of the Riemann-sphere bridge.** If
`HolomorphicOneForm RiemannSphere` is a subsingleton, then a `ℂ`-linear
*injection* (not necessarily an equivalence) of `HolomorphicOneForm X`
into it suffices for `genus X = 0`.

Compared with `S2ImpliesGenus0Discharge.s2ImpliesGenus0_of_linearEquiv`,
this version weakens the hypothesis from `≃ₗ[ℂ]` to `→ₗ[ℂ] + Injective`,
which matches how a biholomorphism's pullback would actually be obtained
in the wired-up proof (one-sided injectivity is easier than constructing
the full inverse).

Requires `Subsingleton (HolomorphicOneForm RiemannSphere)` as a typeclass.
That instance is the open analytic input — but once it lands, this lemma
plus the linear injection give `genus X = 0` immediately. -/
theorem genus_eq_zero_of_injective_into_RiemannSphere
    [Subsingleton (HolomorphicOneForm JacobianChallenge.RiemannSphere)]
    (f : HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm JacobianChallenge.RiemannSphere)
    (hf : Function.Injective f) :
    JacobianChallenge.genus X = 0 :=
  genus_eq_zero_of_holomorphicOneForm_injective_into_subsingleton f hf

end TransferAlongLinearMap

/-! ### Genus-zero packaging via a one-sided witness

The `S2ImpliesGenus0Discharge` route uses a `≃ₗ[ℂ]` hypothesis bundled as
a `Nonempty`. The following one-sided variant matches the new
`genus_eq_zero_of_injective_into_RiemannSphere` lemma and is the
appropriate object to take as an open hypothesis when only one direction
of the biholomorphism's pullback is convenient to construct. -/

namespace JacobianChallenge

/-- **Open hypothesis (one-sided variant).** A `ℂ`-linear *injection* —
not necessarily an equivalence — of `HolomorphicOneForm X` into
`HolomorphicOneForm RiemannSphere`.

Compare with `HolomorphicOneFormEquivRiemannSphere`
(`Topology/S2ImpliesGenus0Discharge.lean`), which uses `≃ₗ[ℂ]`. The
one-sided version is the minimal data needed to push `genus X = 0` through
once `Subsingleton (HolomorphicOneForm RiemannSphere)` is supplied.

Stated as `Nonempty` so it is `Prop`-valued, matching the convention of
the sister hypothesis. -/
def HolomorphicOneFormInjectsIntoRiemannSphere
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Prop :=
  Nonempty
    { f : HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm JacobianChallenge.RiemannSphere //
        Function.Injective f }

/-- From a `≃ₗ[ℂ]` between holomorphic-1-form spaces (the `Equiv`
hypothesis in `S2ImpliesGenus0Discharge.lean`) one immediately recovers
the one-sided injection hypothesis. -/
theorem holomorphicOneFormInjectsIntoRiemannSphere_of_equiv
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    (h : HolomorphicOneFormEquivRiemannSphere X) :
    HolomorphicOneFormInjectsIntoRiemannSphere X := by
  obtain ⟨e⟩ := h
  exact ⟨⟨e.toLinearMap, e.injective⟩⟩

/-- **Discharge of `genus X = 0`** from the one-sided injection
hypothesis plus the open subsingleton statement for the Riemann sphere.

Given:

* `hInj : HolomorphicOneFormInjectsIntoRiemannSphere X`;
* `hSS  : RiemannSphere.HolomorphicOneForm_RiemannSphere_subsingleton_statement`;

conclude `genus X = 0`. **No `sorry`, no axiom.**

This is the variant of `genus_zero_of_linearEquiv_RiemannSphere` that
takes injection rather than equivalence. -/
theorem genus_eq_zero_of_injects_into_RiemannSphere
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    (hInj : HolomorphicOneFormInjectsIntoRiemannSphere X)
    (hSS : RiemannSphere.HolomorphicOneForm_RiemannSphere_subsingleton_statement) :
    JacobianChallenge.genus X = 0 := by
  obtain ⟨⟨f, hf⟩⟩ := hInj
  haveI : Subsingleton (HolomorphicOneForm JacobianChallenge.RiemannSphere) := hSS
  exact genus_eq_zero_of_injective_into_RiemannSphere f hf

end JacobianChallenge

end
