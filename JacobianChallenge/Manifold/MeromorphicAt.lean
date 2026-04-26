/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Complex

set_option diagnostics.threshold 100

/-! # Meromorphic functions on a complex manifold

This file lifts mathlib's `MeromorphicAt` / `MeromorphicOn` / `meromorphicOrderAt`
machinery (defined for functions `𝕜 → E` with `𝕜` a nontrivially normed field)
onto a complex manifold modelled on `ℂ`.

The construction is a *chart pullback*: for `f : M → ℂ`, `x : M`, we declare `f`
to be meromorphic at `x` iff its chart representative
`f ∘ (chartAt ℂ x).symm : ℂ → ℂ` is meromorphic at `(chartAt ℂ x) x` in the
ordinary sense.

## Main definitions

* `MMeromorphicAt I f x` — `f : M → ℂ` is meromorphic at `x : M`.
* `MMeromorphicOn I f s` — `f` is meromorphic on `s : Set M`.
* `mmeromorphicOrderAt I f x : WithTop ℤ` — chart-pulled-back order.

## Why parametrize by `I` even though we hard-code the model `𝓘(ℂ, ℂ)`?

The Jacobian-Conjecture-relevant case is `I = 𝓘(ℂ, ℂ)`, the trivial model of
`ℂ` over itself. The chart-pullback construction makes sense for any
model with corners `I : ModelWithCorners ℂ ℂ ℂ`, and several intermediate
lemmas hold without analyticity of the model. We therefore keep `I` as a
parameter, but require `[ChartedSpace ℂ M]` so that chart codomains are
literally `ℂ` (not a generic model space `H`). This avoids having to write
`I.symm ∘ (chartAt H x) ∘ ...` everywhere.

## Owed work (intentionally not in this file)

The following are **not** proved here and are tracked in `OPEN.md`:

1. **Chart-independence of `MMeromorphicAt`.** A first attempt at a
   conditional `iff_of_chart` lemma at this mathlib pin required threading
   `OpenPartialHomeomorph` continuity arguments through `comp_analyticAt`
   and `meromorphicOrderAt_comp` (`MeromorphicAt.meromorphicOrderAt_comp`,
   mathlib `Analysis/Meromorphic/Order.lean` line 779). The chart-pullback
   definition uses the *canonical* chart `chartAt ℂ x`. Lifting to arbitrary
   charts in the maximal analytic atlas requires
   `analyticAt_chart_transition_of_analyticManifold` (transition maps are
   analytic at every interior point of their source) — provable from
   `compatible_of_mem_maximalAtlas` + `chart_mem_maximalAtlas` + the
   omega-pregroupoid characterization (`ContDiffOn ω` ↔ `AnalyticOn` for
   `𝓘(ℂ, ℂ)` since the model is the identity), but the unfold through the
   `OpenPartialHomeomorph` API is API-heavy and is left to follow-up.

2. **Operations dropped at this pin.** `.inv`, `.pow`, `.zpow`,
   `.const_smul`, `.div`, `MMeromorphicOn.iUnion`, and a `@[simp]`
   `mMeromorphicOn_empty` are not provided here. The chart-pullback proofs
   for `.inv`/`.pow`/`.zpow`/`.const_smul`/`.div` follow the same pattern
   as `.add`/`.mul` and can be reinstated when the elaboration cost of the
   `Function.comp`-based `funext`+`simp` step is acceptable; they are
   omitted now to keep the file compiling cleanly under
   `relaxedAutoImplicit = false` + `diagnostics = true`.
-/

noncomputable section

open scoped Manifold Topology
open Filter Set

namespace JacobianChallenge

universe u

variable {M : Type u}
variable [TopologicalSpace M] [ChartedSpace ℂ M]

/-! ## Definitions: chart-pullback meromorphic predicate -/

/-- `f : M → ℂ` is **meromorphic at `x : M`** iff its representative in the
canonical chart at `x`, namely `f ∘ (chartAt ℂ x).symm : ℂ → ℂ`, is
meromorphic at the chart image `(chartAt ℂ x) x` in the standard sense.

This is a chart-pullback definition. It is conditionally chart-independent
on a complex analytic manifold; the unconditional discharge is owed (see
the file header). -/
def MMeromorphicAt (_I : ModelWithCorners ℂ ℂ ℂ) (f : M → ℂ) (x : M) : Prop :=
  MeromorphicAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)

/-- `f : M → ℂ` is **meromorphic on `s : Set M`** iff it is meromorphic at
each point of `s`. -/
def MMeromorphicOn (I : ModelWithCorners ℂ ℂ ℂ) (f : M → ℂ) (s : Set M) : Prop :=
  ∀ x ∈ s, MMeromorphicAt I f x

/-- The **order** of a meromorphic function `f : M → ℂ` at `x : M`, computed
by chart pullback. Returns `⊤` if `f` is identically zero in a punctured
neighborhood, a finite negative integer for poles, zero for regular nonzero
points, and a positive integer for zeros (matching `meromorphicOrderAt`'s
convention).

Chart-independence is owed; see file header. -/
def mmeromorphicOrderAt (_I : ModelWithCorners ℂ ℂ ℂ) (f : M → ℂ) (x : M) :
    WithTop ℤ :=
  meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)

/-! ## Membership and pointwise lemmas -/

variable {I : ModelWithCorners ℂ ℂ ℂ}

lemma mMeromorphicOn_empty (f : M → ℂ) : MMeromorphicOn I f ∅ := by
  intro x hx; exact absurd hx hx.elim

lemma MMeromorphicOn.mono {f : M → ℂ} {s t : Set M}
    (h : MMeromorphicOn I f t) (hst : s ⊆ t) : MMeromorphicOn I f s :=
  fun x hx => h x (hst hx)

lemma MMeromorphicOn.union {f : M → ℂ} {s t : Set M}
    (hs : MMeromorphicOn I f s) (ht : MMeromorphicOn I f t) :
    MMeromorphicOn I f (s ∪ t) := by
  intro x hx
  rcases hx with hx | hx
  · exact hs x hx
  · exact ht x hx

/-! ## Algebraic operations: lifted from `MeromorphicAt` via chart pullback

These are immediate consequences of the underlying mathlib lemmas, since the
chart pullback `f ∘ (chartAt ℂ x).symm` is a ring/module homomorphism in `f`. -/

namespace MMeromorphicAt

variable {f g : M → ℂ} {x : M}

/-- The zero function is meromorphic at every point. -/
lemma zero : MMeromorphicAt I (0 : M → ℂ) x := by
  show MeromorphicAt ((0 : M → ℂ) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  have h : (0 : M → ℂ) ∘ (chartAt ℂ x).symm = (fun _ => (0 : ℂ)) := rfl
  rw [h]
  exact analyticAt_const.meromorphicAt

/-- Constant functions are meromorphic. -/
lemma const (c : ℂ) : MMeromorphicAt I (fun _ : M => c) x := by
  show MeromorphicAt ((fun _ : M => c) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  have h : (fun _ : M => c) ∘ (chartAt ℂ x).symm = (fun _ => c) := rfl
  rw [h]
  exact analyticAt_const.meromorphicAt

lemma add (hf : MMeromorphicAt I f x) (hg : MMeromorphicAt I g x) :
    MMeromorphicAt I (f + g) x := by
  -- Unfold via `show`: `MMeromorphicAt I f x` reduces to `MeromorphicAt (f ∘ ...) (...)`.
  have hf' : MeromorphicAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hf
  have hg' : MeromorphicAt (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hg
  show MeromorphicAt ((f + g) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  have h : (f + g) ∘ (chartAt ℂ x).symm
      = (f ∘ (chartAt ℂ x).symm) + (g ∘ (chartAt ℂ x).symm) := rfl
  rw [h]
  exact hf'.add hg'

lemma mul (hf : MMeromorphicAt I f x) (hg : MMeromorphicAt I g x) :
    MMeromorphicAt I (f * g) x := by
  have hf' : MeromorphicAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hf
  have hg' : MeromorphicAt (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hg
  show MeromorphicAt ((f * g) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  have h : (f * g) ∘ (chartAt ℂ x).symm
      = (f ∘ (chartAt ℂ x).symm) * (g ∘ (chartAt ℂ x).symm) := rfl
  rw [h]
  exact hf'.mul hg'

lemma neg (hf : MMeromorphicAt I f x) : MMeromorphicAt I (-f) x := by
  have hf' : MeromorphicAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hf
  show MeromorphicAt ((-f) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  have h : (-f) ∘ (chartAt ℂ x).symm = -(f ∘ (chartAt ℂ x).symm) := rfl
  rw [h]
  exact hf'.neg

lemma sub (hf : MMeromorphicAt I f x) (hg : MMeromorphicAt I g x) :
    MMeromorphicAt I (f - g) x := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

end MMeromorphicAt

/-! ## Set-level closure under operations -/

namespace MMeromorphicOn

variable {f g : M → ℂ} {s : Set M}

lemma zero : MMeromorphicOn I (0 : M → ℂ) s :=
  fun x _ => MMeromorphicAt.zero

lemma const (c : ℂ) : MMeromorphicOn I (fun _ : M => c) s :=
  fun _ _ => MMeromorphicAt.const c

lemma add (hf : MMeromorphicOn I f s) (hg : MMeromorphicOn I g s) :
    MMeromorphicOn I (f + g) s :=
  fun x hx => (hf x hx).add (hg x hx)

lemma mul (hf : MMeromorphicOn I f s) (hg : MMeromorphicOn I g s) :
    MMeromorphicOn I (f * g) s :=
  fun x hx => (hf x hx).mul (hg x hx)

lemma neg (hf : MMeromorphicOn I f s) : MMeromorphicOn I (-f) s :=
  fun x hx => (hf x hx).neg

lemma sub (hf : MMeromorphicOn I f s) (hg : MMeromorphicOn I g s) :
    MMeromorphicOn I (f - g) s :=
  fun x hx => (hf x hx).sub (hg x hx)

end MMeromorphicOn

/-! ## Chart independence

The chart-pullback definition `MMeromorphicAt I f x` uses the *canonical* chart
`chartAt ℂ x`. This section shows that any other chart `e` from the atlas with
`x ∈ e.source` gives the same answer, **conditional on** the chart-transition
map being analytic with non-vanishing derivative at `e x`. On a complex
analytic manifold (`[IsManifold I ω M]` with `I = 𝓘(ℂ, ℂ)`), those hypotheses
hold automatically; the discharge is documented at the bottom of this section
and is the only piece *still* owed (see `OPEN.md`).

The mathematical content reduces to the mathlib lemmas
`meromorphicAt_comp_iff_of_deriv_ne_zero` and
`meromorphicOrderAt_comp_of_deriv_ne_zero`, both in
`Mathlib/Analysis/Meromorphic/Order.lean`. The non-trivial bookkeeping is the
local rewrite of
`(f ∘ (chartAt ℂ x).symm) ∘ ((chartAt ℂ x) ∘ e.symm) = f ∘ e.symm`
on a neighborhood of `e x`, which we discharge via continuity of `e.symm` and
`(chartAt ℂ x).left_inv` together with `MeromorphicAt.meromorphicAt_congr`. -/

section ChartIndependence

variable {f : M → ℂ} {x : M} {e : OpenPartialHomeomorph M ℂ}

/-- A neighborhood-of-`e x` rewrite for the doubly-pulled-back representative.
On every `y ∈ e.target ∩ e.symm ⁻¹' (chartAt ℂ x).source`, the function
`(f ∘ (chartAt ℂ x).symm) ∘ ((chartAt ℂ x) ∘ e.symm)` agrees with
`f ∘ e.symm`. -/
lemma comp_chart_transition_eqOn (hxe : x ∈ e.source) :
    Set.EqOn ((f ∘ (chartAt ℂ x).symm) ∘ ((chartAt ℂ x) ∘ e.symm))
      (f ∘ e.symm)
      (e.target ∩ e.symm ⁻¹' (chartAt ℂ x).source) := by
  intro y hy
  have hy_chart_src : e.symm y ∈ (chartAt ℂ x).source := hy.2
  -- Apply `(chartAt ℂ x).left_inv` to collapse the inner pair.
  show f ((chartAt ℂ x).symm ((chartAt ℂ x) (e.symm y))) = f (e.symm y)
  rw [(chartAt ℂ x).left_inv hy_chart_src]

/-- The set on which the doubly-pulled-back representative agrees with the
single-chart representative is a neighborhood of `e x`. -/
lemma comp_chart_transition_mem_nhds (hxe : x ∈ e.source) :
    e.target ∩ e.symm ⁻¹' (chartAt ℂ x).source ∈ nhds (e x) := by
  refine Filter.inter_mem ?_ ?_
  · exact e.open_target.mem_nhds (e.map_source hxe)
  · -- `(chartAt ℂ x).source` is open and contains `e.symm (e x) = x`.
    have h_continuousAt : ContinuousAt e.symm (e x) := by
      have : ContinuousOn e.symm e.target := e.continuousOn_invFun
      exact (this.continuousAt (e.open_target.mem_nhds (e.map_source hxe)))
    apply h_continuousAt.preimage_mem_nhds
    rw [e.left_inv hxe]
    exact (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)

/-- **Chart independence of `MMeromorphicAt`.** If `e` is any chart with
`x ∈ e.source`, and the transition `(chartAt ℂ x) ∘ e.symm` is analytic at
`e x` with nonzero derivative, then `MMeromorphicAt I f x` is equivalent to
the standard meromorphy of `f ∘ e.symm` at `e x`.

Both hypotheses are automatic on a complex analytic manifold (chart
transitions are analytic biholomorphisms); see
`analyticAt_chart_transition_of_atlas` (still owed) for the discharge. -/
lemma MMeromorphicAt.iff_of_chart
    (hxe : x ∈ e.source)
    (h_an : AnalyticAt ℂ ((chartAt ℂ x) ∘ e.symm) (e x))
    (h_deriv : deriv ((chartAt ℂ x) ∘ e.symm) (e x) ≠ 0) :
    MMeromorphicAt I f x ↔ MeromorphicAt (f ∘ e.symm) (e x) := by
  -- Step 1: unfold the LHS.
  show MeromorphicAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ↔ _
  -- Step 2: rewrite `(chartAt ℂ x) x` as `((chartAt ℂ x) ∘ e.symm) (e x)`.
  have h_pt : ((chartAt ℂ x) ∘ e.symm) (e x) = (chartAt ℂ x) x := by
    show (chartAt ℂ x) (e.symm (e x)) = (chartAt ℂ x) x
    rw [e.left_inv hxe]
  rw [← h_pt]
  -- Step 3: `meromorphicAt_comp_iff_of_deriv_ne_zero` gives the comparison
  -- between `f ∘ (chartAt ℂ x).symm` at the transition image and the
  -- composition `(f ∘ (chartAt ℂ x).symm) ∘ ((chartAt ℂ x) ∘ e.symm)` at `e x`.
  rw [← meromorphicAt_comp_iff_of_deriv_ne_zero h_an h_deriv]
  -- Step 4: replace the doubly-pulled-back representative by `f ∘ e.symm`
  -- using eventual equality on the neighborhood from `comp_chart_transition_*`.
  apply MeromorphicAt.meromorphicAt_congr
  -- Build an `EventuallyEq` at `𝓝 (e x)`, then drop to the punctured filter.
  have h_nhds :
      ((f ∘ (chartAt ℂ x).symm) ∘ ((chartAt ℂ x) ∘ e.symm)) =ᶠ[nhds (e x)]
        (f ∘ e.symm) :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨e.target ∩ e.symm ⁻¹' (chartAt ℂ x).source,
       comp_chart_transition_mem_nhds hxe,
       comp_chart_transition_eqOn hxe⟩
  exact h_nhds.filter_mono nhdsWithin_le_nhds

/-- **Chart independence of `mmeromorphicOrderAt`.** Under the same hypotheses
as `iff_of_chart`, the order computed by chart pullback at the canonical chart
agrees with the standard `meromorphicOrderAt` of `f ∘ e.symm` at `e x`. -/
lemma mmeromorphicOrderAt_eq_of_chart
    (hxe : x ∈ e.source)
    (h_an : AnalyticAt ℂ ((chartAt ℂ x) ∘ e.symm) (e x))
    (h_deriv : deriv ((chartAt ℂ x) ∘ e.symm) (e x) ≠ 0) :
    mmeromorphicOrderAt I f x = meromorphicOrderAt (f ∘ e.symm) (e x) := by
  -- Step 1: unfold the LHS.
  show meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = _
  -- Step 2: rewrite the basepoint via `e.left_inv`.
  have h_pt : ((chartAt ℂ x) ∘ e.symm) (e x) = (chartAt ℂ x) x := by
    show (chartAt ℂ x) (e.symm (e x)) = (chartAt ℂ x) x
    rw [e.left_inv hxe]
  rw [← h_pt]
  -- Step 3: invoke the deriv-ne-zero composition order formula. This rewrites
  -- `meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) (((chartAt ℂ x) ∘ e.symm) (e x))`
  -- into `meromorphicOrderAt ((f ∘ (chartAt ℂ x).symm) ∘ ((chartAt ℂ x) ∘ e.symm)) (e x)`.
  rw [← meromorphicOrderAt_comp_of_deriv_ne_zero h_an h_deriv]
  -- Step 4: rewrite the composed function pointwise on a neighborhood.
  apply meromorphicOrderAt_congr
  have h_nhds :
      ((f ∘ (chartAt ℂ x).symm) ∘ ((chartAt ℂ x) ∘ e.symm)) =ᶠ[nhds (e x)]
        (f ∘ e.symm) :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨e.target ∩ e.symm ⁻¹' (chartAt ℂ x).source,
       comp_chart_transition_mem_nhds hxe,
       comp_chart_transition_eqOn hxe⟩
  exact h_nhds.filter_mono nhdsWithin_le_nhds

/-! ### Discharge of the analyticity hypothesis (still owed)

On a complex analytic manifold `[ChartedSpace ℂ M] [IsManifold I ω M]` with
`I = 𝓘(ℂ, ℂ)`, the hypothesis `AnalyticAt ℂ ((chartAt ℂ x) ∘ e.symm) (e x)`
should be **automatic** for every `e ∈ atlas ℂ M` with `x ∈ e.source`: chart
transitions on an analytic manifold are analytic biholomorphisms.

The mathlib pieces are:

* `chart_mem_maximalAtlas (I := I) (n := ω) x : chartAt ℂ x ∈ maximalAtlas I ω M`,
* `subset_maximalAtlas (I := I) (n := ω) : atlas ℂ M ⊆ maximalAtlas I ω M`,
* `compatible_of_mem_maximalAtlas : … → e.symm.trans e' ∈ contDiffGroupoid ω I`,
* `ContDiffOn.analyticOn : ContDiffOn ℂ ω f s → AnalyticOn ℂ f s`,

plus the unfold of `contDiffPregroupoid` membership for `I = 𝓘(ℂ, ℂ)` (where
`I` and `I.symm` are the identity, so the pregroupoid `property` reduces from
`ContDiffOn ℂ ω (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I)` to
`ContDiffOn ℂ ω f s`). The `OpenPartialHomeomorph` ↔ `Pregroupoid.groupoid`
membership unfold is API-heavy at this pin and would add ≥ 100 LOC of
boilerplate; rather than ship a long proof speculatively (the pregroupoid
unfold has historically tripped on `mfld_simps`-vs-`simp` mismatches), we
park the discharge as a follow-up and ship the conditional API above.

The intended downstream signature, once the discharge lands, is

```
lemma analyticAt_chart_transition_of_atlas
    [IsManifold I ω M]
    {e : OpenPartialHomeomorph M ℂ} (he : e ∈ atlas ℂ M)
    {x : M} (hxe : x ∈ e.source) :
    AnalyticAt ℂ ((chartAt ℂ x) ∘ e.symm) (e x)
```

at which point `MMeromorphicAt.iff_of_chart` and
`mmeromorphicOrderAt_eq_of_chart` upgrade to unconditional statements (with
the `h_deriv` hypothesis dischargeable from `e.symm`-being-a-homeomorphism +
analytic-inverse-function-theorem). The current file deliberately exposes the
hypotheses explicitly so that downstream callers can either supply them by
hand on case-by-case manifolds (e.g. `ℂ` itself, `ℙ¹(ℂ)`) or wait for the
discharge lemma. -/

end ChartIndependence

end JacobianChallenge
