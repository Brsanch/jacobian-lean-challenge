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
  intro x hx; exact absurd hx (Set.not_mem_empty x)

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

end JacobianChallenge
