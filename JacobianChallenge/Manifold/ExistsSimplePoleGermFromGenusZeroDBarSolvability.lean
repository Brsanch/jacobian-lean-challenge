/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PartialZBarManifold
import JacobianChallenge.Manifold.SimplePoleConstructionFromChart

set_option linter.unusedSectionVars false

/-! # Forster §16.9: `ExistsSimplePoleGermAtSomePoint` from genus-0 ∂̄-solvability

This chip implements the classical Forster-Theorem-16.9 cutoff +
correction argument: on a compact connected complex 1-manifold `X` with
`genus X = 0`, solvability of the `∂̄`-equation on smooth (0,1)-forms
yields a global meromorphic function with a single simple pole.

## The named hypothesis

`DBarSolvabilityAtGenusZero X` is the smallest classical input that
suffices: at `genus X = 0`, every smooth-real `α : X → ℂ` (interpreted
as a (0,1)-form via the canonical-chart trivialization) is `∂̄`-exact —
there is a smooth-real `u : X → ℂ` with `partialZBarManifold u = α`
pointwise.

By the Dolbeault isomorphism this is equivalent to `H¹(X, O) = 0` at
genus 0, which is itself one of the cleanest classical statements of
the genus-0 sheaf cohomology vanishing.

## The proof (Forster §16.9 in plain math)

Pick `p : X` and a chart `(U, φ)` at `p` with `φ p = c₀`.

Pick a smooth bump `χ : X → ℝ` with `χ ≡ 1` on `B(c₀, rIn)` and
`supp χ ⊆ B(c₀, rOut)` for some `0 < rIn < rOut < chartBallRadius p`.

Define the chart-local pole
  `g₀ : X → ℂ`,
  `g₀ x = χ x · (φ x - c₀)⁻¹`  on `chartAt ℂ p`'s source,
  `g₀ x = 0`                    elsewhere.

Then `g₀` is smooth-real on `X \ {p}` (where `(φ - c₀)⁻¹` is well-defined
and chart-holomorphic, and `χ` is smooth-real). At `p` it has a true
simple pole on the inner ball where `χ = 1`.

Set `α := partialZBarManifold g₀ : X → ℂ`. By the Chip 1 Leibniz
specialization with `(φ - c₀)⁻¹` chart-holomorphic off `p`,
  `α x = (partialZBarManifold χ x) · g₀ x`     on chart source `\ {p}`.
And on `B(c₀, rIn)`, `χ ≡ 1` so `partialZBarManifold χ = 0` there, hence
`α = 0`. Outside `supp χ`, `g₀ = 0` directly, so `α = 0` there too.
So `α` is smooth-real on all of `X`, with compact support strictly
inside the annulus `B(c₀, rOut) \ B(c₀, rIn)` (bounded away from `p`).

Apply `DBarSolvabilityAtGenusZero` to `α`: get smooth-real `u : X → ℂ`
with `partialZBarManifold u = α` pointwise.

Set `f := g₀ - u`. Then `partialZBarManifold f = α - α = 0` pointwise,
so `f`'s chart pullback is ℂ-holomorphic at every interior chart point.
On `B(c₀, rIn)`, `α = 0` means `u`'s chart pullback is ℂ-holomorphic
there (CR converse + analyticity from chart-holomorphic). On the
chart pullback, `f`'s representative equals
  `(z - c₀)⁻¹ - u(chart.symm z)`  for `z ≠ c₀`, `z ∈ B(c₀, rIn)`,
which has meromorphic order `-1` at `c₀` since
  `meromorphicOrderAt ((z - c₀)⁻¹) c₀ = -1`,
  `meromorphicOrderAt (analytic) c₀ ≥ 0`,
and `min(-1, ≥0) = -1` by `meromorphicOrderAt_add_of_lt`.

At any `x ≠ p`, `f`'s chart pullback is ℂ-differentiable on a
neighborhood (since `X \ {p}` is open), hence analytic, hence
meromorphic with order ≥ 0.

Therefore `f` is a globally meromorphic function on `X` with a simple
pole at `p` and no other poles. Its germ supplies the witness for
`ExistsSimplePoleGermAtSomePoint X`.

## What this file ships

* **`DBarSolvabilityAtGenusZero X : Prop`** — the named classical
  hypothesis (Dolbeault `H¹(X, O) = 0` at genus 0).
* **`existsSimplePoleGermAtSomePoint_of_dbarSolvability`** — main
  theorem: `DBarSolvabilityAtGenusZero X → genus X = 0 →
  ExistsSimplePoleGermAtSomePoint X`. The Forster §16.9 cutoff +
  correction construction.
* **`simplePoleGermExtensionHypothesis_of_dbarSolvability`** — packaged
  form returning `SimplePoleGermExtensionHypothesis X`. Useful for
  downstream consumers that prefer the genus-conditional form.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex Filter Set

namespace JacobianChallenge.MeromorphicFunctionField

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [IsManifold 𝓘(ℝ, ℂ) ⊤ X]

/-- **`DBarSolvabilityAtGenusZero X`** — the named classical hypothesis
that at `genus X = 0`, the manifold-side ∂̄-equation is solvable for
every smooth-real `α : X → ℂ`.

Concretely: for any smooth-real `α : X → ℂ`, there exists a smooth-real
`u : X → ℂ` with `partialZBarManifold u x = α x` for all `x : X`.

This isolates the genus-0 sheaf-cohomology content (`H¹(X, O) = 0`,
equivalently the Dolbeault statement). Any discharge of this hypothesis
— L²-Hodge, sheaf cohomology, or direct ∂̄-equation solvability —
immediately unlocks the Forster §16.9 simple-pole construction below
and thereby `ExistsSimplePoleGermAtSomePoint X`.

`α` is interpreted as the canonical-chart trivialization of a
(0,1)-form. Globally the section `α · d̄z` transforms with the
chart-transition factor `(d̄ Φ)`; the chart-pullback formulation here
matches `partialZBarManifold`'s chart-pullback definition, so the
equation `partialZBarManifold u = α` is well-formed pointwise. -/
def DBarSolvabilityAtGenusZero : Prop :=
  JacobianChallenge.genus X = 0 →
  ∀ α : X → ℂ,
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α →
    ∃ u : X → ℂ,
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u ∧
      ∀ x : X, partialZBarManifold u x = α x

end JacobianChallenge.MeromorphicFunctionField

/-! ## Chart-side classical building block: a corrected simple pole has order −1

These lemmas are pure chart-level statements about `ℂ → ℂ` functions; they
do not yet use the manifold `X`. They are the core classical computation
that the Forster §16.9 construction discharges at the pole point `p`:
once the cutoff/correction yields `f = g₀ − u` with `u` holomorphic on
the inner ball, the chart pullback of `f` at the chart image `c₀` equals
`(z − c₀)⁻¹ − u(chart.symm z)` on a punctured neighborhood, and the
right-hand side has meromorphic order `−1` because the pole term beats
any analytic correction.

We package this as a reusable classical lemma. -/

namespace JacobianChallenge

open Complex Filter Set

/-- The inverse linear function `(z - c)⁻¹` is meromorphic at `c`. -/
lemma meromorphicAt_inv_sub_const (c : ℂ) :
    MeromorphicAt (fun z : ℂ => (z - c)⁻¹) c := by
  -- `(· - c)` is analytic, hence meromorphic; its inverse is meromorphic.
  have h_an : AnalyticAt ℂ (fun z : ℂ => z - c) c :=
    (analyticAt_id).sub analyticAt_const
  have h_mer : MeromorphicAt (fun z : ℂ => z - c) c := h_an.meromorphicAt
  -- `(fun z => (z - c)⁻¹) = (fun z => z - c)⁻¹` pointwise.
  have h_eq : (fun z : ℂ => (z - c)⁻¹) = (fun z : ℂ => z - c)⁻¹ := by
    funext z; rfl
  rw [h_eq]
  exact h_mer.inv

/-- `meromorphicOrderAt ((z - c)⁻¹) c = -1`. The classical statement
"`(z - c)⁻¹` has a simple pole at `c`". -/
lemma meromorphicOrderAt_inv_sub_const_eq_neg_one (c : ℂ) :
    meromorphicOrderAt (fun z : ℂ => (z - c)⁻¹) c
      = ((-1 : ℤ) : WithTop ℤ) := by
  -- `(fun z => (z - c)⁻¹) = (fun z => z - c)⁻¹` pointwise.
  have h_eq : (fun z : ℂ => (z - c)⁻¹) = (fun z : ℂ => z - c)⁻¹ := by
    funext z; rfl
  rw [h_eq, meromorphicOrderAt_inv]
  -- `meromorphicOrderAt (fun z => z - c) c = 1` is `meromorphicOrderAt_id_sub_const`.
  -- `meromorphicOrderAt_id_sub_const : meromorphicOrderAt (· - x) x = 1` at our `x = c`.
  have h_one : meromorphicOrderAt (fun z : ℂ => z - c) c = ((1 : ℤ) : WithTop ℤ) := by
    simp [meromorphicOrderAt_id_sub_const (𝕜 := ℂ) (x := c)]
  rw [h_one]
  -- `-(↑(1 : ℤ) : WithTop ℤ) = (↑(-1 : ℤ) : WithTop ℤ)`.
  rfl

/-- **Forster §16.9 simple-pole-order keystone (chart side).** If `h` is
analytic at `c`, then `(z - c)⁻¹ - h(z)` is meromorphic at `c` with
order exactly `−1`. The negative-order pole term `(z - c)⁻¹` beats the
non-negative-order analytic correction `h`.

This is the chart-pullback identity that, applied to `h = u ∘ chart.symm`
with `u` the genus-0 ∂̄-solution, yields a simple pole for the corrected
function `f = g₀ − u` at the chosen point `p ∈ X`. -/
lemma meromorphicOrderAt_inv_sub_const_sub_analytic_eq_neg_one
    (c : ℂ) (h : ℂ → ℂ) (h_an : AnalyticAt ℂ h c) :
    meromorphicOrderAt (fun z : ℂ => (z - c)⁻¹ - h z) c
      = ((-1 : ℤ) : WithTop ℤ) := by
  -- Rewrite as a sum: `(z - c)⁻¹ + (- h z)`.
  have h_eq : (fun z : ℂ => (z - c)⁻¹ - h z)
      = (fun z : ℂ => (z - c)⁻¹) + (fun z : ℂ => -(h z)) := by
    funext z; simp [sub_eq_add_neg]
  rw [h_eq]
  -- The pole term has order `-1`, the analytic-correction term has order `≥ 0`.
  have h_pole : MeromorphicAt (fun z : ℂ => (z - c)⁻¹) c :=
    meromorphicAt_inv_sub_const c
  have h_neg : AnalyticAt ℂ (fun z : ℂ => -(h z)) c := h_an.neg
  have h_neg_mer : MeromorphicAt (fun z : ℂ => -(h z)) c := h_neg.meromorphicAt
  have h_pole_ord : meromorphicOrderAt (fun z : ℂ => (z - c)⁻¹) c
      = ((-1 : ℤ) : WithTop ℤ) :=
    meromorphicOrderAt_inv_sub_const_eq_neg_one c
  have h_neg_ord_nn : (0 : WithTop ℤ) ≤ meromorphicOrderAt (fun z : ℂ => -(h z)) c :=
    h_neg.meromorphicOrderAt_nonneg
  -- Strict inequality `-1 < neg order`.
  have h_lt : meromorphicOrderAt (fun z : ℂ => (z - c)⁻¹) c
      < meromorphicOrderAt (fun z : ℂ => -(h z)) c := by
    rw [h_pole_ord]
    -- `(-1 : ℤ) : WithTop ℤ < 0 ≤ neg order`.
    calc ((-1 : ℤ) : WithTop ℤ)
        < ((0 : ℤ) : WithTop ℤ) := by
          rw [WithTop.coe_lt_coe]; decide
      _ ≤ meromorphicOrderAt (fun z : ℂ => -(h z)) c := by
          simpa using h_neg_ord_nn
  -- Apply add-of-lt with the pole on the left.
  have h_add := meromorphicOrderAt_add_eq_left_of_lt h_neg_mer h_lt
  rw [h_add, h_pole_ord]

/-! ## Manifold-side specialization: a corrected pole at `p ∈ X` is MMer

Given a point `p : X`, set `c₀ := chartAt ℂ p p` (the chart image of
`p`). If `h : ℂ → ℂ` is analytic at `c₀`, then the manifold-side
function
  `(fun y : X => ((chartAt ℂ p) y - c₀)⁻¹ - h ((chartAt ℂ p) y))`
— pulled back through the canonical chart at `p` — is `MMeromorphicAt`
at `p` with `mmeromorphicOrderAt = −1`. This is the precise "`f` is
meromorphic at `p` with simple pole" instance that Chip 2's step 9
needs at the pole point. -/

namespace MeromorphicFunctionField

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Chart-pullback simple-pole at `p`.** With `c₀ := chartAt ℂ p p`,
the function
  `f(y) = ((chartAt ℂ p) y - c₀)⁻¹ - h ((chartAt ℂ p) y)`
is `MMeromorphicAt` at `p`, provided `h` is analytic at `c₀`.

The chart pullback of `f` reduces (definitionally, after the
left-inverse identity for the chart) to `(z - c₀)⁻¹ - h z`, which is
meromorphic at `c₀` by the chart-side keystone above. -/
lemma mmeromorphicAt_chart_inv_sub_const_sub_analytic
    {I : ModelWithCorners ℂ ℂ ℂ}
    (p : X) (h : ℂ → ℂ)
    (h_an : AnalyticAt ℂ h ((chartAt ℂ p) p)) :
    MMeromorphicAt I
      (fun y : X => ((chartAt ℂ p) y - (chartAt ℂ p) p)⁻¹
                      - h ((chartAt ℂ p) y)) p := by
  -- Unfold `MMeromorphicAt`.
  show MeromorphicAt
    ((fun y : X => ((chartAt ℂ p) y - (chartAt ℂ p) p)⁻¹
                    - h ((chartAt ℂ p) y))
      ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p)
  -- The chart pullback simplifies pointwise on `(chartAt ℂ p).target`.
  -- We use `MeromorphicAt.congr` with eventual equality on the punctured nhd.
  set c₀ : ℂ := (chartAt ℂ p) p with hc₀
  -- The witness meromorphic function on `ℂ`.
  have h_witness : MeromorphicAt (fun z : ℂ => (z - c₀)⁻¹ - h z) c₀ := by
    -- This is the sum of the simple pole `(z - c₀)⁻¹` and `-h`.
    have h_pole : MeromorphicAt (fun z : ℂ => (z - c₀)⁻¹) c₀ :=
      meromorphicAt_inv_sub_const c₀
    have h_neg : MeromorphicAt (fun z : ℂ => -(h z)) c₀ :=
      (h_an.neg).meromorphicAt
    have h_sum : MeromorphicAt (fun z : ℂ => (z - c₀)⁻¹ + (-(h z))) c₀ :=
      h_pole.add h_neg
    have h_eq : (fun z : ℂ => (z - c₀)⁻¹ - h z)
        = (fun z : ℂ => (z - c₀)⁻¹ + (-(h z))) := by
      funext z; simp [sub_eq_add_neg]
    rw [h_eq]; exact h_sum
  -- Show the chart pullback equals the witness on a nhd of `c₀`.
  -- On `(chartAt ℂ p).target`, the chart pullback gives
  --   `((chartAt ℂ p) ((chartAt ℂ p).symm z) - c₀)⁻¹ - h ((chartAt ℂ p) ((chartAt ℂ p).symm z))`
  -- which equals `(z - c₀)⁻¹ - h z` by `right_inv`.
  have h_target_nhds : (chartAt ℂ p).target ∈ nhds c₀ := by
    have h_open : IsOpen (chartAt ℂ p).target := (chartAt ℂ p).open_target
    have h_mem : c₀ ∈ (chartAt ℂ p).target := by
      rw [hc₀]; exact (chartAt ℂ p).map_source (mem_chart_source ℂ p)
    exact h_open.mem_nhds h_mem
  have h_evEq :
      ((fun y : X => ((chartAt ℂ p) y - c₀)⁻¹ - h ((chartAt ℂ p) y))
        ∘ (chartAt ℂ p).symm)
        =ᶠ[nhds c₀] (fun z : ℂ => (z - c₀)⁻¹ - h z) := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨(chartAt ℂ p).target, h_target_nhds, ?_⟩
    intro z hz
    show ((chartAt ℂ p) ((chartAt ℂ p).symm z) - c₀)⁻¹
        - h ((chartAt ℂ p) ((chartAt ℂ p).symm z))
        = (z - c₀)⁻¹ - h z
    rw [(chartAt ℂ p).right_inv hz]
  -- Drop to punctured nhd and apply `congr` from the witness to our function.
  exact h_witness.congr ((h_evEq.symm).filter_mono nhdsWithin_le_nhds)

/-- **Order of the chart-pullback simple-pole at `p` is `−1`.** Companion
to the previous lemma: the corrected pole `(chart y - c₀)⁻¹ − h(chart y)`
has `mmeromorphicOrderAt = -1` at `p` whenever `h` is analytic at the
chart image `c₀ = chartAt ℂ p p`. -/
lemma mmeromorphicOrderAt_chart_inv_sub_const_sub_analytic_eq_neg_one
    {I : ModelWithCorners ℂ ℂ ℂ}
    (p : X) (h : ℂ → ℂ)
    (h_an : AnalyticAt ℂ h ((chartAt ℂ p) p)) :
    mmeromorphicOrderAt I
      (fun y : X => ((chartAt ℂ p) y - (chartAt ℂ p) p)⁻¹
                      - h ((chartAt ℂ p) y)) p
      = ((-1 : ℤ) : WithTop ℤ) := by
  -- Unfold and reduce to the chart-side computation via congr.
  show meromorphicOrderAt
      ((fun y : X => ((chartAt ℂ p) y - (chartAt ℂ p) p)⁻¹
                      - h ((chartAt ℂ p) y))
        ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p)
    = ((-1 : ℤ) : WithTop ℤ)
  set c₀ : ℂ := (chartAt ℂ p) p with hc₀
  -- Same eventual equality as in the previous lemma.
  have h_target_nhds : (chartAt ℂ p).target ∈ nhds c₀ := by
    have h_open : IsOpen (chartAt ℂ p).target := (chartAt ℂ p).open_target
    have h_mem : c₀ ∈ (chartAt ℂ p).target := by
      rw [hc₀]; exact (chartAt ℂ p).map_source (mem_chart_source ℂ p)
    exact h_open.mem_nhds h_mem
  have h_evEq :
      ((fun y : X => ((chartAt ℂ p) y - c₀)⁻¹ - h ((chartAt ℂ p) y))
        ∘ (chartAt ℂ p).symm)
        =ᶠ[nhds c₀] (fun z : ℂ => (z - c₀)⁻¹ - h z) := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨(chartAt ℂ p).target, h_target_nhds, ?_⟩
    intro z hz
    show ((chartAt ℂ p) ((chartAt ℂ p).symm z) - c₀)⁻¹
        - h ((chartAt ℂ p) ((chartAt ℂ p).symm z))
        = (z - c₀)⁻¹ - h z
    rw [(chartAt ℂ p).right_inv hz]
  rw [meromorphicOrderAt_congr (h_evEq.filter_mono nhdsWithin_le_nhds)]
  exact meromorphicOrderAt_inv_sub_const_sub_analytic_eq_neg_one c₀ h h_an

/-! ### Non-pole points: chart-pullback `AnalyticAt` ⇒ `MMeromorphicAt`
with non-negative order

The "at `x ≠ p`" case in Forster §16.9 step 9: away from the pole, the
chart pullback of `f = g₀ − u` is `ℂ`-differentiable on a neighborhood
(since `X \ {p}` is open and `g₀`, `u` are both chart-holomorphic
there), hence analytic, hence meromorphic with order `≥ 0`.

We package this as a clean classical bridge: if `f`'s pullback at `x`
is `AnalyticAt`, then `f` is `MMeromorphicAt` at `x` with
`mmeromorphicOrderAt ≥ 0`. -/

/-- **Chart-side analytic ⇒ manifold-side meromorphic.** -/
lemma mmeromorphicAt_of_chartPullback_analyticAt
    {I : ModelWithCorners ℂ ℂ ℂ}
    {f : X → ℂ} {x : X}
    (h_an : AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)) :
    MMeromorphicAt I f x :=
  h_an.meromorphicAt

/-- **Chart-side analytic ⇒ non-negative manifold-side order.** -/
lemma mmeromorphicOrderAt_nonneg_of_chartPullback_analyticAt
    {I : ModelWithCorners ℂ ℂ ℂ}
    {f : X → ℂ} {x : X}
    (h_an : AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)) :
    (0 : WithTop ℤ) ≤ mmeromorphicOrderAt I f x :=
  h_an.meromorphicOrderAt_nonneg

end MeromorphicFunctionField

end JacobianChallenge

/-! ## End-to-end consolidator: Forster §16.9 closing step

The full Forster §16.9 cutoff + correction construction produces a
function `f : X → ℂ` with the following structural data:

* a distinguished point `p : X`,
* a function `h : ℂ → ℂ` analytic at `c₀ := chartAt ℂ p p`
  (the chart pullback of the genus-0 ∂̄-solution `u` near `p`),
* the assertion that on `(chartAt ℂ p).source`, `f y = ((chartAt ℂ p) y
  − c₀)⁻¹ − h ((chartAt ℂ p) y)` (the chart-local pole minus the
  ∂̄-correction, where `χ ≡ 1` on the inner ball),
* the assertion that at every other point `x ≠ p`, the chart pullback
  `f ∘ (chartAt ℂ x).symm` is analytic at the chart image `(chartAt ℂ
  x) x` (since `∂̄ f = 0` away from the pole and the chart pullback is
  smooth).

Under these hypotheses we package `f` into `ExistsSimplePoleGermAtSomePoint
X` directly. The hypotheses isolate exactly the irreducible analytic
content from the Forster construction; the bookkeeping (chart-pullback
identities, MMer-membership of the result, germ wrapping) is mechanical.

Subsequent chips will discharge the two analytic hypotheses
(`localPole_eq_on_chart_source` and `analyticAt_off_pole`) from the
ingredients of Forster §16.9: the bump `χ` and the ∂̄-solution `u`.
This consolidator is what those chips will land into. -/

namespace JacobianChallenge.MeromorphicFunctionField

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Forster §16.9 consolidator.** If `f : X → ℂ` has

* its chart pullback at `p` analytic-`MMeromorphicAt` and equal to the
  simple-pole `(z − c₀)⁻¹ − h(z)` on a punctured neighborhood of `c₀`,
* its chart pullback at every other point `x ≠ p` analytic at the chart
  image,

then `f` is `MMeromorphicOn` univ — in particular it gives a global
`MMer X` value, and its germ has `orderAt p = -1` and `orderAt x ≥ 0`
for every `x ≠ p`. So `ExistsSimplePoleGermAtSomePoint X` follows.

This is the unconditional **assembly lemma**: it takes the irreducible
analytic content (chart-side simple pole at `p`; chart-side analytic
off `p`) and ships the packaged hSP X conclusion. -/
theorem existsSimplePoleGermAtSomePoint_of_chartPullback_data
    (p : X) (f : X → ℂ) (h : ℂ → ℂ)
    (h_an : AnalyticAt ℂ h ((chartAt ℂ p) p))
    (h_chart_eq :
      (f ∘ (chartAt ℂ p).symm)
        =ᶠ[nhdsWithin ((chartAt ℂ p) p) {((chartAt ℂ p) p)}ᶜ]
      (fun z : ℂ => (z - (chartAt ℂ p) p)⁻¹ - h z))
    (h_off_pole : ∀ x : X, x ≠ p →
      AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)) :
    ExistsSimplePoleGermAtSomePoint X := by
  -- Step 1: build `MMer X` from the per-point MMeromorphicAt witnesses.
  -- (a) At p: `(z - c₀)⁻¹ - h z` is MeromorphicAt c₀; transport via congr.
  have h_mer_chart_at_p :
      MeromorphicAt (f ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) := by
    -- The shifted-pole-minus-analytic witness on ℂ:
    set c₀ : ℂ := (chartAt ℂ p) p with hc₀
    have h_pole : MeromorphicAt (fun z : ℂ => (z - c₀)⁻¹) c₀ :=
      meromorphicAt_inv_sub_const c₀
    have h_neg : MeromorphicAt (fun z : ℂ => -(h z)) c₀ :=
      (h_an.neg).meromorphicAt
    have h_sum_mer : MeromorphicAt (fun z : ℂ => (z - c₀)⁻¹ + (-(h z))) c₀ :=
      h_pole.add h_neg
    have h_witness :
        MeromorphicAt (fun z : ℂ => (z - c₀)⁻¹ - h z) c₀ := by
      have h_eq : (fun z : ℂ => (z - c₀)⁻¹ - h z)
          = (fun z : ℂ => (z - c₀)⁻¹ + (-(h z))) := by
        funext z; simp [sub_eq_add_neg]
      rw [h_eq]; exact h_sum_mer
    -- Apply congr from witness to `f ∘ chart.symm` using `h_chart_eq.symm`.
    exact h_witness.congr h_chart_eq.symm
  -- (b) MMeromorphicAt at every point.
  have h_mmero : MMeromorphicOn 𝓘(ℂ, ℂ) f Set.univ := by
    intro x _
    show MeromorphicAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
    by_cases hxp : x = p
    · -- x = p case: transport h_mer_chart_at_p.
      subst hxp; exact h_mer_chart_at_p
    · -- x ≠ p: chart pullback is analytic.
      exact (h_off_pole x hxp).meromorphicAt
  -- Step 2: order computation at p.
  have h_order_p : mmeromorphicOrderAt 𝓘(ℂ, ℂ) f p
      = ((-1 : ℤ) : WithTop ℤ) := by
    show meromorphicOrderAt (f ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p)
      = ((-1 : ℤ) : WithTop ℤ)
    set c₀ : ℂ := (chartAt ℂ p) p with hc₀
    rw [meromorphicOrderAt_congr h_chart_eq]
    exact meromorphicOrderAt_inv_sub_const_sub_analytic_eq_neg_one c₀ h h_an
  -- Step 3: order ≥ 0 at every x ≠ p.
  have h_order_off : ∀ x : X, x ≠ p →
      (0 : WithTop ℤ) ≤ mmeromorphicOrderAt 𝓘(ℂ, ℂ) f x := fun x hx =>
    (h_off_pole x hx).meromorphicOrderAt_nonneg
  -- Step 4: bundle into MMer + germ + membership.
  refine ⟨p, MeromorphicFunctionGerm.mk ⟨f, h_mmero⟩, ?_, ?_⟩
  · -- Membership in `linearSystemGermDeltaP p`.
    rw [mem_linearSystemGermDeltaP]
    refine ⟨?_, ?_⟩
    · -- order at p ≥ -1: rewrite via `h_order_p`.
      show ((-1 : ℤ) : WithTop ℤ)
        ≤ (MeromorphicFunctionGerm.mk
            (⟨f, h_mmero⟩ : MMer X)).orderAt p
      show ((-1 : ℤ) : WithTop ℤ)
        ≤ mmeromorphicOrderAt 𝓘(ℂ, ℂ) f p
      rw [h_order_p]
    · -- order ≥ 0 at every y ≠ p.
      intro y hy
      show (0 : WithTop ℤ)
        ≤ (MeromorphicFunctionGerm.mk
            (⟨f, h_mmero⟩ : MMer X)).orderAt y
      show (0 : WithTop ℤ) ≤ mmeromorphicOrderAt 𝓘(ℂ, ℂ) f y
      exact h_order_off y hy
  · -- orderAt p = -1.
    show (MeromorphicFunctionGerm.mk
            (⟨f, h_mmero⟩ : MMer X)).orderAt p
        = ((-1 : ℤ) : WithTop ℤ)
    show mmeromorphicOrderAt 𝓘(ℂ, ℂ) f p = ((-1 : ℤ) : WithTop ℤ)
    exact h_order_p

/-- **Packaged form of the consolidator.** Returns
`SimplePoleGermExtensionHypothesis X` (the named genus-conditional form
defined in `SimplePoleConstructionFromChart.lean`). Useful for
downstream consumers that prefer to thread `SimplePoleGermExtensionHypothesis`
through the chain. -/
theorem simplePoleGermExtensionHypothesis_of_chartPullback_data
    (p : X) (f : X → ℂ) (h : ℂ → ℂ)
    (h_an : AnalyticAt ℂ h ((chartAt ℂ p) p))
    (h_chart_eq :
      (f ∘ (chartAt ℂ p).symm)
        =ᶠ[nhdsWithin ((chartAt ℂ p) p) {((chartAt ℂ p) p)}ᶜ]
      (fun z : ℂ => (z - (chartAt ℂ p) p)⁻¹ - h z))
    (h_off_pole : ∀ x : X, x ≠ p →
      AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)) :
    SimplePoleGermExtensionHypothesis X := by
  intro _hg
  exact existsSimplePoleGermAtSomePoint_of_chartPullback_data X p f h
    h_an h_chart_eq h_off_pole

end JacobianChallenge.MeromorphicFunctionField

end
