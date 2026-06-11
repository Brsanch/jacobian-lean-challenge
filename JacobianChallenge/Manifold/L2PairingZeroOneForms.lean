/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartPullbackExtendZero
import JacobianChallenge.Manifold.MeromorphicAt
import JacobianChallenge.Analysis.HolomorphicChangeOfVariables

/-! # Arc 1 Chip 2 (completion) — the `L²` pairing of (0,1)-forms over a
finite chart cover, and its chart-overlap invariance

The repo encodes a smooth (0,1)-form on a charted-`ℂ` space `X` as a
global coefficient function `α : X → ℂ`: at each `y : X`, `α y` is the
coefficient of the form in the **canonical chart at `y`**
(`partialZBarManifold` produces exactly this encoding). The coefficient
of the same form **anchored in the chart at a fixed `x`** is
`α y * conj (τ_x y)` where

  `τ_x y := deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)`

is the chart-transition derivative (see
`partialZBarManifoldAtChart_eq_manifold_mul_transition`). Consequently
the chart-`x`-anchored **quadratic density** of two forms `α, β` is

  `α y * conj (β y) * normSq (τ_x y)`,

since `conj (τ) * conj (conj (τ)) = normSq τ`. This file defines the
classical partition-of-unity `L²` pairing

  `⟪α, β⟫ := ∑ i, ∫_ℂ chartPullbackZero xᵢ (ρᵢ · α · conj β · normSq τ_{xᵢ}) dA`

over a `FiniteChartCoverPartition` and proves the statement that makes
it geometrically meaningful: **each summand is independent of the
anchoring chart** — for a density supported in the overlap of two chart
sources, the chart-`i` integral of the `τ_i`-weighted density equals the
chart-`j` integral of the `τ_j`-weighted density. The proof is the
holomorphic change of variables of
`Analysis/HolomorphicChangeOfVariables.lean` (chip 2b) combined with the
**cocycle identity** for the transition derivative

  `τ_j y = τ_i y * deriv ((chartAt ℂ i) ∘ (chartAt ℂ j).symm) ((chartAt ℂ j) y)`,

so that `normSq (τ_j) = normSq (τ_i) · normSq (transition deriv)` is
exactly the real Jacobian produced by the substitution rule.

## Design choice (per HANDOFF_ITEM14 chip-2 brief)

The pairing is a **working definition on raw coefficient functions** —
a plain `ℂ`-valued finite sum of Bochner integrals — NOT an element of
a fixed Hilbert completion. Chips 3–4 (weak orthogonality ⟹
anti-holomorphic; genus-0 emptiness) only quote `⟪∂̄f, β⟫ = 0`-style
identities, for which the raw functional suffices; Hilbert-space
packaging is deferred to chip 5 (closed range), which can `MemLp`-wrap
this pairing when needed. Bochner-integral junk values on
non-integrable inputs are harmless here: every theorem in this file is
an unconditional identity between integrals, and the smoothness/
compact-support hypotheses appear only downstream.

## Main definitions

* `chartTransitionDerivAt x y` — the transition derivative `τ_x y`.
* `normSqTransitionC x y` — its `normSq`, coerced to `ℂ`.
* `pairingIntegrand P idx anchor α β` — the `ρ`-weighted anchored
  quadratic density.
* `L2PairSummand P idx α β`, `L2PairForms P α β` — the per-chart
  summand and the full pairing.

## Main results

* `chartTransitionDerivAt_cocycle` — the chain-rule cocycle for `τ`.
* `normSqTransitionC_cocycle` — its `normSq` form.
* `integral_chartPullbackZero_mul_normSqTransitionC_chart_indep` —
  **chart-overlap invariance**: for `tsupport g ⊆ source i ∩ source j`,
  `∫_ℂ chartPullbackZero i (g · normSq τ_i) = ∫_ℂ chartPullbackZero j (g · normSq τ_j)`.
* `L2PairSummand_eq_integral_in_chart` — each pairing summand may be
  computed in any chart whose source contains `tsupport ρᵢ`.

No `sorry`, no `axiom`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff
open Set Function MeasureTheory

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ## The chart-transition derivative and its cocycle -/

/-- The chart-transition derivative `τ_x y`: the `ℂ`-derivative of the
transition from the chart at the **anchor** `x` to the canonical chart
at the **evaluation point** `y`, taken at the chart-`x` image of `y`.

This is exactly the factor appearing in the transfer lemma
`partialZBarManifoldAtChart_eq_manifold_mul_transition`: the chart-`x`-
anchored coefficient of a (0,1)-form with per-point encoding `α` is
`α y * conj (chartTransitionDerivAt x y)`. -/
def chartTransitionDerivAt (x y : X) : ℂ :=
  deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)

/-- The `normSq` of the chart-transition derivative, coerced to `ℂ`.
This is the weight making the per-chart quadratic density of two
(0,1)-forms chart-independent (`normSqTransitionC_cocycle`). -/
def normSqTransitionC (x y : X) : ℂ :=
  ((Complex.normSq (chartTransitionDerivAt x y) : ℝ) : ℂ)

/-- **Cocycle identity for the chart-transition derivative.** For `y`
in the overlap of the chart sources at `i` and `j`,

  `τ_j y = τ_i y * deriv ((chartAt ℂ i) ∘ (chartAt ℂ j).symm) ((chartAt ℂ j) y)`.

Chain rule through the factorization
`chart_y ∘ chart_j.symm = (chart_y ∘ chart_i.symm) ∘ (chart_i ∘ chart_j.symm)`
near `(chartAt ℂ j) y`, with both factors `ℂ`-differentiable by
analyticity of atlas transitions on a complex-analytic manifold. -/
lemma chartTransitionDerivAt_cocycle [IsManifold 𝓘(ℂ, ℂ) ω X]
    {i j y : X}
    (h_i : y ∈ (chartAt ℂ i).source) (h_j : y ∈ (chartAt ℂ j).source) :
    chartTransitionDerivAt j y
      = chartTransitionDerivAt i y
        * deriv ((chartAt ℂ i) ∘ (chartAt ℂ j).symm) ((chartAt ℂ j) y) := by
  have h_y_src : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  -- Analyticity of the two transition factors.
  have h_A : AnalyticAt ℂ ((chartAt ℂ y) ∘ (chartAt ℂ i).symm)
      ((chartAt ℂ i) y) :=
    analyticAt_chart_transition_of_isManifold
      (chart_mem_atlas ℂ i) (chart_mem_atlas ℂ y) h_i h_y_src
  have h_B : AnalyticAt ℂ ((chartAt ℂ i) ∘ (chartAt ℂ j).symm)
      ((chartAt ℂ j) y) :=
    analyticAt_chart_transition_of_isManifold
      (chart_mem_atlas ℂ j) (chart_mem_atlas ℂ i) h_j h_i
  -- The inner transition's value at `chart_j y` is `chart_i y`.
  have h_B_apply :
      ((chartAt ℂ i) ∘ (chartAt ℂ j).symm) ((chartAt ℂ j) y)
        = (chartAt ℂ i) y := by
    show (chartAt ℂ i) ((chartAt ℂ j).symm ((chartAt ℂ j) y)) = (chartAt ℂ i) y
    rw [(chartAt ℂ j).left_inv h_j]
  -- Eventual equality with the composite on the open overlap preimage.
  have h_V_open : IsOpen ((chartAt ℂ j).target ∩
      (chartAt ℂ j).symm ⁻¹' (chartAt ℂ i).source) :=
    (chartAt ℂ j).isOpen_inter_preimage_symm (chartAt ℂ i).open_source
  have h_mem_V : (chartAt ℂ j) y ∈ (chartAt ℂ j).target ∩
      (chartAt ℂ j).symm ⁻¹' (chartAt ℂ i).source := by
    refine ⟨(chartAt ℂ j).map_source h_j, ?_⟩
    show (chartAt ℂ j).symm ((chartAt ℂ j) y) ∈ (chartAt ℂ i).source
    rw [(chartAt ℂ j).left_inv h_j]
    exact h_i
  have h_evEq :
      ((chartAt ℂ y) ∘ (chartAt ℂ j).symm)
        =ᶠ[nhds ((chartAt ℂ j) y)]
        (((chartAt ℂ y) ∘ (chartAt ℂ i).symm)
          ∘ ((chartAt ℂ i) ∘ (chartAt ℂ j).symm)) := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨_, h_V_open.mem_nhds h_mem_V, ?_⟩
    intro w hw
    obtain ⟨_, hw_pre⟩ := hw
    show (chartAt ℂ y) ((chartAt ℂ j).symm w)
        = (chartAt ℂ y) ((chartAt ℂ i).symm
            ((chartAt ℂ i) ((chartAt ℂ j).symm w)))
    rw [(chartAt ℂ i).left_inv hw_pre]
  -- Differentiability of the outer factor at the composite's basepoint.
  have h_A_diff : DifferentiableAt ℂ ((chartAt ℂ y) ∘ (chartAt ℂ i).symm)
      (((chartAt ℂ i) ∘ (chartAt ℂ j).symm) ((chartAt ℂ j) y)) := by
    rw [h_B_apply]
    exact h_A.differentiableAt
  -- Chain rule.
  show deriv ((chartAt ℂ y) ∘ (chartAt ℂ j).symm) ((chartAt ℂ j) y)
      = chartTransitionDerivAt i y
        * deriv ((chartAt ℂ i) ∘ (chartAt ℂ j).symm) ((chartAt ℂ j) y)
  rw [h_evEq.deriv_eq, deriv_comp _ h_A_diff h_B.differentiableAt, h_B_apply]
  rfl

/-- **`normSq` form of the cocycle**: the quadratic weight transforms
by the real Jacobian `normSq` of the chart transition — exactly the
factor produced by the holomorphic substitution rule. -/
lemma normSqTransitionC_cocycle [IsManifold 𝓘(ℂ, ℂ) ω X]
    {i j y : X}
    (h_i : y ∈ (chartAt ℂ i).source) (h_j : y ∈ (chartAt ℂ j).source) :
    normSqTransitionC j y
      = normSqTransitionC i y
        * ((Complex.normSq
            (deriv ((chartAt ℂ i) ∘ (chartAt ℂ j).symm) ((chartAt ℂ j) y))
              : ℝ) : ℂ) := by
  unfold normSqTransitionC
  rw [chartTransitionDerivAt_cocycle h_i h_j, Complex.normSq_mul,
    Complex.ofReal_mul]

/-! ## Reduction of the plane integral to the chart image of the support -/

/-- For `F` supported inside `S`, the plane integral of
`chartPullbackZero x F` reduces to the set integral over the chart
image `chart_x '' S`: the extended pullback vanishes off that image. -/
private lemma integral_chartPullbackZero_eq_setIntegral_image
    {x : X} {F : X → ℂ} {S : Set X}
    (h_supp : Function.support F ⊆ S) :
    ∫ ζ, chartPullbackZero x F ζ ∂volume
      = ∫ ζ in (chartAt ℂ x) '' S, chartPullbackZero x F ζ ∂volume := by
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
  intro ζ hζ
  by_cases h_tgt : ζ ∈ (chartAt ℂ x).target
  · rw [chartPullbackZero_eq_α_chartSymm_on_target x F h_tgt]
    by_contra h_ne
    have h_mem : (chartAt ℂ x).symm ζ ∈ S := h_supp h_ne
    exact hζ ⟨(chartAt ℂ x).symm ζ, h_mem, (chartAt ℂ x).right_inv h_tgt⟩
  · exact chartPullbackZero_eq_zero_off_target x F h_tgt

/-! ## Chart-overlap invariance of the weighted integral -/

/-- **Chart-overlap invariance of the anchored quadratic-density
integral.** For a density `g : X → ℂ` with topological support inside
the overlap of the chart sources at `i` and `j`, the chart-`i` plane
integral of the `normSq τ_i`-weighted density equals the chart-`j`
plane integral of the `normSq τ_j`-weighted density:

  `∫_ℂ chartPullbackZero i (g · normSqTransitionC i)
     = ∫_ℂ chartPullbackZero j (g · normSqTransitionC j)`.

This is the well-definedness statement for the `L²` pairing of
(0,1)-forms: the per-chart summand does not depend on the anchoring
chart. Unconditional in `g` (no integrability or smoothness needed):
both sides reduce to set integrals over the chart images of
`tsupport g`, which the holomorphic change of variables
(`HolomorphicCoV.setIntegral_image_eq_of_differentiableOn`)
identifies, the `normSq` Jacobian being absorbed by the cocycle
`normSqTransitionC_cocycle`. -/
theorem integral_chartPullbackZero_mul_normSqTransitionC_chart_indep
    [IsManifold 𝓘(ℂ, ℂ) ω X]
    {g : X → ℂ} {i j : X}
    (h_ts : tsupport g ⊆ (chartAt ℂ i).source ∩ (chartAt ℂ j).source) :
    ∫ ζ, chartPullbackZero i (fun y => g y * normSqTransitionC i y) ζ ∂volume
      = ∫ ζ, chartPullbackZero j (fun y => g y * normSqTransitionC j y) ζ
          ∂volume := by
  classical
  -- The open overlap and its chart images.
  have hS_open : IsOpen ((chartAt ℂ i).source ∩ (chartAt ℂ j).source) :=
    (chartAt ℂ i).open_source.inter (chartAt ℂ j).open_source
  have hS_sub_i : (chartAt ℂ i).source ∩ (chartAt ℂ j).source
      ⊆ (chartAt ℂ i).source := Set.inter_subset_left
  have hS_sub_j : (chartAt ℂ i).source ∩ (chartAt ℂ j).source
      ⊆ (chartAt ℂ j).source := Set.inter_subset_right
  -- Supports of the weighted densities lie in the overlap.
  have h_supp_i : Function.support
      (fun y => g y * normSqTransitionC i y)
        ⊆ (chartAt ℂ i).source ∩ (chartAt ℂ j).source := by
    intro y hy
    have hgy : g y ≠ 0 := by
      intro h0
      apply hy
      show g y * normSqTransitionC i y = 0
      rw [h0, zero_mul]
    exact h_ts (subset_tsupport g hgy)
  have h_supp_j : Function.support
      (fun y => g y * normSqTransitionC j y)
        ⊆ (chartAt ℂ i).source ∩ (chartAt ℂ j).source := by
    intro y hy
    have hgy : g y ≠ 0 := by
      intro h0
      apply hy
      show g y * normSqTransitionC j y = 0
      rw [h0, zero_mul]
    exact h_ts (subset_tsupport g hgy)
  -- The chart-j image of the overlap is open.
  have hUj_open : IsOpen
      ((chartAt ℂ j) '' ((chartAt ℂ i).source ∩ (chartAt ℂ j).source)) := by
    rw [(chartAt ℂ j).image_eq_target_inter_inv_preimage hS_sub_j]
    exact (chartAt ℂ j).isOpen_inter_preimage_symm hS_open
  -- The transition maps the chart-j image onto the chart-i image.
  have h_img :
      ((chartAt ℂ i) ∘ (chartAt ℂ j).symm)
          '' ((chartAt ℂ j) '' ((chartAt ℂ i).source ∩ (chartAt ℂ j).source))
        = (chartAt ℂ i) '' ((chartAt ℂ i).source ∩ (chartAt ℂ j).source) := by
    rw [Set.image_comp]
    have h_symm_img : (chartAt ℂ j).symm
        '' ((chartAt ℂ j) '' ((chartAt ℂ i).source ∩ (chartAt ℂ j).source))
          = (chartAt ℂ i).source ∩ (chartAt ℂ j).source := by
      ext z
      constructor
      · rintro ⟨w, ⟨y, hyS, rfl⟩, rfl⟩
        rw [(chartAt ℂ j).left_inv (hS_sub_j hyS)]
        exact hyS
      · intro hz
        exact ⟨(chartAt ℂ j) z, ⟨z, hz, rfl⟩,
          (chartAt ℂ j).left_inv (hS_sub_j hz)⟩
    rw [h_symm_img]
  -- Holomorphy of the transition on the chart-j image.
  have h_diff : DifferentiableOn ℂ ((chartAt ℂ i) ∘ (chartAt ℂ j).symm)
      ((chartAt ℂ j) '' ((chartAt ℂ i).source ∩ (chartAt ℂ j).source)) := by
    rintro w ⟨y, hyS, rfl⟩
    exact (analyticAt_chart_transition_of_isManifold
      (chart_mem_atlas ℂ j) (chart_mem_atlas ℂ i)
      (hS_sub_j hyS) (hS_sub_i hyS)).differentiableAt.differentiableWithinAt
  -- Injectivity of the transition on the chart-j image.
  have h_maps : Set.MapsTo (chartAt ℂ j).symm
      ((chartAt ℂ j) '' ((chartAt ℂ i).source ∩ (chartAt ℂ j).source))
      (chartAt ℂ i).source := by
    rintro w ⟨y, hyS, rfl⟩
    rw [(chartAt ℂ j).left_inv (hS_sub_j hyS)]
    exact hS_sub_i hyS
  have h_inj_symm : Set.InjOn (chartAt ℂ j).symm
      ((chartAt ℂ j) '' ((chartAt ℂ i).source ∩ (chartAt ℂ j).source)) := by
    refine ((chartAt ℂ j).symm.injOn).mono ?_
    rintro w ⟨y, hyS, rfl⟩
    simpa [OpenPartialHomeomorph.symm_source] using
      (chartAt ℂ j).map_source (hS_sub_j hyS)
  have h_inj : Set.InjOn ((chartAt ℂ i) ∘ (chartAt ℂ j).symm)
      ((chartAt ℂ j) '' ((chartAt ℂ i).source ∩ (chartAt ℂ j).source)) :=
    ((chartAt ℂ i).injOn).comp h_inj_symm h_maps
  -- Chain of identifications.
  calc ∫ ζ, chartPullbackZero i (fun y => g y * normSqTransitionC i y) ζ
        ∂volume
      = ∫ ζ in (chartAt ℂ i)
            '' ((chartAt ℂ i).source ∩ (chartAt ℂ j).source),
          chartPullbackZero i (fun y => g y * normSqTransitionC i y) ζ
            ∂volume :=
        integral_chartPullbackZero_eq_setIntegral_image h_supp_i
    _ = ∫ ζ in ((chartAt ℂ i) ∘ (chartAt ℂ j).symm)
            '' ((chartAt ℂ j)
              '' ((chartAt ℂ i).source ∩ (chartAt ℂ j).source)),
          chartPullbackZero i (fun y => g y * normSqTransitionC i y) ζ
            ∂volume := by
        rw [h_img]
    _ = ∫ w in (chartAt ℂ j)
            '' ((chartAt ℂ i).source ∩ (chartAt ℂ j).source),
          ((Complex.normSq
              (deriv ((chartAt ℂ i) ∘ (chartAt ℂ j).symm) w) : ℝ) : ℂ)
            * chartPullbackZero i (fun y => g y * normSqTransitionC i y)
                (((chartAt ℂ i) ∘ (chartAt ℂ j).symm) w) ∂volume :=
        HolomorphicCoV.setIntegral_image_eq_of_differentiableOn
          hUj_open h_diff h_inj _
    _ = ∫ w in (chartAt ℂ j)
            '' ((chartAt ℂ i).source ∩ (chartAt ℂ j).source),
          chartPullbackZero j (fun y => g y * normSqTransitionC j y) w
            ∂volume := by
        refine setIntegral_congr_fun hUj_open.measurableSet ?_
        rintro w ⟨y, hyS, rfl⟩
        have h_yi : y ∈ (chartAt ℂ i).source := hS_sub_i hyS
        have h_yj : y ∈ (chartAt ℂ j).source := hS_sub_j hyS
        have h_φ_apply :
            ((chartAt ℂ i) ∘ (chartAt ℂ j).symm) ((chartAt ℂ j) y)
              = (chartAt ℂ i) y := by
          show (chartAt ℂ i) ((chartAt ℂ j).symm ((chartAt ℂ j) y))
              = (chartAt ℂ i) y
          rw [(chartAt ℂ j).left_inv h_yj]
        show ((Complex.normSq
              (deriv ((chartAt ℂ i) ∘ (chartAt ℂ j).symm) ((chartAt ℂ j) y))
                : ℝ) : ℂ)
            * chartPullbackZero i (fun y => g y * normSqTransitionC i y)
                (((chartAt ℂ i) ∘ (chartAt ℂ j).symm) ((chartAt ℂ j) y))
          = chartPullbackZero j (fun y => g y * normSqTransitionC j y)
              ((chartAt ℂ j) y)
        rw [h_φ_apply,
          chartPullbackZero_eq_α_chartSymm_on_target i _
            ((chartAt ℂ i).map_source h_yi),
          chartPullbackZero_eq_α_chartSymm_on_target j _
            ((chartAt ℂ j).map_source h_yj),
          (chartAt ℂ i).left_inv h_yi, (chartAt ℂ j).left_inv h_yj]
        show ((Complex.normSq
            (deriv ((chartAt ℂ i) ∘ (chartAt ℂ j).symm) ((chartAt ℂ j) y))
              : ℝ) : ℂ)
            * (g y * normSqTransitionC i y)
          = g y * normSqTransitionC j y
        rw [normSqTransitionC_cocycle h_yi h_yj]
        ring
    _ = ∫ ζ, chartPullbackZero j (fun y => g y * normSqTransitionC j y) ζ
          ∂volume :=
        (integral_chartPullbackZero_eq_setIntegral_image h_supp_j).symm

/-! ## The `L²` pairing over a `FiniteChartCoverPartition` -/

section Pairing

variable [T2Space X] [IsManifold 𝓘(ℝ, ℂ) ⊤ X]
variable {cover : FiniteChartCover X}

/-- The `ρ`-weighted, chart-`anchor`-anchored quadratic density of two
(0,1)-forms `al, be` (per-point coefficient encoding): pointwise

  `ρ_idx · al · conj be · normSq τ_anchor`.

With `anchor = idx.val` this is the integrand of `L2PairSummand`; the
free `anchor` form is what the chart-overlap invariance theorem moves
between charts. -/
def pairingIntegrand (P : FiniteChartCoverPartition cover)
    (idx : {x : X // x ∈ cover.basePoints}) (anchor : X)
    (al be : X → ℂ) : X → ℂ :=
  fun y => P.rhoC idx y * al y * (starRingEnd ℂ) (be y)
    * normSqTransitionC anchor y

/-- The chart-`idx` summand of the `L²` pairing: the plane integral of
the chart-pullback (extended by zero) of the `ρ_idx`-weighted anchored
quadratic density, anchored at `idx`'s own chart. -/
def L2PairSummand (P : FiniteChartCoverPartition cover)
    (idx : {x : X // x ∈ cover.basePoints}) (al be : X → ℂ) : ℂ :=
  ∫ ζ, chartPullbackZero idx.val (pairingIntegrand P idx idx.val al be) ζ
    ∂volume

/-- **The `L²` pairing of two (0,1)-forms** (per-point coefficient
encoding) over a finite chart cover with subordinate partition of
unity: the finite sum of the per-chart summands. A working definition
on raw coefficient functions (see the file docstring for the design
choice); the classical pairing `∫_X α ∧ ⋆β̄` in coordinates. -/
def L2PairForms (P : FiniteChartCoverPartition cover)
    (al be : X → ℂ) : ℂ :=
  ∑ idx : {x : X // x ∈ cover.basePoints}, L2PairSummand P idx al be

/-- **Each pairing summand may be computed in any chart containing the
support of its partition function.** If `tsupport ρ_idx ⊆ chart_j.source`,
then the chart-`idx`-anchored summand integral equals the
chart-`j`-anchored one. This is the form chips 3–4 consume: it
collapses the pairing against a test density supported in a single
chart `j` into integrals all living in that one chart. -/
theorem L2PairSummand_eq_integral_in_chart [IsManifold 𝓘(ℂ, ℂ) ω X]
    (P : FiniteChartCoverPartition cover)
    (idx : {x : X // x ∈ cover.basePoints}) {j : X}
    (h_j : tsupport (P.rhoC idx) ⊆ (chartAt ℂ j).source)
    (al be : X → ℂ) :
    L2PairSummand P idx al be
      = ∫ ζ, chartPullbackZero j (pairingIntegrand P idx j al be) ζ
          ∂volume := by
  -- The unweighted density is supported where `ρ_idx` is.
  have h_supp_sub : Function.support
      (fun y => P.rhoC idx y * al y * (starRingEnd ℂ) (be y))
        ⊆ Function.support (P.rhoC idx) := by
    intro y hy h0
    apply hy
    show P.rhoC idx y * al y * (starRingEnd ℂ) (be y) = 0
    rw [h0, zero_mul, zero_mul]
  have h_tsub : tsupport
      (fun y => P.rhoC idx y * al y * (starRingEnd ℂ) (be y))
        ⊆ tsupport (P.rhoC idx) :=
    closure_mono h_supp_sub
  have h_ts : tsupport
      (fun y => P.rhoC idx y * al y * (starRingEnd ℂ) (be y))
        ⊆ (chartAt ℂ idx.val).source ∩ (chartAt ℂ j).source :=
    Set.subset_inter (h_tsub.trans (P.tsupport_rhoC_subset idx))
      (h_tsub.trans h_j)
  exact integral_chartPullbackZero_mul_normSqTransitionC_chart_indep
    (g := fun y => P.rhoC idx y * al y * (starRingEnd ℂ) (be y)) h_ts

end Pairing

end JacobianChallenge

end
