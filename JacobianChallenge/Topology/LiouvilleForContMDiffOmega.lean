/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.HolomorphicLocallyConstantDischarge
import JacobianChallenge.Topology.MeromorphicNonzeroBuilder
import JacobianChallenge.Manifold.ContMDiffOmegaAnalytic
import JacobianChallenge.Manifold.IsConstantMapAux
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.LocallyConstant.Basic

/-! # Liouville constancy for `ContMDiff … ω` functions on compact connected `X`

This file ships a Liouville-style constancy theorem for functions
`F : X → ℂ` of regularity `ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω` on a compact
connected complex 1-manifold `X`, working through the existing
`MeromorphicNonzero` + `liouvilleOnCompactConnected_holds` chain.

The bridge has three steps:

1. **Holomorphicity ⇒ meromorphicity on `Set.univ`.** Using
   `Manifold/ContMDiffOmegaAnalytic.lean`'s
   `contMDiff_omega_analyticAt_chart_pullback`, the chart pullback of `F`
   is `AnalyticAt ℂ` at every chart-image point. Mathlib's
   `AnalyticAt.meromorphicAt` then upgrades each chart pullback to
   `MeromorphicAt`, giving `MMeromorphicOn 𝓘(ℂ, ℂ) F Set.univ`.

2. **Holomorphicity ⇒ order ≥ 0 everywhere.** Mathlib's
   `AnalyticAt.meromorphicOrderAt_nonneg` says the meromorphic order of
   an analytic chart pullback is non-negative; unwrapping the
   `mmeromorphicOrderAt` definition gives `0 ≤ mmeromorphicOrderAt _ F x`
   for every `x : X`.

3. **`MeromorphicNonzero` wrap + Liouville.** From the meromorphicity
   plus a `nonvanishing_germ` hypothesis (taken as an input here — the
   manifold-level analytic-continuation argument that would discharge it
   from `¬ IsConstantMap F` is owed in
   `Manifold/AnalyticContinuationGlobalization.lean` and is not at the
   mathlib pin), assemble a `MeromorphicNonzero X` and feed it to
   `liouvilleOnCompactConnected_holds` (already unconditional in
   `Topology/HolomorphicLocallyConstantDischarge.lean`).

## What the named hypothesis means

`(∀ x : X, mmeromorphicOrderAt 𝓘(ℂ, ℂ) F x ≠ ⊤)` says that at no point
is the chart pullback of `F` identically zero on a punctured chart
neighborhood — equivalently, `F` is not "germ-zero" anywhere. For a
holomorphic function on a *connected* manifold, this is automatic
whenever `F` is not the zero function, by analytic continuation. But
that analytic-continuation argument walks paths through chart overlaps,
and the chart-overlap analyticity bridge across the boundary of one
chart into another is documented as owed in the repo
(`Manifold/AnalyticContinuationGlobalization.lean`'s within-one-chart
limitation, line 60–79). So we take it as a hypothesis here.

## What this file proves (no `sorry`, no `axiom`)

* `mmeromorphicOn_univ_of_contMDiff_omega` — `MMeromorphicOn` from
  `ContMDiff … ω`.

* `mmeromorphicOrderAt_nonneg_of_contMDiff_omega` — `0 ≤ mmeromorphicOrderAt _ F x`
  pointwise from analyticity.

* `MeromorphicNonzero.ofContMDiffOmega` — the builder that consumes
  the `nonvanishing_germ` hypothesis.

* `contMDiff_omega_isConstant_of_nonvanishGerm` — the headline
  Liouville-style constancy.
-/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Step 1: `ContMDiff … ω` ⇒ `MMeromorphicOn _ univ` -/

/-- A function `F : X → ℂ` of regularity `ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω` is
meromorphic on the entire manifold, in the chart-pulled-back sense
(`MMeromorphicOn 𝓘(ℂ, ℂ) F Set.univ`).

Proof: `contMDiff_omega_analyticAt_chart_pullback` gives `AnalyticAt ℂ`
of the chart pullback at every chart-image point. `AnalyticAt.meromorphicAt`
upgrades to `MeromorphicAt`, which is the definition of `MMeromorphicAt`. -/
theorem mmeromorphicOn_univ_of_contMDiff_omega
    {F : X → ℂ}
    (hF : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F) :
    MMeromorphicOn (𝓘(ℂ, ℂ)) F Set.univ := by
  intro x _
  -- chart pullback: `F ∘ (chartAt ℂ x).symm`. For F : X → ℂ the target chart
  -- is the identity on ℂ, so the bridge collapses to this.
  -- `contMDiff_omega_analyticAt_chart_pullback hF x` gives
  -- `AnalyticAt ℂ ((chartAt ℂ (F x)) ∘ F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)`.
  -- For ℂ with the trivial chart structure, `chartAt ℂ (F x) = PartialHomeomorph.refl ℂ`,
  -- so this is `AnalyticAt ℂ (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)`.
  have h_analytic :
      AnalyticAt ℂ ((chartAt ℂ (F x)) ∘ F ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) :=
    JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback hF x
  -- The chart on ℂ is the identity (PartialHomeomorph.refl ℂ), so the composition
  -- simplifies. `chartAt ℂ y = PartialHomeomorph.refl ℂ` for any `y : ℂ`.
  have h_chart_eq :
      (chartAt ℂ (F x)) ∘ F ∘ (chartAt ℂ x).symm = F ∘ (chartAt ℂ x).symm := by
    funext z
    -- chartAt ℂ (F x) on ℂ is PartialHomeomorph.refl ℂ which has identity coe.
    rfl
  rw [h_chart_eq] at h_analytic
  -- Now `AnalyticAt ℂ (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)` ⇒ MeromorphicAt.
  -- `MMeromorphicAt 𝓘(ℂ, ℂ) F x` unfolds to `MeromorphicAt (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)`.
  exact h_analytic.meromorphicAt

/-! ## Step 2: `ContMDiff … ω` ⇒ order ≥ 0 -/

/-- A function `F : X → ℂ` of regularity `ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω` has
non-negative `mmeromorphicOrderAt` at every point. -/
theorem mmeromorphicOrderAt_nonneg_of_contMDiff_omega
    {F : X → ℂ}
    (hF : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F) (x : X) :
    0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) F x := by
  -- Same chart-pullback bridge as in step 1.
  have h_analytic :
      AnalyticAt ℂ ((chartAt ℂ (F x)) ∘ F ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) :=
    JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback hF x
  have h_chart_eq :
      (chartAt ℂ (F x)) ∘ F ∘ (chartAt ℂ x).symm = F ∘ (chartAt ℂ x).symm := by
    funext z; rfl
  rw [h_chart_eq] at h_analytic
  -- `mmeromorphicOrderAt 𝓘(ℂ,ℂ) F x = meromorphicOrderAt (F ∘ chart.symm) (chart x)`.
  show 0 ≤ meromorphicOrderAt (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  exact h_analytic.meromorphicOrderAt_nonneg

/-! ## Step 3: `MeromorphicNonzero` builder + Liouville -/

/-- **Builder: `MeromorphicNonzero X` from `ContMDiff … ω` and
`nonvanishing_germ`.** The `nonvanishing_germ` hypothesis is taken as
input — it is the analytic-continuation content owed in
`Manifold/AnalyticContinuationGlobalization.lean`. -/
def MeromorphicNonzero.ofContMDiffOmega
    (F : X → ℂ)
    (h_smooth : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F)
    (h_nonvanish : ∀ x : X, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) F x ≠ ⊤) :
    MeromorphicNonzero X :=
  JacobianChallenge.MeromorphicNonzero.ofContinuousMeromorphic
    F
    (mmeromorphicOn_univ_of_contMDiff_omega h_smooth)
    h_nonvanish
    h_smooth.continuous

@[simp]
lemma MeromorphicNonzero.ofContMDiffOmega_toFun
    (F : X → ℂ)
    (h_smooth : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F)
    (h_nonvanish : ∀ x : X, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) F x ≠ ⊤) :
    (MeromorphicNonzero.ofContMDiffOmega F h_smooth h_nonvanish).toFun = F := rfl

/-- **Liouville for `ContMDiff … ω` functions.** A holomorphic
`F : X → ℂ` on a compact connected complex 1-manifold with no germ-zero
point is constant.

The "no germ-zero" hypothesis is automatic for an `F` that is not
identically zero on a connected `X` (by manifold-level analytic
continuation), but the analytic-continuation argument is owed in
`Manifold/AnalyticContinuationGlobalization.lean` and is therefore
taken as an explicit hypothesis here. -/
theorem contMDiff_omega_isConstant_of_nonvanishGerm
    (F : X → ℂ)
    (h_smooth : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F)
    (h_nonvanish : ∀ x : X, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) F x ≠ ⊤) :
    IsConstantMap F := by
  -- Wrap F as MeromorphicNonzero.
  let f : MeromorphicNonzero X :=
    MeromorphicNonzero.ofContMDiffOmega F h_smooth h_nonvanish
  -- f.toFun = F, with order ≥ 0 everywhere.
  have h_order : ∀ x, 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x := by
    intro x
    show 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) F x
    exact mmeromorphicOrderAt_nonneg_of_contMDiff_omega h_smooth x
  -- Apply the unconditional Liouville for MeromorphicNonzero.
  have h_const : JacobianChallenge.IsConstantMap f.toFun :=
    liouvilleOnCompactConnected_holds X f h_order
  -- f.toFun = F, so IsConstantMap F.
  exact h_const

/-! ## Discharge of `nonvanishGerm` in the `never-zero` case -/

/-- **From `F` never zero to `nonvanishingGerm`.** If `F : X → ℂ` is
`ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω` and never zero, then `mmeromorphicOrderAt _ F x ≠ ⊤`
at every point. The chart pullback is analytic with value `F x ≠ 0`, so
its analytic order at `(chartAt ℂ x) x` is `0`, hence its meromorphic
order is `0` (in `WithTop ℤ`), in particular `≠ ⊤`. -/
theorem mmeromorphicOrderAt_ne_top_of_contMDiff_omega_neverZero
    {F : X → ℂ}
    (hF : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F)
    (h_ne_zero : ∀ x : X, F x ≠ 0) (x : X) :
    mmeromorphicOrderAt (𝓘(ℂ, ℂ)) F x ≠ ⊤ := by
  -- Chart pullback is AnalyticAt; the trivial chart on ℂ collapses the
  -- left composition away.
  have h_analytic :
      AnalyticAt ℂ ((chartAt ℂ (F x)) ∘ F ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) :=
    JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback hF x
  have h_chart_eq :
      (chartAt ℂ (F x)) ∘ F ∘ (chartAt ℂ x).symm = F ∘ (chartAt ℂ x).symm := by
    funext z; rfl
  rw [h_chart_eq] at h_analytic
  -- Value at chart x: F (chart.symm (chart x)) = F x ≠ 0 by chart.left_inv.
  have h_value : (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0 := by
    show F ((chartAt ℂ x).symm ((chartAt ℂ x) x)) ≠ 0
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
    exact h_ne_zero x
  -- AnalyticAt + value ≠ 0 ⇒ analyticOrderAt = 0.
  have h_ord_zero :
      analyticOrderAt (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0 :=
    h_analytic.analyticOrderAt_eq_zero.mpr h_value
  -- meromorphicOrderAt = (analyticOrderAt).map (↑) — definition unfolds to
  -- the same chart-pullback computation as mmeromorphicOrderAt.
  show meromorphicOrderAt (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ ⊤
  rw [h_analytic.meromorphicOrderAt_eq, h_ord_zero]
  simp

/-- **Liouville for `ContMDiff … ω` AND never-zero functions.** Fully
unconditional in the never-zero sub-case: the `nonvanishingGerm`
hypothesis of `contMDiff_omega_isConstant_of_nonvanishGerm` is discharged
by `mmeromorphicOrderAt_ne_top_of_contMDiff_omega_neverZero`. -/
theorem contMDiff_omega_isConstant_of_neverZero
    (F : X → ℂ)
    (h_smooth : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F)
    (h_ne_zero : ∀ x : X, F x ≠ 0) :
    IsConstantMap F :=
  contMDiff_omega_isConstant_of_nonvanishGerm F h_smooth
    (mmeromorphicOrderAt_ne_top_of_contMDiff_omega_neverZero h_smooth h_ne_zero)

/-! ## Unconditional Liouville via the `exp` trick

For a *general* `ContMDiff … ω` function `F : X → ℂ` (which may have
zeros) on a compact connected complex 1-manifold, `Complex.exp ∘ F` is
holomorphic and **never zero**. By the never-zero Liouville above,
`exp ∘ F` is constant. From there:

* For every `x`, `F x - F x₀` is in the kernel of `exp`, which equals
  `2π i · ℤ` (`Complex.exp_eq_exp_iff_exists_int`).
* `F` is continuous, so around any point `x`, choosing the open
  neighborhood `F ⁻¹' Metric.ball (F x) (2π)`, every `y` in it has
  `‖F y - F x‖ < 2π`. But `F y - F x = (n_y - n_x) · 2π i ∈ 2π i · ℤ`,
  and the only element of `2π i · ℤ` with norm `< 2π` is `0`.
* So `F y = F x` on the neighborhood, i.e. `F` is locally constant.
* Connected `X` then forces `F` to be (globally) constant.

This closes the Liouville chain without any `nonvanishingGerm`
hypothesis. -/

/-- `Complex.exp : ℂ → ℂ` is `ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω`. Bridge from
mathlib's `analyticOnNhd_cexp` via `contMDiff_iff_contDiff` and
`contDiff_omega_iff_analyticOnNhd`. -/
theorem contMDiff_omega_complex_exp :
    ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (Complex.exp : ℂ → ℂ) := by
  rw [contMDiff_iff_contDiff]
  exact contDiff_omega_iff_analyticOnNhd.mpr analyticOnNhd_cexp

/-- `Complex.exp ∘ F` is `ContMDiff ω` when `F` is. -/
theorem contMDiff_omega_complex_exp_comp
    {F : X → ℂ} (hF : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F) :
    ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (Complex.exp ∘ F) :=
  contMDiff_omega_complex_exp.comp hF

/-- **Unconditional Liouville for `ContMDiff … ω` functions** on compact
connected complex 1-manifolds. No `nonvanishingGerm` or `never-zero`
hypothesis is required: the `exp` trick reduces the general case to the
never-zero case, then a discrete-target/local-constancy argument closes
the chain. -/
theorem contMDiff_omega_isConstant
    (F : X → ℂ)
    (h_smooth : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F) :
    IsConstantMap F := by
  haveI : Nonempty X := inferInstance
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  -- Step 1: exp ∘ F is ContMDiff ω and never zero, hence constant.
  have h_exp_smooth : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (Complex.exp ∘ F) :=
    contMDiff_omega_complex_exp_comp h_smooth
  have h_exp_ne_zero : ∀ x : X, (Complex.exp ∘ F) x ≠ 0 := fun x =>
    Complex.exp_ne_zero (F x)
  obtain ⟨c, hc⟩ : IsConstantMap (Complex.exp ∘ F) :=
    contMDiff_omega_isConstant_of_neverZero
      (Complex.exp ∘ F) h_exp_smooth h_exp_ne_zero
  -- Step 2: for all x, F x - F x₀ ∈ 2π i · ℤ.
  have h_diff_lattice :
      ∀ x : X, ∃ n : ℤ, F x - F x₀ = (n : ℂ) * (2 * Real.pi * Complex.I) := by
    intro x
    have h_exp_eq : Complex.exp (F x) = Complex.exp (F x₀) := by
      have h1 : Complex.exp (F x) = c := hc x
      have h2 : Complex.exp (F x₀) = c := hc x₀
      rw [h1, h2]
    rw [Complex.exp_eq_exp_iff_exists_int] at h_exp_eq
    obtain ⟨n, hn⟩ := h_exp_eq
    refine ⟨n, ?_⟩
    -- hn : F x = F x₀ + n * (2 * π * I)
    -- goal : F x - F x₀ = (n : ℂ) * (2 * π * I)
    linear_combination hn
  -- Step 3: F is locally constant. For each x, choose the open neighborhood
  -- `F ⁻¹' Metric.ball (F x) (2π)`.
  have h_pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hF_cont : Continuous F := h_smooth.continuous
  have h_locally_const : IsLocallyConstant F := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨F ⁻¹' Metric.ball (F x) (2 * Real.pi),
      Metric.isOpen_ball.preimage hF_cont, ?_, ?_⟩
    · -- x is in the preimage: F x ∈ Metric.ball (F x) (2π)
      simp [Metric.mem_ball, h_pi_pos]
    intro y hy
    -- ‖F y - F x‖ < 2π
    have h_dist : ‖F y - F x‖ < 2 * Real.pi := by
      have := hy
      rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at this
      exact this
    -- F y - F x = (n_y - n_x : ℤ) · 2π i
    obtain ⟨n_y, hn_y⟩ := h_diff_lattice y
    obtain ⟨n_x, hn_x⟩ := h_diff_lattice x
    have h_diff_eq :
        F y - F x = ((n_y - n_x : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      have h_decomp : F y - F x = (F y - F x₀) - (F x - F x₀) := by ring
      rw [h_decomp, hn_y, hn_x]
      push_cast
      ring
    -- ‖((n_y - n_x : ℤ) : ℂ) · 2π i‖ = |n_y - n_x| · 2π
    have h_norm_2piI : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_I, mul_one]
      have h_cast : ((2 * Real.pi : ℝ) : ℂ) = (2 : ℂ) * (Real.pi : ℂ) := by
        push_cast; ring
      rw [← h_cast, Complex.norm_real, Real.norm_of_nonneg h_pi_pos.le]
    have h_norm_calc :
        ‖((n_y - n_x : ℤ) : ℂ) * (2 * Real.pi * Complex.I)‖
          = (|n_y - n_x| : ℝ) * (2 * Real.pi) := by
      rw [norm_mul, h_norm_2piI, Complex.norm_intCast]
      push_cast
      rfl
    rw [h_diff_eq, h_norm_calc] at h_dist
    -- |n_y - n_x| · 2π < 2π ⇒ |n_y - n_x| < 1 ⇒ n_y = n_x
    have h_abs_lt_one : (|n_y - n_x| : ℝ) < 1 := by
      have h := (div_lt_one h_pi_pos).mpr h_dist
      rwa [mul_div_assoc, div_self h_pi_pos.ne', mul_one] at h
    have h_int_abs_lt_one : |n_y - n_x| < 1 := by exact_mod_cast h_abs_lt_one
    have h_int_eq : n_y = n_x := by
      have := h_int_abs_lt_one
      rw [abs_lt] at this
      omega
    -- Conclude F y = F x.
    have h_F_diff_zero : F y - F x = 0 := by
      rw [h_diff_eq, h_int_eq]
      push_cast
      ring
    exact sub_eq_zero.mp h_F_diff_zero
  -- Step 4: F locally constant on connected ⇒ constant.
  haveI : PreconnectedSpace X := inferInstance
  have hF_const : F = Function.const X (F x₀) := h_locally_const.eq_const x₀
  refine ⟨F x₀, fun x => ?_⟩
  have := congrFun hF_const x
  exact this

end JacobianChallenge

end
