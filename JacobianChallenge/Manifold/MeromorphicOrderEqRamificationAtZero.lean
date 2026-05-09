/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RamificationIndex
import JacobianChallenge.Manifold.MeromorphicExtension

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Identification at zeros: ramification index ↔ meromorphic order (chartN side)

At a zero `x` of `f : MeromorphicNonzero X`, i.e. a point with
`f.toRiemannSphere x = ((0 : ℂ) : RiemannSphere)`, we have
`f.toFun x = 0` and `0 ≤ mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x`.
The pole-extension `f.toRiemannSphere` lands in the regular branch
`(some ∘ f.toFun)` on a full neighbourhood of `x`, and the codomain
chart at `f.toRiemannSphere x = some 0` is the north chart `chartN`,
which is the inclusion `OnePoint.some` inverted. Therefore the chart
pullback used in `manifoldRamificationIndex` agrees, on a neighbourhood
of `(chartAt ℂ x) x`, with `f.toFun ∘ (chartAt ℂ x).symm`, and both
representatives are analytic at `(chartAt ℂ x) x` with value `0` there.

The analytic order of that representative — through
`AnalyticAt.meromorphicOrderAt_eq` — equals the meromorphic order of
the chart pullback, hence (definitionally) `mmeromorphicOrderAt 𝓘(ℂ,ℂ)
f.toFun x`. Taking `.toNat` on the analytic side and `.untop₀.natAbs`
on the meromorphic side gives the headline identity.

No `sorry`, no `axiom`. -/

@[expose] public section

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set OnePoint

namespace JacobianChallenge

namespace Manifold

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Helper.** At a zero of `f` (i.e. `f.toRiemannSphere x = some 0`),
the order of `f.toFun` at `x` (as an element of `WithTop ℤ`) is `≥ 0`.

The pole branch of `toRiemannSphere` sends pole points to `∞ ≠ some 0`,
so the hypothesis rules out `mmeromorphicOrderAt < 0`. -/
lemma nonneg_order_of_toRiemannSphere_eq_zero
    (f : JacobianChallenge.MeromorphicNonzero X) {x : X}
    (hx_zero : f.toRiemannSphere x = (((0 : ℂ) : RiemannSphere))) :
    0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x := by
  by_contra hneg
  push_neg at hneg
  have h_inf : f.toRiemannSphere x = (∞ : RiemannSphere) :=
    JacobianChallenge.MeromorphicNonzero.toRiemannSphere_apply_of_neg f hneg
  -- `((0 : ℂ) : RiemannSphere) = OnePoint.some 0 ≠ ∞`.
  have h_ne : (((0 : ℂ) : RiemannSphere)) ≠ (∞ : RiemannSphere) :=
    OnePoint.coe_ne_infty (0 : ℂ)
  exact h_ne (hx_zero.symm.trans h_inf)

/-- **Helper.** At a zero of `f`, `f.toFun x = 0` (extracted from the
`toRiemannSphere` value via `OnePoint.some` injectivity, after the
regular-branch unfolding). -/
lemma toFun_eq_zero_of_toRiemannSphere_eq_zero
    (f : JacobianChallenge.MeromorphicNonzero X) {x : X}
    (hx_zero : f.toRiemannSphere x = (((0 : ℂ) : RiemannSphere))) :
    f.toFun x = 0 := by
  have hx_nonneg : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x :=
    nonneg_order_of_toRiemannSphere_eq_zero f hx_zero
  have h_some : f.toRiemannSphere x =
      (OnePoint.some (f.toFun x) : RiemannSphere) :=
    JacobianChallenge.MeromorphicNonzero.toRiemannSphere_apply_of_nonneg f hx_nonneg
  -- Combine with `hx_zero`: `some (f.toFun x) = some 0` ⇒ `f.toFun x = 0`.
  have h_eq : (OnePoint.some (f.toFun x) : RiemannSphere) =
      (OnePoint.some (0 : ℂ) : RiemannSphere) := by
    rw [← h_some, hx_zero]
  exact OnePoint.coe_injective h_eq

/-- **Helper.** At a zero of `f`, the codomain chart selected by the
`ChartedSpace` instance on `RiemannSphere` is the north chart
`RiemannSphere.chartN`. -/
lemma chartAt_codomain_eq_chartN_at_zero
    (f : JacobianChallenge.MeromorphicNonzero X) {x : X}
    (hx_zero : f.toRiemannSphere x = (((0 : ℂ) : RiemannSphere))) :
    chartAt ℂ (f.toRiemannSphere x) = RiemannSphere.chartN := by
  rw [hx_zero]
  exact JacobianChallenge.chartAt_riemannSphere_coe (0 : ℂ)

/-- **Helper.** Under the chartN coercion at the zero point,
`chartN (f.toRiemannSphere x) = 0`. -/
lemma chartN_apply_toRiemannSphere_at_zero
    (f : JacobianChallenge.MeromorphicNonzero X) {x : X}
    (hx_zero : f.toRiemannSphere x = (((0 : ℂ) : RiemannSphere))) :
    RiemannSphere.chartN (f.toRiemannSphere x) = 0 := by
  rw [hx_zero, JacobianChallenge.RiemannSphere.chartN_apply_coe]

/-- **Headline identification at a zero.** At a zero `x` of `f`, the
manifold-side ramification index of the pole extension equals
`(mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x).untop₀.natAbs`.

Both sides count the multiplicity of vanishing of the chart-pulled-back
representative `f.toFun ∘ (chartAt ℂ x).symm` at `(chartAt ℂ x) x`,
read off as a natural number. -/
theorem mmeromorphicOrderAt_eq_ramificationIndex_at_zero
    (f : JacobianChallenge.MeromorphicNonzero X) (x : X)
    (hx_zero : f.toRiemannSphere x = (((0 : ℂ) : RiemannSphere))) :
    (manifoldRamificationIndex f.toRiemannSphere x : ℕ) =
      (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀.natAbs := by
  -- Set notation.
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀
  have hx_nonneg : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x :=
    nonneg_order_of_toRiemannSphere_eq_zero f hx_zero
  have hf_xval : f.toFun x = 0 :=
    toFun_eq_zero_of_toRiemannSphere_eq_zero f hx_zero
  -- The codomain chart equals `chartN`.
  have h_chartCod : chartAt ℂ (f.toRiemannSphere x) = RiemannSphere.chartN :=
    chartAt_codomain_eq_chartN_at_zero f hx_zero
  -- Build chart-pullback representative `F` and its value at `z₀`.
  set F : ℂ → ℂ :=
    (chartAt ℂ (f.toRiemannSphere x)) ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm
    with hF
  -- `F z₀ = chartN (f.toRiemannSphere x) = 0`.
  have hFz₀ : F z₀ = 0 := by
    show (chartAt ℂ (f.toRiemannSphere x)) (f.toRiemannSphere ((chartAt ℂ x).symm z₀)) = 0
    have h_inv : (chartAt ℂ x).symm z₀ = x :=
      (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
    rw [h_inv, h_chartCod]
    exact chartN_apply_toRiemannSphere_at_zero f hx_zero
  -- The chartN-side local form gives `F =ᶠ[𝓝 z₀] f.toFun ∘ chart.symm`.
  -- We rewrite the codomain chart slot to `chartN` so the lemma applies.
  have h_local : F =ᶠ[𝓝 z₀] (f.toFun ∘ (chartAt ℂ x).symm) := by
    -- Compose with `h_chartCod` to swap the codomain chart for `chartN`.
    have h_localN :
        (RiemannSphere.chartN ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm)
          =ᶠ[𝓝 z₀] (f.toFun ∘ (chartAt ℂ x).symm) :=
      JacobianChallenge.MeromorphicNonzero.toRiemannSphere_chartN_localForm f hx_nonneg
    -- `F = chartN ∘ ...` by `h_chartCod`, so the EventuallyEq transports.
    have h_eqFun :
        F = (RiemannSphere.chartN ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm) := by
      show (chartAt ℂ (f.toRiemannSphere x)) ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm
          = RiemannSphere.chartN ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm
      rw [h_chartCod]
    rw [h_eqFun]
    exact h_localN
  -- Build EventuallyEq `(F · - F z₀) =ᶠ[𝓝 z₀] f.toFun ∘ chart.symm`
  -- (using `F z₀ = 0` and `(f.toFun ∘ chart.symm) z₀ = 0`).
  have h_shift : (fun z => F z - F z₀)
      =ᶠ[𝓝 z₀] (f.toFun ∘ (chartAt ℂ x).symm) := by
    rw [hFz₀]
    -- Goal: `(fun z => F z - 0) =ᶠ[𝓝 z₀] f.toFun ∘ chart.symm`.
    -- The literal `-0` simplifies; transport from `h_local`.
    have h_id : (fun z : ℂ => F z - 0) = F := by funext z; rw [sub_zero]
    rw [h_id]
    exact h_local
  -- LHS of headline: unfold `manifoldRamificationIndex`.
  rw [manifoldRamificationIndex_eq f.toRiemannSphere x]
  -- Now goal:
  --   (analyticOrderAt (fun z => F z - F z₀) z₀).toNat
  -- = (mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x).untop₀.natAbs
  -- (note: `F` and `z₀` are the same `let`-bound names as in the lemma).
  -- Step A: rewrite the analytic order via `h_shift`.
  rw [analyticOrderAt_congr h_shift]
  -- Goal:
  --   (analyticOrderAt (f.toFun ∘ (chartAt ℂ x).symm) z₀).toNat
  -- = (mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x).untop₀.natAbs
  -- Step B: bridge analytic order ↔ meromorphic order via analyticity.
  have h_an : AnalyticAt ℂ (f.toFun ∘ (chartAt ℂ x).symm) z₀ := by
    -- Reuse the chart-pullback analyticity at non-pole points (re-proved
    -- inline, since the existing version is `private`).
    have h_mero : MeromorphicAt (f.toFun ∘ (chartAt ℂ x).symm) z₀ :=
      f.meromorphic x trivial
    -- Continuity of `f.toFun ∘ chart.symm` at `z₀`: chart symm is continuous
    -- there, image is `x`, and `f.toFun` is continuous at `x` because
    -- `0 ≤ order` (use `regular_continuousAt`).
    have h_chart_continuousAt :
        ContinuousAt (chartAt ℂ x).symm z₀ := by
      have h_open : IsOpen (chartAt ℂ x).target := (chartAt ℂ x).open_target
      have h_in : z₀ ∈ (chartAt ℂ x).target :=
        (chartAt ℂ x).map_source (mem_chart_source ℂ x)
      have h_co : ContinuousOn (chartAt ℂ x).symm (chartAt ℂ x).target :=
        (chartAt ℂ x).continuousOn_invFun
      exact h_co.continuousAt (h_open.mem_nhds h_in)
    have h_pt : (chartAt ℂ x).symm z₀ = x :=
      (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
    have h_f_continuousAt : ContinuousAt f.toFun x :=
      f.regular_continuousAt x hx_nonneg
    have h_f_at_pt : ContinuousAt f.toFun ((chartAt ℂ x).symm z₀) := by
      rw [h_pt]; exact h_f_continuousAt
    have h_cont : ContinuousAt (f.toFun ∘ (chartAt ℂ x).symm) z₀ :=
      h_f_at_pt.comp h_chart_continuousAt
    exact h_mero.analyticAt h_cont
  -- `h_mero_eq` : `meromorphicOrderAt h z₀ = (analyticOrderAt h z₀).map (↑ : ℕ → ℤ)`.
  have h_mero_eq :
      meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm) z₀
        = (analyticOrderAt (f.toFun ∘ (chartAt ℂ x).symm) z₀).map (↑· : ℕ → ℤ) :=
    h_an.meromorphicOrderAt_eq
  -- And `mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x` is *definitionally* the chart
  -- pullback `meromorphicOrderAt (f.toFun ∘ chart.symm) z₀`.
  have h_mmero :
      mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x
        = meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm) z₀ := rfl
  -- Combine: `mmeromorphicOrderAt = (analyticOrderAt h z₀).map (↑)`.
  have h_combined :
      mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x
        = (analyticOrderAt (f.toFun ∘ (chartAt ℂ x).symm) z₀).map (↑· : ℕ → ℤ) := by
    rw [h_mmero, h_mero_eq]
  -- Case-split on the analytic order via explicit `match` semantics:
  -- introduce a name for it, then `rcases` on the `WithTop` constructor.
  set α : ℕ∞ := analyticOrderAt (f.toFun ∘ (chartAt ℂ x).symm) z₀ with hα
  -- It cannot be `⊤` (else `mmeromorphicOrderAt = ⊤`, contradicting
  -- `nonvanishing_germ`).
  have h_α_ne_top : α ≠ ⊤ := by
    intro h_top
    have h_top_int : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x = ⊤ := by
      rw [h_combined, h_top]
      simp
    exact f.nonvanishing_germ x h_top_int
  -- Extract the underlying `ℕ` value: `α = (n : ℕ∞)` for some `n : ℕ`.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, α = (n : ℕ∞) := by
    cases h : α with
    | top => exact absurd h h_α_ne_top
    | coe m => exact ⟨m, rfl⟩
  -- Substitute `α = (n : ℕ∞)` everywhere we need it.
  rw [hn]
  -- Goal: `((n : ℕ∞)).toNat = (mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x).untop₀.natAbs`.
  -- Compute `mmeromorphicOrderAt = ((n : ℤ) : WithTop ℤ)` via `h_combined`.
  have h_mmero_val :
      mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x = ((n : ℤ) : WithTop ℤ) := by
    rw [h_combined, hn]
    simp [ENat.map_coe]
  rw [h_mmero_val]
  -- Both sides reduce to `n` via `simp`.
  simp

end Manifold

end JacobianChallenge
