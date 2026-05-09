/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RamificationIndex
import JacobianChallenge.Manifold.MeromorphicExtension
import JacobianChallenge.Divisor.PrincipalDivisor

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Identification at poles: ramification index ↔ meromorphic order (chartS side)

At a pole `x` of `f : MeromorphicNonzero X`, i.e. a point with
`f.toRiemannSphere x = (∞ : RiemannSphere)`, we have
`mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x < 0`. The pole-extension
`f.toRiemannSphere` lands in the south chart `chartS`, which sends
`∞ ↦ 0` and `(some w) ↦ w⁻¹`. The chart-pulled-back representative

  `F z := chartS ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm`

agrees with the chart-pulled-back inverse `(f.toFun ∘ (chartAt ℂ x).symm)⁻¹`
on a *punctured* neighbourhood of `(chartAt ℂ x) x`, and equals
`chartS ∞ = 0` at `(chartAt ℂ x) x` itself.

Two `WithTop ℤ`-level identities pin down the answer:

* `meromorphicOrderAt F z₀` is the analytic order of `F` (since `F`
  extends analytically to a `0` at `z₀`), coerced via `↑ : ℕ → ℤ`.
* `meromorphicOrderAt F z₀ = -mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x`,
  by combining `meromorphicOrderAt_congr` on the punctured-nhd identity
  `F = (f.toFun ∘ chart.symm)⁻¹` with mathlib's `meromorphicOrderAt_inv`.

Putting the two together at a pole (where `mmeromorphicOrderAt _ _ x < 0`)
yields the headline:

  `manifoldRamificationIndex f.toRiemannSphere x
     = (mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x).untop₀.natAbs`.

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

/-- **Helper.** At a pole of `f` (i.e. `f.toRiemannSphere x = ∞`),
the order of `f.toFun` at `x` (as an element of `WithTop ℤ`) is `< 0`. -/
lemma neg_order_of_toRiemannSphere_eq_infty
    (f : JacobianChallenge.MeromorphicNonzero X) {x : X}
    (hx_pole : f.toRiemannSphere x = (∞ : RiemannSphere)) :
    mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0 := by
  exact (JacobianChallenge.MeromorphicNonzero.toRiemannSphere_eq_infty_iff_neg
    f x).mp hx_pole

/-- **Helper.** At a pole of `f`, the codomain chart selected by the
`ChartedSpace` instance on `RiemannSphere` is the south chart
`RiemannSphere.chartS`. -/
lemma chartAt_codomain_eq_chartS_at_pole
    (f : JacobianChallenge.MeromorphicNonzero X) {x : X}
    (hx_pole : f.toRiemannSphere x = (∞ : RiemannSphere)) :
    chartAt ℂ (f.toRiemannSphere x) = RiemannSphere.chartS := by
  rw [hx_pole]
  exact JacobianChallenge.chartAt_riemannSphere_infty

/-- **Helper.** The chart-pulled-back composition `chartS ∘ f.toRiemannSphere
∘ chart.symm` evaluates to `0` at `(chartAt ℂ x) x` whenever
`f.toRiemannSphere x = ∞`. -/
lemma chartS_chartPullback_apply_at_pole
    (f : JacobianChallenge.MeromorphicNonzero X) {x : X}
    (hx_pole : f.toRiemannSphere x = (∞ : RiemannSphere)) :
    (RiemannSphere.chartS ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) = (0 : ℂ) := by
  show RiemannSphere.chartS (f.toRiemannSphere ((chartAt ℂ x).symm
      ((chartAt ℂ x) x))) = 0
  rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x), hx_pole]
  exact RiemannSphere.chartS_apply_infty

/-- **Helper.** The chart-pulled-back composition `chartS ∘ f.toRiemannSphere
∘ chart.symm` is meromorphic at `(chartAt ℂ x) x`. Inline reproof
(public version is `private` in `MeromorphicExtension.lean`). -/
lemma meromorphicAt_chartS_chartPullback_at_pole
    (f : JacobianChallenge.MeromorphicNonzero X) {x : X}
    (hx_pole : f.toRiemannSphere x = (∞ : RiemannSphere)) :
    MeromorphicAt
        (RiemannSphere.chartS ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) := by
  have hx : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0 :=
    neg_order_of_toRiemannSphere_eq_infty f hx_pole
  have h_inv_mero : MeromorphicAt
      (f.toFun ∘ (chartAt ℂ x).symm)⁻¹ ((chartAt ℂ x) x) :=
    (f.meromorphic x trivial).inv
  have h_local := f.toRiemannSphere_chartS_localForm_punctured hx
  exact (MeromorphicAt.meromorphicAt_congr h_local).mpr h_inv_mero

/-- **Helper.** The chart-pulled-back composition `chartS ∘ f.toRiemannSphere
∘ chart.symm` is continuous at `(chartAt ℂ x) x`. Inline reproof. -/
lemma continuousAt_chartS_chartPullback_at_pole
    (f : JacobianChallenge.MeromorphicNonzero X) {x : X}
    (hx_pole : f.toRiemannSphere x = (∞ : RiemannSphere)) :
    ContinuousAt
        (RiemannSphere.chartS ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) := by
  have hx : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0 :=
    neg_order_of_toRiemannSphere_eq_infty f hx_pole
  rw [ContinuousAt]
  have h_val_at_x :
      (RiemannSphere.chartS ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm)
          ((chartAt ℂ x) x) = (0 : ℂ) :=
    chartS_chartPullback_apply_at_pole f hx_pole
  rw [h_val_at_x]
  rw [show (𝓝 ((chartAt ℂ x) x)) =
        𝓝[≠] ((chartAt ℂ x) x) ⊔ pure ((chartAt ℂ x) x)
      from (nhdsNE_sup_pure ((chartAt ℂ x) x)).symm]
  rw [Filter.tendsto_sup]
  refine ⟨?_, ?_⟩
  · -- Punctured branch: use `chartS_localForm_punctured` to reduce to
    -- `(f.toFun ∘ chart.symm)⁻¹`, which → 0 by `tendsto_zero_of_meromorphicOrderAt_pos`.
    have h_local := f.toRiemannSphere_chartS_localForm_punctured hx
    refine Filter.Tendsto.congr' h_local.symm ?_
    -- Positive order of the inverse pulls.
    have h_pos :
        0 < meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm)⁻¹
              ((chartAt ℂ x) x) := by
      have h_orderEq :
          mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x
            = meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm)
                ((chartAt ℂ x) x) := rfl
      rw [h_orderEq] at hx
      rw [meromorphicOrderAt_inv]
      have h_ne_top : meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm)
          ((chartAt ℂ x) x) ≠ ⊤ := fun h => by
        rw [h] at hx; exact absurd hx (not_lt.mpr le_top)
      cases h_eq : meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm)
          ((chartAt ℂ x) x) with
      | top => exact absurd h_eq h_ne_top
      | coe n =>
        rw [h_eq] at hx
        have h_n_neg : n < 0 := by exact_mod_cast hx
        show (0 : WithTop ℤ) < ((-n : ℤ) : WithTop ℤ)
        exact_mod_cast (neg_pos.mpr h_n_neg)
    have h_tend :=
      tendsto_zero_of_meromorphicOrderAt_pos
        (f := (f.toFun ∘ (chartAt ℂ x).symm)⁻¹)
        (x := (chartAt ℂ x) x) h_pos
    convert h_tend using 1
  · -- Pure branch: reduce to `0 ∈ s` for `s ∈ 𝓝 0`.
    refine (Filter.tendsto_pure_left).mpr ?_
    intro s hs
    rw [h_val_at_x]
    exact mem_of_mem_nhds hs

/-- **Helper.** The chart-pulled-back composition `chartS ∘ f.toRiemannSphere
∘ chart.symm` is analytic at `(chartAt ℂ x) x`. -/
lemma analyticAt_chartS_chartPullback_at_pole
    (f : JacobianChallenge.MeromorphicNonzero X) {x : X}
    (hx_pole : f.toRiemannSphere x = (∞ : RiemannSphere)) :
    AnalyticAt ℂ
        (RiemannSphere.chartS ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) :=
  (meromorphicAt_chartS_chartPullback_at_pole f hx_pole).analyticAt
    (continuousAt_chartS_chartPullback_at_pole f hx_pole)

/-- **Headline identification at a pole.** At a pole `x` of `f`, the
manifold-side ramification index of the pole extension equals
`(mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x).untop₀.natAbs`.

Both sides count the multiplicity of the pole, read off as an unsigned
natural number. The signed convention on the meromorphic side (negative
integer at a pole) is absorbed by `.natAbs`. -/
theorem mmeromorphicOrderAt_eq_ramificationIndex_at_pole
    (f : JacobianChallenge.MeromorphicNonzero X) (x : X)
    (hx_pole : f.toRiemannSphere x = (∞ : RiemannSphere)) :
    (manifoldRamificationIndex f.toRiemannSphere x : ℕ) =
      (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀.natAbs := by
  -- Set notation.
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀
  have hx_neg : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0 :=
    neg_order_of_toRiemannSphere_eq_infty f hx_pole
  -- Codomain chart equals `chartS`.
  have h_chartCod : chartAt ℂ (f.toRiemannSphere x) = RiemannSphere.chartS :=
    chartAt_codomain_eq_chartS_at_pole f hx_pole
  -- Introduce the chart-pulled-back representative `F`.
  set F : ℂ → ℂ :=
    (chartAt ℂ (f.toRiemannSphere x)) ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm
    with hF
  -- `F z₀ = chartS ∞ = 0`.
  have hFz₀ : F z₀ = 0 := by
    show (chartAt ℂ (f.toRiemannSphere x))
        (f.toRiemannSphere ((chartAt ℂ x).symm z₀)) = 0
    have h_inv : (chartAt ℂ x).symm z₀ = x :=
      (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
    rw [h_inv, h_chartCod, hx_pole]
    exact RiemannSphere.chartS_apply_infty
  -- Identify `F` with the `chartS`-side composition.
  have h_eqFun :
      F = (RiemannSphere.chartS ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm) := by
    show (chartAt ℂ (f.toRiemannSphere x)) ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm
        = RiemannSphere.chartS ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm
    rw [h_chartCod]
  -- Analytic at `z₀`.
  have h_anF : AnalyticAt ℂ F z₀ := by
    rw [h_eqFun]
    exact analyticAt_chartS_chartPullback_at_pole f hx_pole
  -- LHS unfold.
  rw [manifoldRamificationIndex_eq f.toRiemannSphere x]
  -- Now goal:
  --   (analyticOrderAt (fun z => F z - F z₀) z₀).toNat
  -- = (mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x).untop₀.natAbs
  -- Rewrite the analytic-order argument: `F z - F z₀ = F z - 0 = F z`.
  have h_shift : (fun z => F z - F z₀) =ᶠ[𝓝 z₀] F := by
    rw [hFz₀]
    refine Filter.Eventually.of_forall ?_
    intro z
    show F z - 0 = F z
    rw [sub_zero]
  rw [analyticOrderAt_congr h_shift]
  -- Now: `(analyticOrderAt F z₀).toNat = ...`.
  -- Bridge: `meromorphicOrderAt F z₀ = (analyticOrderAt F z₀).map (↑ : ℕ → ℤ)`.
  have h_mero_eq :
      meromorphicOrderAt F z₀ = (analyticOrderAt F z₀).map (↑· : ℕ → ℤ) :=
    h_anF.meromorphicOrderAt_eq
  -- Bridge: `meromorphicOrderAt F z₀ = -mmeromorphicOrderAt I f.toFun x`.
  -- Step (a): `meromorphicOrderAt F z₀
  --             = meromorphicOrderAt (f.toFun ∘ chart.symm)⁻¹ z₀`
  -- via the punctured EvEq + `meromorphicOrderAt_congr`.
  have h_local :
      F =ᶠ[𝓝[≠] z₀] (fun z => (f.toFun ((chartAt ℂ x).symm z))⁻¹) := by
    rw [h_eqFun]
    exact f.toRiemannSphere_chartS_localForm_punctured hx_neg
  -- Cast the RHS to the pointwise inverse of the chart pullback.
  have h_local' :
      F =ᶠ[𝓝[≠] z₀] (f.toFun ∘ (chartAt ℂ x).symm)⁻¹ := h_local
  have h_meroF_inv :
      meromorphicOrderAt F z₀
        = meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm)⁻¹ z₀ :=
    meromorphicOrderAt_congr h_local'
  -- Step (b): `meromorphicOrderAt (f ∘ chart.symm)⁻¹ z₀ = -mmeromorphicOrderAt`.
  have h_inv_neg :
      meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm)⁻¹ z₀
        = -mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x := by
    show meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm)⁻¹
            ((chartAt ℂ x) x)
        = -meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm)
            ((chartAt ℂ x) x)
    exact meromorphicOrderAt_inv
  -- Combine.
  have h_combined :
      (analyticOrderAt F z₀).map (↑· : ℕ → ℤ)
        = -mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x := by
    rw [← h_mero_eq, h_meroF_inv, h_inv_neg]
  -- `mmeromorphicOrderAt _ _ x` is a finite negative integer at a pole.
  have h_mmero_finite : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x ≠ ⊤ := by
    intro h_eq_top
    rw [h_eq_top] at hx_neg
    exact absurd hx_neg (not_lt.mpr le_top)
  -- Extract `mmeromorphicOrderAt = ((k : ℤ) : WithTop ℤ)` for some `k : ℤ` with `k < 0`.
  obtain ⟨k, hk⟩ : ∃ k : ℤ, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x =
      ((k : ℤ) : WithTop ℤ) := by
    cases h : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x with
    | top => exact absurd h h_mmero_finite
    | coe m => exact ⟨m, rfl⟩
  have hk_neg : k < 0 := by
    have hx' := hx_neg
    rw [hk] at hx'
    exact_mod_cast hx'
  -- Set `n := -k` (a positive natural).
  set n : ℕ := k.natAbs with hn_def
  have hk_eq : k = -(n : ℤ) := by
    have h_abs : (n : ℤ) = -k := by
      rw [hn_def]
      have hk_nonpos : k ≤ 0 := le_of_lt hk_neg
      omega
    linarith
  -- Set α and show `α = (n : ℕ∞)` via `h_combined`.
  set α : ℕ∞ := analyticOrderAt F z₀ with hα
  have h_combined' :
      α.map (↑· : ℕ → ℤ) = ((n : ℤ) : WithTop ℤ) := by
    have h_neg_mmero :
        -mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x = ((n : ℤ) : WithTop ℤ) := by
      rw [hk, hk_eq]
      show -(((-(n : ℤ)) : ℤ) : WithTop ℤ) = ((n : ℤ) : WithTop ℤ)
      push_cast
      rw [neg_neg]
    rw [h_combined, h_neg_mmero]
  -- α has finite value n.
  have h_α_eq : α = (n : ℕ∞) := by
    cases h : α with
    | top =>
      rw [h] at h_combined'
      -- LHS: `(⊤ : ℕ∞).map (↑·) = ⊤`. RHS: `((n : ℤ) : WithTop ℤ)` finite.
      simp at h_combined'
    | coe m =>
      rw [h] at h_combined'
      -- LHS: `((m : ℕ∞)).map (↑·) = ((m : ℤ) : WithTop ℤ)`.
      -- So `((m : ℤ) : WithTop ℤ) = ((n : ℤ) : WithTop ℤ)`, hence `m = n`.
      have : ((m : ℤ) : WithTop ℤ) = ((n : ℤ) : WithTop ℤ) := by
        rw [← h_combined']; rfl
      have h_mn : (m : ℤ) = (n : ℤ) := by exact_mod_cast this
      have : m = n := by exact_mod_cast h_mn
      rw [this]
  rw [h_α_eq, hk]
  -- Goal: `((n : ℕ∞)).toNat = (((k : ℤ) : WithTop ℤ)).untop₀.natAbs`.
  -- LHS = n; RHS = k.natAbs = n (by hn_def).
  simp [hn_def]

end Manifold

end JacobianChallenge
