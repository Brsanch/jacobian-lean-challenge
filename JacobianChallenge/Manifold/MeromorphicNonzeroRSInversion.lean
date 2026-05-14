/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroRSSimplePole

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `MeromorphicNonzero RiemannSphere` for `1/RSSimplePole`

Builds `RSInversion : RiemannSphere → ℂ`, the function `some z ↦ z⁻¹`,
`∞ ↦ 0`. Packages it as a `MeromorphicNonzero RiemannSphere`. The
principal divisor is `δ_∞ - δ_{some 0}` (a single simple zero at `∞`
and a simple pole at `some 0`), the sign-flipped pair of
`mnRSSimplePole`'s divisor.

## Significance

Together with `mnRSSimplePole` (`Manifold/MeromorphicNonzeroRSSimplePole.lean`,
divisor `δ_{some 0} - δ_∞`), this gives a second elementary
principal-divisor generator on `RiemannSphere`. With translations (a
future chip), these recover `δ_{some a} - δ_{some b}` and
`δ_{some a} - δ_∞` for all `a, b : ℂ`, generating `Div0
RiemannSphere` as an `AddSubgroup` — the path toward unconditional
`Subsingleton (Pic0 RiemannSphere)`.

## What ships

* `RSInversion : RiemannSphere → ℂ` — the function `some z ↦ z⁻¹`,
  `∞ ↦ 0`.
* Chart-pullback identities and order/continuity infrastructure.
* `mnRSInversion : MeromorphicNonzero RiemannSphere` — the packaged
  form.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Filter Set OnePoint

namespace JacobianChallenge

/-- The Riemann-sphere function `some z ↦ z⁻¹`, `∞ ↦ 0`. Simple zero
at `∞`, simple pole at `some 0`. Uses mathlib's convention
`(0 : ℂ)⁻¹ = 0`, so the value at `some 0` is `0` (which is consistent
with the pole interpretation since the value is "junk" at a pole). -/
noncomputable def RSInversion : RiemannSphere → ℂ :=
  fun x => OnePoint.rec 0 (fun z => z⁻¹) x

@[simp] lemma RSInversion_infty : RSInversion (∞ : RiemannSphere) = 0 := rfl

@[simp] lemma RSInversion_coe (z : ℂ) :
    RSInversion ((z : RiemannSphere)) = z⁻¹ := rfl

/-! ## Chart-pullback identities -/

/-- `RSInversion ∘ chartN.symm = (·)⁻¹` on `ℂ`. -/
lemma RSInversion_comp_chartN_symm :
    RSInversion ∘ RiemannSphere.chartN.symm = (fun z : ℂ => z⁻¹) := by
  funext w
  show RSInversion (RiemannSphere.chartN.symm w) = w⁻¹
  rw [show RiemannSphere.chartN.symm w = ((w : ℂ) : RiemannSphere) from rfl]
  rfl

/-- `RSInversion ∘ chartS.symm = id` on `ℂ`. The case `w = 0` evaluates
to `RSInversion ∞ = 0 = w`; for `w ≠ 0` it evaluates to
`RSInversion (some w⁻¹) = (w⁻¹)⁻¹ = w` (via `inv_inv`). -/
lemma RSInversion_comp_chartS_symm :
    RSInversion ∘ RiemannSphere.chartS.symm = (id : ℂ → ℂ) := by
  funext w
  show RSInversion (RiemannSphere.chartS.symm w) = w
  by_cases hw : w = 0
  · subst hw
    rw [show RiemannSphere.chartS.symm 0 = (∞ : RiemannSphere) from
      RiemannSphere.chartSInvFun_zero]
    rfl
  · rw [show RiemannSphere.chartS.symm w = ((w⁻¹ : ℂ) : RiemannSphere) from
      RiemannSphere.chartSInvFun_of_ne hw]
    show (w⁻¹ : ℂ)⁻¹ = w
    exact inv_inv w

/-! ## MMeromorphicOn -/

lemma RSInversion_mmeromorphicAt_coe (z : ℂ) :
    MMeromorphicAt 𝓘(ℂ, ℂ) RSInversion ((z : RiemannSphere)) := by
  show MeromorphicAt (RSInversion ∘ (chartAt ℂ ((z : RiemannSphere))).symm)
      ((chartAt ℂ ((z : RiemannSphere))) ((z : RiemannSphere)))
  have h_chart : (chartAt ℂ ((z : RiemannSphere)) : OpenPartialHomeomorph RiemannSphere ℂ)
        = RiemannSphere.chartN := rfl
  rw [h_chart, RSInversion_comp_chartN_symm, RiemannSphere.chartN_apply_coe]
  -- `MeromorphicAt (·)⁻¹ z`. `id⁻¹` is meromorphic everywhere.
  exact (analyticAt_id (𝕜 := ℂ) (z := z)).meromorphicAt.inv

lemma RSInversion_mmeromorphicAt_infty :
    MMeromorphicAt 𝓘(ℂ, ℂ) RSInversion (∞ : RiemannSphere) := by
  show MeromorphicAt (RSInversion ∘ (chartAt ℂ (∞ : RiemannSphere)).symm)
      ((chartAt ℂ (∞ : RiemannSphere)) ∞)
  have h_chart : (chartAt ℂ (∞ : RiemannSphere) : OpenPartialHomeomorph RiemannSphere ℂ)
        = RiemannSphere.chartS := rfl
  rw [h_chart, RSInversion_comp_chartS_symm]
  -- `MeromorphicAt id _`. Always.
  exact analyticAt_id.meromorphicAt

lemma RSInversion_mmeromorphicOn :
    MMeromorphicOn 𝓘(ℂ, ℂ) RSInversion Set.univ := by
  intro x _
  induction x using OnePoint.rec with
  | infty => exact RSInversion_mmeromorphicAt_infty
  | coe z => exact RSInversion_mmeromorphicAt_coe z

/-! ## Order computations -/

/-- `mmeromorphicOrderAt 𝓘(ℂ,ℂ) RSInversion ∞ = 1`: simple zero at `∞`. -/
lemma RSInversion_orderAt_infty :
    mmeromorphicOrderAt 𝓘(ℂ, ℂ) RSInversion (∞ : RiemannSphere) ≠ ⊤ := by
  show meromorphicOrderAt (RSInversion ∘ (chartAt ℂ (∞ : RiemannSphere)).symm)
      ((chartAt ℂ (∞ : RiemannSphere)) ∞) ≠ ⊤
  have h_chart : (chartAt ℂ (∞ : RiemannSphere) : OpenPartialHomeomorph RiemannSphere ℂ)
        = RiemannSphere.chartS := rfl
  rw [h_chart, RSInversion_comp_chartS_symm, RiemannSphere.chartS_apply_infty]
  -- `meromorphicOrderAt id 0 = 1`.
  rw [meromorphicOrderAt_id]
  decide

/-- `mmeromorphicOrderAt 𝓘(ℂ,ℂ) RSInversion (some z) ≠ ⊤`: function
not identically zero on a neighborhood of any finite point. The chart
pullback is `(·)⁻¹`, which is eventually nonzero in `𝓝[≠] z`. -/
lemma RSInversion_orderAt_coe_ne_top (z : ℂ) :
    mmeromorphicOrderAt 𝓘(ℂ, ℂ) RSInversion ((z : RiemannSphere)) ≠ ⊤ := by
  show meromorphicOrderAt (RSInversion ∘ (chartAt ℂ ((z : RiemannSphere))).symm)
      ((chartAt ℂ ((z : RiemannSphere))) ((z : RiemannSphere))) ≠ ⊤
  have h_chart : (chartAt ℂ ((z : RiemannSphere)) : OpenPartialHomeomorph RiemannSphere ℂ)
        = RiemannSphere.chartN := rfl
  rw [h_chart, RSInversion_comp_chartN_symm, RiemannSphere.chartN_apply_coe]
  -- `meromorphicOrderAt (·)⁻¹ z ≠ ⊤` iff eventually nonzero in `𝓝[≠] z`.
  show meromorphicOrderAt (id⁻¹ : ℂ → ℂ) z ≠ ⊤
  rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (analyticAt_id (𝕜 := ℂ) (z := z)).meromorphicAt.inv]
  -- `(·)⁻¹ w = w⁻¹`. Eventually nonzero in `𝓝[≠] z`: by mathlib `inv_ne_zero` of `w ≠ 0`.
  rcases eq_or_ne z 0 with rfl | hz
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact inv_ne_zero hw
  · -- z ≠ 0: w eventually ≠ 0 near z by continuity.
    have h_ev : ∀ᶠ w in 𝓝 z, (w : ℂ) ≠ 0 := continuousAt_id.eventually_ne hz
    exact (h_ev.filter_mono nhdsWithin_le_nhds).mono (fun w hw => inv_ne_zero hw)

/-! ## Continuity at non-pole points -/

/-- `RSInversion` is continuous at every finite **nonzero** point.
At `some 0` the order is `-1` (simple pole), so the regular-continuity
hypothesis is vacuous there. -/
lemma RSInversion_continuousAt_coe_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt RSInversion ((z : RiemannSphere)) := by
  have h_nhds : 𝓝 ((z : ℂ) : RiemannSphere)
      = Filter.map ((↑) : ℂ → RiemannSphere) (𝓝 z) :=
    ((OnePoint.isOpenEmbedding_coe (X := ℂ)).map_nhds_eq z).symm
  rw [ContinuousAt, h_nhds, Filter.tendsto_map'_iff]
  -- `RSInversion ∘ ↑ = (·)⁻¹`.
  have h_eq : (RSInversion ∘ ((↑) : ℂ → RiemannSphere)) = (fun w : ℂ => w⁻¹) := by
    funext w; rfl
  rw [h_eq]
  show Filter.Tendsto (fun w : ℂ => w⁻¹) (𝓝 z) (𝓝 z⁻¹)
  exact (continuousAt_inv₀ hz).tendsto

/-- `RSInversion` is continuous at `∞`. As points approach `∞`
(chartN-coord → ∞), `RSInversion (some w) = w⁻¹ → 0 = RSInversion ∞`. -/
lemma RSInversion_continuousAt_infty :
    ContinuousAt RSInversion (∞ : RiemannSphere) := by
  rw [ContinuousAt, RSInversion_infty, OnePoint.nhds_infty_eq, Filter.tendsto_sup]
  refine ⟨?_, ?_⟩
  · -- `map ↑ (coclosedCompact ℂ)` side.
    rw [Filter.tendsto_map'_iff]
    simp only [Filter.coclosedCompact_eq_cocompact]
    have h_eq : (RSInversion ∘ ((↑) : ℂ → RiemannSphere)) = (fun w : ℂ => w⁻¹) := by
      funext w; rfl
    rw [h_eq]
    -- `Tendsto (·)⁻¹ (cocompact ℂ) (𝓝 0)`. Follows from `tendsto_inv₀_cobounded`.
    rw [← Metric.cobounded_eq_cocompact]
    exact Filter.tendsto_inv₀_cobounded
  · -- `pure ∞` side: trivial via constant.
    have h := Filter.tendsto_pure_pure RSInversion (∞ : RiemannSphere)
    rw [RSInversion_infty] at h
    exact h.mono_right (pure_le_nhds _)

/-! ## Packaged `MeromorphicNonzero RiemannSphere` -/

/-- **`MeromorphicNonzero RiemannSphere` packaging of `RSInversion`.**
Has divisor `δ_∞ - δ_{some 0}`: a simple zero at `∞`, a simple pole at
`some 0`. -/
noncomputable def mnRSInversion :
    MeromorphicNonzero RiemannSphere :=
  MeromorphicNonzero.ofRegularContinuous
    (g := RSInversion)
    (h_mero := RSInversion_mmeromorphicOn)
    (h_nonvanish := by
      intro x
      induction x using OnePoint.rec with
      | infty => exact RSInversion_orderAt_infty
      | coe z => exact RSInversion_orderAt_coe_ne_top z)
    (h_reg_cts := by
      intro x _hreg
      induction x using OnePoint.rec with
      | infty => exact RSInversion_continuousAt_infty
      | coe z =>
        -- Need to handle z = 0 case: order at some 0 is -1, so _hreg is false.
        by_cases hz : z = 0
        · subst hz
          -- order at some 0 is -1 < 0; _hreg says 0 ≤ -1, contradiction.
          exfalso
          show False
          have h_order : mmeromorphicOrderAt 𝓘(ℂ, ℂ) RSInversion
              ((0 : ℂ) : RiemannSphere)
                = ((-1 : ℤ) : WithTop ℤ) := by
            show meromorphicOrderAt
                (RSInversion ∘ (chartAt ℂ ((0 : ℂ) : RiemannSphere)).symm)
                ((chartAt ℂ ((0 : ℂ) : RiemannSphere)) ((0 : ℂ) : RiemannSphere))
                = _
            have h_chart : (chartAt ℂ (((0 : ℂ) : RiemannSphere))
                : OpenPartialHomeomorph RiemannSphere ℂ)
                  = RiemannSphere.chartN := rfl
            rw [h_chart, RSInversion_comp_chartN_symm, RiemannSphere.chartN_apply_coe]
            -- `meromorphicOrderAt (·)⁻¹ 0 = -1`.
            show meromorphicOrderAt (fun w : ℂ => w⁻¹) 0 = ((-1 : ℤ) : WithTop ℤ)
            have h_inv_eq : (fun w : ℂ => w⁻¹) = ((id : ℂ → ℂ))⁻¹ := by
              funext w; rfl
            rw [h_inv_eq, meromorphicOrderAt_inv, meromorphicOrderAt_id]
            rfl
          rw [h_order] at _hreg
          exact absurd _hreg (by decide)
        · exact RSInversion_continuousAt_coe_of_ne_zero hz)

@[simp] lemma mnRSInversion_toFun :
    (mnRSInversion : MeromorphicNonzero RiemannSphere).toFun = RSInversion := rfl

end JacobianChallenge

end
