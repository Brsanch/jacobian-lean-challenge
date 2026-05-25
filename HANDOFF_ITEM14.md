# Item 14 — handoff

Last rewrite: 2026-05-25 (post Chip 2c-Final + étale-leg merge + Phase B Cauchy-Pompeiu audit + Pompeiu Chips 1a, 1b, 1c, 2a, 2b, 2c-prep, 2c-main, 2d, 3a, 3b, 3c-A, 3c-B, 3c-C₁, 3c-C₂, **3c-D** landed).

Prior versions of this file accumulated layered banners across sessions. This rewrite consolidates the current state. `git log HANDOFF_ITEM14.md` preserves the history.

---

## 🟢 ACTIVE ARC: Pompeiu kernel (committed 2026-05-24)

Last rewrite: 2026-05-25 (post Chip 3c-D).

After exhaustive audit (2026-05-24) confirmed no route exists at this mathlib pin to close Item 14 without formalizing classical content, the **Pompeiu kernel + Riemann existence at genus 0** route was selected as the path with lowest expected surprise. Estimated **20–45 focused sessions / 5–10 months** at typical chip cadence (Chips 1a–2d done; Chip 3 is the next and heaviest).

### Where we are right now

* **Chip 1a — DONE** ([`Analysis/PompeiuKernel.lean`](JacobianChallenge/Analysis/PompeiuKernel.lean), commit `bcf6951`).
  - `pompeiuIntegrand`, `pompeiuKernel` definitions.
  - Measurability lemmas for the integrand.
  - `integrableOn_inv_norm_sub_iff_origin` — translation reduction.
  - `integrableOn_inv_norm_sub_of_not_mem_compact` — trivial case.
  - Sorry-free, axiom-free. Library entry added.
* **Chip 1b — DONE** ([`Analysis/InvNormIntegrability.lean`](JacobianChallenge/Analysis/InvNormIntegrability.lean), 163 LOC).
  - `integrableOn_inv_norm_closedBall (R : ℝ) : IntegrableOn (fun ζ : ℂ => ‖ζ‖⁻¹) (closedBall (0 : ℂ) R) volume`.
  - Auxiliary `lintegral_inv_enorm_closedBall_le` gives the quantitative
    bound `∫⁻ ζ in closedBall 0 R, ‖(‖ζ‖⁻¹ : ℝ)‖ₑ ∂volume ≤ (max R 0) * 2π`,
    proved by changing to polar coordinates via
    `Complex.lintegral_comp_polarCoord_symm`; the Jacobian factor cancels
    the integrand factor on `polarCoord.target` leaving an integrand
    bounded by `1`.
  - Sorry-free, axiom-free (`propext`, `Classical.choice`, `Quot.sound`
    only). Library entry added.
* **Chip 1c — DONE** ([`Analysis/PompeiuIntegrandIntegrability.lean`](JacobianChallenge/Analysis/PompeiuIntegrandIntegrability.lean), 140 LOC).
  - `integrable_pompeiuIntegrand_of_continuous_hasCompactSupport
      {α : ℂ → ℂ} (h_cont : Continuous α) (h_supp : HasCompactSupport α) (z : ℂ) :
      Integrable (pompeiuIntegrand α z) volume`.
  - Combines `Continuous.bounded_above_of_compact_support` (uniform
    bound `M` on `‖α‖`), `HasCompactSupport.isBounded.subset_closedBall`
    (`tsupport α ⊆ closedBall 0 R`), the geometric inclusion
    `closedBall 0 R ⊆ closedBall z (R + ‖z‖)`, Chip 1a's
    `integrableOn_inv_norm_sub_iff_origin`, and Chip 1b's
    `integrableOn_inv_norm_closedBall`. Pointwise domination is via the
    enorm identity `‖w⁻¹‖ₑ = ‖(‖w‖⁻¹ : ℝ)‖ₑ` for `w : ℂ`.
  - Sorry-free, axiom-free. Library entry added.
* **Chip 2a — DONE** ([`Analysis/PompeiuKernelTranslation.lean`](JacobianChallenge/Analysis/PompeiuKernelTranslation.lean), 114 LOC).
  - `pompeiuKernel_eq_translated_integrand (α : ℂ → ℂ) (z : ℂ) :
      pompeiuKernel α z = -((Real.pi : ℂ)⁻¹) * ∫ η, α (η + z) * η⁻¹`.
  - Companion `integrable_translated_pompeiuIntegrand_of_continuous_hasCompactSupport`
    transports Chip 1c's integrability to the translated integrand
    via `measurePreserving_add_right`.
  - Pushes the `z`-dependence out of the singular factor `(ζ - z)⁻¹`
    and into the regular factor `α (η + z)`. With the singularity now
    pinned at `η = 0` (independent of `z`), differentiation under the
    integral (Chips 2b/2c) reduces to a routine dominated-convergence
    argument: the dominating function is integrable once (Chip 1c)
    rather than once per `z`.
  - Sorry-free, axiom-free. Library entry added.
* **Chip 2c-prep — DONE** ([`Analysis/PompeiuKernelDirectionalIntegrand.lean`](JacobianChallenge/Analysis/PompeiuKernelDirectionalIntegrand.lean), 135 LOC).
  - `αDeriv α v ζ := fderiv ℝ α ζ v` — directional derivative as a
    `ℂ → ℂ` function.
  - `αDeriv_hasCompactSupport` (from `HasCompactSupport.fderiv_apply`)
    and `αDeriv_continuous` (from `ContDiff.continuous_fderiv` +
    `ContinuousLinearMap.apply` continuity) — input shape for Chips
    1c and 2b.
  - `integrable_pompeiuIntegrand_αDeriv` and
    `continuous_pompeiuKernel_αDeriv` — Chips 1c and 2b applied to
    `αDeriv α v`, giving integrability and continuity of the
    directional-derivative Pompeiu integrand and kernel.
  - `exists_fderiv_norm_bound` — uniform bound `M'` with
    `‖fderiv ℝ α ζ‖ ≤ M'` for all `ζ`, via
    `Continuous.bounded_above_of_compact_support` on `fderiv ℝ α`
    (which has compact support and is continuous for `α ∈ C^1`).
  - `norm_αDeriv_le` — pointwise `‖αDeriv α v ζ‖ ≤ M' · ‖v‖` from the
    uniform bound and `ContinuousLinearMap.le_opNorm`.
  - Sorry-free, axiom-free. Library entry added.
* **Chip 2b — DONE** ([`Analysis/PompeiuKernelContinuity.lean`](JacobianChallenge/Analysis/PompeiuKernelContinuity.lean), 157 LOC).
  - `continuous_pompeiuKernel_of_continuous_hasCompactSupport
      {α : ℂ → ℂ} (h_cont : Continuous α) (h_supp : HasCompactSupport α) :
      Continuous (pompeiuKernel α)`.
  - For each `z₀`, the dominating function `K.indicator (fun η => M · ‖η‖⁻¹)`
    with `K := closedBall 0 (R + ‖z₀‖ + 1)` works uniformly for
    `z ∈ closedBall z₀ 1`: outside `K`, the triangle inequality
    `‖η + z‖ ≥ ‖η‖ - ‖z‖ > R` forces `α (η + z) = 0`; inside `K`,
    the bound is `M · ‖η‖⁻¹`. Integrability via Chip 1b's
    `integrableOn_inv_norm_closedBall` + `IntegrableOn.const_mul`
    + `IntegrableOn.integrable_indicator`. Apply
    `MeasureTheory.continuousAt_of_dominated` for each `z₀` and lift
    via `continuous_iff_continuousAt`.
  - Sorry-free, axiom-free. Library entry added.

* **Chip 2c-main — DONE** ([`Analysis/PompeiuKernelDerivative.lean`](JacobianChallenge/Analysis/PompeiuKernelDerivative.lean), 292 LOC).
* **Chip 2d — DONE** ([`Analysis/PompeiuKernelSmoothness.lean`](JacobianChallenge/Analysis/PompeiuKernelSmoothness.lean), 515 LOC, commit pending).
  - `pompeiuFDerivIntegrand α z η := (η⁻¹ : ℂ) • fderiv ℝ α (η + z) : ℂ →L[ℝ] ℂ` — CLM-valued integrand for the complex-parameter derivative.
  - `hasFDerivAt_translated_integral` — `HasFDerivAt` for `z ↦ ∫ η, α(η + z) * η⁻¹` at any `z₀`, derivative `∫ η, pompeiuFDerivIntegrand α z₀ η`. Proven by `MeasureTheory.hasFDerivAt_integral_of_dominated_of_fderiv_le` with `K := closedBall 0 (R + ‖z₀‖ + 1)` and uniform-in-`z ∈ ball z₀ 1` dominating function `K.indicator (M' · ‖η‖⁻¹)`.
  - `integrable_pompeiuFDerivIntegrand` — integrability of the CLM-valued integrand (needed for `ContinuousLinearMap.integral_apply`).
  - `hasFDerivAt_pompeiuKernel` — scaled by `-(π⁻¹)` via `HasFDerivAt.const_mul`, with the function side rewritten using Chip 2a's translated form.
  - `fderiv_pompeiuKernel_apply` — **the inductive engine**: `fderiv ℝ (pompeiuKernel α) z₀ v = pompeiuKernel (αDeriv α v) z₀`. Proven by `ContinuousLinearMap.integral_apply` + commutativity + Chip 2a applied to `αDeriv α v`.
  - `contDiff_αDeriv` — `α ∈ C^(n+1)` ⇒ `αDeriv α v ∈ C^n` (via `contDiff_succ_iff_fderiv` + `ContinuousLinearMap.apply` smoothness).
  - `contDiff_pompeiuKernel_of_nat` — **the induction**: `∀ n : ℕ`, `ContDiff ℝ n α → HasCompactSupport α → ContDiff ℝ n (pompeiuKernel α)`. Base case `n = 0` via Chip 2b's continuity. Successor via `contDiff_succ_iff_fderiv_apply` (uses finite-dimensionality of `ℂ` over `ℝ`): differentiability from `hasFDerivAt_pompeiuKernel`, ω case vacuous (`(k : WithTop ℕ∞) ≠ ⊤`), and for each `v`, `(fun z => fderiv ℝ (pompeiuKernel α) z v) = pompeiuKernel (αDeriv α v)` is `C^n` by IH on `αDeriv α v`.
  - `contDiff_pompeiuKernel_infty` — **main theorem**: `ContDiff ℝ ∞ α → HasCompactSupport α → ContDiff ℝ ∞ (pompeiuKernel α)`. Via `contDiff_infty : ContDiff 𝕜 ∞ f ↔ ∀ n : ℕ, ContDiff 𝕜 n f`.
  - Sorry-free, axiom-free (`propext`, `Classical.choice`, `Quot.sound` only). Library entry added.
  - `hasDerivAt_pompeiuKernel_real_direction
      {α : ℂ → ℂ} (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
      (v z₀ : ℂ) :
      HasDerivAt (fun t : ℝ => pompeiuKernel α (z₀ + (t : ℝ) • v))
        (pompeiuKernel (αDeriv α v) z₀) 0`.
  - Applies `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
    on Chip 2a's translated parametric integral. Dominating function
    `K.indicator (fun η => M' · ‖v‖ · ‖η‖⁻¹)` with
    `K := closedBall 0 (R + ‖z₀‖ + ‖v‖ + 1)`. Outside `K`, the path
    `η + z₀ + t • v` stays outside `tsupport α` for all
    `t ∈ Ioo (-1) 1`, so `fderiv ℝ α (η + z₀ + t • v) = 0`
    (`fderiv_of_notMem_tsupport`). Identifies both function and
    derivative with `pompeiuKernel` via Chip 2a + `HasDerivAt.const_mul (-π⁻¹)`.
  - Sorry-free, axiom-free. Library entry added.

* **Chip 3c-D — DONE** ([`Analysis/PompeiuKernelStokes.lean`](JacobianChallenge/Analysis/PompeiuKernelStokes.lean), ~370 LOC).
  - **Main theorem (Stokes-for-`∂̄`)**:
    `iteratedIntegral_partialZBar_eq_zero
        {f : ℂ → ℂ} (h_smooth : ContDiff ℝ 1 f) {L : ℝ} (hL_pos : 0 < L)
        (hL_supp : tsupport f ⊆ Metric.ball 0 L) :
        ∫ x in -L..L, ∫ y in -L..L, partialZBar f (x + y * I) = 0`.
    For any compactly-supported `C¹` function `f`, the iterated `∂̄`
    integral over a large enough square rectangle vanishes.
  - **Application (balance equation)**:
    `balance_iteratedIntegral_eq_zero
        {α : ℂ → ℂ} (h_α : ContDiff ℝ 1 α) (z : ℂ) {ε : ℝ} (hε : 0 < ε)
        {L : ℝ} (hL_pos : 0 < L) (hL_supp : tsupport α ⊆ Metric.ball 0 L) :
        ∫ x in -L..L, ∫ y in -L..L,
          partialZBar α (x+y*I) * regularizedInvSub z hε (x+y*I)
            + α (x+y*I) * partialZBar (regularizedInvSub z hε) (x+y*I) = 0`.
    The iterated-integral form of integration-by-parts in the
    Cauchy-Pompeiu argument.
  - Proof of Stokes-for-`∂̄`:
    1. Apply mathlib's
       `Complex.integral_boundary_rect_of_differentiableOn_real` on the
       square `[-L, L]²` (corners `z₀ := -L - L·I`, `w₀ := L + L·I`).
    2. All four boundary line integrals vanish:
       `intervalIntegral_zero_on_uIcc_{horiz,vert}` + helpers
       `norm_horiz_ge`, `norm_vert_ge` (every boundary point has
       Euclidean norm `≥ L`, hence outside `ball 0 L`, hence outside
       `tsupport f`, hence `f = 0` there).
    3. Algebraic identity `partialZBar_eq_integrand_div_two_I`:
       `I • fderiv ℝ f x 1 - fderiv ℝ f x I = 2 * I * partialZBar f x`
       (direct from the Wirtinger definition).
    4. Pull `2 * I` out of both interval integrals (via
       `intervalIntegral.integral_const_mul`); divide by the nonzero
       scalar.
  - Application: combine Stokes with Leibniz expansion
    `partialZBar_alpha_mul_regInvSub` (using existing
    `partialZBar_mul` from `Manifold/PartialZBar.lean` + Chip 3c-C₂'s
    `regularizedInvSub_contDiff`) and
    `tsupport_alpha_mul_regInvSub_subset` (product support is in
    factor support).
  - Sorry-free, axiom-free (`propext`, `Classical.choice`, `Quot.sound`
    only). Library entry added.

* **Chip 3c-C₂ — DONE** ([`Analysis/PompeiuKernelRegularizedInv.lean`](JacobianChallenge/Analysis/PompeiuKernelRegularizedInv.lean), ~140 LOC).
  - `regularizedInvSub z hε : ℂ → ℂ` —
    `regularizedInvSub z hε η := (η - z)⁻¹ * ((pompeiuCutoff z hε η : ℝ) : ℂ)`.
  - `regularizedInvSub_contDiff
      (z : ℂ) {ε : ℝ} (hε : 0 < ε) {n : ℕ∞} :
      ContDiff ℝ n (regularizedInvSub z hε)`.
  - Proof: case-split on `ζ = z` vs `ζ ≠ z` via
    `contDiff_iff_contDiffAt`:
    * `ζ ≠ z` — `regularizedInvSub_contDiffAt_of_ne`. Product of
      `(·-z)⁻¹` (smooth at `ζ` via `contDiffAt_inv` over `ℂ` composed
      with `sub_const` and `restrict_scalars ℝ` under the same
      `set_option backward.isDefEq.respectTransparency false in`
      diamond workaround as 3c-A/3c-B) and `((pompeiuCutoff · : ℝ) : ℂ)`
      (smooth via `Complex.ofRealCLM.contDiff` ∘ `pompeiuCutoff_contDiff`).
    * `ζ = z` — `regularizedInvSub_contDiffAt_of_eq`. Use
      `regularizedInvSub =ᶠ[𝓝 z] 0` (from Chip 3c-C₁'s
      `pompeiuCutoff_eventuallyEq_zero` carried through via
      `filter_upwards`), so `ContDiffAt.congr_of_eventuallyEq` with
      `contDiffAt_const` finishes.
  - Supporting helpers: `contDiff_ofReal`, `contDiffAt_inv_sub_const`,
    `regularizedInvSub_eventuallyEq_zero`.
  - Sorry-free, axiom-free (`propext`, `Classical.choice`, `Quot.sound`
    only). Library entry added.

* **Chip 3c-C₁ — DONE** ([`Analysis/PompeiuKernelCutoff.lean`](JacobianChallenge/Analysis/PompeiuKernelCutoff.lean), ~160 LOC).
  - `pompeiuCutoff (z : ℂ) {ε : ℝ} (hε : 0 < ε) : ℂ → ℝ` — the cutoff
    function `χ_ε(η) := 1 - bump(η)` where `bump : ContDiffBump z` has
    `rIn := ε/2`, `rOut := ε`. The underlying bump is exposed as
    `pompeiuBump z hε`.
  - Key properties (all sorry- and axiom-free):
    * `pompeiuCutoff_eq_zero_of_mem_closedBall_half` — `χ_ε(ζ) = 0` on
      `closedBall z (ε/2)`.
    * `pompeiuCutoff_eq_one_of_not_mem_ball` — `χ_ε(ζ) = 1` outside
      `ball z ε`.
    * `pompeiuCutoff_nonneg`, `pompeiuCutoff_le_one` — `0 ≤ χ_ε ≤ 1`.
    * `pompeiuCutoff_contDiff` — `ContDiff ℝ n χ_ε` for all `n`.
    * `pompeiuCutoff_eventuallyEq_zero` — `χ_ε =ᶠ[𝓝 z] 0`. This is
      the key fact that makes the regularized integrand `α · (·-z)⁻¹ · χ_ε`
      smooth even at `η = z`.
    * `one_sub_pompeiuCutoff_eq_bump`, `tsupport_one_sub_pompeiuCutoff_subset` —
      the "interior" `(1 - χ_ε)` equals the bump, hence is compactly
      supported in `closedBall z ε`.
  - Uses mathlib's `ContDiffBump` (`Analysis/Calculus/BumpFunction/Basic.lean`)
    with `HasContDiffBump ℂ` via the inner-product-space instance
    (`Analysis/Calculus/BumpFunction/InnerProduct.lean:57`).
  - Library entry added.

* **Chip 3c-B — DONE** ([`Analysis/PompeiuKernelMulInvFDeriv.lean`](JacobianChallenge/Analysis/PompeiuKernelMulInvFDeriv.lean), ~130 LOC).
  - `hasFDerivAt_mul_inv_sub
      {α : ℂ → ℂ} {ζ : ℂ}
      (h_α : HasFDerivAt α (fderiv ℝ α ζ) ζ) (z : ℂ) (hζ : ζ ≠ z) :
      HasFDerivAt (fun η : ℂ => α η * (η - z)⁻¹)
        (α ζ • ((smulRight (1 : ℂ →L[ℂ] ℂ) (-((ζ-z)^2)⁻¹)).restrictScalars ℝ)
          + (ζ - z)⁻¹ • fderiv ℝ α ζ)
        ζ`. Plus the `ContDiff ℝ 1`-input corollary
    `hasFDerivAt_mul_inv_sub_of_contDiff`.
  - This is the **input shape** required by mathlib's rectangle Stokes
    (`Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable`),
    whose `Hd` hypothesis demands `HasFDerivAt f (f' x) x` pointwise
    off a countable bad set. With Chip 3c-B, the lone singularity `z`
    becomes the only point we exclude (`s = {z}`).
  - Proof: build `HasDerivAt (fun η => (η - z)⁻¹) (-(ζ-z)⁻²) ζ` over `ℂ`
    via `hasDerivAt_inv` composed with `sub_const` and `HasDerivAt.comp`,
    convert to `ℂ`-`HasFDerivAt`, restrict scalars to `ℝ` (with the same
    `set_option backward.isDefEq.respectTransparency false in` diamond
    workaround as Chip 3c-A), then product-rule via `HasFDerivAt.mul`.
  - Supporting helpers:
    * `hasDerivAt_inv_sub_const` — the `ℂ`-`HasDerivAt`.
    * `hasFDerivAt_real_inv_sub_const` — the `ℝ`-`HasFDerivAt` of `(·-z)⁻¹`.
  - Sorry-free, axiom-free (`propext`, `Classical.choice`, `Quot.sound`
    only). Library entry added.

* **Chip 3c-A — DONE** ([`Analysis/PompeiuKernelLeibniz.lean`](JacobianChallenge/Analysis/PompeiuKernelLeibniz.lean), ~115 LOC).
  - `partialZBar_mul_inv_sub
      {α : ℂ → ℂ} {ζ : ℂ} (h_diff : DifferentiableAt ℝ α ζ) (z : ℂ) (hζ : ζ ≠ z) :
      partialZBar (fun η : ℂ => α η * (η - z)⁻¹) ζ
        = partialZBar α ζ * (ζ - z)⁻¹`.
  - This is the pointwise off-singularity Leibniz reduction that drives
    Chip 3c's rectangle-Stokes argument: on `ζ ≠ z`, the antiholomorphic
    derivative of the Pompeiu integrand collapses to `(∂̄α)(ζ) · (ζ-z)⁻¹`
    because the singular factor `(η - z)⁻¹` is `ℂ`-holomorphic at `η = ζ`
    (Cauchy-Riemann ⇒ `partialZBar = 0`).
  - Proof: apply existing `partialZBar_mul` (Leibniz) from
    `Manifold/PartialZBar.lean` to `f := α`, `g := (· - z)⁻¹`; the second
    Leibniz term vanishes via `partialZBar_eq_zero_of_differentiableAt`
    applied to the `ℂ`-differentiability of `g` at `ζ ≠ z`.
  - Supporting helpers:
    * `differentiableAt_inv_sub_const` — `DifferentiableAt ℂ ((· - z)⁻¹)`
      at `ζ ≠ z`, via `differentiableAt_inv_iff` composed with
      `differentiableAt_id.sub_const`.
    * `differentiableAt_real_inv_sub_const` — the same fact over `ℝ`,
      using `DifferentiableAt.restrictScalars ℝ`. The
      `set_option backward.isDefEq.respectTransparency false in`
      annotation mirrors mathlib's `HasDerivAt.real_of_complex`
      (`Mathlib/Analysis/Complex/RealDeriv.lean:44`) and dodges the
      `IsScalarTower ℝ ℂ ℂ` instance-synthesis diamond flagged in
      `feedback_jacobian_complex_real_diamond` memory.
    * `partialZBar_inv_sub_const_eq_zero` — the Cauchy-Riemann step.
  - Sorry-free, axiom-free (`propext`, `Classical.choice`, `Quot.sound`
    only). Library entry added.

* **Chip 3b — DONE** ([`Analysis/PompeiuKernelPartialZBarBridge.lean`](JacobianChallenge/Analysis/PompeiuKernelPartialZBarBridge.lean), ~180 LOC).
  - `partialZBar_pompeiuKernel_eq_pompeiuKernel_partialZBar
      {α : ℂ → ℂ} (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
      (z : ℂ) :
      partialZBar (pompeiuKernel α) z = pompeiuKernel (partialZBar α) z`.
  - This algebraic bridge reduces the full Cauchy-Pompeiu identity to
    the single classical statement `pompeiuKernel (partialZBar α) z = α z`
    (Chip 3c).
  - Proof: Chip 2d's `fderiv_pompeiuKernel_apply` specialized at
    `v = 1` and `v = I` rewrites the LHS as
    `(1/2) · (pompeiuKernel (αDeriv α 1) z + I · pompeiuKernel (αDeriv α I) z)`.
    By definition `partialZBar α ζ = (1/2) · (αDeriv α 1 ζ) + ((1/2)·I) · (αDeriv α I ζ)`
    pointwise, so the RHS expands the same way via `pompeiuKernel` linearity.
  - Supporting infrastructure (general-purpose, used here and useful
    downstream):
    * `pompeiuKernel_add` — additivity, for continuous compactly-supported
      `α, β` (both integrands integrable by Chip 1c, then
      `MeasureTheory.integral_add`).
    * `pompeiuKernel_const_mul` — `pompeiuKernel (c · α) z = c · pompeiuKernel α z`.
      Unconditional in `α` (Bochner's `integral_const_mul` does not need
      integrability — when not integrable both sides are zero).
    * `pompeiuIntegrand_add`, `pompeiuIntegrand_const_mul` — pointwise
      integrand helpers.
  - Sorry-free, axiom-free (`propext`, `Classical.choice`, `Quot.sound`
    only). Library entry added.

* **Chip 3a — DONE** ([`Analysis/PompeiuKernelSmallDiscLimit.lean`](JacobianChallenge/Analysis/PompeiuKernelSmallDiscLimit.lean), ~250 LOC).
  - `tendsto_circleIntegral_pompeiu_smallDisc
      {α : ℂ → ℂ} (h_cont : Continuous α) (z : ℂ) :
      Tendsto (fun ε : ℝ => ∮ ζ in C(z, ε), α ζ * (ζ - z)⁻¹) (𝓝[>] 0)
        (𝓝 (α z * (2 * ↑π * I)))`.
  - Pointwise decomposition
    `α ζ · (ζ - z)⁻¹ = α z · (ζ - z)⁻¹ + (α ζ - α z) · (ζ - z)⁻¹`
    is lifted to circle integrals on `C(z, ε)` for `ε > 0` via
    `circleIntegral.integral_add`. Both pieces are circle-integrable
    because the singularity at `ζ = z` sits at the centre, not on the
    sphere.
  - Constant piece evaluates exactly: `∮ α z · (ζ - z)⁻¹ = α z · (2πi)`
    via `circleIntegral.integral_const_mul` +
    `circleIntegral.integral_sub_inv_of_mem_ball` with `w = z, c = z,
    R = ε > 0` (so `z ∈ ball z ε`).
  - Remainder is controlled by the modulus of continuity at `z`:
    `‖(α ζ - α z) · (ζ - z)⁻¹‖ ≤ C / ε` on `sphere z ε` where
    `‖ζ - z‖ = ε`, hence
    `‖∮ (α ζ - α z) · (ζ - z)⁻¹‖ ≤ 2 * π * ε * (C / ε) = 2 * π * C`
    via `circleIntegral.norm_integral_le_of_norm_le_const`. For
    `ε < r` from continuity-at-`z` with tolerance `δ / (2π + 1)`, the
    full bound is `2π · δ / (2π + 1) < δ`.
  - Helpers: `circleIntegrable_smul_inv_sub_of_continuous`,
    `circleIntegrable_const_smul_inv_sub`,
    `circleIntegrable_remainder`, `circleIntegral_constant_smul_sub_inv`,
    `norm_circleIntegral_remainder_le`,
    `circleIntegral_pompeiu_decompose`.
  - Sorry-free, axiom-free (`propext`, `Classical.choice`, `Quot.sound`
    only). Library entry added.

### Next chip: **Chip 3c-E — DCT-limit `ε → 0` + final identity `pompeiuKernel (partialZBar α) z = α z`** (~600–1200 LOC)

With Chip 3c-D's balance equation (iterated form) in hand:

```
∫ x in -L..L, ∫ y in -L..L,
  partialZBar α (x+y*I) * regularizedInvSub z hε (x+y*I)
    + α (x+y*I) * partialZBar (regularizedInvSub z hε) (x+y*I) = 0
```

Chip 3c-E takes the `ε → 0` limit to extract
`pompeiuKernel (partialZBar α) z = α z`.

Sub-tasks:

1. **Extend iterated integral to full-plane integral**. For each of the
   two integrand pieces, the support is bounded by `Metric.closedBall 0 L`
   for L large (since `tsupport α ⊆ ball 0 L` and `regularizedInvSub`
   and its `partialZBar` are bounded on `ball 0 L`). So:
   - `∫ x in -L..L, ∫ y in -L..L, (·)` equals
     `∫ ζ : ℂ, (·) ζ ∂volume` for L large.
   This uses `MeasurePreserving.integral_comp` via
   `Complex.volume_preserving_equiv_real_prod` + Fubini.
2. **`ε → 0` limit of `∫ partialZBar α · regularizedInvSub z hε`**.
   - As `ε → 0⁺`, `regularizedInvSub z hε (η) → (η - z)⁻¹` pointwise
     for `η ≠ z` (since `pompeiuCutoff → 1` pointwise off `z`).
   - Dominated convergence: dominating function
     `‖partialZBar α (η)‖ · ‖(η - z)⁻¹‖` is integrable (compact
     support × locally integrable).
   - Limit:
     `∫ ζ, partialZBar α (ζ) * (ζ - z)⁻¹`
     `= -π · pompeiuKernel (partialZBar α) z` (by definition).
3. **`ε → 0` limit of `∫ α · partialZBar (regularizedInvSub z hε)`**.
   This is the harder piece. Using Chip 3c-A's Leibniz reduction
   off `z`:
   `partialZBar (regularizedInvSub z hε) (η)
       = partialZBar (pompeiuCutoff z hε) (η) · (η - z)⁻¹`
   for `η ≠ z`. The support of `partialZBar (pompeiuCutoff z hε)`
   is in the annulus `closedBall z ε \ ball z (ε/2)`. As `ε → 0`, this
   becomes a small-disc contribution.
   
   The cleanest path: use Green's theorem / 2D divergence theorem to
   convert `∫∫_{annulus} α · ∂̄g_ε` to a contour integral around
   the inner boundary `C(z, ε/2)` (where `g_ε = (·-z)⁻¹` outside
   the inner ball, plus the boundary contour around the outer ball
   where `g_ε = 0`). Result:
   `∫ α(η) · partialZBar (regularizedInvSub z hε)(η) dA → -π · α(z)`
   as `ε → 0`, via Chip 3a's small-disc Cauchy limit (scaled by
   `1/(2I)` due to Green's-theorem orientation factor).
4. **Combine**: balance equation `→ 0 = -π · (pompeiuKernel (∂̄α) z) - π · α(z)`, so `pompeiuKernel (∂̄α) z = α(z)`. Wait sign: balance gives `∫(∂̄α)·g_ε = -∫α·∂̄g_ε → -π·α(z)·(-1) = π·α(z)`. Hence `pompeiuKernel (∂̄α) z = -(1/π) · π · α z = -α z`? Sign check needed. The Cauchy-Pompeiu identity standard form is `(∂̄α)/π · (·)⁻¹ → α` so sign should work out. Verify in proof.

5. **Compose with Chip 3b** for the final
   `partialZBar (pompeiuKernel α) z = α z`.

After Chip 3c-E lands, the Item 14 reduction is closed (modulo the
per-`p` `ChartAtConstantOnSource` structural hypothesis, which is
discharged trivially on every concrete X). Chips 4–7 are
chart-pullback + globalization + integration into the existing chain.

**Estimate**: Chip 3c-E is the most analytically heavy piece (DCT,
Green-theorem-like manipulation, careful sign tracking). Realistic
~3–6 sessions, ~600–1200 LOC.

**Estimate**: Chip 3c is ~6–12 sessions across multiple sub-chips
(annulus-Stokes setup, cutoff function, DCT-limit, Leibniz product
rule for `partialZBar` on `(·-z)⁻¹`, assembly). Likely the heaviest
single chip in the arc.

### Chips 4 through 7 (after Chip 3)

* **Chip 4 (~1–2k LOC)** — chart pull-back: lift the Pompeiu kernel from ℂ to a chart-disk on X.
* **Chip 5 (~2–3k LOC)** — globalize to compact X at genus 0. Combines partition of unity over a finite chart cover with the genus-0-specific spreading function construction (Forster Ch. 14, Behnke-Stein-light). This is the substantive classical-content step.
* **Chip 6 (~200 LOC)** — wire to the existing `ofCurve_inj_under_genus_pos`-style chain at [`OfCurveInjFromDegreeOne.lean:90`](JacobianChallenge/Manifold/OfCurveInjFromDegreeOne.lean) to get `δQ - δP ∈ PrincDiv X`, then through the unconditional chain to `X ≃ₜ S²`.
* **Chip 7 (<50 LOC)** — close `Basic.lean:73` by composition.

**Net (remaining, Chips 3–7): 20–45 sessions, 4–9k LOC.**

### Discipline lesson learned today (KEEP)

**No backing out.** The pattern of writing → hitting an error → deleting and restarting eats session time and produces nothing. When stuck:

1. **Debug in place.** Don't delete.
2. **For typeclass synth errors,** decompose the prerequisites and test each in isolation. The fix is usually a missing import 1–2 dependency-hops away.
3. **For tactic failures,** read the actual goal at the failure point and pick the right replacement tactic. `linarith` doesn't work on complex sub-eq-zero; use `sub_ne_zero.mpr` or `sub_eq_zero.mp` directly.
4. **Pull the file only after the session ends with a sorry-free result OR after a clear decision to descope.** Don't pull mid-debug.

This was a real failure mode in the Chip 1a session (three deletion cycles before pushing through). After committing to debug-in-place, the import calibration resolved in ~5 minutes.

---

## TL;DR — current frontier

**`Basic.lean:73 genus_eq_zero_iff_homeo`** still has a `sorry`. The reduction chain in tree, after this session's work:

```
genus_eq_zero_iff_homeo X
  ⇐ Topology/Item14FromHSPOnly.genus_eq_zero_iff_homeo_from_hSP             (in tree, sorry/axiom-free)
  + Topology/S2ImpliesGenus0FromEtalePrimitives.s2ImpliesGenus0_etalePrimitivesArc  (unconditional, in tree)
  + ExistsSimplePoleGermAtSomePoint X                                       ← THE ONE OPEN INPUT

ExistsSimplePoleGermAtSomePoint X
  ⇐ Manifold/ForsterCutoffPoleConstruction.existsSimplePoleGermAtSomePoint_of_dbarSolvability_under_chartConst
                                                                            (in tree, sorry/axiom-free)
  + (p : X)                                                                 ← any p
  + ChartAtConstantOnSource p                                               ← per-p structural; innocuous on
                                                                              every concrete X (RS at finite p,
                                                                              ℂ/L tori, single-chart spaces)
  + DBarSolvabilityAtGenusZero X                                            ← THE ONE CLASSICAL-CONTENT GAP
  + (hg : genus X = 0)                                                      ← available from iff direction
```

**Net**: one classical-content gap (DBar at genus 0) plus a per-`p` structural assumption that's discharge-free on every X anyone cares about in practice.

**BSLB is obsolete for Item 14.** Older HANDOFF / OPEN.md framings of "Item 14 = hSP + BSLB" predate the 2026-05-24 étale-leg merge.

## What's in tree (file by file)

### Forward leg

* [`Manifold/PartialZBarManifold.lean`](JacobianChallenge/Manifold/PartialZBarManifold.lean) — manifold-side `partialZBarManifold f y` (chart-y based), algebraic lemmas (`_add`, `_sub`, `_neg`, `_mul`), Forster specializations, and the "vanishing on holomorphic-pullback functions" theorem. Chip 1 deliverable.
* [`Manifold/PartialZBarManifoldChartPullbackVanish.lean`](JacobianChallenge/Manifold/PartialZBarManifoldChartPullbackVanish.lean) — chart-pullback ∂̄ vanishing transfer lemma. Without `LocallyConstantChartAt` typeclass, transfers `partialZBarManifold f y = 0` (chart-y view) to `partialZBar (f ∘ chart_x.symm) (chart_x y) = 0` (chart-x view) via the holomorphic chart transition.
* [`Manifold/ExistsSimplePoleGermFromGenusZeroDBarSolvability.lean`](JacobianChallenge/Manifold/ExistsSimplePoleGermFromGenusZeroDBarSolvability.lean) — definition of `DBarSolvabilityAtGenusZero X`, classical pole-order keystone `meromorphicOrderAt_inv_sub_const_sub_analytic_eq_neg_one`, **Forster §16.9 consolidator** `existsSimplePoleGermAtSomePoint_of_chartPullback_data` (the unconditional assembly lemma). Chip 2 deliverable.
* [`Manifold/ForsterCutoffPoleConstruction.lean`](JacobianChallenge/Manifold/ForsterCutoffPoleConstruction.lean) — **Chip 2c + 2c-Final**. Bump function `b`, local pole `g₀`, compactly-supported source `α`, off-pole identity `partialZBarManifold_g₀_eq_α_off_pole`, α smoothness `α_contMDiff_under_const`, and the **main theorem `existsSimplePoleGermAtSomePoint_of_dbarSolvability_under_chartConst`**.

### Reverse leg (étale-primitives arc, merged from `feat/item14-affineChartTriangleSimplex-ball`)

* [`Manifold/EtalePrimitives.lean`](JacobianChallenge/Manifold/EtalePrimitives.lean) — étale space of ω-primitives over X. Alt-B foundation.
* [`Manifold/ChartLocalPrimitiveOverlapLocallyConst.lean`](JacobianChallenge/Manifold/ChartLocalPrimitiveOverlapLocallyConst.lean) — overlap locally constant. Alt-B keystone.
* [`Manifold/EtalePrimitivesIsLocalHomeomorph.lean`](JacobianChallenge/Manifold/EtalePrimitivesIsLocalHomeomorph.lean) — `proj : EtalePrimitives om → X` is a local homeomorphism. Chip 3.
* [`Manifold/EtalePrimitivesCovering.lean`](JacobianChallenge/Manifold/EtalePrimitivesCovering.lean) + [`EtalePrimitivesCoveringInfra.lean`](JacobianChallenge/Manifold/EtalePrimitivesCoveringInfra.lean) — `proj` is a covering map. Chip 4a-4b.
* [`Manifold/EtalePrimitivesGlobalSection.lean`](JacobianChallenge/Manifold/EtalePrimitivesGlobalSection.lean) + [`EtalePrimitivesGlobalSmooth.lean`](JacobianChallenge/Manifold/EtalePrimitivesGlobalSmooth.lean) — global primitive on simply-connected X. Chips 4c-4d.
* [`Topology/S2ImpliesGenus0FromEtalePrimitives.lean`](JacobianChallenge/Topology/S2ImpliesGenus0FromEtalePrimitives.lean) — **`s2ImpliesGenus0_etalePrimitivesArc : S2ImpliesGenus0 X`** unconditional. Chip 4e (commit `829a6e8`).

### Integration

* [`Topology/Item14ForwardFromCompactConnected.lean:68`](JacobianChallenge/Topology/Item14ForwardFromCompactConnected.lean) — `genus_eq_zero_iff_homeo_from_existsSimplePoleGerm`, the existing two-input form (`hSP X + S2ImpliesGenus0 X` → iff).
* [`Topology/Item14FromHSPOnly.lean`](JacobianChallenge/Topology/Item14FromHSPOnly.lean) — **`genus_eq_zero_iff_homeo_from_hSP`**, the post-merge one-input form. Composes the existing two-input theorem with the unconditional `s2ImpliesGenus0_etalePrimitivesArc`.

## The ONE open input: `DBarSolvabilityAtGenusZero X`

Stated as the named hypothesis:

```
DBarSolvabilityAtGenusZero X : Prop :=
  genus X = 0 → ∀ α : X → ℂ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α →
    ∃ u : X → ℂ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u ∧ ∀ x : X, partialZBarManifold u x = α x
```

Equivalent classical statements:
- `H¹(X, 𝒪) = 0` at genus 0 (sheaf cohomology).
- Surjectivity of `∂̄` on smooth (0,1)-forms at genus 0 (Dolbeault).
- `Nonempty (HolomorphicEquiv X RiemannSphere)` at genus 0 (uniformization), which separately discharges hSP via the in-tree transport `existsSimplePoleGermAtSomePoint_of_holomorphicEquiv_RS`.

None of these are in mathlib at the pinned commit. Three discharge routes, in order of estimated effort:

| Route | Effort | What it gives |
|---|---|---|
| **Cauchy-Pompeiu kernel + uniformization for genus 0** | ~5–8k LOC, 4–8 person-months focused mathlib-quality work | Targeted route to DBar at genus 0 only. Pompeiu kernel is upstreamable independently (~1k LOC, 2–4 weeks). |
| **Hörmander L² methods for ∂̄** | ~8k LOC, 10–20 person-months | Generic ∂̄-solvability; applies beyond genus 0. Heavy. |
| **Full Hodge / Dolbeault apparatus** | ~15–18k LOC, 18–36 person-months | Reusable across complex geometry. Heaviest. |

## Phase B verdict (2026-05-24): Cauchy-Pompeiu alone does not short-circuit

What mathlib has:
- Building blocks for Pompeiu kernel: rectangle Stokes for real-differentiable functions ([CauchyIntegral.lean:187](.lake/packages/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean) `integral_boundary_rect_of_hasFDerivAt_real_off_countable`), circle integrals, divergence theorem, 2D Lebesgue integration.

What mathlib lacks:
- Explicit Pompeiu kernel formula `u(z) = -(1/π) ∫∫ α(ζ)/(ζ-z) dA(ζ)` and its regularity / `∂̄u = α` proof.
- Dolbeault complex isomorphism with sheaf cohomology.
- Hodge decomposition on Riemann surfaces.
- Sheaf cohomology applied to `𝒪_X` (only abstract `CategoryTheory/Sites/SheafCohomology` exists, no analytic instantiation).

Why Pompeiu alone is not enough: the Pompeiu kernel solves `∂̄u = α` locally on a disk in ℂ, but `u` has `1/z` tails at infinity (not compactly supported even when α is). Globalizing to compact X via partition of unity introduces a residual `(∂̄η)·u` term that requires `H¹(𝒪) = 0` to discharge — exactly the statement we're trying to prove. So Pompeiu + cutoff is circular.

A genus-0-specific route avoiding the circularity must use either uniformization (X ≃ RS biholomorphically, then transport from RS) or a Behnke-Stein-style "spreading function" construction, both of which are textbook content not in mathlib at the pin.

## What's NOT a route to closure

- **`ChartAtConstantOnSource p` removal via mfderiv refactor.** Investigated 2026-05-24. The intrinsic ∂̄ on complex 1-manifolds requires canonical-bundle / `Ω^{0,1}` line-bundle machinery (not in mathlib). The chain-rule alternative (carry the chart-transition factor through ~10 lemmas) is ~1500–2500 LOC of real work but yields only a cosmetically smaller hypothesis list — DBar remains the actual gap. **Not worth pursuing as a standalone effort.**
- **RR-direct route via lifting from RS without biholom.** Audited 2026-05-24, see [`RR_AUDIT.md`](RR_AUDIT.md). Every in-tree route to `RiemannRochGenusZero X` on arbitrary X consumes either `hSP X` or `Nonempty (HolomorphicEquiv X RS)`. No biholom-free transport exists. The "RR-direct" framing relabels the gap rather than shortening it.
- **`SimplePoleGermExtensionHypothesis X` reformulations.** The genus-conditional form (`genus = 0 → hSP X`) is definitionally equivalent to hSP X under the iff's forward direction. Reformulating does not reduce the open content.

## Practical next directions (if you want to keep moving)

1. **Pompeiu kernel as a standalone mathlib PR.** 2–4 weeks focused work, ~1k LOC, upstream-able even without item 14 context. Would be the first concrete step of the Route-1 path above, and is useful infrastructure regardless.
2. **Documentation cleanup pass.** This rewrite + the doc updates this session leave the audit pile in a coherent state. No further code work needed if you want to pause.
3. **Wait for organic mathlib progress on complex geometry.** Estimated 1–3 years for the relevant infrastructure (Hodge, Dolbeault, or uniformization) to land via other contributors.
4. **Sponsor a focused arc** (mathlib-experienced contributor, ~6 months for Route 1). Realistic if Item 14 closure is a hard goal.

The current branch state (`feat/item14-forward-dbar-mul`, tip `bcf6951`) is a stable handoff point: both legs present, single named-hypothesis reduction, Pompeiu Chip 1a landed, all assemblies sorry/axiom-free and individually verified. See the **ACTIVE ARC** section at the top for the in-flight chip breakdown and next-session entry point.

## Pointers

- [`OPEN.md`](OPEN.md) — per-item Buzzard-spec status (item 14 row updated 2026-05-24).
- [`HSP_AUDIT.md`](HSP_AUDIT.md) — hSP-family chain-trace (audit 2026-05-23, post-Chip-2c-Final + post-merge banner added 2026-05-24).
- [`RR_AUDIT.md`](RR_AUDIT.md) — RR-direct route audit (2026-05-24).
- [`C3_AUDIT.md`](C3_AUDIT.md) — Jacobian-side sorries (items 5/11/12/13/17/18/21).
- [`RESIDUE_AUDIT.md`](RESIDUE_AUDIT.md) — residue-theorem sub-tree.
- [`REPO_AUDIT.md`](REPO_AUDIT.md) — repo-wide audit per sorry.

## Discipline notes (apply to any continuation)

- **No paraphrase chips.** Don't introduce new named hypotheses, "from N inputs" reformulations, or per-X structural variants that don't discharge classical content. See `tools/chip-prompt-preamble.md` for the 7 anti-paraphrase gates.
- **No bundling.** One chip per commit; one direction per branch.
- **Local-verify primary.** `LEAN_NUM_THREADS=1 lake env lean FILE.lean`. Never `lake build` (parallel default → apfsd panic on this machine, per CLAUDE.md).
- **Audits live in-repo.** Don't summarize per-item state in commit messages or external notes — update the relevant `*_AUDIT.md` / `OPEN.md` / this file.
