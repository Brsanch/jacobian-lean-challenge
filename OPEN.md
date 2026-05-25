# OPEN

The 24 challenge items in `JacobianChallenge/Basic.lean`, mapped to Buzzard's
spec. Three statuses, with one tag for partial progress:

- **OPEN** — `sorry` still present in `Basic.lean`.
- **STUB** — `sorry` replaced by a body that compiles against the verbatim
  signature but is not the intended mathematics. Either the formula is wrong
  (`pullback := 0`, `degree := 0/1 indicator`, `TopologicalSpace := ⊥`), the
  underlying object the lemma is about is itself a stub (`Jacobian := Pic⁰`
  with `PrincDiv := ⊥`), or the proof crucially depends on a placeholder
  being a placeholder.
- **STRICT-CLOSED** — Buzzard-acceptable: the implementation is honest, the
  underlying object is the intended analytic Jacobian, and the lemma is
  what a strict reviewer would sign off on with no further qualification.
  This is the *only* "closed" bar in this repo.
- *(tag)* **PROOF-HONEST** — applies to a STUB item whose proof body is
  honest and would survive future honest replacement of the upstream
  placeholders. Not closure; it's a tag indicating the proof is real even
  though the underlying object is a stub.

## Authoritative current state (2026-05-23 deep audit)

**14 STRICT-CLOSED, 2 STUB, 8 OPEN.** Per-item details below; full
deep-audit rationale (chain-trace per sorry, doc-bloat findings,
classical-content collapse to 3 textbook theorems) in
[`REPO_AUDIT.md`](REPO_AUDIT.md). Item-14-specific status in
[`HANDOFF_ITEM14.md`](HANDOFF_ITEM14.md). C3 / Jacobian-side status in
[`C3_AUDIT.md`](C3_AUDIT.md).

For chronological session history, see `git log --oneline`. The prior
~2,500-line "Scoreboard" section of this file was deleted 2026-05-23
because it accumulated contradictory item counts (e.g. item 16 appeared
as both OPEN and STRICT-CLOSED in different sections) and obscured the
authoritative item table that follows.

## Definitions (data) — Basic.lean items 1–9 in OPEN.md numbering

| # | Item | Status | Notes |
|---|---|---|---|
| 1 | `genus X : ℕ` | **STRICT-CLOSED** *(post-Forster, 2026-05-17)* | Body: `JacobianChallenge.genus X = Module.finrank ℂ (HolomorphicOneForm X)`. **Finite-dimensionality on a compact connected complex 1-manifold is unconditional** via `DiskChartCover.holomorphicOneFormFiniteDim_holds` (`Manifold/DiskChartCoverFiniteDim.lean`), so the junk-zero convention does not kick in and `Module.finrank` returns the honest geometric genus. |
| 2 | `Jacobian X : Type u` | **STRICT-CLOSED** *(post-ZZ256, 2026-05-12)* | Body: `Jacobian X := Pic0 X` with `Pic0 X = Div0 X ⧸ (PrincDiv X).addSubgroupOf (Div0 X)` and **`PrincDiv X := PrincDivHonestCandidate X`** (honest principal-divisor subgroup, in `Divisor/PrincipalDivisorRange.lean`). |
| 3 | `instance : AddCommGroup (Jacobian X)` | **STRICT-CLOSED** | Inherits from the honest `Pic0` quotient. |
| 4 | `instance : TopologicalSpace (Jacobian X)` | **STUB** | Discrete (`⊥`). The challenge wants the complex-manifold topology (item 5 `ChartedSpace`); discrete is not it. Flips mechanically with item 5. |
| 5 | `instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` | **OPEN** | `sorry`. Requires the analytic-Jacobian rewire of `Jacobian X` to `CanonicalAnalyticJacobianAnonymous X` (under `[HasJacobianAnalyticStructure X]`). Bottom-of-chain: `C3FullInputExt X` bundle = Riemann bilinear + Abel + Jacobi. See `C3_AUDIT.md`. |
| 6 | `Jacobian.ofCurve : X → Jacobian X` | **STRICT-CLOSED** | Body: `Q ↦ [δQ − δP]` in honest `Pic⁰`. |
| 7 | `Jacobian.pushforward f hf` | **STRICT-CLOSED** | Body: `JacobianChallenge.Jacobian.pushforward hf` in `JacobianPushforward.lean`. Descent via P1.4 on the non-constant branch + degree-zero trivialization on the constant branch. |
| 8 | `Jacobian.pullback f hf` | **STRICT-CLOSED** | Body: `Jacobian.pullbackHonest_of_rsum`, with `Pic0.pullbackWeighted` descent obligation discharged unconditionally by `Pic0.divPullbackWeighted_descent_of_smooth`. |
| 9 | `ContMDiff.degree f hf : ℕ` | **STRICT-CLOSED** *(post-zzITEM9, 2026-05-12)* | Body: `JacobianChallenge.ContMDiff.degreeFiber f hf`. Well-definedness across regular witnesses via `degreeFiber_eq_card_of_regular_witness`. |

## Theorems (Prop) — Basic.lean items 10–24 in OPEN.md numbering

| # | Item | Status | Notes |
|---|---|---|---|
| 10 | `instance : T2Space (Jacobian X)` | **STUB** | Discrete ⇒ T2 is honest, but the topology itself is wrong (item 4). Flips with item 5. |
| 11 | `instance : CompactSpace (Jacobian X)` | **OPEN** | `sorry`. Reduces to item 5 via the C3 rewire. |
| 12 | `instance : IsManifold ... ω (Jacobian X)` | **OPEN** | `sorry`. Reduces to item 5. |
| 13 | `instance : LieAddGroup ... ω (Jacobian X)` | **OPEN** | `sorry`. Reduces to item 5 plus smoothness of group ops (auto from the analytic Jacobian construction). |
| 14 | `genus_eq_zero_iff_homeo` (anti-hack vs. `genus := 0`) | **OPEN — Pompeiu arc in flight** | `sorry`. **Post-merge state (2026-05-24):** reduces to ONE named classical hypothesis `hSP X = ExistsSimplePoleGermAtSomePoint X`. The reverse leg `S2ImpliesGenus0 X` is unconditional via `s2ImpliesGenus0_etalePrimitivesArc` (étale-primitives arc, merged from `feat/item14-affineChartTriangleSimplex-ball`). One-input composition is `Topology/Item14FromHSPOnly.lean:genus_eq_zero_iff_homeo_from_hSP`. **BSLB is no longer needed for Item 14.** Via Chip 2c-Final (`Manifold/ForsterCutoffPoleConstruction.lean:existsSimplePoleGermAtSomePoint_of_dbarSolvability_under_chartConst`), hSP X further reduces to `DBarSolvabilityAtGenusZero X` (genus-0 sheaf cohomology / `H¹(X,𝒪)=0`) plus a per-`p` structural hypothesis `ChartAtConstantOnSource p` (innocuous on every concrete X: RS at finite p, ℂ/L tori, single-chart spaces). **Pompeiu kernel arc started 2026-05-24:** Chip 1a landed (`Analysis/PompeiuKernel.lean`, commit `bcf6951` — definitions, measurability, translation reduction, trivial integrability case). Chip 1b landed (`Analysis/InvNormIntegrability.lean`, 163 LOC — `integrableOn_inv_norm_closedBall` via `Complex.lintegral_comp_polarCoord_symm`; sorry-free, axiom-free). Chip 1c landed (`Analysis/PompeiuIntegrandIntegrability.lean`, 140 LOC — `integrable_pompeiuIntegrand_of_continuous_hasCompactSupport`, combining 1a translation reduction + 1b polar bound + bounded-α + `closedBall 0 R ⊆ closedBall z (R + ‖z‖)`; sorry-free, axiom-free). Chip 2a landed (`Analysis/PompeiuKernelTranslation.lean`, 114 LOC — `pompeiuKernel_eq_translated_integrand` pushing `z`-dependence into `α (η + z)` via `integral_add_right_eq_self`; companion integrability transport; sorry-free, axiom-free). Chip 2b landed (`Analysis/PompeiuKernelContinuity.lean`, 157 LOC — `continuous_pompeiuKernel_of_continuous_hasCompactSupport` via `continuousAt_of_dominated` + a `z₀`-local indicator-of-closedBall dominating function; sorry-free, axiom-free). Chip 2c-prep landed (`Analysis/PompeiuKernelDirectionalIntegrand.lean`, 135 LOC — `αDeriv`, its compact-support + continuity preservation, Chip 1c/2b applied to it, plus `exists_fderiv_norm_bound` and `norm_αDeriv_le`; sorry-free, axiom-free). Chip 2c-main landed (`Analysis/PompeiuKernelDerivative.lean`, 292 LOC — `hasDerivAt_pompeiuKernel_real_direction` for `ContDiff ℝ 1 α + HasCompactSupport α` via `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on Chip 2a's translated form; sorry-free, axiom-free). Chip 2d landed (`Analysis/PompeiuKernelSmoothness.lean`, 515 LOC — `contDiff_pompeiuKernel_infty`: `ContDiff ℝ ∞ α + HasCompactSupport α → ContDiff ℝ ∞ (pompeiuKernel α)`, via `hasFDerivAt_pompeiuKernel` (HasFDerivAt lift through `hasFDerivAt_integral_of_dominated_of_fderiv_le` with complex parameter), `fderiv_pompeiuKernel_apply : fderiv ℝ (pompeiuKernel α) z₀ v = pompeiuKernel (αDeriv α v) z₀` (using `ContinuousLinearMap.integral_apply`), and ℕ-induction via `contDiff_succ_iff_fderiv_apply` (`ℂ` finite-dim over `ℝ`); sorry-free, axiom-free). Chip 3a landed (`Analysis/PompeiuKernelSmallDiscLimit.lean`, ~250 LOC — `tendsto_circleIntegral_pompeiu_smallDisc : Continuous α → Tendsto (fun ε => ∮ ζ in C(z, ε), α ζ · (ζ - z)⁻¹) (𝓝[>] 0) (𝓝 (α z · (2πI)))`, via the splitting `α ζ · (ζ - z)⁻¹ = α z · (ζ - z)⁻¹ + (α ζ - α z) · (ζ - z)⁻¹`, exact constant integral from `circleIntegral.integral_sub_inv_of_mem_ball`, and remainder bound from `circleIntegral.norm_integral_le_of_norm_le_const` + continuity at `z`; sorry-free, axiom-free). Chip 3b landed (`Analysis/PompeiuKernelPartialZBarBridge.lean`, ~180 LOC — `partialZBar_pompeiuKernel_eq_pompeiuKernel_partialZBar : ContDiff ℝ 1 α → HasCompactSupport α → ∀ z, partialZBar (pompeiuKernel α) z = pompeiuKernel (partialZBar α) z`, via Chip 2d's `fderiv_pompeiuKernel_apply` at v=1 and v=I plus `pompeiuKernel` additivity + scalar-multiplication linearity proved in the same file; reduces the full Cauchy-Pompeiu identity to the single classical statement `pompeiuKernel (partialZBar α) z = α z` (Chip 3c); sorry-free, axiom-free). Chip 3c-A landed (`Analysis/PompeiuKernelLeibniz.lean`, ~115 LOC — `partialZBar_mul_inv_sub : DifferentiableAt ℝ α ζ → ζ ≠ z → partialZBar (fun η => α η · (η - z)⁻¹) ζ = partialZBar α ζ · (ζ - z)⁻¹`, the pointwise off-singularity Leibniz reduction, via existing `partialZBar_mul` + `partialZBar_eq_zero_of_differentiableAt` applied to the `ℂ`-holomorphy of `(· - z)⁻¹` at `ζ ≠ z`; uses `set_option backward.isDefEq.respectTransparency false in` for the `restrictScalars ℝ` step mirroring mathlib's `HasDerivAt.real_of_complex` to dodge the `IsScalarTower ℝ ℂ ℂ` diamond; sorry-free, axiom-free). Chip 3c-B landed (`Analysis/PompeiuKernelMulInvFDeriv.lean`, ~130 LOC — `hasFDerivAt_mul_inv_sub : HasFDerivAt α (fderiv ℝ α ζ) ζ → ζ ≠ z → HasFDerivAt (fun η => α η · (η - z)⁻¹) (α ζ • g'_ζ + (ζ-z)⁻¹ • fderiv ℝ α ζ) ζ`, the input shape required by mathlib's rectangle Stokes, via `HasDerivAt.comp` for `(·-z)⁻¹`, `HasFDerivAt.restrictScalars ℝ` with the same diamond-workaround `set_option`, and `HasFDerivAt.mul`; sorry-free, axiom-free). Chip 3c-C₁ landed (`Analysis/PompeiuKernelCutoff.lean`, ~160 LOC — `pompeiuCutoff z ε : ℂ → ℝ` defined via mathlib's `ContDiffBump z` with `rIn := ε/2, rOut := ε`, with all properties: `= 0` on `closedBall z (ε/2)`, `= 1` outside `ball z ε`, `0 ≤ · ≤ 1`, `ContDiff ℝ n` for all `n`, `=ᶠ[𝓝 z] 0` (the key fact for smoothness of the regularized integrand at `z`), plus `tsupport (1 - pompeiuCutoff) ⊆ closedBall z ε`; sorry-free, axiom-free). Chip 3c-C₂ landed (`Analysis/PompeiuKernelRegularizedInv.lean`, ~140 LOC — `regularizedInvSub z hε η := (η - z)⁻¹ · ((pompeiuCutoff z hε η : ℝ) : ℂ)` with `regularizedInvSub_contDiff : ContDiff ℝ n (regularizedInvSub z hε)`. Proof: case-split on `ζ = z` vs `ζ ≠ z`. Off `z`: product of smooth `(·-z)⁻¹` (via `contDiffAt_inv` over ℂ + `restrict_scalars ℝ` with the same diamond `set_option`) and the cast `((pompeiuCutoff · : ℝ) : ℂ)` (smooth via `Complex.ofRealCLM.contDiff`). At `z`: `=ᶠ[𝓝 z] 0` via `pompeiuCutoff_eventuallyEq_zero` carried through `filter_upwards`, finished by `ContDiffAt.congr_of_eventuallyEq` against `contDiffAt_const`; sorry-free, axiom-free). Chip 3c-D landed (`Analysis/PompeiuKernelStokes.lean`, ~370 LOC — main `iteratedIntegral_partialZBar_eq_zero : ContDiff ℝ 1 f → tsupport f ⊆ ball 0 L → ∫x in -L..L, ∫y in -L..L, partialZBar f (x+y*I) = 0` for cs `C^1`, via mathlib's `integral_boundary_rect_of_differentiableOn_real` on `[-L,L]²` + 4 boundary line integrals vanishing (compact support → every boundary point has norm ≥ L → outside tsupport) + algebraic identity `I•f' 1 - f' I = 2·I·partialZBar f` + constant-pull through interval integrals; plus application `balance_iteratedIntegral_eq_zero` for `α · regularizedInvSub z hε` via Leibniz `partialZBar_mul` from `Manifold/PartialZBar.lean`; sorry-free, axiom-free). Chip 3c-E landed (`Analysis/PompeiuKernelPlaneIntegral.lean` ~230 LOC + `Analysis/PompeiuKernelDCTLimit.lean` ~406 LOC = 636 LOC: Section A = Fubini bridge `integral_complex_eq_iteratedIntegral_of_tsupport_in_ball : Integrable f → tsupport f ⊆ ball 0 L → ∫ζ:ℂ, f ζ = ∫x in -L..L, ∫y in -L..L, f(x+y·I)` via `Complex.volume_preserving_equiv_real_prod` + `MeasureTheory.integral_prod` + `setIntegral_eq_integral_of_forall_compl_eq_zero` cutting outer/inner ℝ-integrals to `Ioc (-L) L` using compact support → `intervalIntegral.integral_of_le`. Section B = plane-form balance equation `balance_plane_eq_zero : ∫ζ:ℂ, partialZBar α ζ · regInvSub z hε ζ + α ζ · partialZBar(regInvSub z hε) ζ = 0`, derived by applying Section A's bridge to Chip 3c-D's `balance_iteratedIntegral_eq_zero` with support certified via `tsupport_partialZBar_subset` (`tsupport_fderiv_apply_subset` + `tsupport_mul_subset_right` + `tsupport_add` chain) and `tsupport_mul_subset_left`. Section C = DCT limit on first summand `tendsto_integral_partialZBar_alpha_mul_regInvSub : Tendsto (fun ε ↦ ∫ζ, partialZBar α ζ · regularizedInvSubReal z ε ζ) (𝓝[>] 0) (𝓝 (∫ζ, partialZBar α ζ · (ζ-z)⁻¹))` via `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` with dominator `‖partialZBar α ζ‖ · ‖(ζ-z)⁻¹‖` integrable by Chip 1c applied to `partialZBar α` (continuous + cs via `partialZBar_continuous` + `partialZBar_hasCompactSupport`), pointwise convergence by eventual constancy `pompeiuCutoff z hε ζ = 1` for `ε < dist ζ z` (and both sides = 0 at ζ = z), norm bound `‖regInvSub z hε ζ‖ ≤ ‖(ζ-z)⁻¹‖` from `|pompeiuCutoff| ≤ 1`. Wrapper `regularizedInvSubReal z ε` defaults to `(·-z)⁻¹` on `ε ≤ 0` to eliminate `Tendsto` dependent-typing on `hε`. RHS equals `-π · pompeiuKernel (partialZBar α) z` by def. Sorry-free, axiom-free). **Chip 3c-F in flight — route (b) explicit radial bump chosen.** Sub-pieces landed: **3c-F-1** (commit `d99d822`, ~380 LOC across `PompeiuKernelRadialBump.lean` + `PompeiuKernelRadialWirtinger.lean`: explicit `psiBump`/`radialBump`/`radialCutoff` mirroring `pompeiuCutoff`'s properties + radial Wirtinger formula `partialZBar_radial_of_ne : η ≠ z → HasDerivAt ψ ψ' ‖η-z‖ → partialZBar (fun w => (ψ ‖w-z‖ : ℂ)) η = (ψ'/2) * (η - z) / ‖η - z‖` via `fderiv_norm_sq_apply` + `HasFDerivAt.sqrt` + `innerSL_{one,I}_complex` evaluations + `Complex.re_add_im` assembly). **3c-F-2-prep** (commit `07333c8`, ~230 LOC across `PompeiuKernelRadialIntegrand.lean` + initial `PompeiuKernelRadialIntegral.lean`: `partialZBar_radial_div_eq_radial : η ≠ 0 → partialZBar (fun w => (ψ ‖w‖ : ℂ)) η / η = (ψ' / (2·‖η‖) : ℂ)` cancelling the `η/‖η‖` factor; `unitRadialBumpC` def + polar-point invariants + `integrand_at_polar_symm : 0 < r → integrand (polarCoord.symm (r, θ)) = ((deriv (psiBump 1) r / (2·r)) : ℂ)`). **3c-F-2 polar transformation** (commit `945aa34`, ~50 LOC extending `PompeiuKernelRadialIntegral.lean`: `scaled_integrand_at_polar_symm` cancelling Jacobian r with 1/(2r); `integral_partialZBar_div_eq_polar_integral : ∫ζ:ℂ, partialZBar unitRadialBumpC ζ / ζ = ∫p in Ioi 0 ×ˢ Ioo (-π) π, ((deriv (psiBump 1) p.1 / 2) : ℂ)` via `Complex.integral_comp_polarCoord_symm` + `setIntegral_congr_fun`). **3c-F-2 bound lemma** (commit `e55dbfb`, ~30 LOC: `exists_bound_deriv_psiBump_one` for the dominating function + `deriv_psiBump_one_eq_zero_of_{neg, one_lt}` vanishing outside [0,1]). **3c-F-2-final landed** (commit `750bab2`, ~205 LOC `PompeiuKernelRadialIntegralFinal.lean`: `integral_partialZBar_unitRadialBumpC_div_eq_neg_pi : ∫ ζ : ℂ, partialZBar unitRadialBumpC ζ / ζ = -π`. Chain: `intervalIntegral.integral_deriv_eq_sub` + `psiBump_one_{zero,one}` for FTC on `[0, 1]` = -1; `Set.Ioc_union_Ioi_eq_Ioi` + `deriv_psiBump_one_eq_zero_of_one_lt` (a.e. zero on Ioi 1) + `setIntegral_union` to extend to `Ioi 0`; `integral_ofReal` + `integral_mul_const` for ℂ-lift to (-1/2 : ℂ); `setIntegral_const` + `Real.volume_real_Ioo_of_le` + `Complex.real_smul` (forced via `show` because `rw` doesn't unify the smul-instance form) for θ-integral = (2π : ℂ); `setIntegral_prod_mul` with `g ≡ 1` (explicit `μ, ν := volume` to resolve SFinite metavariables; `show` aligns `volume` vs `volume.prod volume`; `Eq.trans` instead of `rw` to bypass alpha-equivalence pattern-matching failures) for Fubini; final `(-1/2) * (2π) = -π`). **Chip 3c-F-3a landed** (commit `299034a`, `PompeiuKernelRegularizedInvRadial.lean` ~131 LOC: `regularizedInvSubRadial z ε η := (η-z)⁻¹ · ((radialCutoff z ε η : ℝ) : ℂ)` + `ContDiff ℝ n` via case-split off-z / at-z; also fills the docstring-promised but missing `radialBump_contDiff` / `radialCutoff_contDiff` in `PompeiuKernelRadialBump.lean` via locally-constant-1 on ball z (ε/2) at η=z and `psiBump_contDiff ∘ contDiffAt_norm` at η ≠ z). **Chip 3c-F-3b landed** (commit `44dd309`, `PompeiuKernelStokesRadial.lean` ~136 LOC: `balance_iteratedIntegral_eq_zero_radial`, line-for-line replay of 3c-D applying the generic `iteratedIntegral_partialZBar_eq_zero` to `α · regularizedInvSubRadial` + Leibniz via `partialZBar_mul`). **Chip 3c-F-3c landed** (commit `22f6898`, `PompeiuKernelDCTLimitRadial.lean` ~303 LOC: Section B `balance_plane_eq_zero_radial` via 3c-F-3b + Fubini bridge from 3c-E; Section C `tendsto_integral_partialZBar_alpha_mul_regInvSubRadial` via mathlib's DCT — pointwise convergence at ζ ≠ z eventually `radialCutoff z ε ζ = 1`, at ζ = z via `(z-z)⁻¹ = 0`; dominator reused from 3c-E's `integrable_dominator_partialZBar`; wrapper `regularizedInvSubRadialReal z ε` defaults to `(·-z)⁻¹` on `ε ≤ 0`). **Chip 3c-F-3d-1 landed** (commit `3068824`, `PompeiuKernelSecondSummandIdentity.lean` ~144 LOC: pointwise identity `partialZBar (regularizedInvSubRadial z ε) η = (η-z)⁻¹ · partialZBar (radialCutoffComplex z ε) η` for ALL η — off z by Leibniz + `partialZBar_inv_sub_const_eq_zero` from 3c-A; at η=z both sides 0 via `regularizedInvSubRadial =ᶠ[𝓝 z] 0` and `(z-z)⁻¹ = 0` in ℂ). **Chip 3c-F-3d-2-prep/2a/2b landed** (commits `c9b8c7c`, `83f1e81`, `08479b1` in `PompeiuKernelRadialRescaling.lean`, total ~246 LOC: 2-prep gives `psiBump_rescale : psiBump ε (ε·r) = psiBump 1 r`, `norm_z_add_smul_sub`, and the `radialBump`/`radialCutoff` rescaling identities under η = z + εw; 2a gives `deriv_psiBump_rescale : deriv (psiBump ε) (ε·r) = ε⁻¹ · deriv (psiBump 1) r` via differentiating 2-prep using `HasDerivAt.unique`; 2b is the headline pointwise ∂̄ rescaling `partialZBar (radialBumpComplex z ε)(z + εw) = ε⁻¹ · partialZBar (unitRadialBumpC) w` — case-split w = 0 (both vanish via eventuallyEq 1) / w ≠ 0 (apply Chip 3c-F-1's `partialZBar_radial_of_ne` to each side + 2a's derivative rescaling + `push_cast`/`field_simp`)). All sorry-free, axiom-free. **Remaining for Chip 3c-F**: 3c-F-3d-2c (substitution identity for the integral via change-of-variable + the pointwise identity, ~150-250 LOC); 3c-F-3d-3 (DCT on substituted integral, ~150-200 LOC); 3c-F-4 (combine + Chip 3b compose, ~50 LOC). Estimate: 1-2 more sessions, ~300-450 more LOC. **Chip 5 scouting (2026-05-25)**: refined Chips 4-7 estimate via direct repo + mathlib audit. Chip 4 (chart-pullback): **600-1,200 LOC, 3-5 sessions** (lighter than original 1-2k thanks to existing `PartialZBarManifold.lean` + `PartialZBarManifoldChartPullbackVanish.lean` + `ChartPullbackDataConstruction.lean`). Chip 5 (genus-0 globalization → `DBarSolvabilityAtGenusZero X`): **1,800-2,800 LOC, 7-12 sessions** realistic (floor 1,200 LOC if tight Forster Ch. 14 tracking; ceiling 3,500-4,000 LOC if Dolbeault/sheaf-cohomology framework needs building). Mathlib has manifold partition-of-unity (✓) but NO Dolbeault complex, NO sheaf cohomology of analytic structure sheaf, NO Behnke-Stein — classical content built from scratch. Repo has ~4,200 LOC of `DiskChartCover*` infrastructure (mostly C3/Hodge-chain-targeted; partial reuse). Dominant uncertainty: whether direct Cauchy-Pompeiu + partition-of-unity argument suffices (2,000-2,500 LOC range) vs needing framework build (pushes toward 3,500+). Chip 6 (~200 LOC, 1 session) + Chip 7 (<50 LOC). **Net remaining (3c-F-rest through 7): ~3,250-5,250 LOC, ~13-22 sessions** (refined from 20-45 sessions / 4-9k LOC). See `HANDOFF_ITEM14.md` "Chip 5 scouting report" for cited defs and infrastructure list. |
| 15 | `ofCurve_self : ofCurve P P = 0` | **STRICT-CLOSED** | Real proof reducing to `[δP − δP] = 0` in honest `Pic⁰`. |
| 16 | `ofCurve_inj` (anti-hack vs. `Jacobian := PUnit`) | **STRICT-CLOSED** | Body in `Basic.lean` line 143–144: `JacobianChallenge.ofCurve_inj_holds P h` (`Manifold/ChartDerivNeZeroImpliesNonCriticalDischarge.lean`). All-unconditional discharge chain: `PrincDivWitnessExtraction` → degree-1 mero function (via `DegreeOneFromSimpleZeroSimplePoleDischarge`) → `bijective_of_degreeFiber_eq_one` + `bijectiveAnalyticIsBiholomorphism_holds` → biholomorphism `X ≃ RiemannSphere` → `genus = 0`, contradicting `0 < genus X`. |
| 17 | `Jacobian.ofCurve_contMDiff` | **OPEN** | `sorry`. Requires item 5 plus per-curve Abel–Jacobi smoothness from `JacobianAnalyticClosureBundle`. |
| 18 | `Jacobian.pushforward_contMDiff` | **OPEN** | `sorry`. Requires item 5 plus per-curve `JacobianAnalyticPushforwardLift`. |
| 19 | `pushforward_id_apply` | **STRICT-CLOSED** | Real proof via `Pic0.pushforward_id` ↦ `Div.singletonMap_id_apply`. |
| 20 | `pushforward_comp_apply` | **STRICT-CLOSED** | Real proof via `Pic0.pushforward_comp` ↦ `Div.singletonMap_comp_apply`. |
| 21 | `Jacobian.pullback_contMDiff` | **OPEN** | `sorry`. Requires item 5 plus per-curve `JacobianAnalyticPullbackLift`. |
| 22 | `pullback_id_apply` | **STRICT-CLOSED** | Body: `JacobianChallenge.Jacobian.pullbackHonest_of_rsum_id _ P`. |
| 23 | `pullback_comp_apply` | **STRICT-CLOSED** | Body: `pullbackHonest_of_rsum_comp` with multiplicative ramification weights `manifoldRamificationIndex_comp_unconditional`. |
| 24 | `pushforward_pullback : pushforward f (pullback f P) = degree f • P` | **STRICT-CLOSED** | Body: `pushforward_pullbackHonest_of_rsum` — case-splits on `IsConstantMap f`. |

## Score

- **STRICT-CLOSED: 14 / 24** — items 1, 2, 3, 6, 7, 8, 9, 15, 16, 19, 20, 22, 23, 24.
- **STUB: 2** — items 4, 10 (placeholder discrete topology; flips mechanically with item 5).
- **OPEN: 8** — items 5, 11, 12, 13, 14, 17, 18, 21.

## The 8 OPEN items collapse to 2 substantive classical theorems

(Was 3 pre-2026-05-24 merge; BSLB became obsolete when the étale-primitives
arc merged in, leaving `DBarSolvabilityAtGenusZero X` and `C3FullInputExt X`.)

After auditing every named-hypothesis chain to its leaves (2026-05-23):

1. **Item 14's `hSP`** — `ExistsSimplePoleGermAtSomePoint X`. After
   Chip 2c-Final (2026-05-24, `Manifold/ForsterCutoffPoleConstruction.lean`),
   reduces further to **`DBarSolvabilityAtGenusZero X`** (= `H¹(X, 𝒪) = 0`
   at genus 0, equivalently solvability of `∂̄ u = α` for smooth (0,1)
   forms α at genus 0) plus a per-`p` structural hypothesis
   `ChartAtConstantOnSource p` (innocuous on concrete X). DBar is the
   actual classical-content gap. Bottom of the alternate Riemann-Roch
   chain: `RR_DimGE2_GenusZero_Germ X` (equivalent statement, not
   shorter).
2. ~~**Item 14's `BSLB`**~~ **OBSOLETE for Item 14 (2026-05-24 merge).**
   The reverse leg `S2ImpliesGenus0 X` is unconditionally discharged
   on arbitrary X by `s2ImpliesGenus0_etalePrimitivesArc`
   (`Topology/S2ImpliesGenus0FromEtalePrimitives.lean`, étale-primitives
   arc from `feat/item14-affineChartTriangleSimplex-ball`). The BSLB
   chain was a parallel route to the same conclusion and is no longer
   needed. The one-input composition
   `Topology/Item14FromHSPOnly.genus_eq_zero_iff_homeo_from_hSP` shows
   Item 14 reduces to hSP alone.
3. **C3's `C3FullInputExt X`** — bundle of Riemann bilinear relations
   + Abel's theorem + Jacobi inversion. Closes items 5/11/12/13/17/18/21
   collectively once landed. Per-curve `lattice_match` certificates
   close items 18/21.

That's it. The infrastructure is enormously over-built (1072 `.lean`
files, 182k LOC), but the genuine remaining classical content is
textbook Forster Ch. III §16–21 / Griffiths-Harris Ch. 2 §2–§3.

## Mathlib-prerequisite candidates (likely needed before strict closure)

- ~~**Whitney smooth approximation for manifold-valued maps**~~ —
  was tagged for the BSLB path; **obsolete after the 2026-05-24
  étale-primitives merge** (reverse leg discharged unconditionally
  without Whitney machinery).
- **Cauchy-Pompeiu kernel + ∂̄-solvability on disks** — would let us
  formalize Forster's elementary route to `DBarSolvabilityAtGenusZero X`
  if combined with classical content on globalization. Mathlib has
  the building blocks (rectangle Stokes, divergence thm, 2D integrals)
  but not the explicit kernel. ~1k LOC, 2–4 weeks. Useful upstream
  even outside this project. **Does not by itself close item 14** —
  globalization still requires `H¹(𝒪) = 0` at genus 0 or equivalent.
- **Riemann–Roch + Serre duality** — for item 14 `hSP` (alternate
  classical route to DBar). Multi-month Lean project; no current
  mathlib coverage.
- **Period-lattice / Hodge bilinear positivity** — for C3 `C3FullInputExt`.
- **Topological degree of proper holomorphic maps** between Riemann
  surfaces. `fibres_finite_statement` and `regular_value_exists_statement`
  are discharged unconditionally in tree.

## Local infrastructure

The repo's per-file map lives in `JacobianChallenge.lean` (the import
manifest) and the file system. `CHANGELOG.md` documents which files
landed in which session. This OPEN.md is intentionally short — the
authoritative status is the item table above + the audit docs
referenced at the top of this file.
