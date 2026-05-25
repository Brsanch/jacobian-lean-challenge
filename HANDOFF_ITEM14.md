# Item 14 — handoff

Last rewrite: 2026-05-24 (post Chip 2c-Final + étale-leg merge + Phase B Cauchy-Pompeiu audit + Pompeiu Chips 1a, 1b, 1c, 2a landed).

Prior versions of this file accumulated layered banners across sessions. This rewrite consolidates the current state. `git log HANDOFF_ITEM14.md` preserves the history.

---

## 🟢 ACTIVE ARC: Pompeiu kernel (committed 2026-05-24)

After exhaustive audit (2026-05-24) confirmed no route exists at this mathlib pin to close Item 14 without formalizing classical content, the **Pompeiu kernel + Riemann existence at genus 0** route was selected as the path with lowest expected surprise. Estimated **25–50 focused sessions / 6–12 months** at typical chip cadence.

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

### Next chip: **Chip 2b — continuity of `pompeiuKernel α` in `z`** (~150–300 LOC)

**Target lemma.**

```
theorem continuous_pompeiuKernel_of_continuous_hasCompactSupport
    {α : ℂ → ℂ} (h_cont : Continuous α) (h_supp : HasCompactSupport α) :
    Continuous (pompeiuKernel α)
```

**Strategy.** Use Chip 2a's translation form
`pompeiuKernel α z = -(π⁻¹) · ∫ η, α (η + z) · η⁻¹`. The singularity is
now pinned at `η = 0` (independent of `z`). For `z` in any bounded
ball `B ⊆ ℂ`:
1. Pick a fixed compact `K ⊇ closedBall 0 R₀` containing `tsupport α
   − z` uniformly for `z ∈ B` (concretely `K := closedBall 0
   (R₀ + diam B + ‖center B‖)`).
2. Outside `K`, `α (η + z) = 0` (for `z ∈ B`), so the integrand
   vanishes; uniformly bound by `M · ‖η‖⁻¹` on `K`, which is
   integrable by Chip 1b.
3. Apply `MeasureTheory.continuous_of_dominated` (or
   `Continuous.integral_continuous_param`) with the integrable
   dominating function `M · ‖η‖⁻¹ · K.indicator`.

### Chip 2c, 2d (after 2b)

* **Chip 2c (~400–700 LOC)** — first ℝ-derivative `∂/∂z` (or partial in
  Re/Im). Differentiation under the integral: `∂_z [α(η+z) · η⁻¹] =
  (∂_z α)(η+z) · η⁻¹`. Dominating function still `‖∂_z α‖_∞ · M' · ‖η‖⁻¹`.
* **Chip 2d (~300–500 LOC)** — iterate to obtain ℝ-C^∞ smoothness. Use
  `ContDiff.of_succ` or induction on derivative order.

### Chips 3 through 7 (after 2)

* **Chip 2 (~1–2k LOC)** — smoothness in z: `pompeiuKernel α` is `C^∞ ℝ` on ℂ. Uses differentiation under the integral.
* **Chip 3 (~2–4k LOC, the heaviest chip)** — the identity `∂̄(pompeiuKernel α) = α`. Routes through Cauchy-Pompeiu boundary terms; rectangle Stokes (`integral_boundary_rect_of_hasFDerivAt_real_off_countable` from mathlib's CauchyIntegral) is the key tool.
* **Chip 4 (~1–2k LOC)** — chart pull-back: lift the Pompeiu kernel from ℂ to a chart-disk on X.
* **Chip 5 (~2–3k LOC)** — globalize to compact X at genus 0. Combines partition of unity over a finite chart cover with the genus-0-specific spreading function construction (Forster Ch. 14, Behnke-Stein-light). This is the substantive classical-content step.
* **Chip 6 (~200 LOC)** — wire to the existing `ofCurve_inj_under_genus_pos`-style chain at [`OfCurveInjFromDegreeOne.lean:90`](JacobianChallenge/Manifold/OfCurveInjFromDegreeOne.lean) to get `δQ - δP ∈ PrincDiv X`, then through the unconditional chain to `X ≃ₜ S²`.
* **Chip 7 (<50 LOC)** — close `Basic.lean:73` by composition.

**Net: 25–50 sessions, 5–10k LOC.**

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
