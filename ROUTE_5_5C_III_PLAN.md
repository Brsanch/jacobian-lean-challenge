# Route III planning — Behnke-Stein iteration for `DBarSolvabilityAtGenusZero`

**Date**: 2026-05-26.
**Status**: user-selected after Forster Ch.14 audit ruled out Route I
(see [`ROUTE_5_5C_FORSTER_AUDIT.md`](ROUTE_5_5C_FORSTER_AUDIT.md)).

## Goal

Discharge

```lean
def DBarSolvabilityAtGenusZero : Prop :=
  JacobianChallenge.genus X = 0 →
  ∀ α : X → ℂ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α →
  ∃ u : X → ℂ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u ∧
    ∀ x : X, partialZBarManifold u x = α x
```

via a Schauder-type iteration on the partition-sum candidate built in
Chip 5.4b. The unconditional Cauchy-Pompeiu identity (Chip 3c-F-4) is
the disk-level building block; the iteration spreads it globally.

## The classical structure

Following Forster, *Lectures on Riemann Surfaces*, §14 (Solution of
`∂̄u = ω` on a compact Riemann surface):

Define an operator `T : C^∞(X) → C^∞(X)` such that solving `∂̄u = α`
is equivalent to solving a fixed-point equation `u = Tu + u_0` for some
explicit `u_0` (the candidate from Chip 5.4b assembly). Show `T` is a
contraction in a suitable norm (sup-norm on a compact subset, or
Hölder-norm if sup-norm is insufficient). Sum the geometric series.

Operationally, the iteration replaces partition-of-unity in `y` with
**explicit error control**:

* `u_0 := Σ_i v_i` — the partition-Pompeiu candidate (existing).
* `E_0(y) := α(y) - partialZBarManifold u_0 y` — the error.
* Bound `‖E_0‖_∞ ≤ c · ‖α‖_∞` for some `c < 1` (this is the
  Schauder estimate; constant depends on the cover geometry).
* Iterate: `u_{n+1} := u_n + (correction built from E_n)`,
  `E_{n+1} := α - ∂̄ u_{n+1}`, `‖E_{n+1}‖ ≤ c · ‖E_n‖`.
* Sum: `u := lim u_n = u_0 + Σ corrections`. Geometric-series
  convergence in sup-norm gives `u ∈ C^∞` (smoothness needs Schauder
  estimates on higher derivatives, NOT just sup-norm — see "open
  research" below).

## Chip sequence

### Phase A — Norm infrastructure on ℂ (foundational)

* **5.5c-III-1 — Pompeiu sup-norm bound on ℂ.** First chip.
  ```
  |pompeiuKernel α z| ≤ (constant · R) · ‖α‖_∞
  ```
  for `α : ℂ → ℂ` continuous with `tsupport α ⊆ closedBall 0 R`. The
  factor scales with R = radius of support. Reuses Chip 1b's polar-
  coordinate bound. ~150-220 LOC.

* **5.5c-III-2 — Pompeiu Lipschitz / Hölder bound on ℂ.**
  ```
  |pompeiuKernel α z - pompeiuKernel α z'| ≤ C · |z - z'| · ‖α‖_∞
  ```
  (or possibly weaker: `≤ C · |z - z'|^{1/2}` if Lipschitz fails — to
  be checked). Used in Phase B for higher-derivative norm control.
  ~250-400 LOC.

### Phase B — Norm infrastructure on X

* **5.5c-III-3 — Sup-norm on `C^∞(X)` for compact X.**
  ```
  ‖f‖_∞ := ⨆ x, ‖f x‖
  ```
  Standard mathlib `Continuous.bounded_above_of_compact_support` or
  `iSup_norm`. Algebra of sup-norm. ~100-150 LOC.

* **5.5c-III-4 — Pompeiu pullback sup-norm on X.** Pull the Phase A
  bound across the cover charts. For each `i ∈ basePoints`, the
  contribution `v_i := pompeiuKernel(chartPullbackZero i (ρ_i α)) ∘
  chart_i` satisfies `‖v_i‖_∞ ≤ C_i · ‖ρ_i · α‖_∞ ≤ C_i · ‖α‖_∞`.
  Summing over i, `‖u_0‖_∞ ≤ (Σ_i C_i) · ‖α‖_∞`. ~200-300 LOC.

### Phase C — Error operator and contraction

* **5.5c-III-5 — Define the error operator `T : (X → ℂ) → (X → ℂ)`.**
  `T α := α - partialZBarManifold u_0` where `u_0` is the
  partition-Pompeiu candidate built from `α`. Smoothness of `T α` from
  smoothness of `α` and `u_0`. ~150-250 LOC.

* **5.5c-III-6 — Contraction estimate `‖T α‖_∞ ≤ c · ‖α‖_∞`.** The
  central analytic content. Bounds the outer-ring leakage error
  (where `χ_i ≠ 0` but `ρ_i = 0`, the cutoff transition zone). The
  constant `c` depends on the cover geometry. For a sufficiently
  refined cover, `c < 1` is achievable. ~400-600 LOC. **Heaviest
  chip in Phase C.**

### Phase D — Iteration and convergence

* **5.5c-III-7 — Geometric series of corrections.** Define
  `u_∞ := Σ_{n ≥ 0} T^n(u_0)` (formally). Convergence in sup-norm
  from Phase C. ~200-300 LOC.

* **5.5c-III-8 — Smoothness of the limit.** From Phase A's Hölder
  bound + iteration, the limit u_∞ is in some Sobolev / Hölder class.
  Bootstrap to C^∞. **Open research question**: does the iteration
  preserve C^∞ smoothness in finite norm, or only in C^k for finite
  k? Classical Forster argument uses C^0 + interior regularity of
  ∂̄; need to check at this mathlib pin. ~300-500 LOC.

### Phase E — Final assembly

* **5.5c-III-9 — `∂̄ u_∞ = α`.** Combine convergence + smoothness +
  Phase C's contraction to get `partialZBarManifold u_∞ y = α y` for
  all `y`. ~150-250 LOC.

* **5.5c-III-10 — Discharge `DBarSolvabilityAtGenusZero`.** Final
  glue. Requires the genus-0 condition to dispatch — note that the
  iteration as described is **NOT genus-specific**; the
  cutoff-leakage error contracts for any compact RS, regardless of
  genus. The genus-0 condition is consumed elsewhere (e.g.
  ForsterCutoffPoleConstruction). ~50-100 LOC.

## Total LOC estimate

| Phase | LOC | Sessions |
|---|---|---|
| A (norm bounds on ℂ) | 400-600 | 2-3 |
| B (norm transport to X) | 300-450 | 1-2 |
| C (error + contraction) | 550-850 | 3-5 |
| D (iteration + smoothness) | 500-800 | 3-5 |
| E (final assembly) | 200-350 | 1-2 |
| **Total** | **~1950-3050** | **10-17** |

Higher than the original ~800-1200 estimate in
`ROUTE_5_5C_AUDIT.md`, primarily because:
* Phase A includes Lipschitz/Hölder bound (not just sup-norm) for
  smoothness bootstrap.
* Phase B includes norm transport across the chart cover.
* Phase D's smoothness bootstrap is non-trivial at this mathlib pin
  (no out-of-the-box Schauder/Hölder spaces).

## Open research before Phase D

The smoothness preservation in 5.5c-III-8 is the largest unknown.
Three possible resolutions:

1. **Higher-order Schauder estimates.** Bound `‖∂^k (T α)‖_∞ ≤ c ·
   ‖∂^k α‖_∞ + C_k · ‖α‖_{k-1}` for each `k`. Iterate the geometric
   series at each order independently. Heavy but classical.

2. **Interior regularity.** The Pompeiu integral `pompeiuKernel α` is
   `C^∞` whenever α is `C^∞` (Chip 2d, already proven). The iteration
   composes Pompeiu with smoothing operators that preserve `C^∞`.
   This may suffice without explicit higher-order norm tracking.

3. **L²-Hodge bypass.** If mathlib gains L² Hodge during this arc,
   it gives a direct existence + regularity proof without iteration.
   Not realistic at this pin but worth noting.

Path 2 is the lightest if it goes through. **Plan**: investigate
Path 2 before committing to Path 1's higher-order norm machinery,
at the start of Phase D.

## Reuse from existing infrastructure

* **Pompeiu kernel on ℂ + smoothness**: Chips 1a, 1b, 1c, 2a, 2b,
  2c-prep, 2c-main, 2d (complete, axiom-free, ~1500 LOC).
* **Cauchy-Pompeiu identity on ℂ**: Chip 3c-F-4 (complete,
  axiom-free).
* **Chart-pullback lift + manifold identity**: Chip 4 (complete,
  axiom-free).
* **Cover + partition + cutoff + global candidate**: Sub-chips 5.1,
  5.2, 5.3, 5.4 + assembly layer (complete, ~1700 LOC).
* **Chart-anchored ∂̄ + per-i recovery**: Sub-chips 5.5a + 5.5b
  (complete, ~339 LOC). The per-i recovery is the input to Phase C.
* **OmegaForm record + ofChartLocalFunction constructor**: Sub-chips
  5.5c-I-{a, b family} (complete, ~1140 LOC). **Orphaned** — not
  consumed by Route III, retained as bundle-route infrastructure.

## Mathlib prerequisites — preliminary check

Mathlib (at pin `8e3c989`) has:
* `Continuous.bounded_above_of_compact_support` — for sup-norm on
  compact-support functions.
* `Mathlib.Analysis.Normed.*` — full `NormedSpace` infrastructure.
* `Mathlib.Topology.MetricSpace.Lipschitz` — Lipschitz bounds.
* `Mathlib.Analysis.Calculus.ContDiff.Operations` — `C^k` and `C^∞`
  algebra.
* **No** Hölder spaces as a typeclass (so Phase A's Hölder bound is
  ad-hoc pointwise).
* **No** L²-Hodge / weak derivatives library at this pin.
* **No** Banach fixed-point theorem in the precise form needed
  (it has `ContractingWith.fixedPoint`, which may or may not apply
  to `T` depending on the chosen norm).

Phase C's `ContractingWith` fit is a concrete sub-question for
sub-chip 5.5c-III-6.

## Risk register

| Risk | Severity | Mitigation |
|---|---|---|
| Contraction constant `c ≥ 1` for any cover | high | Cover refinement: use a Lebesgue-number argument to shrink ρ_i supports until the leakage zone is small. Phase C sub-chip's first task. |
| Smoothness bootstrap fails (Phase D) | high | Investigate Path 2 (interior regularity) first; fall back to Path 1 (higher-order Schauder) if needed. |
| Total LOC exceeds 3000 | medium | Break work into smaller chips; if Phase C exceeds budget by >2x, escalate to user for re-evaluation. |
| Hölder bound (5.5c-III-2) not Lipschitz | medium | Acceptable; the iteration tolerates any positive Hölder exponent. |
| The classical Forster Ch.14 argument is non-compact (Stein) and doesn't apply to compact RS | **critical** | TBD — re-read Forster §14 carefully before Phase C. For compact ℂℙ¹, the correct path may be Cousin I / Laurent decomposition on the two-chart annulus, not abstract Behnke-Stein. If so, Phase B/C will be much lighter but specialized to ℂℙ¹. |

The last risk is the most important to resolve. Stop and re-read
Forster §14 before committing significant Phase C LOC.

## Immediate next step

**Sub-chip 5.5c-III-1 — Pompeiu sup-norm bound on ℂ.** Foundational,
self-contained, useful in any iteration path. Start here.
