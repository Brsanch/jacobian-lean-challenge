# Forster Ch.14 / Dolbeault Lemma — pinned classical structure

**Date**: 2026-05-26.
**Context**: Resolves the **CRITICAL risk** flagged in
[`ROUTE_5_5C_III_PLAN.md`](ROUTE_5_5C_III_PLAN.md): is the classical
proof of `H¹(compact-RS-genus-0, O) = 0` iteration on the surface
itself (Behnke-Stein on X), or something else?

**Finding**: my earlier framing **conflated two distinct ingredients**.
The classical compact-ℂℙ¹ proof uses BOTH:

1. **Behnke-Stein-style iteration on the disk Δ** (or equivalently
   on `ℂ`), to lift the Cauchy-Pompeiu solution for compactly-
   supported `g` to a smooth solution for arbitrary smooth `g` on
   the disk.

2. **Cousin I / Laurent decomposition on the chart overlap `ℂ*`**,
   to glue two disk-level solutions across the two-chart atlas of
   `ℂℙ¹` into a globally smooth solution.

Neither alone discharges `DBarSolvabilityAtGenusZero` on a compact
genus-0 RS. **Iteration on X (without Cousin I) does not appear in
either reference.** My original "Behnke-Stein iteration as Phase
B/C/D/E on `X`" plan was wrong.

## Sources

Two corroborating lecture-note treatments (each follows Forster
*Lectures on Riemann Surfaces*, Ch.12-14):

### McMullen, Berkeley 241/96 — Theorems 7.1, 7.2, 7.5, 7.6

`https://people.math.harvard.edu/~ctm/home/text/class/berkeley/241/96/course/course.pdf`

* **Theorem 7.1 (Pompeiu on `ℂ`)**: For `g ∈ Cc^∞(ℂ)`,
  ```
  f(z) := g ⋆ (1/(πz)) = (1/(2πi)) ∫_ℂ g(w) dw ∧ dw̄ / (z - w)
  ```
  solves `df/dz̄ = g`. **Already proven in this repo as Chip 3c-F-4
  (`partialZBar_pompeiuKernel_eq_self`).**

* **Theorem 7.2 (Dolbeault Lemma on the disk Δ)**: For
  `g ∈ C^∞(Δ)`, there exists `f ∈ C^∞(Δ)` with `df/dz̄ = g`.
  **Proof** (verbatim): write
  `g = Σ_n g_n` where each `g_n` is smooth and compactly supported
  outside the disk `D_n` of radius `1 - 1/n`. Solve `df_n/dz̄ = g_n`
  via Thm 7.1. Then `f_n` is holomorphic on `D_n`. Expanding `f_n`
  in power series, find holomorphic `h_n` on the disk such that
  `|f_n - h_n| < 2^{-n}` on `D_n`. Then
  `f := Σ_n (f_n - h_n) = lim F_N` converges uniformly, and
  `F - F_i` is holomorphic on `D_n` for all `i > n`, so the
  convergence is `C^∞` too.

  **This is the Behnke-Stein iteration**, but on the **disk**, not
  on the compact `X`. The "iteration" is a geometric-series
  convergence after correcting each Pompeiu local solution by a
  polynomial (holomorphic correction) approximating its Taylor
  expansion to within `2^{-n}` on the relevant subdisk.

* **Theorem 7.5**: `H¹(Δ, O) = 0` and `H¹(ℂ, O) = 0`.

* **Corollary 7.6 (`H¹(ℂℙ¹, O) = 0`)**: cover `ℂℙ¹ = U_1 ∪ U_2`
  with `U_1 = ℂ` and `U_2 = ℂℙ¹ - {0}`. `H¹(U_i, O) = 0` by Thm 7.5,
  so by Leray, `H¹(ℂℙ¹, O) = H¹(𝓤, O)` (Čech). A cocycle
  `g_{12} ∈ O(U_1 ∩ U_2) = O(ℂ*)` has Laurent expansion
  `g_{12}(z) = Σ_{n=-∞}^{∞} a_n z^n`. **Split into positive and
  negative parts**:
  - `f_2 := Σ_{n ≥ 0} a_n z^n ∈ O(U_1)` (holomorphic on `ℂ`).
  - `f_1 := -Σ_{n < 0} a_n z^n ∈ O(U_2)` (each `z^{-m}` with `m > 0`
    is polynomial in the `U_2` chart coordinate `w = 1/z`, hence
    holomorphic on `U_2`).
  Then `g_{12} = f_2 - f_1`, so the cocycle is a coboundary, i.e.
  `H¹(ℂℙ¹, O) = 0`.

### Anagol et al., Berkeley 213b — Item 52

`https://math.berkeley.edu/~ianagol/complexriemann.pdf`

Same statement, independent treatment:
> "Example: ℂ̂ = U_1 ∪ U_2 where U_1 = ℂ, U_2 = ℂ̂ - {0} is an
> acyclic covering for O; from Laurent series we see any
> f_{12}(z) ∈ O(U_1 ∩ U_2 = ℂ*) is given by g_1 - g_2, g_i ∈ O(U_i),
> so H¹(ℂ̂, O) = 0."

## What this means for the Lean discharge

The Behnke-Stein iteration the user originally selected is **on the
disk Δ**, not on the compact `X`. The compact-`X` closure step uses
Cousin I / Laurent, which is a **separate ingredient** that my
original plan missed.

### Corrected chip arc

| Phase | Content | Status | LOC |
|---|---|---|---|
| A | Pompeiu kernel on `ℂ` + sup-norm bounds | **DONE** | 356 (5.5c-III-1a + 1b) |
| B | Behnke-Stein iteration on the disk Δ (Forster Thm 14 / Berkeley 7.2): given smooth `g : Δ → ℂ`, build smooth `f : Δ → ℂ` with `∂̄f = g`. Cutoff partition `g = Σ g_n` (each compactly supported in a slightly larger subdisk than `D_n`), per-piece Pompeiu solutions `f_n`, polynomial corrections `h_n` from Taylor series + Schwarz / `2^{-n}` error, geometric-series convergence. | TODO | 600-900 |
| C | Laurent expansion / Cousin I infrastructure: for `f : ℂ* → ℂ` holomorphic, split `f = f_+ + f_-` with `f_+` extending to `ℂ` and `f_-` extending to `ℂℙ¹ \ {0}`. Bounds on the splitting; smoothness; mathlib `Complex.hasFPowerSeriesOnBall` / `HasLaurentSeriesAt` audit. | TODO | 400-600 |
| D | RiemannSphere atlas + assembly. Specialize to the concrete two-chart atlas. Local Pompeiu solutions via Phase B applied to each chart; gluing via Phase C's Laurent decomposition; verify global smoothness. | TODO | 300-500 |
| E | Discharge `DBarSolvabilityAtGenusZero`. **Two options:** (E.1) specialize to `RiemannSphere` and accept the named-hypothesis discharge only for that concrete `X`; (E.2) prove uniformization (or a weaker structure theorem) for `[ChartedSpace ℂ X] [CompactSpace X] [ConnectedSpace X] [genus X = 0]` to reduce abstract `X` to `RiemannSphere`. | TODO | 200-300 (E.1) / **huge** (E.2) |

**Revised total**: ~1500-2300 LOC for Phases B-E.1 (RiemannSphere
specialization).

Phase E.2 (uniformization for abstract genus-0 compact RS) is a
separate mathlib-grade theorem; at this pin it is not feasible in
the chip budget.

### Reuse from existing infrastructure

* **Phase B reuse**: Chips 1-4 (Pompeiu integral, smoothness,
  Cauchy-Pompeiu identity) + Phase A (sup-norm bound) give the
  per-piece local solver. The cutoff partition + polynomial
  correction + geometric series is the new analytic content.

* **Phase C reuse**: mathlib has `Complex.hasFPowerSeriesOnBall`
  for Taylor series; `HasFPowerSeriesOnBall.coeff_eq` etc. The
  Laurent / annulus case is less directly available — a quick
  mathlib audit is needed before Phase C.

* **Phase D reuse**: the repo's `Manifold/RiemannSphere*.lean`
  family already has the two-chart structure (atlas, chart
  transitions, basic properties). The Cousin I assembly itself is
  new.

### Updated risk register

* **Phase B's polynomial correction step** depends on uniform
  approximation of holomorphic `f_n` on `D_n` by polynomials, which
  is standard (truncate the Taylor series; error bounded by tail).
  Mathlib has `Polynomial.taylor` and `HasFPowerSeriesOnBall`-level
  truncation. Should be straightforward.
* **Phase C is the biggest unknown**: mathlib's Laurent / annular
  analytic-function infrastructure at this pin is thin. May need to
  build `HasLaurentSeriesAt` ad-hoc. **Audit before starting Phase C.**
* **Phase E.1 (RiemannSphere specialization) limits the named
  hypothesis discharge** to one concrete `X`. Downstream consumers
  (`ForsterCutoffPoleConstruction`, etc.) take the hypothesis at
  abstract `X` — they would need to specialize too. This is a
  scope-narrowing decision that should be confirmed.

## Decision point

Three concrete forks:

1. **Continue Phase B (Behnke-Stein on the disk)**. Self-contained,
   foundational, classical. ~600-900 LOC. Useful regardless of
   whether the eventual discharge is via Cousin I or some other
   path.

2. **Skip Phase B, attempt direct Pompeiu-on-`ℂ`-with-decay**: for
   `α` smooth on `ℂℙ¹`, in the finite chart `ℂ` the restriction has
   the right decay at `∞` to make `pompeiuKernel α` extend smoothly
   to `∞`. Avoids the cutoff iteration but requires careful decay
   analysis. Might be ~400-600 LOC. **High risk** because the decay
   may not actually hold for arbitrary smooth `α` on `ℂℙ¹` (the
   compact-support assumption on `ℂ` is genuinely needed).

3. **Specialize the named hypothesis to `RiemannSphere` and skip
   abstract `X`**. Reformulate `DBarSolvabilityAtGenusZero` (or
   prove a `RiemannSphere`-specific corollary that the downstream
   chips consume) so the discharge can use the concrete two-chart
   atlas + Laurent decomposition + Phase B's disk solver. Need to
   audit `ForsterCutoffPoleConstruction` to see if it accepts the
   specialization.

Fork 1 is the safe continuation. Fork 3 is the path to actually
closing the named hypothesis (with a scope narrowing). Fork 2 is
risky.
