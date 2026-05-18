# jacobian-lean-challenge

A Lean 4 / mathlib formalization in response to Kevin Buzzard's "Jacobians" AI
challenge ([gist](https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9),
v0.3, 2026-04-15).

The challenge asks for an API for the Jacobian variety of a compact Riemann
surface: definitions of `genus`, `Jacobian`, `ofCurve` (Abel–Jacobi),
`pushforward`, `pullback`, `ContMDiff.degree`, plus the structural typeclass
instances and the headline lemmas (`genus_eq_zero_iff_homeo`, `ofCurve_inj`,
holomorphicity of `ofCurve` / `pushforward` / `pullback`, functoriality,
`pushforward_pullback = degree • id`).

## Status

**Current state (2026-05-18 late):** 13 of 24 items STRICT-CLOSED, 2 STUB, 9 OPEN.
Build clean at **9061 jobs** (zero `sorry`, zero `axiom`). Repo:
**140,066 LOC across 781 `.lean` files**.

Major recent landings (all on `main`):

* **`stokesBoundaries 𝓘(ℝ, ℂ) RS = ⊤` reduced to ONE atomic input**
  (2026-05-18 late, 22-chip arc, ~4,350 LOC, HEAD `9e1fe1a`).
  Full concat-additivity in stokesBoundaries (no integration-side
  approximation), rebasing + loop-rebasing identities, V-loop-bounds
  unconditional on any normed ℝ-vector space, stokesBoundaries
  pushforward, and the structural reduction
  `LoopFactorsThroughVectorSpaceHypothesis ℂ RiemannSphere p₀` —
  every smooth loop on RS factors through ℂ via a smooth chart-style
  map. Two named sub-hypotheses (`SmoothLoopAvoidsInftyHypothesis`
  + `SmoothLoopChartNPullbackExistsHypothesis`) jointly discharge
  it via the chart-N inverse smoothness
  (`chartN_symm_contMDiff`, `chartS_symm_contMDiff`).

* **A1 + A2 closed unconditionally** — the two RS-side classical inputs
  of the genus-0 Riemann–Roch chain (`LinearSystemAtInftyRS_BoundedBySimplePoleSpan`
  via polynomial-growth Liouville at ∞; `ExistsMobiusToInftyRS` via
  antipode + translation as `HolomorphicEquiv RS RS`).
* **`Pic⁰(ℙ¹) = 0` unconditional in-tree** — every degree-zero divisor
  on the Riemann sphere is principal. Headline:
  `AbelJacobiInput.abelJacobiEquiv_of_RiemannSphere_unconditional`
  gives `Pic⁰ RS ≃+ AnalyticJacobian RS` axiom-free.
* **C3 + C4 reduced to atomic textbook hypotheses at general genus** —
  `AbelHypothesis B` factors through `AbelGeneratorPeriodCondition B`
  (per meromorphic function); `JacobiInversion` at genus 0 reduces to
  `Subsingleton (Pic0 X)`.
* **`SimplyConnectedS2` UNCONDITIONAL** (2026-05-15, 15-chip
  polygonal-approximation arc, capstone in
  `Topology/SimplyConnectedS2Unconditional.lean`) — the mathlib gap
  `SimplyConnectedSpace JacobianChallenge.StandardS2` is closed via a
  two-chart stereographic cover + `lebesgue_number_lemma` partition +
  canonical `stereographicStraightLine` per piece + Baire-style finite
  union of nowhere-dense ranges. Reduces the simple-connectedness
  route for item 14's reverse leg from two named classical inputs to
  one (the Stokes + Liouville analytic chain
  `HolomorphicOneFormSubsingletonOfSimplyConnected X`).
* **Hodge finite-dim Forster scaffolding** (2026-05-17, 16 chips,
  +2,948 LOC) — `HolomorphicOneFormFiniteDim X` proof reduced to two
  remaining steps: seminorm convergence (inner-disk uniform → outer-
  disk seminorm via multi-chart density bound) and Riesz application
  via `FiniteDimensional.of_isCompact_closedBall₀`.
* **`RegularLevelSetLatticeClause` discharge — algebraic side
  complete** (2026-05-17 evening, 19 chips, ~3,460 LOC). Three waves:
  (i) per-`t` trace identity at sub-interval (6 chips); (ii) full
  eventually-form composition near `t = 0` (6 chips); (iii)
  **lifted-point chain rule + global integrand-trace integral
  identity** (8 chips). The lifted-point breakthrough — sheets
  centered at the lifted point `q := extend t₀ p` automatically
  satisfy the sub-interval condition — bypasses Hurwitz subdivision
  entirely. Headline now in tree:
  ```
  SmoothChain.integrate (levelSetChain f β) om
    = ∫ t in 0..1, derivσ(t) *
        applyCotangent (traceAt … (β(σ t)) om) (mfderiv β (σ t) 1)
  ```
  Remaining for full clause discharge: σ-reparametrisation,
  `f_*ω` smooth-on-`regularValueSet` packaging, residue theorem
  adaptation `principalDivisorMap → f_*ω` on ℙ¹.

The remaining 12 items either depend on classical content not at the
mathlib pin (Hodge L² finite-dim, period lattice for genus ≥ 1, surface
classification for item 14's forward leg, Abel–Jacobi at genus ≥ 1) or
on the named-hypothesis inputs above. See `OPEN.md` for the per-item
map, `CLOSURE_MAP.md` §D.2.6 for the SimplyConnectedS2 arc, and
`CHANGELOG.md` for the per-commit history.

## Layout

```
JacobianChallenge.lean          -- library entry point
JacobianChallenge/
  Basic.lean                    -- Buzzard's challenge signature, verbatim
  ...                           -- additional modules added as content lands
lakefile.toml                   -- mathlib pinned to commit 8e3c989...
lean-toolchain                  -- v4.30.0-rc1
.github/workflows/              -- CI (lean-action, release-on-toolchain, mathlib update)
DEVELOPMENT.md                  -- workstation rules + CI-as-default workflow
OPEN.md                         -- sorry inventory mapped to challenge items
```

## Building

This project is developed with **CI as the authoritative build**. See
`DEVELOPMENT.md` for the full rationale (apfsd kernel-panic mitigation on
Apple Silicon) and the recommended workflow. In short: do not run
`lake build` locally on a Mac; push to GitHub and read the CI log.

For single-file no-write elaboration on a Linux box or a Mac that you're
willing to risk:

```sh
LEAN_NUM_THREADS=1 lake env lean JacobianChallenge/Basic.lean
```

## Mathlib pin

The `lakefile.toml` pins mathlib to commit
`8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (15 April 2026), as required by
Buzzard's challenge v0.3. Do not bump this without a corresponding bump in
the challenge file's compatibility line.

## License

MIT. See `LICENSE`.
