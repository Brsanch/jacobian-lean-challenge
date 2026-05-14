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

**Current state (2026-05-14):** 12 of 24 items STRICT-CLOSED, 3 STUB, 9 OPEN.
**86,894 LOC** across 416 files. `taskpolicy lake build` clean
(8710 jobs, zero `sorry`, zero `axiom`).

Major recent landings (all on `main`):

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

The remaining 12 items either depend on classical content not at the
mathlib pin (Hodge L² finite-dim, period lattice for genus ≥ 1, surface
classification, Abel–Jacobi at genus ≥ 1) or on the named-hypothesis
inputs above. See `OPEN.md` for the per-item map and `CHANGELOG.md`
for the per-commit history.

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
