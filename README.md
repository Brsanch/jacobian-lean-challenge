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

Initial scaffold (v0.1.0). All challenge items are `sorry`. See `OPEN.md` for
the current open list and `CHANGELOG.md` for the sequence of closures.

## Layout

```
JacobianChallenge.lean          -- library entry point
JacobianChallenge/
  Basic.lean                    -- Buzzard's challenge signature, verbatim
  ...                           -- additional modules added as content lands
lakefile.toml                   -- mathlib pinned to commit 8e3c989...
lean-toolchain                  -- v4.29.0
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
