# jacobian-lean-challenge

> **⚠ Challenge completed externally (2026-06-11).** The full challenge has
> been solved — sorry-free, axiom-clean, conformance-checked against the
> verbatim gist — in [rkirov/jacobian-claude](https://github.com/rkirov/jacobian-claude)
> (AI-produced; ~3.3k LOC of this repo's degree/fibre machinery is part of it,
> credited). A statement-level review from this repo found **no
> misformalization**: see [`EXTERNAL_COMPLETION_REVIEW.md`](EXTERNAL_COMPLETION_REVIEW.md).
> This repo is now **frozen as an independent partial development**
> (14/24 strict-closed); its remaining open walls are closed in the external
> tree.
>
> **Final version (v1.0.0, 2026-06-11):** the tree was debloated for the
> freeze — an import-reachability sweep (`tools/reachability.py`) removed 730
> modules (~110k LOC) of paraphrase chips, parallel routes, and superseded
> scaffolding, keeping the 480 modules reachable from the challenge
> implementation (`Basic.lean`), the Arc-1 L² analysis toolkit, the
> Riemann-sphere end-to-end demo, and the substantive closed towers
> (Cauchy–Pompeiu identity, unconditional residue theorem, étale-primitives
> reverse leg). Every deleted file remains in git history.

A Lean 4 / mathlib formalization in response to Kevin Buzzard's "Jacobians" AI
challenge ([gist](https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9)).
`Basic.lean` signatures use the **v0.4** notation (`𝓘(ℂ, E)`, per Buzzard's
2026-05-21 gist revision — "syntactically identical to v0.3").

The challenge asks for an API for the Jacobian variety of a compact connected
Riemann surface: definitions of `genus`, `Jacobian`, `ofCurve` (Abel–Jacobi),
`pushforward`, `pullback`, `ContMDiff.degree`, plus the structural typeclass
instances and the headline lemmas (`genus_eq_zero_iff_homeo`, `ofCurve_inj`,
holomorphicity of `ofCurve` / `pushforward` / `pullback`, functoriality,
`pushforward_pullback = degree • id`).

## Status

| Category | Count | Items |
|---|---|---|
| **Strict-closed** (real Lean proofs, no `sorry`) | **14 / 24** | 1, 2, 3, 6, 7, 8, 9, 15, 16, 19, 20, 22, 23, 24 |
| Stub (compiles; placeholder body flips with the C3 structural rewire) | 2 | 4, 10 |
| Shipped conditional on a named classical hypothesis (chain proven and compile-verified) | 8 | 5, 11, 12, 13, 14, 17, 18, 21 |

On the concrete `X = RiemannSphere`, every item is unconditionally closed via
the subsingleton route (`Manifold/JacobianRiemannSphereInstances.lean`,
`Topology/Item14ForRiemannSphere.lean`).

### The two open walls

The 8 conditional items reduce to two classical theorems, neither of which is
in mathlib at the pin.

**Item 14** (`genus_eq_zero_iff_homeo`) reduces to
`ExistsMeroSimplePole_GenusZero X` — Forster Theorem 16.9: a compact connected
genus-0 Riemann surface admits a non-constant meromorphic function with a
single simple pole. Equivalent textbook names (any closes Item 14 on abstract
X via in-tree transport): `hSP X` = `ExistsSimplePoleGermAtSomePoint X`,
`DBarSolvabilityAtGenusZero X` + `ChartAtConstantOnSource`,
`RR_DimGE2_GenusZero X`, `Nonempty (HolomorphicEquiv X RiemannSphere)` at
`genus X = 0`. Closure cost across any classical arc (Riemann–Roch + Serre,
Dolbeault / Behnke–Stein, direct uniformization): ~28–50k LOC. See
[`HANDOFF_ITEM14.md`](HANDOFF_ITEM14.md).

**C3 cluster** (items 5, 11, 12, 13, 17, 18, 21) reduces to `C3FullInputExt X`
— bundling Riemann bilinear relations, Abel's theorem, Jacobi inversion,
Abel–Jacobi smoothness, Abel–Jacobi injectivity — plus per-curve
`C3FullInputCurve B_X B_Y f hf` (period-pairing adjunction, for items 18/21).
Closure cost: ~40–60k LOC. See [`HANDOFF_C3.md`](HANDOFF_C3.md).

`Basic.lean` carries comment blocks above each `sorry` documenting the chain,
the named hypothesis the gap reduces to, and file:line citations of every
in-tree unconditional discharge.

## Layout

```
JacobianChallenge.lean          library entry point
JacobianChallenge/
  Basic.lean                    Buzzard's challenge signature
  Analysis/                     Pompeiu kernel, integrability, Cauchy–Pompeiu
  Manifold/                     manifold ∂̄, degree theory, period lattice,
                                AbelJacobi, Hodge scaffolding, etc.
  Topology/                     Item 14 chain, uniformization transport
  Divisor/                      divisor / Pic⁰ infrastructure
HANDOFF_ITEM14.md               Item 14 canonical wall doc + audit
HANDOFF_C3.md                   C3 canonical wall doc + audit
OPEN.md                         per-item status table
REPO_AUDIT.md                   full-repo chain-trace per sorry
DEVELOPMENT.md                  workstation + CI guidance
lakefile.toml                   mathlib pin
lean-toolchain                  Lean version
.github/workflows/              CI
```

The repo contains ~204k LOC across ~1,180 `.lean` files. Most of that is
in-tree analytic scaffolding (Pompeiu kernel, residue theorem on a compact
Riemann surface, manifold ∂̄ operator, degree / ramification theory, period
lattice, path-integral FTC, biholomorphism upgrade lemmas) that is reusable
beyond this challenge.

## Building

CI is the authoritative build (Lean Action CI on push). Local building on
Apple Silicon is constrained by an apfsd kernel-panic risk with `lake build`
and `lake exe cache get`; see [`DEVELOPMENT.md`](DEVELOPMENT.md) for the
recommended workflow.

Single-file elaboration:

```sh
LEAN_NUM_THREADS=1 lake env lean JacobianChallenge/Basic.lean
```

## Mathlib pin

`lakefile.toml` pins mathlib to commit
`8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (15 April 2026), the pin from
Buzzard's v0.3 gist. The pin was not bumped to v0.4's
`548398201a64f3a5127d90d83945278cfe38cac4` (15 May 2026) because Buzzard's
own v0.4 changelog states "v0.4 is syntactically identical to v0.3" — both
notations are definitionally equal, the math content is unchanged, and a
full-repo recompile under the bumped pin is prohibitively expensive without
`lake exe cache get` (apfsd panic constraint). See the pin comment in
`lakefile.toml` for details.

## License

MIT. See [`LICENSE`](LICENSE).
