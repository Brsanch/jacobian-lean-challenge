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

**Current state (2026-05-19 late):** 13 of 24 items STRICT-CLOSED, 2 STUB, 9 OPEN.
Build clean at **9151 jobs** (zero `sorry`, zero `axiom`). Repo:
**153,172 LOC across 866 `.lean` files**.

Major recent landings (all on `main`):

* **`SmoothPathLiftHypothesisTorus L` CLOSED unconditionally on T²**
  (2026-05-19 late, 17 chips, 2,558 LOC). The universal-cover
  smooth-lift content of the SmoothHurewicz reduction chain is now
  unconditional. Every smooth based loop `γ` at `0` on `ℂ ⧸ L`
  admits a smooth ambient lift `Γ : ℝ → ℂ` with `Γ(0) = 0` and
  `mkQ ∘ Γ = γ.ambient` on `Icc 0 1`. Construction: chart-anchor
  Lebesgue partition + cumulative seam-shift `∈ L` + per-piece
  chart-symm composition + local agreement near seams (continuity
  into discrete `L` + `discRadius_separates`) + bump multiplier
  to extend smoothly to `ℝ`. Closes the hardest open atom on the
  reduction chain; remaining genus-1 content is the bordism /
  word-rep identification + the Cauchy-Stokes side.

* **`riemannBilinear` CLOSED on T² + `SmoothHurewicz` arc opened**
  (2026-05-19, 16 chips across two arcs, ~2,300 LOC). End-to-end
  closure of `riemannBilinear` (period computation `∫_{γ_lam} dz =
  lam` via mfderiv-mkQ-is-id + chain rule + integration; ℝ-linear-
  independence via `(Fin 1 → ℂ) ≃ₗ[ℝ] ℂ`). Substantial
  `SmoothHurewicz` infrastructure: `mkQ` is a covering map (via
  mathlib's `AddSubgroup.isAddQuotientCoveringMap_of_comm`),
  continuous lift (`contLift`), named smooth-lift atom
  (`SmoothPathLiftHypothesisTorus`), and chart-based local smooth
  lift (`localLift`) with smoothness + anchor identity. Also closes
  `1 ≤ genus (ℂ ⧸ L)` lower bound via Forster-Riesz + `dz_ne_zero`.
  Net atom closure: **1 full atom + 1 half-atom**.

* **Complex torus `ℂ ⧸ L` infrastructure as the genus-1 example**
  (2026-05-18 late late + 8, 10 chips, ~1,100 LOC). `IsManifold
  𝓘(ℂ, ℂ) ω (ℂ ⧸ L)` instance, symplectic basis, smooth-path-
  connectedness, named Hurewicz hypothesis on T², `H1_spans_top`
  reduction unconditional in α.

* **Smooth-Hurewicz arc completion (genus-≥1 syntactic + chart-local
  geometry)** (2026-05-18 late late + 7, ~4,500 LOC across the session).
  Built the full bordism+word-rep factoring of `SmoothHurewiczHypothesis`,
  discharged the bordism side via concrete geometric construction
  (`smoothBordant_of_smoothHomotopy` — explicit Smooth2Chain whose
  boundary is `single γ₀ - single γ₁`), shipped the straight-line homotopy
  in ℂ + the chart-local generalisation, and closed
  `WordRepresentativeHypothesis` *syntactically* at any genus `g` on RS
  and ℂ via the `constSymplecticBasis` discharge. **Honest caveat:** the
  genus-≥1 syntactic closure uses a degenerate basis (all loops = const);
  the genuinely-non-trivial genus-≥1 statement (basis representing
  H₁-non-trivial classes on a non-simply-connected surface) remains open
  and needs surface-topology infrastructure (T² = ℂ/Λ as a Riemann surface,
  path lifting, cellular approximation) not in tree.

* **Smooth-Hurewicz arc: symplectic basis + commutator
  null-homology** (2026-05-18 late late + 6, 5 chips, ~622 LOC).
  Opens the hardest open atom (`BasedLoopHomologyDecompositionHypothesis`,
  the smooth-Hurewicz content on a genus-`g` surface) with the
  symplectic-basis data structure, the `SmoothHurewiczHypothesis`
  Prop, an `ofSmoothHurewicz` constructor through to the period-lattice
  symplectic bundle, an `RS` validation, and a **real homological
  identity** — `single_commutatorLoop_mem_stokesBoundaries`: the
  commutator `[α, β]` of any two based loops is null-homologous in
  `stokesBoundaries`, the classical "`H₁` is abelian" content
  verified for arbitrary commutator words.

* **Generic genus-≥1 period-lattice: per-based-loop homology +
  complex-valued Stokes consolidation** (2026-05-18 late late + 5,
  6 chips, ~964 LOC). The fourth atomic input
  (`H1_spans_top_canonical`) factors through a per-based-loop homology
  decomposition hypothesis + smooth-path-connectedness; the holomorphic
  side's two real-valued vanishings consolidate into a single
  complex-valued `HolomorphicComplexBoundaryVanishingHypothesis`. The
  most-atomic constructor
  `GenericGenusPeriodLatticeInputs.ofAtomicData` packages the reduced
  data list. The
  fourth atomic input of `GenericGenusPeriodLatticeInputs`
  (`H1_spans_top_canonical`) now factors through a per-based-loop
  homology decomposition hypothesis + smooth-path-connectedness, the
  genuine generalisation of `BasedSmoothLoopsBoundHypothesis` (the
  genus-0 case is the trivial decomposition). Headline
  `H1_spans_top_canonical_of_basedLoopHomology` aggregates the
  per-path decomposition over `c.support` and uses the αShift
  cycle-property cancellation to track an extra
  `∑ Nᵢ • cycleGens i` term alongside the original genus-0 argument.
  Clean-atomic constructor
  `GenericGenusPeriodLatticeInputs.ofBasedLoopHomology` packages the
  reduced atomic data; validated on `RiemannSphere` end-to-end via
  `genericGenusPeriodLatticeInputs_RiemannSphere_via_basedLoopHomology`.

* **Full genus-0 period-lattice closure on `RiemannSphere`,
  unconditional** (2026-05-18 late late + 4, HEAD `419b009`).
  The 4-tuple `GenericGenusPeriodLatticeInputs` on RS is now
  constructible without any classical-input hypothesis. Headline
  `stokesBoundaries 𝓘(ℝ, ℂ) RiemannSphere = ⊤` (in
  `Manifold/StokesBoundariesRiemannSphereTop.lean`) composes the
  Finsupp cycle aggregation `cycle_in_stokesBoundaries_of_basedLoopsBound`
  with the unconditional `basedSmoothLoopsBoundHypothesis_RS_holds`.
  All four atomic inputs of `GenericGenusPeriodLatticeInputs` then
  discharge: `cycleGens` via `IsEmpty.elim`, `riemannBilinear` via
  `linearIndependent_empty_type`, `holomorphicCanonicalClosed` via
  `HolomorphicComponentsCanonicalClosed.of_subsingleton`, and
  `H1_spans_top_canonical` via `Subsingleton.elim` after
  `subsingleton_canonical_H1_of_stokesBoundaries_eq_top` consumes
  `stokesBoundaries_RS_eq_top`.

* **Cotangent-bundle chart-pullback identity proven under frame
  stability** (2026-05-18 late late + 4). The substantive identity
  `α.eval (γ.ambient t) (γ.velocity t)
    = α.localCoeff basePoint (chartPath t) * deriv chartPath t`
  for chart-contained smooth loops is now an in-tree theorem
  (`pointwiseChartEvalIdentity_of_frameStable` in
  `Manifold/PointwiseChartEvalFromFrameStability.lean`).
  Frame stability (`chartAt ℂ (γ.ambient t) = chartAt ℂ basePoint`)
  is automatic on `RS` for `basePoint ≠ ∞`. Composite
  `complexChainPeriod_vanishes_RiemannSphere` (in
  `Manifold/CotangentChartFrameStableRS.lean`) gives **fully
  unconditional per-loop complex-period vanishing** for any
  chart-contained closed loop on RS with basepoint off ∞.

* **`BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) RiemannSphere p₀`
  UNCONDITIONAL** (2026-05-18 late late, HEAD `ce40ac7`). The full
  load-bearing genus-0 input for canonical period-lattice closure
  is now structurally complete: every smooth loop on `RS` at any
  basepoint has its single in `stokesBoundaries`. End-to-end pipeline:

  ```
  smooth loop on RS
    → [Sard via Hausdorff dimH ≤ 1 < 2 = finrank ℝ ℂ]
      misses some point
    → [Möbius `mobiusComposed c` + chart-N pullback via `tubularBump`]
      factors through ℂ as `γ = push f γ'`
    → [V-loop-bounds linear contraction + stokesBoundaries pushforward]
      based loop bounds a smooth 2-chain
    → [loop-rebasing + rebasing] every smooth loop's single ∈ stokesBoundaries
    → [concat-additivity + reverse-cancellation + const-membership +
       cycle-boundary-cancellation]
      every smooth 1-cycle's single ∈ stokesBoundaries
    → stokesBoundaries 𝓘(ℝ, ℂ) RiemannSphere = ⊤
  ```

  ~5,140 LOC across ~30 chips landed 2026-05-18 (concat-additivity
  arc → V-loop-bounds → factorisation pipeline → chart-symm smoothness
  → structural reduction → chart-N pullback discharge → Möbius shift
  → missed-point discharge → capstone). Headline:
  `basedSmoothLoopsBoundHypothesis_RS_holds` in
  `Manifold/StokesBoundariesTopRiemannSphere.lean`.

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
