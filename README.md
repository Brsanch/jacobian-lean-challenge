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

**Current state (2026-05-22):** 14 of 24 items STRICT-CLOSED, 2 STUB, 8 OPEN.
Zero `sorry`, zero `axiom`. Repo:
**196,786 LOC across 1,237 `.lean` files**. Full-graph build: **9,495 jobs**.

Major recent landings:

* **Hodge–Riemann bridge reduction arc — bridge identity factored into `g(g+1)/2` scalar pairing identities; C3 wave's universal classical content at general genus reduced to `(SCD + g² scalar identities)`** (2026-05-22 continuation+1, 29 feat commits + 2 docs commits, +2,733 LOC across 29 new files + 3 manifest/docs edits, branch `feat/c3-surface-classification-data`, HEAD `479c853`, pushed). At general genus on every compact connected complex 1-manifold:
  - the matrix bridge identity for `J = standardSymplectic g` reduces to `g(g+1)/2` upper-triangular entries via Hermitian symmetry of both sides;
  - via the new period sesquilinear form `Q_sq cycleGens J ω₀ ω₁ := ∑ k l, J_{k,l} · P(γ_k, ω₀) · star(P(γ_l, ω₁))` (with full sesquilinearity + anti-Hermitian symmetry properties), the bridge identity is equivalent to a finite family of scalar pairing identities `I · Q_sq(basis_ω i, basis_ω j) = H(basis_ω i, basis_ω j)` for `i ≤ j`;
  - at genus 1 it collapses to a single scalar equation (the fundamental Riemann area identity `H(ω₀, ω₀) = 2 · Im(star pm[k₀,i₀] · pm[k₁,i₀])`);
  - the C3 wave's universal classical content at general genus reduces to `(SCD + g(g − 1)/2 strict-upper Q vanishing + g(g + 1)/2 upper-tri Petersson sesquilinear pairings)`. End-to-end constructors shipped for `HasC3FullClassicalContent`, `HasJacobianAnalyticStructure`, and `HasJacobianHodgeChain` at the three input layouts (general genus / genus 0 / genus 1), plus a new `HasJacobianClassicalContent X` typeclass with unconditional RS instance, bridge to HJAS, and `inferInstance` smoke tests. No items flip — items 5/11/12/13/17/18/21 still require the universal HJAS instance whose remaining content is now the `g(g+1)/2` open sesquilinear pairing identities + SCD.
* **Chip S.8 unconditional + `HodgeInnerProductHypothesis`
  unconditional + Riemann second relation + Complete Hodge–Riemann
  at genus 0** (2026-05-22 continuation, 8 feat commits, +1,246
  LOC across 9 new files, branch `feat/c3-surface-classification-data`).
  Closes the four outstanding items of the arc-S programme.
  **Closed unconditionally on every compact connected complex
  1-manifold (every genus)**: `HodgeInnerProductHypothesis X` — the
  Hodge inner product on `H⁰(X, Ω)` is no longer a named hypothesis
  but an in-tree theorem, witness `globalPettersonHermitianForm X`
  packaged from the partition-of-unity Petersson L² inner product
  (linearity via `mul_finsum` + `integral_const_mul` +
  `finsum_add_distrib`; positive-definiteness via S.3 + S.6 + the
  strict-positivity S.8 just shipped). **Closed unconditionally at
  genus 0**: `RiemannBilinearFirstRelation` and
  `HodgeRiemannBridgeHypothesis` (extensionality on 0×0 matrices),
  `RiemannBilinearSecondRelation`, `CompleteHodgeRiemannHypothesis`
  (both via the vacuous Subsingleton-ω route already in tree and via
  a new non-vacuous Petersson-form route). The bridge identity at
  genus ≥ 1 (wedge product + Stokes + cup-product) remains open
  classical content; combined with the in-tree genus-0
  `SmoothSymplecticBasis` / `SmoothHurewiczHypothesis` discharges,
  **the entire Hodge-positivity chain is in tree at genus 0**.
* **L²-positivity arc COMPLETE for `HolomorphicOneForm` + ℂ→ℝ
  ContDiff diamond closed + Petersson Hermitian form positive
  semi-definite at the diagonal (arc S chips S.1–S.7')** (2026-05-22,
  19 feat commits + 1 docs commit, +2,190 LOC across 17 new files,
  branch `feat/c3-surface-classification-data`). Ships the
  partition-of-unity Petersson L²-square norm
  `globalPettersonL2Sq om f` and the headline
  `globalPettersonL2Sq_pos_of_ne_zero` — for every nonzero holomorphic
  1-form `om` on any compact connected complex 1-manifold and every
  smooth partition of unity `f` subordinate to the chart-source cover,
  `0 < globalPettersonL2Sq om f`. Composes 11 chips A → E.4 (chart-
  local L²-square seminorm, finiteness, real-valued projection,
  finite chart cover, smooth PoU, weighted seminorm, global PoU sum,
  non-vanishing existence at chart-image, non-vanishing ball,
  positive seminorm on ball, generalised non-vanishing localCoeff,
  finsum assembly via `LocallyFinite.finite_nonempty_of_compact`).
  Plus the memory-flagged `IsManifold (𝓘(ℝ, ℂ)) ∞ X` instance from
  `[IsManifold (𝓘(ℂ, ℂ)) ω X]`, dispatching the ℂ→ℝ ContDiff diamond
  via `set_option backward.isDefEq.respectTransparency false` (the
  trick mathlib uses for `StarModule.complexToReal`). Plus arc S
  chips S.1–S.7' (ℂ-valued chart-local + global Petersson Hermitian
  sesquilinear pairing via Bochner integration; Hermitian symmetry;
  diagonal real and nonneg via Hermitian symmetry + `Complex.mul_conj`
  + `integral_complex_ofReal` + `Complex.reCLM.toAddMonoidHom.map_finsum`).
  Plus the shared C3↔Item-14 atom `UniformizationGenus0Hypothesis X`
  (Topology/…), with unconditional RS instance and a substantive
  `of_RiemannRochGenusZero` discharge.
* **Chip 19q-r + chip 20a-r: T_L unconditional Hodge–Riemann +
  general-genus structural reductions** (2026-05-21, 23 commits,
  +2,015 LOC across 22 new files, branch
  `feat/c3-chip-19-iperiodform-hermitian` continuing the chip 19
  arc). *T_L:* `HasJacobianHodgeChain (ℂ ⧸ L)` is now a typeclass
  instance (chip 19q biconditional `ℝ-LI ![a, b] ⟺ Im(star a · b) ≠ 0`
  composed with `basisFin2OfL_realLinearIndependent` and orientation
  by-cases). `CompleteHodgeRiemannHypothesis`,
  `RiemannBilinearRelations`, ℝ-LI of period vectors, and the first
  relation are all UNCONDITIONAL on T_L. Explicit period matrix
  entries: `(0, 0) = lam₁`, `(1, 0) = lam₂`. *Universal genus 0:*
  CHRH + RBR + ℝ-LI of period vectors UNCONDITIONAL on every compact
  connected complex 1-manifold with `genus X = 0` via
  `DiskChartCover.holomorphicOneFormFiniteDim_holds` +
  `holomorphicOneForm_subsingleton_of_genus_eq_zero` +
  `completeHodgeRiemannHypothesis_of_subsingleton`. *General genus:*
  diagonal of `pmatᵀ · J.cast · pmat` vanishes from anti-sym `J`;
  first relation ⟺ strict-upper-triangular vanishing; second relation
  reduces to positivity (Hermitian conjunct automatic). At `g = 2`
  reduces to a single scalar equation `N 0 1 = 0` + 2 × 2 Hermitian
  PD. Per-genus picture for CHRH: `g = 0` vacuous, `g = 1` one
  diagonal positivity, `g = 2` one scalar zero + 2 × 2 PD, `g ≥ 3`
  `g(g − 1)/2` scalar zeros + `g × g` PD. *No items flip* — the same
  `[HasJacobianAnalyticStructure X]` universality blocker remains.

* **Chip 19 arc: Hodge–Riemann second-relation full reduction**
  (2026-05-20, 16 commits, +1,616 LOC across 16 new files, branch
  `feat/c3-chip-19-iperiodform-hermitian`). Structurally closes the
  Hodge–Riemann second bilinear bundle. Reduces
  `CompleteHodgeRiemannHypothesis` from a 5-named-hypothesis bundle
  `(J, H, IsPositiveDefinite, first, bridge)` to
  **(anti-sym `J` + first relation + matrix positivity)** — the Hodge
  form choice and the bridge identity are both eliminated as separate
  atoms via `canonicalHodgeFormFromAntiSymm` +
  `hodgeFormFromMatrix_toMatrix`. At genus 1, reduces further to a
  SINGLE scalar inequality on the period matrix's diagonal. Validates
  the chain on `T_L = ℂ ⧸ L` end-to-end:
  `HasJacobianHodgeChain (ℂ ⧸ L)` from a single
  `0 < Im(star lam₁ · lam₂)` input on the explicit in-tree basis. Key
  artifacts: `PeriodMatrixAntiHermitian` (`iPeriodMatrixForm_isHermitian`),
  `HodgeFormFromMatrix` (`hodgeFormFromMatrix` + `toMatrix` recovery),
  `HodgeFormFromPeriodMatrix[PD]` (canonical Hodge form, bridge
  automatic, PD bridge), `CompleteHodgeRiemannFromAntiSymm`,
  `CompleteHodgeRiemannFromStandardSymplectic`,
  `RiemannBilinearMatrixPosGenusOne` (genus-1 quadratic-form collapse),
  `PeriodMatrixFormStandardSymplecticOne[Symbolic]` (closed-form
  diagonal `(2 · Im(star (pm 0 0) · pm 1 0) : ℂ)`),
  `CompleteHodgeRiemannGenusOneOrientation`,
  `CompleteHodgeRiemannComplexTorus`,
  `HasJacobianHodgeChainComplexTorus[FromOrientation/Swap/FromNonzero]`.
  *No items flip* — this is a structural reduction of the named
  classical content required by the items 5/11/12/13/17/18/21 chain.

* **Period-lattice plumbing + classical-content scaffolding + item-14
  advances** (2026-05-20 late, two arcs, 35 commits + merge,
  ~3,778 LOC across 34 new files, HEAD `ce776c9`). *No items flipped*
  — work is foundational plumbing + named classical hypotheses; items
  5/11/12/13/17/18/21 are now reducible to a single class hypothesis
  `[HasJacobianAnalyticStructure X]` once it lands universally. **Arc
  A** (period-lattice + classical, ~2,200 LOC): class-keyed
  `CanonicalAnalyticJacobian` chain with 7 instances per X
  (Compact/Charted/IsManifold/LieAddGroup on the analytic Jacobian
  Type); basis-anonymous `HasJacobianAnalyticStructure X` class + RS
  + T_L instances; `CanonicalOfCurve` with self-vanishing +
  smoothness/constancy at genus 0; canonical pushforward/pullback
  lifts + smoothness corollaries; RS + T_L smoke tests confirming
  end-to-end composition; classical scaffolding via
  `HodgeInnerProductHypothesis`, `HodgeFormMatrix`, `PeriodMatrix`,
  `RiemannBilinearRelations` (first + second + bundled),
  `RiemannBilinearImpliesLI` (genus-0 discharge),
  `StandardSymplecticForm` (anti-symmetry `J^T = -J` proven),
  `HodgeRiemannBridge` (the deep identity `i Π^T J Π̄ = H.toMatrix`,
  Hermitian half proven). **Arc B** (item 14, ~1,580 LOC):
  `ChartLocalPrimitiveExtend` + ContMDiff/mfderiv/Continuous transfer
  theorems; global `pathPrimitive ContMDiff` + FTC via
  `PathPrimitiveAdmissibleChartCover`; `S2ImpliesGenus0` from BSLB +
  admissibility; **unconditional item-14 biconditional on `RiemannSphere`**;
  `HasAdmissibleChartCover` + `HasConvexTargetChartCover` typeclasses
  with class-driven compositions and automatic admissibility under
  Subsingleton ω.

* **Full T_L period-lattice closure + `ℂ⧸L ≃ₘ AnalyticJacobianSymp`
  smooth diffeomorphism UNCONDITIONAL** (2026-05-19 late++++++, 20
  chips, ~3,037 LOC). End-to-end closure of the period-lattice /
  Abel-Jacobi infrastructure on the complex torus. `Nonempty
  (PeriodLatticeSymplecticBundle … T_L)` unconditional via
  `SmoothSymplecticBasis.reindex`; explicit AJ point formula
  `abelJacobiPoint Q = mk (fun _ => Q.out)`; full lattice
  characterization `periodLatticeImage = {fun _ => z : z ∈ L}`; two
  classical hypotheses CLOSED unconditional (`AbelJacobiInjective`,
  `AbelJacobiSmoothness`); `AbelHypothesis` reduced to T_L-level
  `TLDivSumHypothesis` (Abel's elliptic theorem) and
  `JacobiInversion.injective` reduced to `TLAbelConverseHypothesis`
  (Weierstrass σ existence); `JacobiInversion.surjective` conditional
  on `AbelHypothesis`. Headline `abelJacobiPointDiffeomorph` packages
  ℂ⧸L ≃ₘ AnalyticJacobianSymp as a mathlib `Diffeomorph` —
  UNCONDITIONAL.

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
