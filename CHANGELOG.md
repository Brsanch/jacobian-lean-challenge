# Changelog

## 2026-05-18 (late late + 8) — Complex torus `ℂ ⧸ L` infrastructure as the genus-1 example (10 chips, ~1,100 LOC)

Opens the "T² as a Riemann surface" gap called out in the prior
session's caveat. `ℂ ⧸ L` is now in tree as a concrete complex
1-manifold (`IsManifold 𝓘(ℂ, ℂ) ω` instance), with an explicit
symplectic basis of two torus loops parameterised by lattice elements,
unconditional smooth-path-connectedness data, and the full reduction
of `H1_spans_top_canonical` in the canonical Stokes quotient against a
single named Hurewicz hypothesis on the torus.

The smooth-Hurewicz content (universal-cover lifting `ℂ → ℂ ⧸ L`),
the `riemannBilinear` non-degeneracy, and the `holomorphicCanonicalClosed`
chart-pullback Cauchy step remain as genuinely-classical open atoms;
the in-tree framework now consumes them directly.

### Smooth-homotopy Hurewicz abstraction

* `Manifold/SmoothHomotopyHurewiczHypothesis.lean` (~90 LOC) — the
  predicate `SmoothHomotopyHurewiczHypothesis sb : Prop` saying every
  smooth based loop at `p₀` admits a *concrete smooth homotopy* to a
  `basisProductLoop sb n` for some integer tuple `n`. Strictly
  stronger than `WordRepresentativeHypothesis sb`. Routes through
  `smoothBordant_of_smoothHomotopy` to give the bordism downgrade and
  then through `smoothHurewiczHypothesis_of_wordRepresentative` to
  give `SmoothHurewiczHypothesis sb`.

* `Manifold/SmoothHomotopyHurewiczC.lean` (~65 LOC) — discharge of
  the smooth-homotopy version on `ℂ` for `constSymplecticBasis` via
  the straight-line homotopy. Same degenerate-basis caveat as
  `WordRepresentativeAnyGenus.lean`.

### Complex torus as a complex 1-manifold

* `Manifold/PeriodLatticeComplexQuotientGeneric.lean` (~165 LOC) —
  generic `IsManifold 𝓘(ℂ, E) ω (E ⧸ L)` for any finite-dim complex
  normed `E` and discrete full-rank `ℤ`-lattice `L ≤ E`. Stated as a
  `def` (not `instance`) to avoid diamond conflict with the existing
  `Fin g → ℂ` instance.

* `Manifold/ComplexTorus.lean` (~165 LOC) — specialises to `E = ℂ`,
  yielding `IsManifold 𝓘(ℂ, ℂ) ω (ℂ ⧸ L)` as a regular Lean
  instance. Also derives `mkQ_contMDiff` (both complex and real
  models) — the quotient projection `ℂ → ℂ ⧸ L` is smooth via the
  chart-symm-of-maximal-atlas argument.

### Symplectic basis and per-loop primitives

* `Manifold/ComplexTorusBasisLoop.lean` (~115 LOC) — for any lattice
  element `lam ∈ L`, the smooth based loop
  `torusBasisLoop lam hlam : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)` defined by
  `t ↦ π((t : ℂ) * lam)`, both endpoints at the zero class.

* `Manifold/ComplexTorusSymplecticBasis.lean` (~95 LOC) — bundles a
  pair of torus basis loops as
  `SmoothSymplecticBasis 𝓘(ℝ, ℂ) (ℂ ⧸ L) 0 1`. The data side of the
  genus-1 symplectic basis is now unconditionally in tree.

### Pushforward + path-connectedness

* `Manifold/BasedLoopAtPush.lean` (~60 LOC) — pushforward of
  `BasedLoopAt I X p₀` along any smooth `f : X → Y`, producing
  `BasedLoopAt I Y (f p₀)`. Primary intended use is `f := mkQ`
  for "lift in ℂ, project to T²" Hurewicz constructions.

* `Manifold/ComplexTorusPathConnected.lean` (~95 LOC) —
  **unconditional** smooth-path-connectedness data
  `α : (ℂ ⧸ L) → SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)` from `0` to `x`
  parameterised by `t ↦ π((t : ℂ) * x.out)` (using `Quotient.out_eq`).
  Discharges the `(α, h_α_src, h_α_tgt)` ingredient.

### Named Hurewicz hypothesis + headline

* `Manifold/ComplexTorusPeriodLatticeInputs.lean` (~95 LOC) —
  surfaces named atoms `SmoothHurewiczHypothesisTorus` and the
  smooth-homotopy stronger sibling, plus the structural reduction to
  `BasedLoopHomologyDecompositionHypothesis sb.cycleGens 0`.

* `Manifold/ComplexTorusH1SpansTop.lean` (~75 LOC) — **headline**:
  `SmoothHurewiczHypothesisTorus L lam₁ lam₂ ⟹ H1_spans_top_canonical`
  on `(symplecticBasis L lam₁ lam₂).cycleGens` in the canonical
  Stokes quotient, **unconditional in α**.

### Atomic-input status on the torus

After this session, the four atomic inputs of
`GenericGenusPeriodLatticeInputs` on `X := ℂ ⧸ L` reduce to:

| Atom | Status on `T_L = ℂ ⧸ L` |
|---|---|
| `cycleGens` | Unconditional in tree |
| `H1_spans_top_canonical` | Reduces to one named atom (`SmoothHurewiczHypothesisTorus`) |
| smooth-path-connectedness | Unconditional in tree |
| `holomorphicCanonicalClosed` | Open — chart-pullback Cauchy |
| `riemannBilinear` | Open — Hodge theory |
| `genus (ℂ ⧸ L) = 1` | Open — Hodge identification |
| `SmoothHurewiczHypothesisTorus` | Open — universal-cover lifting |

Three substantive classical-content atoms remain; the rest is in tree.

Build **9119 jobs** clean, **148,333 LOC across 834 `.lean` files**.
Zero `sorry`, zero `axiom`. Scoreboard unchanged at 13/24.

## 2026-05-18 (late late + 7) — Smooth-Hurewicz arc continuation (10 chips, ~2,900 LOC)

Continuation of the smooth-Hurewicz arc beyond the symplectic-basis +
commutator-null-homology base from session 6. Built the bordism +
word-rep factoring, discharged the bordism side via concrete geometric
construction, and shipped chart-local + ℂ-specific homotopy primitives.
Closes `WordRepresentativeHypothesis` syntactically at any genus `g` on
RiemannSphere and ℂ.

* `Manifold/SmoothBordismAndWordRepresentative.lean` (~255 LOC) —
  factor `SmoothHurewiczHypothesis sb` into `SmoothBordant` predicate
  + `WordRepresentativeHypothesis sb` (every loop bordant to a
  canonical `basisProductLoop sb n`). Headline implication
  `smoothHurewiczHypothesis_of_wordRepresentative`.

* `Manifold/SmoothBordantOfSmoothHomotopy.lean` (~558 LOC) — **real
  geometric content**. Given a `SmoothHomotopyBasedLoop γ₀ γ₁`
  (smooth `H : ℝ² → X` with the four edge conditions), construct
  `SmoothBordant γ₀ γ₁`. Decomposes the unit square into two standard
  2-simplices via the diagonal, identifies their 6 faces (γ₀, γ₁,
  diagonal D, const p₀ — with D cancelling), shows the 2-chain boundary
  equals `single γ₁ - single γ₀ + 2 · single (const p₀)` mod stokes,
  subtracts the `2 · single const` (in stokes already). Closes the
  bordism side of the factoring **unconditionally** given the homotopy
  data.

* `Manifold/WordRepresentativeEmptyBasis.lean` (~150 LOC) — discharge
  `WordRepresentativeHypothesis (emptySymplecticBasis p₀)` (genus 0)
  from `BasedSmoothLoopsBoundHypothesis`. Unconditional on RS.

* `Manifold/SmoothHomotopyStraightLineC.lean` (~198 LOC) —
  straight-line interpolation in `ℂ`: `H(s, t) := (1-s) · γ₀.amb(t) +
  s · γ₁.amb(t)`. Concrete construction of a `SmoothHomotopyBasedLoop`
  for any two based loops in `ℂ` at the same point. Corollary
  `smoothBordant_straightLineC` gives bordism on ℂ.

* `Manifold/BasedSmoothLoopsBoundC.lean` (~129 LOC) — end-to-end:
  straight-line homotopy → bordism to const → `BasedSmoothLoopsBound`
  on ℂ unconditionally. Composed through to empty-basis
  `WordRepresentativeHypothesis` and `SmoothHurewiczHypothesis` on ℂ.

* `Manifold/SmoothBordantCongruence.lean` (~166 LOC) — `SmoothBordant`
  is preserved by `concat` and `zpow`. Real algebraic congruences via
  concat-additivity + ℤ-power identity + abelian-group manipulation
  in `stokesBoundaries`.

* `Manifold/SmoothHomotopyChartLocal.lean` (~284 LOC) — **real
  geometric content**. Chart-local straight-line homotopy on a complex
  1-manifold `X`: given two based loops at `p₀` with the strong
  hypotheses (both ambients globally land in `(chartAt ℂ p₀).source`,
  chart-straight-line globally lands in `(chartAt ℂ p₀).target`),
  construct `SmoothHomotopyBasedLoop` via `ψ.symm ∘ straightLine ∘ ψ`.
  Uses `contMDiffOn_chart` + `contMDiffOn_chart_symm` +
  `ContMDiffOn.comp_contMDiff` to handle the chart smoothness. Strong
  hypotheses restrict applicability (need bump-extension to weaken).

* `Manifold/WordRepresentativeAnyGenus.lean` (~214 LOC) — closes
  `WordRepresentativeHypothesis sb` for `sb := constSymplecticBasis
  p₀ g` (all-constant basis) at any `g ≥ 1` on any X with
  `BasedSmoothLoopsBound`. Unconditional on RS and ℂ. **Honest
  caveat:** this is syntactic closure with a degenerate basis whose
  `cycleGens` are all in `stokesBoundaries` already. The genuine
  mathematical content at genus ≥ 1 (basis with H₁-non-trivial
  generators on a non-simply-connected manifold) requires
  surface-topology infrastructure not in tree.

**Honest scoreboard:**
* `SmoothBordant` predicate + reflexive/symmetric/transitive: closed.
* `smoothBordant_of_smoothHomotopy`: closed unconditionally (real
  geometry).
* `SmoothBordant.concat`, `SmoothBordant.zpow`: closed.
* Straight-line homotopy in ℂ: closed (real construction).
* Chart-local straight-line homotopy on X under strong hypotheses:
  closed (real construction).
* `BasedSmoothLoopsBound` on ℂ: closed unconditionally.
* `WordRepresentativeHypothesis sb` for `sb = empty` or `sb =
  constSymplecticBasis`: closed (syntactic).
* `SmoothHurewiczHypothesis` for the same `sb` choices on RS and ℂ:
  closed.

**Honest open:**
* `WordRepresentativeHypothesis sb` for a non-degenerate `sb` (basis
  representing H₁-non-trivial classes on a genus-≥1 manifold): open.
* The whole arc is gated on constructing genus-≥1 Riemann surfaces
  (T² = ℂ/Λ as a Riemann surface, hyperelliptic curves, etc.) and
  cellular-approximation infrastructure.

Repo state: **147,252 LOC across 824 `.lean` files**, build **9109
jobs** clean (zero `sorry`, zero `axiom`). Scoreboard unchanged at
13/24.

## 2026-05-18 (late late + 6) — Smooth-Hurewicz arc: symplectic basis + commutator null-homology (5 chips, ~622 LOC)

Begins the hardest open atom — `BasedLoopHomologyDecompositionHypothesis`
(smooth-Hurewicz on a genus-`g` surface) — by introducing the
symplectic-basis data structure, the smooth-Hurewicz hypothesis as a
named Prop, an `ofSmoothHurewicz` constructor wiring through to the
period-lattice symplectic bundle, a `RiemannSphere` validation, and a
real homological identity (the commutator of two based loops is
null-homologous in `stokesBoundaries`).

* `Manifold/SmoothSymplecticBasis.lean` (~84 LOC) —
  `SmoothSymplecticBasis I X p₀ g`: data of `2g` smooth based loops at
  `p₀` representing the standard symplectic homology basis. Carries
  only the loops; `SmoothSymplecticBasis.cycleGens` derives the
  corresponding `Fin (2g) → SmoothCycle I X` tuple via
  `single_smoothLoop_smoothCycle`.

* `Manifold/SmoothHurewiczHypothesis.lean` (~103 LOC) —
  `SmoothHurewiczHypothesis sb`: the classical smooth-Hurewicz content
  as a single named Prop. Every smooth based loop's `single`
  decomposes as a ℤ-combination of basis-loop singles modulo
  `stokesBoundaries`. Biconditional with
  `BasedLoopHomologyDecompositionHypothesis sb.cycleGens p₀`
  (extensionally identical predicates).

* `Manifold/GenericGenusPeriodLatticeInputsFromSmoothHurewicz.lean`
  (~95 LOC) — `GenericGenusPeriodLatticeInputs.ofSmoothHurewicz`
  constructor: builds the inputs structure from a symplectic basis +
  smooth-Hurewicz + the other 3 atomic inputs. `Nonempty` composition
  through to `PeriodLatticeSymplecticBundle`.

* `Manifold/SmoothHurewiczHypothesisRiemannSphere.lean` (~86 LOC) —
  validation chip. At genus 0 on `RS`, the empty symplectic basis
  (`Fin (2*0) = Fin 0`) discharges `SmoothHurewiczHypothesis`
  unconditionally via `basedSmoothLoopsBoundHypothesis_RS_holds`
  applied with all coefficients 0.

* `Manifold/CommutatorOfBasedLoopsNullHomologous.lean` (~254 LOC) —
  **a real homological identity**: for any two smooth based loops
  `α, β` at a common basepoint `p₀ : X`, the **commutator path**
  `[α, β] := α ⋆ β ⋆ α⁻¹ ⋆ β⁻¹` is also a based loop at `p₀`, and
  `single ([α, β]) ∈ stokesBoundaries`. Classical content: `H₁` is
  abelian. Proof composes
  `concat_additive_in_stokesBoundaries` (3 nested applications) +
  `single_smoothPath_plus_reverse_mem_stokesBoundaries` (2 reverse
  cancellations), then `abel` collapses the chain-level equality.
  Also ships `single_inverseConcatLoop_mem_stokesBoundaries` (the
  inverse-pair `α ⋆ α⁻¹` is null-homologous, the simpler
  specialization).

**Significance.** The commutator-null-homology lemma is the first
concrete homological identity in the smooth-Hurewicz framework: it
confirms that the algebraic relations of `π₁` (the commutator) vanish
in `H₁ = π₁^{ab}` at the smooth-singular level on `X`. The next
direction (multi-session) is to prove that **every** smooth based loop
is null-homologous up to a ℤ-combination of basis-loop classes — the
full smooth-Hurewicz statement.

Repo state: **144,344 LOC across 812 `.lean` files**, build **9097
jobs** clean (zero `sorry`, zero `axiom`). Scoreboard unchanged at
13/24.

## 2026-05-18 (late late + 5) — Generic genus-≥1 period-lattice: per-based-loop homology + complex-valued Stokes consolidation (6 chips, ~964 LOC)

**Follow-on chips 5–6 (after the per-based-loop homology reduction landed
above).** Consolidate the holomorphic side's two real-valued vanishings
into a single complex-valued statement, then package the most-atomic
data list into a single one-shot constructor.

* `Manifold/HolomorphicStokesFromComplexBoundary.lean` (~140 LOC) —
  factors `HolomorphicStokesHypothesis X` (two real-valued vanishings)
  through `HolomorphicComplexBoundaryVanishingHypothesis X` (a single
  complex-valued vanishing: `complexChainPeriod (∂σ) om = 0` for every
  smooth 2-simplex `σ` and every holomorphic `om`).
  - `HolomorphicStokesHypothesis_of_complexBoundary` — Re/Im extraction
    of the complex identity.
  - `complexBoundary_of_HolomorphicStokesHypothesis` — reverse
    direction; reassembles re + i · im.
  - `holomorphicStokesHypothesis_iff_complexBoundary` — biconditional.
  - `HolomorphicComponentsCanonicalClosed.of_complexBoundary` — direct
    composition route.

* `Manifold/GenericGenusPeriodLatticeAtomicHeadline.lean` (~110 LOC) —
  the most-atomic entry point.
  - `GenericGenusPeriodLatticeInputs.ofAtomicData` builds the full
    inputs structure from the smallest atomic data list in tree:
    `cycleGens` + `riemannBilinear` +
    `HolomorphicComplexBoundaryVanishingHypothesis X` +
    smooth-path-connectedness `(p₀, α)` +
    `BasedLoopHomologyDecompositionHypothesis cycleGens p₀`.
  - `nonempty_periodLatticeSymplecticBundle_ofAtomicData` —
    `Nonempty` composition through to the symplectic bundle.

**Net.** The user-facing atomic data list at general genus now reads:

1. `cycleGens : Fin (2g) → SmoothCycle 𝓘(ℝ, ℂ) X` — chosen tuple;
2. `riemannBilinear` — ℝ-linear independence of period vectors;
3. `HolomorphicComplexBoundaryVanishingHypothesis X` — complex-valued
   holomorphic-form Stokes vanishing on every smooth 2-simplex
   boundary;
4. `(p₀, α)` — basepoint + smooth-path-connectedness;
5. `BasedLoopHomologyDecompositionHypothesis cycleGens p₀` — per-loop
   ℤ-combination-mod-stokesBoundaries hypothesis.

Repo state: **143,695 LOC across 807 `.lean` files**, build **9092
jobs** clean (zero `sorry`, zero `axiom`). Scoreboard unchanged at
13/24.

## 2026-05-18 (late late + 5a) — Generic genus-≥1 period-lattice: per-based-loop homology reduction (4 chips, ~711 LOC)

First structural-reduction chip arc that gets the **generic genus-≥1**
period-lattice picture into the tree. The fourth atomic input of
`GenericGenusPeriodLatticeInputs basis` —
`H1_spans_top_canonical` (the canonical-Stokes quotient is ℤ-spanned
by the projections of the `cycleGens`) — now factors through a
**per-based-loop homology decomposition hypothesis** plus
smooth-path-connectedness, mirroring the existing genus-0 route via
`cycle_in_stokesBoundaries_of_basedLoopsBound`. The genus-0 case is
the trivial decomposition (all coefficients 0, recovering "single
basedLoop ∈ stokesBoundaries"); the genus-≥1 case carries the chosen
ℤ-combination.

* `Manifold/GenericGenusH1SpansTopFromLoopHomology.lean` (~369 LOC) —
  the headline reduction.
  - `BasedLoopHomologyDecompositionHypothesis cycleGens p₀` predicate:
    every smooth loop `γ` based at `p₀` admits a ℤ-tuple `n` with
    `single γ - ∑ nᵢ • cycleGens i ∈ stokesBoundaries`.
  - `singlePlusCorrectionCycle_eq_zsmul_mod_stokesBoundaries` —
    per-path version: each `singlePlusCorrectionCycle γ` differs from
    a ℤ-combination of `cycleGens` by a Stokes-boundary, via the
    unconditional rebasing identity + the per-loop hypothesis applied
    to `basedLoopOf γ`.
  - `H1_spans_top_canonical_of_basedLoopHomology` — the structural
    reduction. Aggregates the per-path decomposition over `c.support`
    of any cycle `c`, internally replicating the `αShift`
    cycle-property cancellation argument with an extra
    `∑ Nᵢ • cycleGens i` term tracked alongside; the swap-of-summation
    `Finset.sum_comm` + `Finset.sum_smul` collapses
    `∑ γ ∑ i (f γ · nᵢ(γ)) • cycleGens i` to `∑ i Nᵢ • cycleGens i`.
    The canonical quotient projection then puts `S.proj c` in
    `Submodule.span ℤ {S.proj (cycleGens i)}`.

* `Manifold/GenericGenusPeriodLatticeInputsFromBasedLoopHomology.lean`
  (~153 LOC) — the clean-atomic constructor.
  - `GenericGenusPeriodLatticeInputs.ofBasedLoopHomology` builds
    `GenericGenusPeriodLatticeInputs basis` from the three "outer"
    atomic inputs (`cycleGens`, `riemannBilinear`,
    `holomorphicCanonicalClosed`) + smooth-path-connectedness
    `(p₀, α, h_α_src, h_α_tgt)` + the per-loop hypothesis.
  - `nonempty_*` headlines compose through to
    `Nonempty (PeriodLatticeSymplecticBundle ...)`.

* `Manifold/BasedLoopHomologyFromBasedLoopsBound.lean` (~92 LOC) —
  trivial subsumption: `BasedSmoothLoopsBoundHypothesis I X p₀` ⟹
  `BasedLoopHomologyDecompositionHypothesis cycleGens p₀` for **any**
  `cycleGens` (taking all coefficients 0). Specialised to
  `basedLoopHomologyDecompositionHypothesis_RS_holds` unconditional
  on `RiemannSphere`.

* `Manifold/GenericGenusPeriodLatticeInputsRiemannSphereViaBasedLoopHomology.lean`
  (~97 LOC) — validation chip. Reproduces
  `genericGenusPeriodLatticeInputs_RiemannSphere` via the new
  per-based-loop homology route end-to-end on the known genus-0 case.

**Net structural reduction.** For any compact connected complex
1-manifold `X`, the analytic Jacobian period-lattice symplectic bundle
now factors through the following reduced atomic data:

1. `cycleGens : Fin (2g) → SmoothCycle 𝓘(ℝ, ℂ) X` (a chosen tuple);
2. `riemannBilinear`: ℝ-linear independence of the 2g period vectors;
3. `holomorphicCanonicalClosed`: real/imag components of every
   holomorphic 1-form lie in `canonicalClosedForms`;
4. `(p₀, α)`: a basepoint + smooth-path-connectedness data;
5. `BasedLoopHomologyDecompositionHypothesis cycleGens p₀`: the
   per-based-loop ℤ-combination-mod-stokesBoundaries hypothesis.

(4)/(5) replace the single canonical-H₁ generation field of the prior
atomic 4-tuple with smooth-path-connectedness + a per-loop hypothesis,
which on a genus-`g` surface is exactly the smooth-Hurewicz content
(every smooth loop's class is a ℤ-combination of the symplectic basis
classes in `H₁(X; ℤ)`).

Repo state: **143,442 LOC across 805 `.lean` files**, build
**9090 jobs** clean (zero `sorry`, zero `axiom`). Scoreboard unchanged
at 13/24.

## 2026-05-18 (late late + 4) — Full genus-0 period-lattice closure on RS + cotangent-bundle chart-pullback identity (8 chips, ~950 LOC, MERGED + PUSHED to origin/main HEAD `419b009`)

Two intertwined arcs landed this session:

**Arc A — Genus-0 period-lattice closure unconditional on `RiemannSphere`**
(5 chips, ~360 LOC). The full `GenericGenusPeriodLatticeInputs` 4-tuple on
RS is now constructible without any classical-input hypothesis.

* `Manifold/SmoothCycleInStokesBoundariesOfBasedLoopsBound.lean`
  (~225 LOC) — Finsupp aggregation headline
  `cycle_in_stokesBoundaries_of_basedLoopsBound`. Aggregates the
  per-path discharge `singlePlusCorrectionCycle_mem_stokesBoundaries`
  over `c.support` via a Finsupp ℤ-linear-combination construction.
  Each summand lies in `stokesBoundaries` by `zsmul_mem`; the cycle
  property `∂c = 0` collapses the `S_src - S_tgt` α-shift correction
  (via an explicit `αShift : (X →₀ ℤ) →ₗ[ℤ] SmoothChain I X` linear
  combination). Closes the structural reduction
  `BasedSmoothLoopsBoundHypothesis I X p₀ → ∀ c, c ∈ stokesBoundaries`.

* `Manifold/StokesBoundariesRiemannSphereTop.lean` —
  **`stokesBoundaries 𝓘(ℝ, ℂ) RiemannSphere = ⊤`** as an in-tree
  theorem. Picks `p₀ := (0 : ℂ)`, extracts the based-path family `α`
  via `Classical.choose` on `smoothPathConnected_RiemannSphere`, and
  composes the cycle decomposition with the unconditional
  `basedSmoothLoopsBoundHypothesis_RS_holds` from the prior arc.

* `Manifold/C3PeriodLatticeStokesRiemannSphereUnconditional.lean` —
  `C3PeriodLatticeStokesSpanTopInputs_RiemannSphere_unconditional`
  via `trivial_at_genus_zero_canonical_of_stokesBoundaries_top`.

* `Manifold/PeriodLatticeSymplecticBundleRiemannSphereUnconditional.lean`
  — `periodLatticeSymplecticBundle_RiemannSphere_unconditional`
  via `.toBundle`.

* `Manifold/GenericGenusPeriodLatticeInputsRiemannSphere.lean` —
  full 4-tuple `GenericGenusPeriodLatticeInputs` on RS unconditional.
  All four atomic inputs discharged:
    - `cycleGens` via `IsEmpty.elim` on `Fin (2 * 0)`.
    - `riemannBilinear` via `linearIndependent_empty_type`.
    - `holomorphicCanonicalClosed` via
      `HolomorphicComponentsCanonicalClosed.of_subsingleton`.
    - `H1_spans_top_canonical` via `Subsingleton.elim` after
      `subsingleton_canonical_H1_of_stokesBoundaries_eq_top` consuming
      the new `stokesBoundaries_RS_eq_top`.

**Arc B — Cotangent-bundle chart-pullback identity** (3 chips, ~590 LOC).
The substantive cotangent-bundle content for chart-contained-loop
vanishing is now in tree under a structural hypothesis (frame stability),
and dischargeable per-loop on `RS` for `basePoint ≠ ∞`.

* `Manifold/ComplexEvalIntegrandContinuity.lean` —
  `complexEvalIntegrand_continuousOn`: the benign continuity hypothesis
  of `chartContainedLoopVanishingHypothesis_from_pointwise`
  (`ContinuousOn (fun t => (α.eval (γ.ambient t)) (γ.velocity t)) (Icc 0 1)`)
  is discharged unconditionally via decomposition into `Re + I·Im`
  of the existing real-valued continuous integrands.
  Headline `chartContainedLoopVanishingHypothesis_from_pointwise_only`
  collapses the chart-contained-loop vanishing to the single
  substantive ingredient `PointwiseChartEvalIdentity`.

* `Manifold/PointwiseChartEvalFromFrameStability.lean` —
  **`PointwiseChartEvalIdentity` proven under frame stability.**
  Defines `CotangentChartFrameStable data` (`chartAt ℂ (γ.ambient t) =
  chartAt ℂ basePoint` for `t ∈ [0, 1]`). Under it:
    - Cotangent collapse: `localCoeff α basePoint (chartPath t) =
      (α.toFun (γ.ambient t)) 1` via
      `cotangentBundleCore_coordChange_self`.
    - Tangent collapse: `mfderiv (chart basePoint) (γ.ambient t) =
      ContinuousLinearMap.id ℝ ℂ` via
      `mfderiv_chartAt_eq_tangentCoordChange` + `tangentCoordChange_self`.
    - Chain rule + ℂ-linearity close the identity.
  Composite headline `chartContainedLoopVanishingHypothesis_of_frameStable`
  reduces `ChartContainedLoopVanishingHypothesis` to universal frame
  stability.

* `Manifold/CotangentChartFrameStableRS.lean` —
  `cotangentChartFrameStable_RiemannSphere`: frame stability is
  automatic for chart-contained loops on RS with `basePoint ≠ ∞`
  (`chartAt ℂ x = chartN` for every `x ≠ ∞`, via `chartAt'_coe` and
  `chartN_source = {x | x ≠ ∞}`). Per-loop headline
  **`complexChainPeriod_vanishes_RiemannSphere`**: for any
  `ChartContainedClosedLoop` on RS with `basePoint ≠ ∞` and any
  holomorphic 1-form, `complexChainPeriod (single γ) α = 0`
  (composing frame stability + `PointwiseChartEvalIdentity` + ℂ-integrand
  continuity + the structural bridge + `chartPath_loop_integral_zero`).
  Also adds the public re-export
  `RiemannSphere.chartAt_eq_chartN_of_ne_infty` of the previously-
  `private` `chartAt_of_ne_infty`.

**Net effect.**

* The full genus-0 corner of period-lattice closure is closed on RS
  without any classical hypothesis (Arc A). For `RiemannSphere` —
  `Subsingleton (HolomorphicOneForm RS)` already gave 3 of the 4
  atomic inputs trivially; the new piece is `H1_spans_top_canonical`
  via the SmoothCycle-level `stokesBoundaries = ⊤`.

* The cotangent-bundle chart-pullback identity that powers
  chart-contained loop vanishing is now in tree under a structural
  reduction (frame stability, Arc B). Frame stability for a single
  loop on RS off ∞ is automatic, giving the first **fully unconditional**
  per-loop integral-vanishing result on a genus-0 manifold via the
  Cauchy-disk + chart-pullback chain.

**Repo state.** 8 new files, ~950 LOC. Repo total: **142,731 LOC across
801 `.lean` files**. Build: clean, full library at **9086 jobs**
(up from 9074). Zero `sorry`, zero `axiom`.

**Gotchas surfaced.**

* `SmoothChain I X` is a `def` (not `abbrev`); applying `c.val γ`
  fails since Lean won't unfold the type synonym for function
  application. Bind `let f : SmoothPath I X →₀ ℤ := c.val` and apply
  `f γ`.
* `AddSubgroup.coe_zsmul` / `AddSubmonoidClass.coe_zsmul` aren't in
  the mathlib pin. For `((n • s : ↥G) : G)` use
  `(AddSubgroup.subtype G).map_zsmul`.
* `smul_sub`/`smul_add` chains fail on `f γ • (a + b - c)` when the
  goal has already partially distributed; use the `module` tactic
  to close ℤ-Module distributivity in one shot.
* `zsmulAddGroupHom n : α →+ α` is **not** the right slot for
  `Finsupp.liftAddHom (X → ℤ →+ ...)`; use `Finsupp.linearCombination ℤ`
  to get the `(α →₀ ℤ) →ₗ[ℤ] _` shape.
* Rewriting `genus_RiemannSphere_eq_zero` inside a structure literal
  breaks the dependent type of `riemannBilinear`; extract
  `haveI hempty : IsEmpty (Fin (2 * g))` separately.
* `CotangentSpace 𝓘(ℂ, ℂ) x` is a non-reducible `def` for `ℂ →L[ℂ] ℂ`;
  applying `α.toFun x` to `1 : ℂ` requires
  `show ℂ →L[ℂ] ℂ from α.toFun x` ascription. Direct ascription
  `(α.toFun x : ℂ →L[ℂ] ℂ) 1` fails.
* `mfderiv_eq_fderiv` for `ℝ → ℂ` is the bridge converting
  `(mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) f t) 1` to `deriv f t`.
* The Lean style linter rejects `show` tactic invocations that
  change the goal; use `change` for sub-elaborations.

## 2026-05-18 (late late + 3) — Chipping at barrier (1): boundary loop reduction + RS loop-level discharge (3 chips, ~220 LOC, MERGED + PUSHED to origin/main HEAD `8271224`)

Toward chipping away at the mathlib barrier for `holomorphicCanonicalClosed`
on general genus. Reformulates the analytical content via smooth loops
(natural form for Cauchy's theorem).

* `Manifold/Smooth2SimplexBoundaryLoop.lean` (~95 LOC) —
  `Smooth2Simplex.boundaryLoop σ := face2 ⋆ face0 ⋆ face1.reverse`,
  the closed loop traced by the simplex boundary. Headline
  `boundaryLoop_integrate_eq`: loop integral equals boundary chain
  integral.

* `Manifold/HolomorphicStokesFromLoopHypothesis.lean` (~70 LOC) —
  `HolomorphicLoopIntegralVanishes X : Prop` (loop-level formulation).
  Equivalence with `HolomorphicStokesHypothesis X` via the boundary-loop
  identity. Direct discharge of `HolomorphicComponentsCanonicalClosed`
  from the loop hypothesis.

* `Manifold/HolomorphicLoopIntegralVanishesRS.lean` (~55 LOC) —
  unconditional discharge for `RiemannSphere` via
  `Subsingleton (HolomorphicOneForm RiemannSphere)`. Routes the genus-0
  discharge through the new loop-level infrastructure.

**Net effect on barrier (1).** The general-genus discharge of
`holomorphicCanonicalClosed` now reduces (structurally) to discharging
`HolomorphicLoopIntegralVanishes X` for the specific X. For X = RS,
unconditional (this arc). For genus ≥ 1, future work: chart-pullback
of integration + mathlib's Cauchy theorem on disks
(`DifferentiableOn.isExactOn_ball`, already in tree).

Build: clean, full library at **9074 jobs**. Zero `sorry`, zero `axiom`.

## 2026-05-18 (late late + 2) — Per-path cycle-decomposition primitives + genus ≥ 1 barrier triage (1 chip, ~205 LOC, MERGED + PUSHED to origin/main HEAD `2d8855c`)

`Manifold/SmoothCycleDecompositionToBasedLoops.lean` ships per-path
infrastructure toward genus ≥ 1 `H1_spans_top_canonical`:

* `basedLoopOf α γ := α(γ.src) ⋆ γ ⋆ (α γ.tgt).reverse` — based loop at p₀.
* `rebasingCycleOf γ` packaged + `_mem_stokesBoundaries` via existing
  `rebasing_in_stokesBoundaries`.
* `singlePlusCorrectionCycle γ` (= `single γ + single (α γ.src) - single (α γ.tgt)`)
  packaged as a SmoothCycle.
* `singlePlusCorrectionCycle_mem_stokesBoundaries` (per-path discharge):
  under `BasedSmoothLoopsBoundHypothesis I X p₀`, the chain
  `single γ + α-correction ∈ stokesBoundaries`. Proof: sum the rebasing
  cycle and `single (basedLoopOf γ)` (basedLoop in stokesBoundaries by
  hypothesis); the `single (basedLoopOf γ)` summands cancel algebraically.

**Genus ≥ 1 barrier triage.** After attempting each of the four atomic
inputs of `GenericGenusPeriodLatticeInputs`, every one is **true-barrier
blocked** on classical mathlib gaps:

1. `holomorphicCanonicalClosed` — Stokes' theorem on smooth 2-simplices
   is not in mathlib at this pin. Without it, the closure of
   real/imaginary components of holomorphic 1-forms in
   `canonicalClosedForms` cannot be discharged.
2. `H1_spans_top_canonical` — Surface classification (compact orientable
   genus-g 2-manifold ≅ Σ_g) + symplectic basis construction not in
   mathlib.
3. `cycleGens` — Depends on (2): cycle representatives of a symplectic
   basis require surface classification.
4. `riemannBilinear` — Riemann bilinear non-degeneracy depends on Hodge
   theory (Hodge ⋆-operator, ω ∧ ω̄ positivity) not in mathlib at this
   pin. Also requires `HolomorphicOneFormFiniteDim X` finished
   (Forster Riesz arc has the seminorm-convergence + Riesz gaps from
   2026-05-17).

All four are *classical content not at the mathlib pin* — genuine
external prerequisites, not Lean-tactical issues. The work delivered
in this and the prior arc is the **structural framework + per-path
infrastructure** ready to consume each input once the relevant mathlib
prerequisite lands.

Build: clean, full library at **9071 jobs**. Zero `sorry`, zero `axiom`.

## 2026-05-18 (late late + 1) — Generic-genus entry point `GenericGenusPeriodLatticeInputs` (1 chip, ~140 LOC, MERGED + PUSHED to origin/main HEAD `2189d49`)

Opens the genus ≥ 1 work. `Manifold/GenericGenusPeriodLatticeInputs.lean`
ships a structure bundling the FOUR atomic canonical-bundle inputs:

  structure GenericGenusPeriodLatticeInputs basis where
    cycleGens                  -- Fin (2g) → H₁(X; ℤ): symplectic basis
    riemannBilinear            -- ℝ-LI of period vectors
    holomorphicCanonicalClosed -- holomorphic ω ⟹ Stokes-closed
    H1_spans_top_canonical     -- ℤ-span of cycleGens = canonical H₁

* `toBundle` — promotes to `C3PeriodLatticeStokesSpanTopInputs basis`
  via the canonical-bundle constructor.
* `nonempty_C3PeriodLatticeStokesSpanTopInputs_of_genericGenus`.
* `nonempty_periodLatticeSymplecticBundle_of_genericGenus` — composite
  to `PeriodLatticeSymplecticBundle`.

For genus 0 (X with `Subsingleton (HolomorphicOneForm X)`), each of
the four is unconditional in tree.

For genus ≥ 1, each is genuinely-new classical content:
* `cycleGens` — surface classification + symplectic basis.
* `riemannBilinear` — Riemann bilinear / Hodge theory.
* `holomorphicCanonicalClosed` — Stokes' theorem + Cauchy-Riemann.
* `H1_spans_top_canonical` — cellular homology of compact orientable
  2-manifolds.

Build: clean, full library at **9070 jobs**.
Zero `sorry`, zero `axiom`.

## 2026-05-18 (late late) — `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) RS p₀` UNCONDITIONAL — Sard via Hausdorff + Möbius shift + chart-N pullback (6 chips, ~890 LOC, MERGED + PUSHED to origin/main HEAD `ce40ac7`)

The load-bearing genus-0 input for canonical period-lattice closure
is now structurally complete: every smooth loop on `RiemannSphere`
at any basepoint has its single in `stokesBoundaries 𝓘(ℝ, ℂ) RS`.
Repo: **141,139 LOC across 788 files**, full `lake build` at
**9068 jobs**.

The atomic predicate chain — `SmoothLoopHasMissedPointHypothesis`
→ `LoopFactorsThroughVectorSpaceHypothesis` →
`BasedSmoothLoopsBoundHypothesis` — is now end-to-end unconditional.

* **`Manifold/SmoothPathTubularBump.lean`** (~165 LOC) — smooth bump
  `tubularBump δ : ℝ → ℝ` (= product of two `Real.smoothTransition`)
  with `=1` on `[0, 1]`, `=0` outside `[-δ, 1+δ]`. Plus
  `exists_tubular_delta` (open `U ⊇ Icc 0 1 ⟹ ∃ δ > 0, Ioo (-δ) (1+δ) ⊆ U`).

* **`Manifold/SmoothLoopChartNPullbackDischarge.lean`** (~205 LOC) —
  `smoothLoopChartNPullbackExistsHypothesis_holds`. Constructs the
  smooth pullback `γ' : SmoothPath 𝓘(ℝ, ℂ) ℂ` of a smooth loop with
  image in `chartN.source`, via `g'(t) := tubularBump δ t *
  chartN(γ.ambient t)`. Smoothness via two-region open cover
  `Ioo (-δ_outer, 1+δ_outer) ∪ (Iio (-δ) ∪ Ioi (1+δ))`.

* **`Manifold/LoopFactorsThroughVectorSpaceFromAvoidInfty.lean`** (~50 LOC) —
  composite wiring the chart-N discharge into the structural reduction.

* **`Manifold/RiemannSphereMobiusComposed.lean`** (~165 LOC) —
  `mobiusComposed c := antipode ∘ translateBy (-c) : RS → RS` sending
  `(some c) ↦ ∞`; `mobiusComposedInv c := translateBy c ∘ antipode`.
  Smoothness in real model (`𝓘(ℝ, ℂ) ∞`) via composition + realification.

* **`Manifold/LoopFactorsThroughVectorSpaceFromMissedPoint.lean`** (~195 LOC) —
  `SmoothLoopHasMissedPointHypothesis p₀` predicate. Derives
  `LoopFactorsThroughVectorSpaceHypothesis ℂ RS p₀` by case-split on
  the missed point (∞ direct, finite `c` via `mobiusComposed`).

* **`Manifold/SmoothLoopHasMissedPointDischarge.lean`** (~140 LOC) —
  `smoothLoopHasMissedPointHypothesis_holds` UNCONDITIONAL via Sard
  through Hausdorff dimension:
  - `chartN ∘ γ.ambient` is locally Lipschitz on
    `s := γ.ambient⁻¹ chartN.source ∩ Icc 0 1`
    (smooth composition + `ContDiffAt.exists_lipschitzOnWith`).
  - `dimH_image_le_of_locally_lipschitzOn` ⟹ `dimH image ≤ dimH s ≤ 1`.
  - `1 < 2 = finrank ℝ ℂ` ⟹ `dense_compl_of_dimH_lt_finrank` ⟹
    complement is dense, hence non-empty.
  - Pick `z` in complement; `chartN.symm z` is the missed point.

* **`Manifold/StokesBoundariesTopRiemannSphere.lean`** (~50 LOC) —
  capstone composite `basedSmoothLoopsBoundHypothesis_RS_holds (p₀)`:
  `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) RiemannSphere p₀` is
  unconditional.

Build: each file clean via `LEAN_NUM_THREADS=1 lake env lean`. Zero
`sorry`, zero `axiom`.

## 2026-05-18 (late) — Chart-symm smoothness + structural reduction to two atomic predicates (2 chips, ~250 LOC, MERGED + PUSHED to origin/main HEAD `9e1fe1a`)

Continues toward an unconditional discharge of
`LoopFactorsThroughVectorSpaceHypothesis ℂ RiemannSphere p₀`:

* **`Manifold/RiemannSphereChartSymmSmooth.lean`** — global C^∞
  smoothness of `chartN.symm : ℂ → RS` and `chartS.symm : ℂ → RS` as
  manifold maps with model `𝓘(ℝ, ℂ)`, at regularity `⊤`. Proof:
  `chartAt ℂ ((0 : ℂ) : RS) = chartN`, `chartAt ℂ ∞ = chartS`, then
  mathlib's `contMDiffOn_chart_symm` + `chartN.target = univ` (resp.
  `chartS.target = univ`) gives global smoothness.

* **`Manifold/LoopFactorsThroughVectorSpaceFromChartN.lean`** —
  structural reduction: two named atomic predicates
  `SmoothLoopAvoidsInftyHypothesis p₀` (every smooth loop on RS at
  `p₀` misses `∞`) and `SmoothLoopChartNPullbackExistsHypothesis p₀`
  (smooth-loops-with-image-in-chartN.source have smooth chart pullbacks
  to `ℂ`) jointly discharge
  `LoopFactorsThroughVectorSpaceHypothesis ℂ RiemannSphere p₀` via
  `chartN.symm`.

Build: clean via `LEAN_NUM_THREADS=1 lake env lean`. Zero `sorry`,
zero `axiom`. Project total: **~140,066 LOC across 781 files**, full
`lake build` at **9061 jobs**.

## 2026-05-18 (late night continuation) — Rebasing + V-loop-bounds + factorisation pipeline (11 chips, ~1840 LOC, MERGED + PUSHED to origin/main HEAD `3d765aa`)

Continues the period-lattice closure pipeline. Reduces
`stokesBoundaries 𝓘(ℝ, ℂ) RiemannSphere = ⊤` to a SINGLE atomic
predicate `LoopFactorsThroughVectorSpaceHypothesis ℂ RiemannSphere p₀`,
itself constructively dischargeable via stereographic projection
from a missed point.

* **Rebasing arc (3 chips, ~510 LOC):**
  - `Manifold/SmoothPathRebasingIdentity.lean` —
    `triple_concat_in_stokesBoundaries`. Sum of two
    `concat_additive_in_stokesBoundaries` applications gives the
    triple-concat identity.
  - `Manifold/SmoothPathRebasingFull.lean` —
    `rebasing_in_stokesBoundaries`: any smooth path γ : a → b is
    homologous (mod stokesBoundaries) to a based loop
    `α ⋆ γ ⋆ β.reverse` at p₀ minus the rebasing corrections
    `single α - single β`.
  - `Manifold/SmoothPathLoopRebasing.lean` —
    `loop_rebasing_in_stokesBoundaries`: specialisation to a loop γ
    with β = α (corrections collapse to 0).

* **Named hypothesis (1 chip, ~150 LOC):**
  - `Manifold/BasedSmoothLoopsBound.lean` —
    `BasedSmoothLoopsBoundHypothesis I X p₀` predicate +
    `single_smoothLoop_in_stokesBoundaries_of_basedLoopsBoundHypothesis`:
    every smooth loop (not necessarily based) on a smooth-path-connected
    manifold has single in stokesBoundaries given the hypothesis.

* **V-loop-bounds (3 chips, ~620 LOC):**
  - `Manifold/Smooth2SimplexLoopBoundsVectorSpaceT1.lean`,
    `T2.lean` — square-diagonal split of the smooth homotopy
    `H(s, t) := (1-s) • γ.ambient t + s • γ.src` into two triangles.
  - `Manifold/SmoothLoopBoundsInVectorSpace.lean` —
    `single_smoothLoop_in_stokesBoundaries_vectorSpace` (any smooth
    loop in a normed ℝ-vector space V has single in stokesBoundaries),
    `basedSmoothLoopsBoundHypothesis_vectorSpace` (discharge the
    named hypothesis unconditionally on V).

* **stokesBoundaries pushforward (1 chip, ~210 LOC):**
  - `Manifold/Smooth2SimplexPush.lean` — `Smooth2Simplex.push`,
    `Smooth2Chain.push`, `boundary₂_push`, and the structural
    headline `stokesBoundaries_push` (pushforward via a smooth map
    sends `stokesBoundaries I X → stokesBoundaries I Y`).

* **Composition + factorisation (2 chips, ~230 LOC):**
  - `Manifold/SmoothLoopBoundsViaChart.lean` — composes V-loop-bounds
    with `stokesBoundaries_push`:
    `single_pushSmoothLoop_in_stokesBoundaries_of_vectorSpaceSource`
    for any smooth loop γ' in V and smooth map f : V → X.
  - `Manifold/BasedSmoothLoopsBoundFromFactorisation.lean` — named
    predicate `LoopFactorsThroughVectorSpaceHypothesis V X p₀` +
    `basedSmoothLoopsBoundHypothesis_of_factorisation` discharging
    `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, V) X p₀` from it.

Build: each file individually verified via
`LEAN_NUM_THREADS=1 lake env lean`. Zero `sorry`, zero `axiom`
across all 11 chips.

**Net atomic-input boundary for the period-lattice side of C3 on
RiemannSphere** is now:

  `LoopFactorsThroughVectorSpaceHypothesis ℂ RiemannSphere p₀`

— a single Prop expressing "every smooth loop on RS at p₀ factors
through ℂ via some smooth map". Constructive on RS via stereographic
projection from a missed point.

## 2026-05-18 (continuation) — Concat-additivity in stokesBoundaries CLOSED (10 chips, ~2210 LOC, MERGED + PUSHED to origin/main HEAD `a349fd8`)

Foundational chain-level identity:

```
single (γ.concat δ h) - single γ - single δ  ∈  stokesBoundaries I X
```

for any compatible smooth paths γ, δ : SmoothPath I X on any smooth
manifold X. Equivalently, in the canonical Stokes H₁ quotient,
`[γ.concat δ h] = [γ] + [δ]`. Net effect: concatenation of smooth
paths is additive in homology — the structural identity needed to
reduce arbitrary smooth 1-cycles into based loops at a fixed
basepoint, which in turn is the last reduction toward
`stokesBoundaries 𝓘(ℝ, ℂ) RiemannSphere = ⊤`.

* **Concat 2-simplex (3 chips, ~580 LOC):**
  - `Manifold/Smooth2SimplexFromConcat.lean` —
    `Smooth2Simplex.ofSmoothPathConcat γ δ h` with toFun
    `(x₀, x₁) := γ.concatAmbient δ (x₀/2 + x₁)`. `face1 σ = γ.concat δ h`
    via `SmoothPath.ext` (load-bearing identity: both have the same
    underlying `toPath.toFun` because face1's parameterisation
    `σ(0, t) = γ.concatAmbient δ t` matches the concat ambient
    exactly).
  - `Manifold/SmoothPathBumpedHalf.lean` — `SmoothPath.bumpedHalfLeft γ`
    and `bumpedHalfRight δ`: the bump-half-flat reparameterisations
    of γ, δ. Public `ambient_zero_eq_src`, `ambient_one_eq_tgt`.
  - `Manifold/Smooth2SimplexConcatFaceIdent.lean` — identifies
    `face2 σ = γ.bumpedHalfLeft`, `face0 σ = δ.bumpedHalfRight`. So
    the boundary chain is exactly
    `single δ.bumpedHalfRight - single (γ.concat δ h)
       + single γ.bumpedHalfLeft ∈ stokesBoundaries`.

* **Left reparam-invariance (3 chips, ~770 LOC):**
  - `Manifold/Smooth2SimplexReparamLeftT1.lean` — first triangle T₁
    of the square-diagonal split of
    `(s, t) ↦ γ.ambient((1-s)*t + s*concatRepLeft(t/2))`. Faces:
    `face0=const γ.tgt`, `face2=γ`, `face1`=diagonal. Auxiliary
    `reparamLeftF s t := (1-s)*t + s*concatRepLeft(t/2)` and its C^∞
    proof + endpoint specialisations.
  - `Manifold/Smooth2SimplexReparamLeftT2.lean` — second triangle T₂.
    Faces: `face0=γ.bumpedHalfLeft.reverse`, `face1=const γ.src`,
    `face2`=same diagonal (cancellation lemma).
  - `Manifold/SmoothPathBumpedHalfLeftReparamInvariance.lean` —
    after diagonal cancellation,
    `∂(T₁+T₂) = const γ.tgt + γ + bumpedHalfLeft.reverse - const γ.src
      ∈ stokesBoundaries`. Combined with const-membership and
    reverse-cancellation:
    `single γ - single γ.bumpedHalfLeft ∈ stokesBoundaries`
    (`bumpedHalfLeft_reparam_invariance`).

* **Right reparam-invariance (3 chips, ~640 LOC):**
  - Symmetric: `Smooth2SimplexReparamRightT1.lean`,
    `Smooth2SimplexReparamRightT2.lean`,
    `SmoothPathBumpedHalfRightReparamInvariance.lean`.
  - Headline `bumpedHalfRight_reparam_invariance`:
    `single δ - single δ.bumpedHalfRight ∈ stokesBoundaries`.

* **Concat-additivity capstone (1 chip, ~220 LOC):**
  - `Manifold/SmoothPathConcatAdditivityStokes.lean` — linear
    combination `-(face_ident) - (left_reparam) - (right_reparam)`
    collapses to `single (γ.concat δ h) - single γ - single δ`.
    Headline `concat_additive_in_stokesBoundaries`.

Build: each file individually verified via
`LEAN_NUM_THREADS=1 lake env lean`. Zero `sorry`, zero `axiom`
across all 10 chips.

**Net classical-input boundary** for the period-lattice side of
C3 reduces from (1)-(4) to:

1. `cycleGens` (symplectic basis choice);
2. `riemannBilinear`;
3. `HolomorphicStokesHypothesis X`;
4. **`stokesBoundaries 𝓘(ℝ, ℂ) RiemannSphere = ⊤`**.

For (4): with concat-additivity + reverse-cancellation +
const-membership in hand, every smooth 1-cycle reduces to a sum of
based smooth loops. The remaining classical input is: every smooth
loop on a simply-connected smooth manifold bounds a smooth 2-chain.
For RiemannSphere specifically, this is constructive via chart-based
linear contraction in `ℂ` after avoiding a missed point.

## 2026-05-18 — Period-lattice canonical Stokes bundle + smooth-singular foundation + path-plus-reverse identity (23 chips, ~2280 LOC, MERGED to main, origin/main HEAD `bc2a239`)

Three-phase arc shipping 23 chips totaling ~2280 LOC:

* **Phase 1 (chips 1-7, ~770 LOC):** canonical-bundle migration —
  see "Canonical Stokes bundle / Atomic holomorphic-side hypothesis /
  Layered constructors / RS canonical-bundle headline" subsections
  below.
* **Phase 2 (chips 8-13, ~530 LOC):** smooth-singular constant-2-simplex
  foundation. `Smooth2Simplex.const` + `boundary_const_smoothCycle
  ∈ stokesBoundaries` (`Manifold/Smooth2SimplexConst.lean`, ~109 LOC);
  generic `SmoothPath.integrate_eq_zero_of_toPath_eq_const`
  (`Manifold/SmoothPathIntegrateConstToPath.lean`, ~177 LOC);
  constant-2-simplex boundary integrates to zero against any form
  (`Manifold/Smooth2SimplexConstBoundaryIntegrate.lean`, ~80 LOC);
  `subsingleton_canonical_H1_iff_stokesBoundaries_eq_top`
  (`Manifold/StokesCanonicalH1SubsingletonChar.lean`, ~95 LOC);
  alt-formulation `trivial_at_genus_zero_canonical_of_stokesBoundaries_top`
  (`Manifold/C3PeriodLatticeStokesCanonicalFromStokesBoundariesTop.lean`,
  ~80 LOC); items 11/5/12 canonical-bundle discharge on RS
  (`Manifold/C3PeriodLatticeCanonicalItemsDischarge.lean`, ~80 LOC).
* **Phase 3 (chips 14-23, ~980 LOC):** SmoothPath-equality machinery
  + smooth-2-simplex-from-path + path-plus-reverse identity. Face-
  equality of constant 2-simplex via `congr 1` + Prop irrelevance
  (`Manifold/Smooth2SimplexConstFaceEq.lean`, ~145 LOC);
  `face0 (const P) = SmoothPath.const I X P` +
  `single_smoothPath_const_smoothCycle_mem_stokesBoundaries`
  (`Manifold/SmoothPathConstFromFace0.lean`, ~95 LOC);
  `@[ext] SmoothPath.ext` (`Manifold/SmoothPathExt.lean`, ~70 LOC);
  `Smooth2Simplex.ofSmoothPathFstProj γ` + face identifications
  (face0 = γ.reverse, face1 = const γ.src, face2 = γ) + boundary
  identity (`Manifold/Smooth2SimplexFromPath.lean`, ~230 LOC);
  **`single γ + single γ.reverse ∈ stokesBoundaries`** for any γ
  (`Manifold/SmoothPathReverseStokesBoundary.lean`, ~95 LOC);
  direct integration computation `integrate (single γ + single
  γ.reverse) om = 0` for any form
  (`Manifold/SmoothPathReverseIntegrateZero.lean`, ~55 LOC);
  canonical-H1 quotient class is zero
  (`Manifold/SmoothPathReverseH1Zero.lean`, ~50 LOC);
  `SmoothPath.const_reverse`, `SmoothPath.reverse_reverse` algebraic
  identities (`Manifold/SmoothPathConstReverseEq.lean` ~55 LOC,
  `Manifold/SmoothPathReverseReverse.lean` ~55 LOC); chain-level
  concat-additive integration
  (`Manifold/SmoothPathConcatIntegrateChain.lean`, ~50 LOC).

Cumulative build: 9039 jobs clean. Zero `sorry`, zero `axiom`. The
4-atomic-input canonical-bundle classical-content boundary holds
end-to-end on any X with `[IsManifold 𝓘(ℂ, ℂ) ω X]`; on `RiemannSphere`
specifically, items 11/5/12 discharge reduces to the single
`Subsingleton (canonical _).H1` hypothesis (the canonical-Stokes-quotient
analogue of `H₁(S²;ℤ) = 0`), with concrete homological identities
(reverse cancellation, constant paths bound) fully foundationally laid.

The detailed per-chip notes below cover Phase 1 (chips 1-7) only;
Phase 2-3 chip details are summarised in `OPEN.md` and the per-file
docstrings.

## 2026-05-18 (canonical-bundle migration phase) — Period-lattice canonical Stokes bundle (7 chips, ~770 LOC, branch `feat/period-lattice-canonical-bundle`, MERGED to main)

Refactors `C3PeriodLatticeStokesSpanTopInputs` so the `boundaries` and
`closedForms` fields of the consumed `StokesBoundaryInvariance` bundle
become **canonical** rather than consumer-supplied. The user-visible
classical input boundary for the period-lattice side of `C3FullInput X`
shrinks from 5 fields (with two of them being setup-of-the-bundle
choices) to 4 atomic classical statements with no bundle infrastructure
left for the consumer to choose.

### Canonical Stokes bundle (chips 1–2, ~265 LOC)

* **`Manifold/StokesCanonicalClosedForms.lean`** (~119 LOC) —
  `canonicalClosedForms I X : Submodule ℝ (SmoothOneForm I X)` defines
  the largest submodule of forms for which the single-simplex Stokes
  hypothesis holds: forms whose integral around every smooth 2-simplex
  boundary vanishes. `canonicalIntegrationStokes` discharges the
  hypothesis tautologically. `StokesBoundaryInvariance.canonical I X`
  composes these via `ofSingleSimplexStokes`, fixing
  `boundaries := stokesBoundaries I X` and
  `closedForms := canonicalClosedForms I X` with the vanishing
  hypothesis automatic.

* **`Manifold/C3PeriodLatticeStokesCanonical.lean`** (~146 LOC) —
  `C3PeriodLatticeStokesSpanTopInputs.ofCanonical` constructor: from
  `cycleGens`, `riemannBilinear`, `holomorphicCanonicalClosed`,
  `H1_spans_top_canonical`, builds the bundle with
  `stokes := StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X`.

### Atomic holomorphic-side hypothesis (chip 3, ~120 LOC)

* **`Manifold/HolomorphicComponentsCanonicalClosed.lean`** (~120 LOC) —
  Named predicate `HolomorphicComponentsCanonicalClosed X` (each
  holomorphic form's real / imaginary components lie in
  `canonicalClosedForms`) and the more-atomic `HolomorphicStokesHypothesis
  X` (Stokes' theorem for the components of every holomorphic 1-form
  against every smooth 2-simplex boundary), with derivations
  `.of_hypothesis` and `.of_subsingleton` (genus-0 trivial discharge).

### Layered constructors (chips 4–6, ~290 LOC)

* **`Manifold/C3PeriodLatticeStokesCanonicalFromHypothesis.lean`**
  (~102 LOC) — `C3PeriodLatticeStokesSpanTopInputs.ofStokesHypothesis`
  (takes the single atomic `HolomorphicStokesHypothesis X` instead of
  the unfolded predicate) and `.ofCanonicalGenusZero` (drops the
  Stokes-side input when `Subsingleton (HolomorphicOneForm X)`).

* **`Manifold/C3PeriodLatticeStokesCanonicalH1Subsingleton.lean`**
  (~110 LOC) — `h1_spans_top_canonical_of_subsingleton`: if the
  canonical Stokes H₁ quotient is subsingleton, then for any tuple of
  cycles the ℤ-span of their projected classes equals `⊤` (the
  classical "H₁(X; ℤ) = 0 at genus 0" content as a single Subsingleton
  hypothesis). `.ofCanonicalGenusZeroSubsingleton` composes through
  this to take only `cycleGens` + `riemannBilinear`.

* **`Manifold/C3PeriodLatticeStokesCanonicalTrivialAtGenusZero.lean`**
  (~79 LOC) — `trivial_at_genus_zero_canonical`: at `genus X = 0`
  with the two subsingleton hypotheses, the bundle is unconditionally
  inhabited via the canonical Smooth2Chain-based Stokes bundle
  (no unconventional `boundaries := ⊤` choice as in
  `C3PeriodLatticeStokesGenusZero.lean`).

### RS canonical-bundle headline (chip 7, ~76 LOC)

* **`Manifold/C3PeriodLatticeStokesCanonicalRiemannSphere.lean`** (~76
  LOC) — `nonempty_C3PeriodLatticeStokesSpanTopInputs_RiemannSphere_canonical`
  and `periodLatticeSymplecticBundle_RiemannSphere_canonical`,
  conditional on the canonical-H₁ subsingleton hypothesis (`H₁(S²; ℤ)
  = 0`). The simply-connectedness route is `simplyConnectedS2_holds`
  (unconditional in tree) + Hurewicz / smooth singular comparison
  (not at the mathlib pin).

### Net classical-input boundary post-refactor

The period-lattice side of `C3FullInput X` now reduces to **4 atomic
classical inputs**:

1. `cycleGens : Fin (2g) → SmoothCycle 𝓘(ℝ, ℂ) X` — symplectic
   homology basis choice;
2. `riemannBilinear` — ℝ-LI of the `2g` period vectors;
3. `HolomorphicStokesHypothesis X` — Stokes' theorem for the components
   of every holomorphic 1-form;
4. `H1_spans_top_canonical` — H₁ ℤ-generation via the canonical Stokes
   quotient (subsingleton at genus 0).

`boundaries` and `closedForms` are now **canonical** — no consumer
choice left at the infrastructure level.

Build: 9022 jobs clean via `taskpolicy lake build JacobianChallenge`.
Zero `sorry`, zero `axiom` across all 7 chips.

## 2026-05-17 (very late late night) — Period Lattice Construction structural decomposition + classical-content infrastructure (8 chips, ~1,250 LOC, branch `feat/period-lattice-stokes-refactored`)

Structural decomposition of the Period Lattice Construction into
atomic classical inputs, plus the concrete `Smooth2Simplex` / `d² = 0`
algebra and the irreducible-`Prop` packaging of the single-simplex
Stokes hypothesis. Chips 1–2 fast-forwarded into `origin/main` mid-
session via the parallel item-14 session's merge; chips 3–8 live on
`feat/period-lattice-stokes-refactored` (pushed to remote).

### Structural decomposition (chips 1–5, ~660 LOC)

* **`Manifold/C3PeriodLatticeStokesRefactored.lean`** (~217 LOC) —
  `C3PeriodLatticeStokesInputs basis` factors
  `C3PeriodLatticeClassicalInputs.homologySpans` into two atomic
  textbook inputs: a `StokesBoundaryInvariance 𝓘(ℝ, ℂ) X` bundle +
  `holomorphic_closed` hypothesis, and a `homologyGeneration`
  predicate. Provides `.toClassical` deriving the unrefactored
  `homologySpans` via additivity of `periodVector` and the
  period-on-boundary vanishing lemma (`ComplexPeriodH1.lean`).

* **`Manifold/C3PeriodLatticeStokesH1Generation.lean`** (~193 LOC) —
  `C3PeriodLatticeStokesSpanTopInputs basis` replaces
  `homologyGeneration`'s existential predicate with the cleaner
  textbook statement `H1_spans_top`: `Submodule.span ℤ (range (S.proj
  ∘ cycleGens)) = ⊤`. Derivation uses `Finsupp.mem_span_range_iff_
  exists_finsupp` + `QuotientAddGroup.eq_zero_iff`.

* **`Manifold/C3PeriodLatticeStokesGenusZero.lean`** (~120 LOC) —
  `C3PeriodLatticeStokesSpanTopInputs.trivial_at_genus_zero` provides
  an inhabitant at `genus X = 0` given `Subsingleton (HolomorphicOneForm
  X)`. Uses `boundaries := ⊤`, `closedForms := ⊥`, and the helper
  `subsingleton_quotientAddGroup_top` (private lemma showing
  `G ⧸ (⊤ : AddSubgroup G)` is subsingleton).

* **`Manifold/C3PeriodLatticeStokesRiemannSphere.lean`** (~75 LOC) —
  Unconditional `nonempty_C3PeriodLatticeStokesSpanTopInputs_
  RiemannSphere` instance, composing `genus_RiemannSphere_eq_zero`
  + `Subsingleton (HolomorphicOneForm RS)` instance (both
  unconditional via `Manifold/RiemannSphereChartSCoeffOverlap.lean`).

* **`Manifold/C3PeriodLatticeStokesNonemptyHeadline.lean`** (~45
  LOC) — Single-typeclass promotion `[Nonempty
  (C3PeriodLatticeStokesSpanTopInputs basis)] → Nonempty
  (PeriodLatticeSymplecticBundle data basis)`. The cleanest external
  boundary for the period-lattice side of the C3 cascade.

### Classical-content infrastructure (chips 6–8, ~635 LOC)

* **`Manifold/Smooth2Simplex.lean`** (~370 LOC) — Concrete smooth
  singular 2-simplex infrastructure. Ships `Smooth2Simplex I X`
  (ambient `C^∞` map `(Fin 2 → ℝ) → X`); vertices `v0 = (0,0),
  v1 = (1,0), v2 = (0,1)`; three face parameter maps and their
  `ContMDiff` proofs (affine functions are `C^∞`); `face0 / face1 /
  face2 : Smooth2Simplex → SmoothPath` derived from the ambient
  extension; `Smooth2Chain I X := Smooth2Simplex I X →₀ ℤ` with
  `AddCommGroup` / `Module ℤ` instances; `boundary₂ : Smooth2Chain
  →ₗ[ℤ] SmoothChain` via `Finsupp.linearCombination`; and the
  unconditional **`boundary_squared : SmoothChain.boundary ∘
  boundary₂ = 0` (d² = 0)** identity, proved via vertex cancellation
  (`face₀ - face₁ + face₂` boundaries cancel pairwise in the formal
  combination of vertices).

* **`Manifold/Smooth2ChainStokesBoundary.lean`** (~140 LOC) —
  Promotes `boundary₂` to a `ℤ`-linear map `Smooth2Chain →ₗ[ℤ]
  SmoothCycle` (the codomain is the subtype, available via `d²=0`).
  Packages its image as the **canonical Stokes-boundary subgroup**
  `stokesBoundaries I X : AddSubgroup (SmoothCycle I X)`, suitable
  as the `boundaries` field of `StokesBoundaryInvariance`. Provides
  `mem_stokesBoundaries_iff` (membership = exists-2-chain-preimage)
  and the `zero/add/neg` closure lemmas.

* **`Manifold/StokesBoundaryInvarianceFromSimplex.lean`** (~125
  LOC) — Collapses the legacy three-named-hypothesis structure of
  `StokesBoundaryInvariance` to a **single `Prop`**:
  `IntegrationStokesHypothesis I X closedForms` =
  `∀ σ : Smooth2Simplex, ∀ ω ∈ closedForms, integrate (∂σ) ω = 0`.
  Constructor `StokesBoundaryInvariance.ofSingleSimplexStokes`
  uses this hypothesis + `Finsupp.induction_linear` +
  `SmoothChain.integrate_zsmul / _add / _zero` to lift the
  single-simplex hypothesis to the full chain level, then plugs
  `stokesBoundaries` in as the canonical `boundaries` field.

### Net effect on the period-lattice classical-input boundary

The classical content needed for the period-lattice side of C3
reduces to (parameterised over a chosen ℂ-basis `basis` and a chosen
real submodule `closedForms`):

1. **The single-simplex Stokes `Prop`**
   `IntegrationStokesHypothesis I X closedForms` (one Prop, single
   2-simplex level).
2. **`holomorphic_closed`** — every holomorphic 1-form is
   Stokes-closed (`realComponent`, `imagComponent` both in
   `closedForms`); on a complex 1-manifold this is the standard
   "d-closed" content for type-(1,0) forms.
3. **`cycleGens`** — a tuple of `2g` cycle generators.
4. **`riemannBilinear`** — ℝ-LI of their period vectors (Hodge
   bilinear non-degeneracy).
5. **`H1_spans_top`** — the cycleGens project to a ℤ-generating set
   of `H₁(X; ℤ) := SmoothCycle / boundaries` (cellular-homology
   content).

`boundaries` is now CANONICAL (`stokesBoundaries`, the image of
`boundary₂Cycle`). The five remaining inputs are the irreducible
classical content for general-genus inhabitation; the `Smooth2Simplex`
/ `d²=0` algebra is fully unconditional.

Build: all eight files individually verified via
`LEAN_NUM_THREADS=1 lake env lean ...`. Zero `sorry`, zero `axiom`.

## 2026-05-17 (very late late night) — `DegreeOneFromSimpleZeroSimplePole` non-constancy fully closed (~220 LOC, direct to `main`)

New file `Manifold/DegreeOneFromSimpleZeroSimplePoleDischarge.lean`
ships:

* `order_eq_one_at_Q1` — from `principalDivisorMap f = single Q₁ - single Q₂`
  (and `Q₁ ≠ Q₂`), `mmeromorphicOrderAt f.toFun Q₁ = 1`. Uses
  `principalDivisorMap_apply` + `Div.single_sub_single_apply` +
  `MMeromorphicOn.orderFun` unfolding.

* `order_eq_neg_one_at_Q2` — similarly `mmeromorphicOrderAt f.toFun Q₂ = -1`.

* `order_eq_zero_off` — at `x ∉ {Q₁, Q₂}`, `mmeromorphicOrderAt f.toFun x = 0`
  (via `MMeromorphicOn.orderFun_eq_zero_iff`).

* `toRiemannSphere_nonconst` — **non-constancy fully discharged**:
  `f.toRiemannSphere Q₂ = ∞` (from order -1, via
  `toRiemannSphere_eq_infty_of_order_neg`) while a constant map would
  force `f.toRiemannSphere Q₁ = ∞`, requiring order < 0 at Q₁,
  contradicting `order = 1`.

* `OrderOneSingleFibreRegular f Q₁` — named sub-hypothesis for the
  remaining content: `(some 0 : RS) ∈ regularValueSet` AND
  `fiberFinset = {Q₁}`. This is the focused analytic content
  (locally-injective at Q₁ from order 1; uniqueness of the zero from
  order-0 elsewhere) deferrable to a sister chip.

* `degreeOneFromSimpleZeroSimplePole_holds_of_OrderOneSingleFibreRegular`
  — the conditional discharge: under the named sub-hypothesis,
  `DegreeOneFromSimpleZeroSimplePole X` holds.

**Significance.** Half of item 16's full closure is now discharged:
the non-constancy is unconditional, and the degree-1 conclusion reduces
to a focused, single-statement analytic claim (fibre at 0 = {Q₁} +
0 regular). The classical content for the remaining sub-hypothesis is
**inverse function theorem applied to the chart pullback at a simple
zero** + **value characterization of `toRiemannSphere`** — both
standard, deferrable to a future chip.

Build: `LEAN_NUM_THREADS=1 lake env lean ...` clean. Zero `sorry`,
zero `axiom`.

## 2026-05-17 (very late late night) — Item 16 (`ofCurve_inj`) reduced to single classical hypothesis (~230 LOC across 2 chips, direct to `main`)

Two follow-on chips composing into a conditional closure of item 16
(`Jacobian.ofCurve_inj` under `0 < genus X`).

### Chip A: `Manifold/PrincDivWitnessExtraction.lean` (~80 LOC)

`exists_meromorphicNonzero_principalDivisorMap_of_mem_PrincDiv`:
for any `D ∈ PrincDiv X`, there exists a single
`f : MeromorphicNonzero X` such that `principalDivisorMap f = D`.

Uses `PrincDivHonestCandidateGerm_eq` and the `CommGroup` structure on
`MeromorphicNonzero.Germ X` to switch `PrincDiv X` from the
`AddSubgroup.closure`-of-generators form to the `range`-of-`AddMonoidHom`
form, then `Quotient.inductionOn` extracts a representative.

### Chip B: `Manifold/OfCurveInjFromDegreeOne.lean` (~150 LOC)

* `DegreeOneFromSimpleZeroSimplePole X` — named classical hypothesis:
  if `principalDivisorMap f = Div.single Q₁ - Div.single Q₂` for distinct
  `Q₁ Q₂`, then `f.toRiemannSphere` is a non-constant degree-1
  ω-smooth map. Classical content: local pole-extension construction
  (Forster §1.4) + degree counting on the regular fibre.

* `ofCurve_inj_under_genus_pos`: under `0 < genus X` and the named
  classical hypothesis `DegreeOneFromSimpleZeroSimplePole X`,
  `Function.Injective (Jacobian.ofCurve P)` holds.

**Proof chain (composing six prior chips):**

1. Suppose `ofCurve P Q₁ = ofCurve P Q₂` with `Q₁ ≠ Q₂`.
2. Unfold the quotient: `single Q₁ - single Q₂ ∈ PrincDiv X`.
3. Extract witness `f` via chip A.
4. Apply the named degree-1 hypothesis.
5. `bijective_of_degreeFiber_eq_one` (with the now-unconditional
   `ramificationSumEqualsDegree_holds_unconditional` +
   `surjective_of_NonConstant_Analytic_Manifold_holds`) gives
   `f.toRiemannSphere` bijective.
6. `bijectiveAnalyticIsBiholomorphism_holds X` (discharged today)
   gives `e : HolomorphicEquiv X RiemannSphere`.
7. `genus_eq_zero_iff_homeo_of_HolomorphicEquiv_RiemannSphere` (in
   tree from PullbackLinearEquiv route) + `RiemannSphere.toSphereHomeo`
   give `genus X = 0`.
8. Contradicts `0 < genus X`.

**Net state on item 16.** The polymorphic-X closure reduces to a
**single** named classical hypothesis (`DegreeOneFromSimpleZeroSimplePole X`),
which is itself a clean self-contained statement (no further sub-hypotheses
beyond the classical pole-extension + degree-counting content).

Build: both files single-file `LEAN_NUM_THREADS=1 lake env lean` clean.
Zero `sorry`, zero `axiom`.

## 2026-05-17 (very late late night) — `BijectiveAnalyticIsBiholomorphism` DISCHARGED (1 chip, ~240 LOC, direct to `main`)

New file `Manifold/BijectiveAnalyticToBiholomorphismDischarge.lean`
ships:

`bijectiveAnalyticIsBiholomorphism_holds (X : Type*) [compact connected
complex 1-manifold instances] : BijectiveAnalyticIsBiholomorphism X` —
**unconditional**.

This discharges the third of the four named-classical-input hypotheses
for item 14's forward direction
(`Manifold/BijectiveAnalyticToBiholomorphism.lean`):

1. `ramificationSumEqualsDegree_statement` — already discharged.
2. `Surjective_of_NonConstant_Analytic_Manifold` — already discharged.
3. **`BijectiveAnalyticIsBiholomorphism` — DISCHARGED HERE.**
4. `RiemannRochGenusZero` — still open.

### Proof structure (~240 LOC)

For globally bijective `ω`-smooth `f : X → Y` between compact connected
complex 1-manifolds:

* Build the homeomorphism via `Continuous.homeoOfEquivCompactToT2`
  (bijective + compact + T2 → continuous inverse).

* Per-point analytic local inverse from
  `ContMDiff.chartPullback_localInverse_of_injective` — uses
  `ContMDiff.deriv_chart_pullback_ne_zero_of_injective` (zz384) and
  mathlib's `HasStrictDerivAt.localInverse`.

* Show the chart pullback of `e⁻¹` equals the local-inverse `h` on a
  neighbourhood. The proof uses:
  - `g ∘ K = id` on a nbhd of `(chartAt y) y`, where
    `K := (chartAt x) ∘ e⁻¹ ∘ (chartAt y).symm` is the chart pullback
    of `e⁻¹`. Follows from `f ∘ e⁻¹ = id` and the chart `right_inv`.
  - Eventually-left-inverse of `h` at `K w` (using continuity of `K`
    at `(chartAt y) y` to ensure `K w` is near `(chartAt x) x`).
  - Conclusion: `h w = h (g (K w)) = K w`.

* Promote to `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e⁻¹ y` via the iff bridge
  `contMDiffAt_omega_iff_analyticAt_chart_pullback` (continuity of
  `e⁻¹` + analyticity of chart pullback).

* Package as `Diffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) X Y ω = HolomorphicEquiv X Y`.

**Significance.** Three of the four named-classical hypotheses for
item-14 strict closure on the forward direction are now discharged.
Only `RiemannRochGenusZero` (the genus-0 RR upper-bound piece) remains.
This also unlocks a path to item 16 (`ofCurve_inj`): if
`principalDivisorMap f = single Q₁ - single Q₂` with Q₁ ≠ Q₂, then
`f.toRiemannSphere` has degree 1, is bijective (by
`bijective_of_degreeFiber_eq_one`), and now upgrades to a
biholomorphism `X ≃ RiemannSphere`, forcing `genus X = 0` (via the
unconditional `PullbackLinearEquiv` route).

Build: `LEAN_NUM_THREADS=1 lake env lean
JacobianChallenge/Manifold/BijectiveAnalyticToBiholomorphismDischarge.lean`
clean. Zero `sorry`, zero `axiom`.

## 2026-05-17 (very late late night) — Period-lattice classical-inputs data structure (1 chip, ~90 LOC, direct to `main`)

New file `Manifold/C3PeriodLatticeClassicalInputs.lean` packages the
three named classical hypotheses (from
`PeriodLatticeSymplecticBundleClassical.lean`) into a single data
structure `C3PeriodLatticeClassicalInputs basis` parametrised over a
chosen ℂ-basis of holomorphic 1-forms:

```
structure C3PeriodLatticeClassicalInputs
    (basis : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) where
  cycleGens : Fin (2 * genus X) → (PeriodPairingData.ofSmoothCycle X).H1
  riemannBilinear : LinearIndependent ℝ
    (fun i => periodVector data basis (cycleGens i))
  homologySpans : ∀ γ, periodVector data basis γ ∈
    Submodule.span ℤ (Set.range (fun i => periodVector data basis (cycleGens i)))
```

Plus the headline constructor:

```
noncomputable def C3PeriodLatticeClassicalInputs.toBundle (cls) :
    PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) basis
```

via `PeriodLatticeSymplecticBundle.ofClassicalInputs`. Downstream code
can now cite a SINGLE named hypothesis "period-lattice classical
inputs exist" rather than threading three separate hypotheses.

**Significance.** Final period-lattice closure-path chip in the arc.
Together with the prior `PeriodLatticeSymplecticBundle.ofClassicalInputs`
(reducing the bundle to 3 named hypotheses) and
`abelHypothesis_of_abelJacobiDivHom_principal_zero` (reducing
`AbelHypothesis` to generator-only), the **period-lattice + Abel**
side of `C3FullInputSymp X` is now mechanically constructible from a
small classical-input set: `C3PeriodLatticeClassicalInputs basis`
plus the generator-only Abel theorem (one statement per
`MeromorphicNonzero X`). Only Jacobi inversion remains as an open
classical hypothesis.

Build: `LEAN_NUM_THREADS=1 lake env lean ...` clean. Zero `sorry`,
zero `axiom`.

## 2026-05-17 (very late late night) — `AbelHypothesis` from generators-only Abel input (1 chip, ~90 LOC, direct to `main`)

New file `Manifold/AbelHypothesisFromPrincipal.lean` shipping
`abelHypothesis_of_abelJacobiDivHom_principal_zero`:

```
theorem abelHypothesis_of_abelJacobiDivHom_principal_zero
    (B : AbelJacobiInputSymp α h)
    (h_princ : ∀ f : MeromorphicNonzero X,
        B.abelJacobiDivHom (principalDivisorMap f) = 0) :
    AbelHypothesis B
```

Strips the subgroup-closure bookkeeping from
`AbelHypothesis B = ∀ D ∈ PrincDiv X, B.abelJacobiDiv0Hom D = 0`,
reducing it to the **generator-only** statement
`∀ f, B.abelJacobiDivHom (principalDivisorMap f) = 0` — i.e. classical
Abel's theorem stripped of the additional `AddSubgroup.closure` shape.

The proof uses `AddSubgroup.closure_induction` to lift vanishing on
generators to vanishing on the full closure. The `Div`-level
`abelJacobiDivHom : Div X →+ AnalyticJacobianSymp …` (an `AddMonoidHom`)
handles the algebraic closure operations (`+`, `0`, `neg`) via
`map_add`, `map_zero`, `map_neg`.

**Significance.** This is the cleanest named-classical-input boundary
for the Abel side of `C3FullInputSymp X`. Combined with the prior
`PeriodLatticeSymplecticBundle.ofClassicalInputs` chip
(`PeriodLatticeSymplecticBundleClassical.lean`), constructing
`C3FullInputSymp X` for general genus now reduces to **three** named
classical hypotheses (plus the path-connectedness `AbelJacobiInputSymp`
which is already unconditional via `nonempty_of_connected`):

1. A tuple `cycleGens : Fin (2g) → SmoothCycle X` representing a
   symplectic homology basis (the H₁ ≅ ℤ^{2g} classical theorem).
2. Riemann bilinear non-degeneracy of the periods of `cycleGens`.
3. Generator-only Abel vanishing
   (`∀ f, abelJacobiDivHom (principalDivisorMap f) = 0`).

Plus `JacobiInversion` (theta-divisor surjectivity) for the full bundle.

Build: `LEAN_NUM_THREADS=1 lake env lean ...` clean. Zero `sorry`, zero
`axiom`. Theorem uses an inline-`{X}`-instance signature (rather than a
`variable`-block) because Lean's instance synthesis was confused by
the auto-bound implicit `X` when `T2Space`/`CompactSpace` were declared
only via `variable`.

## 2026-05-17 (very late late night) — Period lattice classical-input constructor (1 chip, ~140 LOC, direct to `main`)

New file `Manifold/PeriodLatticeSymplecticBundleClassical.lean` shipping
the classical-input boundary for `PeriodLatticeSymplecticBundle`:

* `finrank_real_pi_fin_complex (g : ℕ) : finrank ℝ (Fin g → ℂ) = 2 * g`
  — via `Module.finrank_pi_fintype` + `Complex.finrank_real_complex` +
  `Fintype.card_fin`.

* `PeriodLatticeSymplecticBundle.ofClassicalInputs` — given a tuple
  `cycleGens : Fin (2 * genus X) → data.H1` of cycle generators
  together with two named classical hypotheses:
  - `h_LI : LinearIndependent ℝ (periodVector ∘ cycleGens)` — Riemann
    bilinear non-degeneracy of the periods.
  - `h_span : ∀ γ : data.H1, periodVector γ ∈ Submodule.span ℤ
    (Set.range (periodVector ∘ cycleGens))` — the chosen tuple's
    period vectors ℤ-span the period image (classically: chosen
    homology classes generate H₁, plus Stokes for boundaries).
  Produces a full `PeriodLatticeSymplecticBundle data α`. The
  `periodBasis` field is constructed via `Basis.mk` on `h_LI` plus
  the dimension count `Fintype.card (Fin (2g)) = 2g = finrank ℝ
  (Fin g → ℂ)`, using `LinearIndependent.span_eq_top_of_card_eq_finrank'`
  (the `'`-form that requires only `FiniteDimensional ℝ (Fin g → ℂ)`,
  not `[Nonempty (Fin 2g)]` — so the genus-0 case flows through
  identically).

**Significance.** This is the cleanest named-classical-input
boundary for the period-lattice side of `C3FullInputSymp X`.
Previously, downstream consumers had to construct the full
`PeriodLatticeSymplecticBundle` shape (a tuple + a basis + a
compatibility statement + a spanning statement). With this chip, the
construction reduces to **two** named classical hypotheses, both of
which are standard textbook content: Riemann bilinear non-degeneracy
+ H₁ generation by a chosen tuple. The bundle construction itself is
now mechanical.

Builds: `LEAN_NUM_THREADS=1 lake env lean
JacobianChallenge/Manifold/PeriodLatticeSymplecticBundleClassical.lean`
clean; zero `sorry`, zero `axiom`.

## 2026-05-17 (very late late night) — `fStarOmegaHolOn` punctured-ball differentiability (1 chip, ~100 LOC, direct to `main`)

New file `Manifold/FStarOmegaHolOnPuncturedDifferentiableOn.lean`
(100 LOC) shipping the **boundedness-input precursor** for the
`HolomorphicTraceExtension X` item-(2) globalize step:

`fStarOmegaHolOn_localCoeff_differentiableOn_punctured_ball` —
for `f : MeromorphicNonzero X` non-constant, `α : HolomorphicOneForm X`,
and any critical value `v₀ ∈ f.criticalValues`, there exists a chart
radius `ρ > 0` such that the chart-target ball
`Metric.ball ((chartAt ℂ v₀) v₀) ρ` is contained in `(chartAt ℂ v₀).target`,
and on the *punctured* ball, the chart-`v₀` local coefficient of
`f.fStarOmegaHolOn hnc α` is `DifferentiableOn ℂ`.

The proof composes two prior chips:

* `chart_radius_shrink_only_v₀_critical`
  (`Manifold/CriticalValueChartShrink.lean`): gives `ρ > 0` with the
  chart-target ball mapping (under `(chartAt ℂ v₀).symm`) into the
  union of `regularValueSet` and `{v₀}`.

* `HolomorphicOneFormOn.localCoeff_differentiableOn_chartImage`
  (`Manifold/HolomorphicOneFormOnChartCoeff.lean`): gives
  `DifferentiableOn ℂ` on the chart image of
  `regularValueSet ∩ (chartAt ℂ v₀).source`.

The punctured ball lies in this chart image because `(chartAt ℂ v₀).symm`
is injective on `(chartAt ℂ v₀).target` (via `right_inv`), so excluding
the puncture `(chartAt ℂ v₀) v₀` forces the chart-shrink dichotomy into
its regular branch.

**Significance.** Together with the prior bundle-wiring chip
(`removable_extension_analyticAt_of_traceExtensionChartCoeff_eventuallyEq`),
this is the manifold-side input for the removable-singularity step: the
local coefficient is `DifferentiableOn ℂ` on the punctured ball
(established here), and *also* matches the algebraic descent's
`Q (v - w₀) / k` on the punctured ball (the substantive bundle-wiring
identification, still open). Once both are in tree, the
`HolomorphicOneFormOn` extends to `HolomorphicOneForm RiemannSphere`
at every critical value via the new removable-extension API — with no
boundedness hypothesis needing to be exposed at the call site.

Build: `LEAN_NUM_THREADS=1 lake env lean
JacobianChallenge/Manifold/FStarOmegaHolOnPuncturedDifferentiableOn.lean`
clean; zero `sorry`, zero `axiom`.

## 2026-05-17 (very late late night) — Bundle-wiring removable singularity bridge (1 chip, ~95 LOC, direct to `main`)

New file `Manifold/TraceExtensionRemovableSingularity.lean` (98 LOC)
combining the prior `RemovableSingularityAdapter` agreement lemmas with
`traceExtensionChartCoeff` (`Q v / k`, the algebraic-descent output of
chip 3d-5/3d-6) into bundle-wiring-ready theorems:

* `analyticAt_Q_sub_const` — for `Q : ℂ → ℂ` analytic at `0`,
  `fun v => Q (v - w₀)` is analytic at `w₀`. Via `AnalyticAt.comp_of_eq'`
  with the affine `id - const`.

* `analyticAt_traceExtensionChartCoeff_sub_const` — the candidate
  extended chart-coefficient `v ↦ Q (v - w₀) / k` is analytic at `w₀`
  for `k ≥ 1`.

* `removable_extension_analyticAt_of_traceExtensionChartCoeff_eventuallyEq`
  — **one-shot bundle-wiring lemma**: if a scalar `g : ℂ → ℂ` matches
  `v ↦ Q (v - w₀) / k` on a punctured nbhd of `w₀`, the canonical
  removable extension is `AnalyticAt w₀`. No boundedness hypothesis
  needs to be supplied by the caller.

* `removable_extension_value_of_traceExtensionChartCoeff_eventuallyEq` —
  the value of the extension at `w₀` is `Q 0 / k`. Direct via
  `sub_self` + `rfl` on `traceExtensionChartCoeff_apply`.

**Significance.** Together with the prior `RemovableSingularityAdapter`
chip, this is the **direct downstream-friendly endpoint** for the
algebraic-descent → manifold-extension bridge: a bundle-wiring chip
that identifies the chart-pulldown of `f.fStarOmegaHol hnc α` near a
critical value `v₀` of `f` (on a *punctured* chart-disc) with the
algebraic-descent expression now has a one-line theorem to produce the
analytic chart-coefficient on the *full* chart-disc, with explicit
value at `v₀`.

Build: `LEAN_NUM_THREADS=1 lake env lean
JacobianChallenge/Manifold/TraceExtensionRemovableSingularity.lean`
clean; zero `sorry`, zero `axiom`.

## 2026-05-17 (very late late night) — RemovableSingularityAdapter: analytic-continuation agreement (1 chip, ~55 LOC, direct to `main`)

Three new theorems in `Manifold/RemovableSingularityAdapter.lean` bridging
the algebraic descent's `Q v / k` (an `AnalyticAt 0` analytic continuation
of the trace 1-form's chart-coefficient across a critical value) to the
canonical removable-singularity extension. No boundedness or
differentiability hypothesis needs to be supplied to the downstream
caller when an analytic continuation `q` is already in hand:

* `removable_extension_value_of_analyticAt_eventuallyEq` — under
  `AnalyticAt ℂ q c` and `g =ᶠ[𝓝[≠] c] q`,
  `removable_extension g c c = q c`. Proof: `q` is continuous at `c`,
  so `q` tends to `q c` along `𝓝[≠] c`; `g` matches `q` there, so `g`
  has the same limit; `limUnder` reads off this limit (using the
  automatic `NeBot (𝓝[≠] c)` instance for `c : ℂ` from
  `NontriviallyNormedField.nhdsNE_neBot`).

* `removable_extension_eventuallyEq_of_analyticAt` — under the same
  hypotheses, `removable_extension g c =ᶠ[𝓝 c] q`. Combines the
  punctured-nbhd `removable_extension_apply_of_ne` (definitional via
  `Function.update_of_ne`) with the value-at-`c` lemma above.

* `removable_extension_analyticAt_of_analyticAt_eventuallyEq` — the
  streamlined corollary: `AnalyticAt ℂ (removable_extension g c) c`
  follows from `AnalyticAt ℂ q c` and `g =ᶠ[𝓝[≠] c] q` via
  `AnalyticAt.congr`. No boundedness hypothesis is required on `g`.

**Significance.** The trace-extension chart coefficient
`traceExtensionChartCoeff Q k = fun v => Q v / k`
(`Manifold/TraceExtensionChartCoeff.lean`) is `AnalyticAt 0`. The
algebraic descent chip 3d-3
(`hurwitz_cyclic_sum_descent_oneForm_divided` from
`HurwitzCyclicSumDescentOneFormDivided.lean`) identifies it with the
chart-pulldown of `f.fStarOmegaHol hnc α` near a critical value `w₀` on
a *punctured* chart-disc. The new corollary
`removable_extension_analyticAt_of_analyticAt_eventuallyEq`
then immediately delivers the extension across `w₀`, modulo the
bundle-wiring chips identifying the chart-pulldown with the algebraic
expression. This is the cleanest possible interface for the next-chip
arc consuming the algebraic descent to construct the global
`HolomorphicOneForm RiemannSphere` extension of `fStarOmegaHolOn`.

Build: zero `sorry`, zero `axiom`, single-file `LEAN_NUM_THREADS=1 lake
env lean` clean.

## 2026-05-17 (very late night) — Jacobian RiemannSphere manifold instances + genus-0 generalisation (6 chips, ~850 LOC, direct to `main`)

Follow-on to the late-late-night symplectic migration. Lifts the
analytic-Jacobian content from `JacobianAnalyticChoiceSymp X` to the
actual `JacobianChallenge.Jacobian RiemannSphere` (= `Pic⁰ RS`) via
the closure path `Subsingleton (Pic0 RiemannSphere)` → all 7
structural manifold instances on `Jacobian RiemannSphere`. Then
generalises to any genus-0 X with `[Subsingleton (Pic0 X)]`.

### Chip 12 — Pic0 RS subsingleton + CompactSpace on Jacobian RS (~75 LOC, `4d73cf0`)
- `instance : Subsingleton (Pic0 RiemannSphere)`.
- `instance : Subsingleton (Jacobian RiemannSphere)`.
- `instance : CompactSpace (Jacobian RiemannSphere)` via
  `Subsingleton.compactSpace`.

### Chip 13 — Full manifold instances on Jacobian RS (~165 LOC, `d4e2ee4`)

The key insight: mathlib has `contMDiff_of_subsingleton` (any function
into a subsingleton manifold is `ContMDiff`) and
`OpenPartialHomeomorph.singletonChartedSpace` +
`singleton_hasGroupoid` (single-chart atlas auto-compatible with any
`ClosedUnderRestriction` groupoid — including `contDiffGroupoid n I`).
Pushed through mathlib API names previously gotten wrong:
- `OpenPartialHomeomorph` (the open variant) — not `PartialHomeomorph`.
- `IsManifold = HasGroupoid M (contDiffGroupoid n I)` extension —
  construct via `IsManifold.mk'`.
- `LieAddGroup.contMDiff_neg` / `ContMDiffAdd.contMDiff_add` — the
  legacy `smooth_add`/`smooth_neg` are gone.

Ships:
- `trivialChart_RiemannSphere : OpenPartialHomeomorph (Jacobian RS)
  (Fin 0 → ℂ)`.
- `instance ChartedSpace … (Jacobian RS)` via
  `OpenPartialHomeomorph.singletonChartedSpace`.
- `instance IsManifold (𝓘(ℂ, Fin 0 → ℂ)) ω (Jacobian RS)` via
  `singleton_hasGroupoid` + `IsManifold.mk'`.
- `instance ContMDiffAdd … (Jacobian RS)` + `instance LieAddGroup …
  (Jacobian RS)` via `contMDiff_of_subsingleton`.
- `ofCurve_contMDiff_RiemannSphere` — same.

### Chip 14 — Generalise smoothness content to any X with subsingleton Jacobian (~95 LOC, `934a371`)

Lifts the smoothness instances (`ContMDiffAdd`, `LieAddGroup`,
`ofCurve_contMDiff_of_subsingleton_jacobian`) to any X with
`[Subsingleton (Jacobian X)]` and accompanying `ChartedSpace` /
`IsManifold` instances. All route through `contMDiff_of_subsingleton`.

### Chip 15 — Lift Charted/IsManifold to general genus-0 X (~135 LOC, `353c704`)

Generalises the charted-space + manifold construction to any X with
`genus X = 0` + `[Subsingleton (Pic0 X)]`:
- `subsingleton_fin_genus_to_complex_holds (hgenus : genus X = 0)`.
- `compactSpace_Jacobian_holds [Subsingleton (Pic0 X)]`.
- `trivialChart_Jacobian hgenus` — single OpenPartialHomeomorph
  between two subsingleton spaces.
- `chartedSpace_Jacobian_holds hgenus [Subsingleton (Pic0 X)]`.
- `isManifold_Jacobian_holds` via parent-class promotion `{ __ := hg
  }` from a `HasGroupoid`.

RS recovers via `genus_RiemannSphere_eq_zero` +
`subsingleton_pic0_RiemannSphere`. Any future genus-0 X (e.g. via
uniformization to RS) inherits the full manifold structure on
`Jacobian X` by supplying those two hypotheses.

### Chip 16 — OPEN.md state update (`6fe91b7`)

Documents the migration arc + new entry points + remaining closure
path. Scoreboard unchanged at 13/24 — explicitly states the
remaining structural blocker (placeholder discrete topology on
`Pic0 X` cannot honestly support unconditional `CompactSpace`
at general genus in Basic.lean's verbatim signature).

### Net state after migration

Full RS closure path in tree end-to-end. The structural rewrite of
`JacobianChallenge.Jacobian X`'s topology (discrete → analytic-quotient
under `[Nonempty (C3FullInputExtSymp X)]`) is the remaining gap to
flip items 11/5/12/13/17 — all the analytic content is now available.

Build clean throughout (warm 2740-8593 jobs). Zero `sorry`, zero `axiom`.

## 2026-05-17 (late late night) — Symplectic-bundle migration of the AJ chain (7 chips, ~1305 LOC, direct to `main`)

Follow-on to the late-night `PeriodLatticeSymplecticBundle` refactor.
Lifts the full Abel-Jacobi chain (`AbelJacobiPath` → `AbelJacobiPoint`
→ `AbelJacobiDiv` → `AbelJacobiPic0` → `AbelJacobiIso` → `C3FullInput`
→ `C3FullInputExt` → `JacobianAnalyticChoice`) to the corrected
symplectic bundle. The legacy `PeriodLatticeDiscretenessBundle`'s
`h1Basis : Basis (Fin 2g) ℤ data.H1` is dead code at every genus for
`data = ofSmoothCycle X`, so this migration moves the closure-relevant
chain onto the actually-inhabitable bundle.

### Chip 5 — `AbelJacobiInputSymp` + path/chain AJ (~180 LOC, `42555ec`)

`Manifold/AbelJacobiPointSymp.lean`: `abelJacobiPathSymp` +
`_eq_of_shared_endpoints` + `abelJacobiChainSymp` (`AddMonoidHom`) +
`AbelJacobiInputSymp` structure + `abelJacobiPoint` / `relAbelJacobi`
+ `AbelJacobiInput.toSymp`.

### Chip 6 — `C3FullInputSymp` + full divisor-/Pic⁰-level chain (~480 LOC, `24efbc8`)

`Manifold/C3FullInputSymp.lean`: full mirror of the legacy
`abelJacobiDiv` → `AbelHypothesis` → `JacobiInversion` →
`abelJacobiEquiv` chain. `C3FullInputSymp` 5-field bundle +
instance-discharge helpers + `C3FullInput.toSymp` conversion.
Per-point / per-divisor identity bridges (`toSymp_abelJacobiPoint_eq`
/ `toSymp_abelJacobiDiv_eq`) exploit `AnalyticJacobian =
AnalyticJacobianSymp` definitional equality at the
`(Fin g → ℂ) ⧸ periodLatticeImage` level.

### Chip 7 — `C3FullInputExtSymp` (~230 LOC, `ccc41b7`)

`Manifold/C3FullInputExtSymp.lean`: `AbelJacobiSmoothnessSymp` (item
17) + `AbelJacobiInjectiveSymp` (item 16) + `C3FullInputExtSymp`
3-field structure + `C3FullInputExt.toSymp`.

### Chip 8 — `JacobianAnalyticChoiceSymp` + 7 instances + `picZeroEquivSymp` (~130 LOC, `0c72dde`)

`Manifold/JacobianAnalyticChoiceSymp.lean`: `chosenC3Symp` via
`Classical.choice`, `JacobianAnalyticChoiceSymp` abbrev, all 7
structural typeclass instances (items 3, 4, 5, 10, 11, 12, 13), and
`picZeroEquivSymp : Pic⁰ X ≃+ JacobianAnalyticChoiceSymp X`.

### Chip 9 — Genus-0 / RS chain (~155 LOC, `f2e01b3`)

`Manifold/Pic0RiemannSphereSymp.lean`: `Subsingleton.analyticJacobianSymp_of_genus_zero`,
`abelHypothesis_of_genus_zero`, `jacobiInversion_of_genus_zero_and_subsingleton_pic0`,
`abelJacobiEquiv_of_genus_zero`, `abelJacobiEquiv_of_RiemannSphere`,
`abelJacobiEquiv_of_RiemannSphere_unconditional`.

### Chip 10 — Path-connectedness discharges (~85 LOC, `c5b9fc2`)

`Manifold/SmoothPathConnectedSymp.lean`: `ofSmoothPathConnected`,
`nonempty_of_smoothPathConnected`, `nonempty_of_preconnected`,
`nonempty_of_connected`.

### Chip 11 — RS-specific `AbelJacobiInputSymp` existence (~45 LOC, this commit)

`Manifold/SmoothPathConnectedRiemannSphereSymp.lean`:
`nonempty_abelJacobiInputSymp_RiemannSphere` — unconditional
existence on `RiemannSphere`.

### Net state after migration

The symplectic chain is now usable end-to-end as a parallel of the
legacy chain. Every legacy → symplectic transition has a `toSymp`
witness. The genus-0 + RS-unconditional path
(`AbelJacobiInputSymp.abelJacobiEquiv_of_RiemannSphere_unconditional`)
is in tree. The Basic.lean items 4, 5, 10, 11, 12, 13 STUB →
STRICT-CLOSED flip has a documented closure path via
`Nonempty (C3FullInputExtSymp X)` + `picZeroEquivSymp` (analogue of
the legacy `picZeroEquiv`), now resting on the corrected bundle.

The remaining gap is the same as before — discharging the classical
content of `AbelHypothesis` + `JacobiInversion` + `AbelJacobiSmoothness`
+ `AbelJacobiInjective` at general genus. The migration makes those
discharges target the actually-inhabitable bundle.

Build clean throughout. Zero `sorry`, zero `axiom`.

## 2026-05-17 (late night) — Period-lattice bundle refactor: PeriodLatticeSymplecticBundle (4 chips, ~400 LOC, direct to `main`)

Architectural refactor addressing a latent bug in
`PeriodLatticeDiscretenessBundle`: the legacy bundle declares
`h1Basis : Basis (Fin (2 * genus X)) ℤ data.H1`. For the canonical
`data = PeriodPairingData.ofSmoothCycle X`, `data.H1 = SmoothCycle X`
is the **full submodule of smooth 1-cycles** — infinite-dimensional
over `ℤ` for any non-trivial `X` (uncountably many smoothly inequivalent
loops). The legacy bundle's `ofBundle` construction path is therefore
**dead code at every genus**: no inhabitant of the legacy bundle is
classically producible. The genus-0 chips earlier this evening had
to bypass `ofBundle` for exactly this reason.

The corrected design replaces the over-strong basis condition with a
**tuple** of `2g` cycle generators + a **geometric** ℤ-span condition
on their period vectors (every cycle's period vector lies in the
ℤ-span of the chosen tuple's periods — classically, "the chosen tuple
represents the homology classes" + Stokes, where boundaries have zero
period).

This session lands the new bundle side-by-side with the legacy bundle,
re-derives the downstream `DiscreteTopology` / `IsZLattice ℝ`
identifications, validates the genus-0 case flows through the bundle
cleanly (no bypass needed), and mirrors the full
`JacobianOfLatticeFromBundle` pipeline.

### Chip 1 — `PeriodLatticeSymplecticBundle` + genus-0 trivial constructor (~250 LOC, `77220bb`)

New file `Manifold/PeriodLatticeSymplecticBundle.lean`:

* `PeriodLatticeSymplecticBundle` — corrected bundle:
  - `cycleGenerators : Fin (2 * genus X) → data.H1` (a tuple, not a basis)
  - `periodBasis : Basis (Fin (2 * genus X)) ℝ (Fin (genus X) → ℂ)`
    (unchanged)
  - `periodBasis_eq` compat (unchanged)
  - `period_image_spanned : ∀ γ, periodVector γ ∈ Submodule.span ℤ (range periodBasis)`
    — the corrected geometric content.
* `range_periodBasis_eq_image` — counterpart of legacy lemma.
* `periodLatticeImage_toIntSubmodule_eq_span_periodBasis` — re-proved
  via `period_image_spanned` (replacing `h1Basis.span_eq` reliance).
* `periodLatticeImage_discreteTopology_of_bundle` /
  `_isZLattice_of_bundle` — derived `DiscreteTopology` + `IsZLattice ℝ`.
* `PeriodLatticeDiscretenessBundle.toSymplectic` — legacy → new
  conversion (legacy is strictly stronger).
* `PeriodLatticeSymplecticBundle.trivial_at_genus_zero` — validates
  the refactor: trivially constructible at genus 0 (empty tuple,
  empty basis, vacuous compat, every-period-is-0 spanning).

### Chip 2 — `PeriodLatticeAnalyticHypotheses.ofSymplecticBundle` + genus-0 `PeriodLatticeOfRankTwoG` (~40 LOC, `6513416`)

* `PeriodLatticeAnalyticHypotheses.ofSymplecticBundle` — parallel of
  legacy `.ofBundle`, builds the full analytic-hypotheses bundle
  via `ofDiscrete` + chip-1 derivations.
* `PeriodLatticeOfRankTwoG.ofGenusZeroSymplectic` — headline: at
  genus 0, `PeriodLatticeOfRankTwoG.ofPeriodPairing` fires
  unconditionally via the trivial bundle.

### Chip 3 — Bundle-route equals bypass at genus 0 (~40 LOC, `9387996`)

* `periodLatticeImage_eq_bot_of_genus_zero` — direct consequence of
  subsingleton ambient: every `AddSubgroup` of `Fin 0 → ℂ` is `⊥`.
* `PeriodLatticeOfRankTwoG.ofGenusZeroSymplectic_lattice` — the
  lattice field of the bundle-route construction equals `⊥`,
  matching the `PeriodLatticeOfRankTwoG.trivialAtGenusZero` bypass
  in `Manifold/PeriodLatticeRiemannSphere.lean`.

### Chip 4 — Full parallel pipeline: `PeriodLatticeOfRankTwoG.ofSymplectic` + `AnalyticJacobianSymp` (~70 LOC, `2bf40e1`)

Mirrors `Manifold/JacobianOfLatticeFromBundle.lean`:

* `PeriodLatticeOfRankTwoG.ofSymplectic` — parallel of `.ofBundle`.
* `PeriodLatticeOfRankTwoG.ofSymplectic_compactSpace` /
  `_chartedSpace` — parallel of the per-bundle discharges.
* `AnalyticJacobianSymp` abbrev — parallel of `AnalyticJacobian`.

The full corrected pipeline is now in tree, from the bundle up to
the analytic-Jacobian type + structural typeclass instances.

### Net state

The new pipeline works at **all genera** (legacy was structurally
dead). Genus-0 case unconditionally constructible. The refactor is
side-by-side: no existing consumers were modified. Next steps to
complete the refactor: `AbelJacobiInputSymp`, `C3FullInputSymp`,
`C3FullInputExtSymp`, `JacobianAnalyticChoiceSymp` (each is a
mechanical replication of the legacy structure with the new bundle).

Build: 8993 jobs, zero `sorry`, zero `axiom`.

## 2026-05-17 (late evening) — Item 14 + analytic-Jacobian-for-RS arc (10 chips, ~645 LOC, direct to `main`)

Four follow-on chips on top of the day's 36-chip arc, all reducing the
hypothesis count on item 14's two legs.

### Chip 1 — `pathPrimitiveFTC_of_basis` (~60 LOC, `ac38c8b`)

`pathPrimitiveFTC_of_basis` lands the previously-deferred FTC counterpart
to `pathPrimitiveSmoothness_of_basis` in
`Manifold/PathPrimitiveBasisFTC.lean`. With this, `PathPrimitiveFTC`
reduces to a per-basis-element check, paralleling the smoothness
reduction. Both `PathPrimitiveSmoothness` and `PathPrimitiveFTC` of item
14's reverse leg are now factored through a ℂ-basis of
`HolomorphicOneForm X`.

Mechanics: `Submodule.span_induction` with predicate `fun v _ => v.eval
x = mfderiv (pathPrimitive v) x`. Zero case via `eval_zero` +
`pathPrimitive_zero` + `mfderiv_const`. Add case via `eval_add` +
`pathPrimitive_add` + `mfderiv_add` (using `MDifferentiableAt`
obtained from `PathPrimitiveSmoothness` derived upfront via
`pathPrimitiveSmoothness_of_basis`). Smul case via `eval_smul` +
`pathPrimitive_smul` + `const_smul_mfderiv`.

Gotcha: `Submodule.span_induction` leaves the predicate un-beta-reduced
at the `zero` branch, so an explicit `show (0 : HolomorphicOneForm X).eval
x = …` before the rewrite chain is required. `fun y => f y + g y` is NOT
definitionally `f + g` for the purpose of `mfderiv_add` pattern-matching
(even though `Pi.add_apply` is `rfl`); an explicit `funext` rewrite
bridges them. After `mfderiv_add` / `const_smul_mfderiv`, the final
goal is `LHS = LHS` and needs a terminal `rfl`.

Build: 8987 jobs, zero `sorry`, zero `axiom`.

### Chip 2 — `genus0ImpliesS2_from_existsSimplePoleGerm` (~75 LOC, `f773489`)

New file `Topology/Item14ForwardFromCompactConnected.lean` lifts the
three theorems of `Item14ForwardFromFiniteDim.lean` to variants that
drop the `[FiniteDimensional ℂ (HolomorphicOneForm X)]` typeclass
argument. Since item 1 became STRICT-CLOSED today
(`holomorphicOneFormFiniteDim_holds` unconditional on compact connected
complex 1-manifolds), the FiniteDimensional typeclass is derivable
internally via `finiteDimensional_of_HolomorphicOneFormFiniteDim ∘
DiskChartCover.holomorphicOneFormFiniteDim_holds`.

Net effect for item 14's forward leg: only
`ExistsSimplePoleGermAtSomePoint X` (+ `S2ImpliesGenus0 X` for the
bundled biconditional) remains as a hypothesis.

Build: 8988 jobs.

### Chip 3 — `s2ImpliesGenus0_from_subsingletonOfSimplyConnected` (~75 LOC, `a949ddb`)

New file
`Topology/S2ImpliesGenus0FromSubsingletonHypothesis.lean` drops the
`SimplyConnectedS2` premise from `s2ImpliesGenus0_from_simplyConnected`
(unconditional via `simplyConnectedS2_holds`, the 15-chip Phase-3
smoothing arc), and assembles the bundled biconditional through to
`genus_eq_zero_iff_homeo_from_subsingletonOfSimplyConnected`.

Net for the simple-connectedness route: only **two** classical inputs
remain — `ExistsSimplePoleGermAtSomePoint X` (forward) and
`HolomorphicOneFormSubsingletonOfSimplyConnected X` (reverse).

Build: 8989 jobs.

### Chip 4 — `s2ImpliesGenus0_of_basisPathPrimitive` (~115 LOC, `2d934b6`)

New file
`Topology/S2ImpliesGenus0FromPrimitiveExistenceUnconditional.lean`
drops `SimplyConnectedS2` from `s2ImpliesGenus0_of_primitiveExistence`,
and provides the **finest-grained reverse leg**: given any ℂ-basis of
`HolomorphicOneForm X` plus the three per-basis-element analytic
hypotheses (`LoopPeriodVanishes`, `ContMDiff ω` of `pathPrimitive`,
FTC at `eval`), assembles the named
`HolomorphicOneFormSubsingletonOfSimplyConnected X` predicate via the
chip-1 basis-reductions, then composes through to `S2ImpliesGenus0 X`.

Three theorems:
* `s2ImpliesGenus0_of_primitiveExistence_uncond`
* `holomorphicOneFormSubsingletonOfSimplyConnected_of_basisPathPrimitive`
* `s2ImpliesGenus0_of_basisPathPrimitive`

`[FiniteDimensional ℂ (HolomorphicOneForm X)]` is derived internally,
so callers see only the three per-basis-element analytic statements +
the chosen basis (or implicitly via `Module.finBasis`).

Build: 8990 jobs, zero `sorry`, zero `axiom`.

### Chip 5 — `S2ImpliesGenus0 RiemannSphere` unconditional (~30 LOC, `b97941b`)

New file
`Topology/HolomorphicOneFormSubsingletonOfSimplyConnectedRS.lean`
discharges two named hypotheses unconditionally on `RiemannSphere`:

* `holomorphicOneFormSubsingletonOfSimplyConnected_riemannSphere` —
  trivial since `Subsingleton (HolomorphicOneForm RiemannSphere)` is
  unconditional via `Manifold/RiemannSphereChartSCoeffOverlap.lean`,
  so the simply-connectedness premise is vacuous.
* `s2ImpliesGenus0_riemannSphere` — composes with chip 3's
  `s2ImpliesGenus0_from_subsingletonOfSimplyConnected` (which uses
  `simplyConnectedS2_holds` internally). Both classical inputs to the
  simple-connectedness route to the reverse leg of item 14 are now
  discharged unconditionally on RS.

Build: 8991 jobs.

### Chip 6 — Item 14 unconditional on RiemannSphere (~26 LOC, `fc44f2f`)

Extends the same file with the full RS-specialised biconditional via
the substantive proof chain:

* `genus0ImpliesS2_riemannSphere` — composes chip 2's
  `genus0ImpliesS2_from_existsSimplePoleGerm` (with
  `[FiniteDimensional]` derived internally) with the unconditional
  `existsSimplePoleGermAtSomePoint_RiemannSphere`.
* `surfaceClassificationGenus_riemannSphere` — bundles both directions.
* `genus_eq_zero_iff_homeo_riemannSphere` — the headline biconditional
  with zero external hypotheses, via the substantive
  simple-connectedness + simple-pole-germ chain.

(Note: the trivial direct discharge already exists in
`Topology/Item14ForRiemannSphere.lean`. This chip provides the
substantive-chain validation that the full forward/reverse leg
infrastructure composes correctly end-to-end on RS.)

Build: 8991 jobs, zero `sorry`, zero `axiom`.

### Chips 7-10 — Analytic Jacobian for RiemannSphere unconditional (~235 LOC)

Architectural breakthrough: the `PeriodLatticeDiscretenessBundle.ofBundle`
route to `PeriodLatticeOfRankTwoG` is **structurally blocked at genus 0**
— it requires `h1Basis : Basis (Fin 0) ℤ (SmoothCycle 𝓘(ℝ, ℂ) RS)`,
which forces `SmoothCycle 𝓘(ℝ, ℂ) RS = 0` (false; SmoothCycle is
non-trivial even when its homology classes collapse to 0). The bundle
encodes a stricter classical condition than the geometric statement.

Pivot: build `PeriodLatticeOfRankTwoG RiemannSphere` **directly**,
bypassing the bundle. New file
`Manifold/PeriodLatticeRiemannSphere.lean`.

**Chip 7** (`cee9147`, ~115 LOC): `PeriodLatticeOfRankTwoG.trivialAtGenusZero`
+ `periodLatticeOfRankTwoG_RiemannSphere` + `DiscreteTopology` /
`IsZLattice ℝ` instances on the trivial lattice (via
`Subsingleton.discreteTopology` + subsingleton-ambient argument) +
`compactSpaceHypothesis_holds_RiemannSphere` (specialises
`PeriodLatticeOfRankTwoG.compactSpaceHypothesis_holds`).

**Chip 8** (`f8c1138`, ~30 LOC):
`chartedSpaceHypothesis_holds_RiemannSphere` +
`lieAddGroupHypothesis_holds_RiemannSphere` — completes the trio of
hypothesis-bundle discharges needed for the analytic-Jacobian
instances.

**Chip 9** (`8b81d5c`, ~50 LOC): `AnalyticJacobianRiemannSphere` —
concrete `Type` (= `JacobianOfLattice RS periodLatticeOfRankTwoG_RS`)
+ 7 structural instances: `AddCommGroup`, `TopologicalSpace`,
`T2Space`, `CompactSpace`, `ChartedSpace`, `IsManifold`, `LieAddGroup`
— all landing unconditionally via the per-bundle wiring. This is the
RS-specialised parallel to `JacobianAnalyticChoice X` (which requires
`[Nonempty (C3FullInputExt X)]`).

**Chip 10** (`dfa96fc`, ~40 LOC): `Subsingleton AnalyticJacobianRiemannSphere`
+ `picZeroEquiv_RiemannSphere : Pic⁰ RS ≃+ AnalyticJacobianRiemannSphere`
— both sides subsingleton (via `subsingleton_pic0_RiemannSphere` and
the quotient-of-subsingleton argument), so the AddEquiv is trivially
constructible.

Net effect: items **3, 4, 5, 10, 11, 12, 13** of Buzzard's spec
(`AddCommGroup`, `TopologicalSpace`, `ChartedSpace`, `T2Space`,
`CompactSpace`, `IsManifold`, `LieAddGroup` on the Jacobian) are now
**unconditionally discharged on `AnalyticJacobianRiemannSphere`** —
the RS-specialised analytic-Jacobian type. Wiring this through to
`Basic.lean`'s `Jacobian X = Pic⁰ X` for `X = RS` requires the
`picZeroEquiv_RiemannSphere` AddEquiv (now in-tree) plus
topology-transport along it (future chip).

Build: 8992 jobs.

## 2026-05-17 (afternoon → evening) — Item 1 STRICT-CLOSED + C3 cascade + Item 14 reverse-leg arc (36 chips, ~3700 LOC, direct to `main`)

Major session. Three arcs landed on top of the late-morning
functoriality work.

### Arc A — Forster density-bound + Riesz finale → item 1 STRICT-CLOSED (12 chips, ~1430 LOC)

`HolomorphicOneFormFiniteDim X` is now **unconditional** on a compact
connected complex 1-manifold. Item 1 (`genus X := finrank ℂ (HolomorphicOneForm X)`)
flips from STUB to **STRICT-CLOSED** (scoreboard: 12 → 13 / 24).

Chips:
1. `DiskChartCoverDensityCoverage.lean` (125 LOC) — X-side outer disk
   compact + inner sets open + coverage.
2. `DiskChartCoverDensityTransition.lean` (95 LOC) — transition factor
   + `ContinuousOn` on chart overlap.
3. `DiskChartCoverDensityIdentity.lean` (130 LOC) — per-point localCoeff
   transition identity via `cotangentBundleCore_coordChange_apply` +
   tangent cocycle + ℂ-linearity.
4. `DiskChartCoverDensityPointwiseBound.lean` (65 LOC) — norm form +
   inequality.
5. `DiskChartCoverDensityTransitionBound.lean` (73 LOC) — uniform
   transition bound on compact overlap subsets.
6. `DiskChartCoverDensityClosedInner.lean` (140 LOC) — closed inner
   disk in X + per-pair density bound on outer ∩ closed-inner.
7. `DiskChartCoverDensityPerX.lean` (100 LOC) — per-y bound aggregated
   to `seminormValInner`.
8. `DiskChartCoverDensityAggregate.lean` (165 LOC) — **headline**
   `∃ M, seminormVal ≤ M · seminormValInner`.
9. `DiskChartCoverRiesz.lean` (115 LOC) — `localCoeffBcf_limitHolomorphicOneForm`
   compatibility for `limitHolomorphicOneForm`.
10. `DiskChartCoverFiniteDim.lean` (170 LOC) — Riesz finale: outer
    closed ball seq-compact → compact → `FiniteDimensional.of_isCompact_closedBall₀`
    → `holomorphicOneFormFiniteDim_holds` unconditional.

### Arc B — C3 cascade: items 4, 5, 10, 11, 12, 13, 16, 17, 18, 21 on the analytic Jacobian (10 chips, ~1090 LOC)

Conditional discharges of ten OPEN.md items on the analytic Jacobian
under named classical inputs.

Chips:
* `C3RewireBundle.lean` (75 LOC) — `C3PeriodLatticeAnalyticInput X` +
  `periodLatticeOfRankTwoG_of_input`.
* `C3FullInput.lean` (85 LOC) — full bundle: basis + discreteness +
  ajInput + abel + jacobi; `abelJacobiEquiv` extraction.
* `C3FullInputInstances.lean` (~100 LOC) — `compactSpaceHypothesis`
  (item 11), `chartedSpaceHypothesis` (items 5 + 12),
  `lieAddGroupHypothesis` (item 13) on analytic Jacobian.
* `C3FullInputExt.lean` (95 LOC) — extended bundle (+ smoothness +
  injective); `toClosureBundle` → `JacobianAnalyticClosureBundle`.
* `C3FullInputExtClosures.lean` (115 LOC) — items 16, 17 closures.
* `C3FullInputCurve.lean` (170 LOC) — per-curve bundle (per-`f`
  push/pull lattice-match certificates); `toPushforwardLift` /
  `toPullbackLift` extractions.
* `C3FullInputCurveClosures.lean` (140 LOC) — items 18, 21
  `Nonempty`-form lift existence.
* `JacobianAnalyticChoice.lean` (115 LOC) — `JacobianAnalyticChoice X`
  type alias via `Classical.choice` from `[Nonempty (C3FullInputExt X)]`;
  carries `AddCommGroup`, `TopologicalSpace`, `T2Space`, `CompactSpace`,
  `ChartedSpace`, `IsManifold`, `LieAddGroup` instances. `picZeroEquiv`
  AddEquiv to `Pic⁰ X`.

With these, items 4, 5, 10, 11, 12, 13, 16, 17, 18, 21 are
*conditionally* discharged on the analytic Jacobian. Flipping
Basic.lean's `Jacobian X = Pic⁰ X` requires instance transport along
`picZeroEquiv` (deferred — needs Homeomorph upgrade or full rewire,
which itself requires `Nonempty (C3FullInputExt X)` unconditional —
i.e., the full classical period-lattice + Abel-Jacobi content).

### Arc C — Item 14 reverse leg structural reduction (10 chips, ~870 LOC)

Reduces `HolomorphicOneFormSubsingletonOfSimplyConnected X` to **per-
basis-element** classical inputs.

Chips:
* `PrimitiveOnSmoothPathConnected.lean` (~150 LOC) — `pathPrimitive` via
  `Classical.choice` from `SmoothPathConnected`; `LoopPeriodVanishes`
  named hypothesis; well-definedness modulo path choice.
* `PrimitiveSubsingletonReduction.lean` (~90 LOC) —
  `Subsingleton (HolomorphicOneForm X)` from three named hypotheses
  (`AllLoopsVanish`, `PathPrimitiveSmoothness`, `PathPrimitiveFTC`).
* `PrimitiveRiemannSphere.lean` (~75 LOC) — all three named hypotheses
  unconditional on `RiemannSphere` (Subsingleton ⇒ vacuous).
* `PathPrimitiveLinear.lean` (~130 LOC) — `pathPrimitive_zero/add/neg/smul`
  + `pathPrimitiveLinearMap : HolomorphicOneForm X →ₗ[ℂ] ℂ`.
* `PathPrimitiveBasisReduction.lean` (~100 LOC) —
  `loopPeriodVanishes_of_spanning` + `allLoopsVanish_of_basis`:
  `AllLoopsVanish` factors through a ℂ-basis via `Submodule.span_induction`.
* `PathPrimitiveBasisFTC.lean` (~70 LOC) — `pathPrimitiveSmoothness_of_basis`
  (FTC basis-reduction sketched but deferred).
* `LoopPeriodConstant.lean` (~40 LOC) — `complexChainPeriod_const_loop`
  unconditional.

Net structural state of item 14 reverse leg: reduces to **3 × g**
per-basis-element classical inputs (`LoopPeriodVanishes`, `ContMDiff ω`,
FTC at the `eval` level), each a concrete analytic statement about one
specific holomorphic 1-form.

### Build state

Build green at 8987 jobs (up from 8959), zero `sorry`, zero `axiom`.
Repo total: ~126,700 LOC across 696 files (up from ~120,800 LOC / 643
files at session start).


> **Note on dates (audit 2026-05-16):** Earlier sessions wrote
> *future-dated* labels driven by anchoring on inflated dates in prior
> memory files instead of the system `currentDate`. The CHANGELOG
> headers below were remapped on 2026-05-16 to match git-timestamp
> reality:
>
> - originally `2026-05-15` headers → real `2026-05-14`,
> - originally `2026-05-16` headers → real `2026-05-15`,
> - originally `2026-05-17`/`2026-05-18`/`2026-05-19-afternoon`/-`—` → real `2026-05-15`,
> - originally `2026-05-19-late-afternoon`/`-evening`/`2026-05-20` → real `2026-05-16`.
>
> Git commit timestamps are the authoritative source; the labels here
> now reflect them. A `feedback_check_system_currentDate.md` memory
> documents the root cause and prevention for future sessions.

## 2026-05-17 (late morning) — Pushforward/Pullback functoriality + PeriodPairingMorphism (id, comp) (7 chips, ~697 LOC, direct to `main`)

A bundled functoriality arc completing the (id, comp) pair on three
levels: `SmoothPath`/`Chain`/`Cycle.push`, `PeriodPairingMorphism`,
and the dual `pullbackLinearLift` / `JacobianAnalyticPullbackLift`
canonical constructors. With this arc, both sides of the
pushforward/pullback per-curve pair have canonical-`T` constructors
and matching functoriality witnesses.

### Chip-by-chip

* **Chip 1** `SmoothCyclePushComp.lean` (102 LOC, `aa88f58`). The
  composition pair at three levels:
  - `SmoothPath.push_comp` — `push (g ∘ f) γ = push g (push f γ)` via
    `Path.map_map` + structure congruence (smooth field is `Prop` so
    proof-irrelevant).
  - `SmoothChain.push_comp` — `ℤ`-linear-map equality via
    `Finsupp.lhom_ext` + `lmapDomain_apply` + `mapDomain_single`.
  - `SmoothCycle.pushHom_comp` — `AddMonoidHom` equality on cycles.

* **Chip 2** `PeriodPairingMorphismComp.lean` (98 LOC, `254d1c2`).
  General composition `PeriodPairingMorphism.comp` over arbitrary
  `PeriodPairingData`. `f := g ∘ f`, `cyclePush := cyclePush_g.comp
  cyclePush_f`, adjunction via `adj_g`, `adj_f`,
  `← HolomorphicOneForm.pullback_comp`. Companion `@[simp]` lemmas
  `comp_f` and `comp_cyclePush`.

* **Chip 3** `PeriodPairingMorphismIdGeneral.lean` (58 LOC, `cb40d8d`).
  General identity `PeriodPairingMorphism.id` over arbitrary
  `PeriodPairingData`. `f := id`, `cyclePush := AddMonoidHom.id`,
  adjunction via `HolomorphicOneForm.pullback_id`. Companion `@[simp]`
  lemmas `id_f` and `id_cyclePush`. Sister to the previously-existing
  `id'_ofSmoothCycle` (the `ofSmoothCycle`-specialised variant).

* **Chip 4** `SmoothCyclePushId.lean` (77 LOC, `83c8a16`). The
  identity pair at three levels:
  - `SmoothPath.push_id` — `push id γ = γ` (via `Path.map_id` under
    `congr 1`, which closes automatically since `Path.map_id` is
    `@[simp]`).
  - `SmoothChain.push_id` — equals `LinearMap.id`.
  - `SmoothCycle.pushHom_id` — equals `AddMonoidHom.id`.

* **Chip 5** `PeriodPairingMorphismCompOfSmoothCycle.lean` (109 LOC,
  `bc71ae0`). Specialisation of `comp` for `ofSmoothCycle`-style
  inputs: takes two holomorphic curve maps + period adjunctions for
  the canonical `SmoothCycle.pushHom` cyclePush, builds the composite
  with `cyclePush := SmoothCycle.pushHom (g ∘ f) _` (the canonical
  `ofSmoothCycle` form, NOT the bare `pushHom g . pushHom f` that the
  generic `comp` would deliver). Uses `SmoothCycle.pushHom_comp` +
  proof-irrelevance for `ContMDiff.complex_to_real` witness threading.

* **Chip 6** `HolomorphicOneFormPullbackLinearLift.lean` (139 LOC,
  `c14f5fd`). Defines `pullbackLinearLift αX αY f hf` as the CLM
  `(Fin gY → ℂ) →L[ℂ] (Fin gX → ℂ)` via
  `Matrix.mulVecLin (pullbackMatrix αX αY f hf)` (no transpose, unlike
  pushforward). Functoriality witnesses parallel `pushforwardLinearLift`:
  `pullbackLinearLift_id` (equals `ContinuousLinearMap.id`),
  `pullbackLinearLift_const` (equals `0`), `pullbackLinearLift_comp`
  (contravariant `T_{g ∘ f} = T_f ∘ T_g`). Plus
  `pullbackLinearLift_apply` definitional.

* **Chip 7** `JacobianAnalyticPullbackLiftOfCurveCanonical.lean`
  (98 LOC, `45b695c`). Canonical-`T` variant of
  `JacobianAnalyticPullbackLift.ofCurveMap` fixing `T` to
  `pullbackLinearLift` (no caller choice). Sister to
  `JacobianAnalyticPushforwardLift.ofCurveMap`. Companion `@[simp]`
  lemmas `ofCurveMapCanonical_T` and `_f`.

### Build state

All 7 chips verified via single-file `LEAN_NUM_THREADS=1 lake env lean`
then full `taskpolicy -b nice -n 19 env LEAN_NUM_THREADS=1 lake build`
(8958–8959 jobs across the arc). Zero `sorry`, zero `axiom`, zero
linter warnings (one transient `show`→`change` style nag fixed
mid-iteration on chip 1).

Manifest `JacobianChallenge.lean` updated with all 7 imports.

### Items flipped

None — items 4, 5, 10, 11, 12, 13, 16, 17, 18, 21 in `Basic.lean` still
STUB/OPEN. The functoriality arc is infrastructure that lands underneath
the (still-pending) C3 rewire of `Jacobian X` to `AnalyticJacobian X _ _`.
With these chips, the eventual `JacobianAnalyticPushforwardLift.ofMorphism_id`
and `_comp` bridge lemmas (mapping `PeriodPairingMorphism.id`/`.comp`
through `ofMorphism` into `JacobianAnalyticPushforwardLift.id'`/`.comp`)
become straightforward structural matches.

### Gotchas surfaced

* `Path.map_map` and `Path.map_id` are `@[simp]` in mathlib, so
  `congr 1` on `SmoothPath.mk` constructor equality closes the toPath
  goal automatically — explicit `exact Path.map_map _` lines produce
  "No goals to be solved" errors.
* `SmoothCycle.pushHom` consumes a `ContMDiff I I ∞ f` argument, but
  `ContMDiff` is `Prop`; two distinct smoothness proofs give
  definitionally-equal `pushHom` applications by proof-irrelevance, so
  bridging `ContMDiff.complex_to_real (hg.comp hf)` and
  `(complex_to_real hg).comp (complex_to_real hf)` is `rfl`.
* `ext c` on an `AddMonoidHom` equality between `pushHom`-style maps
  produces the underlying-value goal directly; no need for an
  intervening `apply Subtype.ext` (it errors with "could not unify").
* `show ...` is now linter-flagged when it changes the goal; use
  `change ...` instead.

## 2026-05-17 — E+F cluster: LieAddGroup discharge + ContMDiff building blocks + items 16/17/18/21 predicates (8 chips, ~1,020 LOC, direct to `main`)

Implements the **E + F cluster** from `CLOSURE_MAP.md` §F.5 step 4
("`Basic.lean` instance bodies + smoothness lemmas") at the
**analytic-Jacobian level**. The cluster discharges OPEN.md item 13's
named hypothesis, ships the ContMDiff-on-quotient building block for
items 18, 21, and surfaces items 16 and 17 as named-hypothesis
predicates `AbelJacobiInjective` and `AbelJacobiSmoothness`. Items 4,
5, 10, 11, 12, 13 on `Jacobian X` and items 16, 17, 18, 21 in
`Basic.lean` flip via this cluster the moment C3 supplies the
`Pic⁰ X ≃+ AnalyticJacobian X` rewire.

Net effect: **item 13's content is now unconditional** on
`(Fin g → ℂ) ⧸ L` for any ℤ-lattice `L`, and **items 18, 21 reduce**
to "the holomorphic curve map `f : X → Y` induces a ℂ-linear lift on
covers matching period lattices" — the C3-adjacent content that
remains. **Items 16, 17 are surfaced as named predicates** with
documented discharge routes (Abel's theorem for 16, C1 chart-cover
lift + FTC for 17), giving Basic.lean a clean per-item handle.

### Chip-by-chip

* **Chip 1** `Manifold/PeriodLatticeMkQContMDiff.lean` (~140 LOC). The
  quotient projection `L.mkQ : (Fin g → ℂ) → (Fin g → ℂ) ⧸ L` is
  `ContMDiff 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin g → ℂ) n` for every
  `n : WithTop ℕ∞`. Atlas membership of `(localChart L _ x).symm` plus
  `contMDiffOn_symm_of_mem_maximalAtlas` plus `localChart` agreeing
  with `L.mkQ` on its source. The cornerstone for all downstream
  smoothness arguments.

* **Chip 2** `Manifold/PeriodLatticeLieGroupAdd.lean` (~230 LOC). Two
  headline theorems:
  - `add_contMDiff_complex` — `+ : G × G → G` is `ContMDiff` for the
    complex model, where `G := (Fin g → ℂ) ⧸ L`.
  - `neg_contMDiff_complex` — `Neg.neg : G → G` is `ContMDiff`.

  Plus two registered instances:
  - `contMDiffAdd_quotient_of_zlattice` — `ContMDiffAdd 𝓘(ℂ, Fin g → ℂ) n G`.
  - `lieAddGroup_quotient_of_zlattice` — `LieAddGroup 𝓘(ℂ, Fin g → ℂ) n G`.

  Proof structure: locally near any `(q₁, q₂)`, addition reads as
  `(a, b) ↦ mkQ (chartAt q₁ a + chartAt q₂ b)` — composition of
  `chartAt q_i` (ContMDiffOn on source), `+_E : E × E → E` (ContMDiff,
  standard), `mkQ` (ContMDiff, Chip 1). Negation mirrors. Discharges
  OPEN.md item 13's content on the lattice-quotient construction
  unconditionally.

* **Chip 3** `Manifold/PeriodLatticeOfRankTwoG_LieGroupWiring.lean`
  (~76 LOC). Wires Chip 2's `lieAddGroup_quotient_of_zlattice` through
  to the `PeriodLatticeOfRankTwoG` bundle's `LieAddGroupHypothesis`
  field. Sister to `_Wiring` (item 11) and `_ComplexWiring` (items
  5 + 12). With all three wired, the **complete named-hypothesis trio**
  on `PeriodLatticeOfRankTwoG` is unconditional once
  `[DiscreteTopology] [IsZLattice ℝ]` instance arguments are supplied.

* **Chip 4** `Manifold/PeriodLatticeLinearQuotient.lean` (~180 LOC).
  Headline theorem `quotientLinearMap_contMDiff`: for ℤ-lattices
  `L ⊆ (Fin g₁ → ℂ)` and `L' ⊆ (Fin g₂ → ℂ)` and a ℂ-linear
  `T : (Fin g₁ → ℂ) →L[ℂ] (Fin g₂ → ℂ)` with `T '' L ⊆ L'`, the
  induced quotient map `quotientLinearMap L L' T hT` is
  `ContMDiff 𝓘(ℂ, Fin g₁ → ℂ) 𝓘(ℂ, Fin g₂ → ℂ) n`. The **building block
  for OPEN.md items 18 and 21**: every analytic-Jacobian-level
  pushforward and pullback factors through such a quotient map.
  Construction via `Submodule.mapQ` + lifted-form
  `L'.mkQ ∘ T ∘ chartAt q` smoothness.

* **Chip 5** `Manifold/JacobianAnalyticOfCurveContMDiff.lean` (~98 LOC).
  Named-hypothesis predicate
  `AbelJacobiSmoothness B := ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin g → ℂ) ω
    (B.abelJacobiPoint : X → AnalyticJacobian _ α h)`,
  with `[DiscreteTopology] [IsZLattice]` instance arguments. **OPEN.md
  item 17's analytic-Jacobian-level content.** Discharge route: C1
  chart-cover lift + FTC for complex line integrals.

* **Chip 6** `Manifold/JacobianAnalyticOfCurveInjective.lean` (~86 LOC).
  Named-hypothesis predicate
  `AbelJacobiInjective B := 0 < genus X →
    Function.Injective (B.abelJacobiPoint : X → AnalyticJacobian _ α h)`.
  **OPEN.md item 16's analytic-Jacobian-level content.** Discharge
  route: Abel's theorem on compact Riemann surfaces (C4 content).
  Corollary `relAbelJacobi_injective` for the relative map.

* **Chip 7** `Manifold/JacobianAnalyticPushforwardPullbackContMDiff.lean`
  (~80 LOC). Repackaging `quotientLinearMap_contMDiff` (Chip 4) at the
  AnalyticJacobian shape: `analyticJacobian_linearLift_contMDiff`
  takes a ℂ-linear cover lift `T : (Fin g_X → ℂ) →L[ℂ] (Fin g_Y → ℂ)`
  carrying `data_X.lattice` into `data_Y.lattice` and produces the
  ContMDiff statement for the induced map between AnalyticJacobians.
  **Items 18 and 21's analytic-Jacobian-level content** modulo the
  per-curve construction of `T_f`.

* **Chip 8** `Manifold/JacobianAnalyticClosureBundle.lean` (~97 LOC).
  Composite named-hypothesis bundle
  `JacobianAnalyticClosureBundle α h` aggregating
  `AbelJacobiSmoothness` (item 17) and `AbelJacobiInjective` (item 16)
  for a single downstream consumer point. Item 18/21 lifts live as
  per-curve hypotheses (sister structure noted but not yet packaged,
  since their shape depends on `Y` as well).

### Build state

All 8 chips checked via single-file `LEAN_NUM_THREADS=1 lake env lean`.
Zero `sorry`, zero `axiom`. Two warnings in
`PeriodLatticeLinearQuotient.lean` are about unused-but-required
section variables (linter false positive on private helpers).

Manifest `JacobianChallenge.lean` updated with all 8 imports.

### Items flipped / surfaced

| Item | Status before | Status after |
|---|---|---|
| 13 (`LieAddGroup`) — named-hypothesis bundle field | Conditional on unwritten classical fact | **Unconditional** on `(Fin g → ℂ) ⧸ L`; `lieAddGroupHypothesis_holds` discharge |
| 18 (`pushforward_contMDiff`) — building block | Not in tree | **Unconditional** `quotientLinearMap_contMDiff` |
| 21 (`pullback_contMDiff`) — building block | Not in tree | **Unconditional** `quotientLinearMap_contMDiff` |
| 17 (`ofCurve_contMDiff`) — analytic-Jacobian content | Not in tree | **Named-hypothesis predicate** `AbelJacobiSmoothness` |
| 16 (`ofCurve_inj`) — analytic-Jacobian content | Not in tree | **Named-hypothesis predicate** `AbelJacobiInjective` |

Items 4, 5, 10, 11, 12, 13 in `Basic.lean` itself remain at their prior
status (STUB / OPEN), because flipping them requires the C3 rewire of
`Jacobian X` to `AnalyticJacobian X _ _`. **The E+F cluster's role**
is to make all of these flips one-line `inferInstance` / one-`exact`
discharges once C3 lands.

## 2026-05-16 (late night) — `HolomorphicTraceExtension X` item-(2) descent + Hurwitz form arc (32 chips, ~2,660 LOC, direct to `main`)

Builds on the night's algebraic foundation to ship the full pure-
analytic content of item (2): cyclic-sum descent through `ξ^k`, Hurwitz
local normal form, analytic local inverse, composed source-side z-form
identity, divided chart-coefficient form, and bundle-level bridge at a
fibre point.

* **Chip 3b-4** `CyclicSumFactorKthPowerDescent.lean` (~75 LOC). The
  descent headline: combining the night's
  `cyclicSum_factor_pow_k_sub_one_cyclic_invariant` with the existing
  `analyticAt_descent_of_mu_k_invariant`, produces `Q : ℂ → ℂ`
  analytic at `0` with
  `cyclicSum h ω k ξ = ξ^(k-1) · Q(ξ^k)` eventually.
  Conversion from "∀ᶠ ξ, ∀ j ∈ range k" to "∀ ζ, ζ^k = 1 → ..." uses
  `IsPrimitiveRoot.eq_pow_of_pow_eq_one`.

* **Chip 3b-5** `CyclicSumFactorKthPowerDescentKthRoot.lean` (~100 LOC).
  Re-quantification over `v = ξ^k`: openness of `ξ ↦ ξ^k` at `0` gives
  `∀ᶠ v in 𝓝 0, ∀ ξ, ξ^k = v → cyclicSum h ω k ξ = ξ^(k-1) · Q v`.
  Helper `eventually_forall_pow_kth_root_mem_of_mem_nhds` packages
  "preimage of any 𝓝 0 under ξ ↦ ξ^k is a 𝓝 0".

* **Chip 3c-1** `HurwitzLocalForm.lean` (~115 LOC). Composes
  `analytic_local_factorization` (gives `g - w₀ = (z-x₀)^k · u`) and
  `analytic_kth_root_of_nonvanishing` (gives analytic `r` with
  `r^k = u`) to produce the Hurwitz local normal form:
  `g z - w₀ = ψ z^k` with `ψ z := (z-x₀) · r z`, `ψ x₀ = 0`,
  `deriv ψ x₀ = r x₀ ≠ 0`. Derivative via `HasDerivAt` product rule.

* **Chip 3c-2** `HurwitzLocalFormInverse.lean` (~95 LOC). Strengthens
  `hurwitz_local_form` with an analytic local inverse `φ` at `0`
  (mathlib's `AnalyticAt.analyticAt_localInverse`). Outputs `φ 0 = x₀`
  and the two eventual identities `ψ (φ s) = s`, `φ (ψ z) = z`.

* **Chip 3c-3** `HurwitzCyclicSumDescent.lean` (~95 LOC). Composes
  chip 3c-2 with chip 3b-4: for any analytic `h` at `x₀`, the
  transported coefficient `h ∘ φ` is analytic at `0`, so the descent
  produces `Q` analytic at `0` with
  `cyclicSum (h ∘ φ) ω k ξ = ξ^(k-1) · Q(ξ^k)` eventually.

* **Chip 3c-4** `HurwitzCyclicSumDescentKthRoot.lean` (~80 LOC).
  Target-side k-th root form of chip 3c-3: re-quantifies over
  `v = ξ^k` while keeping the same `Q`. Direct composition of 3c-3
  with the openness helper.

* **Chip 3c-5** `HurwitzCyclicSumDescentZForm.lean` (~95 LOC). Source-
  side z-form: pulls the target-side eventual back to `∀ᶠ z in 𝓝 x₀`
  via `Tendsto.eventually` applied to `z ↦ (ψ z)^k`, then specialises
  at `ξ := ψ z` and substitutes `(ψ z)^k = g z - w₀` from the Hurwitz
  identity. Final form:
  `∀ᶠ z in 𝓝 x₀, cyclicSum (h ∘ φ) ω k (ψ z) = (ψ z)^(k-1) · Q(g z - w₀)`.

* **Chip 3c-6** `HurwitzZetaLocalNonzero.lean` (~50 LOC). Local non-
  vanishing `ψ z ≠ 0` for `z ≠ x₀` near `x₀`. From the eventual left
  inverse `φ (ψ z) = z` and `ψ x₀ = 0`: if `ψ z = 0 = ψ x₀`, then
  `z = φ (ψ z) = φ (ψ x₀) = x₀`. Specialising at `x₀` uses
  `Filter.Eventually.self_of_nhds`.

* **Chip 3c-7** `HurwitzCyclicSumDescentZFormDivided.lean` (~115 LOC).
  Divided form of the source-side z-form descent: combines the kth-root
  form (which exposes `h_left`) with the non-vanishing chip to yield

    `∀ᶠ z in 𝓝 x₀, z ≠ x₀ →`
    `   cyclicSum (h ∘ φ) ω k (ψ z) / ((↑k) · (ψ z)^(k-1)) = Q (g z - w₀) / ↑k`.

  Closes the chart-coefficient form of the trace 1-form `f_*α` near a
  critical value: LHS = source-fibre cyclic-sum normalised by
  `k · (ψ z)^(k-1)`, RHS = `Q (g z - w₀) / k` analytic across `w₀`.

* **Chip 3d-1** `CriticalFibreCyclicSumDescent.lean` (~105 LOC).
  Manifold-level bridge: specialises the pure-analytic z-form descent
  to `g := f.chartPullback z₀` and `h := α.localCoeff z₀`, with both
  analyticities supplied by `analyticAt_chartPullback` and
  `localCoeff_analyticAt_chart_image`. Primitive-root binder renamed
  to `ζ` to avoid clashing with the `ω` `ContDiff` smoothness-level
  notation needed for `IsManifold (𝓘(ℂ, ℂ)) ω X`.

* **Chip 3d-2** `HurwitzCyclicSumDescentOneForm.lean` (~100 LOC).
  **1-form-corrected** descent: chips 3c-3..3d-1 use `h ∘ φ` as cyclic-
  sum input (correct for function pullback but omits the Jacobian
  factor for 1-form pullback). This chip uses
  `H := (h / deriv ψ) ∘ φ`, which equals `λ s, h(φ s) · φ'(s)` —
  the correct 1-form chart-coefficient transform. Uses
  `AnalyticAt.deriv` and `AnalyticAt.div`.

* **Chip 3d-3** `HurwitzCyclicSumDescentOneFormDivided.lean` (~140 LOC).
  **1-form-corrected divided form**, the chart-coefficient
  identification:

    ∀ᶠ z in 𝓝 x₀, z ≠ x₀ →
      cyclicSum ((h / deriv ψ) ∘ φ) ω k (ψ z) / ((↑k) · (ψ z)^(k-1))
        = Q (g z - w₀) / ↑k.

  Because chip 3d-2's φ is existentially packed, this chip rebuilds
  the construction from scratch using `hurwitz_local_form_with_inverse`
  directly to expose `h_left` for chip 3c-6.

* **Chip 3d-4** `CriticalFibreOneFormDescent.lean` (~100 LOC).
  Manifold-level 1-form-corrected divided form: parallel to 3d-1 but
  for chip 3d-3. The final pure-analytic-plus-chart-pullback chart-
  coefficient identification chip before the sheet / cotangent-
  pullback identification on the source side.

* **Chip 3d-5** `TraceExtensionChartCoeff.lean` (~50 LOC). Packages
  `Q v / ↑k` as `traceExtensionChartCoeff Q k` with apply lemma and
  analyticity at 0 (via `AnalyticAt.div` with constant).

* **Chip 3d-6** `TraceExtensionChartCoeffOnDisc.lean` (~30 LOC).
  Extracts an explicit positive radius `r > 0` with
  `AnalyticOnNhd ℂ (traceExtensionChartCoeff Q k) (Metric.closedBall 0 r)`
  via `AnalyticAt.exists_ball_analyticOnNhd` + closed-ball-of-half-radius.

* **Chip 3d-7** `HurwitzFibreImageIdentity.lean` (~65 LOC). Planar fibre-
  image identity `g(φ(ζ^j · ξ)) - w₀ = ξ^k` from `ψ ∘ φ = id eventually`
  and `(ζ^j · ξ)^k = (ζ^k)^j · ξ^k = ξ^k`.

* **Chip 3d-8** `HurwitzFibreInjective.lean` (~80 LOC). Planar fibre-point
  distinctness: `φ(ζ^j₁ · ξ) ≠ φ(ζ^j₂ · ξ)` for distinct j₁, j₂ ∈ range k
  and ξ ≠ 0, via `Filter.eventually_all_finset` + ψ left-inverse +
  `IsPrimitiveRoot.pow_inj`.

* **Chip 3d-9** `HurwitzManifoldFibreImage.lean` (~70 LOC). Manifold-level
  fibre-image identity: lifts chip 3d-7 through `(chartAt ℂ z₀).symm`,
  conclusion `f.toRiemannSphere (lift) = (chartAt ℂ (f z₀)).symm (ξ^k + w₀)`.

* **Chip 3d-10** `HurwitzManifoldFibreInjective.lean` (~50 LOC). Manifold-
  level fibre-point distinctness via chart-symm right-inverse on target.

* **Chip 3d-11** `HurwitzManifoldFibreEnumeration.lean` (~80 LOC). Packaged
  manifold-level fibre enumeration: image + distinctness for `j ∈ range k`.

* **Chip 3d-12** `HurwitzDerivFormula.lean` (~85 LOC). Hurwitz derivative
  formula `deriv g w = ↑k · ψ(w)^(k-1) · deriv ψ w` for `w ∈ ball x₀ R`,
  via `HasDerivAt.pow` on ψ + `HasDerivAt.const_add` for `w₀ + ψ^k` +
  `congr_of_eventuallyEq` transport. Companion `hurwitz_deriv_ne_zero`.

* **Chip 3d-13** `HurwitzDerivPsiNonzero.lean` (~40 LOC). Eventual
  `deriv ψ z ≠ 0` near x₀ via `AnalyticAt.deriv` continuity +
  `ContinuousAt.eventually_ne`.

* **Chip 3d-14** `HurwitzPlanarFRegularity.lean` (~50 LOC). Combines
  chips 3c-6, 3d-12, 3d-13 to give `deriv g z ≠ 0` for `z` near `x₀`,
  `z ≠ x₀`, `z ∈ ball x₀ R`.

* **Chip 3d-15** `HurwitzFibreRegularPlanar.lean` (~90 LOC). Eventual planar
  f-regularity at Hurwitz fibre points: for ξ ≠ 0 small,
  `deriv g (φ(ζ^j · ξ)) ≠ 0`. Tendsto pulled from chip 3d-14 via
  `ξ ↦ φ(ζ^j · ξ)`.

* **Chip 3d-16** `HurwitzFibreLocalInjOn.lean` (~55 LOC). Planar local
  injectivity at Hurwitz fibre points: composes chip 3d-15 +
  `AnalyticAt.exists_local_biholomorphism` + `LeftInvOn.injOn`. Takes
  caller-supplied `AnalyticAt ℂ g (φ(ζ^j · ξ))` hypothesis.

* **Chip 3d-17** `HurwitzManifoldFibreLocalInjOn.lean` (~60 LOC). Manifold-
  level InjOn lift from planar chart-pullback InjOn, via chart-equality
  manipulation.

* **Chip 3d-18** `HurwitzRegularSetFromInjOn.lean` (~30 LOC). Direct
  membership: `∃ U ∈ 𝓝 a, Set.InjOn f.toRiemannSphere U → a ∈ f.regularSet`
  (by definition of `regularSet`).

* **Chip 3d-19** `HurwitzManifoldFibreRegular.lean` (~80 LOC). Manifold
  f-regularity at chart-target points: composes chips 3d-16, 3d-17,
  3d-18; uses `OpenPartialHomeomorph.isOpen_image_symm_of_subset_target`
  for the manifold-side neighbourhood construction.

* **Chip 3d-20** `HurwitzManifoldFibreRegularEnumeration.lean` (~80 LOC).
  Packaging chip: manifold fibre enumeration (image, distinctness,
  regularity) for `j ∈ range k`.

* **Chip 3d-21** `ChartPullbackAnalyticAtTarget.lean` (~80 LOC) — **ZZ24**,
  the long-flagged owed chart-pullback-AnalyticAt-on-target lemma from
  `AnalyticContinuationGlobalization.lean`. For `w ∈ (chartAt ℂ z₀).target`
  with `f.toRiemannSphere ((chartAt ℂ z₀).symm w) ∈ (chartAt ℂ (f z₀)).source`:
  `AnalyticAt ℂ (f.chartPullback z₀) w`. Composition of `contMDiffOn_chart_symm`
  + `toRiemannSphere_contMDiff` + `contMDiffOn_chart` + `ContMDiffAt.comp`
  + `contMDiffAt_iff_contDiffAt` + `ContDiffAt.analyticAt`.

* **Chip 3d-22** `HurwitzManifoldFibreRegularUnconditional.lean` (~50 LOC).
  Composes chip 3d-19 with chip 3d-21 to discharge the AnalyticAt
  hypothesis. **Manifold f-regularity at chart-target points is now
  unconditional in tree** modulo the standard small-disc continuity
  argument for chart-source containment.

* **Chip 3d-23** `HolCotangentPullbackOne.lean` (~25 LOC). Building
  block for the per-sheet identification chip arc: definitional
  `holCotangentPullbackAt g y α = (α.toFun (g y)).comp (mfderiv g y)`
  exposed as a `@[simp]` lemma with explicit ℂ →L[ℂ] ℂ coercion.

Build green across all chips. Zero `sorry`, zero `axiom`.

**Net effect.** The complete pure-analytic foundation for item (2) of
`HolomorphicTraceExtension X` is now in tree. The remaining work is
the manifold/cotangent-bundle wiring: identify the source-chart
coefficient of α with `h`, the chart-pullback of `f` with `g`, the
chart of RS at the critical value with the target side, and bundle
the resulting `Q` as the chart coefficient of a `HolomorphicOneForm
RiemannSphere` extending `fStarOmegaHolOn`.

## 2026-05-16 (night) — `HolomorphicTraceExtension X` item-(2) algebraic foundation (11 chips, ~1501 LOC, direct to `main`)

Lays the complete algebraic foundation for item (2) of the
`HolomorphicTraceExtension X` closure plan: extension across critical
values of `f : X → ℙ¹` via n-th-root cancellation + Riemann removable
singularity. Closes prior dependencies and ships all the algebraic
content needed for the bounded-trace step; manifold-side wiring +
descent are split out for future sessions.

**Bridge primitives (3 chips, 594 LOC):**

* `JacobianChallenge/Manifold/RemovableSingularityAdapter.lean`
  (123 LOC) — Scalar `ℂ → ℂ` wrapper for
  `Complex.differentiableOn_update_limUnder_of_bddAbove`. Produces
  `removable_extension g c := Function.update g c (limUnder (𝓝[≠] c) g)`,
  `holomorphic_extend_of_bounded_on_punctured_nhd`, and
  `removable_extension_analyticAt`.
* `JacobianChallenge/Manifold/HolomorphicOneFormOnChartCoeff.lean`
  (340 LOC) — On-set analogue of `HolomorphicOneForm.localCoeff` plus
  the chart-target `ContMDiffOn ω` smoothness on
  `(chartAt ℂ y) '' (s ∩ chart.source)`. Cocycle work done inline,
  mirroring `HolomorphicOneFormChartCoeffOnTarget` with
  `ContMDiffWithinAt _ _ _ s _` where the global version had
  `ContMDiffAt`.
* `JacobianChallenge/Manifold/CriticalValueChartShrink.lean`
  (131 LOC) — For `v₀ ∈ f.criticalValues`, finds `ρ > 0` so that the
  ball `ball ((chartAt ℂ v₀) v₀) ρ` chart-pulls back to regular values
  plus `v₀` itself; single-puncture set-up for removable-singularity
  application.

**N-th-root cancellation algebraic core (8 chips, ~907 LOC):**

* `JacobianChallenge/Manifold/PrimitiveRootCyclicSum.lean` (87 LOC) —
  Roots-of-unity orthogonality
  `∑ j ∈ range k, ω^(j*m) = if k ∣ m then k else 0`, generic over a
  primitive `k`-th root of unity in any field plus the `ℂ`-specialisation
  via `Complex.isPrimitiveRoot_exp k h0`. The algebraic kernel of the
  n-th-root cancellation projection.
* `JacobianChallenge/Manifold/KthRootSubstitutionGeneral.lean`
  (122 LOC) — **Closes the previously named-only general-`k` gap.** For
  `g : ℂ → ℂ` analytic at `x₀` with analytic order `k ≥ 1` at `x₀ − w₀`,
  builds the substitution `v(z) := (z − x₀) · r(z)` where `r` is the
  analytic `k`-th root of the local factorisation's unit factor.
  Composes `analytic_local_factorization` + `analytic_kth_root_of_nonvanishing`
  (both already in the repo — the stale doc comment in
  `LocalKFoldMultiplicity.lean` had labelled them open).
* `JacobianChallenge/Manifold/CyclicSumSymmetry.lean` (121 LOC) —
  Definition `cyclicSum h ω k ξ := ∑ j ∈ range k, ω^j · h(ω^j · ξ)`
  and the symmetry identity
  `cyclicSum h ω k (ω · ξ) = ω⁻¹ · cyclicSum h ω k ξ`. Algebraic; proof
  reindexes `j ↦ (j + 1) mod k`, using `ω^k = 1` to wrap.
* `JacobianChallenge/Manifold/CyclicSumZeroAtZero.lean` (69 LOC) —
  First-order vanishing `cyclicSum h ω k 0 = 0` for `k ≥ 2` and any
  function `h`. Immediate from the symmetry at `ξ = 0`:
  `S(0) = ω⁻¹ · S(0)` with `ω⁻¹ ≠ 1`.
* `JacobianChallenge/Manifold/CyclicSumVanishingOrder.lean` (200 LOC)
  — **Vanishing to order `(k−1)`.** For analytic `h` at `0` and ω a
  primitive `k`-th root with `k ≥ 2`, builds the analytic factor `q`:
  `∃ q analytic at 0, cyclicSum h ω k ξ = ξ^(k-1) · q(ξ)` near `0`.
  Strategy:
  1. `cyclicSum` is analytic at `0` (`Finset.analyticAt_fun_sum` +
     composition with linear).
  2. Case-split via `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`:
     if `cyclicSum` is identically `0` near `0`, take `q := 0`; else
     get `m, g` with `cyclicSum = ξ^m · g` and `g(0) ≠ 0`.
  3. Symmetry at `ωξ`: `ω^m · ξ^m · g(ωξ) = ω⁻¹ · ξ^m · g(ξ)`. Cancel
     `ξ^m` on `𝓝[≠] 0`; take continuity at `0` to get
     `(ω^m − ω⁻¹) · g(0) = 0`. Since `g(0) ≠ 0`, force
     `ω^(m+1) = 1`, hence `k ∣ m + 1`, hence `m ≥ k − 1`.
  4. Factor `ξ^m = ξ^(k-1) · ξ^(m-(k-1))`; take
     `q(ξ) := ξ^(m-(k-1)) · g(ξ)`.
* `JacobianChallenge/Manifold/CyclicSumNormBounded.lean` (84 LOC) —
  Quantitative form of the previous: there exist `C, ρ > 0` with
  `‖cyclicSum h ω k ξ‖ ≤ C · ‖ξ‖^(k-1)` for `‖ξ‖ ≤ ρ`. From
  `q` continuous at `0`, get `‖q ξ‖ ≤ ‖q 0‖ + 1` on a small ball; the
  factorisation gives the conclusion. This is the bound that, applied
  at each preimage of a critical value `v₀` with ramification index
  `k`, cancels the `ξ^(1-k)` factor in the per-sheet trace contribution.
* `JacobianChallenge/Manifold/CyclicSumFactorOmegaInvariant.lean`
  (144 LOC) — **ω-invariance of the analytic factor**:
  `q(ω · ξ) = q(ξ)` near `0`. Pull the factorisation back along
  `ξ ↦ ω · ξ` and combine with the symmetry to derive
  `ω^k · q(ωξ) = q(ξ)` on the punctured neighbourhood. Lift to a full
  neighbourhood via `eventually_nhdsWithin_iff` + `by_cases ξ = 0` +
  `tendsto_nhds_unique` on the continuous extension. Sets up the
  descent of `q` to a function of `ξ^k`.
* `JacobianChallenge/Manifold/CyclicSumFactorGroupInvariant.lean`
  (80 LOC) — **Full cyclic-group invariance**:
  `∀ᶠ ξ in 𝓝 0, ∀ j ∈ Finset.range k, q(ω^j · ξ) = q ξ`. Induction on
  `j`: the inductive step pulls `q(ω^n · (ω · ξ)) = q(ω · ξ)` back
  along `ξ ↦ ω · ξ` and composes with the base ω-invariance via
  `ω^(n+1) · ξ = ω^n · (ω · ξ)`. The `k` eventual statements are
  collected into one via `Filter.eventually_all_finset`. Sets up the
  averaging operator `(P_k q)(ξ) := (1/k) ∑_{j ∈ range k} q(ω^j ξ)`
  needed in the descent step.

**Status (item (2) closure plan).** The algebraic foundation is now
COMPLETE. The remaining work is split as two heavier, multi-session
chips:

* **Descent (~300-500 LOC, `FormalMultilinearSeries` Taylor subseries)**
  — Given `q` ω-invariant and analytic at `0`, build the analytic `Q`
  with `q(ξ) = Q(ξ^k)`. Strategy: extract the Taylor series `p` of `q`
  via `HasFPowerSeriesOnBall`; ω-invariance forces `p_n = 0` for `k ∤ n`;
  define `c n := p.coeff (n*k)`; build `Q := ofScalarsSum (ofScalars ℂ c)`.
  Convergence radius of `Q` is `r^k` where `r` is the radius of `p`.
* **Manifold/cotangent-bundle wiring (~400-600 LOC)** — Per-preimage
  trace contribution via `KthRootSubstitution` at each critical
  preimage; express the per-sheet `α`-pullback sum in `v_p` chart
  coords as `(1/k_p) · ξ_p^{1-k_p} · cyclicSum h_p ω_p k_p ξ_p`. Apply
  `cyclicSum_norm_bounded` + `holomorphic_extend_of_bounded_on_punctured_nhd`
  to extend the trace 1-form across `v₀`.

**Gotchas surfaced in this session:**

* **`open scoped ContDiff` required** in MeromorphicNonzero contexts:
  without it, `IsManifold (𝓘(ℂ, ℂ)) ω X` parses but `criticalValues_finite`
  etc. fail with `IsManifold 𝓘(ℂ, ℂ) ⊤ X` synth.
* **`unfold_let` unavailable** on `set`-introduced locals; use `show`
  with the expanded form or `let` (which reduces by default).
* **`eventually_nhdsWithin_iff` + `by_cases` upgrade**: cleanest way to
  go from `∀ᶠ ξ in 𝓝[≠] 0, P ξ = 0` + `P 0 = 0` to
  `∀ᶠ ξ in 𝓝 0, P ξ = 0`. Avoids decomposing
  `𝓝 0 = pure 0 ⊔ 𝓝[≠] 0`.
* **`AnalyticAt.comp_of_eq'` for `fun z => g (f z)`**: argument is
  `(hg.comp_of_eq' hf (f x = y))` — hypothesis is `f x = y`, not
  `y = f x`. The `'`-version is for the `fun`-form; bare `comp_of_eq`
  is for `g ∘ f`.
* **`NeBot (𝓝[≠] (0 : ℂ))` is an auto-instance** via
  `nhdsNE_neBot` in `Mathlib.Analysis.Normed.Field.Basic`; just
  `inferInstance` rather than `Module.punctured_nhds_neBot ℂ ℂ 0`.
* **`Filter.eventually_all_finset` for ∀-over-Finset eventual
  statements**: collects `∀ j ∈ I, ∀ᶠ x in l, p j x` to
  `∀ᶠ x in l, ∀ j ∈ I, p j x` when `I` is finite.
* **Single-file `lake env lean` needs deps pre-built**: when a new
  chip imports a just-added chip from the same session, run
  `taskpolicy -b nice -n 19 lake build <ModuleName>` first.

**Build**: full lake build 8887 jobs clean after every commit; zero
`sorry`, zero `axiom` across the 11 new files.

**Commits (in order)**: `c9dd5d9`, `544f7d7`, `a35b544`, `27837c3`,
`558cdc5`, `e89bbf5`, `c535e63`, `36e06ff`, `400a86b`, `40e010c`,
`8313d78`.

## 2026-05-16 (evening) — Trace-level realification compatibility (chip 3, 345 LOC, direct to `main`)

Closes the third piece of item (3) of the `HolomorphicTraceExtension`
closure plan. Sums the per-summand realification compatibility (chip 2)
over the fiber to get the trace-level identity:

  `(realPartCLM (f.fStarOmegaHol hnc α v)) w
     = SmoothPath.applyCotangent (f.fStarOmega hnc (realComponent α) v) w`

(and analogously for `imagPartCLM` / `imagComponent`), at every regular
value `v` and tangent vector `w : ℂ`.

**1 new file** (`JacobianChallenge/Manifold/`):

* `FStarOmegaHolRealification.lean` (345 LOC) — trace-level real-part /
  imag-part realification compatibility. Strategy:
  1. Reduce both traces to fiber-finset sums via
     `holTraceAt_eq_sum_holSheetCotPullback` /
     `traceAt_eq_sum_sheetCotPullback`.
  2. Per-summand: chip 2's `realPartCLM_holCotangentPullbackAt_apply`
     (resp. `imag`), feeding `MDifferentiableAt` via a fresh helper
     `mdifferentiableAt_localSheet_g_at_value` (using `subst hp_to_v`
     to avoid the `LocalSheetData`-dependent-type `rw [hp_to_v]` failure).
  3. Sum-pushing: a generalised inner lemma `general` parametrised by
     an arbitrary `S : Finset { x // x ∈ f.fiberFinset hv }` and a
     per-summand hypothesis. Induction over `S` via
     `Finset.induction_on`:
     - **empty**: `realPartCLM 0 w = applyCotangent 0 w = 0` via `map_zero`.
     - **insert**: `Finset.sum_insert` + `map_add realPartCLM` +
       `map_add cotangentEquiv` distributes; per-summand `h_each q` and
       the inductive hypothesis close.

  This generalised-inner-lemma pattern works around the `map_sum
  realPartCLM` rewrite that failed on the `CotangentSpace`-typed sum
  expression (noted in the prior commit): the explicit
  `map_add realPartCLM _ _` rewrite with the underscore-typed `_ + _`
  pattern matches successfully because Lean unifies the args from the
  `show` context.

**Net state.** Items (1) ✓ (on-regular-set holomorphic 1-form built
via `fStarOmegaHolOn`) and (3) ✓ (realification compatibility, both
real and imag) are now CLOSED. Remaining for
`HolomorphicTraceExtension X`:

* **Item (2)** — Extension across critical values (n-th-root
  cancellation + Riemann removable singularity for 1-forms on `ℙ¹`).
  Genuinely-new classical content not at the mathlib pin.

**Build**: full lake build 8887 jobs clean; zero `sorry`, zero `axiom`.

## 2026-05-16 (late afternoon) — Realification compatibility primitives (2 chips, 289 LOC, direct to `main`)

Per-summand realification compatibility for the holomorphic cotangent
pullback, closing two of the three pieces needed for item (3) of the
`HolomorphicTraceExtension` closure plan. The trace-sum-level identity
(third piece) is left for a follow-up due to typeclass-pattern-matching
issues described below.

**2 new files** (`JacobianChallenge/Manifold/`):

* `MFDerivComplexToRealApply.lean` (171 LOC) — **manifold-derivative
  application-level realification.** For ℂ-differentiable
  `g : X → Y` at `x`, `((mfderiv 𝓘(ℝ, ℂ) g x) w : ℂ)
  = ((mfderiv 𝓘(ℂ, ℂ) g x) w : ℂ)` for every `w : ℂ`. Bypasses the
  `TangentSpace` non-reducibility issue by working at the function
  application level. Ships:
  - `MDifferentiableAt.complex_to_real` — `MDifferentiableAt 𝓘(ℂ, ℂ)`
    implies `MDifferentiableAt 𝓘(ℝ, ℂ)`.
  - `mfderiv_complex_to_real_apply` — the application-level identity.
  - Private helpers `writtenInExtChartAt_complex_eq_real`,
    `extChartAt_apply_complex_eq_real` — chart-pullback agrees across
    `𝓘(ℂ, ℂ)` and `𝓘(ℝ, ℂ)`.
  - Private helpers `isScalarTower_R_C_C` +
    `differentiableAt_restrictScalars_R_C_C` +
    `hasFDerivAt_restrictScalars_R_C_C` — work around the mathlib synth
    failure for `IsScalarTower ℝ ℂ ℂ` in `restrictScalars` contexts
    (synth never tries `IsScalarTower.right`, only fails on
    `Complex.instIsScalarTowerOfReal`; explicit `@`-applied wrappers
    are needed to make the instance pass through).

* `HolCotangentPullbackRealification.lean` (118 LOC) — **per-summand
  realification compatibility for the holomorphic cotangent
  pullback.** For ℂ-differentiable `g : Y → X` at `y` and every
  `w : ℂ`:

      (realPartCLM (holCotangentPullbackAt g y α)) w
        = Complex.re ((α.eval (g y)) ((mfderiv 𝓘(ℝ, ℂ) g y) w))

  and similarly for `imagPartCLM`. Both sides are `ℝ`-values. The
  substantive content reduces to `mfderiv_complex_to_real_apply`
  (chip 1). Apply-level statement avoids the typed
  `restrictScalars`-on-`CotangentSpace` synth failures.

**Net effect on item (3) closure plan.** The
`(mfderiv 𝓘(ℂ, ℂ) g x).restrictScalars ℝ = mfderiv 𝓘(ℝ, ℂ) g x`
identity attempted on the prior commit (typed-level) hit
`Module ℂ (TangentSpace 𝓘(ℝ, ℂ) x)` synth failures because `TangentSpace`
is non-reducible by design (mathlib comment in
`Mathlib/Geometry/Manifold/IsManifold/Basic.lean:1037`). This chip
arc demonstrates the workaround pattern (apply-level statements +
explicit `@`-applied instance passing) that gets us past the
`TangentSpace` abstraction barrier.

**What's left for item (3).** A **trace-sum-level** identity
`(realPartCLM (f.fStarOmegaHol hnc α v)) w
  = applyCotangent (f.fStarOmega hnc (realComponent α) v) w`
at every regular `v` and `w : ℂ`. This sums the per-summand identity
(chip 2) over `f.fiberFinset hv` and was attempted but hit further
`map_sum`-pattern-matching issues (Lean's `rw [map_sum realPartCLM]`
fails to match the goal's `realPartCLM (∑ p, X p)` pattern despite
type-equivalence — likely a deeper consequence of `CotangentSpace`
abstraction interacting with `ContinuousLinearMap` map-out
synthesis). Estimated 100-200 LOC once the right intermediate form
is found.

**Build**: full lake build 8886 jobs clean; zero `sorry`, zero `axiom`.

## 2026-05-16 (afternoon) — `fStarOmegaHolOn` arc: holomorphic-side parallel (6 chips, 828 LOC, direct to `main`)

Continues the morning's `fStarOmegaOn` arc with the **holomorphic-side
parallel**: builds `f.fStarOmegaHolOn hnc α : HolomorphicOneFormOn
RiemannSphere f.regularValueSet` unconditionally for any
`α : HolomorphicOneForm X`. After this arc, the discharge of
`HolomorphicTraceExtension X` reduces to (i) **extension of the
on-regular-set holomorphic 1-form to a global one** on `ℙ¹`
(n-th-root cancellation + Riemann removable singularity — genuinely
new classical content not at the mathlib pin) and (ii) **realification
compatibility** (a finite analytic identity reducing to `mfderiv
𝓘(ℂ, ℂ) g x).restrictScalars ℝ = mfderiv 𝓘(ℝ, ℂ) g x` for ℂ-smooth
`g`; doable in tree as a separate chip arc).

**6 new files** (`JacobianChallenge/Manifold/`):

* `HolomorphicCotangentPullbackAt.lean` (133 LOC) — pointwise
  holomorphic cotangent pullback `holCotangentPullbackAt g y α =
  (α (g y)).comp (mfderiv 𝓘(ℂ, ℂ) g y) : CotangentSpace 𝓘(ℂ, ℂ) y`.
  ℂ-linearity in α; germ congruence in g via
  `Filter.EventuallyEq.mfderiv_eq` (model-generic).

* `MeromorphicNonzeroHolTraceAt.lean` (192 LOC) — `holTraceAt =
  ∑_{p ∈ fiberFinset hv} holCotangentPullbackAt sheet_p.g v α`;
  `holSheetCotPullback` wrapper (mirrors `sheetCotPullback`);
  ℂ-linearity; **cross-sheet identification**
  `holCotangentPullbackAt_localSheet_eq_at_target_sheet` —
  parallel to the realified version, reusing the model-generic
  `LocalSheetData.g_eventuallyEq_of_isLocalRightInverse` +
  `holCotangentPullbackAt_congr_of_eventuallyEq`.

* `MeromorphicNonzeroFStarOmegaHolDef.lean` (137 LOC) — total
  dependent function `fStarOmegaHol α v` defined as
  `if v ∈ regularValueSet then holTraceAt v α else 0`. Apply lemmas
  at regular vs. critical values; pointwise ℂ-linearity.

* `FStarOmegaHolLocalAt.lean` (131 LOC) — fixed-Finset rewrite on the
  labelling nbhd. Exact mirror of
  `fStarOmega_eq_sum_sheetCotPullback_at_v0`: re-indexing via the
  bijection `p ↦ (fiberSheetAt p).g v` (bundle-independent —
  `fiberSheetAt` machinery doesn't care about scalar field) +
  cross-sheet identification (holomorphic version).

* `FStarOmegaHolContMDiffAt.lean` (139 LOC) — pointwise
  `ContMDiffAt ω` at every regular value `v₀`. Ships
  `holSheetCotPullback_contMDiffAt` wrapper to hide
  `LocalSheetData`'s dependent-type index (the `rw [hp_to_v₀] at h`
  motive in the realified case works through the wrapper but not on
  the raw `localSheetPullbackPointwise` expression). Then composes
  per-sheet smoothness (sub-chip A) + `ContMDiffAt.sum_section` +
  `congr_of_eventuallyEq` on the labelling nbhd.

* `FStarOmegaHolOn.lean` (96 LOC) — final packaging as
  `HolomorphicOneFormOn RiemannSphere f.regularValueSet`. `ContMDiffOn`
  from pointwise `ContMDiffAt` + open `regularValueSet`.

**Net effect on RLSL closure.** Pre-arc, the smoothness/holomorphicity
side of `HolomorphicTraceExtension X` was a future chip arc with the
parallel-to-`fStarOmegaOn` infrastructure to be built. Post-arc, the
**smoothness/holomorphicity on the open regular set is unconditional**
(in the same way `fStarOmegaOn` already discharges it for the
realified case). What remains for `HolomorphicTraceExtension X` is
(i) extension across critical values, (ii) realification compatibility
with the realified trace on the regular set.

**Gotchas surfaced**:

* `LocalSheetData`'s dependent-type index (`y₀ : Y` in
  `LocalSheetData f y₀ x₁`) bleeds through into `localSheetData_at_regular
  hnc hp_reg`'s type (`LocalSheetData f.toRiemannSphere
  (f.toRiemannSphere p) p`). Naïve `rw [hp_to_v₀] at h` on a statement
  with `localSheetPullbackPointwise (sheet.g) α v` exposed fails with
  "motive not type correct". Fix: package as
  `f.holSheetCotPullback hnc hp_reg v α` (hiding the sheet in a
  non-dependent wrapper).
* `RealificationCompatibility` (next chip arc) reduces to
  `(mfderiv 𝓘(ℂ, ℂ) g x).restrictScalars ℝ = mfderiv 𝓘(ℝ, ℂ) g x` for
  ℂ-smooth `g`. The chart-pullback `fderivWithin` identity is
  `DifferentiableAt.fderiv_restrictScalars` (mathlib); manifold
  bridging requires `HasMFDerivAt ↔ HasFDerivWithinAt` + uniqueness.
  Not yet built.

**Build**: full lake build 8884 jobs clean; zero `sorry`, zero `axiom`.

## 2026-05-16 (morning) — `fStarOmegaOn` arc + `HolomorphicTraceExtension` reduction (6 chips, ~974 LOC, direct to `main`)

**6 new files** (`JacobianChallenge/Manifold/`):

* `SheetCotangentPullbackContMDiffAt.lean` (238 LOC) — per-sheet
  cotangent-pullback section smoothness at a regular value in the
  **holomorphic** `𝓘(ℂ, ℂ) ω` bundle. Local-sheet analogue of
  `HolomorphicEquiv.pullbackSection_contMDiffAt`
  (`PullbackSectionSmoothness.lean`) with the global smoothness witness
  replaced by a pointwise `ContMDiffAt ω g y₀` hypothesis. Three lemmas
  shipped:
  - `localSheetPullbackPointwise` — dependently-typed pointwise pullback
    `∀ y : Y, CotangentSpace 𝓘(ℂ, ℂ) y` (mirrors
    `HolomorphicEquiv.pullbackPointwise` to avoid bundle-instance
    ambiguity).
  - `cotangent_inCoordinates_flip_eventually_eq_of_continuousAt` —
    local eventually-form of the cotangent↔tangent inCoordinates bridge
    from `PullbackSectionSmoothness`.
  - `pullbackSection_contMDiffAt_of_localSheet` — headline.
  - `MeromorphicNonzero.sheetPullbackSection_contMDiffAt` — wrapper
    discharging the smoothness witness via
    `f.contMDiffAt_localSheet_g_at_basePoint`.

* `SheetCotPullbackContMDiffAtReal.lean` (292 LOC) — realified
  companion in the `𝓘(ℝ, ℂ) ⊤` bundle. Same `clm_apply_of_inCoordinates`
  scaffold with 𝕜 := ℝ; underlying mathlib lemmas
  (`inCotangentCoordinates_eq`, `cotangentBundleCore_coordChange_apply`,
  `inTangentCoordinates_eq`, `ContMDiffAt.mfderiv_transpose`) are
  field-generic. Includes:
  - `cotangent_inCoordinates_flip_eq_flip_inTangentCoordinates_real` —
    realified bridge identity.
  - `ContMDiffAt.complex_to_real_omega` — regularity-preserving
    complex-to-real realification (companion to the existing
    `complex_to_real` which drops `ω → ∞`; this variant skips the
    final `.of_le`).
  - `pullbackSection_contMDiffAt_of_localSheet_real` — headline.
  - `MeromorphicNonzero.sheetCotPullback_contMDiffAt` — wrapper for
    `sheetCotPullback`.

* `FStarOmegaContMDiffAt.lean` (118 LOC) — pointwise `ContMDiffAt ⊤` of
  `f.fStarOmega hnc om` at every regular value, by combining the
  per-sheet smoothness across `(f.fiberFinset hv₀).attach` via
  mathlib's `ContMDiffAt.sum_section` and bridging to `fStarOmega` via
  `FStarOmegaLocalAt.fStarOmega_eq_sum_sheetCotPullback_at_v0` on the
  labelling neighbourhood.

* `FStarOmegaOn.lean` (81 LOC) — final packaging as a
  `SmoothOneFormOn 𝓘(ℝ, ℂ) RiemannSphere f.regularValueSet`. Ships:
  - `fStarOmega_contMDiffOn` — `ContMDiffOn ⊤` on `regularValueSet`
    (open ⇒ `ContMDiffAt`-at-every-point suffices).
  - `MeromorphicNonzero.fStarOmegaOn` — the bundled structure.

* `TraceAtVanishesOnHolomorphicReduction.lean` (147 LOC) —
  **structural reduction** of `TraceAtVanishesOnHolomorphic X` to a
  single named hypothesis:
  - `HolomorphicTraceExtension X` — for every non-constant `f` and
    `α : HolomorphicOneForm X`, ∃ `α' : HolomorphicOneForm
    RiemannSphere` whose realified components agree pointwise on
    `f.regularValueSet` with the realified trace of `α`.
  - `traceAtVanishesOnHolomorphic_of_extension` — discharge via
    `Subsingleton (HolomorphicOneForm RiemannSphere)` (unconditional,
    in tree) + `realComponent_zero` / `imagComponent_zero`.
  - `regularLevelSetLatticeClause_of_holomorphicTraceExtension` —
    composes with `regularLevelSetLatticeClause_of_traceVanishing` to
    discharge the regular-case lattice clause from a single named
    input.

* `HolomorphicOneFormOn.lean` (98 LOC) — partial-domain holomorphic
  1-form type (analogue of `SmoothOneFormOn` in `𝓘(ℂ, ℂ) ω`). Ships
  the type, `CoeFun` instance, and `HolomorphicOneForm.restrictHolOn`
  canonical restriction. Sets up the target type for the eventual
  on-regular-set holomorphic trace.

**Net effect on RLSL closure.** Pre-session, RLSL discharge reduced to
`TraceAtVanishesOnHolomorphic X` (a *global pointwise vanishing*
hypothesis, opaque to construction). Post-session, this further
reduces to `HolomorphicTraceExtension X` — *existence* of a global
holomorphic 1-form on `ℙ¹` agreeing with the realified trace on the
regular set. The smoothness side of that extension (on the open
regular set) is now **unconditional** via `fStarOmegaOn`. The
remaining classical content for the next chip arc is the
holomorphic-side parallel (target type now exists via
`HolomorphicOneFormOn`) + extension across critical values (n-th-root
cancellation + Riemann removable singularity theorem on 1-forms on
`ℙ¹`); this is genuinely new content not at the mathlib pin.

**Gotchas surfaced during writing** (next-session hazards):

* Bundle topology instance ambiguity — raw
  `(α.toFun (g v)).comp (mfderiv g v) : ℂ →L[ℂ] ℂ` doesn't bind the
  `CotangentSpace` bundle structure; need a typed
  `∀ y, CotangentSpace _ y` wrapper definition first.
* `clm_apply_of_inCoordinates` requires **named arguments**
  `(hϕ := …) (hv := …) (hb₂ := …)` to pin the `VectorBundle`
  metavariables.
* `congr_of_eventuallyEq` direction: `f₁ =ᶠ f + ContMDiffAt f →
  ContMDiffAt f₁`, *not* the reverse.
* `SmoothOneForm`'s regularity is `⊤` (= `ω`, the analytic top of
  `WithTop ℕ∞`), strictly above `∞`. `ContMDiffAt.complex_to_real`
  drops to `∞` via a final `.of_le`; for `⊤`-preserving realification
  use `complex_to_real_omega` (shipped in
  `SheetCotPullbackContMDiffAtReal.lean`).

**Build**: all 6 chips single-file `LEAN_NUM_THREADS=1 lake env lean`
clean; zero `sorry`, zero `axiom`. Full `lake build` deferred to
next-session merge gate.

## 2026-05-16 (early morning) — `RegularLevelSetLatticeClause` from holomorphic-trace vanishing (1 chip, ~180 LOC, direct to `main`)

**1 new file** (`JacobianChallenge/Manifold/`):

* `RegularLevelSetLatticeClauseFromTraceVanishing.lean` — second
  structural reduction route for the regular-case lattice clause,
  parallel to `RegularLevelSetLatticeClauseFromAJ.lean`. Ships:

  - `TraceAtVanishesOnHolomorphic X` — named hypothesis: for every
    non-constant `f`, every `α : HolomorphicOneForm X`, and every
    regular value `v`,
    `f.traceAt hnc hv (realComponent α) = 0` and
    `f.traceAt hnc hv (imagComponent α) = 0`.

  - `regularLevelSetLatticeClause_of_traceVanishing` — conditional
    discharge. Composes today's σ-1 chip (now unconditional via
    `integrandContinuousAlongBeta_holds`) + the real-imag split of
    `complexChainPeriod` + `applyCotangent_zero` + integral of zero is
    zero, to conclude the period vector is zero (hence in lattice).

**Status**: this isolates the *irreducible analytic content* of Abel
forward at the regular-case clause as a single named hypothesis. The
hypothesis is equivalent to: the trace map
`HolomorphicOneForm X → HolomorphicOneForm RiemannSphere` lands in a
subsingleton group (`HolomorphicOneForm ℙ¹ = 0`, in tree). The
construction of the trace map is the remaining classical work
(n-th-root cancellation at critical values + Riemann removable
singularity theorem on 1-forms).

**Build**: 8872 jobs, zero `sorry`, zero `axiom`.

## 2026-05-16 (early morning) — `RegularLevelSetLatticeClause` ↔ `AbelGeneratorPeriodCondition` structural reduction (1 chip, ~130 LOC, direct to `main`)

**1 new file** (`JacobianChallenge/Manifold/`):

* `RegularLevelSetLatticeClauseFromAJ.lean` — completes the structural
  loop in the regular-case lattice clause. Two theorems:

  - `regularLevelSetLatticeClause_of_abelGeneratorPeriodCondition`:
    given any `B : AbelJacobiInput α h` and the per-`f` AJ-chain period
    condition `AbelGeneratorPeriodCondition B`, the regular-case
    lattice clause `RegularLevelSetLatticeClause X α h` follows.

    **Proof**: cycle witness `Z + AJ ∈ SmoothCycle`
    (`regularLevelSetCycleWitness`, in tree) gives
    `period(Z + AJ) ∈ lattice` automatically. `period(AJ) ∈ lattice`
    by hypothesis. `period(Z) = period(Z + AJ) - period(AJ) ∈ lattice`
    via `AddSubgroup.sub_mem`.

  - `regularLevelSetLatticeClause_of_genus_zero`: at genus zero, the
    period vector is a subsingleton (`Fin 0 → ℂ`), so the lattice
    clause holds unconditionally.

**Status**: the structural gap between
`RegularLevelSetLatticeClause` (a clause on the analytic chain) and
`AbelGeneratorPeriodCondition` (a clause on the formal AJ chain) is
now closed. The substantive analytic content of Abel forward —
discharging `AbelGeneratorPeriodCondition` for arbitrary non-constant
`f` at genus ≥ 1 — remains open and is the residue theorem on 1-forms
on `ℙ¹` / Stokes on 2-chains content (~1,500–2,500 LOC of genuine
classical infrastructure).

**Build**: 8871 jobs, zero `sorry`, zero `axiom`.

## 2026-05-15 (late evening) — `IntegrandContinuousAlongBeta` UNCONDITIONAL (4 chips, ~600 LOC, direct to `main`)

End-to-end discharge of `MeromorphicNonzero.IntegrandContinuousAlongBeta`
via the chart-coord-pair architecture extended through the f-5 sheet
smoothness layer. Closes the named hypothesis blocking
`IntegrateLevelSetChainSigmaReparam.lean`'s σ-1 chip and one of the two
remaining inputs to `RegularLevelSetLatticeClause` discharge.

**4 new files** (`JacobianChallenge/Manifold/`):

* `PairingContinuityBetaLocal.lean` — chip 12 relaxed from
  `ContMDiff β` (global) to `ContMDiffAt β s₀` (pointwise). Ships:
  - `chartBetaVelocity_contMDiffAt_local` (local chip 9).
  - `chartBetaVelocity_continuousAt_local`.
  - `continuousAt_pairing_smoothOneForm_beta_local` (local chip 12).
  Chart-preimage nbhd obtained via `ContinuousAt.preimage_mem_nhds`
  rather than `IsOpen.preimage Continuous`. Identical chart-coord-pair
  structure otherwise.

* `SheetCotPullbackPairingContinuity.lean` — per-sheet pairing
  continuity at `s₀`. Headline: for `β s₀ ∈ u` (open) with
  `sheet.g := (localSheetData_at_regular hnc hp_reg).g` real-smooth
  on `u`, the pairing
  ```
  s ↦ applyCotangent (sheetCotPullback hnc hp_reg (β s) om) (mfderiv β s 1)
  ```
  is `ContinuousAt s₀`. **Proof**: on the open nbhd `β ⁻¹' u` of `s₀`,
  the chain rule (`mfderiv_comp_apply`) + `applyCotangent_cotangentPullbackAt`
  rewrites the LHS to the pairing of `om` along the composed smooth
  path `γ := sheet.g ∘ β : ℝ → X`. Then the local chip 12 applied to
  `ContMDiffAt γ s₀` (= compose `β` smooth at `s₀` with `sheet.g` smooth
  at `β s₀`) gives `ContinuousAt s₀` of the RHS. `ContinuousAt.congr`
  transfers via the open-nbhd EqOn.

* `FStarOmegaPairingContinuity.lean` — `fStarOmega`-pairing
  `ContinuousAt s₀` for `β s₀ ∈ regularValueSet`. **Proof**: on the
  open nbhd `β ⁻¹' localFiberLabelingNbhd hnc hβs₀_reg`, the `f-3`
  rewrite `fStarOmega_eq_sum_sheetCotPullback_at_v0` expresses
  `fStarOmega om (β s)` as a fixed Finset sum over `fiberFinset hβs₀_reg`.
  `applyCotangent_finset_sum` distributes the pairing. Each summand
  is `ContinuousAt s₀` via the per-sheet chip (instantiated with the
  realified ω-smooth nbhd from
  `exists_contMDiffOn_localSheet_g_near_basePoint`). Finset induction
  with `ContinuousAt.add` collapses the sum. `ContinuousAt.congr`
  finishes via the open-nbhd EqOn.

* `IntegrandContinuousAlongBetaUnconditional.lean` — assembles
  `continuousOn_fStarOmega_pairing_Icc01` (point-by-point on
  `Icc 0 1` via `hβ_reg`) and plugs it into the in-tree
  `integrandContinuousAlongBeta_of_fStarOmega_pairing_continuousOn`
  reduction. **Headline**:
  ```
  theorem integrandContinuousAlongBeta_holds
      (f : MeromorphicNonzero X)
      (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
      (hβ_smooth : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) ∞ β)
      (hβ_reg : ∀ s ∈ Icc 0 1, β s ∈ f.regularValueSet)
      (om : SmoothOneForm 𝓘(ℝ,ℂ) X) :
      f.IntegrandContinuousAlongBeta hnc hβ_smooth hβ_reg om
  ```

**Architectural caveat dissolved:** the prior factor-decomposed route
(2026-05-15 evening, chips 1–8) routed through `cotangentEquiv` which
is NOT globally continuous for non-trivial cotangent bundles. The
chart-coord-pair route from today bypasses this entirely — the
pairing is chart-invariant (chip 11) so the per-sheet pairing
continuity uses only ω-smooth-on-open data, which IS chart-cocycle-
clean by composing with the bundle's natural trivialisation
internal to `cotangentPullbackAt`.

**Status post-f-5 close**: `RegularLevelSetLatticeClause` discharge
now requires only the **residue theorem on 1-forms on `ℙ¹`**
(`paper/jacobian.md`, ~1,500–2,500 LOC). Chain-difference reduction
in `RegularLevelSetChainBoundaryAJ.lean` reduces `period(Z) ∈ lattice`
to `period(AJ-chain) ∈ lattice`, which IS
`AbelGeneratorPeriodCondition` — circular w.r.t. our goal. The
residue theorem is the genuinely new classical input needed.

**Build:** 8870 jobs, zero `sorry`, zero `axiom`.

## 2026-05-15 (evening) — Chart-coord-pair architecture: SmoothOneForm pairing continuity (3 chips, ~351 LOC, direct to `main`)

Three chips completing the SmoothOneForm side of the chart-coord-pair
architecture for `IntegrandContinuousAlongBeta` (started 2026-05-15
evening with chip 9, `ChartBetaVelocity`).

**3 new files** (`JacobianChallenge/Manifold/`):

* `ChartBetaVelocitySelfEval.lean` (90 LOC) —
  `chartBetaVelocity_self`: at the anchor `s₀`, both source-side
  (`tangentBundleCore_coordChange_model_space` on `ℝ`) and target-side
  (`coordChange_self` at base `β s₀`) cocycles collapse, giving
  `chartBetaVelocity I β s₀ s₀ = mfderiv 𝓘(ℝ, ℝ) I β s₀ (1 : ℝ)`.

* `ChartBetaPairingInvariance.lean` (145 LOC) —
  `applyCotangent_eq_chart_pairing_beta`: for any cotangent
  `φ : CotangentSpace I (β s)` with `β s ∈ (chartAt H (β s₀)).source`,
  the pairing
  `applyCotangent φ (mfderiv β s 1)`
  equals the chart-coord pairing of `φ` (transported to chart at
  `β s₀`) with `chartBetaVelocity I β s₀ s`. Mirrors
  `SmoothPath.integrand_eq_chart_pairing` but stated for a *free*
  cotangent, decoupling it from any `SmoothOneForm` wrapping — ready
  to compose with `traceAt` directly. The cancellation is the
  tangent-bundle cocycle `coordChange j i x ∘ coordChange i j x = id`
  at `x = β s`, paired with `cotangentBundleCore_coordChange_apply`.

* `PairingContinuityBeta.lean` (116 LOC) —
  `continuousAt_pairing_smoothOneForm_beta` and
  `continuous_pairing_smoothOneForm_beta`: for smooth `β : ℝ → M` and
  `om : SmoothOneForm I M`, the function
  `s ↦ applyCotangent (om (β s)) (mfderiv β s 1)` is `ContinuousAt s₀`
  for every `s₀`, hence `Continuous`. β-analogue of
  `SmoothPath.continuous_integrand_at`. Assembled from the three
  primitives above plus `cotangentSection_contMDiffAt_iff` (factored
  through `Continuous β`) and `ContinuousAt.clm_apply`. When
  `fStarOmega` is upgraded to a `SmoothOneForm` (post-`f-5`), this
  lemma directly discharges `IntegrandContinuousAlongBeta` for the
  trace-pairing along `β`.

**Remaining blocker for unconditional `IntegrandContinuousAlongBeta`:**
`f-5` — section smoothness of `fStarOmega` on `regularValueSet` (or
the `SmoothOneFormOn` upgrade). Once `f_*ω` is a `SmoothOneForm` (or
`SmoothOneFormOn regularValueSet`), the SmoothOneForm pairing
continuity above gives the conclusion.

**Build:** 8866 jobs (was 8863), zero `sorry`, zero `axiom`.

## 2026-05-15 (evening) — `IntegrandContinuousAlongBeta` groundwork (9 chips, ~893 LOC, direct to `main`)

Nine chips toward unconditional discharge of
`MeromorphicNonzero.IntegrandContinuousAlongBeta` — the named hypothesis
introduced by the σ-1 chip
(`integrate_levelSetChain_eq_traceAt_lineIntegral`,
`IntegrateLevelSetChainSigmaReparam.lean`) and the remaining analytic
input to step 6 of the `RegularLevelSetLatticeClause` discharge (the
other being the residue theorem for `f_*ω` on `ℙ¹`).

The first eight chips build a **factor-decomposed entry point** (trace
factor × velocity factor), reaching a single API
`integrandContinuousAlongBeta_of_per_sheet_univ_and_velocity` that
discharges `IntegrandContinuousAlongBeta` from two plain `ContinuousOn`
hypotheses on `Icc 0 1`. The ninth chip (`ChartBetaVelocity`) is the
first primitive of the **chart-coord-pair architecture** (mirroring
`SmoothPathIntegrability.continuous_integrand_at`), which is the
architecturally correct path to *unconditional* discharge for general
regular-value paths (see caveat below).

**9 new files** (`JacobianChallenge/Manifold/`):

* `ApplyCotangentContinuity.lean` (107 LOC) — bilinear continuity of
  `SmoothPath.applyCotangent` lifting mathlib's
  `ContinuousOn.clm_apply` / `Continuous.clm_apply` /
  `ContinuousAt.clm_apply` / `ContinuousWithinAt.clm_apply` through
  `cotangentEquiv`. Reduces joint continuity of `applyCotangent (φ y)
  (v y)` to continuity of the cotangent factor (as a CLM via
  `cotangentEquiv`) and the vector factor.

* `IntegrandContinuousAlongBetaFStarOmega.lean` (111 LOC) — dependent-if
  kill. Reduces `IntegrandContinuousAlongBeta` (which uses `if hs : s ∈
  Icc 0 1 then …`) to a plain `ContinuousOn` of the un-guarded
  `fStarOmega`-pairing on `Icc 0 1`, via `fStarOmega_apply_of_regular`
  + `ContinuousOn.congr`.

* `IntegrandContinuousAlongBetaFactors.lean` (104 LOC) — factor-decomposed
  entry point. Composes the previous two chips to discharge
  `IntegrandContinuousAlongBeta` from trace-factor `ContinuousOn` +
  velocity-factor `ContinuousOn` (both on `Icc 0 1`, both plain).

* `CotangentEquivFStarOmegaSum.lean` (76 LOC) — CLM-level Finset-sum
  rewrite. Lifts the `f-3` identity
  `fStarOmega = ∑_p sheetCotPullback` through `cotangentEquiv` (which
  commutes with `Finset.sum` since it is a `LinearEquiv`) on the
  labelling nbhd.

* `TraceFactorContinuousOnFromSheets.lean` (99 LOC) — trace-factor
  `ContinuousOn` on the labelling nbhd from per-sheet `ContinuousOn`
  inputs, via `continuousOn_finset_sum` + the prior CLM-level rewrite.

* `TraceFactorContinuousOnAlongBeta.lean` (94 LOC) — pullback along
  continuous `β : ℝ → RiemannSphere`. Trace-factor `ContinuousOn` on
  any `S ⊆ β ⁻¹' (labelling nbhd)` via `ContinuousOn.comp` +
  `MapsTo`-of-preimage.

* `TraceFactorContinuousOnIcc01.lean` (111 LOC) — pointwise gluing to
  global `ContinuousOn (Icc 0 1)`. At each `s₀ ∈ Icc 0 1`, the labelling
  nbhd at `β s₀` is an open nhd of `β s₀` (by
  `mem_localFiberLabelingNbhd_self`), so the β-preimage is an open ℝ-nhd
  of `s₀`; `ContinuousOn` ⇒ `ContinuousAt` ⇒ `ContinuousWithinAt
  (Icc 0 1)`. Discharge input is a single **universal**
  `h_per_sheet_univ` hypothesis.

* `IntegrandContinuousAlongBetaPerSheetVel.lean` (102 LOC) — top-level
  API endpoint composing the trace-factor `Icc 0 1` lifting with the
  factor-decomposed entry point. Headline:
  `integrandContinuousAlongBeta_of_per_sheet_univ_and_velocity`.

* `ChartBetaVelocity.lean` (89 LOC) — direct-smooth-map analogue of
  `SmoothPath.chartVelocity` (which is `SmoothPath`-only). For smooth
  `β : ℝ → M` and base parameter `s₀`, defines the chart-coord
  representative of `β'(s) := mfderiv β s 1` trivialised via
  `chartAt H (β s₀)`. Three lemmas: `chartBetaVelocity` def,
  `contMDiffAt_chartBetaVelocity ∞` at `s₀` (via
  `ContMDiffAt.mfderiv_const`), and `continuousAt_` corollary. First
  primitive of the chart-coord-pair architecture.

### Architectural caveat on chips 1–8 (cotangentEquiv factor-decomposition)

The factor-decomposition API in chips 4–8 routes through `cotangentEquiv
(φ v) : ℂ →L[ℝ] ℝ` as an *absolute-coord* function `v ↦ (CLM : ℂ
→L[ℝ] ℝ)`. **For non-trivial cotangent bundles (RS has 2 charts,
non-identity chart transitions), this absolute-coord view is NOT
globally continuous in general** — sections are continuous *in the
bundle topology*, which differs from absolute-coord at chart boundaries.

The chart-cocycle cancellation only happens inside the *pairing*
`applyCotangent (om v) (vel v)`, which is why
`SmoothPathIntegrability.continuous_integrand` proves the whole
integrand continuous **without** factoring through individual
covector/vector continuities.

**Consequence:** the `h_per_sheet_univ` discharge in chip 8 is
discharge-friendly only when (i) the labelling nbhd fits within a single
RS chart and (ii) each `sheet.g`'s image fits within a single X chart.
For paths that don't cross `∞`, this holds. For general regular-value
paths, the architecturally correct discharge is the **chart-coord-pair
architecture** (mirroring `SmoothPathIntegrability.continuous_integrand_at`):
chart-coord cotangent representative (`chartFStarOmega β s₀ s`) +
chart-coord velocity (chip 9's `chartBetaVelocity`) +
chart-invariant pairing.

### Remaining for unconditional `IntegrandContinuousAlongBeta`

* `chartFStarOmega β s₀ s` — chart-coord representative of
  `fStarOmega(β s)` anchored at chart `chartAt H (β s₀)`. Requires
  `fStarOmega` as a smooth section on `regularValueSet` (i.e. the
  `f-5` chip: `SmoothOneFormOn 𝓘(ℝ, ℂ) RiemannSphere
  (regularValueSet f)`), which in turn requires per-sheet section
  smoothness for `cotangentPullbackAt sheet.g`. The latter is the
  `f-4` analogue of `PullbackSectionSmoothness.HolomorphicEquiv
  .pullbackSection_contMDiffAt`, adapted from global biholomorphisms to
  local sheets (estimated ~300–500 LOC).
* Same-point self-evaluation
  `chartBetaVelocity β s₀ s₀ = mfderiv β s₀ 1` (via
  `inTangentCoordinates_eq` at `(s₀, s₀)` + `coordChange_self`,
  ~30–50 LOC).
* Chart-invariance of pairing on chart preimage near `s₀` (analogue of
  `SmoothPathIntegrability.integrand_eq_chart_pairing`).
* Pointwise gluing to `ContinuousOn (Icc 0 1)` via chart-coord pairing
  + `ContinuousOn.congr`.

Plus the unrelated track for step 6 of `RegularLevelSetLatticeClause`:
the **residue theorem on 1-forms on `ℙ¹`** (adaptation of the in-tree
`JacobianChallenge.residue_theorem`, function-level, to meromorphic
1-forms; estimated ~1,500–2,500 LOC).

### Verification

Build green at **8863 jobs** (was 8854 pre-session). Zero `sorry`,
zero `axiom`. All chips locally verified via
`taskpolicy -b nice -n 19 env LEAN_NUM_THREADS=1 lake build` (serial,
no parallel sub-agents).

### Per-commit history

* `4830b71` — chip 1 (`ApplyCotangentContinuity`)
* `f4fdbc2` — chip 2 (`IntegrandContinuousAlongBetaFStarOmega`)
* `8d009a8` — chip 3 (`IntegrandContinuousAlongBetaFactors`)
* `c4c393a` — chip 4 (`CotangentEquivFStarOmegaSum`)
* `b18ddb7` — chip 5 (`TraceFactorContinuousOnFromSheets`)
* `62507b3` — chip 6 (`TraceFactorContinuousOnAlongBeta`)
* `b4a7acf` — chip 7 (`TraceFactorContinuousOnIcc01`)
* `e22807b` — chip 8 (`IntegrandContinuousAlongBetaPerSheetVel`)
* `b142751` — chip 9 (`ChartBetaVelocity`)

## 2026-05-15 — Global integrand-trace integral identity (4 chips, ~640 LOC, direct to `main`)

Lifts the lifted-point local-identification arc to a **global**
integrand-trace integral identity:

```
SmoothChain.integrate (levelSetChain f β) om
  = ∫ t in 0..1, derivσ(t) *
      applyCotangent (traceAt … (β(σ t)) om) (mfderiv β (σ t) 1)
```

This is the **integrated source-side equality** with the traceAt-based
RHS in `derivσ` factored form — exactly the shape needed for the
σ-reparametrisation change-of-variables (which would convert to
`∫ s in 0..1, applyCotangent (traceAt … (β s) om) (mfderiv β s 1) ds`,
modulo continuity of the integrand-as-function-of-s = f_*ω smoothness).

**4 new files** (`JacobianChallenge/Manifold/`):

* `SourceFiberPathIntegrandChainAtT.lean` (~238 LOC) — chain-rule-
  unfolded per-fibre integrand at general `t₀`. Composes local
  identification with two `mfderiv_comp_apply` applications and
  `applyCotangent_cotangentPullbackAt`. Headline:
  ```
  ∃ a b ∈ [0,1], a ≤ t₀ ≤ b, ∀ u ∈ Ioo a b,
    (sourceFiberPath p).integrand om u
      = applyCotangent (cotangentPullbackAt sheet_q.g (β(σ u)) om)
          (mfderiv β (σ u) (mfderiv σ u 1))
  ```
  Required exposing strict bounds `0 < t₀ → a < t₀` and `t₀ < 1 → t₀ < b`
  in upstream chips (SourceFiberPathExtendEqSheetGAtT,
  SourceFiberPathIntegrandLocalSheetGAtT) for downstream use at
  `u = t` strictly.

* `GlobalIntegrandTraceIdentity.lean` (~165 LOC) — global per-`t`
  identity at any `t ∈ Ioo 0 1`:
  ```
  ∑ p, (sourceFiberPath p).integrand om t
    = applyCotangent (traceAt f hnc hβσt_reg om)
        (mfderiv β (σ t) (mfderiv σ t 1))
  ```
  No sub-interval restriction. Composes per-fibre chain-rule + Finset
  bijection (sourceFiber ↔ fiberFinset(β(σ t)) via `extend t`) +
  `applyCotangent_traceAt`. Boundary cases `t = 0, 1` are Lebesgue-
  null and not needed for integration.

* `IntegrateLevelSetChainEqTraceAt.lean` (~125 LOC) — integrated
  identity:
  ```
  SmoothChain.integrate (levelSetChain f β) om
    = ∫ t in 0..1, applyCotangent (traceAt … (β(σ t)) om)
        (mfderiv β (σ t) (mfderiv σ t 1))
  ```
  Composes `integrate_levelSetChain` (chain → ∑_p path-integrals) +
  `intervalIntegral.integral_finset_sum` (swap ∑ and ∫) +
  `intervalIntegral.integral_congr_ae` (boundary `{1}` measure-zero) +
  global per-`t` identity.

* `IntegrandSigmaSmulFactor.lean` (~162 LOC) — factors out `derivσ(t)`:
  ```
  ∫ t in 0..1, applyCotangent (…) (mfderiv β (σ t) (mfderiv σ t 1))
    = ∫ t in 0..1, derivσ(t) * applyCotangent (…) (mfderiv β (σ t) 1)
  ```
  Via `mfderiv_eq_fderiv` (mfderiv σ t 1 = derivσ(t) on ℝ → ℝ),
  `ContinuousLinearMap.map_smul` (mfderiv β linearity), and
  `cotangentEquiv` ℝ-linearity (applyCotangent φ (c • w) = c * apply
  Cotangent φ w).

Build green at **8842 jobs** (up from 8838). Zero `sorry`, zero
`axiom`. No item flips.

**Remaining for `RegularLevelSetLatticeClause` discharge:**
1. σ-reparametrisation `s = σ t` via
   `intervalIntegral.integral_comp_mul_deriv`. Requires
   continuity of the integrand-as-function-of-s, which is the
   `f_*ω` smooth-on-`regularValueSet` packaging.
2. `f_*ω` smooth-on-`regularValueSet` packaging.
3. Residue theorem adaptation `principalDivisorMap → f_*ω` on ℙ¹
   → period ∈ `periodLatticeImage`.

## 2026-05-15 — Lifted-point local identification at general t₀ (2 chips, ~345 LOC, direct to `main`)

Generalises the existing local-identification chip
`sourceFiberPath_toPath_extend_eq_sheet_g_locally` (at `t₀ = 0`) to
**arbitrary** `t₀ ∈ Icc 0 1`, using the **lifted-point sheet**
`sheet_q` centered at `q := (sourceFiberPath p).toPath.extend t₀`
instead of the source-fibre sheet `sheet_x` centered at `x ∈
sourceFiber(β 0)`.

The key observation: `sheet_q.V` is automatically a nbhd of
`f.toRiemannSphere q = β(σ t₀)` (via `sheet_q.mem_V`), so the
sub-interval condition is dischargeable at every `t₀` — bypassing
the β 0-centered sub-interval restriction of the original chain
rule. This opens the path to a **global** integrand-trace identity
without Hurwitz subdivision.

**2 new files**:

* `SourceFiberPathExtendEqSheetGAtT.lean` (~218 LOC) — local
  identification at general `t₀`. Same proof template as the existing
  `t₀ = 0` chip, generalised via `Metric.ball t₀ ε` constructions
  using `ε := min ε₁ ε₂` from the two preimage nbhds. Headline:
  ```
  ∃ a b ∈ [0,1], a ≤ t₀ ≤ b, ∀ t ∈ Icc a b,
    (sourceFiberPath p).toPath.extend t = sheet_q.g (β(σ t))
  ```

* `SourceFiberPathIntegrandLocalSheetGAtT.lean` (~127 LOC) — composes
  with `SmoothPath.integrand_eq_of_ambient_eqOn_Icc_fun` to give the
  per-fibre integrand identity at general `t₀`:
  ```
  ∃ a b ∈ [0,1], a ≤ t₀ ≤ b, ∀ u ∈ Ioo a b,
    (sourceFiberPath p).integrand om u
      = applyCotangent (om (sheet_q.g(β(σ u))))
          (mfderiv (sheet_q.g ∘ β ∘ σ) u 1)
  ```
  Bridges `extend` equality to `ambient` equality via
  `ambient_eq_on_unitInterval` + `Path.extend_extends'`.

The chain-rule unfolding into
`applyCotangent (cotangentPullbackAt sheet_q.g (β(σ u)) om) (...)` form
is the natural next chip; combined with the bijection re-indexing,
gives the **global integrand-trace identity** at any regular `t`,
which integrates to the global integral identity without Lebesgue
subdivision.

Build green at **8838 jobs** (up from 8836). Zero `sorry`, zero
`axiom`. No item flips.

## 2026-05-15 — Integrand-trace identity in full eventually form (5 chips, ~720 LOC, direct to `main`)

Building on the per-`t` trace identity arc, lifts the integrand-level
chain-rule + trace identity to a fully eventually-quantified form
near `t = 0`. Composing all hypotheses (per-fibre chain-rule realified
smoothness, sub-interval V-membership, lift-equality, regularity)
gives:

```
∀ᶠ t in 𝓝[Ioc 0 1] 0, ∃ hβσt_reg : β(σ t) ∈ regularValueSet,
  ∑ p ∈ sourceFiber, (sourceFiberPath p).integrand om t
    = applyCotangent (traceAt f hnc hβσt_reg om) (β'(σ t) σ'(t))
```

This is the integrand of `(levelSetChain f β).integrate ω` equating to
the integrand of the line integral of `f_*ω` along β (modulo σ-reparam).
Lebesgue subdivision over Hurwitz patches of `[0, 1]` lifts to global
integral identity.

**5 new files** (`JacobianChallenge/Manifold/`):

* `PerFiberSheetEventually.lean` (~125 LOC) — per-fibre + uniform
  filter forms of the lift-equality and sub-interval V-membership
  conditions near `t = 0`.

* `SourceSheetSumEqTraceAtEventually.lean` (~120 LOC) — eventually
  form of the per-`t` trace identity:
  `∀ᶠ t in 𝓝[Icc 0 1] 0, ∃ hβσt_reg, source-sum = traceAt(...)`.

* `LevelSetIntegrandEqTraceAtApply.lean` (~145 LOC) — integrand-level
  per-`t` identity composing chain-rule structural identity with the
  trace identity:
  `∑ p, integrand(sourceFiberPath p) om t
     = applyCotangent (traceAt f hnc hβσt_reg om) (β'(σt) σ'(t))`.

* `SheetGRealSmoothEventually.lean` (~125 LOC) — realified sheet.g
  smoothness eventually near `t = 0`, via
  `exists_contMDiffOn_localSheet_g_near_basePoint` +
  `ContMDiffAt.complex_to_real`. Uniform-over-sourceFiber form.

* `PerFiberChainRuleEventually.lean` (~125 LOC) — promotes the
  per-fibre chain-rule chip from `∃ δ > 0, ...` to filter form
  `∀ᶠ t in 𝓝[>] 0, ...` via intersection with realified-smoothness
  filter.

* `LevelSetIntegrandEqTraceAtApplyEventually.lean` (~125 LOC) — the
  full eventually composition headline.

Build green at **8836 jobs** (up from 8829). Zero `sorry`, zero
`axiom`. No item flips.

## 2026-05-15 — `RegularLevelSetLatticeClause` per-`t` trace identity (6 chips, ~975 LOC, direct to `main`)

Closes the substantive analytic primitives needed to bridge the
chain-rule structural identity (`sum_sourceFiber_integrand_chain_at`)
with the trace `traceAt(f)(β(σ t))(ω)` at any `t ∈ Icc 0 1` on a
sub-interval where `β(σ t) ∈ sheet_p.V` for every fibre point `p`. This
is the second-to-last step in discharging `RegularLevelSetLatticeClause`
(the substantive named input for `AbelHypothesis B` in general genus
that, combined with `AbelLatticeWitnessCriticalCase`, flips items
4, 5, 10, 11, 12, 13).

**6 new files** (`JacobianChallenge/Manifold/`):

* `MeromorphicNonzeroFiberFinsetCard.lean` (~140 LOC) — bridges
  `(f.fiberFinset hv).card` to `JacobianChallenge.ContMDiff.degreeFiber
  f.toRiemannSphere` via a `RegularValueWitnessReg`-builder
  (`regularValueWitnessReg_of_mem_regularValueSet`). Headlines:
  `fiberFinset_card_eq_degreeFiber` and the constancy corollary
  `fiberFinset_card_const : (fiberFinset hv₁).card = (fiberFinset hv₂).card`.

* `SourceFiberPathAmbientSurjOnAt.lean` (~210 LOC) — surjectivity-by-
  cardinality. Headlines:
  - `sourceFiberPath_toPath_extend_image_eq_fiberFinset_at` — Finset
    equality `image of sourceFiber.attach under (extend t) = fiberFinset
    (β(σ t))` via the existing image ⊆ inclusion + injection +
    cardinality match (from `fiberFinset_card_const`).
  - `sourceFiberPath_toPath_extend_surjOn_at` — surjectivity statement.
  - `sourceFiberPath_toPath_extend_bijOn_at` — `Set.BijOn` packaging.

* `CotangentPullbackAtCongr.lean` (~85 LOC) — `cotangentPullbackAt` is
  germ-determined: `cotangentPullbackAt_congr_of_eventuallyEq` (via
  `Filter.EventuallyEq.mfderiv_eq`) and `_of_eqOn_open` corollary.

* `LocalSheetDataUnique.lean` (~140 LOC) — uniqueness of local right-
  inverses. Two versions:
  - `g_eventuallyEq_of_g_eq` — between two `LocalSheetData`s sharing a
    base point: agreeing at `y₀` implies eqOn a nbhd.
  - `g_eventuallyEq_of_isLocalRightInverse` — general version against
    arbitrary local right-inverse `g : Y → X` near `y` with `g y ∈ s.U`,
    `f ∘ g = id` near `y`. Used by the cross-sheet identification.

* `CotangentPullbackSheetIdentification.lean` (~190 LOC) — cross-sheet
  cotangent pullback identification at a regular value:
  `cotangentPullbackAt_localSheet_eq_at_target_sheet` — for source-side
  sheet `sheet_p` (centered at `p` over a *different* base value) and
  the target-side sheet `sheet_q` (where `q := sheet_p.g v`) at
  `v ∈ sheet_p.V`, the cotangent pullbacks at `v` agree.

* `SourceSheetSumEqTraceAt.lean` (~210 LOC) — the headline per-`t`
  trace identity. `sheetCotPullback` wrapper fixes both model arguments
  at `𝓘(ℝ, ℂ)` (dodging an `open scoped unitInterval` parser
  interference with the `(I := …)` named-arg syntax in the conclusion
  position). `source_sheet_sum_eq_traceAt`:
  ```
  ∑_{p ∈ sourceFiber} sheetCotPullback sheet_p.g (β(σ t)) ω
    = traceAt f hnc hβσt_reg ω
  ```
  parametrized over the sub-interval condition `h_sub_interval`
  (`β(σ t) ∈ sheet_p.V` for every `p`) and the lift-equality condition
  `h_lift_eq` (`(sourceFiberPath p).toPath.extend t = sheet_p.g (β(σ t))`).
  Both will be discharged downstream on a uniform-δ sub-interval.

**Net effect on `RegularLevelSetLatticeClause`.** The cycle path from
sourceFiber → fiberFinset bijection (chip 2) and the trace identity
(chip 6) together complete the **algebraic** content of the per-`t`
lattice clause discharge — what remains for the full clause is:

1. Lebesgue gluing across the Hurwitz subdivision (composing per-sheet
   sub-interval identities to a global `[0, 1]` identity), via the
   already-built `exists_subdivision_hurwitzPatching`.
2. σ-reparametrisation reducing the integrand to the natural β-form.
3. Residue theorem for `f_*ω` on `ℙ¹` → period in `periodLatticeImage`,
   layered on top of `JacobianChallenge.residue_theorem`
   (`Manifold/ResidueTheoremUnconditional.lean`) adapted from the
   principal-divisor case to `f_*ω`'s residue divisor on RS.

Build green at **8829 jobs** (up from 8808). Zero `sorry`, zero
`axiom`. No item flips.

## 2026-05-15 — Hodge finite-dim Forster scaffolding through HolomorphicOneForm packaging (16 chips, 2948 LOC, direct to `main`)

End-to-end scaffolding of the elementary Forster/Montel/Riesz proof of
`HolomorphicOneFormFiniteDim X` for compact complex 1-manifolds. The
final chip packages the limit of a seminorm-bounded subsequence as an
honest `HolomorphicOneForm X`; only the seminorm-convergence upgrade
(inner-disk uniform → outer-disk seminorm) and the Riesz application
remain.

**16 new files** (`JacobianChallenge/Manifold/`):

* `HolomorphicOneFormChartCoeff.lean` (340 LOC) — chart-coord coefficient
  `localCoeff om y : ℂ → ℂ` of a holomorphic 1-form `om` via canonical
  chart at base point `y`. Pointwise linearity (`_zero`, `_add`, `_neg`,
  `_sub`, `_smul`) + ℂ-linear map `localCoeffₗ y`. `ContMDiffAt` at the
  chart image of `y` via `cotangentSection_contMDiffAt_iff`.
  **Supersedes the prior `chartCoeffAt` API from the 2026-05-16
  HolomorphicOneFormSubsingleton arc** — the local-coeff content is a
  proper extension; downstream `chartCoeffAt`-only consumers can rebase
  onto `localCoeff`.
* `HolomorphicOneFormChartCoeffOnTarget.lean` (338 LOC) —
  `localCoeff_contMDiffOn` on the whole chart target via the cocycle
  transport: at any `y' ∈ (chartAt ℂ y).source`, the chart-`y'` and
  chart-`y` frames are bridged by `coordChange_comp` applied through
  `ContMDiffAt.clm_apply` on the chart-`y'`-frame smoothness (canonical
  bridge) and chart-transition smoothness from
  `cotangentBundleCore.isContMDiff`.
* `CompactDiskChartCover.lean` (201 LOC) — `DiskChartCover X` structure:
  finite base points with outer/inner radii (`outerRadius > innerRadius
  > 0`), `closedDisk_in_target`, and chart-preimage of inner ball
  covers `X`. Existence via `IsCompact.elim_finite_subcover` on
  compact nonempty `X`.
* `DiskChartCoverSeminorm.lean` (252 LOC) — `localCoeffMax cover x om`
  = sup of `‖localCoeff om x ·‖` on the outer closed disk. Bounded
  via `IsCompact.exists_isMaxOn`. Subadditive / smul-homogeneous /
  sign-invariant via `Real.sSup_smul_of_nonneg` + standard sSup api.
* `DiskChartCoverSeminormAggregate.lean` (119 LOC) — `seminormVal cover
  om` = `Finset.sup'` of `localCoeffMax` over base points. Seminorm
  axioms (`_zero`, `_neg`, `_add_le`, `_smul`) via `Finset.sup'_le`,
  `Finset.sup'_congr`, `Finset.mul₀_sup'`.
* `DiskChartCoverCauchyEstimate.lean` (204 LOC) — Cauchy's first-derivative
  estimate on the inner disk via `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`
  with radius `R := outerRadius - dist w (center)`, sharpened to
  `localCoeffMax / (outerRadius - innerRadius)` via
  `div_le_div_of_nonneg_left`.
* `DiskChartCoverLipschitz.lean` (154 LOC) — Lipschitz bound on the
  inner disk via `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`
  + `norm_deriv_eq_norm_fderiv` to bridge `deriv` (used in chip 4) and
  `fderiv` (used by the convex MVT). Strengthened to
  `localCoeff_lipschitz_innerDisk_of_seminorm_le`: Lipschitz constant
  `M / (outerRadius - innerRadius)` independent of `om`.
* `DiskChartCoverArzela.lean` (188 LOC) — per-chart Arzelà-Ascoli via
  `BoundedContinuousFunction.arzela_ascoli`. Packages
  `localCoeff om x | _closedBall (innerRadius)` as
  `localCoeffBcf cover om hx : BoundedContinuousFunction
  ↥(closedBall (innerRadius)) ℂ`. Equicontinuity input via chip 5a's
  Lipschitz bound. Extracts a strictly monotone subsequence convergent
  in the BCF metric.
* `DiskChartCoverDiagonal.lean` (114 LOC) — diagonal subsequence
  convergent at every base point. `Finset.induction_on` builds the
  subseq one base point at a time, refining `ψ_S' ∘ φ` at each step.
* `DiskChartCoverPointwiseLimit.lean` (113 LOC) — `chosenBasePoint cover
  y` (via `Classical.choose` on `cover.covers y`) gives a base point
  with `y` in its inner-ball preimage. `chartLimit_tendsto` produces a
  scalar limit `c_y` for `localCoeff (om_n (ψ k)) (chosenBasePoint y)
  ((chartAt ℂ ...) y) → c_y`.
* `DiskChartCoverCLMLimit.lean` (192 LOC) — CLM-level pointwise limit:
  `(om_n (ψ k)).toFun y → T_lim_y` in `ℂ →L[ℂ] ℂ` (cotangent fibre).
  Uses `clm_eq_smulRight_value_at_one` (a `ℂ →L[ℂ] ℂ` CLM equals
  `smulRight 1 (T 1)`) + `coordChange_comp` cocycle inverse for the
  transport back from chart-`x_y` frame.
* `DiskChartCoverLimitAnalytic.lean` (173 LOC) — `bcfExtend cover g_lim`
  is `AnalyticOn ℂ` on the open inner ball. From BCF convergence on
  closedBall (uniform via `BoundedContinuousFunction.dist_coe_le_dist`)
  → `TendstoLocallyUniformlyOn` on ball (via
  `TendstoUniformlyOn.tendstoLocallyUniformlyOn` + `.mono`) →
  `DifferentiableOn` (via `TendstoLocallyUniformlyOn.differentiableOn`)
  → `AnalyticOn` (via `DifferentiableOn.analyticOn`).
* `DiskChartCoverLimitSection.lean` (79 LOC) — `limitSectionToFun cover
  om_n h_diag : ∀ y, CotangentSpace 𝓘(ℂ) y` via `Classical.choose` on
  the chip 5e existential. `limitSectionToFun_tendsto` packages
  pointwise convergence.
* `DiskChartCoverLimitSmooth.lean` (188 LOC) — chart-`x`-frame
  identification: for `y` in `chart-x.source` with chart-image in the
  inner closed disk, the chart-`x`-frame CLM at `y` of the limit
  equals `smulRight 1 (g_lim_x ⟨(chartAt ℂ x) y, _⟩)`. Proof:
  pointwise convergence (chip 5g) + continuity of `coordChange ...` +
  `tendsto_nhds_unique` against the BCF point-evaluation convergence.
* `DiskChartCoverLimitContMDiff.lean` (109 LOC) — composed
  `smulRight 1 (bcfExtend cover g_lim_x ((chartAt ℂ x) y'))` is
  `ContMDiffAt` at `y` in chart-`x` preimage of the open inner ball.
  Composition of: `chartAt ℂ x` ContMDiffAt (via
  `contMDiffOn_of_mem_maximalAtlas`), `bcfExtend` analytic → ContMDiffAt
  via `AnalyticAt.contDiffAt` + `contMDiffAt_iff_contDiffAt`, and
  `smulRight 1` continuous linear via
  `ContinuousLinearMap.smulRightL`.
* `DiskChartCoverLimitPackage.lean` (184 LOC) — **end-to-end packaging**:
  `limitHolomorphicOneForm cover om_n h_diag : HolomorphicOneForm X`.
  Uses mathlib's `Trivialization.contMDiffAt_section_iff` at
  `trivializationAt _ x` (auto `MemTrivializationAtlas`) for each
  base point `x = chosenBasePoint y`, identifies the snd component
  with the chip 5h+5f form on a neighborhood (via
  `cotangentBundle_trivializationAt_snd_apply` +
  `chartFrame_limit_eq_smulRight` + `bcfExtend_apply`), then applies
  `ContMDiffAt.congr_of_eventuallyEq` with chip 5i's composed
  smoothness.

Build green at **8802 jobs** (+16 from 8786 at session start), zero
`sorry`, zero `axiom`. **2948 LOC across 16 commits.** Remaining
~1,000-1,800 LOC: seminorm convergence (inner→outer multi-chart
bound) + NormedAddCommGroup + separating + Riesz
`FiniteDimensional.of_isCompact_closedBall₀`.

## 2026-05-15 — C3 structural reduction + chain-rule pathway segments 1-3 (13 chips, ~2,280 LOC, FF to `main`)

Two-tier delivery on top of the May-15 path-lift infrastructure, off
`origin/main` at `4081de3` via branch `feat/abel-generator-input-independence`,
fast-forward-merged into `main` at `9a9d45c`.

### Tier 1 — Structural reductions (3 chips, ~822 LOC)

* `Manifold/AbelGeneratorInputIndependence.lean` (+314 LOC) —
  `dischargedGenerators` and `AbelGeneratorPeriodCondition` are
  **invariant under the choice of `AbelJacobiInput`** (basePoint and
  pathFromBase). Proof: the difference of two AJ-chains for a divisor
  `D` has boundary `D.degree • (δ_{B'.base} − δ_{B.base})`; for
  principal divisors `(principalDivisorMap f).degree = 0` via
  `residue_theorem`, so the difference is a smooth cycle and its
  period vector lies in `periodLatticeImage`.

* `Manifold/AbelHypothesisFromLatticeWitness.lean` (+193 LOC) — C3
  reduces to **one named classical input** `AbelLatticeWitness X α h`
  (the Abel-forward existence statement, restricted to non-constant
  `f.toFun`). Constant-`toFun` discharge is internal via
  `principalDivisorMap_of_toFun_const`.

* `Manifold/AbelLatticeWitnessFromRegular.lean` (+192 LOC) +
  `Manifold/MeromorphicNonzeroConstantBridge.lean` (+181 LOC) —
  splits `AbelLatticeWitness` into:
  - `RegularLevelSetLatticeClause` (substantive analytic core: period
    of `regularLevelSetChain f hnc h0 h∞` ∈ `periodLatticeImage`).
  - `AbelLatticeWitnessCriticalCase` (small residual for `0`/`∞`
    critical, classically a Möbius substitution).
  Public bridge `not_isConstantMap_toRiemannSphere_of_toFun_nonconst`
  replicates `R4FibreSumBalance.lean`'s private `isConst_toFun_of_toRS_const`
  / `not_isConstantMap_toRS_infty` (chart-ball + `poles_finite`).

### Tier 2 — Chain-rule pathway segments 1-3 (10 chips, ~1,458 LOC)

Targets the substantive analytic content inside
`RegularLevelSetLatticeClause`. Builds the per-`t` chain-rule identity
on a sub-interval `Ioo 0 δ` end-to-end at the structural level.

* `Manifold/SmoothPathVelocityEqLocal.lean` (+132 LOC) +
  `Manifold/SmoothPathVelocityFromFun.lean` (+132 LOC) — generic
  primitives: `velocity`, `integrand`, and `∫_s^t integrand` are
  invariant under `ambient` pointwise-equality on `Icc s t` (template
  from `velocity_compSmoothPath_of_mem_Ioo`). The `_FromFun` variant
  compares against an external function `f : ℝ → X` (used for
  `f := sheet.g ∘ β ∘ σ`).

* `Manifold/SourceFiberPathAmbientSheetEq.lean` (+121 LOC) — lifts
  `sourceFiberPath_toPath_extend_eq_sheet_g_locally` from
  `toPath.extend` to `ambient`, then composes with
  `integrand_eq_of_ambient_eqOn_Icc_fun` to give the per-fiber-point
  integrand on `Ioo 0 δ` as a chart-level expression.

* `Manifold/SheetGBetaSigmaChainRule.lean` (+140 LOC) — chain rule
  `mfderiv (sheet.g ∘ β ∘ σ) t (1) = mfderiv sheet.g (β(σ t)) (mfderiv β (σ t) (mfderiv σ t (1)))`
  via two `mfderiv_comp_apply` applications, plus a specialised version
  at the base value with realified smoothness from
  `contMDiffAt_localSheet_g_at_basePoint` + `ContMDiffAt.complex_to_real`.

* `Manifold/SourceFiberPathIntegrandChainExpand.lean` (+135 LOC) —
  combines the integrand identification with the chain rule to fully
  expand the per-fiber-point integrand on `Ioo 0 δ`.

* `Manifold/SourceFiberPathIntegrandPullback.lean` (+103 LOC) —
  repackages via `applyCotangent_cotangentPullbackAt`:
  `integrand = applyCotangent (cotangentPullbackAt sheet_p.g (β(σ t)) ω) (β'(σ t) σ'(t))`.

* `Manifold/SumSourceFiberIntegrandPullback.lean` (+93 LOC) — pulls
  `applyCotangent` outside the sourceFiber sum via
  `applyCotangent_finset_sum`.

* `Manifold/LevelSetIntegralChainRuleStructural.lean` (+140 LOC) —
  **structural headline** `sum_sourceFiber_integrand_chain_at`:
  `∑_p integrand(sourceFiberPath p) ω t = applyCotangent (∑_p cotangentPullbackAt sheet_p.g (β(σ t)) ω) (β'(σ t) σ'(t))`.

* `Manifold/SourceFiberUniformDelta.lean` (+195 LOC) — uniform `δ`
  across sourceFiber via `Finset.min'`. Headlines: `perFiberDelta`,
  `uniformFiberDelta` (with `1`-fallback when empty), and the bounds
  `0 < uniformFiberDelta`, `uniformFiberDelta ≤ 1`,
  `uniformFiberDelta ≤ perFiberDelta p`.

* `Manifold/SourceFiberPathAmbientInjOn.lean` (+124 LOC) —
  `sourceFiberPath_toPath_extend_injOn_at`: generalises
  `sourceFiberPath_tgt_injOn` to **any** `t₀ ∈ Icc 0 1`.

* `Manifold/SourceFiberPathAmbientImageAt.lean` (+148 LOC) —
  lift-at-t, fiberFinset membership, `Set.InjOn`-form, and Finset
  image ⊆ `fiberFinset (β(σ t))`. The **injection half** of the
  sourceFiber ↔ `f⁻¹(β(σ t))` bijection is now structurally closed.

### Net status

* `AbelHypothesis B` (any `B`) ← `RegularLevelSetLatticeClause` +
  `AbelLatticeWitnessCriticalCase`. Two named classical inputs.
* Build green at 8808 jobs (+15 over baseline 8793). Zero `sorry`,
  zero `axiom`. No item flips (12/24 unchanged).
* Item-flip blockers for `RegularLevelSetLatticeClause`: the
  surjectivity half of the bijection (cardinality argument via
  `degreeFiber_eq_card_of_regular_witness`, or time-reversal
  generalisation), Lebesgue gluing across the
  `exists_subdivision_hurwitzPatching` cover, σ-reparametrisation,
  and the residue theorem for meromorphic 1-forms on `ℙ¹`.

### Hazards captured

* `Basis` is in `namespace Module` post-mathlib-refactor —
  `open Module` (or `open Submodule Module`) needed in chips that use
  `Basis` directly; transitive import is not enough.
* `Path.extend_extends` deprecated to `Path.extend_apply`.
* `LinearMap.map_smul_of_tower` (for `→ₗ[ℤ]` maps) requires
  `CompatibleSMul` typically unavailable for `SmoothChain` boundary;
  use the unbundled `map_smul` instead.

## 2026-05-15 — `HolomorphicOneFormSubsingletonOfSimplyConnected` arc (13 chips, ~1,510 LOC, direct to `main`)

End-to-end **analytic-side closure** of Item 14's reverse leg via the
simple-connectedness route. Reduces
`HolomorphicOneFormSubsingletonOfSimplyConnected X` (input (b) on the
simple-connectedness route in
`Topology/S2ImpliesGenus0FromSimplyConnected.lean`) to **one named
classical input**: smooth primitive existence under
simple-connectedness (`∀ om, ∃ F smooth with om.eval = mfderiv F`).

### Headline architectural reduction

```lean
theorem holomorphicOneFormSubsingletonOfSimplyConnected_of_primitiveExistence
    (h_primitive_exists : SimplyConnectedSpace X →
        ∀ om : HolomorphicOneForm X,
          ∃ F : X → ℂ,
            ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω F ∧
              ∀ x : X, om.eval x = mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) F x) :
    HolomorphicOneFormSubsingletonOfSimplyConnected X
```

Composed with the existing unconditional `simplyConnectedS2_holds`
(`SimplyConnectedS2Unconditional.lean`) and
`s2ImpliesGenus0_from_simplyConnected`, the reverse leg of Item 14
(`S2ImpliesGenus0 X`) now reduces to a **single named classical
input** — the smooth-Stokes / path-integral primitive on simply-
connected manifolds — captured in
`s2ImpliesGenus0_of_primitiveExistence`.

### Foundation: continuous-homotopy from simple-connectedness

* `Manifold/SmoothPathHomotopyFromSimplyConnected.lean` (~111 LOC) —
  for `[SimplyConnectedSpace X]`, any two `SmoothPath I X` with
  matching endpoints have *continuously* homotopic underlying `Path`s.
  Wraps mathlib's `SimplyConnectedSpace.paths_homotopic` and exposes a
  concrete `Path.Homotopy` witness plus the underlying
  `C(unitInterval × unitInterval, X)` map for downstream smooth-
  approximation chips. `apply_zero` / `apply_one` simp lemmas at the
  homotopy boundaries.

### Liouville chain — unconditional for `ContMDiff ω` on compact connected

* `Manifold/HolomorphicOneFormChartCoeff.lean` (~100 LOC) — general-X
  `HolomorphicOneForm.chartCoeffAt om x : ℂ → ℂ` with pointwise
  linearity (zero / add / neg / sub / smul). General-X analog of
  `RiemannSphere.chartNCoeff`.

* `Topology/LiouvilleForContMDiffOmega.lean` (~373 LOC) — the
  unconditional Liouville for `ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω F : X → ℂ`.
  Three layers:

  1. `mmeromorphicOn_univ_of_contMDiff_omega` +
     `mmeromorphicOrderAt_nonneg_of_contMDiff_omega` — chart-pullback
     analyticity gives `MMeromorphicOn _ univ` and order ≥ 0
     everywhere, via `contMDiff_omega_analyticAt_chart_pullback` +
     `AnalyticAt.meromorphicAt` + `AnalyticAt.meromorphicOrderAt_nonneg`.

  2. `MeromorphicNonzero.ofContMDiffOmega` +
     `contMDiff_omega_isConstant_of_nonvanishGerm` — Liouville
     conditional on a `nonvanishingGerm` hypothesis, via
     `MeromorphicNonzero.ofContinuousMeromorphic` and the existing
     `liouvilleOnCompactConnected_holds`.

  3. `mmeromorphicOrderAt_ne_top_of_contMDiff_omega_neverZero` +
     `contMDiff_omega_isConstant_of_neverZero` — discharges the
     `nonvanishingGerm` hypothesis for never-zero functions via
     `AnalyticAt.analyticOrderAt_eq_zero` (analyticOrderAt = 0 at a
     point where the value is non-zero).

  4. **`contMDiff_omega_complex_exp`** +
     **`contMDiff_omega_complex_exp_comp`** +
     **`contMDiff_omega_isConstant`** — **the unconditional Liouville**.
     Strategy: `exp ∘ F` is `ContMDiff ω` and never zero, so constant
     by layer 3; then `F x − F x₀ ∈ 2π i · ℤ` (kernel of `exp`); a
     continuous `F` into this discrete set is locally constant on
     each `Metric.ball (F x) (2π)`, hence constant by
     `IsLocallyConstant.eq_const` on `PreconnectedSpace X`.

### Closing composition: Subsingleton ⇐ primitive existence

* `Topology/SubsingletonFromPrimitiveExistence.lean` (~268 LOC) —

  - `HolomorphicOneForm.eq_zero_iff_eval` — general-X analog of
    `RiemannSphere.eq_zero_iff_eval_eq_zero`. `om = 0` iff
    `om.eval x = 0` pointwise; via `ContMDiffSection.ext`.

  - `HolomorphicOneForm.eq_zero_of_primitive_const` — pure algebra:
    `om.eval = mfderiv F` pointwise with `F` constant ⇒ `om = 0`, via
    `mfderiv_const`.

  - **`holomorphicOneForm_eq_zero_of_smooth_primitive`** — combines the
    unconditional Liouville (`F` constant) with `mfderiv_const`
    (constant derivative = 0) to land `om = 0`.

  - **`subsingleton_of_primitiveExistence`** — the headline. From
    `∀ om, ∃ F smooth primitive`, derive `Subsingleton`.

  - `HolomorphicOneForm.eq_zero_iff_eval_at_one` +
    `subsingleton_of_eval_at_one_eq_zero` — general-X analogs of the
    RS-specific scalarised variants.

  - **`holomorphicOneFormSubsingletonOfSimplyConnected_of_primitiveExistence`**
    — bridge to the named predicate from
    `S2ImpliesGenus0FromSimplyConnected.lean`.

  - **`s2ImpliesGenus0_of_primitiveExistence`** — full-arc composition.

### `complexChainPeriod` algebraic toolkit

* `Manifold/ComplexChainPeriodFormLinear.lean` (~244 LOC) — completes
  the form-side algebra of `complexChainPeriod c om` (cycle-level
  `complexPeriod` was already in
  `Manifold/ComplexPeriodPairing.lean` /
  `Manifold/ComplexPeriodSmulRight.lean`; this fills the chain level):

  - `complexChainPeriod_zero_right`, `_add_right`, `_neg_right`,
    `_sub_right`, `_smul_real_right` — pointwise linearity in `om`.
  - `complexChainPeriod_smul_complex_right` — full ℂ-scaling via the
    `realComponent_smul` / `imagComponent_smul` real-vs-complex
    mixing.
  - `complexChainPeriod_single_reverse` — `complexChainPeriod (single γ.reverse) om
    = -complexChainPeriod (single γ) om`. Via `SmoothPath.integrate_reverse`.
  - `complexChainPeriod_single_concat` — additivity over path
    concatenation. Via `SmoothPath.integrate_concat`.
  - `complexChainPeriodHomRight` (additive in form), `complexChainPeriodLinearMap`
    (ℂ-linear in form for fixed chain), `complexChainPeriodBilinear`
    (ℤ-additive in chain ⊗ ℂ-linear in form).

### `chartLocalPrimitive` infrastructure (E sub-chips)

* `Manifold/ChartLocalPrimitive.lean` (~236 LOC) —

  - **`chartLocalPrimitive`** — the candidate primitive
    `F(x) := complexChainPeriod (single γ_{x₀,x}) om` where
    `γ_{x₀,x} := SmoothPath.linearInChartSegment φ x₀ x` is the
    C^∞-bumped affine segment in chart coordinates (convex chart target
    discharges the segment-in-target precondition).

  - `bumpedSegment_self` — `bumpedSegment a a t = a` (algebraic).

  - `linearInChartSegment_self_{ambient_eq_on_unitInterval,
    ambient_eventuallyEq_const, velocity_of_mem_Ioo,
    integrand_of_mem_Ioo, integrate}` — the constant-ambient chain at
    coinciding endpoints, mirroring `SmoothPath.integrate_const`'s
    structure.

  - **`chartLocalPrimitive_self`** — `F(x₀) = 0` basepoint identity.

* `Manifold/ChartLocalPrimitiveSmoothness.lean` (~178 LOC) — joint
  continuity foundation for the eventual smoothness-of-F-in-endpoint
  argument:

  - `continuous_bumpedSegment_param z₀` — joint continuity of
    `(z, t) ↦ bumpedSegment z₀ z t` on `ℂ × ℝ`. Routes through
    `Complex.real_smul` to avoid the `ContinuousSMul ℝ ℂ` synth issue.

  - `continuous_chartSymm_bumpedSegment` — joint continuity of
    `(z, t) ↦ φ.symm (bumpedSegment z₀ z t)` on
    `φ.target ×ˢ Set.univ` (uses convex-target hypothesis).

  - `chartCoordVelocity z₀ z t := σ'(t) · (z − z₀)` +
    `continuous_chartCoordVelocity_param z₀` — the chart-coordinate
    path velocity (explicit formula, sidesteps the opaque
    `Classical.choose` of `SmoothPath.ambient`) and its joint
    continuity in `(z, t)`.

These joint-continuity foundations are the first sub-step of the
*continuity-of-`chartLocalPrimitive`-in-endpoint* sub-chip. Completing
the full `Continuous (fun x ↦ chartLocalPrimitive ... x)` requires
expressing `γ_z.integrand om` as a chart-coord formula equal a.e. on
`Ioo 0 1` to a jointly-continuous expression, then applying
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`.
The remaining gap is the chart-coord identification of `γ_z.velocity`
with `chartCoordVelocity` post-`dφ.symm`, which needs the
`mfderiv`-of-chart-inverse joint continuity in the bundle setting.

### Net effect on the strict-closed scoreboard

No item flips in this commit. Item 14 remains OPEN, but **input (b)
of the simple-connectedness route**
(`HolomorphicOneFormSubsingletonOfSimplyConnected X`) now reduces
cleanly to a single named classical input (primitive existence under
simple-connectedness). The full chain:

```
Item 14 (genus_eq_zero_iff_homeo)
  reverse leg ⇐ s2ImpliesGenus0_of_primitiveExistence (this commit)
    ⇐ SimplyConnectedS2 (discharged unconditionally 2026-05-15)
    ⇐ primitive existence under simple-connectedness ← THE remaining input
```

Build: 8793 jobs, zero `sorry`, zero `axiom`.

## 2026-05-15 — Local identification of `sourceFiberPath` with `sheet.g ∘ β ∘ σ` (1 chip, ~222 LOC, direct to `main`)

Concrete identification of the `Classical.choose`-opaque
`sourceFiberPath p` with the explicit local-sheet pullback
`sheet_p.g ∘ β ∘ Real.smoothTransition` on a sub-interval `[0, δ]`.

**New file** (`Manifold/MeromorphicNonzeroSourceFiberPathSheetEq.lean`,
~222 LOC):

* `sourceFiberPath_toPath_extend_eq_sheet_g_locally` — for `x` over
  `β 0` and the local sheet centered at `x`, there exists `δ ∈ (0, 1]`
  such that `(sourceFiberPath p).toPath.extend t = sheet.g (β (σ t))`
  pointwise for `t ∈ [0, δ]`.

The proof composes:

* Continuity of `β ∘ σ` at `0`, with `β 0 ∈ sheet.V` (sheet target
  neighborhood of `f x`), gives `δ₁ > 0` such that `β(σ [0, δ₁]) ⊆
  sheet.V`.
* Continuity of `toPath.extend` at `0`, with `x ∈ sheet.U` (sheet
  source neighborhood), gives `δ₂ > 0` such that `toPath.extend [0,
  δ₂] ⊆ sheet.U`.
* `δ := min (min δ₁ δ₂) 1`. On `[0, δ]`:
  - Both paths lift `β ∘ σ` (one via `sourceFiberPath_toPath_lifts`,
    the other via `sheet.rightInvOn` at the codomain side).
  - Both agree at `t = 0` (`(sourceFiberPath p).src = x` and
    `sheet.g (f x) = x` via `sheet.leftInvOn`).
* Apply `path_lift_eqOn_Icc_of_continuousOn` (just landed in
  `MeromorphicNonzeroPathLiftUniqueOnContinuousOn.lean`).

This is the **local** identification. The global identification on
`[0, 1]` requires a subdivision argument over a finite open cover of
the β-image by sheet domains (a future chip).

Net for the trace integral: combined with the scalar bridging in
`CotangentPullbackAtApply.lean`, the chain-rule identity
`(sourceFiberPath p).integrand om t = applyCotangent
(cotangentPullbackAt sheet_p.g (β(σ t)) om)
(mfderiv (β ∘ σ) ...)` becomes derivable on `Ioo 0 δ`, since on this
sub-interval the source-fiber-path coincides explicitly with the
sheet pullback.

Build: 8786 jobs (was 8785), zero `sorry`, zero `axiom`.

## 2026-05-15 — `ContinuousOn` variant of `path_lift_eqOn_Icc` (1 chip, ~131 LOC, direct to `main`)

Sister lemma to `path_lift_eqOn_Icc` that accepts `ContinuousOn γᵢ
(Icc a b)` instead of global `Continuous γᵢ`. The variant needed to
identify `(sourceFiberPath p).toPath` with the locally-defined
`sheet_p.g ∘ β ∘ σ` on sub-intervals where `sheet_p.g` is only
continuous on a neighborhood of `β(σ ·)`'s image.

**New file** (`Manifold/MeromorphicNonzeroPathLiftUniqueOnContinuousOn.lean`,
~131 LOC):

* `path_lift_eqOn_Icc_of_continuousOn` — two lifts of `β` on `Icc a b`
  that are merely `ContinuousOn (Icc a b)` (not globally continuous on
  ℝ) and agree at some `t₀ ∈ Icc a b` agree on all of `Icc a b`.

The proof mirrors the existing `path_lift_eqOn_Icc`'s clopen argument
in the subspace topology, with `continuousOn_iff_continuous_restrict`
replacing `Continuous.comp continuous_subtype_val` to extract
subspace-level continuity from the `ContinuousOn` hypothesis. The
`preimage_mem_nhds` step stays inside the subspace via the
subspace-restricted function's `ContinuousAt`.

This unblocks the next chip in the f_*ω stack: identification of
`(sourceFiberPath p).toPath` with `sheet_p.g ∘ β ∘ σ` on sub-intervals
where `β(σ ·)` lands in `sheet_p.V`. Combined with the scalar bridging
of `cotangentPullbackAt` + `traceAt` (in
`CotangentPullbackAtApply.lean`), the chain-rule statement
`(sourceFiberPath p).integrand om t = applyCotangent
(cotangentPullbackAt sheet_p.g (β t) om) (β.velocity t)` becomes
provable on each sub-interval, and via subdivision over the cover of
`[0, 1]` by sheet pre-images, globally on `Ioo 0 1`.

Build: 8785 jobs (was 8784), zero `sorry`, zero `axiom`.

## 2026-05-15 — Scalar evaluation of cotangent pullback and trace (1 chip, ~123 LOC, direct to `main`)

Scalar-level bridging lemmas between `cotangentPullbackAt`/`traceAt`
and the path-integral machinery (`applyCotangent` + `SmoothPath.integrand`).

**New file** (`Manifold/CotangentPullbackAtApply.lean`, 123 LOC):

* `applyCotangent_cotangentPullbackAt` — for any smooth `g : Y → X`,
  `y : Y`, `om : SmoothOneForm I X`, `v : E'`:
  `applyCotangent (cotangentPullbackAt g y om) v = applyCotangent (om (g y))
  (mfderiv g y v)`. Pure definitional unfold.

* `applyCotangent_finset_sum` — pairing is linear in the cotangent
  argument: `applyCotangent (Σ_i φ_i) v = Σ_i applyCotangent (φ_i) v`.
  Via `ContinuousLinearMap.sum_apply` + `cotangentEquiv`'s identity-as-CLM.

* `MeromorphicNonzero.applyCotangent_traceAt` — scalar pairing of the
  trace: `applyCotangent (traceAt f hnc hv om) w = Σ_{p ∈ fiberFinset}
  applyCotangent (cotangentPullbackAt sheet_p.g v om) w`. Follows from
  the linear-sum lemma applied to the definition of `traceAt`.

These are the scaffolding for the eventual Stokes-type integral
identity

  `(levelSetChain f β).integrate om = ∫ t in 0..1, applyCotangent
    (traceAt f hnc (hβ_reg t) om) (β.velocity t)`

which expresses the X-chain integral as a ℙ¹-line integral against the
trace 1-form `f_*ω`. The chain-rule piece tying
`(sourceFiberPath p).integrand om t` to `applyCotangent
(cotangentPullbackAt sheet_p.g (β t) om) (β.velocity t)` requires the
identification `(sourceFiberPath p).toPath ≡ sheet_p.g ∘ β ∘
Real.smoothTransition`, which is opaque (Classical.choose) in the
current infrastructure and will be the next chip's content.

Build: 8784 jobs (was 8783), zero `sorry`, zero `axiom`.

## 2026-05-15 — `SmoothOneFormOn` partial-section type (1 chip, ~74 LOC, direct to `main`)

Foundational chip for the trace `f_*ω` as a smooth 1-form on the open
subset `regularValueSet f`.

**New file** (`Manifold/SmoothOneFormOn.lean`, 74 LOC):

* `SmoothOneFormOn I X s` — a structure bundling:
  - `toFun : ∀ x : X, CotangentSpace I x` (global function-valued
    section; junk allowed outside `s`).
  - `contMDiffOn_section` : the total-space lift
    `x ↦ ⟨x, toFun x⟩ : X → Bundle.TotalSpace (E →L[ℝ] ℝ)
    (CotangentSpace I)` is `ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ⊤`
    on `s`.

This mirrors `SmoothOneForm I X` (which uses `ContMDiffSection` for
global sections) but allows the smoothness witness to be restricted to
a subset. Required for `f_*ω` whose natural domain is the open subset
`regularValueSet f ⊂ ℙ¹`.

Subsequent chips will:

* Show that the pointwise `traceAt f hnc hv om` (from
  `MeromorphicNonzeroTraceAt.lean`) assembles into a
  `SmoothOneFormOn 𝓘(ℝ, ℂ) RiemannSphere (regularValueSet f)`.
* Define `SmoothPath.integrateOn` for paths landing in the partial
  domain.

This file ships only the type definition + a `CoeFun` instance.
Algebra (`AddCommGroup`, `Module ℝ`) and a `restrictOn` map from
`SmoothOneForm` are deferred.

Build: 8783 jobs (was 8782), zero `sorry`, zero `axiom`.

## 2026-05-15 — Pointwise trace `f_*ω` at a regular value (1 chip, ~117 LOC, direct to `main`)

Combines `cotangentPullbackAt` with the fibre-finiteness infrastructure
to give the **pointwise trace** `f_*om` at a regular value.

**New file** (`Manifold/MeromorphicNonzeroTraceAt.lean`, 117 LOC):

* `fiberFinset f hv : Finset X` — the fiber `f⁻¹({v})` at a regular
  value `v`, packaged as a `Finset`. Uses
  `fiber_finite_of_mem_regularValueSet`.
* `mem_fiberFinset_iff` — membership characterised by
  `f.toRiemannSphere x = v`.
* `traceAt f hnc hv om : CotangentSpace 𝓘(ℝ, ℂ) v` — the trace, a
  finite sum of per-sheet `cotangentPullbackAt` contributions over the
  fiber. Each sheet's local inverse comes from
  `f.localSheetData_at_regular hnc hp_reg` where `hp_reg` is derived
  from `mem_regularSet_of_preimage_regularValue`.
* `traceAt_zero`, `traceAt_add`, `traceAt_smul` — ℝ-linearity of the
  trace in the 1-form argument, via the underlying
  `cotangentPullbackAt_{zero, add, smul}` + `Finset.sum_{zero,
  add_distrib, smul_sum}`.

This is the **pointwise** `f_*ω`. Smoothness of `v ↦ traceAt f hnc hv
om` as a function of `v` is a separate downstream layer.

Build: 8782 jobs (was 8781), zero `sorry`, zero `axiom`.

## 2026-05-15 — Pointwise cotangent pullback primitive (1 chip, ~94 LOC, direct to `main`)

The foundational pointwise primitive for the trace construction
`f_*ω` on regular values.

**New file** (`Manifold/CotangentPullbackAt.lean`, 94 LOC):

* `cotangentPullbackAt (g : Y → X) (y : Y) (om : SmoothOneForm I X) :
  CotangentSpace I' y` — defined as `(om (g y)).comp (mfderiv g y)`.
  Takes a smooth map between real C^∞ manifolds and a 1-form on the
  codomain; produces the pulled-back cotangent vector at the domain
  point.
* `cotangentPullbackAt_zero` — zero 1-form pulls back to zero.
* `cotangentPullbackAt_add` — additivity in the 1-form.
* `cotangentPullbackAt_smul` — ℝ-linearity in the 1-form.

This is the per-point/per-sheet primitive for the trace `f_*ω` at a
regular value `y`: summing `cotangentPullbackAt sheet.g y om` over the
finite fiber (`f.sourceFiber y`) of `f` produces the trace cotangent.
Smoothness of the trace as a function of `y` is a separate layer
(needs the smooth local-sheet structure + sum continuity).

Build: 8781 jobs (was 8780), zero `sorry`, zero `axiom`.

## 2026-05-15 — Real-model RS manifold + open-set realification (1 chip, ~96 LOC, direct to `main`)

Foundation chip for downstream `SmoothOneForm 𝓘(ℝ, ℂ) RiemannSphere`
work (in particular the `f_*ω` trace construction on `regularValueSet`).

**New file** (`Manifold/RiemannSphereRealManifold.lean`, 96 LOC):

* Documents the auto-derived real-model RS instances via `inferInstance`
  examples for `n : WithTop ℕ∞`, `∞`, `⊤`. The instance chain is
  `RiemannSphere.instIsManifold` (complex-analytic ω) →
  `complexManifoldRealification` (generic conversion) →
  `IsManifold 𝓘(ℝ, ℂ) n RiemannSphere`. No new content — just a
  discoverable reference point for downstream files.

* `ContMDiffOn.complex_to_real_of_isOpen` — sister lemma to the
  existing pointwise `ContMDiffAt.complex_to_real` (in
  `Manifold/ContMDiffRealification.lean`), generalised to smoothness
  on an *open* subset. Converts `ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g u`
  to `ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ g u` via pointwise application of
  `ContMDiffAt.complex_to_real` on each `x ∈ u` (using `IsOpen.mem_nhds`
  to extract `ContMDiffAt` from `ContMDiffOn`).

This is the workhorse for converting the complex-analytic local-sheet
smoothness (`exists_contMDiffOn_localSheet_g_near_basePoint` produces
`ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω`) into the real-smooth regularity
required by `SmoothOneForm` pullbacks.

Build: 8780 jobs (was 8779), zero `sorry`, zero `axiom`.

## 2026-05-15 — Concrete regular level-set chain (1 chip, ~146 LOC, direct to `main`)

Wires the β-existence chip into the level-set chain construction.

**New file** (`Manifold/MeromorphicNonzeroConcreteLevelSetChain.lean`, 146 LOC):

* `regularBeta f hnc h0_reg h_inf_reg : ℝ → RiemannSphere` — the
  `Classical.choose` extraction of the regular path from
  `exists_regular_path_zero_to_infty`.
* `regularBeta_{smooth, zero, one, regular}` — the four spec properties,
  re-exported from `Classical.choose_spec` as standalone lemmas
  (`@[simp]` on the endpoint ones).
* `regularLevelSetChain f hnc h0_reg h_inf_reg : SmoothChain 𝓘(ℝ, ℂ) X`
  — the level-set chain on the concrete β, built by composing
  `f.levelSetChain` with the smooth + regular witnesses.
* `boundary_regularLevelSetChain` — the boundary identification
  `(boundary regularLevelSetChain).toFun x = -principalDivisorMap f x`
  pointwise. One-line composition of step 7d-d's
  `boundary_levelSetChain_eq_neg_principalDivisorMap_pointwise` with
  `regularBeta_zero` and `regularBeta_one`.

**Net.** For `f` with `0, ∞ ∈ regularValueSet`, the boundary clause of
`h_struct` in `abelGeneratorPeriodCondition_of_levelSet_lattice` is
now **mechanically discharged** for the explicit witness
`Z := f.regularLevelSetChain hnc h0_reg h_inf_reg`. Only the
**lattice-period clause** remains — the analytical residual
(`f_*ω` SmoothOneForm construction + Stokes/residue argument).

Build: 8779 jobs (was 8778), zero `sorry`, zero `axiom`.

## 2026-05-15 — Regular β: 0→∞ existence on ℙ¹ (1 chip, ~431 LOC, direct to `main`)

Lands the **β-existence input** for step 9's structural reduction. Given
`f : MeromorphicNonzero X` non-constant with both `0` and `∞` regular
values, produces a smooth `β : ℝ → RiemannSphere` with `β 0 = 0`,
`β 1 = ∞`, and `β t ∈ f.regularValueSet` for all `t ∈ [0, 1]`.

This is the β that the level-set chain construction
(`MeromorphicNonzeroLevelSetChain.lean` + downstream) consumes. Combined
with step 7d-d's boundary identification, it concretely wires the
boundary clause of `h_struct` in
`abelGeneratorPeriodCondition_of_levelSet_lattice` — only the
**lattice-period clause** for `levelSetChain f β` remains as the
analytical residual.

**New file** (`Manifold/MeromorphicNonzeroRegularPath.lean`, 431 LOC):

* `exists_s_avoiding_critical` — for any finite `S ⊂ ℂ`, there exists
  `s : ℝ` such that `s * w.im ≠ w.re` for every `w ∈ S` with `w.im > 0`.
  (Pure cardinality: ℝ infinite, the forbidden set `{w.re / w.im}` finite.)
* `chartN_segment_mem_regularValueSet` — for such `s`, the chartN
  segment `{t (s + i) | t ∈ [0, 1]}` in ℂ avoids `chartN`-images of
  critical values. Uses `0 ∈ regularValueSet` to kill the `t = 0`
  endpoint.
* `chartS_segment_mem_regularValueSet` — symmetric. The chartS segment
  from `1/(s + i)` to `0` avoids `chartS`-images of critical values
  via the reciprocal formula `arg(1/w) = -arg w` (reduced to the same
  `s = w.re/w.im` condition by direct computation). Uses
  `∞ ∈ regularValueSet` for the `0` endpoint.
* `exists_regular_path_zero_to_infty` — the headline. Builds two
  `SmoothPath.linearInChartSegment` paths through the bridge point
  `r := some(s + i)`, concatenates via `SmoothPath.concat`, and extracts
  the underlying `ℝ → RS` ambient smooth function from
  `SmoothPath.ambient`. Endpoint identities via
  `ambient_eq_on_unitInterval` + `Path.source'/target'`. Regularity on
  `[0, 1]` by case-splitting `t ≤ 1/2` vs `t > 1/2` and applying the two
  segment lemmas to each half's chart-pullback.

Build: 8778 jobs (was 8777), zero `sorry`, zero `axiom`.

## 2026-05-15 — `h_AJ_boundary` discharged (1 chip, ~125 LOC, direct to `main`)

Discharges the second named-hypothesis input of step 9
(`abelGeneratorPeriodCondition_of_levelSet_lattice`) unconditionally.

After yesterday's C3 staircase steps 1–9 landed, step 9's structural
reduction still took two named inputs: `h_struct` (existence of a chain
`Z` with the boundary identity AND lattice period) and `h_AJ_boundary`
(boundary of `principalDivisorAJChain` = principal divisor pointwise).
This chip dispatches `h_AJ_boundary` to a discharged lemma, leaving only
the analytical-content `h_struct` (`f_*ω` pushforward + Stokes/residue)
as the residual.

**New file** (`Manifold/PrincipalDivisorAJChainBoundary.lean`, 125 LOC):

* `AbelJacobiInput.boundary_principalDivisorAJChain_apply_of_degree_zero`
  — for any `D : Div X` with `D.degree = 0`,
  `(boundary (principalDivisorAJChain D)).toFun y = D y` pointwise. Pure
  ℤ-linearity: unfold the sum, push `boundary` through with
  `LinearMap.map_smul`, evaluate at `y`, split as `D y − D.degree •
  δ_basePoint(y)`, and absorb the second term via `hD : D.degree = 0`.
* `AbelJacobiInput.boundary_principalDivisorAJChain_principalDivisorMap`
  — the `D := principalDivisorMap f` specialisation, discharging the
  degree hypothesis via `JacobianChallenge.residue_theorem`.

**Refactor**
(`Manifold/MeromorphicNonzeroAbelGeneratorFromLevelSet.lean`): the
`h_AJ_boundary` parameter is dropped from
`abelGeneratorPeriodCondition_of_levelSet_lattice`; the proof now uses
the discharged lemma internally. No callers had bound the old
signature.

**Net.** Step 9's structural reduction now takes one named-hypothesis
input (`h_struct`) instead of two. The residual analytical content for
full step 9 — the `f_*ω` pushforward 1-form construction + Stokes on
β: 0 → ∞ in ℙ¹ — is unchanged in scope (~800–1,500 LOC by the
CLOSURE_MAP §F.3 estimate).

## 2026-05-14 — C3 staircase steps 1–9 fully landed (15 chips, ~2,582 LOC, `feat/c3-staircase` direct to `main`)

Discharges the entire 9-step C3 general-genus staircase (HANDOFF
`HANDOFF_2026_05_15_C3_PATH_LIFT.md`) as 15 chip files. Step 7 was
split into 7a/b/c/d-a/d-b/d-c/d-d to keep each chip standalone-useful;
step 9 landed as a structural reduction with a named-hypothesis
`h_struct` input for the residual `f_*ω + Stokes` content.

**Path-lift trunk** (steps 1–4, ~823 LOC):

* `MeromorphicNonzeroPathLiftClosed.lean` (331 LOC) — closedness
  `sSup ∈ liftReachable` via `CompactSpace.tendsto_subseq` (with
  `ChartedSpace.secondCountable_of_sigmaCompact` deriving
  SecondCountable ⇒ FirstCountable ⇒ SeqCompact on `X`) + clip+if_le
  patching from chip 24 of c3_path_lift.
* `MeromorphicNonzeroPathLiftExistsOnIcc.lean` (117 LOC) — clopen
  finish `sSup = T` (openness contradicts strict <T) + headline
  `exists_continuous_lift_on_Icc`.
* `MeromorphicNonzeroPathLiftSmoothOnIcc.lean` (225 LOC) — smooth
  upgrade `ContMDiffOn ∞ γ (Icc 0 T)` via per-point
  `ContMDiffWithinAt.congr_of_eventuallyEq_of_mem` against
  chip 15's local smooth lift.
* `MeromorphicNonzeroPathLiftSmoothPath.lean` (~150 LOC, also exposes
  the toPath lift identity via a follow-up amend) —
  `exists_smoothPath_of_lift_on_unitInterval` packages the smooth lift
  into `SmoothPath 𝓘(ℝ, ℂ) X` via the `Real.smoothTransition` σ
  reparametrisation trick (γ ∘ σ is globally `ContMDiff ∞` because
  σ([0,1]) ⊆ [0,1] and γ is `ContMDiffOn ∞` on `[0,1]`).

**Level-set chain** (steps 5–6, ~281 LOC):

* `MeromorphicNonzeroLevelSetChain.lean` (~170 LOC) — `sourceFiber`
  as Finset, `sourceFiberPath` classical-chosen per fiber point,
  `levelSetChain` as the Finset sum, plus `sourceFiberPath_toPath_lifts`
  bridging to the underlying β ∘ σ reparametrisation.
* `MeromorphicNonzeroLevelSetChainBoundary.lean` (111 LOC) —
  `sourceFiberDivisor` + `targetFiberDivisor` + `boundary_levelSetChain
  = target - source` via `boundary_single` linearity.

**Target-map bijection** (steps 7a/b/c, 584 LOC):

* `MeromorphicNonzeroLevelSetTargetInjective.lean` (151 LOC) —
  `sourceFiberPath_tgt_injOn` via `Path.extend` + `path_lift_eqOn_Icc`
  on `β ∘ Real.smoothTransition`.
* `MeromorphicNonzeroLevelSetTargetSurjective.lean` (240 LOC) —
  `sourceFiberPath_tgt_surjOn` via time-reverse β + step 4 at y +
  step 2 raw lift + double `path_lift_eqOn_Icc` (one for β ∘ τ from
  back-path, one for β ∘ σ from forward-path, common γ_raw).
* `MeromorphicNonzeroLevelSetTargetFiber.lean` (193 LOC) — `targetFiber`
  Finset, `sourceFiberPath_tgt_image_eq_targetFiber` Finset bijection,
  `boundary_levelSetChain_eq_fiberDiff` headline.

**Principal-divisor identification** (step 7d, 643 LOC):

* `MeromorphicNonzeroPrincipalDivisorOffFiber.lean` (110 LOC) — order
  = 0 off-fiber via `tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero`
  using `f.regular_continuousAt` for chart-pullback continuity.
* `MeromorphicNonzeroPrincipalDivisorAtZero.lean` (198 LOC) — order
  = 1 at simple zero via chart-pullback eventual equality
  (`chartPullback_eventuallyEq_toFun_at_finite`) +
  `AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero` +
  `deriv_chartPullback_ne_zero_of_regular`.
* `MeromorphicNonzeroPrincipalDivisorAtPole.lean` (188 LOC) — order
  = -1 at simple pole via `MMeromorphicAt.iff_of_isManifold`
  (chart-independence lifting `f.toFun ∘ chart.symm` to
  `MeromorphicOn chart.target`) +
  `MeromorphicOn.eventually_analyticAt` (pole isolation) +
  `meromorphicOrderAt_inv` (sign flip).
* `MeromorphicNonzeroLevelSetPrincipalDivisorIdentification.lean`
  (147 LOC) — pointwise `(∂ levelSetChain) x = -(principalDivisorMap
  f) x` via `boundary_levelSetChain_eq_fiberDiff` + case split on
  fiber membership + Finset.sum_ite_eq' evaluation of the indicator
  Finsupp sums.

**Integral linearity + structural reduction** (steps 8, 9, 236 LOC):

* `MeromorphicNonzeroLevelSetIntegrate.lean` (98 LOC) —
  `integrate(levelSetChain)` Finset-sum expansion via
  `SmoothChain.integrateLinearMap` ℤ-linearity.
* `MeromorphicNonzeroAbelGeneratorFromLevelSet.lean` (138 LOC) —
  `abelGeneratorPeriodCondition_of_levelSet_lattice`: if any chain
  Z exists with boundary = -principalDivisorMap f (Finsupp pointwise)
  AND `complexChainPeriodVector α Z ∈ periodLatticeImage`, then
  `AbelGeneratorPeriodCondition B` holds. Cycle Z + AJ has boundary
  0, period in lattice tautologically, linearity gives AJ's period
  ∈ lattice − period(Z) ⊆ lattice (AddSubgroup.sub_mem).

**LOC calibration:** every chip landed within or below HANDOFF
estimate. Aggregate session LOC (~2,582) vs aggregate HANDOFF
estimate (1,830–3,220 LOC for steps 5–9) is in the middle of the
estimate range — first session this has held cleanly.

**Build:** `taskpolicy lake build` green at 8776 jobs across 17 chip
+ doc commits. Zero `sorry`, zero `axiom`. Items 4/5/10/11/12/13
remain STUB/OPEN — these flip when the residual `f_*ω + Stokes`
content for `h_struct`'s lattice clause discharges.

## 2026-05-14 — `SimplyConnectedS2` UNCONDITIONAL via polygonal approximation (15 chips, branch `feat/phase3-s2-simply-connected`)

Closes the Phase-3 item-14 reverse-leg's named hypothesis
`SimplyConnectedS2 = SimplyConnectedSpace JacobianChallenge.StandardS2`
unconditionally at this mathlib pin. The simple-connectedness route in
`Topology/S2ImpliesGenus0FromSimplyConnected.lean` now reduces to a
single remaining input — the analytic chain
`HolomorphicOneFormSubsingletonOfSimplyConnected X` — instead of two.

**Reduction-chain chips** (chips 1-3, ~390 LOC).

* `SimplyConnectedS2Reduction.lean` — narrows `SimplyConnectedS2` to
  `S2LoopsNullHomotopic` by discharging path-connectedness of the
  unit sphere in `EuclideanSpace ℝ (Fin 3)`
  (`isPathConnected_sphere` + rank ≥ 2 + subtype lift).
* `S2PuncturedSimplyConnected.lean` — for any unit `v`, the punctured
  sphere `↥(stereographic hv).source` is `ContractibleSpace` via the
  stereographic homeomorphism into `(ℝ ∙ v)ᗮ` (a real top vec space),
  hence `SimplyConnectedSpace`. `s2LoopAvoidingNullHomotopic` follows
  by lifting the loop through the inclusion + `paths_homotopic` +
  `Path.Homotopic.map`.
* `S2LoopsNullHomotopicReduction.lean` — single-hypothesis composition.

**Smoothing-infrastructure chips** (chips 4a-c, ~430 LOC).

* `S2TwoChartCover.lean` — two stereographic charts at `v` and `-v`
  cover the sphere (witness `ne_neg_self_of_norm_one`).
* `S2LoopLebesgueSubdivision.lean` — `lebesgue_number_lemma` applied
  to the two-chart preimage cover of `unitInterval`, converted to a
  metric `δ > 0` via `Metric.mem_uniformity_dist`.
* `S2LoopChartPartition.lean` — equidistant `Fin N → Set` chart
  assignment with `1/N < δ` from `exists_nat_gt`; midpoint argument
  bounds each `[k/N, (k+1)/N]` inside `Metric.ball (ck k) δ`.

**Smoothing reduction** (chips 4e, 4i', 4i'', ~250 LOC).

* `S2LoopAvoidingFromNonSurjective.lean` — reduces
  `S2LoopHomotopicToAvoidingLoop` to the pure-topology hypothesis
  `EveryS2LoopHomotopicToNonSurjective`. Picks the missing point as
  the chart's pole.
* `S2SingleChartLoopNonSurjective.lean` — single-chart corollary.
* `S2PartitionVertices.lean` — `Fin (N+1) → unitInterval`, `k ↦ ⟨k/N, _⟩`.

**Dimensional argument** (chips 4d, 4f, 4g, 4h, ~580 LOC).

* `S2EquatorialBeltPathConnected.lean` — `S² ∖ {v, -v}` is
  path-connected. Uses `finrank_orthogonal_span_singleton` to show
  `(ℝ ∙ v)ᗮ` has rank 2, then `isPathConnected_compl_singleton_of_one_lt_rank`
  on `(ℝ ∙ v)ᗮ ∖ {0}` and transport via the stereographic
  homeomorphism (using `stereographic_apply_neg` to identify
  `⟨-v, _⟩ ↦ 0`).
* `S2StereographicStraightLine.lean` — canonical
  `(stereographic hv).symm`-pullback of a line segment in `(ℝ ∙ v)ᗮ`
  as a `Path p q`. Any in-chart `γ` is `Path.Homotopic` to it via
  chip 2's `S2Punctured.instSimplyConnectedSpace`.
* `S2SegmentEmptyInterior.lean` — line segment in `(ℝ ∙ v)ᗮ` has
  empty interior. Uses `Convex.interior_nonempty_iff_affineSpan_eq_top`
  + `vectorSpan_pair` + `finrank_span_singleton ≤ 1` vs `finrank ⊤ = 2`.
* `S2StraightLineNowhereDense.lean` — transports the segment's
  empty-interior result to the sphere level via the stereographic
  homeomorphism + `Homeomorph.isOpenMap`.

**Polygonal closure** (chip 4j, ~370 LOC + capstone, ~50 LOC).

* `S2EveryLoopHomotopicNonSurjective.lean` — `everyS2LoopHomotopicToNonSurjective_holds`.
  Builds `γ' := Path.concat (γ ∘ partitionVertex) stereographicStraightLine_k . cast _ _`,
  shows `γ ≃ γ'` via `Path.Homotopic.concat_subpath.symm + concat_hcomp`
  + a `Path.cast = γ.subpath (pV 0) (pV last)` path-equality via
  `DFunLike.coe_injective + Icc.coe_convexCombo + ring`. Cast across
  endpoint types via local `homotopyRecastEndpoints` helper
  (reusing the underlying continuous function). Non-surjectivity
  via `range_concat_subset_iUnion_of_pos + interior_iUnion_closed_empty`
  Baire-style induction.
* `SimplyConnectedS2Unconditional.lean` — capstone:
  `simplyConnectedS2_holds : SimplyConnectedS2` by composing
  `everyS2LoopHomotopicToNonSurjective_holds` with the chip-1/3/4e
  reduction chain. **Zero hypotheses.**

Total: **15 chips, ~3000 LOC, zero `sorry`, zero `axiom`**, all
locally verified via `LEAN_NUM_THREADS=1 lake env lean FILE.lean`.

## 2026-05-14 — C3 sub-arc: algebra closure + path-lift infrastructure (25 chips)

Continued past the 19-chip set above with six further chips on the
inductive global path lift:

* `Manifold/MeromorphicNonzeroPathLiftAtPoint.lean` (chip 20) —
  `exists_sheet_data_extending_to_right` and
  `extend_continuous_lift_to_right`: per-point extension primitive
  using local sheet at the current lift endpoint plus chip 19.

* `Manifold/MeromorphicNonzeroPathLiftSequencePatch.lean` (chip 21) —
  `lifts_agree_globally` and `lifts_agree_at`: choice-independence of
  patched lifts via chip 16 (uniqueness).

* `Manifold/MeromorphicNonzeroPathLiftUniqueOn.lean` (chip 22) —
  `path_lift_eqOn_Icc`: strengthens chip 16 to lifts defined only on
  `Icc a b`.  Clopen argument inside the connected subspace.

* `Manifold/MeromorphicNonzeroPathLiftGlobal.lean` (chip 23) —
  `liftReachable f β x₀ T` definition + `zero_mem_liftReachable` +
  `liftReachable_downward_closed`.

* `Manifold/MeromorphicNonzeroPathLiftGlobalOpen.lean` (chip 24) —
  `liftReachable_extends_right`: openness via clip+if_le construction.
  Globally-continuous lift built as `if t ≤ b then γ t else sheet.g
  (β (clip t))` where `clip t := max b (min (b + ε) t)` keeps β
  inside `sheet.V`; both pieces globally continuous + agreement at b
  ⇒ `Continuous.if_le`.

* `Manifold/MeromorphicNonzeroPathLiftGlobalClosed.lean` (chip 25) —
  `liftReachable_subset_Icc`, `liftReachable_bddAbove`,
  `sSup_liftReachable_le`, `sSup_liftReachable_nonneg`: boundedness +
  sSup bounds setting up the closedness/clopen argument for the
  global lift.

**Net open content after the 25 chips.** Closing C3 (general genus)
reduces to: (i) the substantive closedness `sSup ∈ liftReachable`
(local-sheet-limit argument); (ii) clopen+univ in connected
`[0, T]`; (iii) smoothness upgrade of the global lift to SmoothPath
regularity; (iv) `levelSetChain f β` definition; (v) boundary
computation + Stokes/lattice argument.

Build at HEAD: `taskpolicy lake build` green, 8746 jobs. Zero `sorry`,
zero `axiom`. +~2,900 LOC across 19 new files today.

## 2026-05-14 — C3 sub-arc: algebra closure + path-lift infrastructure (19 chips)

Extending the same-day work past the 11-chip set, eight further chips
landed on the path-lift portion:

* `Manifold/MeromorphicNonzeroLocalSheetSmooth.lean` (chip 12, ~190 LOC)
  — `contMDiffAt_localSheet_g_at_basePoint`: pointwise `ContMDiffAt ω`
  of the manifold local-sheet inverse at the base point.  Via
  `contMDiffAt_omega_of_analyticAt_chart_pullback` applied to
  `manifoldLocalOph.symm`, with the chart pullback shown to locally
  equal `φ.symm` (planar inverse from chip 6) on an open subset of `ℂ`
  containing `d v₀`.

* `Manifold/MeromorphicNonzeroSmoothLocalLift.lean` (chip 13, ~90 LOC)
  — `contMDiffAt_local_lift_at_basepoint`: the lift `sheet.g ∘ β` is
  `ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞` at `t₀`.  Composition: chip 12 +
  `ContMDiffAt.complex_to_real` (realification) + `ContMDiffAt.comp`.

* `Manifold/MeromorphicNonzeroLocalSheetSmoothOn.lean` (chip 14, ~65
  LOC) — `exists_contMDiffOn_localSheet_g_near_basePoint`: extracts
  open nbhd of `v₀` with `ContMDiffOn 𝓘(ℂ, ℂ) ω sheet.g` via
  `contMDiffAt_iff_contMDiffOn_nhds` (valid at `ω ≠ ∞`).

* `Manifold/MeromorphicNonzeroSmoothLocalLiftOn.lean` (chip 15, ~125
  LOC) — `exists_contMDiffOn_local_lift`: globally `ContMDiff` β yields
  a smooth (`ContMDiffOn ∞` in SmoothPath regularity) local lift on
  an open neighbourhood `W ⊆ ℝ` of `t₀`, via `ContMDiffOn.contMDiffAt`
  + complex-to-real realification + `ContMDiffAt.comp` at every `t ∈ W`.

* `Manifold/MeromorphicNonzeroPathLiftUnique.lean` (chip 16, ~120
  LOC) — `path_lift_unique`: two continuous lifts of a regular-valued
  `β` agreeing at one point agree everywhere.  Clopen argument on
  the agreement set: closed (equalizer into T2), open (local
  injectivity at regular preimages), non-empty, in connected `ℝ`.

* `Manifold/MeromorphicNonzeroPathLiftPartition.lean` (chip 17, ~105
  LOC) — `exists_subdivision_hurwitzPatching`: Lebesgue-number-lemma
  subdivision of `unitInterval` such that on each subinterval, `β`
  maps into one `HurwitzPatchingData.W`.

* `Manifold/MeromorphicNonzeroPathLiftSingleSheet.lean` (chip 18, ~85
  LOC) — `exists_continuous_lift_single_sheet`: if `β` maps the entire
  `ℝ` into one local sheet's `V`-set with `x₀` in its `U`-set, then
  `sheet.g ∘ β` is a continuous global lift.

* `Manifold/MeromorphicNonzeroPathLiftExtend.lean` (chip 19, ~145
  LOC) — `extend_lift_across_sheet`: the inductive step.  Given a
  continuous lift on `Icc a b` and `β` mapping `Icc b c` into one
  local sheet's `V`, the piecewise function `if t ≤ b then γ t else
  sheet.g (β t)` is `ContinuousOn (Icc a c)` and lifts `β` there.
  Continuity via `ContinuousOn.if` + agreement at `b` from
  `leftInvOn`.

**Net open content after the 19 chips.** Closing C3 (general genus)
reduces to: (i) iterate `extend_lift_across_sheet` across the
partition from chip 17 to produce a global continuous lift on
`unitInterval`; (ii) upgrade to `SmoothPath`-class smoothness using
chip 15 at every junction; (iii) define `levelSetChain f β` as the
sum-over-fiber of single-preimage smooth lifts; (iv) compute the
chain boundary; (v) the Stokes / lattice argument for the period
vector.  The path-lift infrastructure for (i)–(ii) is now in-tree
axiom-free; the level-set chain Stokes work (iii)–(v) is the
remaining classical content.

Build at HEAD: `taskpolicy lake build` green, 8740 jobs. Zero `sorry`,
zero `axiom`. +~2,200 LOC across 14 new files.
## 2026-05-14 — C3 sub-arc: algebra closure + path-lift infrastructure (11 chips)

Six chips landed reducing the open content of `AbelHypothesis B`
(the C3 named hypothesis) from "discharge `AbelGeneratorPeriodCondition
B` for every `f : MeromorphicNonzero X`" to "discharge it on a
multiplicative generating set of *non-constant* meromorphic functions."
The chips also lay analytic foundations (regular-value set, planar
local biholomorphism at every regular point) consumed by the level-set
chain construction.

**Algebra-side closure** (3 chips, `Manifold/AbelGeneratorDischargedSet.lean`,
~280 LOC).

* `dischargedGenerators B := { f | period vector of AJ chain of (f) ∈
   periodLatticeImage }`. Closed under `1` (`one_mem`), constants
   (`const_mem`), `*` (`mul_mem`), `invMer` (`invMer_mem`), and
   quotients (`mul_invMer_mem`).
* `mem_dischargedGenerators_of_principalDivisor_zero` — vacuous-divisor
   discharge.
* `principalDivisorMap_of_toFun_const` + `toFun_const_mem_dischargedGenerators`
   — closes the constant-function case via
   `mmeromorphicOrderAt_const_ne_zero`.
* `toFun_ne_const_zero` — the `c = 0` branch is blocked by
   `nonvanishing_germ`.
* `abelGeneratorPeriodCondition_iff_dischargedGenerators_eq_univ` and
  `abelGeneratorPeriodCondition_of_forall_nonconst_toFun` — case-split
   reduction to the non-constant `toFun` case.

**Regular-value set** (1 chip,
`Manifold/MeromorphicNonzeroRegularValueSet.lean`, ~120 LOC).

* `MeromorphicNonzero.regularValueSet f := (f.criticalValues)ᶜ`.
* `criticalValues_finite` / `criticalValues_isClosed` /
  `regularValueSet_isOpen` under non-constancy.

**Planar local biholomorphism at every regular point** (2 chips,
~280 LOC).

* `MeromorphicNonzero.chartPullback f x := (chartAt ℂ (f.toRiemannSphere
   x)) ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm`
  (`Manifold/MeromorphicNonzeroLocalBiholomorphism.lean`).
* `analyticAt_chartPullback` — ω-smoothness ⇒ analytic chart pullback.
* `deriv_chartPullback_ne_zero_of_regular` — non-zero derivative at
   every regular point, pulled directly from `DerivBridgeData.hCompat`
   via the existing `criticalSet_finite_unconditional` infrastructure.
* `exists_local_biholomorphism_chartPullback` — planar local inverse via
   `AnalyticAt.exists_local_biholomorphism`.
* `chartPullback_oph` (`Manifold/MeromorphicNonzeroLocalSheet.lean`,
   ~120 LOC) — packages the planar inverse as a canonical
   `OpenPartialHomeomorph ℂ ℂ` via
   `HasStrictFDerivAt.toOpenPartialHomeomorph`.

**Manifold-level local sheet** (1 chip, +223 LOC inside `MeromorphicNonzeroLocalSheet.lean`).

* `manifoldLocalOph` — `OpenPartialHomeomorph X RiemannSphere` built
  via two `restrOpen`s of `c.trans (φ'.trans d.symm)`: planar source
  ∩ `c.target`, then outer ∩ `f.toRiemannSphere ⁻¹' d.source`.  Resulting
  underlying function agrees with `f.toRiemannSphere` on its source
  via `d.left_inv`.
* `manifoldLocalOph_apply` / `mem_source_manifoldLocalOph` /
  `mem_target_manifoldLocalOph`.
* `localSheetData_at_regular` — assembles `LocalSheetData
  f.toRiemannSphere (f.toRiemannSphere x₀) x₀` from `manifoldLocalOph`'s
  fields.

**`IsLocalHomeomorphOn` packaging** (1 chip,
`MeromorphicNonzeroLocalSheet.lean`, +39 LOC).

* `isLocalHomeomorphOn_toRiemannSphere` — `IsLocalHomeomorphOn
  f.toRiemannSphere f.regularSet` via `IsLocalHomeomorphOn.mk` +
  `manifoldLocalOph` + `manifoldLocalOph_apply`.
* `continuousAt_toRiemannSphere_of_regular` /
  `map_nhds_eq_of_regular` — corollaries.

**Fiber finiteness at regular values** (1 chip,
`Manifold/MeromorphicNonzeroFiberFinite.lean`, ~135 LOC).

* `fiber_isClosed` — preimage of singleton in T1 codomain under
  continuous `f.toRiemannSphere`.
* `mem_regularSet_of_preimage_regularValue` — preimages of regular
  values are regular points.
* `fiber_finite_of_mem_regularValueSet` — compactness + isolation via
  `IsCompact.elim_nhds_subcover` + `choose!`.

**`HurwitzPatchingData` at every regular value** (1 chip,
`Manifold/MeromorphicNonzeroHurwitzPatching.lean`, ~90 LOC).

* `hurwitzPatchingData_at_regularValue` — composes
  `HurwitzPatchingData.ofLocalSheets` with chip 7 (`localSheetData_at_regular`)
  and chip 9 (`fiber_finite_of_mem_regularValueSet`).  Provides the
  evenly-covered nbhd structure of a topological covering map at every
  regular value.

**Continuous local path lift** (1 chip,
`Manifold/MeromorphicNonzeroLocalPathLift.lean`, ~120 LOC).

* `exists_continuous_local_lift_of_continuous` — for `β : ℝ →
  RiemannSphere` continuous with `β t₀ ∈ f.regularValueSet` and any
  preimage `x₀`, produces an open `W ⊆ ℝ` ∋ t₀, a continuous local lift
  `γ : ℝ → X = sheet.g ∘ β`, with `γ t₀ = x₀` and
  `f.toRiemannSphere (γ t) = β t` for all `t ∈ W`.

**Net open content after the 11 chips.** `AbelHypothesis B` (general
genus) reduces to: discharge `f ∈ dischargedGenerators B` for every
`f : MeromorphicNonzero X` whose `toRiemannSphere` is non-constant. The
covering-map structure on `f.toRiemannSphere : f.toRiemannSphere ⁻¹'
regularValueSet → regularValueSet` is now in-tree (via `LocalSheetData`,
`HurwitzPatchingData`, `IsLocalHomeomorphOn`, fiber-finiteness, and
continuous local path lift).  The remaining classical content is the
*smooth* upgrade of the lift, *global* lift over the unit interval,
the level-set chain definition, and the Stokes argument.

Build at HEAD: `taskpolicy lake build` green, 8731 jobs. Zero `sorry`,
zero `axiom`. +~1,400 LOC across 7 new files.

## 2026-05-14 — C1 sub-arc CLOSED: `SmoothPathConnected` on any preconnected complex 1-manifold

The four chips of 2026-05-15 (SmoothPath refactor, `linearInChartSegment`,
`concat`, local-convex + open-closed) close the C1 sub-arc of
CLOSURE_MAP §F.3 unconditionally for any preconnected complex
1-manifold.

**`Manifold/SmoothPathLocalConvex.lean`** (182 LOC, new). Two
top-level theorems:

* `exists_smooth_path_connected_chart_nbhd p` — for every `p : X`,
  there is an open neighborhood `U ∋ p` such that any two points of
  `U` are joined by a smooth path. Construction: `U := φ.source ∩
  φ ⁻¹' Metric.ball z r` where `φ = chartAt ℂ p`, `z = φ p`,
  `r > 0` with `Metric.ball z r ⊆ φ.target`. Convexity of the ball
  plus `linearInChartSegment` gives the smooth-path-connected
  property of `U`.

* `smoothPathConnected_of_preconnected [PreconnectedSpace X] :
   SmoothPathConnected 𝓘(ℝ, ℂ) X` — the open-closed argument
  applied to the reachable set
  `reachableFrom p := {x | ∃ γ : SmoothPath I X, γ.src = p ∧
   γ.tgt = x}`. Helper lemmas (private):
  - `p_mem_reachableFrom` via `SmoothPath.const`.
  - `reachableFrom_isOpen` via `concat` + local lemma.
  - `compl_reachableFrom_isOpen` via the symmetric argument.
  - `reachableFrom_isClopen` combines.
  Then `IsClopen.eq_univ` closes it.

**`Manifold/SmoothPathConnectedRiemannSphere.lean`** (223 LOC,
landed earlier today). `smoothPathConnected_RiemannSphere` + the
composed `nonempty_abelJacobiInput_RiemannSphere`.

**`Manifold/SmoothPathConcat.lean`** (337 LOC, landed earlier
today). `SmoothPath.concat` via bump-flatten reparameterisations
`concatRepLeft t = σ(4(t - 1/8))` and `concatRepRight t = σ(4(t -
5/8))` (with `σ = Real.smoothTransition`), making both halves
identically equal to the junction point on `(3/8, 5/8)`.

Net (combined with `nonempty_of_smoothPathConnected` from
`Manifold/SmoothPathConnected.lean`): **`Nonempty (AbelJacobiInput
α h)` is now unconditional on any nonempty preconnected complex
1-manifold.** Items 4/5/10/11/12/13 remain blocked on the C3 and
C4 general-genus discharges (Stokes-on-2-chains, Abel converse,
Jacobi inversion).

Build across all four chips: `taskpolicy lake build` green, 8713
jobs at HEAD. Zero `sorry`, zero `axiom`. +742 LOC total.

## 2026-05-14 — `SmoothPath` refactored ω → C^∞ + `linearInChartSegment`

**Headline.** The `SmoothPath` structure's smoothness witness was
declared at `ContMDiff ... ⊤` where `⊤ : WithTop ℕ∞` resolves to the
analytic level `ω` despite a docstring stating the intent was `C^∞`.
The mismatch obstructed chart-cover lifts (analytic functions on `ℝ`
are germ-determined; concatenation across charts cannot satisfy the
analytic-germ agreement at junction points). The refactor brings the
implementation in line with the docstring and unblocks the C1
chart-cover sub-arc.

Files modified (5):

* `Manifold/SmoothChain.lean` — SmoothPath.smooth field type
  `ContMDiff (𝓘(ℝ, ℝ)) I ∞ f` (C^∞ = `((⊤ : ℕ∞) : WithTop ℕ∞)`)
  instead of `⊤`. File docstring updated.

* `Manifold/SmoothPathIntegral.lean` — `ambient_contMDiff` returns
  `ContMDiff (𝓘(ℝ, ℝ)) I ((⊤ : ℕ∞) : WithTop ℕ∞)` (the explicit form
  is used because `open scoped ContDiff` would clash with the file's
  `ω : SmoothOneForm I X` binders).

* `Manifold/SmoothPathChartCompat.lean` — `mdifferentiableAt_ambient`
  consumes the C^∞ witness; `n ≠ 0` discharged by `decide`.

* `Manifold/SmoothPathIntegrability.lean` —
  `contMDiffAt_chartVelocity` returns C^∞; `ContMDiffAt.mfderiv_const`
  invoked with `∞ + 1 ≤ ∞` (top of `ℕ∞` is absorptive in `WithTop`).

* `Manifold/SmoothPathLinearInChart.lean` — existing `linearInChart`
  retained; its ω-level chart-inverse smoothness is downcast to C^∞
  via `ContMDiffAt.of_le (by decide)`. New constructors:
    - `bumpedSegment a b t = (1 - σ t) • a + σ t • b` where
      `σ = Real.smoothTransition`.
    - `bumpedSegment_mem_segment`: image of `bumpedSegment a b` on
      all of `ℝ` lies in `segment ℝ a b` (the closed convex hull).
    - `contDiff_bumpedSegment` / `contMDiff_bumpedSegment` at `∞`.
    - `SmoothPath.linearInChartSegment` — **segment-in-target**
      smooth path constructor. Strict weakening of
      `linearInChart`'s line-in-target hypothesis. Only available at
      C^∞ because `Real.smoothTransition` is C^∞ but not analytic.
    - `linearInChartSegment_src` / `_tgt`.

Build: `taskpolicy lake build` green, 8710 jobs. Zero `sorry`, zero
`axiom`. +212 / -68 LOC.

Net unblock: chart-cover lift to `SmoothPathConnected I X` on a
compact connected complex 1-manifold is no longer obstructed by
analytic germ-determination. The remaining steps are (i) a C^∞
concatenation primitive (next sub-chip, ~150–300 LOC via partition
of unity); (ii) a chart-cover argument exploiting convex chart
targets to discharge segment-in-target trivially (~400–800 LOC).

## 2026-05-14 — `Subsingleton (Pic0 RiemannSphere)` UNCONDITIONAL — Pic⁰(ℙ¹) = 0 in-tree

**Headline.** Closes the closure decomposition for every degree-zero
divisor on the Riemann sphere as a finite ℤ-linear combination of
elementary divisors `Div.single (some a) - Div.single ∞`, each of
which is the principal divisor `principalDivisorMap (mnRSAffineFactor
a)`. Result: `Subsingleton (Pic0 RiemannSphere)` is **unconditional**,
and consequently `Pic⁰ RiemannSphere ≃+ AnalyticJacobian RiemannSphere`
is unconditional too.

New file: `Manifold/Pic0RiemannSphereSubsingleton.lean` (~190 LOC).

* `Div.finset_sum_apply` — `(∑ n ∈ s, F n : Div RS) y = ∑ n ∈ s, F n y`.
  Pointwise eval pushed through finite sums via `Finset.induction` plus
  the existing `Div.add_apply`.

* `single_sub_infty_mem_PrincDiv` — `Div.single x - Div.single ∞ ∈
  PrincDiv RS` for any `x ≠ ∞`, via `elementaryDivisor_mem_PrincDiv`.

* `sum_elementary_eq_div0 D y` — for `D : Div0 RS`,
  `(∑ x ∈ supp(D).filter (· ≠ ∞), D(x) • (Div.single x - Div.single ∞)) y
   = D y`. Split on `y = ∞` (uses `D.degree = 0` to balance contributions
  via `Finset.sum_filter_add_sum_filter_not`) vs `y` finite (isolates
  the `y`-th term via `Finset.sum_eq_single_of_mem`).

* `subsingleton_pic0_RiemannSphere : Subsingleton (Pic0 RiemannSphere)`
  — the final discharge. `AddSubgroup.sum_mem` plus
  `AddSubgroup.zsmul_mem` plus the elementary divisor lemma combine
  through the reconstruction.

* `AbelJacobiInput.abelJacobiEquiv_of_RiemannSphere_unconditional` —
  full Abel-Jacobi iso `Pic0 RS ≃+ AnalyticJacobian RS` on RS,
  **axiom-free**.

Build: `taskpolicy lake build` green, 8710 jobs. Zero `sorry`, zero
`axiom`.

## 2026-05-14 — `mnRSAffineFactor` + elementary-divisor identity

Lands the translation generator `f(z) = z - a` on the Riemann sphere
as `MeromorphicNonzero RS`, with principal divisor `δ_{some a} - δ_∞`.

New files (302 LOC across two):

* `Manifold/MeromorphicNonzeroRSAffineFactor.lean` (~190 LOC) —
  `RSAffineFactor a = RSSimplePole - (const a)`, packaged as
  `mnRSAffineFactor a : MeromorphicNonzero RiemannSphere`. The
  chart-S pullback proof reuses `RSSimplePole_comp_chartS_symm_eq`
  to reduce to `w⁻¹ - a` on a punctured nbhd of `0`, whose
  meromorphic order is `-1` (via factoring `w⁻¹ - a = (1 - a w)/w`
  and `meromorphicOrderAt_div`).

* `Manifold/Pic0RiemannSphereTrivial.lean` (~140 LOC) —
  `principalDivisorMap_mnRSAffineFactor a` and
  `elementaryDivisor_mem_PrincDiv`. The divisor computation uses
  `meromorphicOrderAt_comp_of_deriv_ne_zero` (translating `id` by
  `-a`) for the order-`1` zero at `some a`, plus
  `analyticOrderAt_eq_zero` for the order-`0` regular points.

## 2026-05-14 — `mnRSInversion`: second principal-divisor generator on RS

Sister chip to `mnRSSimplePole`. Builds the inversion function
`RSInversion : RiemannSphere → ℂ` (`some z ↦ z⁻¹`, `∞ ↦ 0`)
and packages it as a `MeromorphicNonzero RiemannSphere` with
principal divisor `δ_∞ - δ_{some 0}` (simple zero at `∞`, simple
pole at `some 0`).

New file: `Manifold/MeromorphicNonzeroRSInversion.lean` (~200 LOC).

* Chart-pullback identities: `RSInversion ∘ chartN.symm = (·)⁻¹`,
  `RSInversion ∘ chartS.symm = id`.
* `mnRSInversion : MeromorphicNonzero RiemannSphere` — packaged form.
* Order at `∞` is `1` (chart-S pullback is `id`,
  `meromorphicOrderAt_id`); order at finite is `≠ ⊤`; order at
  `some 0` is `-1` (chart-N pullback is `(·)⁻¹`,
  `meromorphicOrderAt_inv ∘ meromorphicOrderAt_id`).
* Continuity at non-pole points: at finite `z ≠ 0` via
  `continuousAt_inv₀`; at `∞` via `tendsto_inv₀_cobounded` (the
  `1/w → 0` as `|w| → ∞` limit).

Together with `mnRSSimplePole`, this gives two non-constant
principal-divisor generators on RS whose divisors are
sign-flipped (`δ_{some 0} - δ_∞` and `δ_∞ - δ_{some 0}`). Combined
with future translation generators (`δ_{some a} - δ_∞`), they
generate `Div0 RiemannSphere` and unblock unconditional
`Subsingleton (Pic0 RiemannSphere)`.

Build: 8707 jobs clean. Zero `sorry`, zero `axiom`.

## 2026-05-14 — `mnRSSimplePole`: first non-trivial principal-divisor generator on RS

Lands the first non-constant `MeromorphicNonzero RiemannSphere` — the
explicit packaging of `RSSimplePole : RiemannSphere → ℂ` (zero at
`some 0`, simple pole at `∞`) — used as the base case for any
constructive discharge of `Subsingleton (Pic0 RiemannSphere)`.

New file: `Manifold/MeromorphicNonzeroRSSimplePole.lean` (~110 LOC).

* `RSSimplePole_continuousAt_coe` — continuity at every finite
  point, via the open embedding `(↑) : ℂ → RiemannSphere`.
* `mnRSSimplePole : MeromorphicNonzero RiemannSphere` — bundled
  packaging via `MeromorphicNonzero.ofRegularContinuous`.

The non-vanishing-germ proof at finite points uses
`meromorphicOrderAt_ne_top_iff_eventually_ne_zero` on the
chart-pulled-back `id`. The `regular_continuousAt` field is
discharged at finite points via the continuity lemma above;
at `∞` the order is `-1`, making the hypothesis vacuous (proven
by contradiction on `0 ≤ -1`).

The principal divisor of `mnRSSimplePole` is `δ_{some 0} - δ_∞`.
Future chips build the translation `δ_{some a} - δ_∞` and inversion
`δ_∞ - δ_{some 0}` generators, plus the closure argument turning
these into a full discharge of `Subsingleton (Pic0 RiemannSphere)`
(equivalently `Pic⁰(ℙ¹) = 0`).

Build: 8706 jobs clean. Zero `sorry`, zero `axiom`.

## 2026-05-14 — C4 bridge: Subsingleton (Pic0 X) ↔ every Div0 is principal

New file: `Manifold/Pic0SubsingletonBridge.lean` (~85 LOC).

* `subsingleton_pic0_iff_every_div0_principal` — the bridge.
  Forward via `Subsingleton.elim` + `QuotientAddGroup.eq_zero_iff`;
  backward via `QuotientAddGroup.induction_on`.
* `subsingleton_pic0_of_every_div0_principal` — one-way form.

Why this matters: lets a future discharge of `Subsingleton (Pic0
RiemannSphere)` produce the equivalent existential statement —
constructing explicit meromorphic representatives (rational
functions on `ℂ`) for every degree-0 divisor on `RS`.

Build: 8705 jobs clean. Zero `sorry`, zero `axiom`.

## 2026-05-14 — Abel-Jacobi iso on `RiemannSphere` from Pic⁰(ℙ¹) = 0

New file: `Manifold/AbelJacobiEquivRiemannSphere.lean` (~75 LOC).
Specialises `abelJacobiEquiv_of_genus_zero` to `X = RiemannSphere`
using the unconditional `genus_RiemannSphere_eq_zero`.

* `abelJacobiEquiv_of_RiemannSphere` — from `Subsingleton (Pic0
  RiemannSphere)` and an AJ input, build `Pic0 RS ≃+ AnalyticJacobian`.
  After this commit the Abel-Jacobi iso on RS sits on exactly one
  named classical input.

Build: 8704 jobs clean. Zero `sorry`, zero `axiom`.

## 2026-05-14 — C4 genus-0: JacobiInversion ← Subsingleton (Pic0 X)

Parallel chip to the C3 genus-0 corner, closing the C4 (Jacobi
inversion) input at genus 0 down to a single textbook hypothesis.

New file: `Manifold/JacobiInversionGenusZero.lean` (~90 LOC).

* `jacobiInversion_of_genus_zero_and_subsingleton_pic0` — builds
  `JacobiInversion B hAbel` from `genus X = 0` + `Subsingleton (Pic0
  X)`. Surjectivity is automatic at genus 0 (codomain subsingleton);
  injectivity reduces to source-side subsingleton.
* `abelJacobiEquiv_of_genus_zero` — packages the full Abel-Jacobi
  isomorphism `Pic0 X ≃+ AnalyticJacobian` at genus 0 by composing
  `abelHypothesis_of_genus_zero` with the new JacobiInversion discharge.

After this commit, both halves of `Pic⁰ ≃+ AnalyticJacobian` at
genus 0 reduce to a single classical input — `Subsingleton (Pic0 X)`
(genus-0 case of Abel's converse, equivalent to Pic⁰(ℙ¹) = 0). The
general-genus content of C4 remains the open work.

Build: 8703 jobs clean. Zero `sorry`, zero `axiom`.

## 2026-05-14 — C3 per-generator reduction: AbelChainPeriodCondition ← AbelGeneratorPeriodCondition

Fourth C3 piece. Reduces `AbelChainPeriodCondition B` to the
per-generator statement `AbelGeneratorPeriodCondition B`: for each
`f : MeromorphicNonzero X`, the period vector of the AJ chain of
`div(f)` lies in `periodLatticeImage`. This is Abel forward in its
sharpest atomic form — one meromorphic function at a time.

Extends `Manifold/AbelHypothesisFromPeriodCondition.lean`.

* `AbelGeneratorPeriodCondition B : Prop` — per-`f` form of the
  period-lattice condition.
* `abelChainPeriodCondition_of_abelGeneratorPeriodCondition` —
  closure induction on `PrincDiv X = AddSubgroup.closure (Set.range
  principalDivisorMap)` using the algebra-side closure lemmas.
* `abelHypothesis_of_abelGeneratorPeriodCondition` — direct
  composite to `AbelHypothesis`.

Build: 8702 jobs clean. Zero `sorry`, zero `axiom`.

## 2026-05-14 — C3 algebra layer: additivity + closure of AbelChainPeriodCondition

Third C3 piece. Algebraic infrastructure for the C3 chain-level
reduction.

Extends `Manifold/AbelHypothesisFromPeriodCondition.lean`.

* `principalDivisorAJChain_add` — additivity of the AJ chain in the
  divisor.
* `principalDivisorAJChainHom : Div X →+ SmoothChain 𝓘(ℝ, ℂ) X` —
  bundled `AddMonoidHom` form.
* `complexChainPeriodVector_principalDivisorAJChain_add_mem` and
  `_neg_mem` — closure of "period vector ∈ periodLatticeImage" under
  addition and negation of divisors.

Build: 8702 jobs clean. Zero `sorry`, zero `axiom`.

## 2026-05-14 — C3 chain-level reduction: AbelHypothesis ← AbelChainPeriodCondition

Second piece of C3 (Abel's theorem forward direction). Lands a
concrete chain-level reduction of `AbelHypothesis B` to a single,
textbook-citable hypothesis `AbelChainPeriodCondition B` on period
vectors of explicit Abel-Jacobi chains. After this commit, the open
content of C3 at arbitrary genus is exactly the period-vector
condition.

New file: `Manifold/AbelHypothesisFromPeriodCondition.lean` (~210
LOC).

* `AbelJacobiInput.principalDivisorAJChain B D` — explicit
  Abel-Jacobi chain for any `D : Div X`:
  `Σ x ∈ D.supportFinset, D(x) • SmoothChain.single (B.pathFromBase x)`.
  Boundary on `Div0` equals `D` as a 0-chain.

* `abelJacobiChain_principalDivisorAJChain_eq_abelJacobiDivHom` —
  diagram identity routing the chain through the AJ formalism
  (`map_sum` + `AddMonoidHom.map_zsmul` + `abelJacobiChain_single`).

* `complexChainPeriodVector_principalDivisorAJChain` — period-
  vector form of the chain.

* `AbelChainPeriodCondition B : Prop` — the reduction hypothesis:
  for every principal divisor `D`, the period vector of its AJ
  chain lies in `periodLatticeImage`. Classical content: for `D
  = div(f)`, the period vector decomposes as an integer
  combination of basis periods via the level-set chain of `f`.

* `abelHypothesis_of_abelChainPeriodCondition` — the reduction
  itself. Proof via the diagram identity + `QuotientAddGroup.eq_zero_iff`
  + `PeriodLatticeOfRankTwoG.ofBundle_lattice`.

* `abelChainPeriodCondition_of_genus_zero` — sanity check
  recovering the prior genus-0 discharge through the new reduction.

Build: 8702 jobs clean. Zero `sorry`, zero `axiom`.

## 2026-05-14 — C3 corner: AbelHypothesis trivially holds at genus 0

Lands a small but real piece of C3 (Abel's theorem). At genus 0 the
analytic Jacobian collapses to a single point, so the named
hypothesis `AbelHypothesis B` of `Manifold/AbelJacobiPic0.lean`
holds vacuously. The general-genus content of `AbelHypothesis`
(classical Abel forward via Stokes on a 2-chain whose boundary
represents the principal divisor) is unaffected by this corner; it
remains the open content of C3 (CLOSURE_MAP §F.3, est.
1,200–2,800 LOC).

New file: `Manifold/AbelHypothesisGenusZero.lean` (99 LOC).

* `subsingleton_pi_fin_genus_zero` — `Subsingleton (Fin (genus X)
  → ℂ)` whenever `genus X = 0` (via `Pi.uniqueOfIsEmpty`).
* `Subsingleton.analyticJacobian_of_genus_zero` — the analytic
  Jacobian collapses to a single point at genus 0, since
  `JacobianOfLattice = (Fin (genus X) → ℂ) ⧸ lattice` quotients a
  subsingleton group.
* `AbelJacobiInput.abelHypothesis_of_genus_zero` — `AbelHypothesis
  B` unconditionally from `genus X = 0`. Every value of
  `B.abelJacobiDiv0Hom` collapses to `0` in the subsingleton
  codomain.

Build: `taskpolicy lake build` green, 8701 jobs. Zero `sorry`,
zero `axiom`.

## 2026-05-14 — A2 closed + genus-0 RR chain unconditional (modulo uniformization)

Merges `feat/antipode-smoothness` (parallel branch off `main`) into
the linear-system-divisor trunk and composes with the A1 discharge
that landed earlier today. The genus-0 Riemann–Roch `dim_ℂ L(δp) ≥
2` chain on the germ field is now reduced to exactly **one** named
classical input — uniformization at genus 0.

New files merged from `feat/antipode-smoothness` (660 LOC total):

* `Manifold/RiemannSphereAntipodeSmooth.lean` (255 LOC) — discharges
  the `contMDiff_antipode_TODO` follow-up from
  `RiemannSphereMobius.lean`: `ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω antipode` via
  `contMDiffAt_iff_of_mem_source` on the three-case `OnePoint.rec`
  split (chart pairs at `∞`, at `coe 0`, and at `coe w` with `w ≠
  0`; chart-coord maps `z ↦ -z` for the first two and `z ↦ -z⁻¹`
  for the third). Packages as `antipodeEquiv : HolomorphicEquiv RS RS`
  (self-inverse).
* `Manifold/RiemannSphereTranslate.lean` (322 LOC) — `translateBy c`
  on RS (fixing `∞`, `coe z ↦ coe (z + c)`) as `ContMDiff 𝓘(ℂ) 𝓘(ℂ)
  ω` and packaged as `translateEquiv c : HolomorphicEquiv RS RS`
  with inverse `translateEquiv (-c)`.
* `Manifold/MobiusTransitivityRS.lean` (80 LOC) —
  `RiemannSphere.existsMobiusToInftyRS`: ∀ `p : RS`, ∃ `e :
  HolomorphicEquiv RS RS`, `e p = ∞`. Concrete witnesses: identity
  for `p = ∞`; `translateEquiv(-z₀).trans antipodeEquiv` for `p =
  coe z₀` (sending `coe z₀ ↦ coe 0 ↦ ∞`).

New trunk-side file (this commit):

* `Topology/LinearSystemGermDeltaPFiniteDimRSUnconditional.lean`
  (109 LOC) — composes the two unconditional discharges:
  - `existsMobiusToInftyRS_holds : ExistsMobiusToInftyRS` — 1-line
    bridge identifying the in-tree theorem with the named-hypothesis
    Prop (definitionally equal, `rfl`-level).
  - `linearSystemGermDeltaPFiniteDim_RiemannSphere_unconditional :
    LinearSystemGermDeltaPFiniteDim RiemannSphere` — the headline,
    no hypothesis.
  - `rr_DimGE2_GenusZero_Germ_of_uniformization_unconditional_RSFiniteDim`
    — for any compact connected complex 1-manifold `X`, genus-0 RR
    dim ≥ 2 on the germ field reduces to genus-conditional
    uniformization alone.

**Net post-this-commit state.** The genus-0 RR `dim_ℂ L(δp) ≥ 2`
content on:

* **`RiemannSphere`**: **unconditional**.
* **Arbitrary compact connected complex 1-manifold `X`**: depends on
  **one** named classical input — `genus X = 0 → Nonempty
  (HolomorphicEquiv X RiemannSphere)` (uniformization at genus 0).

Build: 8700 jobs clean. Zero `sorry`, zero `axiom`.

## 2026-05-14 — `feat/c1-smooth-path-connected` merged: SmoothPathConnected predicate + linearInChart (ω-level)

Two-commit branch off `main` (`d97dcd5..c189052`) merged into
`feat/linear-system-divisor` after the A1 discharge below. Net +371
LOC, two new files in `JacobianChallenge/Manifold/`, zero `sorry`,
zero `axiom`. Full `taskpolicy lake build` green post-merge (8696
jobs). Disjoint from the linear-system-divisor RR work: files live
in `Manifold/SmoothPath*` only.

**Smooth-path-connectedness layer** — `Manifold/SmoothPathConnected.lean`
(177 LOC):

- `SmoothPathConnected I X : Prop` — every two points of `X` joined
  by a `SmoothPath I X`; smooth analogue of mathlib's
  `PathConnectedSpace`.
- `SmoothPathConnected.diagonal` — the `p = p` case is uniform via
  `SmoothPath.const`.
- `AbelJacobiInput.ofSmoothPathConnected` — constructor producing
  the bundle from `SmoothPathConnected 𝓘(ℝ, ℂ) X` + a chosen base
  point. Path-picker via `Classical.choose`.
- `AbelJacobiInput.nonempty_of_smoothPathConnected` — packaging:
  `Nonempty X + SmoothPathConnected 𝓘(ℝ, ℂ) X ⇒ Nonempty
  (AbelJacobiInput α h)`.
- `AbelJacobiInput.exists_smoothPath_from_basePoint` — one-sided
  back-projection.

Splits the `AbelJacobiInput α h` named-hypothesis bundle along a
textbook fault line: from "base point + per-target picker" down to
the classical predicate plus `Nonempty X`. CLOSURE_MAP §F.5 step 2
(C1) now factors through `SmoothPathConnected` as a single citable
classical input.

**Linear-in-chart primitive** — `Manifold/SmoothPathLinearInChart.lean`
(192 LOC):

- `affineSegment a b t = (1 - t) • a + t • b` — affine map `ℝ → ℂ`
  with `affineSegment_zero/one` endpoint identities.
- `contDiff_affineSegment` / `contMDiff_affineSegment` — affine maps
  are `C^ω`; manifold-side lift via `contMDiff_iff_contDiff`.
- `SmoothPath.linearInChart φ h_atlas p q hp hq h_line` — constructor
  of a `SmoothPath 𝓘(ℝ, ℂ) X` between `p, q` whose chart-coordinate
  line `{(1-t) • φ p + t • φ q : t ∈ ℝ}` lies entirely in
  `φ.target`. Ambient `t ↦ φ.symm (affineSegment (φ p) (φ q) t)`,
  smooth at ω-regularity via `contMDiffAt_symm_of_mem_maximalAtlas
  ∘ contMDiff_affineSegment`.
- `SmoothPath.linearInChart_src` / `_tgt` — endpoint identities.

**ω-level structural finding** (documented in the file's docstring
and accompanying commit):

The `SmoothPath` structure demands `ContMDiff 𝓘(ℝ, ℝ) I ⊤ f` with
`⊤ : WithTop ℕ∞`, which mathlib's `Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries`
notes equals `ω` (analytic). Globally analytic functions are
germ-determined, so the standard `C^∞` trick of smoothly extending
by constants outside `[0, 1]` does *not* produce an analytic path.
This forces `linearInChart` to require the *entire chart-coordinate
line* (not merely the segment) in `φ.target`. The hypothesis is
unconditional on the affine chart of `RiemannSphere` (target = ℂ);
on a generic Riemann surface chart with bounded target it fails.
Closing the "segment-only" case at the ω level genuinely requires
either changing the `SmoothPath` definition (downgrade to `C^∞`) or
an analytic-continuation argument; neither is in scope of this chip.

**Net post-this-merge state.** CLOSURE_MAP §F.5 step 2 (C1
`AbelJacobiInput`) factors through `SmoothPathConnected 𝓘(ℝ, ℂ) X +
Nonempty X`, with `linearInChart` as the first chart-side primitive.
Full chart-cover discharge remains open.

## 2026-05-14 — A1 closed: `LinearSystemAtInftyRS_BoundedBySimplePoleSpan` discharged

Two new files (~870 LOC total) discharging the polynomial-growth
Liouville bound at `∞` on the Riemann sphere, the first of the two
remaining classical inputs in the genus-0 RR `dim_ℂ L(δp) ≥ 2`
chain.

`Analysis/PolynomialLiouville.lean` (~180 LOC) — foundational
mathlib-style lemma: an entire `f : ℂ → ℂ` with `‖f z‖ ≤ C ‖z‖` for
`‖z‖ ≥ R₀` is an affine function `f z = f 0 + (deriv f 0) · z`.
Proven via the Cauchy first-derivative estimate
(`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`) plus basic
Liouville (`Differentiable.exists_const_forall_eq_of_bounded`) and
constancy from zero derivative (`is_const_of_deriv_eq_zero`).

`Topology/LinearSystemAtInftyRSDischarge.lean` (~690 LOC) —
discharge of `LinearSystemAtInftyRS_BoundedBySimplePoleSpan` for an
arbitrary germ in `linearSystemGermDeltaP (∞ : RS)`:

1. Affine-chart restriction `affineChartFun f := f.toFun ∘ some`,
   with `mmeromorphicOrderAt (some z) = meromorphicOrderAt
   (affineChartFun f) z`.
2. Entire normal-form representative `entireRep f := toMeromorphicNFOn
   (affineChartFun f) Set.univ`, analytic on all of `ℂ` by
   `MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd`.
3. Linear growth bound at infinity: `id ∘ (f ∘ chartS.symm)` has
   order `≥ 0` at `0` (additivity), so bounded near `0` by
   `tendsto_nhds_of_meromorphicOrderAt_nonneg`. Translating via the
   substitution `w = z⁻¹` gives `‖entireRep f z‖ ≤ M ‖z‖` for `‖z‖`
   large (limit-comparison lift across continuity).
4. Polynomial Liouville: `entireRep f w = a + b w` for all `w`.
5. Germ identity at `some 0`: `f.toFun =ᶠ[𝓝[≠] (some 0)] (a + b ·
   RSSimplePole)` by composing the chart-side EvEq with the
   polynomial identity.
6. Identity theorem (`mmeromorphicOrderAt_ne_top_forall`):
   single-point germ identity propagates globally to all of RS.
7. Final: `mk f = a • 1 + b • RSSimplePoleGerm ∈ span ℂ {1,
   RSSimplePoleGerm}`.

**Net post-this-commit state.** `LinearSystemGermDeltaPFiniteDim
RiemannSphere` reduces to a single remaining classical input
(`ExistsMobiusToInftyRS` — Möbius transitivity on RS). Combined
with uniformization at genus 0, the genus-0 RR `dim_ℂ L(δp) ≥ 2`
chain reduces to **two** named classical inputs: uniformization +
Möbius transitivity. Build: 8694 jobs clean (pre-C1 merge). Zero
`sorry`, zero `axiom`.

## 2026-05-14 — RS-FiniteDim architectural reduction (feat/linear-system-divisor cont.)

New file `Topology/LinearSystemGermDeltaPFiniteDimRSFromInputs.lean`
(~210 LOC) architecturally reduces `LinearSystemGermDeltaPFiniteDim
RiemannSphere` (the second of the two remaining classical inputs in
the genus-0 RR `dim_ℂ L(δp) ≥ 2` chain) to **exactly two** named
classical inputs:

1. `LinearSystemAtInftyRS_BoundedBySimplePoleSpan` — polynomial-growth
   Liouville bound at `∞`: `linearSystemGermDeltaP (∞ : RS) ≤
   Submodule.span ℂ {1, RSSimplePoleGerm}`. Classical content: entire
   `ℂ → ℂ` with `|f| = O(|z|)` at ∞ is a polynomial of degree ≤ 1.
   Mathlib at the pin has basic Liouville
   (`Complex.liouville_theorem_aux`) but not the polynomial-growth
   extension; Cauchy-estimate-based proof.
2. `ExistsMobiusToInftyRS` — Möbius transitivity on RS: ∀ `p : RS`,
   `∃ e : HolomorphicEquiv RS RS, e p = ∞`. Concrete witnesses are
   identity (for `p = ∞`) and antipode-composed-with-translation
   (for finite `p = z₀`); packaging requires checking smoothness on
   the two-chart atlas.

Helpers:
- `linearSystemGermDeltaP_finite_of_holomorphicEquiv` — per-point
  version of the existing `LinearSystemGermDeltaPFiniteDim.of_holomorphicEquiv`
  (the ∀-quantified one). Direct `Module.Finite.equiv` wrap of
  `linearSystemGermDeltaPLinearEquiv_via_holomorphicEquiv`.
- `linearSystemGermDeltaP_finite_of_le_span_pair` — pure linear-algebra:
  `L(δp) ≤ span ℂ {1, ψ} ⇒ Module.Finite ℂ (L(δp))`. Proof via
  `Module.Finite.span_of_finite` + `Module.Finite.of_injective` on
  `Submodule.inclusion`.

Headline `linearSystemGermDeltaPFiniteDim_RiemannSphere` composes the
two: the polynomial bound gives finiteness at `∞`; transitivity
transports it to every `p` via per-point transport.

**Post-this-commit state.** Combined with the existing
`feat/linear-system-divisor` branch, the genus-0 RR `dim_ℂ L(δp) ≥ 2`
on the germ field reduces to exactly **three** named classical inputs:
(i) uniformization at genus 0 (`genus X = 0 → Nonempty (HolomorphicEquiv
X RS)`), (ii) `LinearSystemAtInftyRS_BoundedBySimplePoleSpan`
(polynomial-growth Liouville on RS at ∞), (iii) `ExistsMobiusToInftyRS`
(Möbius transitivity on RS). All three are citable textbook content;
(ii) and (iii) are smaller-scale than (i) (which is full uniformization
theory). Zero `sorry`, zero `axiom`.

## 2026-05-14 — `feat/linear-system-divisor` branch (germ-field RR layer)

15-commit branch (`957fdd0..380ac85`) building the full architectural
reduction for genus-0 RR `dim_ℂ L(δp) ≥ 2` on the germ field. Net
+2807 LOC, zero `sorry`, zero `axiom`. After this branch, the
content reduces to exactly two classical inputs: (i) uniformization at
genus 0, and (ii) `LinearSystemGermDeltaPFiniteDim RiemannSphere`.

**L(D) ambient on the germ field** (closes the architectural issue
flagged earlier — pointwise `linearSystemDeltaP` was vacuously infinite
via "blip" elements):
- `Topology/LinearSystemDivisor.lean` — `linearSystemDivisor D :
  Submodule ℂ (MeromorphicFunctionGerm X)` for any `D : Div X`, with
  closure under `zero`/`add`/`smul`. Specialises to
  `linearSystemGermDeltaP p` at `D = Div.single p`.
- `Topology/LinearSystemDivisorConstants.lean` — `constantsToLinearSystemDivisor`
  for effective `D`, with injectivity under `ConnectedSpace`.
- `Topology/LinearSystemDivisorMono.lean` — monotonicity in `D`.
- `Topology/LinearSystemDivisorMul.lean` — multiplicative grading
  `L(D₁) · L(D₂) ⊆ L(D₁ + D₂)`.

**Dim-bound layer**:
- `Topology/LinearSystemDivisorZeroLiouville.lean` —
  `linearSystemDivisor 0 = constantsGerm X` and
  `finrank_linearSystemDivisor_zero_eq_one` (UNCONDITIONAL via
  the existing `liouvilleOnCompactConnected_holds`).
- `Topology/LinearSystemDivisorSimplePoleRank.lean` —
  `LinearIndependent ℂ ![1, ψ]` from a simple-pole germ, then
  `2 ≤ Module.rank ℂ (linearSystemGermDeltaP p)` (unconditional) and
  `RR_DimGE2_GenusZero_Germ` discharge from `ExistsSimplePoleGerm` +
  `LinearSystemGermDeltaPFiniteDim` (named hypothesis added).

**Existence side — RS base case + transport**:
- `Manifold/RiemannSphereSimplePole.lean` — explicit `RSSimplePole :
  RiemannSphere → ℂ` (`some z ↦ z`, `∞ ↦ 0`), packaged as
  `RSSimplePoleGerm` with simple pole at `∞`. Discharges
  `ExistsSimplePoleGermAtSomePoint RiemannSphere` UNCONDITIONALLY.
- `Manifold/MMeromorphicHolomorphicEquivTransport.lean` —
  `mmeromorphicOrderAt` preservation through a `HolomorphicEquiv`
  (composes existing `contMDiff_omega_analyticAt_chart_pullback` +
  `deriv_chart_pullback_ne_zero_of_injective` + mathlib's
  `meromorphicOrderAt_comp_of_deriv_ne_zero`).
- `Topology/ExistsSimplePoleGermFromHolomorphicEquivRS.lean` —
  `Nonempty (HolomorphicEquiv X RS) → ExistsSimplePoleGermAtSomePoint X`.

**Finite-dim side — transport**:
- `Manifold/MeromorphicFunctionGermHolomorphicEquivPullback.lean` —
  germ-field pullback `MeromorphicFunctionGerm Y → MeromorphicFunctionGerm
  X` via composition with `e`, preserving `orderAt`.
- `Topology/LinearSystemGermDeltaPHolomorphicEquivTransport.lean` —
  `IsBoundedByDeltaPGerm` iff under pullback; bundled `LinearMap`
  between `L(δ(e p))` and `L(δp)`.
- `Topology/LinearSystemGermDeltaPFiniteDimTransport.lean` —
  `LinearEquiv` packaging + `Module.Finite.equiv` to transport
  `LinearSystemGermDeltaPFiniteDim`.

**Final assembly**:
- `Topology/RRDimGE2FromUniformizationAndFiniteDim.lean` /
  `Topology/RRDimGE2FromUniformizationAndFiniteDimRS.lean` —
  `rr_DimGE2_GenusZero_Germ_of_uniformization_and_RSFiniteDim` and
  variants. Headline assembly.

## 2026-05-13 — Period-lattice arc PL-1 closed + germfield arc to main

**Germfield arc (item 14 reduction)** — `2e5cfb4..main`:
- 9 chips landed reducing item 14's `genus_eq_zero_iff_homeo` from 5 named
  classical hypotheses to **one classical input**
  (`ExistsSimplePoleGermAtSomePoint X`) modulo the **structural typeclass**
  `[Subsingleton (HolomorphicOneForm X)]`.
- New files: `Manifold/MeromorphicFunctionField.lean`,
  `Manifold/MeromorphicFunctionGermCanonicalize.lean`,
  `Manifold/MeromorphicFunctionGermIdentityCorollary.lean`,
  `Topology/LinearSystemGermDeltaP.lean`,
  `Topology/RRDimensionFormGerm.lean`,
  `Topology/RRGenusZeroGermComposition.lean`,
  `Topology/RRStrictLtFromSimplePole.lean`,
  `Topology/Item14FromGermfield.lean`,
  `Topology/HTopFromSubsingleton.lean`.

**Period-lattice arc PL-1** — `60ba76d`, `df0227c`, `8f4e0a7`:

- `Manifold/ComplexManifoldRealification.lean` — bridging
  `instance complexManifoldRealification : IsManifold 𝓘(ℝ, ℂ) n X` from
  `[IsManifold 𝓘(ℂ, ℂ) ω X]`. Unblocks `SmoothOneForm 𝓘(ℝ, ℂ) X` as the
  ambient type for the real-side period pairing.
- `Manifold/HolomorphicOneFormRealComponent.lean` (400 LOC) — the bundled
  PL-1 step in full. Provides:
  - `realPartCLM`, `imagPartCLM : (ℂ →L[ℂ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℝ)` as
    bundled continuous **ℝ**-linear maps.
  - `tangentBundleCore_coordChange_restrictScalars_eq` — the two manifold
    structures' tangent transitions related by `restrictScalars ℝ`.
  - `cotangentBundleCore_coordChange_realPartCLM` / `_imagPartCLM` —
    cotangent coordinate change commutes with the fibrewise CLMs.
  - `ContMDiffAt_restrictScalars_to_real` — manifold-level scalar
    restriction bridge.
  - `realPart_section_contMDiff` / `_imag` — section smoothness over the
    real cotangent bundle.
  - `realComponent`, `imagComponent : HolomorphicOneForm X → SmoothOneForm
    𝓘(ℝ, ℂ) X` — the bundled deliverable.

  Recurring obstacle navigated throughout: the `NormedSpace ℝ ℂ` instance
  diamond (between `NormedSpace.complexToReal` priority-900 and
  `NormedAlgebra.toNormedSpace`) breaks `IsScalarTower.right`'s unifier
  whenever the synth context has `NormedSpace ℂ ℂ` resolved first. Pinned
  with `letI : NormedSpace ℝ ℂ := @NormedAlgebra.toNormedSpace ℝ ℂ _ _ _`
  per def at every `restrictScalars` site.

  Build: 8650 jobs, clean. PL-1 unblocks the holomorphic-side period
  pairing construction (PL-2).

## v0.1.0 (2026-04-26) — initial scaffold

- Repo scaffold (`lakefile.toml`, `lean-toolchain`, CI workflows, `.gitignore`).
- Mathlib pinned to commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (the
  exact rev Buzzard's challenge gist v0.3 specifies, dated 2026-04-15).
- `JacobianChallenge/Basic.lean` contains Buzzard's challenge signature
  verbatim; every `def`/`lemma`/`theorem` is `:= sorry`. Each `sorry`
  corresponds to one open item in `OPEN.md`.
- `DEVELOPMENT.md` carries the apfsd kernel-panic rules and CI-as-default
  workflow inherited from `sqg-lean-proofs` and `ns-lean-proofs`.
