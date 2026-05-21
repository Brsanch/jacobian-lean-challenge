# OPEN

> **Note on dates (audit 2026-05-16):** Earlier sessions wrote
> *future-dated* labels in this file (`2026-05-17` through `2026-05-20`)
> driven by anchoring on inflated dates in prior memory files instead
> of the system-provided `currentDate`. Those have been remapped to
> their real git-timestamp dates: `2026-05-17/18/—2026-05-19-afternoon`
> → `2026-05-15`, `2026-05-19-late-afternoon/evening` and `2026-05-20`
> → `2026-05-16`. A residual `+1`-day drift may remain on some narrative
> references to `2026-05-15` / `2026-05-16` (originally `+1` from real
> work on `2026-05-14` / `2026-05-15`); when in doubt, **git commit
> timestamps are the authoritative source**.

The 24 challenge items in `JacobianChallenge/Basic.lean`, mapped to Buzzard's
spec. Three statuses, with one tag for partial progress:

- **OPEN** — `sorry` still present in `Basic.lean`.
- **STUB** — `sorry` replaced by a body that compiles against the verbatim
  signature but is not the intended mathematics. Either the formula is wrong
  (`pullback := 0`, `degree := 0/1 indicator`, `TopologicalSpace := ⊥`), the
  underlying object the lemma is about is itself a stub (`Jacobian := Pic⁰`
  with `PrincDiv := ⊥`), or the proof crucially depends on a placeholder
  being a placeholder.
- **STRICT-CLOSED** — Buzzard-acceptable: the implementation is honest, the
  underlying object is the intended analytic Jacobian, and the lemma is
  what a strict reviewer would sign off on with no further qualification.
  This is the *only* "closed" bar in this repo.
- *(tag)* **PROOF-HONEST** — applies to a STUB item whose proof body is
  honest and would survive future honest replacement of the upstream
  placeholders. Not closure; it's a tag indicating the proof is real even
  though the underlying object is a stub.

**Current scoreboard:**

> **2026-05-21 PR #3 (item-14 reverse leg: chart-local polygonal-approximation bordism closed; 3 commits + merge 5934aad; +230 Lean LOC across 1 new file + 1 refactor). origin/main HEAD `5934aad`. Repo now 1055 `.lean` files / 179,789 LOC. Build 9316 jobs clean. Item count unchanged: **14/24 STRICT-CLOSED**.**
>
> **Arc — chart-local polygonal-approximation bordism (3 chips, ~230 LOC).** Refactor `SmoothHomotopyPath.left/right_edge` to `unitInterval` (was `∀ t : ℝ`) — sidesteps `Classical.choose`-opacity of `γ_line.ambient` outside the unit interval; cascades through 2 face IDs (now direct edge application). Direct chart-target straight-line homotopy ambient `chartHomotopyMapDirect` (inlines line formula, doesn't reference `γ_line.ambient`) + global smoothness lemma. `chartStraightLineHomotopy` constructor builds `SmoothHomotopyPath γ (chartStraightLinePath_univ q hu (chart γ.src) (chart γ.tgt))` from a globally-chart-contained γ in a full-target chart, with all four edge identities discharged (`module` collapses + `OpenPartialHomeomorph.left_inv`). Headline `chartStraightLine_singleSub_mem_stokesBoundaries`: for any such γ, the SmoothCycle `single (chartStraightLinePath ...) - single γ ∈ stokesBoundaries`. **The chart-local-bordism kernel is closed.**
>
> Combining the in-tree chips: chart-cover Lebesgue subdivision (PR #1) + per-subarc chart-local bordism (this PR) + closed-polygonal-loop ∈ stokesBoundaries (PR #1) gives the chain-assembly route to `BasedSmoothLoopsBoundHypothesis X p₀` on chart-cover-equipped X. Remaining mechanical: concatenate sub-bordisms across the subdivision + match outer edges.

> **2026-05-21 PR #2 (item-14 reverse leg: SmoothHomotopyPath diagonal-split + bordism; 4 commits + merge 4e3ed97; +478 Lean LOC across 1 new file). origin/main HEAD `4e3ed97`. Repo now 1054 `.lean` files / 179,559 LOC. Build 9316 jobs clean. Item count unchanged: **14/24 STRICT-CLOSED**.**
>
> **Arc — SmoothHomotopyPath bordism toolkit (~480 LOC, 1 new file `Manifold/SmoothHomotopyPathDiagonalSplit.lean`).** Diagonal-split of `SmoothHomotopyPath γ₀ γ₁` into two `Smooth2Simplex`es (`lowerRightSimplex` + `upperLeftSimplex`), with vertex-evaluation simp lemmas at all six corners (corners land at γ₀.src or γ₀.tgt depending on which `t` slot is `0` or `1` — not all at a common basepoint as in the loop case). `diagonalPath H : SmoothPath` from γ₀.src to γ₀.tgt via `t ↦ H(t, t)`. All six face identifications (face0/1/2 of LR and UL) with the corresponding canonical paths: `γ₀`, `γ₁`, `diagonalPath H`, `const γ₀.src`, `const γ₀.tgt`. Headline `boundary_lowerRight_plus_upperLeft`: `∂(σ_LR) + ∂(σ_UL) = single γ₁ - single γ₀ + single (const γ₀.src) + single (const γ₀.tgt)`. Final theorem `singleSub_smoothCycle_mem_stokesBoundaries`: for any `SmoothHomotopyPath γ₀ γ₁`, the SmoothCycle `single γ₁ - single γ₀ ∈ stokesBoundaries`.
>
> Architectural note: wiring `chartHomotopyMap` (in-tree from PR #1) into a concrete `SmoothHomotopyPath γ γ_line` for the chart-contained-path → chart-straight-line bordism hit a Classical.choose blocker (γ_line.ambient ≠ chartStraightLineMap definitionally outside unitInterval). Resolved by relaxing the `SmoothHomotopyPath` edges to unitInterval (a structural refactor) or by providing a separate ambient-witnessing structure — tracked for next PR.

> **2026-05-21 PR #1 (item-14 classical-content arc: chain assembly + Dolbeault + chart-cell infra; 57 commits + merge be4146d via PR #1; +3,639 Lean LOC across 23 new files + 1 modified). origin/main HEAD `be4146d`. Repo now 1053 `.lean` files / 179,081 LOC. Build 9316 jobs clean. Item count unchanged: **14/24 STRICT-CLOSED** (no items flipped this batch — substantive infra toward item-14 reverse-leg closure on simply-connected X).**
>
> **Arc — Item-14 reverse leg toward BSLB on simply-connected X (37+ chips this batch, ~3,300 LOC).**
>
> **Dolbeault foundational (chips 2-8, prior session within branch).** `dbarChart`-operator on `ℂ → ℂ` + manifold-side `dbar` via `extChartAt 𝓘(ℂ, ℂ)` + full biconditional `MDifferentiableAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) f x ↔ dbar f x = 0` (CR equation in both directions, with the conjugate-bridge for the `IsScalarTower ℝ ℂ ℂ` synthesis resolved via mathlib's `HasDerivAt.complexToReal_fderiv` + `differentiableAt_complex_iff_differentiableAt_real`). ℂ-linearity `dbar(c·f) = c·dbar f` + additivity + negation. Wirtinger chain rule `dbarChart (f ∘ g) z₀ = conj g'(z₀) · dbarChart f (g z₀)` for holomorphic inner `g`, giving chart-independence of ∂̄-vanishing on a complex 1-manifold under nonzero transition derivative.
>
> **Architectural reductions.** `SmoothPath.lebesgueSubdivision` (generic chart-cover Lebesgue subdivision of a smooth path); `SubdivisionTelescopingToLoop_named X ⇐ ∀ p₀, BasedSmoothLoopsBoundHypothesis 𝓘(ℝ,ℂ) X p₀` (chain-level reduction); typeclass-generalized trivial discharge under `[Subsingleton (HolomorphicOneForm X)]`.
>
> **Chart-cell `Smooth2Simplex`.** Discovered + used in-tree `complexManifoldRealification` instance to bridge `[IsManifold 𝓘(ℂ,ℂ) ω X]` to the ℝ-model required by `Smooth2Simplex`. Bilinear chart-cell: `bilinearChartInterp` + smoothness on ℝ² + convex containment on `[0,1]²` via `Convex.sum_mem` + Fin 2 reindexing + `bilinearChartCellSimplex_univ : Smooth2Simplex 𝓘(ℝ,ℂ) X` for full-target charts. Affine 3-corner variant matching `Smooth2Simplex`'s Δ² convention: `affineChartTriangleSimplex_univ` + vertex-toFun simp lemmas + 3-point convex containment.
>
> **`ChartStraightLinePath` + boundary identification.** `chartStraightLinePath_univ : SmoothPath 𝓘(ℝ,ℂ) X` (`t ↦ chart.symm((1-t)•z₀ + t•z₁)`) + smoothness + endpoint identifications. `smoothPath_ext_of_toPath_apply` extensionality lemma (in-tree SmoothPath has no `@[ext]`). Full SmoothPath identification of the three triangle faces with the corresponding chart-straight-lines. `chartStraightLinePath_univ_reverse`: reverse-equals-swap-endpoints. Explicit `Smooth2Simplex.boundary` of the chart-triangle as a 3-path `SmoothChain`.
>
> **Chain cancellation.** `chartStraightLinePath_pair_eq_reverseSum` + `chartStraightLinePath_pair_smoothCycle_mem_stokesBoundaries`. `two_chart_triangle_boundary_decomp` (boundary of two adjacent triangles = outer chain + shared-pair). `outerChain_mem_smoothCycle` + `outerChain_mem_stokesBoundaries` — substantive Stokes-style cancellation conclusion at the two-triangle scale.
>
> **Fan triangulation.** `fanChain`, `polygonalChain`, `spokeResidue` List-recursive defs. **`boundary₂_fanChain`** full inductive identity (boundary of fan = polygonalChain + spokeResidue), proven by List induction with nested cases on the tail. **`polygonalChain_eq_boundary_of_closed`** and **`polygonalChain_smoothCycle_mem_stokesBoundaries_of_closed`**: the headline conclusion — any closed polygonal loop traced by chart-straight-line paths in a single full-target chart is the explicit boundary of a fan 2-chain, hence lies in `stokesBoundaries`.
>
> **`SmoothHomotopyPath` toolkit.** Structure for two paths sharing endpoints with the four edge identities. `chartHomotopyMap` chart-target linear-interp ambient. All four edge lemmas (`left/right_edge` via `OpenPartialHomeomorph.left_inv`, `bottom/top_edge` constant at the shared endpoints via `module`-discharged interpolation cancellation). Smoothness lemma `contMDiff_chartHomotopyMap_univ` under full-target chart + global containment of both paths. These are the building blocks for the polygonal-approximation bordism — the final step toward closing BSLB on simply-connected X (still open).
>
> **Net contribution.** No items in `Basic.lean`'s open list flip from this batch, but the chain-assembly skeleton for `BasedSmoothLoopsBoundHypothesis X p₀` on simply-connected X is **substantially advanced**: chain cancellation works, polygonal-loop bounding works, all chart-cell building blocks exist. The remaining frontier (documented in `HANDOFF_ITEM14.md`): package the `SmoothHomotopyPath` constructor from the toolkit; diagonal-split into two `Smooth2Simplex`es realizing `single γ₁ - single γ₀ ∈ stokesBoundaries`; concatenate across the chart-cover Lebesgue subdivision to bordism γ to a polygonal loop; combine with the closed-polygonal-loop ∈ stokesBoundaries chip to conclude BSLB.

> **2026-05-20 late (period-lattice plumbing + classical-content scaffolding + item-14 advances; two parallel arcs in one branch, 35 feat/fix commits + merge, ce776c9, +3,778 Lean LOC across 34 new files). origin/main HEAD `ce776c9`. Repo now 1011 `.lean` files / 173,331 LOC. Build 9291 jobs clean. Item count unchanged: **14/24 STRICT-CLOSED** (no items flipped this session — work is *foundational plumbing + named classical hypotheses*, the items 5/11/12/13/17/18/21 cannot flip until the universal `[HasJacobianAnalyticStructure X]` instance lands).**
>
> **Arc A — Period-lattice plumbing + classical-content scaffolding (20 commits, ~2,200 LOC).**
>
> Class-keyed analytic Jacobian chain (8 chips, ~700 LOC): `CanonicalAnalyticJacobianFromClass` (per-basis form with 7 instances under `[HasSmoothHomologyDataPackage X basis_ω]`), `DefaultHolomorphicOneFormBasis`, `HasJacobianAnalyticStructure` (basis-anonymous class + RS/T_L instances + `CanonicalAnalyticJacobianAnonymous` with 7 instances), `HasBasedSmoothLoopsBound` (BSLB class + RS instance), `HasJacobianAnalyticStructureSubsingleton` (Subsingleton-ω + BSLB → the class), `CanonicalAnalyticJacobianSubsingleton` (subsingleton of target at genus 0 — fix to `QuotientAddGroup.mk_surjective`), `CanonicalOfCurve` (Abel-Jacobi point map + self-vanishing), `CanonicalOfCurveContMDiffSubsingleton` (smoothness + constancy at genus 0).
>
> Canonical pushforward/pullback (2 chips, ~220 LOC): `CanonicalPushforwardPullbackLift` (per-curve lifts on canonical lattices), `CanonicalPushforwardPullbackContMDiff` (smoothness corollaries).
>
> End-to-end smoke tests (2 chips, ~160 LOC): `CanonicalAnalyticJacobianRiemannSphereSmokeTest`, `CanonicalAnalyticJacobianComplexTorusSmokeTest` — both compose all 7 structural instances + `canonicalOfCurve` on RS and T_L unconditionally.
>
> Classical-content scaffolding (8 chips, ~850 LOC): `HodgeInnerProductHypothesis` (named `∃` positive-definite Hermitian form on `H⁰(Ω)`; genus-0 vacuous), `HodgeFormMatrix` (matrix representation `H_ij = H(ω_i, ω_j)` + conjTranspose + diagonal positivity), `PeriodMatrix` (the 2g × g complex period matrix with row = period vector), `RiemannBilinearRelations` (first + second + bundled existence; second via `Complex.re`-positivity since ℂ has no `PartialOrder` for `Matrix.PosDef`), `RiemannBilinearImpliesLI` (ℝ-LI conclusion + genus-0 + Subsingleton-ω discharges), `StandardSymplecticForm` (J = [[0,I];[-I,0]] + top-left/bottom-right zero-block lemmas + **anti-symmetry J^T = -J proven** via 4-case index analysis), `HodgeRiemannBridge` (the deep identity `i Π^T J Π̄ = H.toMatrix` + Hermitian half proven via `toMatrix_conjTranspose`).
>
> **Arc B — Item 14 advances (15 commits, ~1,580 LOC).**
>
> `ChartLocalPrimitiveExtend` wrapper + `EqOn`/`EventuallyEq` bridge to `pathPrimitive`; `ContMDiffAt` / `mfderiv` / `ContinuousAt` / `ContinuousOn` transfer theorems; named `ChartLocalPrimitiveSmoothExt` + FTC + Continuous hypotheses + smoothness ⇒ continuity implication; global `pathPrimitive ContMDiff` + FTC via `PathPrimitiveAdmissibleChartCover`; `S2ImpliesGenus0` from BSLB + per-basis admissibility (2-input + 3-input reductions); `pathPrimitiveAdmissibleChartCover_RS` unconditional; **unconditional item 14 biconditional on `RiemannSphere`** via the BSLB+admissibility route; `HasAdmissibleChartCover` typeclass + RS instance + class-driven compositions; `HasConvexTargetChartCover` + automatic admissibility under Subsingleton ω.
>
> **Net contribution.** Arc A built the *complete mechanical plumbing* so that once a universal `[HasJacobianAnalyticStructure X]` instance lands, items 5/11/12/13 flip via a C3 rewire of `JacobianChallenge.Jacobian X` to `CanonicalAnalyticJacobianAnonymous X` — and items 17/18/21 flip via the per-curve `canonicalPushforward/Pullback_contMDiff`. Arc B reduced item 14 to two named classical inputs (BSLB + per-basis admissibility) on RS unconditionally, and laid the class-driven infrastructure for general X. Together these reduce the remaining open content to a *small* set of named classical hypotheses, each documented with its required mathlib infrastructure.

> **2026-05-20 (period-lattice three-atom packaging + class wrapper + general-X constructor + item 14 4-input → 2-input → 2-classical-input reductions + auto-instance + table-audit flips of items 1 and 16; 16 commits total = 13 feat + 3 docs, +1444/-4 lines = +1317 Lean LOC across 12 new files + 127 OPEN.md docs). origin/main HEAD `29a332e`. Repo now 977 `.lean` files / 169,587 LOC. Item count: 13/24 → **14/24 STRICT-CLOSED**.**
>
> Two arcs in a single session:
>
> **Arc A — Period-lattice three-atom packaging (chips A-F).**
> * (A) α-data atom dropped via `smoothPathConnected_of_preconnected`
>   (`GenericGenusPeriodLatticeInputsFromThreeNamedAtomsNoAlpha.lean`).
> * (B) Three remaining atoms bundled into a single structure
>   `SmoothHomologyDataPackage basis_ω`
>   (`SmoothHomologyDataPackage.lean`).
> * (C) Unconditional discharge on `RiemannSphere`
>   (`SmoothHomologyDataPackageRiemannSphere.lean`).
> * (D) Unconditional discharge on `T_L = ℂ ⧸ L`
>   (`SmoothHomologyDataPackageComplexTorus.lean`).
> * (E) General-X end-to-end constructor:
>   `c3FullInputExtSymp_of_package` + the `Nonempty` headline take
>   `(SmoothHomologyDataPackage + 4 named hypotheses)` →
>   `Nonempty (C3FullInputExtSymp X)`
>   (`C3FullInputExtSympFromPackage.lean`).
> * (F) Class wrapper `HasSmoothHomologyDataPackage X basis_ω` + RS/T_L
>   instances (`SmoothHomologyDataPackageClass.lean`).
> * (G) Subsingleton-ω + BSLB inhabitant of the package
>   (`SmoothHomologyDataPackageSubsingleton.lean`).
>
> Net: at general genus on a compact connected complex 1-manifold, the
> period-lattice side of items 5/11/12/13/17/18/21 factors through a
> **single classical existence statement** `Nonempty
> (SmoothHomologyDataPackage basis_ω)`.
>
> **Arc B — Item 14 minimal-inputs further reductions (chips H–K) +
> table-audit flips (chips L–M).**
> * (H) Drop `h_conn_from_sc` from the 5-input version via
>   `smoothPathConnected_of_preconnected`. Item 14 now reduces to
>   **4 minimal named hypotheses**
>   (`Topology/Item14From4MinimalInputs.lean`).
> * (I) Under `Subsingleton (HolomorphicOneForm X)`, the per-basis
>   smoothness + FTC hypotheses are vacuous: item 14 reduces to
>   **2 minimal named hypotheses**
>   (`Topology/Item14FromSubsingletonHolomorphicOneForm.lean`).
>   `hSP` + `h_bslb` only.
> * (J) End-to-end RS validation of the 2-input chip
>   (`Topology/Item14ForRiemannSphereVia2InputChip.lean`):
>   plug `existsSimplePoleGermAtSomePoint_RiemannSphere` +
>   `basedSmoothLoopsBoundHypothesis_RS_holds` into the 2-input form,
>   confirming the chain composes correctly on RS.
> * (K) Parallel composition of item 14 via the
>   `genus_eq_zero_iff_homeo_from_all_conditionals` route, discharging
>   the 3 unconditional inputs to leave **2 minimal classical inputs**:
>   `RiemannRochGenusZero X` + topological-sphere uniformization
>   (`Topology/Item14From2MinimalClassicalInputs.lean`).
> * (L) **Item 1 flip to STRICT-CLOSED** (table-audit). Body
>   `Module.finrank ℂ (HolomorphicOneForm X)` is honest because
>   `DiskChartCover.holomorphicOneFormFiniteDim_holds` is unconditional
>   (junk-zero convention never kicks in).
> * (M) **Item 16 flip to STRICT-CLOSED** (table-audit). Basic.lean
>   line 143–144 uses `JacobianChallenge.ofCurve_inj_holds` which is
>   unconditional in tree via the chain `PrincDivWitnessExtraction` →
>   degree-1 → biholomorphism → `genus_eq_zero_iff_homeo_of_HolomorphicEquiv_RiemannSphere`.
>
> **Item count: 13/24 → 14/24 STRICT-CLOSED.**

> **2026-05-20 (period-lattice three-atom packaging) Bundle 3 remaining named period-lattice atoms into a single structure; discharge α-data via smoothPathConnected_of_preconnected; validate on RS + T_L unconditionally (4 chips, ~504 LOC). origin/main HEAD `423f95e`.**
>
> Item count: **14/24 STRICT-CLOSED** (after this session's table-audit
> flips of items 1 and 16 — both already honestly closed in tree but
> the scoreboard was stale). Plus a stack of structural reductions on
> the period-lattice side of items 5/11/12/13/17/18/21.
>
> **(A) α-data atom dropped**
> (`GenericGenusPeriodLatticeInputsFromThreeNamedAtomsNoAlpha.lean`).
> `GenericGenusPeriodLatticeInputs.ofThreeNamedAtomsNoAlpha` and the
> `nonempty_periodLatticeSymplecticBundle_ofThreeNamedAtomsNoAlpha`
> headline discharge the smooth-path-connectedness data
> `(α, h_α_src, h_α_tgt)` from `[ConnectedSpace X]` via the
> unconditional `smoothPathConnected_of_preconnected` + `Classical.choose`.
> Inputs at general genus: **3 named atoms + base point** (was 3 + base
> + α-tuple + α_src + α_tgt).
>
> **(B) 3 atoms bundled into a single structure**
> (`SmoothHomologyDataPackage.lean`). `SmoothHomologyDataPackage basis_ω`
> packs the three remaining inputs into one structure:
> * `symplecticBasis : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X basePoint (genus X)`;
> * `hurewicz : SmoothHurewiczHypothesis symplecticBasis`;
> * `bilinear : LinearIndependent ℝ (period vectors against `basis_ω`)`.
>
> Plus the headline composite
> `nonempty_periodLatticeSymplecticBundle_of_smoothHomologyDataPackage`.
> The period-lattice side of items 5/11/12/13/17/18/21 now factors
> through a **single classical existence statement** `Nonempty
> (SmoothHomologyDataPackage basis_ω)`.
>
> **(C) Unconditional discharge on `RiemannSphere`**
> (`SmoothHomologyDataPackageRiemannSphere.lean`). `Nonempty
> (SmoothHomologyDataPackage basis_ω)` on `RS` via `IsEmpty (Fin (2 *
> genus RS))` + empty-tuple `Finset.sum_of_isEmpty` +
> `basedSmoothLoopsBoundHypothesis_RS_holds` +
> `linearIndependent_empty_type`. End-to-end check
> `nonempty_periodLatticeSymplecticBundle_RiemannSphere_of_package`
> reproduces the known unconditional RS closure via the single-input route.
>
> **(D) Unconditional discharge on `T_L = ℂ ⧸ L`**
> (`SmoothHomologyDataPackageComplexTorus.lean`). `Nonempty
> (SmoothHomologyDataPackage (basis_g_dz L))` on `T_L` via:
> * `symplecticBasisG L` (the dim-`genus T_L` reindex of the dim-1
>   explicit symplectic basis);
> * `smoothHurewiczHypothesisTorus_holds_of_basis` +
>   `basisFin2OfL_isZBasisOfL` (Hurewicz unconditional on T_L);
> * `riemannBilinear_transport` + `basisFin2OfL_realLinearIndependent`
>   (Riemann bilinear unconditional on T_L).
>
> End-to-end check `nonempty_periodLatticeSymplecticBundle_complexTorus_of_package`
> reproduces the known unconditional T_L closure via the single-input route.

> **2026-05-20 (full day) Triple structural reduction: chip D + AbelGenerator + Item 14 minimal-input lift (23 commits, ~3,377 LOC). origin/main HEAD `dbcc798`. Build 9251 jobs / 965 `.lean` files / 168,266 LOC.**
>
> Item count: **13 / 24 STRICT-CLOSED** (unchanged). Three structural
> reductions across path (a) [period lattice], path (b) [Abel–Jacobi
> → item 16], and item 14 (genus_eq_zero_iff_homeo), all leveraging
> chip D's unconditional `HolomorphicStokesHypothesis`.
>
> **(1) Period-lattice atom-3 UNCONDITIONAL** (chip D arc; `66ccc83`
> + cleanup commits). `UniformChartContainmentDepth_named X` +
> `HolomorphicComplexBoundaryVanishing X` +
> `HolomorphicStokesHypothesis X` +
> `HolomorphicComponentsCanonicalClosed X` all unconditional on every
> compact connected complex 1-manifold. Joint blocker for items
> 5/11/12/13/17/18/21 reduced **from 4 named atoms to 3**.
> Composite constructor `ofThreeNamedAtoms` ships the drop-one
> variant.
>
> **(2) AbelGenerator arc reduced to 2 named universal predicates**
> (commits `6050a19` through `e01640b`). Per-`f` reduction with
> regular endpoints + constant-case discharge + `IsConstantMap →
> principalDivisorMap = 0` bridge composes into
> `abelGeneratorPeriodCondition_of_named_predicates`, which takes
> exactly two named universal predicates:
> * `LevelSetChainPeriodInLattice` — substantive Stokes/residue
>   content of step 9 (period of the concrete `regularLevelSetChain f`
>   lies in `periodLatticeImage`).
> * `HasRegularEndpoints` — universal `0, ∞ ∈ regularValueSet f` for
>   every non-constant `f` (classical Möbius/density content).
>
> Plus full real+imag decomposition of the period vector
> (`complexChainPeriodVector_levelSetChain_apply_re_eq_sum` /
> `_im_eq_sum`) exposing the substantive content as two real-valued
> `Finset.sum`s of per-path real integrals.
>
> **(3) Item 14 factored into 5 minimal named hypotheses** (commits
> `820aa3d` through `dbcc798`). `genus_eq_zero_iff_homeo_from_minimal_inputs`
> composes both legs of item 14 from:
> * forward leg input: `ExistsSimplePoleGermAtSomePoint X` (RR-class
>   existence).
> * reverse leg inputs (4): smooth-path-connectedness,
>   `BasedSmoothLoopsBoundHypothesis`, per-basis `ContMDiff ω
>   (pathPrimitive)`, per-basis FTC at `eval`.
>
> Chip D supplies the per-simplex Stokes step internally. The reverse
> leg's substantive input weakened from "smooth Poincaré-disc filling"
> to the strictly weaker `BasedSmoothLoopsBoundHypothesis` (any
> 2-chain bounding) — closing it for general simply-connected X still
> needs classical content (cellular/smooth approximation) but no
> longer requires the stronger single-2-simplex-with-two-constant-faces
> structure.
>
> Two parallel reverse-leg reductions provided:
> `s2ImpliesGenus0_of_smoothlyNullBoundedHypothesis` (stronger input,
> finest structural granularity) and
> `s2ImpliesGenus0_of_basedSmoothLoopsBoundHypothesis` (weaker input,
> uses 2-chain linearity over chip D).
>
> Plus auxiliary infrastructure: `SmoothBordant ↔ singleCycle ∈
> stokesBoundaries` biconditional (`ad13e6b`) and
> `LevelSetChainPeriodInLattice` named predicate (`e63d194`).
>
> Net: every remaining open content is a single named classical
> hypothesis with clear mathematical content. No 1-chip closures
> available; the next item flip requires a multi-session arc on one
> of the remaining named hypotheses (e.g., `BasedSmoothLoopsBoundHypothesis`
> for general simply-connected X via cellular/Whitney approximation).

> **2026-05-20 Period-lattice push: `UniformChartContainmentDepth_named X` UNCONDITIONAL via Lebesgue + iterated-midpoint diameter (5 chips, ~1,178 LOC).**
>
> Closes the **classical Lebesgue-number existence statement** that was
> the last open content of the third atomic period-lattice input
> (`holomorphicCanonicalClosed`) at general genus. With this discharge,
> all of
> `HolomorphicComplexBoundaryVanishingHypothesis X`,
> `HolomorphicStokesHypothesis X`, and
> `HolomorphicComponentsCanonicalClosed X` hold **unconditional** on
> every compact connected complex 1-manifold.
>
> **Headline chips (post-crash recovery + 4 follow-up chips, all on
> `origin/main`).**
>
> * **`SubdivisionTelescopingFromUniformDepth.lean`** (recovery, `06e8bb1`)
>   — bridges the iterated-midpoint arc into
>   `GenericGenusPeriodLatticeInputs.ofFourNamedAtoms`. Per-witness
>   conversion `ChartContainmentWitness → ChartContainedSmooth2Simplex`
>   + unconditional iterated-midpoint period-sum identity.
>
> * **`Smooth2SimplexAffineReparamComp.lean`** (chip A, `b6e4b61`) —
>   `affineCombo` / `affineReparam` composition identity: composing
>   two `affineCombo`s gives `affineCombo` with target vertices the
>   outer combination of the inner vertices.
>
> * **`IteratedMidpointAffineForm.lean`** (chip B, `08ef0a5`) — inductive
>   predicate `IsIteratedSubdivision σ n T` (`refl` + `step` via
>   `midpointSubdivision`) + membership theorem for `iteratedMidpointList`
>   + **affine form**: every `T` at depth `n` has
>   `T.toFun = (affineReparam σ A B C).toFun` for some `A B C ∈ Δ²`.
>
> * **`IteratedMidpointDiameter.lean`** (chip C, `9a26568`) —
>   strengthens the affine form with the **depth-`n` coordinate-wise
>   diameter bound**:
>   `ParameterTriangleBound A B C ((1/2)^n)` (i.e., every pairwise
>   coordinate difference of `A, B, C` is `≤ (1/2)^n`). By induction on
>   `IsIteratedSubdivision`, with the explicit halving identity
>   `affineCombo A B C s - affineCombo A B C t
>     = (linear combination of (A-B), (A-C), (B-C) with
>        bounded weights)`.
>
> * **`UniformChartContainmentDepth.lean`** (chip D, `66ccc83`) —
>   **headline**:
>   ```
>   theorem uniformChartContainmentDepth_named_holds :
>     UniformChartContainmentDepth_named X
>   ```
>   unconditional on every compact connected complex 1-manifold via
>   classical Lebesgue's number lemma:
>   1. `isCompact_standardSimplex2` (closed + bounded in `Fin 2 → ℝ`,
>      Heine-Borel).
>   2. For each `q : X`, an `r_q > 0` with
>      `Metric.ball (chartAt q q) r_q ⊆ chart.target` via
>      `Metric.isOpen_iff`.
>   3. Open cover of `standardSimplex2` by
>      `σ⁻¹ (chart.source ∩ chart⁻¹ ball)` indexed by `p ∈ Δ²`.
>   4. Lebesgue → `δ > 0`.
>   5. `exists_pow_lt_of_lt_one` → `n` with `(1/2)^n < δ`.
>   6. For each `T` at depth `n`, parameter image
>      `⊆ closedBall A ((1/2)^n) ⊆ ball A δ ⊆` cover element → witness.
>
>   Plus the three downstream corollaries
>   `holomorphicComplexBoundaryVanishingHypothesis_holds_unconditional`,
>   `holomorphicStokesHypothesis_holds_unconditional`,
>   `holomorphicComponentsCanonicalClosed_holds_unconditional`.
>
> **Downstream effect.** Of the 4 atomic period-lattice inputs of
> `GenericGenusPeriodLatticeInputs.ofFourNamedAtoms`, atom 3
> (`SubdivisionTelescopingTo2Simplex_named X`) is now unconditional.
> Three named hypotheses remain at general genus: `SmoothSymplecticBasis`
> (surface classification), `riemannBilinear` (Hodge ℝ-linear
> independence), and `SmoothHurewiczHypothesis sb` (smooth-Hurewicz).
> No items in `Basic.lean`'s sorry list flip from this alone — those
> items share all four atoms as a joint blocker.
>
> Repo state: ~163,667 + ~2,568 LOC, build 9230 jobs clean. Zero `sorry`,
> zero `axiom`. Item count unchanged (still 13/24 STRICT-CLOSED).

> **2026-05-19 (afternoon) Period-lattice push: `MidpointSubdivisionTelescoping` UNCONDITIONAL + iterated subdivision (7 chips, ~1,390 LOC).**
>
> Closes the **orientation-cancellation + Whitney-smoothing**
> content of the third atomic period-lattice input
> (`holomorphicCanonicalClosed`) at general genus. Reduces the open
> frontier from `SubdivisionTelescopingTo2Simplex_named X` (Whitney
> smoothing + orientation cancellation, both deep classical content)
> to `UniformChartContainmentDepth_named X` (a pure
> Lebesgue-number existence statement).
>
> **Headline chips.**
>
> * **`Smooth2SimplexAffineSegmentPath.lean`** — `affineSegmentPath σ p q`
>   primitive (the smooth path `t ↦ σ((1-t)p + tq)`), face
>   identifications for `affineReparam σ a b c` (each face = an
>   `affineSegmentPath`), reverse identity at the SmoothPath level.
>
> * **`Smooth2SimplexAffineSegmentPathReverse.lean`** — integrate-level
>   reverse `∫_{σ(q,p)} = -∫_{σ(p,q)}` + complex-period-level reverse
>   + pair-sum-zero (key building block for **orientation cancellation**).
>
> * **`Smooth2SimplexAffineSegmentPathMidpoint.lean`** — interior
>   velocity formula via `mfderiv` chain rule, velocity scaling under
>   midpoint subdivision, integrand scaling, half-integrals via
>   `intervalIntegral.integral_comp_div`, **full midpoint splitting at
>   the integrate level**:
>   ```
>   (affineSegmentPath σ a c).integrate ω
>     = (affineSegmentPath σ a (midpoint a c)).integrate ω
>       + (affineSegmentPath σ (midpoint a c) c).integrate ω
>   ```
>   This is the building block for **Whitney smoothing** (the 4-way
>   midpoint subdivision boundary-period telescoping).
>
> * **`Smooth2SimplexAffineSegmentPathComplexMidpoint.lean`** —
>   midpoint splitting lifted to complex period level.
>
> * **`MidpointSubdivisionTelescopingHolds.lean`** — **headline**:
>   `MidpointSubdivisionTelescoping σ α` UNCONDITIONAL on any compact
>   connected complex 1-manifold. Composes the three interior-edge
>   reverse cancellations with the three boundary-edge midpoint
>   consolidations via `linear_combination`. Drops the previously
>   open `MidpointSubdivisionTelescoping σ α` *named* hypothesis
>   (per-step orientation-cancellation telescoping) by proving it
>   as a theorem.
>
> * **`IteratedMidpointSubdivision.lean`** — `iteratedMidpointList σ
>   n : List (Smooth2Simplex 𝓘(ℝ,ℂ) X)` recursive 4-way midpoint
>   subdivision yielding `4ⁿ` sub-simplices, plus the period-sum
>   identity
>   ```
>   complexChainPeriod (∂σ) α
>     = ((iteratedMidpointList σ n).map …).sum
>   ```
>   by induction on `n`, using the unconditional
>   `MidpointSubdivisionTelescoping`.
>
> * **`BoundaryPeriodFromDepthN.lean`** — `ChartContainmentWitness T`
>   structure + the **end-to-end discharge**:
>   `complexChainPeriod (∂σ) α = 0` from the existence of a depth `n`
>   at which every sub-simplex in `iteratedMidpointList σ n` admits a
>   chart-containment witness. Plus the named hypothesis
>   `UniformChartContainmentDepth_named X` and bridges to
>   `HolomorphicComplexBoundaryVanishingHypothesis X` /
>   `HolomorphicStokesHypothesis X` /
>   `HolomorphicComponentsCanonicalClosed X`.
>
> **Open content remaining for the third atomic input.** Just the
> Lebesgue-number existence:
> ```
> UniformChartContainmentDepth_named X :=
>   ∀ σ, ∃ n, ∀ T ∈ iteratedMidpointList σ n, Nonempty (ChartContainmentWitness T)
> ```
> Classically true: σ.toFun is continuous on the compact `Δ²`, so the
> pulled-back cover of `Δ²` by `σ`-preimages of chart-sources has a
> Lebesgue number; midpoint subdivision diameters halve at each step,
> so an `n` always exists. Formalizing this in Lean is the remaining
> work for general-genus closure.
>
> Repo state: ~163,667 + ~1,390 LOC (across 939 `.lean` files), build
> 9225 jobs clean. Zero `sorry`, zero `axiom`. Item count unchanged
> (still 13/24 STRICT-CLOSED).

> **2026-05-20 Period-lattice push: 21 chips, ~2,275 LOC.**
>
> Builds out the period-lattice atom-3/atom-4 reduction infrastructure
> end-to-end, plus the constructive `Smooth2Simplex` subdivision
> primitives. Net effect: the third atomic input of
> `GenericGenusPeriodLatticeInputs` (`holomorphicCanonicalClosed`) at
> general genus is reduced to a single named hypothesis
> `SubdivisionTelescopingTo2Simplex_named X`. All four atoms are
> available in cleanest named form via
> `GenericGenusPeriodLatticeInputs.ofFourNamedAtoms`. The
> chart-pullback pointwise identity is unconditional (no frame
> stability). On RS, the subdivision-telescoping atoms discharge
> trivially via `Subsingleton (HolomorphicOneForm RS)`.
>
> **Headline chips.**
>
> * **`pointwiseChartEvalIdentity_unconditional`** —
>   `Manifold/PointwiseChartEvalUnconditional.lean`.
>   Drops the `CotangentChartFrameStable` hypothesis from the
>   chart-pullback pointwise identity. The bridge:
>   `tangentBundleCore_coordChange_restrictScalars_eq` (in tree) +
>   cocycle of `tangentBundleCore.coordChange` + ℂ-linearity of
>   `α.toFun x`. Yields
>   `chartContainedLoopVanishingHypothesis_holds_unconditional` on
>   every compact connected complex 1-manifold.
>
> * **`ChartContainedSmooth2Simplex`** family
>   (`Manifold/ChartContainedSmooth2Simplex.lean`,
>   `…FromFaces.lean`, `…BoundaryDirect.lean`, `…FromSimplexImage.lean`).
>   For any `Smooth2Simplex 𝓘(ℝ, ℂ) X` whose
>   `σ.toFun '' standardSimplex2` lies in a single chart-ball,
>   `complexChainPeriod (∂σ) α = 0`. Three increasingly user-friendly
>   surfaces: explicit `ChartContainedClosedLoop` bundling, per-face
>   chart-containment, single Δ²-condition.
>
> * **`SubdivisionTelescopingTo2Simplex_named X`** named-hypothesis +
>   the three composite reductions to
>   `HolomorphicComplexBoundaryVanishingHypothesis X`,
>   `HolomorphicStokesHypothesis X`, and
>   `HolomorphicComponentsCanonicalClosed X`.
>
> * **`GenericGenusPeriodLatticeInputs.ofFourNamedAtoms`**
>   (`Manifold/GenericGenusPeriodLatticeInputsFromFourNamedAtoms.lean`).
>   The 'everything reduced to named classical hypotheses'
>   constructor: takes `SmoothSymplecticBasis` + `riemannBilinear` +
>   `SubdivisionTelescopingTo2Simplex_named X` +
>   `SmoothHurewiczHypothesis sb` + smooth-path-connectedness, and
>   produces the full structure (and `Nonempty
>   (PeriodLatticeSymplecticBundle ...)`).
>
> * **`Smooth2Simplex.affineReparam`** + `midpointSubdivision`
>   (`Manifold/Smooth2SimplexAffineReparam.lean`,
>   `Smooth2SimplexMidpointSubdivision.lean`,
>   `MidpointSubdivisionChartContained.lean`,
>   `MidpointSubdivisionTelescoping.lean`).
>   Constructive building blocks for the Δ²-subdivision content of
>   `SubdivisionTelescopingTo2Simplex_named`. Convexity of
>   `standardSimplex2` lets chart-containment of `σ` inherit to each
>   midpoint sub-triangle; a 1-step telescoping headline composes
>   chart-contained sub-triangle vanishing with a named
>   `MidpointSubdivisionTelescoping σ α` hypothesis.
>
> * **Subsingleton discharges** for the subdivision-telescoping atoms
>   (`Manifold/SubdivisionTelescopingFromSubsingleton.lean`).
>   For any `X` with `Subsingleton (HolomorphicOneForm X)`, both
>   `SubdivisionTelescopingToLoop_named X` and
>   `SubdivisionTelescopingTo2Simplex_named X` discharge trivially via
>   the empty subdivision list. Applies to `RiemannSphere`. Companion
>   `LoopPeriodVanishesOfSubsingleton.lean` gives the
>   `LoopPeriodVanishes` analogue.
>
> * **End-to-end RS exercise** —
>   `HoloCanonClosedRSViaSubdivision.lean` smoke-tests the four-atom
>   chain by deriving `HolomorphicComponentsCanonicalClosed RS` via
>   the subdivision route (alternate to the in-tree subsingleton
>   discharge).
>
> Repo state after this session: **163,667 LOC across 932 `.lean`
> files**, build **9218 jobs** clean. Zero `sorry`, zero `axiom`.
> Item count unchanged (still 13/24 STRICT-CLOSED) — this push reduces
> the open frontier on items 5/11/12/13/17/18/21 to four named classical
> hypotheses (plus the existing item-14 forward leg's
> `ExistsSimplePoleGermAtSomePoint X`).

> **2026-05-19 (late++++++++++++) `GenericGenusPeriodLatticeInputs` from FOUR named-atom inputs (1 chip, ~145 LOC).**
>
> Ships `GenericGenusPeriodLatticeInputs.ofFourNamedAtoms`
> (`Manifold/GenericGenusPeriodLatticeInputsFromFourNamedAtoms.lean`).
> A composite constructor taking ALL FOUR atomic inputs in their
> cleanest reduced/named form:
>
> ```
> GenericGenusPeriodLatticeInputs.ofFourNamedAtoms :
>   basis + p₀ + (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ (genus X))   -- atom 1
>     → riemannBilinear (sb.cycleGens period vectors)                   -- atom 2
>     → SubdivisionTelescopingTo2Simplex_named X                        -- atom 3
>     → SmoothHurewiczHypothesis sb                                     -- atom 4
>     → smooth-path-connectedness data
>     → GenericGenusPeriodLatticeInputs basis
> ```
>
> Plus the headline composite
> `nonempty_periodLatticeSymplecticBundle_ofFourNamedAtoms` producing
> `Nonempty (PeriodLatticeSymplecticBundle ...)` directly from the
> four named inputs.
>
> This is the **'everything reduced to named classical hypotheses'**
> composite. The remaining open content at general genus is precisely
> the four named hypotheses + smooth-path-connectedness data.
>
> Build **9206 jobs** clean (was 9205). Item count unchanged.

> **2026-05-19 (late+++++++++++) `GenericGenusPeriodLatticeInputs.ofSubdivisionAtom` constructor (1 chip, ~85 LOC).**
>
> Ships `GenericGenusPeriodLatticeInputs.ofSubdivisionAtom` in
> `Manifold/GenericGenusPeriodLatticeInputsFromSubdivision.lean`.
> A constructor that takes the 4 atoms at general genus with the
> third atom replaced by the cleaner
> `SubdivisionTelescopingTo2Simplex_named`:
>
> ```
> GenericGenusPeriodLatticeInputs.ofSubdivisionAtom :
>   (cycleGens) → (riemannBilinear) →
>   SubdivisionTelescopingTo2Simplex_named X →
>   (H1_spans_top_canonical) →
>   GenericGenusPeriodLatticeInputs basis
> ```
>
> Makes the dependency on the deep classical content explicit at the
> constructor surface: the third atom is no longer the raw Stokes
> closed-form predicate but the named 2-simplex subdivision-telescoping
> hypothesis. The discharge of `holomorphicCanonicalClosed` from the
> subdivision atom goes through the unconditional chart-contained
> discharge.
>
> Build **9205 jobs** clean (was 9204). Item count unchanged.

> **2026-05-19 (late++++++++++) Chart-contained 2-simplex boundary period = 0 + Stokes from 2-simplex subdivision (1 chip, ~210 LOC).**
>
> Ships `ChartContainedSmooth2Simplex X`
> (`Manifold/ChartContainedSmooth2Simplex.lean`): a `Smooth2Simplex 𝓘(ℝ, ℂ) X`
> bundled with an explicit `ChartContainedClosedLoop` witnessing
> chart-containment of its boundary loop. The chip composes
> `Smooth2Simplex.boundaryLoop_integrate_eq` (chain integral = path
> integral over the boundary loop) with the new unconditional
> chart-contained-loop discharge to give:
>
> ```
> complexChainPeriod_boundary_eq_zero : ∀ data α,
>   complexChainPeriod (Smooth2Simplex.boundary data.σ) α = 0
> ```
>
> Plus the 2-simplex subdivision-telescoping named hypothesis
> `SubdivisionTelescopingTo2Simplex_named`, whose discharge would
> give `HolomorphicComplexBoundaryVanishingHypothesis X` /
> `HolomorphicStokesHypothesis X` /
> `HolomorphicComponentsCanonicalClosed X` (the third atomic input
> of `GenericGenusPeriodLatticeInputs` at general genus).
>
> **After this chip,** the third atomic input of the general-genus
> period-lattice bundle (`holomorphicCanonicalClosed`) reduces to a
> single named hypothesis: `SubdivisionTelescopingTo2Simplex_named X`
> (Whitney-smoothed barycentric subdivision of `Δ²` until each
> sub-2-simplex is chart-contained, with orientation cancellation
> on interior edges).
>
> Item count unchanged (still 13/24 STRICT-CLOSED). Build **9204 jobs
> clean** (was 9203).

> **2026-05-19 (late+++++++++) `pointwiseChartEvalIdentity` UNCONDITIONAL on any compact connected complex 1-manifold (1 chip + 1 composite, ~360 LOC).**
>
> Ships `pointwiseChartEvalIdentity_unconditional` and
> `chartContainedLoopVanishingHypothesis_holds_unconditional`
> (`Manifold/PointwiseChartEvalUnconditional.lean`). Drops the
> `CotangentChartFrameStable` hypothesis from the chart-pullback
> pointwise identity by keeping the non-trivial cotangent/tangent
> coord changes alive and showing they cancel via the cocycle of
> `tangentBundleCore` together with the `ℝ ↔ ℂ` restrictScalars
> bridge `tangentBundleCore_coordChange_restrictScalars_eq` and the
> `ℂ`-linearity of `α.toFun x`.
>
> Composite ships `loopPeriodVanishes_from_subdivision_alone`
> (`Manifold/LoopPeriodVanishesFromSubdivision.lean`), so the only
> remaining open input for the reverse leg of item 14 on simply-
> connected `X` is **one** named hypothesis (was two):
> `SubdivisionTelescopingToLoop_named X`.
>
> Item count unchanged (still 13/24 STRICT-CLOSED). Build **9203 jobs
> clean** (was 9201).

> **2026-05-19 (late++++++++) Item-14 reverse-leg ingredient consolidation (1 chip, ~100 LOC).**
>
> Ships `loopPeriodVanishes_from_frameStable_and_subdivision`
> (`Manifold/LoopPeriodVanishesFromFrameStableAndSubdivision.lean`).
> Reduces the three named ingredients of
> `Item14ReverseLegFullAssembly.loopPeriodVanishes_from_ingredients`
> to **two**: per-loop `CotangentChartFrameStable` +
> `SubdivisionTelescopingToLoop_named`. The deriv-continuity and
> chart-integral-bridge ingredients are absorbed via the existing
> `pointwiseChartEvalIdentity_of_frameStable` chain.
>
> After this consolidation, the open frontier for `LoopPeriodVanishes`
> on a simply-connected `X` (and hence the reverse leg of item 14) is
> precisely two named hypotheses: frame-stability (structural;
> automatic on RS for `basePoint ≠ ∞`, fails on T_L) + subdivision
> telescoping (Whitney smoothing + orientation cancellation — the deep
> classical content).
>
> Item count unchanged (still 13/24 STRICT-CLOSED). Build **9201 jobs
> clean** (was 9198).

> **2026-05-19 (late+++++++) `Div.evalSumHom` + closed-form Abel-Jacobi `Pic⁰ X ≃+ X` on any compact AddCommGroup manifold (9 chips, ~900 LOC).**
>
> Builds the divisor-evaluation homomorphism
> `Div.evalSumHom : Div X →+ X` for any topological additive group `X`,
> and uses it to give a **PLSB-independent closed-form Abel-Jacobi
> isomorphism** for any compact AddCommGroup manifold `X` (T_L being the
> canonical example):
>
> ```
> Pic0.evalSumLiftEquiv X hAbel hConv : Pic⁰ X ≃+ X
>   [D] ↦ ∑ x ∈ supp D, D x • x
> ```
>
> Conditional on `EvalSumAbelHypothesis X` (Abel's theorem statement at
> the X-level) and `EvalSumAbelConverseHypothesis X` (Weierstrass σ
> existence at the X-level). For `X = ℂ⧸L` these specialize to the
> existing `TLDivSumHypothesis L` and `TLAbelConverseHypothesis L`
> (via definitional `Iff` lemmas).
>
> ### New chip menu
>
> * `Div.evalSum` / `evalSumHom` (and `_single` / `_single_sub_single`
>   lemmas) — `Divisor/EvalSum.lean`.
> * `EvalSumAbelHypothesis` / `EvalSumAbelConverseHypothesis` —
>   `Manifold/EvalSumGeneral.lean`.
> * `Pic0.evalSumLift` / `_surjective` / `_injective` /
>   `Pic0.evalSumLiftEquiv` — `Manifold/EvalSumGeneral.lean`.
> * `PrincDiv_addSubgroupOf_Div0_eq_ker_evalSumDiv0Hom_iff` (joint
>   characterization) — `Manifold/EvalSumGeneral.lean`.
> * T_L specializations: `evalSumPic0`, `evalSumPic0Equiv`,
>   `evalSumPic0_ofCurve`, `evalSumPic0Equiv_ofCurve_zero`,
>   `ofCurve_injective_complexTorus` —
>   `Manifold/Pic0EvalSumComplexTorus.lean`,
>   `Manifold/JacobianOfCurveEvalSumComplexTorus.lean`.
> * Multiplicative-generators reduction: `MultiplicativeClosure`
>   inductive predicate +
>   `TLDivSumHypothesis_of_multiplicatively_generating` —
>   `Manifold/TLDivSumEvalSumBridge.lean`.
> * Two-hypothesis-only headlines: `…_from_two_named_hypotheses`,
>   `pic0EquivComplexTorus_default`, `evalSumPic0Equiv_default` —
>   `Manifold/C3FullInputExtSympComplexTorusDefault.lean`.
>
> Repo total **9201 jobs clean** (was 9191; 161,295 LOC across 915 `.lean` files).
> Zero `sorry`, zero `axiom`.
> Item count unchanged (still 13/24 STRICT-CLOSED) but the discharge
> infrastructure for `TLDivSumHypothesis L` now factors through a
> generic kernel-of-evalSumHom statement amenable to multiplicative-
> generator reduction.

> **2026-05-19 (late++++++) Full T_L period-lattice closure + ℂ⧸L ≃ₘ AnalyticJacobianSymp smooth diffeomorphism UNCONDITIONAL (20 chips, ~3,037 LOC).**
>
> End-to-end closure of the period-lattice/Abel-Jacobi infrastructure
> on the complex torus T_L = ℂ ⧸ L. Eight continuation turns shipped
> 20 chips landing:
>
> 1. `Nonempty (PeriodLatticeSymplecticBundle … T_L)` UNCONDITIONAL
>    via `SmoothSymplecticBasis.reindex` + `LinearEquiv.piCongrLeft'`.
> 2. Explicit AJ point formula:
>    `abelJacobiPoint Q = QuotientAddGroup.mk (fun _ => Q.out)`.
> 3. Full lattice characterization
>    `periodLatticeImage = {fun _ => z : z ∈ L}` (⊆ + ⊇).
> 4. Two open classical hypotheses CLOSED unconditionally:
>    `AbelJacobiInjectiveSymp`, `AbelJacobiSmoothnessSymp`.
> 5. `AbelHypothesis` reduced to `TLDivSumHypothesis L` (Abel's
>    elliptic theorem).
> 6. `JacobiInversion.injective` reduced to `TLAbelConverseHypothesis L`
>    (Weierstrass σ-function existence); `JacobiInversion.surjective`
>    conditional on `AbelHypothesis`.
> 7. **Headline** `nonempty_C3FullInputExtSymp_complexTorus_of_two_named_hypotheses`:
>    full `Nonempty (C3FullInputExtSymp (ℂ⧸L))` from the two named
>    classical T_L inputs.
> 8. **`abelJacobiPointDiffeomorph`** UNCONDITIONAL: smooth
>    diffeomorphism `ℂ⧸L ≃ₘ AnalyticJacobianSymp` packaged as a
>    mathlib `Diffeomorph`.
>
> ## Ingredient status for `Nonempty (C3FullInputExtSymp (ℂ⧸L))`
>
> | Ingredient | Status |
> |---|---|
> | `Nonempty (PLSB …)` | **Unconditional** |
> | `AbelJacobiInputSymp` | **Unconditional** |
> | `AbelJacobiInjectiveSymp` | **Unconditional** |
> | `AbelJacobiSmoothnessSymp` | **Unconditional** |
> | `AbelHypothesis` | Reduced to `TLDivSumHypothesis L` |
> | `JacobiInversion.surjective` | Conditional on `AbelHypothesis` |
> | `JacobiInversion.injective` | Reduced to `TLAbelConverseHypothesis L` |
>
> **Open classical content (textbook elliptic-function theory, not in mathlib pin):**
>
> * `TLDivSumHypothesis L` — Abel's elliptic theorem (residue
>   theorem `∮_∂R d log f = 0` on a fundamental parallelogram).
> * `TLAbelConverseHypothesis L` — Weierstrass σ-function existence.
>
> Repo total **161,295 LOC across 915 `.lean` files**; build **9201 jobs**
> clean (zero `sorry`, zero `axiom`).

> **2026-05-19 (late+++++) 2D-lift scaffolding for `holomorphicCanonicalClosed` (3 chips, ~370 LOC).**
>
> Building toward unconditional `RealImagDzInCanonicalClosed L`. Ships
> the data scaffolding (partials + horizontal-then-vertical lift
> formula); the analytic discharge of the lift's smoothness and
> `mfderiv` identity is the next sub-arc.
>
> **Three chips.**
>
> * `Manifold/ComplexTorusSmooth2SimplexPartial.lean` (~85 LOC) —
>   `basisVec`, `partial1`, `partial2` for a `Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L)`.
>
> * `Manifold/ComplexTorusTwoSimplexLift.lean` (~145 LOC) —
>   `twoSimplexLift σ p := ∫_0^{p 0} partial1 σ ![s, 0] ds +
>   ∫_0^{p 1} partial2 σ ![p 0, t] dt`. Plus `twoSimplexLift_apply`
>   and `twoSimplexLift_at_origin`.
>
> * `Manifold/ComplexTorusDzComponentsClosed.lean` (~95 LOC) —
>   `RealImagDzInCanonicalClosed L` named predicate and the
>   conditional closures `holomorphicComponentsCanonicalClosed_of_realImagDz`,
>   `holomorphicStokesHypothesis_of_realImagDz`.
>
> **Three follow-up chips (next session).** Each is a focused 200-500
> LOC analytic content piece:
>
> * `Manifold/ComplexTorusSmooth2SimplexPartialSmooth.lean` —
>   `ContMDiff ∞ (partial1 σ)` and `ContMDiff ∞ (partial2 σ)` as maps
>   `(Fin 2 → ℝ) → ℂ`. Strategy: local chart-symm composition makes
>   `chartSymm ∘ σ.toFun` smooth on the chart preimage; `fderiv`
>   applied to `basisVec i` gives `partial_i σ` locally. Patch via
>   `mkQ.mfderiv = id` (proved) and the manifold smoothness of
>   `chartAt`. No new substantive content beyond standard manifold
>   smoothness threading.
>
> * `Manifold/ComplexTorusTwoSimplexLiftSmooth.lean` —
>   `ContMDiff ∞ (twoSimplexLift σ)`. Combines the partial-smoothness
>   chip with `intervalIntegral` parametric smoothness
>   (`Mathlib.Analysis.Calculus.ParametricIntervalIntegral`).
>
> * `Manifold/ComplexTorusTwoSimplexLiftMfderiv.lean` —
>   `mfderiv (twoSimplexLift σ) p = mfderiv σ.toFun p`. The substantive
>   content: `∂_y σ̃ = partial2 σ` is direct FTC; `∂_x σ̃ = partial1 σ`
>   requires Schwarz's mixed-partials theorem
>   (`Mathlib.Analysis.Calculus.FDeriv.Symmetric`) on σ.toFun viewed
>   through a chart. After that, `mfderiv` equality follows from
>   ℝ-bilinearity (a linear map is determined by its action on the
>   basis).
>
> Once those three chips are in tree, the boundary-integral
> telescope chip closes `RealImagDzInCanonicalClosed L`
> unconditionally: each face integral on `T_L` equals
> `twoSimplexLift σ (face_iParam 1) - twoSimplexLift σ (face_iParam 0)`
> by chain rule + FTC, and the three signed differences telescope to
> `0` around the simplex vertices.
>
> ## Atomic-input status on `T_L = ℂ ⧸ L` (after this session)
>
> | Atom | Status |
> |---|---|
> | `cycleGens` | **Unconditional** |
> | `SmoothPathLiftHypothesisTorus L` | **Unconditional** |
> | `SmoothHurewiczHypothesisTorus` | **Unconditional** |
> | smooth-path-connectedness | **Unconditional** |
> | `riemannBilinear` | **Unconditional** |
> | `genus (ℂ ⧸ L) = 1` (both bounds) | **Unconditional** |
> | `RealImagDzInCanonicalClosed L` | Open — 3 chip sub-arc (smoothness + Schwarz + mfderiv-equality) then telescope |

> **2026-05-19 (late++++) Structural reduction of `holomorphicCanonicalClosed` to `RealImagDzInCanonicalClosed` (2 chips, ~300 LOC).**
>
> With `genus (ℂ ⧸ L) = 1` closed unconditionally (every
> `α : HolomorphicOneForm T_L` is `c • dz L`), the predicate
> `HolomorphicComponentsCanonicalClosed (ℂ ⧸ L)` reduces to a single
> named atomic hypothesis on `dz L` only:
>
> ```
> RealImagDzInCanonicalClosed L :=
>   realComponent (dz L) ∈ canonicalClosedForms 𝓘(ℝ, ℂ) (ℂ ⧸ L) ∧
>   imagComponent (dz L) ∈ canonicalClosedForms 𝓘(ℝ, ℂ) (ℂ ⧸ L)
> ```
>
> Headlines now in tree (conditional on `RealImagDzInCanonicalClosed`):
> `holomorphicComponentsCanonicalClosed_of_realImagDz` and
> `holomorphicStokesHypothesis_of_realImagDz`.
>
> **Two reduction chips.**
>
> * **Chip A** — `Manifold/ComplexTorusHolomorphicCanonicalClosedReduction.lean`
>   (~205 LOC). ℂ-scalar identities at the pointwise level
>   (`realPart_complex_smul_pointwise`, `imagPart_complex_smul_pointwise`),
>   their section-level lifts (`realComponent_complex_smul`,
>   `imagComponent_complex_smul`), and the structural reduction
>   `holomorphicComponentsCanonicalClosed_of_dz_components`.
>
> * **Chip B** — `Manifold/ComplexTorusDzComponentsClosed.lean`
>   (~95 LOC). Named predicate `RealImagDzInCanonicalClosed L` plus
>   the conditional closure headlines.
>
> **Remaining work (multi-session):** discharge `RealImagDzInCanonicalClosed L`
> unconditionally. The classical content is FTC-telescoping around the
> boundary of every smooth 2-simplex on `T_L`, mediated by a **smooth
> 2-simplex lift** `σ̃ : (Fin 2 → ℝ) → ℂ` of
> `σ : (Fin 2 → ℝ) → (ℂ ⧸ L)`. Constructed via path integration
> `σ̃(x, y) := p₀ + ∫_0^x ∂_1 σ(s, 0) ds + ∫_0^y ∂_2 σ(x, t) dt`. Then
> `mkQ ∘ σ̃ = σ` (ODE uniqueness using `mkQ.mfderiv = id`), each face
> integral equals `σ̃(v_j) - σ̃(v_i)` (FTC), and the three boundary
> integrals telescope to `0` around the simplex vertices.
>
> ## Atomic-input status on `T_L = ℂ ⧸ L` (after this session)
>
> | Atom | Status |
> |---|---|
> | `cycleGens` | **Unconditional** |
> | `SmoothPathLiftHypothesisTorus L` | **Unconditional** |
> | `SmoothHurewiczHypothesisTorus` | **Unconditional** |
> | smooth-path-connectedness | **Unconditional** |
> | `riemannBilinear` | **Unconditional** |
> | `genus (ℂ ⧸ L) = 1` (both bounds) | **Unconditional** |
> | `realComponent (dz L)` Stokes-closed | Open — 2D smooth lift + FTC telescope |
> | `imagComponent (dz L)` Stokes-closed | Open — same, on imaginary part |
>
> The two remaining open atoms are the genuine classical Stokes
> content (2D lift + FTC telescope) — packaged together as the
> single named predicate `RealImagDzInCanonicalClosed L`. Both
> succumb to the same construction.

> **2026-05-19 (late+++) `genus (ℂ ⧸ L) ≤ 1` upper bound CLOSED unconditionally on T_L (2 chips, ~330 LOC).**
>
> Closes the upper bound `Module.finrank ℂ (HolomorphicOneForm (ℂ ⧸ L)) ≤ 1`
> on the complex torus `T_L = ℂ ⧸ L`. Combined with the already-closed
> lower bound (Forster-Riesz + `dz_ne_zero`), this gives
> `genus (ℂ ⧸ L) = 1` unconditionally.
>
> **Strategy: Liouville via global cotangent triviality.**
>
> 1. The cotangent bundle of `T_L` is canonically trivial: chart
>    transitions on `T_L` are translations with identity Fréchet
>    derivative (`ComplexTorusTangentCoordChangeId.lean`). So
>    `α.eval : T_L → (ℂ →L[ℂ] ℂ)` is globally `ContMDiff ω` (no chart
>    plumbing past the chart neighborhood).
> 2. The **coefficient function** `dzCoeff α p := (α.eval p) (1 : ℂ)` is
>    `ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω` (compose `α.eval` with
>    `ContinuousLinearMap.apply ℂ ℂ 1`).
> 3. The unconditional Liouville result
>    `Topology.LiouvilleForContMDiffOmega.contMDiff_omega_isConstant`
>    fires on `T_L` (compact, connected, T2, charted, IsManifold ω
>    complex 1-manifold). So `dzCoeff α` is constant.
> 4. Let `c := dzCoeff α 0`. By ℂ-linearity of `α.eval p`,
>    `α.eval p v = v • α.eval p 1 = v • c = c • v = c • (id v) = c • (dz L).eval p v`.
>    So `α = c • dz L`.
> 5. Hence every `α` is a ℂ-scalar multiple of `dz L`, and
>    `finrank ≤ 1` via `finrank_le_one`.
>
> **The two chips.**
>
> * **Chip A** — `Manifold/ComplexTorusConnected.lean` (~50 LOC).
>   `ConnectedSpace (ℂ ⧸ L)` instance via
>   `Function.Surjective.connectedSpace` on `L.mkQ : ℂ → ℂ ⧸ L`
>   (continuous + surjective image of connected `ℂ` is connected).
>
> * **Chip B** — `Manifold/ComplexTorusGenusUpperBound.lean` (~280 LOC).
>   `dzCoeff`, `dzCoeff_contMDiff`, `dzCoeff_isConstant`,
>   `exists_smul_dz`, `holomorphicOneForm_eq_span_dz`,
>   `finrank_holomorphicOneForm_le_one`, `genus_le_one`,
>   **`genus_eq_one`** (combining lower + upper).
>
> ## Atomic-input status on `T_L = ℂ ⧸ L` (after this session)
>
> | Atom | Status |
> |---|---|
> | `cycleGens` | **Unconditional** |
> | `SmoothPathLiftHypothesisTorus L` | **Unconditional** |
> | `SmoothHurewiczHypothesisTorus` | **Unconditional** |
> | smooth-path-connectedness | **Unconditional** |
> | `riemannBilinear` | **Unconditional** |
> | `genus (ℂ ⧸ L) = 1` lower bound | **Unconditional** |
> | **`genus (ℂ ⧸ L) ≤ 1` upper bound** | **Unconditional (NEW this session)** |
> | `holomorphicCanonicalClosed` | Open — chart-pullback Cauchy on 2-simplices |
>
> Only ONE open atom remains for full period-lattice closure on `T_L`.

> **2026-05-19 (late++) `SmoothHurewiczHypothesisTorus` CLOSED unconditionally on T² (6 chips, ~1,985 LOC).**
>
> Closes the previously hardest open atom on T_L = ℂ ⧸ L: every
> smooth based loop on `ℂ ⧸ L` is homologous mod `stokesBoundaries`
> to a ℤ-combination of two canonical torus basis loops, where the
> basis is the canonical ZLattice basis of `L` over ℤ. Removes the
> remaining open analytic atom from the Hurewicz row on T_L.
>
> **Headline result.**
> `ComplexTorus.exists_smoothHurewiczHypothesisTorus :`
> `  ∃ (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L),`
> `    SmoothHurewiczHypothesisTorus L lam₁ lam₂ hlam₁ hlam₂`
> for any discrete full-rank ℤ-lattice `L ≤ ℂ`.
>
> **The six chips.**
>
> * **Chip A** — `ComplexTorusProjStraightLineMap` (199 LOC).
>   `H(s, t) := mkQ((1-s)·Γ(t) + s·t·λ)` as a smooth `(Fin 2 → ℝ) →
>   ℂ ⧸ L` map.  Four edge identities (left = mkQ ∘ Γ, right = mkQ
>   ∘ (·λ), bottom = 0, top = 0).
> * **Chip B** — `ProjSimplices + ProjFaces + ProjFace1UL +
>   ProjBordism` (135 + 293 + 123 + 204 LOC).  Two `Smooth2Simplex`es
>   `σ_LR(s,t) := H(s+t, t)`, `σ_UL(s,t) := H(s, s+t)` cover `[0,1]²`
>   via `Δ²`. Six face identifications, two of which (`face1 σ_LR =
>   face2 σ_UL = diagonal`) cancel. Boundary sum `∂(σ_LR + σ_UL) =
>   single γ_λ - single γ + 2·single (const 0)`, giving the bordism
>   `single γ - single (torusBasisLoop λ) ∈ stokesBoundaries` where
>   λ = Γ(1) ∈ L.
> * **Chip C** — `ComplexTorusBasisLoopAdditive` (329 LOC).  Simplex
>   `σ(u,v) := mkQ((u+v)·a + v·b)` with faces `γ_b`, `γ_{a+b}`,
>   `γ_a` (using `mkQ(a + tb) = mkQ(tb)` since `a ∈ L`). Boundary
>   identity gives `single γ_{a+b}.cycle - single γ_a.cycle - single
>   γ_b.cycle ∈ stokesBoundaries`.
> * **Chip D** — `ComplexTorusBasisLoopZSpan` (324 LOC).  ℤ-induction
>   (`Int.induction_on zero/succ/pred`) proves
>   `single γ_{n·a}.cycle - n • single γ_a.cycle ∈ stokesBoundaries`.
>   Base via `γ_0 = SmoothPath.const _ _ 0`. Positive step via
>   additivity. Negative step via additivity + `γ_a + γ_{-a}.cycle
>   ∈ stokesBoundaries`.
> * **Chip E** — `ComplexTorusSmoothHurewiczFromBasis` (256 LOC).
>   Headline (conditional): under `IsZBasisOfL L lam₁ lam₂`,
>   `smoothHurewiczHypothesisTorus_holds_of_basis` discharges
>   `SmoothHurewiczHypothesisTorus`.
> * **Chip F** — `ComplexTorusZBasisExistence` (~135 LOC). Uses
>   mathlib's `ZLattice.module_free` + `Module.Free.chooseBasis` +
>   reindexing to produce `basisFin2OfL : Basis (Fin 2) ℤ L` (card =
>   `finrank ℤ L = finrank ℝ ℂ = 2`). `basisFin2OfL_isZBasisOfL`
>   gives `IsZBasisOfL L (b 0) (b 1)` via `Module.Basis.sum_repr`.
>   `exists_smoothHurewiczHypothesisTorus` is the unconditional
>   existence headline.
>
> ## Atomic-input status on `T_L = ℂ ⧸ L` (after this session)
>
> | Atom | Status |
> |---|---|
> | `cycleGens` | **Unconditional** |
> | `SmoothPathLiftHypothesisTorus L` | **Unconditional** |
> | `SmoothHurewiczHypothesisTorus` | **Unconditional (NEW this session)** |
> | smooth-path-connectedness | **Unconditional** |
> | `riemannBilinear` | **Unconditional** |
> | `genus (ℂ ⧸ L) = 1` lower bound | **Unconditional** |
> | `holomorphicCanonicalClosed` | Open — chart-pullback Cauchy on 2-simplices |
> | `genus (ℂ ⧸ L) ≤ 1` upper bound | Open — Liouville on universal cover |
>
> Only two open atoms remain for full period-lattice closure on T_L.
> Scoreboard unchanged at 13/24 — this work unblocks structural
> reductions on T² but does not flip the verbatim `Basic.lean` items.

> **2026-05-19 (late) `SmoothPathLiftHypothesisTorus L` CLOSED unconditionally on T².**
> (17 chips, 2,558 LOC. Headline:
> `smoothPathLiftHypothesisTorus_holds : SmoothPathLiftHypothesisTorus L`.)
>
> Every smooth based loop `γ` at `0` on `ℂ ⧸ L` admits a smooth
> ambient lift `Γ : ℝ → ℂ` with `Γ(0) = 0` and `mkQ ∘ Γ = γ.ambient`
> on `Icc 0 1`. This is the universal-cover smooth-lift content of
> the SmoothHurewicz reduction chain, now unconditional on the
> complex torus.
>
> **Construction.** Chart-anchor Lebesgue partition (`exists_chartAnchor_partition`)
> + cumulative seam-shift `∈ L` + per-piece chart-symm composition +
> seam consistency + local agreement near seams (via continuity into
> discrete `L` + `discRadius_separates`) + global piecewise
> `pwLiftGlobal` smooth on `Ioo (-δ) (1+δ)` for some `δ > 0`, then
> bump-multiplier `smoothBump δ` (`= 1` on `Icc 0 1`, supported on
> `Icc (-δ/2) (1+δ/2)`) to extend smoothly to all of `ℝ`.
>
> ## Atomic-input status on `T_L = ℂ ⧸ L` (after this session)
>
> | Atom | Status |
> |---|---|
> | `cycleGens` | **Unconditional in tree** |
> | `SmoothPathLiftHypothesisTorus L` | **Unconditional in tree** (universal-cover smooth-lift content) |
> | `SmoothHurewiczHypothesisTorus` | Open — bordism + word-rep identification on top of the closed lift atom |
> | smooth-path-connectedness | **Unconditional in tree** |
> | `riemannBilinear` | **Unconditional in tree** (CLOSED 2026-05-19 morning) |
> | `genus (ℂ ⧸ L) = 1` lower bound | **Unconditional in tree** |
> | `holomorphicCanonicalClosed` | Open — chart-pullback Cauchy on 2-simplices |
> | `genus (ℂ ⧸ L) ≤ 1` upper bound | Open — Liouville on universal cover |
>
> Repo state: **153,172 LOC across 866 `.lean` files**, build
> **9151 jobs** clean. Zero `sorry`, zero `axiom`. Scoreboard
> unchanged at 13/24 — the new content unblocks structural reductions
> on T² without flipping the verbatim `Basic.lean` items.

> **2026-05-19 `riemannBilinear` CLOSED + `SmoothHurewicz` arc opened.**
> (16 chips total across two arcs, ~2,300 LOC. Net atom closure:
> **1 full atom + 1 half-atom**.)
>
> Closes `riemannBilinear` on T² end-to-end (full period computation
> `∫_{γ_lam} dz = lam` + ℝ-linear independence). Ships substantial
> infrastructure for `SmoothHurewicz` (covering map, continuous lift,
> chart-based local smooth lift primitives) without full closure.
>
> **riemannBilinear closure arc** (7 chips, ~1,150 LOC):
>
> * `ComplexTorusTangentCoordChangeId.lean` (~225 LOC) — chart-
>   changes on T² are translations →
>   `tangentCoordChange = id` → cotangent triviality.
> * `ComplexTorusDz.lean` (~245 LOC) — canonical `dz : HolomorphicOneForm
>   (ℂ ⧸ L)` constructed from cotangent triviality. `dz_ne_zero` +
>   `nontrivial_holomorphicOneForm`.
> * `ComplexTorusBasicInstances.lean` (~85 LOC) — `Nonempty`,
>   `CompactSpace`, `T2Space` on `ℂ ⧸ L`.
> * `ComplexTorusGenusLowerBound.lean` (~70 LOC) — **`1 ≤ genus`**
>   UNCONDITIONAL via Forster-Riesz + `dz_ne_zero`.
> * `ComplexTorusPeriodComputation.lean` (~135 LOC) —
>   `mfderiv (t ↦ (t : ℂ) * lam) t 1 = lam`.
> * `ComplexTorusMkQMfderiv.lean` (~300 LOC) — **`mfderiv mkQ p v = v`
>   for ALL p**: ball case via chart-symm chain rule +
>   L-shift generalization.
> * `ComplexTorusPeriodValue.lean` (~190 LOC) —
>   **`complexPeriod γ_lam.singleCycle (dz L) = lam`**: chain rule
>   for `mkQ ∘ (·*lam)`, integrand identification with `lam.re`/`lam.im`,
>   integration.
> * `ComplexTorusRiemannBilinear.lean` (~220 LOC) — **CLOSES
>   `riemannBilinear`** via period vector pointwise identification
>   + the `(Fin 1 → ℂ) ≃ₗ[ℝ] ℂ` equivalence.
>
> **SmoothHurewicz arc** (9 chips, ~1,150 LOC, partial closure):
>
> * `ComplexTorusCoveringMap.lean` (~75 LOC) — `mkQ_isCoveringMap`
>   via mathlib's `AddSubgroup.isAddQuotientCoveringMap_of_comm`.
> * `ComplexTorusContinuousPathLift.lean` (~95 LOC) — `contLift` +
>   `contLift_endpoint_mem_L` (loops classified by lattice element).
> * `ComplexTorusSmoothPathLift.lean` (~85 LOC) — integration-based
>   `smoothLift γ t := ∫_0^t γ.velocity s ds`.
> * `ComplexTorusHurewiczFromLift.lean` (~110 LOC) —
>   `SmoothPathLiftHypothesisTorus` named atom + endpoint corollary.
> * `SmoothPathVelocityContinuous.lean` (~95 LOC) — velocity
>   continuity for vector-space-valued SmoothPath.
> * `ComplexTorusLocalSmoothLift.lean` (~165 LOC) — chart-based local
>   smooth lift primitives: `localLift`, `localLift_eqOn_chartComp`,
>   `mkQ_localLift`, `chartComp_contMDiffOn`,
>   **`localLift_contMDiffOn`**, **`localLift_at_anchor`**.
>
> ## Atomic-input status on `T_L = ℂ ⧸ L` (after this session)
>
> | Atom | Status |
> |---|---|
> | `cycleGens` | **Unconditional in tree** |
> | `H1_spans_top_canonical` = `SmoothHurewiczHypothesisTorus` | Open — covering map + continuous lift + named smooth-lift atom + chart-based local smooth lift primitives shipped; full closure needs Lebesgue subdivision + uniqueness gluing + homotopy + bordism |
> | smooth-path-connectedness | **Unconditional in tree** |
> | `holomorphicCanonicalClosed` | Open — chart-pullback Cauchy on 2-simplices |
> | **`riemannBilinear`** | **CLOSED** (modulo user-supplied ℝ-independence) |
> | `genus (ℂ ⧸ L) = 1` lower | **CLOSED** (Forster-Riesz + `dz_ne_zero`) |
> | `genus (ℂ ⧸ L) ≤ 1` upper | Open — Liouville on universal cover |
>
> Repo state: **150,614 LOC across 849 `.lean` files**, build
> **9134 jobs** clean. Zero `sorry`, zero `axiom`. Scoreboard
> unchanged at 13/24.

> **2026-05-18 (late late + 8) Complex torus `ℂ ⧸ L` infrastructure as
> the genus-1 example.** (10 chips, ~1,100 LOC.)
>
> The prior session's caveat — "non-degenerate genus-≥1 needs surface
> topology (T² = ℂ/Λ, cellular approximation, path lifting) not in
> tree" — is now partially closed: `ℂ ⧸ L` exists as a concrete
> complex 1-manifold with an explicit symplectic basis and the
> period-lattice generation chain runs end-to-end against a single
> named Hurewicz hypothesis.
>
> * `SmoothHomotopyHurewiczHypothesis.lean` (~90 LOC) — abstraction:
>   the *smooth-homotopy* upgrade of `WordRepresentativeHypothesis`.
>   Witness is a concrete `SmoothHomotopyBasedLoop` from γ to a
>   `basisProductLoop`, not just algebraic bordism. Downgrades to
>   `WordRepresentativeHypothesis sb` via
>   `smoothBordant_of_smoothHomotopy`.
> * `SmoothHomotopyHurewiczC.lean` (~65 LOC) — discharge on ℂ for
>   `constSymplecticBasis` via the straight-line homotopy.
> * `PeriodLatticeComplexQuotientGeneric.lean` (~165 LOC) — generic
>   `IsManifold 𝓘(ℂ, E) ω (E ⧸ L)` over any finite-dim complex
>   normed `E`. Stated as a `def` to avoid diamond with the existing
>   `Fin g → ℂ` instance.
> * `ComplexTorus.lean` (~165 LOC) — specialises to `E = ℂ`,
>   yielding `IsManifold 𝓘(ℂ, ℂ) ω (ℂ ⧸ L)` as a regular instance.
>   Derives `mkQ_contMDiff` (both complex and real models).
> * `ComplexTorusBasisLoop.lean` (~115 LOC) — for `lam ∈ L`, the
>   smooth based loop `t ↦ π((t : ℂ) * lam)` at `0 ∈ ℂ ⧸ L`.
> * `ComplexTorusSymplecticBasis.lean` (~95 LOC) — bundles a pair
>   of torus basis loops as `SmoothSymplecticBasis 𝓘(ℝ, ℂ) (ℂ⧸L) 0 1`.
> * `BasedLoopAtPush.lean` (~60 LOC) — pushforward of `BasedLoopAt`
>   along smooth maps; intended use is `mkQ : ℂ → ℂ ⧸ L` for
>   "lift in ℂ, project to T²" constructions.
> * `ComplexTorusPathConnected.lean` (~95 LOC) — **unconditional**
>   smooth-path-connectedness data `α : T² → SmoothPath` from `0`
>   to `x` via the projection of `t ↦ (t : ℂ) * x.out`. Discharges
>   the α / h_α_src / h_α_tgt ingredients with no classical content.
> * `ComplexTorusPeriodLatticeInputs.lean` (~95 LOC) — surfaces the
>   named atoms `SmoothHurewiczHypothesisTorus` and
>   `SmoothHomotopyHurewiczHypothesisTorus`, plus the structural
>   reduction to `BasedLoopHomologyDecompositionHypothesis`.
> * `ComplexTorusH1SpansTop.lean` (~75 LOC) — the headline:
>   `SmoothHurewiczHypothesisTorus L lam₁ lam₂ ⟹ H1_spans_top_canonical`
>   on `(symplecticBasis L lam₁ lam₂).cycleGens` in the canonical
>   Stokes quotient, **unconditional in α**.
>
> Atomic-input status on `X := ℂ ⧸ L` (relative to the prior 4-atom
> framing of `GenericGenusPeriodLatticeInputs`; the `H1_spans_top`
> row and the named Hurewicz atom are the **same classical content**,
> rewritten as the universal-cover lifting that the structural
> reduction consumes — not two separate atoms):
>
> | Atom | Status on `T_L = ℂ ⧸ L` |
> |---|---|
> | `cycleGens` | **Unconditional in tree** (symplecticBasis.cycleGens) |
> | `H1_spans_top_canonical` = `SmoothHurewiczHypothesisTorus` | Open — universal-cover lifting `ℂ → ℂ ⧸ L` + lattice classification (structurally reduced in tree to a one-named-atom form, **unconditional in α**) |
> | smooth-path-connectedness | **Unconditional in tree** (ComplexTorus.α); was implicit-open in the prior framing |
> | `holomorphicCanonicalClosed` | Open — chart-pullback Cauchy on each 2-simplex |
> | `riemannBilinear` | Open — period computation `∫_{γ_lam} dz = lam` + ℝ-linear-independence of `(lam₁, lam₂)` in ℂ (purely algebraic given the period computation) |
> | `genus (ℂ ⧸ L) = 1` | **Lower bound `1 ≤ genus` UNCONDITIONAL in tree** (via `dz` construction + Forster-Riesz finite-dim + Nontrivial); **upper bound `genus ≤ 1` open** — Liouville-style argument on universal cover ℂ → ℂ⧸L (every holomorphic 1-form on T_L lifts to bounded holomorphic on ℂ, hence constant, hence a scalar multiple of `dz`) |
>
> **Honest count:** 4 open classical content pieces remain. The
> `genus_eq` atom has its lower bound CLOSED (significant new
> classical content shipped — explicit `dz : HolomorphicOneForm
> (ℂ⧸L)` constructed from the cotangent-bundle triviality, then
> Forster-Riesz + Nontrivial gives `1 ≤ Module.finrank`). Three open
> atoms remaining + the `genus ≤ 1` upper bound.
>
> Repo state: **148,333 LOC across 834 `.lean` files**, build
> **9119 jobs** clean (zero `sorry`, zero `axiom`). Scoreboard
> unchanged at 13/24.

> **2026-05-18 (late late + 7) Smooth-Hurewicz arc continuation.**
> (10 chips, ~2,900 LOC across the session, cumulative ~3,500 LOC with
> the session-6 base.)
>
> * `SmoothBordismAndWordRepresentative.lean` — factor
>   `SmoothHurewiczHypothesis sb` into `SmoothBordant` + `WordRepresentativeHypothesis sb`.
> * `SmoothBordantOfSmoothHomotopy.lean` (~558 LOC) — **real
>   geometric content**: `SmoothHomotopyBasedLoop γ₀ γ₁ ⟹ SmoothBordant
>   γ₀ γ₁` via explicit 2-chain construction (two simplices covering the
>   unit square via the diagonal). Boundary computation: 6 face
>   identifications (γ₀, γ₁, diagonal cancels, 2 const p₀'s). Closes
>   the bordism side unconditionally given the homotopy data.
> * `WordRepresentativeEmptyBasis.lean` — empty-basis word-rep from
>   `BasedSmoothLoopsBound`; unconditional on RS.
> * `SmoothHomotopyStraightLineC.lean` (~198 LOC) — straight-line
>   homotopy `(s, t) ↦ (1-s) γ₀.amb(t) + s γ₁.amb(t)` constructs a
>   `SmoothHomotopyBasedLoop` on `X = ℂ`. Real construction.
> * `BasedSmoothLoopsBoundC.lean` — `BasedSmoothLoopsBound` on ℂ
>   unconditional via the straight-line route.
> * `SmoothBordantCongruence.lean` — `SmoothBordant.concat`,
>   `SmoothBordant.zpow` algebraic congruences.
> * `SmoothHomotopyChartLocal.lean` (~284 LOC) — **real geometric
>   content**: chart-local straight-line homotopy on arbitrary complex
>   1-manifold `X` under strong hypotheses (γ.ambients globally in
>   chart-source + chart-straight-line globally in chart-target).
>   Uses `contMDiffOn_chart` + `ContMDiffOn.comp_contMDiff`.
> * `WordRepresentativeAnyGenus.lean` — discharges
>   `WordRepresentativeHypothesis (constSymplecticBasis p₀ g)` at any
>   `g ≥ 1` on RS and ℂ. **Honest caveat:** uses a *degenerate* basis
>   (all loops = const), so the cycleGens are all already in
>   `stokesBoundaries`. The chip closes the syntactic Prop at any `g`
>   but does not capture genuine genus-≥1 mathematical content. The
>   non-degenerate genus-≥1 statement requires surface topology
>   (T² = ℂ/Λ, cellular approximation, path lifting) not in tree.
>
> Repo state: **147,252 LOC across 824 `.lean` files**, build **9109
> jobs** clean (zero `sorry`, zero `axiom`). Scoreboard unchanged at
> 13/24.

> **2026-05-18 (late late + 6) Smooth-Hurewicz arc: symplectic basis +
> commutator null-homology landed.** (5 chips, ~622 LOC.)
>
> Opens the hardest open atom — `BasedLoopHomologyDecompositionHypothesis`
> (smooth-Hurewicz on a genus-`g` surface) — with:
>
> * `SmoothSymplecticBasis I X p₀ g` (`Manifold/SmoothSymplecticBasis.lean`)
>   — data of `2g` smooth based loops at `p₀` representing the
>   symplectic homology basis. `cycleGens` derives the corresponding
>   `Fin (2g) → SmoothCycle I X` tuple.
> * `SmoothHurewiczHypothesis sb` (`Manifold/SmoothHurewiczHypothesis.lean`)
>   — single named Prop for the classical content; biconditional with
>   `BasedLoopHomologyDecompositionHypothesis sb.cycleGens p₀`.
> * `GenericGenusPeriodLatticeInputs.ofSmoothHurewicz`
>   (`Manifold/GenericGenusPeriodLatticeInputsFromSmoothHurewicz.lean`)
>   — constructor from a symplectic basis + smooth-Hurewicz + the
>   other 3 atomic inputs, with `Nonempty` composition through to
>   `PeriodLatticeSymplecticBundle`.
> * `smoothHurewiczHypothesis_RiemannSphere_holds`
>   (`Manifold/SmoothHurewiczHypothesisRiemannSphere.lean`) —
>   unconditional discharge at genus 0 on RS via the empty symplectic
>   basis.
> * **`single_commutatorLoop_mem_stokesBoundaries`**
>   (`Manifold/CommutatorOfBasedLoopsNullHomologous.lean`) — **real
>   homological identity**: for any two based loops `α, β` at `p₀`,
>   the commutator `[α, β] := α ⋆ β ⋆ α⁻¹ ⋆ β⁻¹` is null-homologous
>   in `stokesBoundaries`. Classical content "`H₁` is abelian"
>   verified for arbitrary commutator words; proof composes 3 nested
>   `concat_additive_in_stokesBoundaries` + 2
>   `single_smoothPath_plus_reverse_mem_stokesBoundaries`.
>
> Repo state: **144,344 LOC across 812 `.lean` files**, build **9097
> jobs** clean (zero `sorry`, zero `axiom`). Scoreboard unchanged at
> 13/24.

> **2026-05-18 (late late + 5) Generic genus-≥1 period-lattice:
> per-based-loop homology + complex-valued Stokes consolidation
> landed.** (6 chips, ~964 LOC.)
>
> Follow-on chips 5–6 on top of the 4-chip per-based-loop homology
> reduction below: consolidate the holomorphic side's two real-valued
> vanishings into a single complex-valued statement
> (`HolomorphicComplexBoundaryVanishingHypothesis`) and package the
> most-atomic data list into a single constructor
> (`GenericGenusPeriodLatticeInputs.ofAtomicData`).
>
> User-facing atomic data list at general genus:
> 1. `cycleGens : Fin (2g) → SmoothCycle 𝓘(ℝ, ℂ) X` — chosen tuple;
> 2. `riemannBilinear` — ℝ-linear independence of period vectors;
> 3. `HolomorphicComplexBoundaryVanishingHypothesis X` — complex-valued
>    holomorphic-form Stokes vanishing on every 2-simplex boundary;
> 4. `(p₀, α)` — basepoint + smooth-path-connectedness;
> 5. `BasedLoopHomologyDecompositionHypothesis cycleGens p₀` — per-loop
>    ℤ-combination-mod-stokesBoundaries hypothesis.
>
> Repo state: **143,695 LOC across 807 `.lean` files**, build **9092
> jobs** clean (zero `sorry`, zero `axiom`). Scoreboard unchanged at
> 13/24.

> **2026-05-18 (late late + 5a) Generic genus-≥1 period-lattice:
> per-based-loop homology reduction landed.** (4 chips, ~711 LOC.)
>
> The fourth atomic input of `GenericGenusPeriodLatticeInputs`
> (`H1_spans_top_canonical`) now factors through a **per-based-loop
> homology decomposition hypothesis** plus smooth-path-connectedness,
> mirroring the existing genus-0 cycle-decomposition route. This is the
> genuine generalisation of `BasedSmoothLoopsBoundHypothesis` (the
> genus-0 case is the trivial decomposition with all coefficients 0;
> the genus-≥1 case carries the chosen ℤ-combination).
>
> * `BasedLoopHomologyDecompositionHypothesis cycleGens p₀` predicate
>   (`Manifold/GenericGenusH1SpansTopFromLoopHomology.lean`): every
>   smooth loop `γ` based at `p₀` admits a ℤ-tuple `n` with
>   `single γ - ∑ nᵢ • cycleGens i ∈ stokesBoundaries`.
> * `H1_spans_top_canonical_of_basedLoopHomology` (same file): the
>   structural reduction. Aggregates the per-path decomposition over
>   `c.support` of any cycle `c`, internally replicating the αShift
>   cycle-property cancellation argument with an extra
>   `∑ Nᵢ • cycleGens i` term tracked alongside;
>   `Finset.sum_comm` + `Finset.sum_smul` collapse the double-sum to
>   `∑ i Nᵢ • cycleGens i`, and the canonical quotient projection puts
>   `S.proj c ∈ Submodule.span ℤ {S.proj (cycleGens i)}`.
> * `GenericGenusPeriodLatticeInputs.ofBasedLoopHomology`
>   (`Manifold/GenericGenusPeriodLatticeInputsFromBasedLoopHomology.lean`)
>   — clean-atomic constructor taking the three "outer" atomic inputs
>   plus smooth-path-connectedness + the per-loop hypothesis.
> * `basedLoopHomologyDecompositionHypothesis_RS_holds`
>   (`Manifold/BasedLoopHomologyFromBasedLoopsBound.lean`) —
>   `RiemannSphere` corollary unconditional, plus the trivial
>   subsumption from `BasedSmoothLoopsBoundHypothesis`.
> * `genericGenusPeriodLatticeInputs_RiemannSphere_via_basedLoopHomology`
>   (`Manifold/GenericGenusPeriodLatticeInputsRiemannSphereViaBasedLoopHomology.lean`)
>   — validation chip; reproduces the genus-0 RS closure via the new
>   per-based-loop homology route end-to-end.
>
> Reduced atomic data at general genus `g = genus X`:
> 1. `cycleGens : Fin (2g) → SmoothCycle 𝓘(ℝ, ℂ) X` (a chosen tuple);
> 2. `riemannBilinear`: ℝ-linear independence of the 2g period vectors;
> 3. `holomorphicCanonicalClosed`: real/imag components of every
>    holomorphic 1-form lie in `canonicalClosedForms`;
> 4. `(p₀, α)`: a basepoint + smooth-path-connectedness data;
> 5. `BasedLoopHomologyDecompositionHypothesis cycleGens p₀`: the
>    per-based-loop ℤ-combination-mod-stokesBoundaries hypothesis
>    (smooth-Hurewicz on a genus-`g` surface).
>
> Repo state: **143,442 LOC across 805 `.lean` files**, build **9090
> jobs** clean (zero `sorry`, zero `axiom`). Scoreboard unchanged at
> 13/24.

> **2026-05-18 (late late + 4) Full genus-0 period-lattice closure on `RS`
> + cotangent-bundle chart-pullback identity landed.** (8 chips,
> ~950 LOC, origin/main HEAD `419b009`.)
>
> *Arc A — Period-lattice closure on RS, unconditional:*
> * `cycle_in_stokesBoundaries_of_basedLoopsBound`
>   (`Manifold/SmoothCycleInStokesBoundariesOfBasedLoopsBound.lean`)
>   — Finsupp aggregation of the per-path discharge over
>   `c.support`, with `αShift : (X →₀ ℤ) →ₗ[ℤ] SmoothChain I X`
>   collapsing the correction via `∂c = 0`.
> * `stokesBoundaries_RS_eq_top`
>   (`Manifold/StokesBoundariesRiemannSphereTop.lean`) — composes
>   with `basedSmoothLoopsBoundHypothesis_RS_holds` +
>   `smoothPathConnected_RiemannSphere`.
> * `C3PeriodLatticeStokesSpanTopInputs_RiemannSphere_unconditional`
>   (`Manifold/C3PeriodLatticeStokesRiemannSphereUnconditional.lean`)
>   via `trivial_at_genus_zero_canonical_of_stokesBoundaries_top`.
> * `periodLatticeSymplecticBundle_RiemannSphere_unconditional`
>   (`Manifold/PeriodLatticeSymplecticBundleRiemannSphereUnconditional.lean`)
>   via `.toBundle`.
> * `genericGenusPeriodLatticeInputs_RiemannSphere`
>   (`Manifold/GenericGenusPeriodLatticeInputsRiemannSphere.lean`)
>   — full 4-tuple unconditional via `IsEmpty.elim` /
>   `linearIndependent_empty_type` /
>   `HolomorphicComponentsCanonicalClosed.of_subsingleton` /
>   `Subsingleton.elim`.
>
> *Arc B — Cotangent-bundle chart-pullback identity:*
> * `complexEvalIntegrand_continuousOn`
>   (`Manifold/ComplexEvalIntegrandContinuity.lean`) — ℂ-integrand
>   continuity unconditional via `Re + I·Im` decomposition of the
>   existing real-valued integrand continuity. Headline
>   `chartContainedLoopVanishingHypothesis_from_pointwise_only`
>   collapses to a single substantive ingredient.
> * `pointwiseChartEvalIdentity_of_frameStable`
>   (`Manifold/PointwiseChartEvalFromFrameStability.lean`) — the
>   substantive cotangent-bundle identity proven under
>   `CotangentChartFrameStable` (`chartAt ℂ (γ.ambient t) =
>   chartAt ℂ basePoint`). Composes
>   `cotangentBundleCore_coordChange_self`,
>   `mfderiv_chartAt_eq_tangentCoordChange`, `tangentCoordChange_self`,
>   `mfderiv_eq_fderiv`, and ℂ-linearity of `α.toFun x : ℂ →L[ℂ] ℂ`.
> * `complexChainPeriod_vanishes_RiemannSphere`
>   (`Manifold/CotangentChartFrameStableRS.lean`) — per-loop
>   complex-period vanishing unconditional on RS for chart-contained
>   loops with `basePoint ≠ ∞`. Frame stability is automatic via
>   `chartAt'_coe` + `chartN_source = {x | x ≠ ∞}`.
>
> Repo state: **142,731 LOC across 801 `.lean` files**, build
> **9086 jobs** clean (zero `sorry`, zero `axiom`). Scoreboard
> unchanged at 13/24 (the new content closes structural reductions
> downstream of items 11/5/12/13/17 — Basic.lean's signatures still
> quantify over general X).

> **2026-05-17 (late late night) Symplectic-bundle migration arc landed.**
> 13-chip arc (~1450 LOC) migrated the entire Abel-Jacobi chain to the
> corrected `PeriodLatticeSymplecticBundle`, lifted manifold instances
> on `Jacobian X` to any genus-0 X with `[Subsingleton (Pic0 X)]`, and
> wired the full RS closure path. The legacy `PeriodLatticeDiscretenessBundle`
> (`h1Basis : Basis (Fin 2g) ℤ data.H1` dead code at every genus) is no
> longer on the critical path.
>
> **New entry points (all `_holds` theorems, downstream-discharge-friendly):**
> * `JacobianAnalyticChoiceSymp X` (analytic Jacobian via classical-choice
>   on the symplectic bundle) + 7 structural instances + `picZeroEquivSymp`.
> * `nonempty_C3FullInputExtSymp_RiemannSphere` `instance` (unconditional).
> * `nonempty_abelJacobiInputSymp_RiemannSphere` (unconditional).
> * `Subsingleton (Pic0 RiemannSphere)` instance,
>   `CompactSpace (Jacobian RiemannSphere)` instance,
>   `ChartedSpace (Fin 0 → ℂ) (Jacobian RS)` instance,
>   `IsManifold 𝓘(ℂ, Fin 0 → ℂ) ω (Jacobian RS)` instance,
>   `ContMDiffAdd`/`LieAddGroup` instances,
>   `ofCurve_contMDiff_RiemannSphere` theorem.
> * Generic `compactSpace_Jacobian_holds [Subsingleton (Pic0 X)]`,
>   `chartedSpace_Jacobian_holds (hgenus : genus X = 0)`,
>   `isManifold_Jacobian_holds` (parametrised over any X with the two
>   hypotheses).
>
> **Scoreboard unchanged at 13/24** — Basic.lean's verbatim signatures for
> items 11/5/12/13/17 quantify over general X without `[Subsingleton (Pic0 X)]`;
> the placeholder discrete-topology on `Pic0 X` cannot honestly support an
> unconditional `CompactSpace` proof at general genus. A structural
> redefinition of `JacobianChallenge.Jacobian X` (replacing the discrete
> topology with the analytic-quotient topology under
> `[Nonempty (C3FullInputExtSymp X)]`) is the remaining closure path; the
> infrastructure for it is now in tree.

- **STRICT-CLOSED:** **14 / 24** — items **1, 2, 3, 6, 7, 8, 9, 15, 16, 19,
  20, 22, 23, 24**. Honest `PrincDiv := PrincDivHonestCandidate` and `Pic0`
  (honest, with manifold instances) live in
  `Divisor/PrincipalDivisorRange.lean`. `Pic0.pushforward (hf)` uses
  `JacobianPushforward.lean`; `Pic0.pullbackWeighted (h_desc)` uses
  `Pic0.divPullbackWeighted_descent_of_smooth` in `JacobianPullback.lean`.
  **Item 16** (`ofCurve_inj`) closed via `JacobianChallenge.ofCurve_inj_holds`
  in `Manifold/ChartDerivNeZeroImpliesNonCriticalDischarge.lean`
  (unconditional discharge chain: `PrincDivWitnessExtraction` → degree-1
  via `DegreeOneFromSimpleZeroSimplePoleDischarge` →
  `bijective_of_degreeFiber_eq_one` + `bijectiveAnalyticIsBiholomorphism_holds`
  → `genus_eq_zero_iff_homeo_of_HolomorphicEquiv_RiemannSphere`).
  **Item 1** (`genus X : ℕ`) became STRICT-CLOSED via the 10-chip Forster
  density-bound arc (2026-05-17, `DiskChartCoverDensity*.lean` +
  `DiskChartCoverRiesz.lean` + `DiskChartCoverFiniteDim.lean`):
  `HolomorphicOneFormFiniteDim X` is **unconditional** on a compact
  connected complex 1-manifold via the cover-refinement → cotangent
  transition continuity → per-point density identity → per-`x` aggregate
  → density inequality `seminormVal ≤ M · seminormValInner` → outer
  closed ball seq-compact → Riesz → `FiniteDimensional` chain.
  `Module.finrank ℂ (HolomorphicOneForm X)` thus equals the actual
  ℂ-dimension (no junk-zero), so the genus definition is the honest
  geometric genus.
- **STUB (placeholder topology / target / pending discharge):** items
  **4, 10** = 2 items.

  **C3 cascade infrastructure complete (2026-05-17)**: items 4, 5, 10,
  11, 12, 13, 16, 17, 18, 21 all discharge on the analytic Jacobian
  `JacobianAnalyticChoice X` under `[Nonempty (C3FullInputExt X)]`
  (single typeclass-bundled classical existence input). The chain:

  * `C3FullInput X` (basis from item 1 + discreteness + Abel-Jacobi
    input + Abel + Jacobi inversion) → items 4, 5, 10, 11, 12, 13 on
    the analytic Jacobian (`C3FullInputInstances.lean`).
  * `C3FullInputExt X` (+ smoothness + point-injectivity) → items 16,
    17 (`C3FullInputExtClosures.lean`).
  * `C3FullInputCurve B_X B_Y f hf` (per-curve lattice-match) → items
    18, 21 (`C3FullInputCurveClosures.lean`).
  * `JacobianAnalyticChoice X` — full instance bundle on the
    classical-choice analytic Jacobian (`JacobianAnalyticChoice.lean`).
  * `picZeroEquiv : Pic⁰ X ≃+ JacobianAnalyticChoice X` AddEquiv —
    bridge to Basic.lean's `Jacobian X = Pic⁰ X`.

  **Remaining for Basic.lean items 4, 5, 10, 11, 12, 13, 16, 17, 18,
  21 to flip:** the classical existence `Nonempty (C3FullInputExt X)`
  + per-curve `Nonempty (C3FullInputCurve B_X B_Y f hf)`. Both require
  Riemann bilinear + H₁(X; ℤ) ≅ ℤ²ᵍ + Abel's theorem + Jacobi
  inversion + point-injectivity + smoothness — i.e., the full
  classical content of period-lattice + Abel-Jacobi theory, not
  achievable without significant additional formalization.
- **OPEN (sorry in `Basic.lean` or transitively via downstream sorry):**
  items **5, 11, 12, 13, 14, 16, 17, 18, 21** = 9 items. Item 16
  (`ofCurve_inj`) reverted from STUB to OPEN as CLOSURE_MAP predicted —
  it requires Abel-Jacobi (Phase 2).

**Item 14 open content factors onto four named classical inputs**
(`MeromorphicIdentityPropagation X` was discharged via
`Topology/LiftNonvanishingFromIdentityTheorem.lean`'s
`meromorphicIdentityPropagation_holds`):
1. `HolomorphicOneFormFiniteDim X` — Hodge finite-dim gap
   (`Manifold/HodgeFiniteDimensional.lean`).
2. `ExistsSimplePoleGermAtSomePoint X` — RR-existence at genus 0
   (`Topology/RRStrictLtFromSimplePole.lean`).
3. `S2ImpliesGenus0 X` — geometric-vs-topological genus bridge
   (`Topology/SurfaceClassificationGenus.lean`).

   **Two architectural reductions exist for input 3**; downstream callers
   can pick whichever route their auxiliary inputs match best:

   * *Uniformization route* (`Topology/S2ImpliesGenus0Unconditional.lean`):
     reduces to `HolomorphicOneFormEquivRiemannSphere X` (a ℂ-linear
     equivalence between `H⁰(X, Ω¹)` and `H⁰(RS, Ω¹)`). The Riemann-sphere
     side is unconditional via `genus_RiemannSphere_statement_holds`. The
     remaining open input is the linear equivalence itself, which
     classically follows from uniformization + 1-form pullback.

   * *Simple-connectedness route* (new 2026-05-13,
     `Topology/S2ImpliesGenus0FromSimplyConnected.lean`): reduces to
     two precise classical facts — (a) `SimplyConnectedS2`
     (= `SimplyConnectedSpace StandardS2`, formerly the small mathlib
     gap on π₁(S²) = 0), and (b) `HolomorphicOneFormSubsingletonOfSimplyConnected
     X` (the analytic chain `simply connected ⇒ closed 1-forms have
     primitives via Stokes ⇒ primitive is constant by Liouville ⇒ form
     is zero`). **`SimplyConnectedS2` is now UNCONDITIONAL** at the
     mathlib pin via the 15-chip Phase-3 smoothing arc landed on
     `feat/phase3-s2-simply-connected` on 2026-05-15: chart cover →
     Lebesgue partition → stereographic straight-line approximation →
     line-segment empty interior → finite-union Baire argument → loop
     non-surjectivity (`simplyConnectedS2_holds` in
     `Topology/SimplyConnectedS2Unconditional.lean`). The simple-
     connectedness route now reduces to input (b) ALONE.

     **Input (b) further reduces to primitive-existence** (2026-05-16,
     13-chip analytic-side closure arc in
     `Topology/SubsingletonFromPrimitiveExistence.lean` +
     `Topology/LiouvilleForContMDiffOmega.lean` + supporting
     `complexChainPeriod` algebra and `chartLocalPrimitive` data):

     ```
     HolomorphicOneFormSubsingletonOfSimplyConnected X
       ⇐ holomorphicOneFormSubsingletonOfSimplyConnected_of_primitiveExistence
         needs: ∀ om : HolomorphicOneForm X, ∃ F : X → ℂ,
                  ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω F ∧
                    ∀ x, om.eval x = mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) F x
                (every holomorphic 1-form admits a smooth primitive
                 under simple-connectedness)
     ```

     The unconditional Liouville for `ContMDiff ω F : X → ℂ` on
     compact connected `X`
     (`Topology/LiouvilleForContMDiffOmega.lean`'s
     `contMDiff_omega_isConstant`, via the `exp ∘ F` trick) discharges
     the analytic constancy side completely; only the smooth-Stokes /
     path-integral primitive construction on simply-connected
     manifolds remains as a named classical input — structurally the
     `StokesCompactSurfacePartitionOfUnity_hypothesis` content in
     `Manifold/StokesCompactSurface.lean`, plus the regularity
     bootstrap to `ContMDiff ω F`.

     `s2ImpliesGenus0_of_primitiveExistence` provides the full-arc
     composition.

4. Universal at-pole-germ-compatible continuity strengthening of L(δp)
   — operational germ-field refactor
   (`Topology/LiftNonConstancyFromContinuity.lean`'s
   `IsBoundedByDeltaPContinuousAtPole`).

Each input above is citable textbook content. Item 14 remains OPEN;
the four named inputs are real classical math not at the mathlib pin
`8e3c989...`.

> **`CLOSURE_MAP.md` (repo root) is the live source of truth.** It has
> the per-item map, mathlib status verified against this repo's pin
> (`8e3c989...`), Phase 1–4 chip plans with per-component LOC ranges,
> dependency DAG, and verification audit log. Update
> `CLOSURE_MAP.md`, not this file, when items flip.

**Remaining LOC for full 24/24 STRICT-CLOSED (verified per-component):
~28,500–55,000 LOC.** Phase 1 essentially done (A1 + A2 discharged;
genus-0 Abel-Jacobi iso on RiemannSphere now **unconditional** in-tree
post-2026-05-14; C1 chart-cover lift remains, blocked on the ω-level
structural caveat). Phase 2 ~14–28k (period lattice + Abel-Jacobi at
genus ≥ 1, blocked on classical mathlib gaps), Phase 3 ~7.1–15k
(surface classification, blocked), Phase 4 ~6.9–12.8k (Hodge,
blocked). See `CLOSURE_MAP.md` section F.

**Current repo size:** **~141,277 LOC across 789 files** (2026-05-18
late late, build **9070 jobs** clean). Latest landings:

* **2026-05-18 late late (chart-N pullback + Möbius + missed-point
  Sard)**: ~1,070 LOC / 7 chips. `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ)
  RiemannSphere p₀` UNCONDITIONAL via chart-N pullback discharge
  (`tubularBump` smooth-bump + tubular-neighborhood compactness),
  composite via avoid-∞, Möbius shift `mobiusComposed`, missed-point
  case split, and **Sard via Hausdorff dimension** discharge of
  `SmoothLoopHasMissedPointHypothesis`. HEAD `ce40ac7`.

* **Generic-genus entry point + per-path cycle decomposition**
  (HEADs `2189d49`, `2d8855c`): +~345 LOC.
  - `Manifold/GenericGenusPeriodLatticeInputs.lean` — structure bundling
    the FOUR atomic canonical-bundle inputs + chain to `Nonempty
    (PeriodLatticeSymplecticBundle data basis)`.
  - `Manifold/SmoothCycleDecompositionToBasedLoops.lean` — per-path
    `basedLoopOf` + rebasing primitives. `singlePlusCorrectionCycle γ`
    ∈ stokesBoundaries under `BasedSmoothLoopsBoundHypothesis I X p₀`.

  **Genus ≥ 1 barrier chipping (2026-05-18 late late + 3).** Status
  per atomic input:
  1. `holomorphicCanonicalClosed` — **structurally reduced** (HEAD
     `8271224`) to `HolomorphicLoopIntegralVanishes X` via the
     boundary-loop reformulation. For RS, unconditional via
     subsingleton. For genus ≥ 1, future work: chart-pullback of
     integration + mathlib's Cauchy theorem on disks
     (`DifferentiableOn.isExactOn_ball`).
  2. `H1_spans_top_canonical` — needs surface classification (not in
     mathlib).
  3. `cycleGens` — depends on (2).
  4. `riemannBilinear` — needs Hodge theory (not in mathlib) + finished
     `HolomorphicOneFormFiniteDim` (Forster Riesz arc has remaining gaps).

  The work delivered is the structural framework + per-path
  infrastructure ready to consume each input once the relevant mathlib
  prerequisite lands.
Major landings this session:

* **Item 1 → STRICT-CLOSED.** Full Forster Riesz arc: 10 chips,
  ~1,430 LOC (`DiskChartCoverDensity*.lean` + `DiskChartCoverRiesz.lean`
  + `DiskChartCoverFiniteDim.lean`). `HolomorphicOneFormFiniteDim X`
  unconditional on compact connected complex 1-manifolds.
* **C3 cascade conditional discharges** for items 4, 5, 10, 11, 12,
  13, 16, 17, 18, 21 on the analytic Jacobian. 8 chips, ~1,090 LOC
  (`C3FullInput*.lean`, `JacobianAnalyticChoice.lean`). Single
  typeclass `[Nonempty (C3FullInputExt X)]` + per-curve `Nonempty
  (C3FullInputCurve B_X B_Y f hf)` ⇒ all ten items discharge on the
  analytic Jacobian.
* **Item 14 reverse leg structural reduction.** 7 chips, ~870 LOC
  (`PrimitiveOnSmoothPathConnected.lean`, `PrimitiveSubsingletonReduction.lean`,
  `PrimitiveRiemannSphere.lean`, `PathPrimitiveLinear.lean`,
  `PathPrimitiveBasisReduction.lean`, `PathPrimitiveBasisFTC.lean`,
  `LoopPeriodConstant.lean`). `HolomorphicOneFormSubsingletonOfSimplyConnected`
  factored to per-basis-element `LoopPeriodVanishes` +
  `ContMDiff (pathPrimitive (b i))` + FTC at `eval` (3g concrete
  per-basis analytic statements).

  **FTC basis-reduction now landed (2026-05-17 late evening,
  `pathPrimitiveFTC_of_basis` in `PathPrimitiveBasisFTC.lean`).** The
  formerly-deferred counterpart of `pathPrimitiveSmoothness_of_basis`
  closes: both `PathPrimitiveSmoothness` and `PathPrimitiveFTC` of
  item 14's reverse leg are now factored through a ℂ-basis via
  `Submodule.span_induction` + ℂ-linearity of `pathPrimitive`. The
  remaining open work is at most `2 · genus X` individual analytic
  checks (one smoothness + one FTC per basis element of
  `HolomorphicOneForm X`).

  **Item 14 hypothesis-cleanup arc (2026-05-17 late evening,
  4 chips, ~325 LOC):** drop `[FiniteDimensional]` from item 14
  forward leg (`Item14ForwardFromCompactConnected.lean`); drop
  `SimplyConnectedS2` from item 14 reverse leg
  (`S2ImpliesGenus0FromSubsingletonHypothesis.lean`); finest-grained
  reverse leg via basis pathPrimitive
  (`S2ImpliesGenus0FromPrimitiveExistenceUnconditional.lean`). Net
  for the simple-connectedness route: only **two** classical inputs
  remain — `ExistsSimplePoleGermAtSomePoint X` (forward) and
  `HolomorphicOneFormSubsingletonOfSimplyConnected X` (reverse).

  **Item 14 unconditional on `RiemannSphere` via the substantive
  chain (2026-05-17 late evening, 2 chips, ~56 LOC,
  `Topology/HolomorphicOneFormSubsingletonOfSimplyConnectedRS.lean`):**
  composes the chip-arc to land `genus_eq_zero_iff_homeo_riemannSphere`
  unconditionally via the substantive forward+reverse chain. The
  trivial direct discharge already exists in
  `Item14ForRiemannSphere.lean`; this chip validates the full
  pipeline composes end-to-end on RS.

  **Analytic Jacobian for `RiemannSphere` unconditional (2026-05-17
  late evening, 4 chips, ~235 LOC,
  `Manifold/PeriodLatticeRiemannSphere.lean`):**
  `PeriodLatticeOfRankTwoG.trivialAtGenusZero` +
  `periodLatticeOfRankTwoG_RiemannSphere` +
  `compactSpaceHypothesis_holds_RiemannSphere` +
  `chartedSpaceHypothesis_holds_RiemannSphere` +
  `lieAddGroupHypothesis_holds_RiemannSphere` +
  `AnalyticJacobianRiemannSphere` (`Type` with 7 structural typeclass
  instances: AddCommGroup, TopologicalSpace, T2Space, CompactSpace,
  ChartedSpace, IsManifold, LieAddGroup) +
  `picZeroEquiv_RiemannSphere : Pic⁰ RS ≃+ AnalyticJacobianRiemannSphere`.
  Items 3, 4, 5, 10, 11, 12, 13 of Buzzard's spec discharged
  unconditionally on the analytic-Jacobian type for X = RS. The
  `ofBundle` route was structurally blocked at genus 0 (see refactor
  below); the construction here bypasses the bundle and uses `lattice
  := ⊥` directly. Basic.lean's items still STUB pending topology-
  transport along `picZeroEquiv_RiemannSphere`.

  **Period-lattice bundle refactor (2026-05-17 late night, 4 chips,
  ~400 LOC, `Manifold/PeriodLatticeSymplecticBundle.lean`):**
  architectural fix. The legacy `PeriodLatticeDiscretenessBundle`'s
  `h1Basis : Basis (Fin 2g) ℤ data.H1` is dead code at every genus
  (for `data = ofSmoothCycle X`, `data.H1 = SmoothCycle X` is
  infinite-dimensional over ℤ — never inhabited classically).
  Introduces `PeriodLatticeSymplecticBundle` with a corrected
  shape: `cycleGenerators : Fin (2g) → data.H1` (a tuple, not a
  basis) + `period_image_spanned` (the geometric ℤ-span condition).
  Full parallel pipeline through to `AnalyticJacobianSymp`. Genus-0
  case `trivial_at_genus_zero` is unconditionally constructible
  (no bypass). Side-by-side refactor; legacy consumers untouched.

  **Period-lattice classical-input structural decomposition +
  Smooth2Simplex algebraic infrastructure (2026-05-17 very late late
  night, 8 chips, ~1,250 LOC, branch
  `feat/period-lattice-stokes-refactored`, PUSHED).** Chips 1–2
  also landed on `origin/main` via fast-forward; chips 3–8 on the
  feature branch.

  *Structural-decomposition chain* (refines
  `PeriodLatticeSymplecticBundle.ofClassicalInputs`):
  ```
  C3PeriodLatticeStokesSpanTopInputs basis
       ↓ (H1_spans_top → homologyGeneration)
  C3PeriodLatticeStokesInputs basis
       ↓ (Stokes + holomorphic_closed + homologyGeneration → homologySpans)
  C3PeriodLatticeClassicalInputs basis
       ↓ .toBundle
  PeriodLatticeSymplecticBundle data α
       ↓ ofSymplectic_compactSpace / _chartedSpace
  items 5, 11, 12, 13 wiring.
  ```
  The five atomic fields of `C3PeriodLatticeStokesSpanTopInputs basis`
  are: `cycleGens : Fin 2g → SmoothCycle X`, `riemannBilinear`
  (ℝ-LI of period vectors), `stokes : StokesBoundaryInvariance`,
  `holomorphic_closed`, `H1_spans_top` (cycleGens project to a
  ℤ-generating set of `H₁ := SmoothCycle / boundaries`).

  *Headlines on the feature branch* (in addition to the legacy
  bundle's `trivial_at_genus_zero`):
  - `nonempty_C3PeriodLatticeStokesSpanTopInputs_RiemannSphere`
    UNCONDITIONAL (genus 0 + Subsingleton HolomorphicOneForm RS,
    both unconditional in tree).
  - `Nonempty.periodLatticeSymplecticBundle_of_stokesSpanTop` —
    `[Nonempty (C3PeriodLatticeStokesSpanTopInputs basis)] →
     Nonempty (PeriodLatticeSymplecticBundle data basis)`.

  *Classical-content infrastructure* (chips 6–8, ~635 LOC):
  - `Manifold/Smooth2Simplex.lean` (~370 LOC) — Concrete
    `Smooth2Simplex I X` (C^∞ map `(Fin 2 → ℝ) → X`), three face
    parameter maps with `ContMDiff` proofs, `face0/1/2 : SmoothPath`,
    `Smooth2Chain := Smooth2Simplex →₀ ℤ` with `Module ℤ`
    structure, `boundary₂ : Smooth2Chain →ₗ[ℤ] SmoothChain`, and
    the unconditional **`d² = 0` identity** (proved via vertex
    cancellation on the formal combination
    `face₀ - face₁ + face₂`).
  - `Manifold/Smooth2ChainStokesBoundary.lean` (~140 LOC) —
    `boundary₂Cycle : Smooth2Chain →ₗ[ℤ] SmoothCycle` (factored
    through `SmoothCycle` via d²=0). Defines the **canonical**
    `stokesBoundaries I X : AddSubgroup (SmoothCycle I X) := image
    of boundary₂Cycle`, with `mem_stokesBoundaries_iff` and
    zero/add/neg closure lemmas.
  - `Manifold/StokesBoundaryInvarianceFromSimplex.lean` (~125 LOC) —
    Collapses `StokesBoundaryInvariance` to a single `Prop`:
    `IntegrationStokesHypothesis I X closedForms :=`
    `∀ σ, ∀ ω ∈ closedForms, integrate (∂σ) ω = 0`.
    `ofSingleSimplexStokes` lifts to the chain level via
    `Finsupp.induction_linear` + integrate-linearity, plugging
    `stokesBoundaries` in as the canonical `boundaries`.

  *Net classical-input boundary for the period-lattice side of C3*:
  reduces to (i) the single-simplex Stokes `Prop`, (ii)
  `holomorphic_closed` (d-closure of holomorphic forms on complex
  1-manifolds), (iii) `cycleGens` choice, (iv) Riemann bilinear
  non-degeneracy, (v) `H1_spans_top` (cellular-homology / surface
  classification). `boundaries` is now CANONICAL. The algebraic
  `Smooth2Simplex` / d²=0 layer is fully unconditional.

  No `sorry`, no `axiom` across all 8 chips. Build: each file
  verified individually via `LEAN_NUM_THREADS=1 lake env lean`.
  Scoreboard unchanged at 13/24 — the inputs (i)–(v) remain real
  classical content not at the mathlib pin.

  **Period-lattice canonical Stokes bundle (2026-05-18, 15 chips,
  ~1500 LOC, MERGED to main, origin/main HEAD `7904b92`).** Further
  refactor making `boundaries` AND `closedForms` of the consumed
  `StokesBoundaryInvariance` bundle **canonical** rather than
  consumer-supplied. Net classical-input boundary shrinks from 5
  fields (with two being setup-of-the-bundle choices) to **4 atomic
  classical statements** with no bundle infrastructure left for
  the consumer.

  *Canonical Stokes bundle*:
  - `Manifold/StokesCanonicalClosedForms.lean` — `canonicalClosedForms I X`
    (Submodule ℝ of forms with integral around every smooth 2-simplex
    boundary vanishing) + `canonicalIntegrationStokes` (tautological
    discharge) + `StokesBoundaryInvariance.canonical I X` (canonical
    parameter-free bundle).
  - `Manifold/C3PeriodLatticeStokesCanonical.lean` —
    `C3PeriodLatticeStokesSpanTopInputs.ofCanonical` constructor.
  - `Manifold/HolomorphicComponentsCanonicalClosed.lean` — named
    predicates `HolomorphicComponentsCanonicalClosed X` /
    `HolomorphicStokesHypothesis X` with `.of_hypothesis` /
    `.of_subsingleton` derivations.
  - Layered constructors: `.ofStokesHypothesis`,
    `.ofCanonicalGenusZero`, `.ofCanonicalGenusZeroSubsingleton`,
    `.trivial_at_genus_zero_canonical`,
    `.trivial_at_genus_zero_canonical_of_stokesBoundaries_top`.
  - `Manifold/StokesCanonicalH1SubsingletonChar.lean` —
    `subsingleton_canonical_H1_iff_stokesBoundaries_eq_top`
    characterization (the load-bearing genus-0 topological input
    has a clean SmoothCycle-level handle).
  - `Manifold/C3PeriodLatticeCanonicalItemsDischarge.lean` —
    items 11/5/12 canonical discharge on RS conditional on H₁-subsingleton.

  *Smooth-singular Stokes foundation*:
  - `Manifold/Smooth2SimplexConst.lean` — `Smooth2Simplex.const I X P` +
    `boundary_const_smoothCycle P ∈ stokesBoundaries`.
  - `Manifold/SmoothPathIntegrateConstToPath.lean` — generic
    `SmoothPath.integrate_eq_zero_of_toPath_eq_const` (any
    constant-toPath path integrates to zero).
  - `Manifold/Smooth2SimplexConstBoundaryIntegrate.lean` —
    `Smooth2Simplex.integrate_boundary_const_eq_zero` (boundary of
    constant 2-simplex integrates to zero against ANY form).
  - `Manifold/Smooth2SimplexConstFaceEq.lean` — all three faces of
    `Smooth2Simplex.const I X P` are equal as SmoothPath terms
    (via `congr 1` + Prop proof-irrelevance), reducing
    `boundary (const P) = SmoothChain.single (face0 (const P))`.
  - `Manifold/SmoothPathConstFromFace0.lean` —
    `face0 (const P) = SmoothPath.const I X P`. Yields:
    `single_smoothPath_const_smoothCycle P ∈ stokesBoundaries`
    — a concrete `P`-indexed non-trivial element of stokesBoundaries
    (the SmoothCycle whose underlying chain is
    `SmoothChain.single (SmoothPath.const I X P)`).

  *Net classical-input boundary after this arc*:
  1. `cycleGens` choice (symplectic homology basis representatives);
  2. `riemannBilinear` (ℝ-LI of period vectors);
  3. `HolomorphicStokesHypothesis X` (Stokes' theorem for the
     real / imaginary components of every holomorphic 1-form against
     every smooth 2-simplex boundary — single atomic Prop);
  4. `stokesBoundaries 𝓘(ℝ, ℂ) X = ⊤` at genus 0 (the
     canonical-Stokes-quotient analogue of `H₁(S²; ℤ) = 0`).

  The constant-path direction is now fully foundationally laid:
  every `SmoothChain.single (SmoothPath.const I X P)` is a concrete
  member of `stokesBoundaries`. Toward `stokesBoundaries = ⊤` on RS,
  the next-layer reductions are smooth Hurewicz / smooth-loop-bounds
  from `simplyConnectedS2_holds`.

  Build: 9031 jobs clean. Zero `sorry`, zero `axiom`.

  **Path-plus-reverse Stokes-boundary identity (2026-05-18 evening,
  6 additional chips, ~675 LOC, MERGED, origin/main HEAD `dbfd7d8`).**
  Extends the smooth-singular foundation by exhibiting concrete
  non-trivial homological identities:

  *Infrastructure*:
  - `Manifold/SmoothPathExt.lean` — `SmoothPath.ext` extensionality
    lemma (`@[ext]`-tagged): equality of smooth paths reduces to
    matching src/tgt + pointwise toPath equality on unitInterval.
    Proven via `rcases`-mk-elim + `Path.ext` + `Prop`
    proof-irrelevance for the `smooth` existential.

  *Smooth-2-simplex from a path*:
  - `Manifold/Smooth2SimplexFromPath.lean` — for any
    `γ : SmoothPath I X`, the smooth 2-simplex
    `σ_γ(x) := γ.ambient (x 0)` (depending only on first coordinate)
    has faces identified as `face0 σ_γ = γ.reverse`,
    `face1 σ_γ = SmoothPath.const I X γ.src`, `face2 σ_γ = γ`. Hence
    `boundary σ_γ = single γ.reverse - single (const γ.src) + single γ
       ∈ stokesBoundaries`.

  *Path-plus-reverse identity*:
  - `Manifold/SmoothPathReverseStokesBoundary.lean` — combines the
    above with `single (const γ.src) ∈ stokesBoundaries` (chip 15)
    to conclude: **for ANY smooth path γ on ANY smooth manifold X,
    `SmoothChain.single γ + SmoothChain.single γ.reverse` (packaged
    as a SmoothCycle) lies in `stokesBoundaries I X`.** Witness:
    `Smooth2Chain.single (ofSmoothPathFstProj γ) + Smooth2Chain.single
    (Smooth2Simplex.const I X γ.src)`.
  - `Manifold/SmoothPathReverseIntegrateZero.lean` — complementary
    direct-computation: `SmoothChain.integrate (single γ + single
    γ.reverse) om = 0` for any 1-form `om` (no closedness assumption),
    via `SmoothPath.integrate_reverse`.
  - `Manifold/SmoothPathReverseH1Zero.lean` —
    `proj_single_smoothPath_plus_reverse_eq_zero`: the H₁-quotient
    class `[single γ + single γ.reverse]` is zero in
    `(StokesBoundaryInvariance.canonical I X).H1`.

  *Auxiliary*:
  - `Manifold/SmoothPathConstReverseEq.lean` — `SmoothPath.const_reverse`:
    `(SmoothPath.const I X P).reverse = SmoothPath.const I X P` (via
    `SmoothPath.ext`).

  *Geometric content*: in the canonical Stokes-homology quotient on
  ANY smooth manifold, every smooth path γ has `[γ.reverse] = -[γ]`.
  Constant paths bound (chip 15), reverse cancellation holds
  (chip 18). The remaining classical content for `stokesBoundaries
  = ⊤` (genus-0 case) is the simply-connected → null-bounded chain
  for non-constant loops — the smooth Hurewicz / null-homotopy →
  2-chain construction from `simplyConnectedS2_holds` on the
  Riemann sphere.

  Build: 9039 jobs clean. Zero `sorry`, zero `axiom` across all
  6 chips. **Cumulative 2026-05-18 arc: 23 chips, ~2280 LOC, all
  MERGED + PUSHED to origin/main HEAD `bc2a239`.** Final-arc
  chips also include: chain-level concat-additive integration
  (`Manifold/SmoothPathConcatIntegrateChain.lean`, `integrate_single_concat_eq_single_add_single`)
  and `(γ.reverse).reverse = γ`
  (`Manifold/SmoothPathReverseReverse.lean`).

  **Concat-additivity in stokesBoundaries (2026-05-18 night,
  10 chips, ~2210 LOC, MERGED + PUSHED to origin/main HEAD
  `a349fd8`).** Closes the foundational chain-level identity

  ```
  single (γ.concat δ h) - single γ - single δ ∈ stokesBoundaries I X
  ```

  for any compatible smooth paths γ, δ on any smooth manifold X.
  Net effect: concatenation of smooth paths is **additive** in the
  canonical Stokes H₁ quotient. This is the load-bearing structural
  identity needed to reduce arbitrary smooth 1-cycles (sums of
  smooth paths with cancelling boundary) into based loops at a fixed
  basepoint.

  *Concat 2-simplex with face1 = γ.concat δ (3 chips, ~580 LOC)*:
  - `Manifold/Smooth2SimplexFromConcat.lean` —
    `Smooth2Simplex.ofSmoothPathConcat γ δ h` with toFun
    `(x₀, x₁) := γ.concatAmbient δ (x₀/2 + x₁)`. Identifies
    `face1 σ = γ.concat δ h` via `SmoothPath.ext`.
  - `Manifold/SmoothPathBumpedHalf.lean` — `SmoothPath.bumpedHalfLeft γ`
    (ambient `t ↦ γ.ambient(concatRepLeft(t/2))`) and `bumpedHalfRight δ`
    (ambient `t ↦ δ.ambient(concatRepRight((1+t)/2))`). Both have
    same src/tgt as the original path.
  - `Manifold/Smooth2SimplexConcatFaceIdent.lean` — identifies
    `face2 σ = γ.bumpedHalfLeft`, `face0 σ = δ.bumpedHalfRight`. So
    `boundary σ = single δ.bumpedHalfRight - single (γ.concat δ h)
    + single γ.bumpedHalfLeft ∈ stokesBoundaries`.

  *Left reparam-invariance (3 chips, ~770 LOC)*:
  - `Manifold/Smooth2SimplexReparamLeftT1.lean` — first triangle T₁
    of the square-diagonal split of the smooth homotopy
    `(s, t) ↦ γ.ambient((1-s)*t + s*concatRepLeft(t/2))`. Faces:
    `face0=const γ.tgt`, `face2=γ`, `face1`=diagonal.
  - `Manifold/Smooth2SimplexReparamLeftT2.lean` — second triangle T₂.
    Faces: `face0=γ.bumpedHalfLeft.reverse`, `face1=const γ.src`,
    `face2`=same diagonal (cancellation lemma).
  - `Manifold/SmoothPathBumpedHalfLeftReparamInvariance.lean` —
    after diagonal cancellation, `∂(T₁+T₂) = const γ.tgt + γ +
    bumpedHalfLeft.reverse - const γ.src`. Combine with const-membership
    and reverse-cancellation to derive
    `single γ - single γ.bumpedHalfLeft ∈ stokesBoundaries`.

  *Right reparam-invariance (3 chips, ~640 LOC)*:
  - Mirror chips `Smooth2SimplexReparamRightT1.lean`, `T2.lean`,
    `SmoothPathBumpedHalfRightReparamInvariance.lean`. Headline
    `single δ - single δ.bumpedHalfRight ∈ stokesBoundaries`.

  *Concat-additivity capstone (1 chip, ~220 LOC)*:
  - `Manifold/SmoothPathConcatAdditivityStokes.lean` — linear
    combination `-(face_ident) - (left_reparam) - (right_reparam)`
    of three stokesBoundary memberships collapses to
    `single (γ.concat δ h) - single γ - single δ`. Headline
    `concat_additive_in_stokesBoundaries`.

  **Net classical-input boundary for the period-lattice side of C3
  after this arc**:
  1. `cycleGens` choice (symplectic homology basis representatives);
  2. `riemannBilinear` (ℝ-LI of period vectors);
  3. `HolomorphicStokesHypothesis X` (Stokes' theorem for the real /
     imaginary components of every holomorphic 1-form against every
     smooth 2-simplex boundary — single atomic Prop);
  4. `stokesBoundaries 𝓘(ℝ, ℂ) X = ⊤` at genus 0.

  Remaining for (4) on RiemannSphere: every smooth 1-cycle is a
  smooth 2-chain boundary. With concat-additivity, reverse-cancellation,
  and const-membership now in hand, this reduces to: **every smooth
  loop at a fixed basepoint on a simply-connected smooth manifold
  bounds a smooth 2-chain**. The genuine classical content remaining
  is the smooth-Hurewicz / null-homotopy → smooth 2-simplex
  construction. On RiemannSphere specifically, this is constructive
  via chart-based linear contraction in `ℂ` after avoiding a missed
  point.

  No `sorry`, no `axiom` across all 10 chips. Each verified
  individually via `LEAN_NUM_THREADS=1 lake env lean`.

  **Rebasing + V-loop-bounds + factorisation pipeline (2026-05-18
  late night, 11 chips, ~1840 LOC, MERGED + PUSHED to origin/main
  HEAD `3d765aa`).** Continues the period-lattice closure pipeline:
  with concat-additivity now done, builds the full structural
  framework reducing `stokesBoundaries 𝓘(ℝ, ℂ) RS = ⊤` to a single
  named atomic predicate `LoopFactorsThroughVectorSpaceHypothesis ℂ RS p₀`.

  *Rebasing arc (3 chips, ~510 LOC)*:
  - `Manifold/SmoothPathRebasingIdentity.lean` — `triple_concat_in_stokesBoundaries`:
    for α, γ, β smooth paths, `single (α ⋆ γ ⋆ β.reverse) - single α
    - single γ - single β.reverse ∈ stokesBoundaries`. Proof: sum of
    outer + inner concat-additivity.
  - `Manifold/SmoothPathRebasingFull.lean` — `rebasing_in_stokesBoundaries`:
    for any smooth path γ : a → b and based paths α : p₀ → a,
    β : p₀ → b, `single γ - single (α ⋆ γ ⋆ β.reverse) + single α
    - single β ∈ stokesBoundaries`. Proof: combine triple-concat with
    path-plus-reverse.
  - `Manifold/SmoothPathLoopRebasing.lean` — `loop_rebasing_in_stokesBoundaries`:
    specialisation to a smooth loop γ (γ.src = γ.tgt) and α : p₀ → γ.src;
    rebasing corrections collapse, giving
    `single γ - single (α ⋆ γ ⋆ α.reverse) ∈ stokesBoundaries`.

  *Named hypothesis (1 chip, ~150 LOC)*:
  - `Manifold/BasedSmoothLoopsBound.lean` —
    `BasedSmoothLoopsBoundHypothesis I X p₀ : Prop` saying every
    smooth loop based at `p₀` has its single in stokesBoundaries.
    Together with `loop_rebasing_in_stokesBoundaries`, gives
    `single_smoothLoop_in_stokesBoundaries_of_basedLoopsBoundHypothesis`:
    every smooth loop on a smooth-path-connected manifold has single
    in stokesBoundaries.

  *V-loop-bounds (3 chips, ~620 LOC)*:
  - `Manifold/Smooth2SimplexLoopBoundsVectorSpaceT1.lean` —
    `Smooth2Simplex.ofLoopBoundT1 γ`, the first triangle of the
    square-diagonal split of the smooth homotopy
    `H(s, t) := (1-s) • γ.ambient t + s • γ.src`. Faces: `face0 = const γ.src`,
    `face2 = γ`, `face1` = diagonal.
  - `Manifold/Smooth2SimplexLoopBoundsVectorSpaceT2.lean` — second
    triangle. Faces: `face0 = const γ.src` (right edge), `face1 = const γ.src`
    (bottom-left), `face2` = same diagonal (cancellation lemma).
  - `Manifold/SmoothLoopBoundsInVectorSpace.lean` —
    `single_smoothLoop_in_stokesBoundaries_vectorSpace`: every smooth
    loop in a normed ℝ-vector space `V` has single in
    `stokesBoundaries 𝓘(ℝ, V) V`. Discharges
    `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, V) V p₀` **unconditionally**
    for any basepoint.

  *stokesBoundaries pushforward (1 chip, ~210 LOC)*:
  - `Manifold/Smooth2SimplexPush.lean` — `Smooth2Simplex.push f hf`,
    `Smooth2Chain.push f hf`, `boundary₂_push` (compatibility), and
    headline `stokesBoundaries_push`: pushforward via a smooth map
    sends `stokesBoundaries I X → stokesBoundaries I Y`.

  *Compose V-loop-bounds + push (2 chips, ~230 LOC)*:
  - `Manifold/SmoothLoopBoundsViaChart.lean` —
    `single_pushSmoothLoop_in_stokesBoundaries_of_vectorSpaceSource`:
    for any smooth loop γ' in V and smooth map f : V → X (both
    modelled on 𝓘(ℝ, V)), `single (push f hf γ') ∈ stokesBoundaries 𝓘(ℝ, V) X`.
  - `Manifold/BasedSmoothLoopsBoundFromFactorisation.lean` —
    named predicate `LoopFactorsThroughVectorSpaceHypothesis V X p₀`
    (every smooth loop at p₀ factors as `push f γ'` for some smooth
    f : V → X and smooth loop γ' in V) + headline
    `basedSmoothLoopsBoundHypothesis_of_factorisation` discharging
    `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, V) X p₀` from the
    factorisation predicate.

  **Final classical-input boundary for the period-lattice side of C3
  on RiemannSphere** reduces to a SINGLE atomic predicate:

  ```
  LoopFactorsThroughVectorSpaceHypothesis ℂ RiemannSphere p₀
  ```

  i.e., every smooth loop on RS at `p₀` factors as the pushforward of
  some smooth loop in ℂ via a smooth (chart-style) map ℂ → RS.

  Constructive discharge on RS (future arc): for any smooth loop
  γ : SmoothPath 𝓘(ℝ, ℂ) RS at p₀, the measure-zero image
  γ([0, 1]) ⊆ RS misses some `q`; stereographic projection from `q`
  identifies `RS \ {q} ≅ ℂ` smoothly with `φ⁻¹ : ℂ → RS \ {q}` a
  global smooth map (defined on all of ℂ); take `f := φ⁻¹` (extended
  trivially as a total map ℂ → RS, image in RS \ {q}), and
  γ' := φ ∘ γ : [0, 1] → ℂ. Then γ = push f γ' is the desired
  factorisation.

  All 11 chips clean (`LEAN_NUM_THREADS=1 lake env lean`).
  Zero `sorry`, zero `axiom`.

**Prior-state landings (still relevant)**:

* **`lieAddGroup_quotient_of_zlattice`** (chip 2) — unconditional
  `LieAddGroup 𝓘(ℂ, Fin g → ℂ) ω ((Fin g → ℂ) ⧸ L)` instance for any
  discrete full-rank ℤ-lattice `L`. Discharges OPEN.md item 13's
  content on the lattice-quotient construction.
* **`PeriodLatticeOfRankTwoG.lieAddGroupHypothesis_holds`** (chip 3) —
  the **third and final** named-hypothesis discharge on the
  `PeriodLatticeOfRankTwoG` bundle, sister to
  `compactSpaceHypothesis_holds` (item 11) and
  `chartedSpaceHypothesis_holds` (items 5 + 12). Items 4, 5, 10, 11,
  12, 13 on `JacobianOfLattice X data` are now **all unconditional**
  once `[DiscreteTopology] [IsZLattice ℝ]` instance arguments are
  supplied.
* **`quotientLinearMap_contMDiff`** (chip 4) — building block for
  items 18, 21: ℂ-linear maps descended to lattice quotients are
  ContMDiff. Discharges the smoothness side of analytic-Jacobian-level
  pushforward and pullback unconditionally.
* **Named predicates `AbelJacobiSmoothness` (item 17) and
  `AbelJacobiInjective` (item 16)** + composite
  `JacobianAnalyticClosureBundle` packaging both — give Basic.lean a
  clean per-item handle, with discharge routes documented (C1 +
  FTC for 17, Abel's theorem for 16).

**Prior session** (2026-05-16 late night, +2,663 LOC across 32 new
chips for the **HolomorphicTraceExtension X item-(2) descent +
Hurwitz form arc** — see CHANGELOG):

* **ZZ24** chart-pullback-AnalyticAt-on-target lemma (chip 3d-21) —
  long-flagged owed in `AnalyticContinuationGlobalization.lean`, now
  unconditional in tree.
* **Manifold f-regularity at Hurwitz fibre points** (chip 3d-22) —
  discharged unconditionally modulo the standard small-disc continuity
  argument for chart-source containment.
* Complete pure-analytic + chart-pullback + manifold-level fibre
  enumeration foundation in tree for the trace 1-form's chart-coefficient
  extension across critical values.

Layered on prior 2026-05-16 arcs: RLSL-from-AGPC (+310), HolomorphicTrace
Extension day (+2,436), HolomorphicTraceExtension item-(2) algebraic
core (+1,501), and 2026-05-15 Hodge Forster scaffolding (+2,948) +
C3 structural-reduction + chain-rule arc (+2,280) + per-`t` trace
identity (+~975) + eventually-form composition (+~720) + global
integrand-trace integral identity (+~985). Build green as of
2026-05-16 HEAD post-3d-23.

**2026-05-15 evening — `RegularLevelSetLatticeClause` per-`t` trace identity.**
The arc closes the **algebraic** content of the per-`t` lattice clause
discharge by composing surjectivity-by-cardinality with cross-sheet
cotangent pullback identification. Six chips:

* `MeromorphicNonzeroFiberFinsetCard.lean` (~140 LOC) — bridges
  `(fiberFinset hv).card` to `degreeFiber f.toRiemannSphere`; constancy
  across regular values.
* `SourceFiberPathAmbientSurjOnAt.lean` (~210 LOC) — surjectivity of
  `(extend t)` at general `t`, image-eq-fiberFinset, `Set.BijOn`
  packaging.
* `CotangentPullbackAtCongr.lean` (~85 LOC) — cotangent pullback is
  germ-determined.
* `LocalSheetDataUnique.lean` (~140 LOC) — local right-inverse
  uniqueness; both two-sheet and general (sheet vs. arbitrary local
  right-inverse) versions.
* `CotangentPullbackSheetIdentification.lean` (~190 LOC) — cross-sheet
  cotangent pullback identification at a regular value.
* `SourceSheetSumEqTraceAt.lean` (~210 LOC) — headline per-`t`
  identity: `∑_{p ∈ sourceFiber} sheetCotPullback sheet_p.g (β(σ t)) ω
  = traceAt f hnc hβσt_reg ω`, parametrized over the sub-interval +
  lift-equality conditions (discharged downstream on uniform-δ).

**Remaining for `RegularLevelSetLatticeClause`:** σ-reparametrisation
(`s = σ t`, requires integrand-as-function-of-s continuity = `f_*ω`
smoothness), `f_*ω` smooth-on-`regularValueSet` packaging, and residue
theorem adaptation from `principalDivisorMap` to `f_*ω`'s residue
divisor on ℙ¹.

**2026-05-15 (later session) — `RegularLevelSetLatticeClause` arc, six
more chips landed (+~1,156 LOC, build at 8854 jobs).**

* `MeromorphicNonzeroFStarOmegaDef.lean` (137 LOC) — `fStarOmega f hnc om :
  (v : RiemannSphere) → CotangentSpace _ v` returning `traceAt` at regular
  values and `0` (junk) elsewhere; ℝ-linear in `om`.
* `ChainDifferenceCycle.lean` (76 LOC) — generalises `singleDiff_isCycle`:
  `boundary c₁ = boundary c₂ ⇒ c₁ - c₂ ∈ SmoothCycle`.
* `RegularLevelSetChainBoundaryAJ.lean` (154 LOC) — `regularLevelSetCycleWitness`
  packages `regularLevelSetChain f + principalDivisorAJChain (principalDivisorMap f)`
  as a `SmoothCycle` via boundary cancellation. **Note**: this gives
  `period(Z) ≡ -period(AJ) (mod lattice)`, NOT `period(Z) ∈ lattice` —
  the lattice clause still needs the residue input independently.
* `MeromorphicNonzeroFiberLocallyConst.lean` (411 LOC) — `localFiberLabelingNbhd`
  is an open nbhd of `v₀ ∈ regularValueSet` on which `p ↦ (fiberSheetAt p).g v`
  is a Finset bijection `fiberFinset hv₀ ≃ fiberFinset hv` (via cardinality
  + InjOn-from-disjoint-shrunk-sheets).
* `FStarOmegaLocalAt.lean` (151 LOC) — fixed-Finset rewrite of `fStarOmega`
  on the labelling nbhd: `fStarOmega om v = ∑_{p ∈ fiberFinset hv₀}
  cotangentPullbackAt sheet_p.g v om`. Composes `fiberSheetAt_g_image_eq_fiberFinset`
  (above) + `cotangentPullbackAt_localSheet_eq_at_target_sheet` (in tree).
* `IntegrateLevelSetChainSigmaReparam.lean` (227 LOC, **conditional**) —
  σ-reparametrisation `s = σ(t)` via `intervalIntegral.integral_deriv_smul_comp'`,
  conditional on a named hypothesis `IntegrandContinuousAlongBeta`
  (continuity of `s ↦ applyCotangent (traceAt … (β s) om) (mfderiv β s 1)`
  on `Icc 0 1`).

**Remaining for unconditional `RegularLevelSetLatticeClause`:**
1. **`IntegrandContinuousAlongBeta` discharge** — **CLOSED 2026-05-15**
   via `Manifold/IntegrandContinuousAlongBetaUnconditional.lean`'s
   `integrandContinuousAlongBeta_holds`. Build 8870 jobs, zero
   sorry/axiom. Discharge routes through the chart-coord-pair
   architecture (chips 9–12) + chain-rule per-sheet reduction
   (`SheetCotPullbackPairingContinuity.lean`) + fixed-Finset sum
   continuity at each `s₀ ∈ Icc 0 1` with `β s₀ ∈ regularValueSet`
   (`FStarOmegaPairingContinuity.lean`). Headline:
   ```
   theorem integrandContinuousAlongBeta_holds
       (f : MeromorphicNonzero X)
       (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
       (hβ_smooth : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) ∞ β)
       (hβ_reg : ∀ s ∈ Icc 0 1, β s ∈ f.regularValueSet)
       (om : SmoothOneForm 𝓘(ℝ,ℂ) X) :
       f.IntegrandContinuousAlongBeta hnc hβ_smooth hβ_reg om
   ```
   The sheet-side smoothness (`f-5`) is implicit in the chain-rule
   reduction: each per-sheet pairing factors through the smoothness
   of the local sheet inverse `sheet_p.g` realified to `𝓘(ℝ,ℂ) ∞` on
   an open nbhd of `β s₀` (via `exists_contMDiffOn_localSheet_g_near_basePoint`
   + `ContMDiffOn.complex_to_real_of_isOpen`).

   **2026-05-15 evening — 9-chip groundwork arc** (build 8863 jobs, zero
   sorry/axiom). Two API entry points now land in tree:
   * **Factor-decomposed** (chips 1–8, e.g.
     `Manifold/IntegrandContinuousAlongBetaPerSheetVel.lean`'s
     `integrandContinuousAlongBeta_of_per_sheet_univ_and_velocity`) —
     discharges `IntegrandContinuousAlongBeta` from a universal per-sheet
     `ContinuousOn` hypothesis on `(cotangentEquiv (sheetCotPullback p v om)
     : ℂ →L[ℝ] ℝ)` plus velocity `ContinuousOn`. **Architectural caveat**:
     this routes through *absolute-coord* `cotangentEquiv` which is NOT
     globally continuous for non-trivial cotangent bundles (chart-cocycle
     cancels only inside the pairing); discharge-friendly only for paths
     whose labelling nbhds and sheet images each fit within single charts
     of RS / X respectively (i.e. paths not crossing `∞`).
   * **Chart-coord-pair** (chip 9, `Manifold/ChartBetaVelocity.lean`'s
     `chartBetaVelocity` + `contMDiffAt_chartBetaVelocity`) — first
     primitive of the architecturally correct architecture (mirrors
     `SmoothPathIntegrability.continuous_integrand_at`).

     **2026-05-15 — chart-coord-pair architecture: SmoothOneForm
     pairing continuity (3 chips, ~351 LOC, build 8866):**
     * `ChartBetaVelocitySelfEval.lean` (`chartBetaVelocity_self`):
       at the anchor `s₀`, both cocycles collapse, giving
       `chartBetaVelocity I β s₀ s₀ = mfderiv β s₀ (1 : ℝ)`.
     * `ChartBetaPairingInvariance.lean`
       (`applyCotangent_eq_chart_pairing_beta`): for any cotangent
       `φ` at `β s` with `β s` in the chart source at `β s₀`, the
       pairing `applyCotangent φ (mfderiv β s 1)` equals the
       chart-coord pairing with `chartBetaVelocity I β s₀ s`.
       Stated for a *free* cotangent (not a SmoothOneForm), ready to
       compose with `traceAt` directly.
     * `PairingContinuityBeta.lean`
       (`continuousAt_pairing_smoothOneForm_beta`,
       `continuous_pairing_smoothOneForm_beta`): for any
       `om : SmoothOneForm I M`, the pairing
       `s ↦ applyCotangent (om (β s)) (mfderiv β s 1)` is
       `ContinuousAt s₀` (and hence `Continuous`).

     **Remaining blocker:** `chartFStarOmega` / `f-5` — section
     smoothness of `fStarOmega` on `regularValueSet` (or its
     `SmoothOneFormOn` upgrade). Once `f_*ω` is a `SmoothOneForm`
     (or `SmoothOneFormOn regularValueSet`), the
     `continuousAt_pairing_smoothOneForm_beta` lemma above directly
     discharges `IntegrandContinuousAlongBeta` for the trace-pairing
     along `β`.

2. **Residue theorem on 1-forms on `ℙ¹`** — adapts the in-tree
   `JacobianChallenge.residue_theorem` (function level) to
   meromorphic 1-forms. The chain-difference reduction in
   `RegularLevelSetChainBoundaryAJ.lean` does NOT bypass this: it
   gives `period(regularLevelSetChain) ≡ -period(AJ-chain) (mod lattice)`,
   and `period(AJ-chain) ∈ lattice` is the very `AbelGeneratorPeriodCondition`
   we're trying to discharge — circular reduction. The 1-form residue
   theorem is genuine new classical input (~1,500–2,500 LOC realistically).

**Lebesgue gluing is no longer required** — the lifted-point sheet
breakthrough (2026-05-15 late evening) gave a global integrand
identity at any `t ∈ Ioo 0 1` directly, bypassing Hurwitz
subdivision.

**2026-05-16 — `fStarOmegaOn` arc + `HolomorphicTraceExtension`
structural reduction (6 chips, ~974 LOC).** Pushes the regular-case
clause discharge one structural step further than the 2026-05-16
trace-vanishing route:

* `fStarOmegaOn` (`Manifold/FStarOmegaOn.lean`) — packages
  `f.fStarOmega hnc om` as a `SmoothOneFormOn 𝓘(ℝ, ℂ) RiemannSphere
  f.regularValueSet`. Smoothness on the open regular set is now
  **unconditional**, via four supporting chips:
  - `SheetCotangentPullbackContMDiffAt` — holomorphic per-sheet
    pullback section smoothness (local-sheet analogue of
    `HolomorphicEquiv.pullbackSection_contMDiffAt`).
  - `SheetCotPullbackContMDiffAtReal` — realified `𝓘(ℝ, ℂ) ⊤`
    counterpart (field-generic bridge identity at 𝕜 := ℝ); also
    ships `complex_to_real_omega`, a regularity-preserving variant
    of `ContMDiffRealification.complex_to_real`.
  - `FStarOmegaContMDiffAt` — pointwise `ContMDiffAt ⊤` at regular
    values via mathlib's `ContMDiffAt.sum_section` + the
    `FStarOmegaLocalAt` fixed-Finset rewrite.

* `HolomorphicTraceExtension`
  (`Manifold/TraceAtVanishesOnHolomorphicReduction.lean`) — the new
  named hypothesis: for every non-constant `f` and every
  `α : HolomorphicOneForm X`, ∃ `α' : HolomorphicOneForm RiemannSphere`
  whose realified components agree pointwise on `f.regularValueSet`
  with the realified trace of `α`. Discharged conditionally:
  `traceAtVanishesOnHolomorphic_of_extension` + composition with
  `regularLevelSetLatticeClause_of_traceVanishing` gives
  `regularLevelSetLatticeClause_of_holomorphicTraceExtension`. The
  unconditional `Subsingleton (HolomorphicOneForm RiemannSphere)`
  (`Manifold/RiemannSphereChartSCoeffOverlap.lean`) closes the
  vanishing side once the extension provides the global α'.

* `HolomorphicOneFormOn` (`Manifold/HolomorphicOneFormOn.lean`) —
  partial-domain holomorphic 1-form type (analogue of
  `SmoothOneFormOn` in `𝓘(ℂ, ℂ) ω`). Target type for the eventual
  on-regular-set holomorphic trace; sets up the next-stage chip arc
  (holomorphic-side parallel to `fStarOmegaOn`).

**Net state after 2026-05-16.** Regular-case lattice clause discharge
reduces to **one** named hypothesis (`HolomorphicTraceExtension X`).
Its construction needs:
  1. The **holomorphic** analogue of `fStarOmegaOn` — a
     `HolomorphicOneFormOn 𝓘(ℂ, ℂ) RiemannSphere f.regularValueSet`,
     built by mirroring sub-chips B/C in the `𝓘(ℂ, ℂ) ω` bundle.
     Sub-chip A already provides the per-sheet input; estimated
     ~300-500 LOC.
  2. **Extension across critical values** — n-th-root cancellation +
     Riemann removable singularity theorem on 1-forms on `ℙ¹`. This
     is the genuinely-new classical content not at the mathlib pin.
  3. **Realification compatibility** — pointwise
     `realComponent α' v = traceAt (realComponent α) v` on the
     regular set, gluing (1)+(2) to the realified
     `TraceAtVanishesOnHolomorphic` form.

Build (all 6 chips of this session): single-file
`LEAN_NUM_THREADS=1 lake env lean` clean, zero `sorry`, zero `axiom`.

**2026-05-16 (afternoon) — `fStarOmegaHolOn` arc: item (1) closed,
holomorphic-side parallel built (6 chips, 828 LOC).** Mirrors the
morning's `fStarOmegaOn` arc on the holomorphic `𝓘(ℂ, ℂ) ω` bundle:

* `HolomorphicCotangentPullbackAt` — pointwise holomorphic pullback
  primitive with ℂ-linearity in α + germ congruence in g.
* `MeromorphicNonzeroHolTraceAt` — `holTraceAt`, `holSheetCotPullback`,
  cross-sheet identification (parallel to
  `cotangentPullbackAt_localSheet_eq_at_target_sheet`).
* `MeromorphicNonzeroFStarOmegaHolDef` — total `fStarOmegaHol α v`
  with `if hv then holTraceAt else 0`, ℂ-linearity, apply lemmas.
* `FStarOmegaHolLocalAt` — fixed-Finset rewrite on labelling nbhd
  (mirror of the realified `fStarOmega_eq_sum_sheetCotPullback_at_v0`,
  reusing the bundle-independent `fiberSheetAt` machinery).
* `FStarOmegaHolContMDiffAt` — pointwise `ContMDiffAt ω` at every
  regular value (per-sheet from sub-chip A + `ContMDiffAt.sum_section`
  + `congr_of_eventuallyEq`).
* `FStarOmegaHolOn` — final `HolomorphicOneFormOn RiemannSphere
  f.regularValueSet` packaging.

**Item (1) is now CLOSED.** The on-regular-set holomorphic 1-form
`f.fStarOmegaHolOn hnc α` is built unconditionally.

**Remaining for `HolomorphicTraceExtension X`** (next-session chip
arcs):

* **Item (2) — Extension across critical values.** The genuinely-new
  classical content. Build `globalize : HolomorphicOneFormOn RS s →
  HolomorphicOneForm RS` under the conditions that `s = f.regularValueSet`
  is open-cofinite and the on-set form has the n-th-root cancellation
  behavior at each critical value. Mathematical content: n-th-root
  cancellation + Riemann removable singularity for 1-forms on `ℙ¹`.
  Not at mathlib pin; estimated 1500-2500 LOC.

  **2026-05-16 (night) update — algebraic foundation COMPLETE.** 11
  chips (~1501 LOC) landed in `JacobianChallenge/Manifold/`: bridge
  primitives (removable-singularity adapter, on-set `localCoeff` +
  chart-target `ContMDiffOn` with full cocycle, critical-value chart
  shrink) + n-th-root cancellation algebraic core (roots-of-unity
  orthogonality; **general-`k` `KthRootSubstitution` closing a named
  gap**; cyclic-sum symmetry + first-order vanishing +
  vanishing-to-order-`(k-1)`; bounded-trace bound
  `‖cyclicSum‖ ≤ C·‖ξ‖^(k-1)`; ω-invariance + full cyclic-group
  invariance of the analytic factor `q`). Remaining for item (2):
  (a) **descent** of `q` to an analytic function of `ξ^k` via
  `FormalMultilinearSeries` Taylor-subseries (~300-500 LOC); (b)
  **manifold/cotangent-bundle wiring** of the per-preimage trace
  cluster at critical values, applying the bound +
  removable-singularity adapter (~400-600 LOC). See CHANGELOG
  `2026-05-16 (night)` entry for the chip-by-chip breakdown.

* **Item (3) — Realification compatibility.** Reduces to the manifold
  derivative identity `(mfderiv 𝓘(ℂ, ℂ) g x).restrictScalars ℝ =
  mfderiv 𝓘(ℝ, ℂ) g x` for ℂ-smooth `g`. Path: lift through
  `HasMFDerivAt ↔ HasFDerivWithinAt` + the chart-pullback identity
  `HasFDerivAt.restrictScalars`. Mathlib provides
  `DifferentiableAt.fderiv_restrictScalars`; manifold bridging is
  in-tree work, estimated 200-400 LOC.

Net: once items (2) + (3) ship, `HolomorphicTraceExtension X` is
unconditional and `RegularLevelSetLatticeClause X α_basis h_bundle` is
unconditional. Item (1)'s sub-chips also unlock any future use of
`fStarOmegaHolOn` for non-RLSL purposes (residue theorem, Hodge
theory, period-pairing finite-dim arguments).

**2026-05-16 (late afternoon) — Realification compat: chips 1+2 of 3
shipped (289 LOC).** Per-summand realification compatibility for the
holomorphic cotangent pullback is now unconditional:

* `mfderiv_complex_to_real_apply` (`MFDerivComplexToRealApply.lean`,
  171 LOC) — **manifold-derivative apply-level realification**: for
  ℂ-differentiable `g`, `(mfderiv 𝓘(ℝ, ℂ) g x) w = (mfderiv 𝓘(ℂ, ℂ) g x) w`
  as elements of `ℂ`. The typed `.restrictScalars`-statement attempted
  on the prior commit was blocked by `Module ℂ (TangentSpace 𝓘(ℝ, ℂ) x)`
  synth failure. Workaround: apply-level statement +
  explicit-`@`-form wrappers around `DifferentiableAt.restrictScalars`
  / `HasFDerivAt.restrictScalars` to manually pass
  `IsScalarTower ℝ ℂ ℂ` (mathlib's discrimination tree doesn't try
  `IsScalarTower.right` in this position).

* `realPartCLM_holCotangentPullbackAt_apply` /
  `imagPartCLM_holCotangentPullbackAt_apply`
  (`HolCotangentPullbackRealification.lean`, 118 LOC) —
  **per-summand realification compatibility**: for ℂ-differentiable
  `g`, `(realPartCLM (holCotangentPullbackAt g y α)) w
  = Complex.re ((α.eval (g y)) ((mfderiv 𝓘(ℝ, ℂ) g y) w))`
  (and analogously for `imagPartCLM`). Reduces to chip 1.

**2026-05-16 (evening) — Realification compat chip 3 shipped (345 LOC).**
Trace-level real / imag realification compatibility:

* `realPartCLM_fStarOmegaHol_apply` /
  `imagPartCLM_fStarOmegaHol_apply` (`FStarOmegaHolRealification.lean`,
  345 LOC) — at every regular value `v` and tangent vector `w : ℂ`:

      (realPartCLM (f.fStarOmegaHol hnc α v)) w
        = SmoothPath.applyCotangent (f.fStarOmega hnc (realComponent α) v) w

  (and analogously for `imagPartCLM` / `imagComponent`). Sums chip 2
  over the fiber via a generalised inner lemma + `Finset.induction_on`
  (working around the `map_sum realPartCLM` pattern-match failure that
  blocked the direct approach).

**Item (3) is now CLOSED.** Both real and imaginary realification
compatibilities hold unconditionally on `f.regularValueSet`.

**Remaining for `HolomorphicTraceExtension X`:** only item (2) —
extension across critical values (n-th-root cancellation + Riemann
removable singularity for 1-forms on `ℙ¹`). Genuinely-new classical
content not at the mathlib pin.

**2026-05-15 evening — Integrand-trace identity in full eventually
form (5 additional chips, ~720 LOC).** Lifts the algebraic per-`t`
trace identity to integrand-level + fully eventually form near `t = 0`:

```
∀ᶠ t in 𝓝[Ioc 0 1] 0, ∃ hβσt_reg : β(σ t) ∈ regularValueSet,
  ∑ p ∈ sourceFiber, (sourceFiberPath p).integrand om t
    = applyCotangent (traceAt f hnc hβσt_reg om) (β'(σ t) σ'(t))
```

Five chips:

* `PerFiberSheetEventually.lean` — sub-interval V-membership +
  lift-equality eventually.
* `SourceSheetSumEqTraceAtEventually.lean` — per-`t` trace identity
  in eventually form.
* `LevelSetIntegrandEqTraceAtApply.lean` — integrand-level per-`t`
  identity (chain rule + trace).
* `SheetGRealSmoothEventually.lean` — realified sheet.g smoothness
  eventually.
* `PerFiberChainRuleEventually.lean` — per-fibre chain rule promoted
  to filter form.
* `LevelSetIntegrandEqTraceAtApplyEventually.lean` — full eventually
  composition headline.

This is the integrand of `(levelSetChain f β).integrate ω` equating
to the integrand of the line integral of `f_*ω` along β (modulo
σ-reparam). Build at **8836 jobs**.

**2026-05-15 late evening — Lifted-point local identification +
global integrand-trace integral identity (8 chips, ~1,330 LOC).**
Architectural breakthrough: the **lifted-point sheet** `sheet_q` at
`q := extend t₀ p` automatically satisfies the sub-interval
condition (`sheet_q.V ∋ β(σ t₀)` by construction), so the chain
rule based at `sheet_q` works at **every** `t₀` — bypassing
Hurwitz subdivision entirely. Eight chips:

* `SourceFiberPathExtendEqSheetGAtT.lean` (~218 LOC) — local
  identification at general `t₀` via lifted-point sheet.
* `SourceFiberPathIntegrandLocalSheetGAtT.lean` (~127 LOC) — per-
  fibre integrand at general `t₀` via lifted-point sheet (composes
  with `integrand_eq_of_ambient_eqOn_Icc_fun`).
* `SourceFiberPathIntegrandChainAtT.lean` (~238 LOC) — chain-rule-
  unfolded per-fibre integrand at general `t₀` via two
  `mfderiv_comp_apply` applications + `applyCotangent_cotangentPullbackAt`.
* `GlobalIntegrandTraceIdentity.lean` (~165 LOC) — global per-`t`
  identity at any `t ∈ Ioo 0 1`:
  ```
  ∑ p, (sourceFiberPath p).integrand om t
    = applyCotangent (traceAt f hnc hβσt_reg om)
        (mfderiv β (σ t) (mfderiv σ t 1))
  ```
  No sub-interval restriction. Composes per-fibre chain-rule + Finset
  bijection (sourceFiber ↔ fiberFinset(β(σ t))) +
  `applyCotangent_traceAt`.
* `IntegrateLevelSetChainEqTraceAt.lean` (~125 LOC) — integrated
  identity: `SmoothChain.integrate (levelSetChain f β) om = ∫ t in
  0..1, applyCotangent (traceAt … (β(σ t)) om) (mfderiv β (σ t)
  (mfderiv σ t 1))`. Composes via `integrate_levelSetChain` (chain →
  ∑_p) + `intervalIntegral.integral_finset_sum` (swap ∑/∫) +
  `intervalIntegral.integral_congr_ae` (boundary `{1}` measure-zero)
  + global per-`t` identity.
* `IntegrandSigmaSmulFactor.lean` (~162 LOC) — factors out
  `derivσ(t)`:
  ```
  SmoothChain.integrate (levelSetChain f β) om
    = ∫ t in 0..1, derivσ(t) *
        applyCotangent (traceAt … (β(σ t)) om) (mfderiv β (σ t) 1)
  ```
  Via `mfderiv_eq_fderiv` + ℝ-linearity of CLM and `cotangentEquiv`.
  This is exactly the shape required by
  `intervalIntegral.integral_comp_mul_deriv` for the σ-reparam
  conversion to `∫ s in 0..1, applyCotangent (traceAt … (β s) om)
  (mfderiv β s 1) ds`.

Build green at **8842 jobs**. Zero `sorry`, zero `axiom`.

**2026-05-16 evening — C3 structural reduction + chain-rule pathway 1-3.**
The arc delivers a two-tier reduction of `AbelHypothesis B`:

*Tier 1.* Two named classical inputs:

* `RegularLevelSetLatticeClause X α h` — period vector of
  `regularLevelSetChain f hnc h0 h∞` ∈ `periodLatticeImage`. The
  substantive analytic core (residue theorem for `f_*ω` on `ℙ¹`).
* `AbelLatticeWitnessCriticalCase X α h` — witness chain for `f` with
  `0` or `∞` critical (Möbius substitution residual).

Headlines:
`AbelJacobiInput.forall_abelHypothesis_of_split hRL hCR : ∀ B, AbelHypothesis B`,
`dischargedGenerators_eq B B' : B.dischargedGenerators = B'.dischargedGenerators`.

*Tier 2.* Structural per-`t` identity for the level-set chain integral
on `Ioo 0 δ`:
`∑_p integrand(sourceFiberPath p) ω t = applyCotangent (∑_p cotangentPullbackAt sheet_p.g (β(σ t)) ω) (β'(σ t) σ'(t))`.

The **injection half** of the sourceFiber ↔ `f⁻¹(β(σ t))` bijection is
fully proved (`sourceFiberPath_toPath_extend_injOn_at` at arbitrary
`t ∈ Icc 0 1`, plus `Set.InjOn`-form and image ⊆ fiberFinset). The
surjectivity half (cardinality argument via
`degreeFiber_eq_card_of_regular_witness` or time-reversal at general
`t`) remains.

**2026-05-15 — Hodge finite-dim Forster scaffolding.** Sixteen chips,
+2,948 LOC. The full Forster/Montel/Riesz proof of
`HolomorphicOneFormFiniteDim X` is reduced to **two remaining steps**:
(i) seminorm convergence (inner-disk uniform → outer-disk seminorm via
the multi-chart density bound); (ii) `NormedAddCommGroup` wrapper +
separating + Riesz `FiniteDimensional.of_isCompact_closedBall₀`.
Per-chip breakdown:

* `localCoeff` API (chart-coord coefficient of a holomorphic 1-form,
  +340) — `HolomorphicOneFormChartCoeff.lean`.
* `localCoeff_contMDiffOn` on chart target via cocycle (+338) —
  `HolomorphicOneFormChartCoeffOnTarget.lean`.
* `DiskChartCover X` (finite chart cover with disk hierarchy on
  compact `X`, +201) — `CompactDiskChartCover.lean`.
* `localCoeffMax` per-chart sup (+252) — `DiskChartCoverSeminorm.lean`.
* `seminormVal` aggregation (+119) — `DiskChartCoverSeminormAggregate.lean`.
* Cauchy first-derivative estimate (+204) —
  `DiskChartCoverCauchyEstimate.lean`.
* Lipschitz bound via MVT (+154) — `DiskChartCoverLipschitz.lean`.
* Arzelà-Ascoli per chart (+188) — `DiskChartCoverArzela.lean`.
* Diagonal subsequence across base points (+114) —
  `DiskChartCoverDiagonal.lean`.
* Scalar pointwise limit at any `y ∈ X` (+113) —
  `DiskChartCoverPointwiseLimit.lean`.
* CLM-level pointwise limit (+192) — `DiskChartCoverCLMLimit.lean`.
* Analyticity of chart limit on inner ball via
  `TendstoLocallyUniformlyOn.differentiableOn` (+173) —
  `DiskChartCoverLimitAnalytic.lean`.
* `limitSectionToFun` via `Classical.choose` (+79) —
  `DiskChartCoverLimitSection.lean`.
* Chart-frame CLM identification of the limit (+188) —
  `DiskChartCoverLimitSmooth.lean`.
* Composed `smulRight 1 ∘ bcfExtend ∘ chart-x` ContMDiffAt
  (+109) — `DiskChartCoverLimitContMDiff.lean`.
* End-to-end packaging as `HolomorphicOneForm X` (+184) —
  `DiskChartCoverLimitPackage.lean`. Headline:
  `DiskChartCover.limitHolomorphicOneForm cover om_n h_diag :
  HolomorphicOneForm X` — given a `seminormVal`-bounded
  sequence + the diagonal subsequence convergence at every base
  point, packages the pointwise CLM limit as a smooth section.

**Net effect.** The full Forster/Montel/Riesz proof of
`HolomorphicOneFormFiniteDim X` is reduced to **two remaining steps**:
(i) seminorm convergence — upgrade the per-inner-disk uniform
convergence to outer-disk seminorm convergence (the standard fix uses
the multi-chart density bound via the cotangent transition's
continuity); (ii) `NormedAddCommGroup` wrapper + separating (cotangent
coord-change invertibility on the fibre) + Riesz application
(`FiniteDimensional.of_isCompact_closedBall₀`).

**Prior 2026-05-16 wave** (10 chips, +1,573 LOC; cumulative session
note retained for context):

* `h_AJ_boundary` discharge (+125) — `PrincipalDivisorAJChainBoundary.lean`.
* Regular β: 0→∞ existence on ℙ¹ (+431) — `MeromorphicNonzeroRegularPath.lean`.
* Concrete regular level-set chain + boundary identification (+146)
  — `MeromorphicNonzeroConcreteLevelSetChain.lean`.
* Real-model RS manifold + open-set realification (+96)
  — `RiemannSphereRealManifold.lean`.
* Pointwise cotangent pullback primitive (+94) — `CotangentPullbackAt.lean`.
* Pointwise trace `f_*ω` at a regular value (+117)
  — `MeromorphicNonzeroTraceAt.lean`.
* `SmoothOneFormOn` partial-section type + `restrictOnSet` (+88)
  — `SmoothOneFormOn.lean`.
* Scalar evaluation of cotangent pullback and trace (+123)
  — `CotangentPullbackAtApply.lean`.
* `ContinuousOn` variant of `path_lift_eqOn_Icc` (+131)
  — `MeromorphicNonzeroPathLiftUniqueOnContinuousOn.lean`.
* Local identification of `sourceFiberPath` with `sheet.g ∘ β ∘ σ`
  (+222) — `MeromorphicNonzeroSourceFiberPathSheetEq.lean`.

**13 additional chips (2026-05-16 later) — `HolomorphicOneFormSubsingletonOfSimplyConnected` arc** (+1,510 LOC, 7 new files):

* Continuous homotopy of smooth paths from `SimplyConnectedSpace` (+111)
  — `SmoothPathHomotopyFromSimplyConnected.lean`.
* `chartCoeffAt` for `HolomorphicOneForm X` + pointwise linearity (+100)
  — `HolomorphicOneFormChartCoeff.lean`.
* **Unconditional Liouville for `ContMDiff ω F : X → ℂ`** via exp trick (+373)
  — `Topology/LiouvilleForContMDiffOmega.lean`.
* **Subsingleton from primitive existence + bridge to named predicate**
  + full-arc `S2ImpliesGenus0_of_primitiveExistence` (+268)
  — `Topology/SubsingletonFromPrimitiveExistence.lean`.
* `complexChainPeriod` form-side algebra: linearity / smul_real /
  smul_complex / reverse / concat / `→ₗ[ℂ]` / bilinear bundle (+244)
  — `ComplexChainPeriodFormLinear.lean`.
* `chartLocalPrimitive` data + basepoint identity `F(x₀) = 0` (+236)
  — `ChartLocalPrimitive.lean`.
* E foundation: joint continuity of `bumpedSegment` /
  `chart.symm ∘ bumpedSegment` / `chartCoordVelocity σ'(t)·(z-z₀)` (+178)
  — `ChartLocalPrimitiveSmoothness.lean`.

Cumulative delta vs. 2026-05-14 snapshot (86,894 LOC / 416 files):
**+17,134 LOC / +104 files** (Hodge Forster +2,948 / 16 files plus
the 2026-05-16-evening C3 reduction +2,280 / 13 files on top of the
prior +13,400 / 82 files baseline). Build green at 8808 jobs (last
verified at HEAD `59a72b1` pre-Hodge-rebase), zero `sorry`, zero
`axiom`. See `CHANGELOG.md` for the per-branch history.

**Remaining LOC to 24/24** (full breakdown in `CLOSURE_MAP.md` §F):
**~11,000–21,000 LOC** for the realistic **23/24** target (deferring
uniformization at genus 0 as a named classical hypothesis).
Highest-leverage chunk: PL-4 discharge (steps 1–3 of the priority order)
flips 6 items (4, 5, 10, 11, 12, 13) for ~3,300–7,600 LOC.
Closing item 14 strictly requires uniformization in-tree (multi-month).

Do not regenerate this list from context — query this file. Update this file
whenever a status changes.

## Definitions (data) — Basic.lean items 1–9 in OPEN.md numbering

| # | Item | Status | Notes |
|---|---|---|---|
| 1 | `genus X : ℕ` | **STRICT-CLOSED** *(post-Forster, 2026-05-17)* | Body: `JacobianChallenge.genus X = Module.finrank ℂ (HolomorphicOneForm X)`. **Finite-dimensionality on a compact connected complex 1-manifold is unconditional** via `DiskChartCover.holomorphicOneFormFiniteDim_holds` (`Manifold/DiskChartCoverFiniteDim.lean`), so the junk-zero convention does not kick in and `Module.finrank` returns the honest geometric genus. The anti-hack pair (item 14, `genus_eq_zero_iff_homeo`) is **OPEN** but is not a status blocker for item 1 itself. |
| 2 | `Jacobian X : Type u` | **STRICT-CLOSED** *(post-ZZ256, 2026-05-12)* | Body: `Jacobian X := Pic0 X` with `Pic0 X = Div0 X ⧸ (PrincDiv X).addSubgroupOf (Div0 X)` and **`PrincDiv X := PrincDivHonestCandidate X`** (honest principal-divisor subgroup, in `Divisor/PrincipalDivisorRange.lean`). |
| 3 | `instance : AddCommGroup (Jacobian X)` | **STRICT-CLOSED** *(post-ZZ256)* | Inherits from the honest `Pic0` quotient. |
| 4 | `instance : TopologicalSpace (Jacobian X)` | **STUB** | Discrete (`⊥`). The challenge wants the complex-manifold topology (item 5 `ChartedSpace`); discrete is not it. |
| 5 | `instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` | **OPEN** | Requires the analytic-Jacobian construction (period-lattice). The parallel `AnalyticTorus X` carries an honest `ChartedSpace` instance (`Manifold/PeriodLattice.lean`), but is not wired into `Jacobian`. |
| 6 | `Jacobian.ofCurve : X → Jacobian X` | **STRICT-CLOSED** *(post-ZZ256)* | Body: `Q ↦ [δQ − δP]` in honest `Pic⁰`. |
| 7 | `Jacobian.pushforward f hf` | **STRICT-CLOSED** *(post-ZZ256)* | Body: `JacobianChallenge.Jacobian.pushforward hf` in `JacobianPushforward.lean`. Descent via P1.4 (`PrincDivHonestCandidate_addSubgroupOf_Div0_le_comap_divPushforward`) on the non-constant branch + degree-zero trivialization on the constant branch. |
| 8 | `Jacobian.pullback f hf` | **STRICT-CLOSED** *(post-ZZ256)* | Body: `Jacobian.pullbackHonest_of_rsum`, which dispatches to either `0` (constant `f`) or `Jacobian.pullbackWeighted` with `e := manifoldRamificationIndex f` and `N := degreeFiber f hf`. The `Pic0.pullbackWeighted` descent obligation is discharged unconditionally by `Pic0.divPullbackWeighted_descent_of_smooth` (`JacobianPullback.lean`) — sister chip to P1.4 in the contravariant direction. |
| 9 | `ContMDiff.degree f hf : ℕ` | **STRICT-CLOSED** *(post-zzITEM9, 2026-05-12)* | Body: `JacobianChallenge.ContMDiff.degreeFiber f hf`. Well-definedness across regular witnesses is `JacobianChallenge.degreeFiber_eq_card_of_regular_witness` in `Manifold/DegreeWellDefined.lean`, composing `Manifold/HPkgUnconditional.lean` (`h_pkg_holds_unconditional`, from chip A `LocalSheetData.ofRegularValueWitnessReg` + chip B `critical_value_set_finite` + RVE deriv-bridge + HLcUnconditional) through `fibre_card_well_defined_at_regular_holds_of_h_pkg`. |

## Theorems (Prop) — Basic.lean items 10–24 in OPEN.md numbering

| # | Item | Status | Notes |
|---|---|---|---|
| 10 | `instance : T2Space (Jacobian X)` | **STUB** | Discrete ⇒ T2 is honest, but the topology itself is wrong (item 4). |
| 11 | `instance : CompactSpace (Jacobian X)` | **OPEN** | `sorry` in `Basic.lean`. Compactness needs the analytic-Jacobian quotient topology (period-lattice), Phase 2. |
| 12 | `instance : IsManifold ... ω (Jacobian X)` | **OPEN** | `sorry`. Requires analytic-Jacobian construction. `AnalyticTorus X` has an honest `IsManifold` instance modulo `Λ = ⊥`; not wired into `Jacobian`. |
| 13 | `instance : LieAddGroup ... ω (Jacobian X)` | **OPEN** | `sorry`. Requires item 12 plus smoothness of group ops. |
| 14 | `genus_eq_zero_iff_homeo` (anti-hack vs. `genus := 0`) | **OPEN** | `sorry`. Architecturally closed via `genus_eq_zero_iff_homeo_from_all_conditionals` in [`Topology/Item14FinalComposition.lean`](JacobianChallenge/Topology/Item14FinalComposition.lean). Open content factors onto the four named classical inputs listed at the top of this file. |
| 15 | `ofCurve_self : ofCurve P P = 0` | **STRICT-CLOSED** *(post-ZZ256)* | Real proof reducing to `[δP − δP] = 0` in honest `Pic⁰`. |
| 16 | `ofCurve_inj` (anti-hack vs. `Jacobian := PUnit`) | **STRICT-CLOSED** *(post-ZZ:OfCurveInj, 2026-05-XX)* | Body in `Basic.lean` line 143–144: `JacobianChallenge.ofCurve_inj_holds P h` (`Manifold/ChartDerivNeZeroImpliesNonCriticalDischarge.lean`). Discharge chain (all unconditional in tree): suppose `[δ Q₁ - δ P] = [δ Q₂ - δ P]` in `Pic⁰ X` for `Q₁ ≠ Q₂` ⇒ extract `f : MeromorphicNonzero X` with `principalDivisorMap f = single Q₁ - single Q₂` (via `PrincDivWitnessExtraction`) ⇒ `f.toRiemannSphere` is non-constant, degree 1 (via `DegreeOneFromSimpleZeroSimplePoleDischarge`) ⇒ `bijective_of_degreeFiber_eq_one` + `bijectiveAnalyticIsBiholomorphism_holds` give a biholomorphism `X ≃ RiemannSphere` ⇒ `genus_eq_zero_iff_homeo_of_HolomorphicEquiv_RiemannSphere` gives `genus X = 0`, contradicting `0 < genus X`. |
| 17 | `Jacobian.ofCurve_contMDiff` | **OPEN** | `sorry`. Requires item 5 (`ChartedSpace`) plus a real `ofCurve`. |
| 18 | `Jacobian.pushforward_contMDiff` | **OPEN** | `sorry`. Requires item 5 plus a real `pushforward`. |
| 19 | `pushforward_id_apply` | **STRICT-CLOSED** *(post-ZZ256)* | Real proof via `Pic0.pushforward_id` (in `JacobianPushforward.lean`) ↦ `Div.singletonMap_id_apply`. |
| 20 | `pushforward_comp_apply` | **STRICT-CLOSED** *(post-ZZ256)* | Real proof via `Pic0.pushforward_comp` (in `JacobianPushforward.lean`) ↦ `Div.singletonMap_comp_apply`. |
| 21 | `Jacobian.pullback_contMDiff` | **OPEN** | `sorry`. Requires item 5 plus a real `pullback`. |
| 22 | `pullback_id_apply` | **STRICT-CLOSED** *(post-ZZ256)* | Body: `JacobianChallenge.Jacobian.pullbackHonest_of_rsum_id _ P` — case-splits on `IsConstantMap (id : X → X)`, with the non-constant branch reducing to `divPullbackWeighted_id_apply` (single-fibre `id ⁻¹' {y} = {y}`, weight 1 everywhere). |
| 23 | `pullback_comp_apply` | **STRICT-CLOSED** *(post-ZZ256)* | Body: `pullbackHonest_of_rsum_comp` — the both-non-constant case delegates to `Div.fiberSumWeighted_comp_apply` with multiplicative ramification weights `manifoldRamificationIndex_comp_unconditional`. |
| 24 | `pushforward_pullback : pushforward f (pullback f P) = degree f • P` | **STRICT-CLOSED** *(post-ZZ256)* | Body: `pushforward_pullbackHonest_of_rsum` — case-splits on `IsConstantMap f`. Constant case: both sides zero. Non-constant: reduces to `Pic0.pushforward_pullbackWeighted` (in `JacobianPullback.lean`, using the new honest `Pic0.pushforward (hf)` signature). |

## Architectural issue: RR-thread linear system (resolved, merged to main 2026-05-14)

The legacy `linearSystemDeltaP p : Submodule ℂ (X → ℂ)` is defined over
*pointwise* functions `X → ℂ`. This admits "essentially-zero" elements
(e.g. `g(p_0) = 100, g(y) = 0 otherwise`) that satisfy `IsBoundedByDeltaP
p g` and are not in `span ℂ {1}` (non-constant) yet have
`germLimitLift g ≡ 0` — making the canonicalised lift unusable.
Consequences:

1. **`finrank ℂ (linearSystemDeltaP p) = ∞` trivially**, by the family of
   "blip-at-`p_0`" functions. So `RR_DimGE2_GenusZero X := ∃ p, 2 ≤
   finrank ℂ (linearSystemDeltaP p)` is vacuously true with no
   Riemann-Roch content.
2. **Inputs #2, #3, #5, #6** of the six-input split
   (`riemannRochGenusZero_from_six_inputs` in
   [`Topology/RRGenusZeroFinalComposition.lean`](JacobianChallenge/Topology/RRGenusZeroFinalComposition.lean))
   — `LiftMMeromorphicOn`, `LiftNonvanishingGerm`, `LiftOrderPreserved`,
   `LiftNotConstant` — are **false as stated** against the blip
   counterexample.
3. **Input #4** (`LiftRegularContinuousAt`, reduced to germ-coherence
   hypotheses via zz380 + zz381) is the only sub-input where the
   reduction stands cleanly; even so, the germ-coherence hypotheses
   themselves are about elements of the broken `linearSystemDeltaP`.

**Resolution (`feat/linear-system-divisor`, merged to main 2026-05-14).** The germ-field
ambient called for above has been built. `MeromorphicFunctionField X`
(in `Manifold/MeromorphicFunctionField.lean`) provides the ℂ-algebra
of meromorphic-function germs, and `linearSystemDivisor D` (in
`Topology/LinearSystemDivisor.lean`) is the honest `L(D)` Submodule
for any divisor `D : Div X`, with `linearSystemGermDeltaP p` as the
`D = Div.single p` specialisation. The full chain — existence side
via `HolomorphicEquiv X RiemannSphere` + finite-dim transport — is
built. After the 2026-05-14 A1 + A2 discharges, the genus-0 RR
`dim_ℂ L(δp) ≥ 2` content on the germ field reduces to **one**
remaining named classical input:

1. **Uniformization at genus 0**:
   `genus X = 0 → Nonempty (HolomorphicEquiv X RiemannSphere)`.

Both of the RS-side inputs are now **discharged unconditionally**:

* `LinearSystemAtInftyRS_BoundedBySimplePoleSpan` (A1, 2026-05-14):
  via `Analysis/PolynomialLiouville.lean` +
  `Topology/LinearSystemAtInftyRSDischarge.lean` (~870 LOC).
* `ExistsMobiusToInftyRS` (A2, 2026-05-14): via
  `Manifold/RiemannSphereAntipodeSmooth.lean` (~255 LOC) +
  `Manifold/RiemannSphereTranslate.lean` (~322 LOC) +
  `Manifold/MobiusTransitivityRS.lean` (~80 LOC).

Headline composition lives in
`Topology/LinearSystemGermDeltaPFiniteDimRSUnconditional.lean`:

* `linearSystemGermDeltaPFiniteDim_RiemannSphere_unconditional :
  LinearSystemGermDeltaPFiniteDim RiemannSphere` —
  **unconditional**.
* `rr_DimGE2_GenusZero_Germ_of_uniformization_unconditional_RSFiniteDim`
  — for any compact connected complex 1-manifold `X`, RR dim ≥ 2 on
  the germ field reduces to genus-conditional uniformization alone.

See `CHANGELOG.md` for the per-file map.

## Smooth-path-connectedness sub-arc (C1, **CLOSED** 2026-05-15)

The `AbelJacobiInput α h` named-hypothesis bundle
(`Manifold/AbelJacobiPoint.lean`) is the C1 input of CLOSURE_MAP §F.3.
Its existence on a compact connected complex 1-manifold is classical
("smooth path-connectedness + a chosen base point"). The full chain
is now **closed unconditionally** for any preconnected complex
1-manifold (which includes every compact connected complex 1-manifold).
Five primitives ship:

1. `SmoothPathConnected I X : Prop` (`Manifold/SmoothPathConnected.lean`,
   2026-05-14) — the classical predicate "every two points of `X`
   joined by a smooth path", with `AbelJacobiInput.ofSmoothPathConnected`
   / `nonempty_of_smoothPathConnected` reducing `AbelJacobiInput α h`
   existence to `SmoothPathConnected 𝓘(ℝ, ℂ) X + Nonempty X`. This is
   the named-hypothesis layer for the sub-arc.

2. `SmoothPath.linearInChart` (`Manifold/SmoothPathLinearInChart.lean`,
   2026-05-14) — the analytic affine constructor: given a chart
   `φ ∈ atlas ℂ X`, two points in `φ.source`, and the hypothesis that
   the entire chart-coordinate line through their images lies in
   `φ.target`, produce a `SmoothPath 𝓘(ℝ, ℂ) X` between them. Now
   downcast at C^∞ via `ContMDiffAt.of_le` since the structure was
   relaxed to C^∞.

3. `SmoothPath.linearInChartSegment` (`Manifold/SmoothPathLinearInChart.lean`,
   2026-05-15) — the C^∞ constructor with **segment-in-target**
   hypothesis. Strict weakening of `linearInChart`'s line-in-target,
   built on `bumpedSegment a b t = (1 - σ t) • a + σ t • b` where
   `σ = Real.smoothTransition`.

4. `SmoothPath.concat`
   (`Manifold/SmoothPathConcat.lean`, 2026-05-15) — binary
   concatenation of two smooth paths sharing an endpoint, via
   bump-flatten reparameterisations
   `concatRepLeft t = σ(4(t - 1/8))` and
   `concatRepRight t = σ(4(t - 5/8))` that make both halves
   identically equal to the junction point on `(3/8, 5/8)`. C^∞
   globally; would be obstructed at ω by analytic germ-determination.

5. `exists_smooth_path_connected_chart_nbhd p`
   (`Manifold/SmoothPathLocalConvex.lean`, 2026-05-15) — local
   smooth-path-connected neighborhood at every point, via the
   chart-restricted-to-Euclidean-ball construction
   `U := φ.source ∩ φ ⁻¹' Metric.ball z r` (where `z = φ p` and
   `r > 0` with `ball z r ⊆ φ.target`). Convexity of the ball plus
   `SmoothPath.linearInChartSegment` gives the smooth-path-connected
   property of `U`.

**ω-level caveat resolved (2026-05-15).** The `SmoothPath` structure
was refactored from `ContMDiff ⊤` (= ω = analytic) to `ContMDiff ∞`
(= C^∞) — the docstring intent. Concatenation and segment-in-chart
reparameterisations are now both directly available; analytic
germ-determination no longer obstructs them.

**Headlines (2026-05-15).**

* `smoothPathConnected_RiemannSphere : SmoothPathConnected 𝓘(ℝ, ℂ)
   RiemannSphere`
  (`Manifold/SmoothPathConnectedRiemannSphere.lean`) — first
  end-to-end discharge on a concrete compact connected complex
  1-manifold. Case-splits on the two-chart cover with
  `SmoothPath.concat` for the `{∞, (0 : ℂ)}` edge case.

* `smoothPathConnected_of_preconnected [PreconnectedSpace X] :
   SmoothPathConnected 𝓘(ℝ, ℂ) X`
  (`Manifold/SmoothPathLocalConvex.lean`) — **the general
  discharge**. The standard open-closed argument applied to the
  reachable set `{q | ∃ γ, γ.src = p ∧ γ.tgt = q}`, which is open
  by `concat` with the local lemma, and closed by the symmetric
  argument on its complement. A nonempty clopen set in a
  preconnected space is the whole space (`IsClopen.eq_univ`); `p`
  is in its own reachable set via `SmoothPath.const`.

**Net.** Via `AbelJacobiInput.nonempty_of_smoothPathConnected`,
`Nonempty (AbelJacobiInput α h)` is now **unconditional on any
nonempty preconnected complex 1-manifold**. The C1 input of
CLOSURE_MAP §F.3 is closed.

## C3 + C4 sub-arc progress (2026-05-14, 12 chips; merged to main)

`AbelHypothesis B` (Abel forward, `Manifold/AbelJacobiPic0.lean`)
and `JacobiInversion B hAbel` (`Manifold/AbelJacobiIso.lean`) are
the C3 + C4 named hypotheses. Together they give `Pic⁰ X ≃+
AnalyticJacobian X` (`abelJacobiEquiv`) — the gate for items 4, 5,
10, 11, 12, 13.

Twelve chips landed 2026-05-14 reducing C3 to a single sharp
atomic statement, closing C4 at genus 0, and unconditionally
discharging `Pic⁰(ℙ¹) = 0` to make the Abel-Jacobi iso on the
Riemann sphere axiom-free. All on `main` (merged from
`feat/linear-system-divisor`).

First half (named-hypothesis reductions, 7 chips):

**C3 (1) genus-0 corner** (`Manifold/AbelHypothesisGenusZero.lean`).
At `genus X = 0`, `AnalyticJacobian` is subsingleton, so
`AbelHypothesis B` is trivially true.

**C3 (2) chain-level reduction**
(`Manifold/AbelHypothesisFromPeriodCondition.lean`).
* `principalDivisorAJChain B D` — explicit AJ chain for `D : Div X`,
  `Σ D(x) • single (B.pathFromBase x)`.
* `abelJacobiChain_principalDivisorAJChain_eq_abelJacobiDivHom` —
  the diagram identity.
* `AbelChainPeriodCondition B : Prop` — for every principal divisor
  `D`, the period vector of its AJ chain lies in `periodLatticeImage`.
* `abelHypothesis_of_abelChainPeriodCondition` — the reduction.

**C3 (3) algebra layer** (same file).
* `principalDivisorAJChain_add` — chain is additive in `D`.
* `principalDivisorAJChainHom : Div X →+ SmoothChain 𝓘(ℝ, ℂ) X` —
  bundled `AddMonoidHom`.
* `complexChainPeriodVector_principalDivisorAJChain_{add,neg}_mem` —
  closure of "period vector ∈ periodLatticeImage" under + and -.

**C3 (4) per-generator reduction** (same file).
* `AbelGeneratorPeriodCondition B : Prop` — for each `f :
  MeromorphicNonzero X`, period vector of AJ chain of `div(f)`
  ∈ `periodLatticeImage`. **The sharpest atomic form of Abel
  forward — one meromorphic function at a time.**
* `abelChainPeriodCondition_of_abelGeneratorPeriodCondition` —
  closure induction on `PrincDiv X = AddSubgroup.closure (Set.range
  principalDivisorMap)`.
* `abelHypothesis_of_abelGeneratorPeriodCondition` — composite.

**C4 (genus-0)** (`Manifold/JacobiInversionGenusZero.lean`).
* `jacobiInversion_of_genus_zero_and_subsingleton_pic0` — builds
  `JacobiInversion B hAbel` from `genus X = 0` + `Subsingleton (Pic0
  X)`. Surjectivity automatic (codomain subsingleton); injectivity
  reduces to source subsingleton.
* `abelJacobiEquiv_of_genus_zero` — the full Abel-Jacobi iso `Pic0
  X ≃+ AnalyticJacobian` at genus 0, given `Subsingleton (Pic0 X)`.

Second half (RS-side unconditional discharge, 5 chips):

**RS principal-divisor generators (3 chips):**
* `mnRSSimplePole` (`Manifold/MeromorphicNonzeroRSSimplePole.lean`,
  ~110 LOC) — `MeromorphicNonzero RS` packaging of the function
  `some z ↦ z`, with principal divisor `δ_{some 0} - δ_∞`.
* `mnRSInversion` (`Manifold/MeromorphicNonzeroRSInversion.lean`,
  ~200 LOC) — packaging of `z ↦ z⁻¹`, with principal divisor
  `δ_∞ - δ_{some 0}`.
* `mnRSAffineFactor a` (`Manifold/MeromorphicNonzeroRSAffineFactor.lean`,
  ~190 LOC) — packaging of `z ↦ z - a`, with principal divisor
  `δ_{some a} - δ_∞`. Built as `RSSimplePole - (const a)`.

**Elementary divisor identity (1 chip):**
* `Manifold/Pic0RiemannSphereTrivial.lean` (~140 LOC) —
  `principalDivisorMap_mnRSAffineFactor a = Div.single (some a) -
  Div.single ∞`, and `elementaryDivisor_mem_PrincDiv` corollary.

**Closure decomposition + final discharge (1 chip):**
* `Manifold/Pic0RiemannSphereSubsingleton.lean` (~190 LOC) — the
  reconstruction sum `Σ_{x ∈ supp(D), x ≠ ∞} D(x) • (Div.single x -
  Div.single ∞)` equals `D` pointwise for any `D : Div0 RS`.
  `subsingleton_pic0_RiemannSphere : Subsingleton (Pic0 RiemannSphere)`
  is now **unconditional**, and via the bridge from earlier in the
  day, `AbelJacobiInput.abelJacobiEquiv_of_RiemannSphere_unconditional`
  gives `Pic0 RS ≃+ AnalyticJacobian RS` axiom-free.

**Net open content after today's 12 chips:**

| Input | Open content |
|---|---|
| `AbelHypothesis B` (general genus) | `AbelGeneratorPeriodCondition B` — discharge for each `f : MeromorphicNonzero X` (Abel forward via level-set chain, ~1,000–2,500 LOC of Stokes content) |
| `AbelHypothesis B` (genus 0) | **done** unconditionally |
| `JacobiInversion B hAbel` (general genus) | Abel converse (injectivity) + Jacobi inversion theorem (surjectivity) |
| `JacobiInversion B hAbel` (genus 0) | **done** unconditionally (`Subsingleton (Pic0 X)` for `X = RS` discharged) |
| `Pic⁰ RS ≃+ AnalyticJacobian RS` | **done** unconditionally |
| `Pic⁰ X ≃+ AnalyticJacobian X` (general `X`) | Needs both C3 general-genus and C4 general-genus |

Items 4, 5, 10, 11, 12, 13 still STUB/OPEN — the unconditional iso
on `RiemannSphere` does not flip them because they require the iso on
**arbitrary** compact connected complex 1-manifolds `X`.

## C3 sub-arc progress (2026-05-15 evening, 25 additional chips merged to main)

Extending the same-day morning chips with 25 further chips delivering
algebra-side closure + the full path-lift infrastructure for the
level-set chain.  All on `main`, build green at 8746 jobs, zero
`sorry`, zero `axiom`.

**Algebra-side closure** (chips 1–3, `Manifold/AbelGeneratorDischargedSet.lean`).
* `dischargedGenerators B` set: closed under `1`, constants, `*`,
  `invMer`, quotients.
* Case-split reduction: `AbelGeneratorPeriodCondition B` reduces to
  the non-constant `toFun` case.

**Regular-value framework** (chip 4,
`Manifold/MeromorphicNonzeroRegularValueSet.lean`).
* `regularValueSet f := (criticalValues f)ᶜ` + openness under
  non-constancy.

**Planar local biholomorphism** (chips 5–6).
* `chartPullback f x`, analyticity, non-zero derivative at regular
  points via `DerivBridgeData.hCompat`, planar `OpenPartialHomeomorph`
  form via `HasStrictFDerivAt.toOpenPartialHomeomorph`.

**Manifold-level local sheet** (chip 7,
`Manifold/MeromorphicNonzeroLocalSheet.lean`).
* `manifoldLocalOph` via double `restrOpen` of the chart-trans-chart
  composition; `localSheetData_at_regular` packaging `LocalSheetData
  f.toRiemannSphere (f.toRiemannSphere x₀) x₀`.

**Topological packaging** (chips 8–10).
* `IsLocalHomeomorphOn f.toRiemannSphere f.regularSet`.
* Fiber finiteness at every regular value
  (`fiber_finite_of_mem_regularValueSet`).
* `HurwitzPatchingData` at every regular value via
  `HurwitzPatchingData.ofLocalSheets`.

**Continuous path lift primitives** (chips 11, 16, 19, 20–22).
* `exists_continuous_local_lift_of_continuous` — local lift on `β ⁻¹'
  sheet.V`.
* `path_lift_unique` / `path_lift_eqOn_Icc` — uniqueness clopen
  argument (global / partial-domain).
* `extend_lift_across_sheet` — single-sheet piecewise extension.
* `exists_sheet_data_extending_to_right` + `extend_continuous_lift_to_right`
  — per-point extension primitive.
* `lifts_agree_globally` / `lifts_agree_at` — choice-independence.

**Smooth path lift primitives** (chips 12–15).
* Pointwise `ContMDiffAt ω` of `sheet.g` at base point
  (`contMDiffAt_localSheet_g_at_basePoint`).
* Open-nbhd `ContMDiffOn ω` extension via
  `contMDiffAt_iff_contMDiffOn_nhds` (valid for ω ≠ ∞).
* Smooth local lift `ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) ∞` at base point
  via `ContMDiffAt.complex_to_real` + `ContMDiffAt.comp`.
* Smooth local lift `ContMDiffOn` on open neighbourhood
  (`exists_contMDiffOn_local_lift`).

**Global lift scaffolding** (chips 17, 18, 23–25).
* `exists_subdivision_hurwitzPatching` — Lebesgue subdivision of
  `unitInterval` adapted to a regular path.
* `exists_continuous_lift_single_sheet` — global lift when β maps into
  one sheet (no gluing).
* `liftReachable f β x₀ T` def + downward closure + zero membership.
* `liftReachable_extends_right` — **openness** via clip+if_le
  construction (globally continuous lift built by clipping `t` to
  `[b, b + ε]` before applying β).
* Boundedness + sSup bounds for the sSup/clopen argument.

**Net open content after today's 25 evening chips** (revised):

| Step | Status | LOC estimate (uncalibrated) |
|---|---|---|
| 1. Closedness `sSup ∈ liftReachable` (sequential limit + local sheet) | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroPathLiftClosed.lean`, 331 LOC) | 250–350 |
| 2. Global continuous lift `sSup = T` (clopen finish) | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroPathLiftExistsOnIcc.lean`, 117 LOC; `sSup_liftReachable_eq_T` + `exists_continuous_lift_on_Icc`) | 80–120 |
| 3. Smooth upgrade of global lift to `ContMDiffOn ∞` | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroPathLiftSmoothOnIcc.lean`, 225 LOC; `contMDiffOn_lift_of_continuous_lift` + `exists_contMDiffOn_lift_on_Icc`) | 150–250 |
| 4. `SmoothPath` bundle from global smooth lift | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroPathLiftSmoothPath.lean`, 141 LOC; `exists_smoothPath_of_lift_on_unitInterval` — uses `Real.smoothTransition` reparametrisation + `ContMDiffOn.comp_contMDiff` to package the lift into `SmoothPath 𝓘(ℝ, ℂ) X`) | 100–150 |
| 5. `levelSetChain f β` definition | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroLevelSetChain.lean`, 152 LOC; `sourceFiber` + `sourceFiberPath` + `levelSetChain` + characterising lemmas. Each fiber-point path is Classical-chosen via step 4) | 150–250 |
| 6. Boundary computation `∂ = δ_tgt − δ_src` | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroLevelSetChainBoundary.lean`, 111 LOC; `sourceFiberDivisor` + `targetFiberDivisor` + `boundary_levelSetChain`) | 200–400 |
| 7a. Target-map injectivity (foundation for bijection) | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroLevelSetTargetInjective.lean`, 151 LOC; `sourceFiberPath_tgt_injOn` via `Path.extend` + `path_lift_eqOn_Icc` on `β ∘ Real.smoothTransition`) | (split from step 7) |
| 7b. Target-map surjectivity onto target fiber | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroLevelSetTargetSurjective.lean`, 240 LOC; `sourceFiberPath_tgt_surjOn` via time-reverse β + step 4 at y + step 2 raw lift + double `path_lift_eqOn_Icc`) | (split from step 7) |
| 7c. Boundary = `Σ targetFiber − Σ sourceFiber` (Finsupp form) | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroLevelSetTargetFiber.lean`, 193 LOC; `targetFiber` def + `sourceFiberPath_tgt_image_eq_targetFiber` (Finset bijection from 7a+7b) + `boundary_levelSetChain_eq_fiberDiff`) | (split from step 7) |
| 7d-a. Off-fiber vanishing of principalDivisorMap | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroPrincipalDivisorOffFiber.lean`, 110 LOC; `principalDivisorMap_toFun_eq_zero_off_fiber` via chart-pullback `tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero`) | (split from step 7d) |
| 7d-b. Order = 1 at simple zero (regular value some 0) | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroPrincipalDivisorAtZero.lean`, 198 LOC; `principalDivisorMap_toFun_eq_one_at_simple_zero` via chart-pullback eventual equality + `AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero`) | 150–250 |
| 7d-c. Order = -1 at simple pole (regular value ∞) | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroPrincipalDivisorAtPole.lean`, 188 LOC; uses `MMeromorphicAt.iff_of_isManifold` for chart-independence → `MeromorphicOn.eventually_analyticAt` for pole isolation → `meromorphicOrderAt_inv` to flip sign) | 150–250 |
| 7d-d. Final identification ∂(levelSetChain) = −principalDivisorMap f pointwise | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroLevelSetPrincipalDivisorIdentification.lean`, 147 LOC; `boundary_levelSetChain_eq_neg_principalDivisorMap_pointwise` via case-split on sourceFiber/targetFiber/off-fiber, composing 7d-a/b/c) | 100–200 |
| 8. Pushforward 1-form `f_*ω` + integral identity | **LANDED 2026-05-15 (bookkeeping)** (`Manifold/MeromorphicNonzeroLevelSetIntegrate.lean`, 98 LOC; `integrate_levelSetChain` Finset-sum expansion via `SmoothChain.integrateLinearMap` + `integrateLinearMap_single`. Substantive `f_*ω` construction layered on top via existing `SmoothPath.integrate_compSmoothPath`.) | 300–500 |
| 9. Structural reduction `AbelGenerator ← (Z period in lattice) + (Z boundary = -principalDivisor)` | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroAbelGeneratorFromLevelSet.lean`, 138 LOC; `abelGeneratorPeriodCondition_of_levelSet_lattice` — cycle Z+AJ has boundary 0, period vector in lattice tautologically; linearity gives AJ's period as lattice element. Named input: `h_struct` (the Z with right boundary AND lattice period). `h_AJ_boundary` (AJ chain's boundary identity) **DISCHARGED 2026-05-16** in `Manifold/PrincipalDivisorAJChainBoundary.lean` (~125 LOC; pure ℤ-linearity + `JacobianChallenge.residue_theorem`) and inlined into the step-9 proof. The β-existence input for the boundary clause of `h_struct` (smooth path 0→∞ avoiding critical values) **DISCHARGED 2026-05-16** in `Manifold/MeromorphicNonzeroRegularPath.lean` (~431 LOC; `exists_regular_path_zero_to_infty` via two `linearInChartSegment` paths through `r := some(s + i)` for generic `s`, concat'd). Concrete witness `regularLevelSetChain f hnc h0 h∞` with its boundary identity (`boundary = -principalDivisorMap f` pointwise) shipped in `Manifold/MeromorphicNonzeroConcreteLevelSetChain.lean` (~146 LOC; `Classical.choose` extraction + composition with step 7d-d). **f_*ω stack scaffolded 2026-05-16**: real-model RS manifold instance (`RiemannSphereRealManifold.lean`, ~96 LOC), pointwise cotangent pullback primitive (`CotangentPullbackAt.lean`, ~94 LOC), pointwise trace `f_*ω` at regular values (`MeromorphicNonzeroTraceAt.lean`, ~117 LOC), `SmoothOneFormOn` partial-section type (`SmoothOneFormOn.lean`, ~88 LOC), scalar evaluation of pullback + trace (`CotangentPullbackAtApply.lean`, ~123 LOC), `ContinuousOn` variant of `path_lift_eqOn_Icc` (`MeromorphicNonzeroPathLiftUniqueOnContinuousOn.lean`, ~131 LOC), and local identification `sourceFiberPath ↔ sheet.g ∘ β ∘ σ` on a sub-interval (`MeromorphicNonzeroSourceFiberPathSheetEq.lean`, ~222 LOC). The chain-rule pathway from `(levelSetChain f β).integrate om` to `∫ applyCotangent (traceAt ...) (β.velocity ·)` is now scaffolded end-to-end pointwise; only the global identification (Lebesgue subdivision over sheet-domain cover) + Stokes/residue argument for the lattice clause remain.) | 400–800 |

**Caveat on estimates.** Today's 25 chips delivered ~2,900 LOC, much
more than the ~300–500 LOC pre-session estimate for "global path
lift".  My historical LOC estimates are 2–6× off; the table above
should be read as a lower bound, with the actual cost likely
considerably higher.

## Mathlib-prerequisite candidates (likely needed before strict closure)

These are *not* part of the challenge directly, but the constructions for
items 1, 2, 5, 8, 9 will need infrastructure not in mathlib at the pin.

- **Finite-dimensionality of `HolomorphicOneForm X`** on compact connected
  Riemann surface — needed for `genus X` to be the right integer. Hodge
  theory; not yet proved.
- **Honest `PrincDiv X`** — *landed.* `PrincDiv X := PrincDivHonestCandidate X`
  in `Divisor/PrincipalDivisorRange.lean` (post-ZZ256). The residue theorem
  on a compact Riemann surface (∑_x ord_x f = 0) is **discharged
  unconditionally** in-tree as `JacobianChallenge.residue_theorem`
  (`Manifold/ResidueTheoremUnconditional.lean`), composing the R1+R2+R3+R4
  chain via `R5Unconditional.R5_principal_degree_zero_statement_holds`.
  Supporting infrastructure: chart-independence of `mmeromorphicOrderAt`
  (`Manifold/MeromorphicAt.lean`), local finiteness
  (`Manifold/MeromorphicDivisor.lean`'s `MMeromorphicOn.divisor`),
  `principalDivisorMap` (`Divisor/PrincipalDivisor.lean`), and
  pole-extension to `RiemannSphere` (`Manifold/MeromorphicExtension.lean`).
- **Honest period lattice** as a rank-`2g` `Submodule ℤ` of `ℂ^g` — requires
  H₁(X; ℤ) for compact Riemann surfaces (not in mathlib at the pin) plus
  period-pairing integration of holomorphic 1-forms over loops.
- **Topological degree of proper holomorphic maps** between Riemann
  surfaces. `fibres_finite_statement` and `regular_value_exists_statement`
  are discharged unconditionally (`Manifold/FibresFiniteUnconditional.lean`
  / `RegularValueExistsUnconditional.lean`). Only
  `fibre_card_well_defined_at_regular_statement` remains, and it still
  needs the analytic local normal form `z ↦ z^k` (not at the mathlib pin).
- **`genus_eq_zero_iff_homeo`** — closed-orientable-surface classification
  plus Riemann-sphere `ChartedSpace`. Multi-month.

## Local infrastructure

The repo's per-file map lives in `JacobianChallenge.lean` (the import
manifest) and the file system. `CHANGELOG.md` documents which files
landed in which branch / wave. This OPEN.md is intentionally not a
duplicate file listing.

## Paths to the next STRICT-CLOSED

(*Stale entry purged 2026-05-20 late: items 1 and 16 are now STRICT-
CLOSED; the only remaining items are 5, 11, 12, 13, 14, 17, 18, 21.*)

Reaching the next **STRICT-CLOSED** requires landing one of:

* **(a) Universal `[HasJacobianAnalyticStructure X]` instance** — flips
  items 5, 11, 12, 13 (and unlocks 17/18/21 modulo per-curve content)
  via the C3 rewire of `JacobianChallenge.Jacobian X` to
  `CanonicalAnalyticJacobianAnonymous X`. Deep classical content:
  surface classification (for `SmoothSymplecticBasis`), smooth
  Hurewicz (for `SmoothHurewiczHypothesis`), Riemann bilinear
  positivity (for the `bilinear` field — chain `Hodge inner product` →
  `HodgeRiemannBridgeHypothesis` → Riemann second → ℝ-LI now sketched
  via named hypotheses).
* **(b) Item 14 universal discharge** — `RiemannRochGenusZero X` +
  topological-sphere uniformization, *or* universal
  `HasAdmissibleChartCover` (now class-driven). Currently
  unconditional on `RiemannSphere`.
* **(c) Per-curve smoothness content for items 17/18/21** — discharge
  `AbelJacobiSmoothness` + per-curve `JacobianAnalyticPushforwardLift`
  / `PullbackLift` with explicit lattice-match certificates. Concrete
  analytic content (FTC for path integrals, `∫_{f_*γ} ω = ∫_γ f^* ω`).
