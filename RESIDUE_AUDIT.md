# Residue Theorem Sub-Tree Audit

Date: 2026-05-23
Auditor: Claude (Opus 4.7 1M, Bryan Sanchez session, read-only audit)
Worktree: `/Volumes/4TB SD/ClaudeCode/jacobian-lean-challenge-item14`
Branch: `feat/item14-classical-content` @ `ee786d2`

Scope: 46 files under `JacobianChallenge/Manifold/` matching the residue /
Stokes / chart-circle patterns named in the audit brief, plus
`JacobianChallenge/Divisor/PrincipalDivisorRange.lean` (the definitional
home of `ResidueTheorem X`). All files inspected via docstrings, top-level
declaration lists, and targeted reads of the key statement / discharge
points. No `lake build` was run.

---

## TL;DR — the audit brief's premise is wrong

> The audit brief told me to trace `ResidueTheorem X` at
> `JacobianChallenge/Divisor/PrincipalDivisorRange.lean:237` as the
> "currently a named hypothesis" leaf the 40+ residue/Stokes files do not
> close.

**`ResidueTheorem X` is already unconditionally discharged in tree** via a
topological-degree (Route A / Hurwitz) chain that does **not** go through
any file in this sub-tree. The chain is:

```
JacobianChallenge.residue_theorem
  (Manifold/ResidueTheoremUnconditional.lean:39)
→ ResidueTheorem.R5_principal_degree_zero_statement_holds
  (Manifold/R5Unconditional.lean:58)
→ R4FibreSumBalance.residue_theorem_unconditional
  (Manifold/R4FibreSumBalance.lean — closes R4 by Hurwitz fibre sum)
→ ramificationSumEqualsDegree_holds_unconditional
  (Manifold/NearbyRegularWitnessUnconditional.lean:1165)
→ nearbyRegularWitnessHypothesis_holds_unconditional
  (same file, via genuine k-fold manifold count + disjoint-fibre nbhds
   + critical-values-finite + preimage-eventual-containment)
```

None of the 46 files in this audit's scope appears on that chain. Every
file in the sub-tree is one of:

1. The Route-B (Stokes / contour integration) **parallel route** that
   bundles a hypothesis (`SumOfResiduesPartitionOfUnity_hypothesis`,
   `StokesResidueTheorem_statement`, `TopologicalDegreeFibreBalance_hypothesis`,
   `GlobalResidueSum_hypothesis`, `ChartCircleSumZero_hypothesis`, etc.)
   and shows the same already-discharged `ResidueTheorem X` follows from it.
2. Substantive mathlib-grounded analytic lemmas (`StokesDiskClosedForm`,
   `CircleResidue.chartCircleIntegral_of_coeff_eq_finite_laurent`,
   `PlanarAnnulusCircleIntegral.*`) that are **correct, real classical
   content** but feed only the parallel-route bundles, not the in-tree
   headline.
3. A pile of `C3PeriodLatticeStokes*` files that have nothing to do with
   the residue theorem at all — they are Period Lattice Stokes Span
   chips for the **separate** C3 program (Riemann bilinear / Abel /
   Jacobi). They got matched because they contain the substring
   "Stokes".

Both downstream-of-Basic-sorry users (`Basic.lean:195`,
`JacobianPullbackHonest`, `DegreeOneInjective*`, etc.) consume
`ramificationSumEqualsDegree_holds_unconditional` **directly**, not via
`ResidueTheorem X`. The deep audit's claim that "40+ residue/Stokes files
do NOT yet close `ResidueTheorem X`" is true but irrelevant — those files
were never on the critical path. They are Route-B parallel-route bloat.

This is exactly the anti-pattern documented in `tools/chip-prompt-preamble.md`
(parallel routes to an already-closed conclusion are net-negative).

---

## Per-file classifications

Sorry-discipline note: every file in the sub-tree is **sorry-free and
axiom-free in actual code**. `grep '\bsorry\b'` matches are universally
inside docstrings ("no `sorry`, no `axiom`" disclaimers). Gaps are
encoded as `def Prop` or `structure ... where` named hypotheses, not as
`sorry` literals. So "sorry count" in the per-file headers below is the
literal grep count; the **structural** gap is the bundled hypothesis
listed under "Owed".

Category legend:
- **SUBSTANTIVE** — proves a real classical theorem from mathlib primitives.
- **REDUCTION** — composes existing pieces, no new content.
- **PARAPHRASE** — rename / "from N inputs" / parallel route / per-X chip.
- **HYPOTHESIS-DEF** — defines a new `def Prop`/`structure` hypothesis without substantive proof.
- **DOC/INDEX** — pure docs or umbrella import file.

### Group 1 — Residue-theorem core (Route A skeleton + Route B parallel)

#### `JacobianChallenge/Manifold/ResidueTheorem.lean` — 266 LOC, sorry=0
**Category: REDUCTION + DOC.** Declares five named statements `R1`–`R5`
(`R1_poleExtension_statement`, `R2_fibres_finite_statement`,
`R3_localMultiplicity_statement`, `R4_fibreSum_balance_statement`,
`R5_principal_degree_zero_statement`) and the conditional discharge
`residue_theorem_of_routeA`. All five are discharged in
`ResidueTheoremFromRsum.lean` + `R4FibreSumBalance.lean`. The file's
"Sketch of Route B (Stokes / contour integration)" section is
explicitly labelled "not implemented" — yet the rest of this audit's
sub-tree is exactly the Route-B attempt.
- Top-level decls: `R1_poleExtension_statement`, `R2_fibres_finite_statement`, `R3_localMultiplicity_statement`, `R4_fibreSum_balance_statement`, `R5_principal_degree_zero_statement`, `residue_theorem_of_routeA`.
- Owed: nothing — all five named statements have unconditional discharge files elsewhere.

#### `JacobianChallenge/Manifold/ResidueTheoremUnconditional.lean` — 51 LOC, sorry=0
**Category: REDUCTION.** One theorem (`residue_theorem`) consuming
`R5_principal_degree_zero_statement_holds`. The actual headline.
- Top-level decls: `residue_theorem`.
- Owed: nothing.

#### `JacobianChallenge/Manifold/ResidueTheoremFromRsum.lean` — 418 LOC, sorry=0
**Category: REDUCTION (heavy).** Discharges `R1`, `R2`, `R3`, and the
`R5 of R4` step. Also provides `residue_theorem_of_R4` and the
`R5_iff_ResidueTheorem` / `R5_iff_forall_zeroCount_eq_poleCount` bridges.
This is the substantive Route-A discharge of three of the five R-leaves.
- Top-level decls: `untop₀_lt_zero_iff_lt_zero`, `untop₀_nonneg_iff_nonneg`, `untop₀_pos_iff_pos`, `R1_poleExtension_statement_holds`, `R2_fibres_finite_statement_holds`, `R3_localMultiplicity_statement_holds`, `R5_principal_degree_zero_statement_of_R4`, `residue_theorem_of_R4`, `R5_iff_ResidueTheorem`, `R5_iff_forall_zeroCount_eq_poleCount`.
- Owed: nothing — composes `MeromorphicExtension` / `MeromorphicDivisor` infrastructure.
- **Note**: this is the only file in the audit scope that's actually on the unconditional path. It is REDUCTION but at the right granularity — composes mathlib + in-tree analytic machinery into the named statements.

#### `JacobianChallenge/Manifold/ResidueTheoremAssembly.lean` — 324 LOC, sorry=0
**Category: PARAPHRASE (parallel route).** Defines a structure
`SumOfResiduesPartitionOfUnity_hypothesis` (5-field bundle: per-point
chart integers, support-finiteness, per-point order identification,
global-sum-zero) and shows `ResidueTheorem_holds_of_hypothesis`. Same
target as the already-unconditional headline; the bundle reduces
`ResidueTheorem X` to one named field plus a per-point identification.
- Top-level decls: `SumOfResiduesPartitionOfUnity_hypothesis` (structure), `degree_principal_eq_sum_residueAt`, `degree_principal_eq_sum_orderFun`, `sumOfResidues_eq_zero_of_hypothesis`, `principalDivisor_degree_eq_zero_of_hypothesis`, `ResidueTheorem_holds_of_hypothesis`, `PrincDivHonestCandidate_le_Div0_of_hypothesis`.
- Owed: the `global_sum_zero` field of the structure (named bundled gap).
- Verdict: classic "from N inputs" reformulation. Imported by 3 files all inside the same parallel-route arc.

#### `JacobianChallenge/Manifold/ResidueTheoremStokes.lean` — 383 LOC, sorry=0
**Category: PARAPHRASE (parallel route).** Defines
`StokesResidueTheorem_statement` and `ResidueTheorem_statement` (each a
`def Prop`), proves they are `Iff` to each other and to `R5`.
`logDiff_statement` is literally `def logDiff_statement (_f) : Prop := True`
— a placeholder. The whole file is bridging parallel-route names.
- Top-level decls: `logDiff_statement`, `residueAt`, `StokesResidueTheorem_statement`, `ResidueTheorem_statement`, `residueTheorem_statement_eq_R5`, `principalDivisor_supportFinset_eq`, `stokesResidueTheorem_iff_residueTheorem`, `stokesResidueTheorem_iff_R5`.
- Owed: a placeholder `True` (`logDiff_statement`) plus the bundled `StokesResidueTheorem_statement`. Imported by 3 files.

#### `JacobianChallenge/Manifold/ResidueViaTopologicalDegree.lean` — 297 LOC, sorry=0
**Category: PARAPHRASE (parallel route).** Defines
`TopologicalDegreeFibreBalance_hypothesis` and shows `ResidueTheorem`
follows from it. Now totally redundant: the actual unconditional Route-A
discharge (via `ramificationSumEqualsDegree_holds_unconditional`)
already lives in `R4FibreSumBalance.lean` and `NearbyRegularWitnessUnconditional.lean`
without needing this hypothesis bundle.
- Top-level decls: `zeroCount`, `poleCount`, `signedMult_eq_zeroCount_sub_poleCount`, `TopologicalDegreeFibreBalance_hypothesis` (structure), `global_sum_zero_via_topological_degree`, `ResidueTheorem_holds_of_topologicalDegreeFibreBalance`, `topologicalDegreeBalance_of_fibreBalance`, `signedMult_zero_of_fibreBalance`.
- Owed: bundle hypothesis. Imported by 4 files.

#### `JacobianChallenge/Manifold/GlobalResidueSum.lean` — 250 LOC, sorry=0
**Category: PARAPHRASE (parallel route, deeper bundle nesting).**
Defines `GlobalResidueSum_hypothesis` (5-field bundle ending in
`global_chain_boundary_eq_zero`) and feeds it into the `S1` bundle of
`ResidueTheoremAssembly`. Net effect: yet another named bundle on top of
the assembly bundle, both of which sit underneath the already-closed
in-tree headline.
- Top-level decls: `GlobalResidueSum_hypothesis` (structure), `globalChainBoundary`, `chain_boundary_decomposition`, `global_sum_zero_of_hypothesis`, `global_sum_zero_witness_for_S1`, `ResidueTheorem_holds_of_globalResidueSum`.
- Owed: `global_chain_boundary_eq_zero` field + `chartIntegral_eq_order` field. Imported by 2 files.

### Group 2 — Chart-circle / Laurent / log-derivative integrals

#### `JacobianChallenge/Manifold/CircleResidue.lean` — 421 LOC, sorry=0
**Category: SUBSTANTIVE + HYPOTHESIS-DEF.** Genuine mathlib-grounded
computation: `chartCircleIntegral_of_coeff_eq_finite_laurent` proves
that the chart-circle integral of a finite Laurent monomial equals its
`(-1)`-coefficient by direct reduction to mathlib's
`circleIntegral.integral_sub_zpow_of_ne` and
`integral_sub_inv_of_mem_ball`. The headline statement
`chartCircleIntegral_eq_residue_statement` (`def Prop`) is left as a
named hypothesis "owed from the local Laurent normal form".
- Top-level decls: `chartCircleIntegral`, `chartCircleIntegral_eq_residue_statement` (def Prop), `chartCircleIntegral_of_coeff_eq_zero`, `chartCircleIntegral_eq_circleIntegral_of_coeff_eq`, `chartCircleIntegral_of_coeff_eq_laurent_monomial`, `circleIntegral_const_mul_zpow_sub_center`, `circleIntegrable_const_mul_zpow_sub_center`, `chartCircleIntegral_of_coeff_eq_finite_laurent`.
- Owed: `chartCircleIntegral_eq_residue_statement` — but **zero downstream consumers** of the named statement (grep finds it only in this file's docstrings). The proven Laurent lemmas are good content; the hypothesis def is orphaned.

#### `JacobianChallenge/Manifold/LogDerivLaurent.lean` — 240 LOC, sorry=0
**Category: HYPOTHESIS-DEF + REDUCTION.** Defines `LogDerivFiniteLaurent`
(a per-point Laurent normal-form hypothesis bundle: `f' / f` is a
finite Laurent series with `(-1)`-coefficient = order). Proves
`chartCircleIntegral_logDeriv_eq_order` and supporting lemmas modulo this
hypothesis. Real content, but consumes a `def Prop` instead of proving it.
- Top-level decls: `LogDerivFiniteLaurent`, `chartCircleIntegral_logDeriv_eq_order`, `canonicalChartIntegral`, `canonicalChartIntegral_eq_order`, `chartIntegral_eq_order_witness`, `chartCircleIntegral_eq_canonicalChartIntegral_cast`.
- Owed: `LogDerivFiniteLaurent` hypothesis bundle. Imported by 1 file.

#### `JacobianChallenge/Manifold/LogDerivLaurentDischarge.lean` — 327 LOC, sorry=0
**Category: PARAPHRASE.** "Discharge" version of LogDerivLaurent that
swaps in `LogDerivResiduePlusAnalytic` — a renamed, smaller-looking
hypothesis bundle (`residue + analytic` instead of `finite Laurent`).
Same content, different decomposition. Classic named-hypothesis rename.
- Top-level decls: `chartCircleIntegral_of_coeff_eq_residue_plus_analytic`, `LogDerivResiduePlusAnalytic`, `chartCircleIntegral_logDeriv_eq_order_of_residue_plus_analytic`, `chartCircleIntegral_eq_canonicalChartIntegral_cast_of_residue_plus_analytic`.
- Owed: `LogDerivResiduePlusAnalytic` hypothesis. **Zero downstream importers.** Dead.

#### `JacobianChallenge/Manifold/PlanarAnnulusCircleIntegral.lean` — 97 LOC, sorry=0
**Category: SUBSTANTIVE.** Two theorems: `circleIntegral_eq_of_holomorphic_on_annulus`
and `circleIntegral_eq_of_continuousOn_closed_differentiableOn_open`.
These are honest mathlib-backed statements about planar circle integrals
on annuli (compose `DiffContOnCl.circleIntegral_eq_zero` with
two-circle-difference rewrites).
- Top-level decls: `circleIntegral_eq_of_holomorphic_on_annulus`, `circleIntegral_eq_of_continuousOn_closed_differentiableOn_open`.
- Owed: nothing. Imported by 3 files.

#### `JacobianChallenge/Manifold/ChartCircleAnchoredAllRadii.lean` — 220 LOC, sorry=0
**Category: REDUCTION.** Four theorems anchoring the chart-circle
integral across a range of radii, given a regular-annulus witness.
Genuine composition of `PlanarAnnulusCircleIntegral` + chart pullbacks.
- Top-level decls: `chartCircleIntegralAnchored_eq_order_via_regular_annulus`, `chartCircleIntegralAnchored_eq_order_for_all_valid_radius`, `chartCircleIntegralAnchored_eq_order_of_regular_annulus_to_witness`, `exists_radius_chartCircleIntegralAnchored_eq_order`.
- Owed: nothing structurally new, but threads `IsRegularOnAnnulus` from `ChartCircleHomotopyAnnulus`. Imported by 3 files.

#### `JacobianChallenge/Manifold/ChartCircleHomotopyAnnulus.lean` — 161 LOC, sorry=0
**Category: SUBSTANTIVE + REDUCTION.** Defines `IsRegularOnAnnulus`
(predicate) and proves the chart-circle integral is invariant on a
regular annulus. Real content via planar annulus integral lemma.
- Top-level decls: `IsRegularOnAnnulus` (def), `chartCircleIntegralAnchored_eq_of_regular_annulus`.
- Owed: nothing. Imported by 2 files.

#### `JacobianChallenge/Manifold/ChartCircleVanishingRegular.lean` — 126 LOC, sorry=0
**Category: SUBSTANTIVE.** Proves chart-circle integral vanishes on a
regular disk (where `f` is holomorphic and nonvanishing). Direct
application of `DiffContOnCl.circleIntegral_eq_zero`.
- Top-level decls: `IsRegularOn` (def), `chartCircleIntegralAnchored_eq_zero_of_regular`.
- Owed: nothing. Imported by 1 file.

#### `JacobianChallenge/Manifold/ChartCircleSumOrders.lean` — 218 LOC, sorry=0
**Category: REDUCTION.** Two theorems both named `chartCircleSum_eq_sum_orders`
(double-definition pattern — see `grep` output line 20 and line 201).
Composes the anchored-radii theorem with finite-sum bookkeeping.
- Top-level decls: `chartCircleSum_eq_sum_orders` (×2 — same name, different signatures), `chartCircleIntegralAnchored_eq_order_of_isRegularChartDiskAround`.
- Owed: nothing. **Zero downstream importers.** Dead.

#### `JacobianChallenge/Manifold/ChartCircleSumZero.lean` — 212 LOC, sorry=0
**Category: HYPOTHESIS-DEF.** Defines `chartCircleSum` and
`ChartCircleSumZero_hypothesis` (per-chart-disk regularity bundle).
Bookkeeping lemmas about the sum (insertion, congruence) and the
hypothesis's projections (`radius_pos_of_mem`, `chart_target_of_mem`).
Real bookkeeping, but the headline is the hypothesis def.
- Top-level decls: `chartCircleSum` (def), `chartCircleSum_insert_of_not_mem`, `chartCircleSum_congr`, `ChartCircleSumZero_hypothesis` (structure), `ChartCircleSumZero_hypothesis.radius_pos_of_mem`, `ChartCircleSumZero_hypothesis.chart_target_of_mem`.
- Owed: bundle hypothesis. Imported by 3 files.

#### `JacobianChallenge/Manifold/ChartCircleSumZeroDischarge.lean` — 221 LOC, sorry=0
**Category: PARAPHRASE.** Defines a *second* bundle
`ChartCircleSum_globalResidueBridge` to discharge the first; defines
yet a third aligned variant `ChartCircleSumZero_hypothesis_aligned`.
Three bundle definitions, each "discharging" the previous, none
proving classical content.
- Top-level decls: `ChartCircleSum_globalResidueBridge` (structure), `chartCircleSum_eq_zero_of_globalResidueSumBridge`, `ChartCircleSumZero_hypothesis_aligned` (def), `chartCircleSum_eq_zero_of_aligned`.
- Owed: two more bundle hypotheses. **Zero downstream importers.** Dead.

#### `JacobianChallenge/Manifold/ChartCircleSumZeroEmpty.lean` — 195 LOC, sorry=0
**Category: SUBSTANTIVE (trivial case).** Closes `chartCircleSum = 0`
and `principalDivisorMap.degree = 0` in the trivial case where `f` has
no zeros and no poles (so the support set is empty). Useful corner case.
- Top-level decls: `chartCircleSum_zero_of_supportFinset_empty`, `principalDivisorMap_degree_zero_of_supportFinset_empty`, `principalDivisorMap_eq_zero_iff_no_zeros_no_poles`, `supportFinset_eq_empty_iff_no_zeros_no_poles`.
- Owed: nothing. **Zero downstream importers.** Dead corner case.

### Group 3 — Stokes-on-disk / compact-surface skeletons

#### `JacobianChallenge/Manifold/StokesDisk.lean` — 193 LOC, sorry=0
**Category: SUBSTANTIVE + DOC.** Proves
`circleIntegral_eq_zero_of_holomorphic_on_closedBall` and
`intervalIntegral_circleMap_eq_zero_of_holomorphic` from
`DiffContOnCl.circleIntegral_eq_zero` (mathlib primitive). Also defines
`Stokes_disk_statement` (a `def Prop`) as a named target. The proven
content is mathlib-direct; the statement def is owed.
- Top-level decls: `circleIntegral_eq_zero_of_holomorphic_on_closedBall`, `intervalIntegral_circleMap_eq_zero_of_holomorphic`, `Stokes_disk_statement` (def Prop).
- Owed: `Stokes_disk_statement` (the manifold-Stokes statement). Imported by 2 files.

#### `JacobianChallenge/Manifold/StokesDiskClosedForm.lean` — 179 LOC, sorry=0
**Category: SUBSTANTIVE.** Three theorems wrapping the previous file's
`circleIntegral_eq_zero` results for `MeromorphicOneForm`-coefficient
functions on a chart disk. Real composition with `chartCircleIntegralOfFun`.
- Top-level decls: `chartCircleIntegralOfFun_eq_zero_of_diffContOnCl`, `chartCircleIntegralOfFun_eq_zero_of_DiffContOnCl`, `chartCircleIntegralAnchored_eq_zero_of_diffContOnCl`.
- Owed: nothing. **Zero downstream importers.** Dead.

#### `JacobianChallenge/Manifold/StokesCompactSurface.lean` — 232 LOC, sorry=0
**Category: PARAPHRASE.** Defines `StokesCompactSurfacePartitionOfUnity_hypothesis`,
`stokesCompactSurface_statement` (`def Prop`), and shows the statement
follows from the hypothesis. Yet another bundle whose conclusion is
already in tree.
- Top-level decls: `StokesCompactSurfacePartitionOfUnity_hypothesis` (structure), `stokesCompactSurface_via_partition_of_unity`, `stokesCompactSurface_statement` (def Prop), `stokesCompactSurface_statement_holds`.
- Owed: bundle hypothesis. Imported by 3 files.

#### `JacobianChallenge/Manifold/StokesCanonicalClosedForms.lean` — 119 LOC, sorry=0
**Category: REDUCTION.** Defines `canonicalClosedForms` and
`canonicalIntegrationStokes`; constructs a `StokesBoundaryInvariance.canonical`.
Routine packaging of mathlib's smooth-form machinery.
- Top-level decls: `canonicalClosedForms` (def), `canonicalIntegrationStokes`, `StokesBoundaryInvariance.canonical`.
- Owed: nothing direct, but consumes upstream named hypotheses. Imported by 6 files.

#### `JacobianChallenge/Manifold/StokesCanonicalH1SubsingletonChar.lean` — 94 LOC, sorry=0
**Category: REDUCTION.** Three theorems chained via `Iff`: `H¹ is Subsingleton ↔ stokesBoundaries = ⊤`. Pure structural rephrasing of subsingleton vs surjectivity.
- Top-level decls: `subsingleton_canonical_H1_of_stokesBoundaries_eq_top`, `stokesBoundaries_eq_top_of_subsingleton_canonical_H1`, `subsingleton_canonical_H1_iff_stokesBoundaries_eq_top`.
- Owed: nothing. Imported by 2 files.

#### `JacobianChallenge/Manifold/StokesBoundaryInvarianceFromSimplex.lean` — 125 LOC, sorry=0
**Category: HYPOTHESIS-DEF + REDUCTION.** Defines
`IntegrationStokesHypothesis` and constructs a `StokesBoundaryInvariance`
from a single-simplex Stokes hypothesis. Real composition.
- Top-level decls: `IntegrationStokesHypothesis` (def), `integrate_boundary₂_eq_zero`, `StokesBoundaryInvariance.ofSingleSimplexStokes`.
- Owed: `IntegrationStokesHypothesis`. Imported by 2 files.

#### `JacobianChallenge/Manifold/StokesBoundariesRiemannSphereTop.lean` — 62 LOC, sorry=0
**Category: REDUCTION (per-X).** One theorem `stokesBoundaries_RS_eq_top`
proving the Riemann-sphere instance of `stokesBoundaries = ⊤`. Per-X
chip — the user's anti-pattern list flags this exact pattern, but it
*is* paired with a substantive RS-specific BSLB discharge below.
- Top-level decls: `stokesBoundaries_RS_eq_top`.
- Owed: nothing. Imported by 2 files.

#### `JacobianChallenge/Manifold/StokesBoundariesTopRiemannSphere.lean` — 56 LOC, sorry=0
**Category: REDUCTION (per-X).** Discharges `basedSmoothLoopsBoundHypothesis_RS_holds`
— the `RiemannSphere` instance of `BasedSmoothLoopsBoundHypothesis`.
Real content but RS-only. Imported by 8 files (the most-imported file in this group).
- Top-level decls: `basedSmoothLoopsBoundHypothesis_RS_holds`.
- Owed: nothing on RS, but everything else awaits general-X discharge.

### Group 4 — Smooth chain / cycle / path Stokes-boundary plumbing

#### `JacobianChallenge/Manifold/Smooth2ChainStokesBoundary.lean` — 140 LOC, sorry=0
**Category: REDUCTION.** Defines `stokesBoundaries` as an `AddSubgroup`
of `SmoothCycle` and proves the obvious group-theoretic closure lemmas
(`zero_mem`, `add_mem`, `neg_mem`) plus `boundary₂Cycle` is a `LinearMap`.
Pure plumbing.
- Top-level decls: `boundary₂_mem_smoothCycle`, `boundary₂Cycle` (def), `boundary₂Cycle_add`, `boundary₂Cycle_neg`, `stokesBoundaries` (def), `mem_stokesBoundaries_iff`, `zero_mem_stokesBoundaries`, `add_mem_stokesBoundaries`, `neg_mem_stokesBoundaries`.
- Owed: nothing. Imported by 4 files.

#### `JacobianChallenge/Manifold/SmoothPathConcatAdditivityStokes.lean` — 213 LOC, sorry=0
**Category: REDUCTION.** Three lemmas about concatenation of smooth
paths and membership in `stokesBoundaries`. Real composition.
- Top-level decls: `concat_additive_chain_mem_smoothCycle`, `concat_additive_smoothCycle` (def), `concat_additive_in_stokesBoundaries`.
- Owed: nothing. Imported by 4 files.

#### `JacobianChallenge/Manifold/SmoothPathReverseStokesBoundary.lean` — 105 LOC, sorry=0
**Category: REDUCTION.** Path-reverse plus original is a Stokes boundary.
- Top-level decls: `single_smoothPath_plus_reverse_mem_smoothCycle`, `single_smoothPath_plus_reverse_smoothCycle` (def), `single_smoothPath_plus_reverse_mem_stokesBoundaries`.
- Owed: nothing. Imported by 7 files.

#### `JacobianChallenge/Manifold/SmoothCycleInStokesBoundariesOfBasedLoopsBound.lean` — 171 LOC, sorry=0
**Category: REDUCTION.** Single theorem: a `SmoothCycle` is in
`stokesBoundaries` if the `BasedSmoothLoopsBoundHypothesis` holds.
Substantive composition step in the canonical-H1-trivial arc.
- Top-level decls: `cycle_in_stokesBoundaries_of_basedLoopsBound`.
- Owed: nothing direct. Imported by 2 files.

### Group 5 — Holomorphic-Stokes hypothesis rephrasings

#### `JacobianChallenge/Manifold/HolomorphicStokesFromComplexBoundary.lean` — 169 LOC, sorry=0
**Category: PARAPHRASE.** Defines `HolomorphicComplexBoundaryVanishingHypothesis`
and proves five Iff-style bridges to/from the existing `HolomorphicStokesHypothesis`
plus a `HolomorphicComponentsCanonicalClosed.of_complexBoundary` reduction.
Bridges between two named hypotheses.
- Top-level decls: `HolomorphicComplexBoundaryVanishingHypothesis` (def), `HolomorphicStokesHypothesis_of_complexBoundary`, `complexBoundary_of_HolomorphicStokesHypothesis`, `holomorphicStokesHypothesis_iff_complexBoundary`, `HolomorphicComponentsCanonicalClosed.of_complexBoundary`, `HolomorphicComplexBoundaryVanishingHypothesis.of_subsingleton`.
- Owed: bundle hypothesis. Imported by 2 files.

#### `JacobianChallenge/Manifold/HolomorphicStokesFromLoopHypothesis.lean` — 95 LOC, sorry=0
**Category: PARAPHRASE.** Defines yet a *third* equivalent hypothesis
`HolomorphicLoopIntegralVanishes` and proves it iff `HolomorphicStokesHypothesis`.
- Top-level decls: `HolomorphicLoopIntegralVanishes` (def), `holomorphicStokesHypothesis_iff_loopIntegralVanishes`, `holomorphicComponentsCanonicalClosed_of_loopIntegralVanishes`.
- Owed: bundle hypothesis. Imported by 1 file.

#### `JacobianChallenge/Manifold/IntegerShadowStokes.lean` — 369 LOC, sorry=0
**Category: HYPOTHESIS-DEF + REDUCTION.** Defines `IntegerShadowChainComplex`
(structure: face/boundary integers) and `ChartIntegralRealisation`
(structure connecting chart-circle integrals to the integer shadow).
Proves `boundaryInt_sum_eq_zero` (clean algebraic identity), then a
chartIntegralFibreBalance reduction. Real algebraic content (the "integer
shadow of `d² = 0`" is a clean lemma) but the structures wrap the
classical analytic step in a hypothesis.
- Top-level decls: `IntegerShadowChainComplex` (structure), `boundaryInt` (def), `boundaryInt_sum_eq_zero`, `ChartIntegralRealisation` (structure), `face_sum_eq_support_sum`, `chartIntegral_sum_eq_zero`, `chartIntegralFibreBalanceOn_of_integerShadow`.
- Owed: realisation existence — the structure presupposes a non-trivial geometric chain complex. Imported by 1 file.

### Group 6 — C3 Period-Lattice Stokes (NOT residue-theorem)

These 13 files belong to a **different program**: the C3 / Riemann
bilinear / Period Lattice Span arc, used in the Jacobian-side
(`JacobianAnalyticBundle`) chain. They are not on any residue-theorem
path. They were matched by `*Stokes*` only. Brief classifications:

| File | LOC | Category | Note |
|---|---:|---|---|
| `C3PeriodLatticeStokesCanonical.lean` | 146 | REDUCTION (per-X-stub) | One `def ... ofCanonical`, no theorems. |
| `C3PeriodLatticeStokesCanonicalFromHypothesis.lean` | 102 | PARAPHRASE | Two `def` bundles, no theorems. |
| `C3PeriodLatticeStokesCanonicalFromStokesBoundariesTop.lean` | 78 | REDUCTION | One nonempty-existence theorem from a top-level Stokes hypothesis. |
| `C3PeriodLatticeStokesCanonicalH1Subsingleton.lean` | 110 | REDUCTION | Two `h1_spans_top_canonical_of_subsingleton*` theorems. |
| `C3PeriodLatticeStokesCanonicalRiemannSphere.lean` | 82 | REDUCTION (per-X RS) | RS-specific canonical bundle. |
| `C3PeriodLatticeStokesCanonicalTrivialAtGenusZero.lean` | 79 | PARAPHRASE | Two `def`s, no theorems — "trivial at genus zero" rephrasing. |
| `C3PeriodLatticeStokesCanonicalUnconditional.lean` | 78 | PARAPHRASE | One `def`, no theorems — claims "unconditional" with no theorem. |
| `C3PeriodLatticeStokesGenusZero.lean` | 120 | PARAPHRASE | One `def`, no theorems. |
| `C3PeriodLatticeStokesH1Generation.lean` | 193 | SUBSTANTIVE | The core: `C3PeriodLatticeStokesSpanTopInputs` structure + `homologyGeneration_of_spans_top` theorem. The one substantive C3-Stokes file. |
| `C3PeriodLatticeStokesNonemptyHeadline.lean` | 57 | REDUCTION | One nonempty-witness theorem. |
| `C3PeriodLatticeStokesRefactored.lean` | 217 | REDUCTION | Re-packaging of the H1-generation file. Likely supersedes earlier variants. |
| `C3PeriodLatticeStokesRiemannSphere.lean` | 76 | REDUCTION (per-X RS) | One RS-specific nonempty witness. |
| `C3PeriodLatticeStokesRiemannSphereUnconditional.lean` | 68 | REDUCTION (per-X RS) | RS-specific "unconditional" rewire. |

**Aggregate**: 1,406 LOC for 13 files, of which only 1
(`StokesH1Generation`) carries the real classical content (the others are
all redirections or per-X RS chips around the same core
`C3PeriodLatticeStokesSpanTopInputs` structure). This is the
chip-multiplication pattern that the user's preamble flags.

### Group 7 — The Divisor home of `ResidueTheorem`

#### `JacobianChallenge/Divisor/PrincipalDivisorRange.lean` — 464 LOC, sorry=0
**Category: SUBSTANTIVE.** Defines `ResidueTheorem X` at line 237 as a
`Prop`-valued `def`, plus the equivalence
`residueTheorem_iff_range_le_Div0` and germ-level repackaging. The file
itself proves no analytic content — it just bridges the residue theorem
to `PrincDiv` / `Div0` group theory. The deep classical fact is owed
externally (and *is* delivered by `ResidueTheoremUnconditional.lean`).
- Top-level decls: `PrincDivHonestCandidate` (def), `principalDivisorMap_mem_PrincDivHonestCandidate`, `ResidueTheorem` (def Prop), `residueTheorem_iff_range_le_Div0`, `germPrincipalDivisorMap_one`, `germPrincipalDivisorMap_mul`, `PrincDivHonestCandidateGerm` (def), `PrincDivHonestCandidateGerm_eq`, plus a few more bookkeeping lemmas.
- Owed: `ResidueTheorem X` itself — but **already discharged** by
  `JacobianChallenge.residue_theorem` (`ResidueTheoremUnconditional.lean`).

---

## Aggregate by category

| Category | Files | LOC |
|---|---:|---:|
| SUBSTANTIVE | 8 | ~1,850 |
| REDUCTION (including per-X) | 18 | ~2,650 |
| PARAPHRASE | 14 | ~2,300 |
| HYPOTHESIS-DEF (no substantive theorem) | 5 | ~1,000 |
| DOC/INDEX | 0 | 0 |

Roughly **3,300 of ~7,800 LOC (~42%) is PARAPHRASE or HYPOTHESIS-DEF
chasing an already-closed conclusion.** All sorry-free, all axiom-free,
all worthless to the residue-theorem program.

Files with **zero downstream importers** (definitively dead):
1. `StokesDiskClosedForm.lean` (179 LOC) — superseded by direct mathlib use upstream.
2. `LogDerivLaurentDischarge.lean` (327 LOC) — orphan rephrasing of `LogDerivLaurent`.
3. `ChartCircleSumOrders.lean` (218 LOC) — double-named theorem, no importer.
4. `ChartCircleSumZeroDischarge.lean` (221 LOC) — three nested bundles, no importer.
5. `ChartCircleSumZeroEmpty.lean` (195 LOC) — trivial-case corner, no importer.

**Total dead: 1,140 LOC across 5 files.** Removing them would not change
any `sorry` count or any theorem statement.

Files with **only same-arc importers** (live but orphan parallel route to
`ResidueTheorem X` which is already in tree):
- `ResidueTheoremAssembly.lean` (324)
- `ResidueTheoremStokes.lean` (383)
- `ResidueViaTopologicalDegree.lean` (297)
- `GlobalResidueSum.lean` (250)
- `HolomorphicStokesFromComplexBoundary.lean` (169)
- `HolomorphicStokesFromLoopHypothesis.lean` (95)
- `StokesCompactSurface.lean` (232)
- `IntegerShadowStokes.lean` (369)
- `ChartCircleSumZero.lean` (212) + `CircleResidue.lean` (421) + `LogDerivLaurent.lean` (240)

**Total parallel-route live-but-orphan: ~2,990 LOC.** These could be
deleted in principle (their conclusion `ResidueTheorem X` is already
discharged unconditionally elsewhere), but some downstream code may
import them for the *Iff* bridges. Audit before deletion.

---

## Synthesis

### 1. What is the frontmost open named hypothesis the residue-theorem program leaves undischarged?

**None.** Tracing from `ResidueTheorem X` (`PrincipalDivisorRange.lean:237`)
through the named-hypothesis chain to its leaves: every leaf is
discharged in tree.

- `ResidueTheorem X` ≡ `R5_principal_degree_zero_statement X` (by
  `R5_iff_ResidueTheorem` in `ResidueTheoremFromRsum.lean:396` — modulo
  `R5` being for all `f`, both are `∀ f, (principalDivisorMap f).degree = 0`).
- `R5_principal_degree_zero_statement X` ⇐ `R4_fibreSum_balance_statement X`
  (proven, `ResidueTheoremFromRsum.R5_principal_degree_zero_statement_of_R4`).
- `R4_fibreSum_balance_statement X` ⇐ `ramificationSumEqualsDegree_holds_unconditional`
  (proven, `R4FibreSumBalance.lean`).
- `ramificationSumEqualsDegree_holds_unconditional` ⇐
  `nearbyRegularWitnessHypothesis_holds_unconditional` + `wd_reg_holds_unconditional`
  (both proven, `NearbyRegularWitnessUnconditional.lean`).
- `nearbyRegularWitnessHypothesis_holds_unconditional` is a real
  multi-page proof using the in-tree `localKFoldMultiplicityOnManifold_genuine_with_radius`
  + `Set.Finite.t2_separation` + `preimage_eventually_in_fibre_neighbourhoods`
  + `criticalValues_finite_general`. Nothing is owed externally.

This audit's brief implicitly assumed the **Route-B (Stokes) path** is the
status of the residue theorem. It is not. The status is **closed via
Route A (topological degree / Hurwitz)**, and has been since the
`R5Unconditional.lean` + `ResidueTheoremUnconditional.lean` landings (no
session date in this audit — just verified by direct trace through the
proof chain).

### 2. Shortest path from `ResidueTheorem X` to closure given what's in tree

**Zero steps.** Already there:

```lean
theorem residue_theorem
  (f : MeromorphicNonzero X) : (principalDivisorMap f).degree = 0 :=
ResidueTheorem.R5_principal_degree_zero_statement_holds X f
```
(`Manifold/ResidueTheoremUnconditional.lean:39`).

If one *insists* on closing Route B for completeness — say to provide
two independent proofs as a cross-check — the chain of bundle leaves
that would need a real proof is:

1. `GlobalResidueSum_hypothesis.global_chain_boundary_eq_zero`
   (`GlobalResidueSum.lean:156`) — "the integer shadow of `d² = 0` on a
   compact 2-manifold without boundary". Genuinely hard: requires the
   manifold-Stokes theorem (not in mathlib at the pin).
2. `GlobalResidueSum_hypothesis.chartIntegral_eq_order`
   (`GlobalResidueSum.lean:147`) — "per-point chart-circle integer
   equals the order of `f`". Equivalent to
   `chartCircleIntegral_eq_residue_statement`
   (`CircleResidue.lean:132`), which **is achievable from mathlib
   primitives** — it follows from the local Laurent expansion of
   `f' / f` at `x` combined with
   `chartCircleIntegral_of_coeff_eq_finite_laurent` (already proven in
   `CircleResidue.lean`).
3. `IntegrationStokesHypothesis` (`StokesBoundaryInvarianceFromSimplex.lean:49`)
   — single-simplex Stokes theorem. Manifold-Stokes again, not at the pin.

### 3. Which leaves are achievable from mathlib primitives?

- ✅ `chartCircleIntegral_eq_residue_statement` /
  `chartIntegral_eq_order` (Group 2 leaf): yes. Combine
  `CircleResidue.chartCircleIntegral_of_coeff_eq_finite_laurent`
  (already proven) with `MeromorphicOn.extract_zeros_poles` (mathlib has
  it — used in `JensenFormula.lean` and `LogMeromorphic.lean`) to get
  the local Laurent normal form of `f' / f`, then thread through.
  Cleanly single-session.
- ❌ `global_chain_boundary_eq_zero` (Group 1 / Group 6 leaf): no.
  Requires manifold-Stokes for compactly supported smooth `(2n-1)`-forms
  on a compact `n`-manifold without boundary — mathlib has
  `divergence_eq_integral` and disk-Stokes via
  `MeasureTheory.Integral.DivergenceTheorem` but no general compact
  2-manifold Stokes at the pin. This would be mathlib-class infrastructure.
- ❌ `IntegrationStokesHypothesis` (single-simplex Stokes): same as above.
- ✅ `Stokes_disk_statement` (`StokesDisk.lean:178`): yes — already
  effectively closed via the two proven theorems in the file that wrap
  `DiffContOnCl.circleIntegral_eq_zero`. The `def Prop` could be
  discharged by routine repackaging.

### 4. Recommended next-session deliverable

**None for the residue-theorem program.** The headline is already
closed. The Route-B parallel route has 2 hard leaves (Stokes on a
compact 2-manifold) that are mathlib-class — explicitly the wrong
granularity per the project's anti-paraphrase rules ("100 LOC chips that
'bridge named hypothesis A to named hypothesis B' are wrong granularity").

If a next session insists on touching this sub-tree, the **least-bad**
deliverable is:

**File to modify: `JacobianChallenge/Manifold/CircleResidue.lean`**

**What it would prove**: discharge the `chartCircleIntegral_eq_residue_statement`
`def Prop` (line 132) into a real `theorem`, by combining the already-proven
`chartCircleIntegral_of_coeff_eq_finite_laurent` (same file, line 347) with
`MeromorphicOn.extract_zeros_poles` applied to `α.coeff` at the pole, plus
the chart-pullback identifications already in `MeromorphicOneForm.lean`.
Result: a real lemma that "for any meromorphic 1-form, the chart-circle
integral around a small disk equals the local residue".

This is the only file in the audit scope whose owed `def Prop` is
**achievable from mathlib primitives** without writing manifold-Stokes
infrastructure, **and** whose closure would be genuinely substantive
classical content (the local residue theorem for meromorphic 1-forms).
Single session, ~150-250 LOC, no new mathlib-class theorems needed.

**But the user should be aware: closing this would still not move any
`sorry` in `Basic.lean`, because the residue-theorem headline is
already independently discharged via Route A.** The honest
recommendation is **skip this sub-tree entirely** and route next-session
effort to one of the two actual open frontiers from the broader audit:

- Item-14 `hSP` / `RR_DimGE2_GenusZero_Germ X` (RR-class arc).
- C3 chain's `Riemann bilinear` / `Abel` / `Jacobi inversion` substantive
  classical theorems.

Either of those moves a real `sorry` in `Basic.lean`. Touching Route-B
of the residue theorem does not.

### 5. Files to delete (safe — no `sorry` count change, no theorem statement change)

Per the project's `tools/chip-prompt-preamble.md` (parallel-route + per-X
+ named-hypothesis-rename are net negative when their conclusion is
already in tree):

**Definitively safe to delete (zero downstream importers, verified by `grep -rl "Manifold\.<file>" JacobianChallenge --include="*.lean"`):**
1. `JacobianChallenge/Manifold/StokesDiskClosedForm.lean` (179 LOC) — superseded by `StokesDisk.lean` + direct mathlib use.
2. `JacobianChallenge/Manifold/LogDerivLaurentDischarge.lean` (327 LOC) — `LogDerivResiduePlusAnalytic` is a renamed `LogDerivFiniteLaurent`. Anti-pattern: named-hypothesis rename (preamble gate #1).
3. `JacobianChallenge/Manifold/ChartCircleSumOrders.lean` (218 LOC) — double-defines the same theorem name; no importer.
4. `JacobianChallenge/Manifold/ChartCircleSumZeroDischarge.lean` (221 LOC) — three nested rephrasings of one hypothesis; no importer. Anti-pattern: named-hypothesis rename chain (preamble gate #1).
5. `JacobianChallenge/Manifold/ChartCircleSumZeroEmpty.lean` (195 LOC) — corner case (`supp f = ∅`) already absorbed by the constant-case in `R4FibreSumBalance.lean`; no importer.

**Total safe-delete: 1,140 LOC across 5 files.**

**Strongly recommended (require import audit first — likely safe):**

6. The C3 Period-Lattice "Stokes" per-X / paraphrase fan-out
   (`C3PeriodLatticeStokesCanonicalFromHypothesis.lean`,
   `C3PeriodLatticeStokesCanonicalTrivialAtGenusZero.lean`,
   `C3PeriodLatticeStokesCanonicalUnconditional.lean`,
   `C3PeriodLatticeStokesGenusZero.lean`,
   `C3PeriodLatticeStokesRiemannSphereUnconditional.lean`): ~447 LOC of
   per-X-instance and named-hypothesis rephrasings around the substantive
   `C3PeriodLatticeStokesH1Generation.lean` core. Anti-pattern: per-X
   instance multiplication + parallel routes (preamble gates #3, #4).
7. **The entire Route-B `ResidueTheorem` parallel route**:
   `ResidueTheoremAssembly.lean`, `ResidueTheoremStokes.lean`,
   `ResidueViaTopologicalDegree.lean`, `GlobalResidueSum.lean`,
   `HolomorphicStokesFromComplexBoundary.lean`,
   `HolomorphicStokesFromLoopHypothesis.lean`,
   `StokesCompactSurface.lean`. Total ~1,930 LOC. Each ends in
   "`ResidueTheorem_holds_of_<bundle>`" — proving an `Iff`/implication to
   the already-discharged headline. Anti-pattern: parallel route to an
   already-closed conclusion (preamble gate #4) and "from N inputs"
   reformulations (preamble gate #2).

**Total recommended for deletion after import audit: ~3,517 LOC across
~13 files** — about 45% of the sub-tree, all of it bloat by the
project's own anti-paraphrase rules. The substantive analytic content
(planar circle integrals, log-derivative Laurent, smooth-cycle plumbing,
chart-circle-anchored-at-radius theorems, and the C3 `StokesH1Generation`
core) would remain.

---

## Methodology note

This audit was strictly read-only. No Lean files were compiled or
modified. No `du` or heavy `find` was executed (kernel-panic risk per
`CLAUDE.md`). All claims are traced via `grep`, `wc -l`, targeted
`Read`s of statement / discharge points, and import-count via
`grep -rl "Manifold\.<file>"`.

**Confidence**:
- High: the topological-degree Route-A discharge of `ResidueTheorem X`
  via `R4FibreSumBalance.residue_theorem_unconditional` and
  `NearbyRegularWitnessUnconditional.ramificationSumEqualsDegree_holds_unconditional`.
  Verified by direct reading of all four files in the chain.
- High: classification of `Residue*Assembly`, `*Stokes`, `*ViaTopologicalDegree`,
  `GlobalResidueSum` as parallel routes ending in a bundle hypothesis
  the in-tree headline does not need. Verified by reading top-level
  decl lists + the `ResidueTheorem_holds_of_<bundle>` statements.
- Medium: classification of `C3PeriodLatticeStokes*` as not-residue-theorem.
  Based on file names + top-level decls; did not exhaustively trace
  the C3 / Jacobian-bundle chain.
- Medium: "safe to delete" depends on `grep -rl` finding all importers.
  If a file is imported under an alias or via `import all` / umbrella
  patterns, the count could underreport. Recommend running
  `lake env lean` once on the full file list before any deletion to
  confirm compilation independence.
