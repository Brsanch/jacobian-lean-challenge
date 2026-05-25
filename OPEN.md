# OPEN

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

## Authoritative current state (2026-05-23 deep audit)

**14 STRICT-CLOSED, 2 STUB, 8 OPEN.** Per-item details below; full
deep-audit rationale (chain-trace per sorry, doc-bloat findings,
classical-content collapse to 3 textbook theorems) in
[`REPO_AUDIT.md`](REPO_AUDIT.md). Item-14-specific status in
[`HANDOFF_ITEM14.md`](HANDOFF_ITEM14.md). C3 / Jacobian-side status in
[`C3_AUDIT.md`](C3_AUDIT.md).

For chronological session history, see `git log --oneline`. The prior
~2,500-line "Scoreboard" section of this file was deleted 2026-05-23
because it accumulated contradictory item counts (e.g. item 16 appeared
as both OPEN and STRICT-CLOSED in different sections) and obscured the
authoritative item table that follows.

## Definitions (data) — Basic.lean items 1–9 in OPEN.md numbering

| # | Item | Status | Notes |
|---|---|---|---|
| 1 | `genus X : ℕ` | **STRICT-CLOSED** *(post-Forster, 2026-05-17)* | Body: `JacobianChallenge.genus X = Module.finrank ℂ (HolomorphicOneForm X)`. **Finite-dimensionality on a compact connected complex 1-manifold is unconditional** via `DiskChartCover.holomorphicOneFormFiniteDim_holds` (`Manifold/DiskChartCoverFiniteDim.lean`), so the junk-zero convention does not kick in and `Module.finrank` returns the honest geometric genus. |
| 2 | `Jacobian X : Type u` | **STRICT-CLOSED** *(post-ZZ256, 2026-05-12)* | Body: `Jacobian X := Pic0 X` with `Pic0 X = Div0 X ⧸ (PrincDiv X).addSubgroupOf (Div0 X)` and **`PrincDiv X := PrincDivHonestCandidate X`** (honest principal-divisor subgroup, in `Divisor/PrincipalDivisorRange.lean`). |
| 3 | `instance : AddCommGroup (Jacobian X)` | **STRICT-CLOSED** | Inherits from the honest `Pic0` quotient. |
| 4 | `instance : TopologicalSpace (Jacobian X)` | **STUB** | Discrete (`⊥`). The challenge wants the complex-manifold topology (item 5 `ChartedSpace`); discrete is not it. Flips mechanically with item 5. |
| 5 | `instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` | **OPEN** | `sorry`. Requires the analytic-Jacobian rewire of `Jacobian X` to `CanonicalAnalyticJacobianAnonymous X` (under `[HasJacobianAnalyticStructure X]`). Bottom-of-chain: `C3FullInputExt X` bundle = Riemann bilinear + Abel + Jacobi. See `C3_AUDIT.md`. |
| 6 | `Jacobian.ofCurve : X → Jacobian X` | **STRICT-CLOSED** | Body: `Q ↦ [δQ − δP]` in honest `Pic⁰`. |
| 7 | `Jacobian.pushforward f hf` | **STRICT-CLOSED** | Body: `JacobianChallenge.Jacobian.pushforward hf` in `JacobianPushforward.lean`. Descent via P1.4 on the non-constant branch + degree-zero trivialization on the constant branch. |
| 8 | `Jacobian.pullback f hf` | **STRICT-CLOSED** | Body: `Jacobian.pullbackHonest_of_rsum`, with `Pic0.pullbackWeighted` descent obligation discharged unconditionally by `Pic0.divPullbackWeighted_descent_of_smooth`. |
| 9 | `ContMDiff.degree f hf : ℕ` | **STRICT-CLOSED** *(post-zzITEM9, 2026-05-12)* | Body: `JacobianChallenge.ContMDiff.degreeFiber f hf`. Well-definedness across regular witnesses via `degreeFiber_eq_card_of_regular_witness`. |

## Theorems (Prop) — Basic.lean items 10–24 in OPEN.md numbering

| # | Item | Status | Notes |
|---|---|---|---|
| 10 | `instance : T2Space (Jacobian X)` | **STUB** | Discrete ⇒ T2 is honest, but the topology itself is wrong (item 4). Flips with item 5. |
| 11 | `instance : CompactSpace (Jacobian X)` | **OPEN** | `sorry`. Reduces to item 5 via the C3 rewire. |
| 12 | `instance : IsManifold ... ω (Jacobian X)` | **OPEN** | `sorry`. Reduces to item 5. |
| 13 | `instance : LieAddGroup ... ω (Jacobian X)` | **OPEN** | `sorry`. Reduces to item 5 plus smoothness of group ops (auto from the analytic Jacobian construction). |
| 14 | `genus_eq_zero_iff_homeo` (anti-hack vs. `genus := 0`) | **OPEN — Pompeiu arc in flight** | `sorry`. **Post-merge state (2026-05-24):** reduces to ONE named classical hypothesis `hSP X = ExistsSimplePoleGermAtSomePoint X`. The reverse leg `S2ImpliesGenus0 X` is unconditional via `s2ImpliesGenus0_etalePrimitivesArc` (étale-primitives arc, merged from `feat/item14-affineChartTriangleSimplex-ball`). One-input composition is `Topology/Item14FromHSPOnly.lean:genus_eq_zero_iff_homeo_from_hSP`. **BSLB is no longer needed for Item 14.** Via Chip 2c-Final (`Manifold/ForsterCutoffPoleConstruction.lean:existsSimplePoleGermAtSomePoint_of_dbarSolvability_under_chartConst`), hSP X further reduces to `DBarSolvabilityAtGenusZero X` (genus-0 sheaf cohomology / `H¹(X,𝒪)=0`) plus a per-`p` structural hypothesis `ChartAtConstantOnSource p` (innocuous on every concrete X: RS at finite p, ℂ/L tori, single-chart spaces). **Pompeiu kernel arc started 2026-05-24:** Chip 1a landed (`Analysis/PompeiuKernel.lean`, commit `bcf6951` — definitions, measurability, translation reduction, trivial integrability case). Chip 1b landed (`Analysis/InvNormIntegrability.lean`, 163 LOC — `integrableOn_inv_norm_closedBall` via `Complex.lintegral_comp_polarCoord_symm`; sorry-free, axiom-free). Chip 1c landed (`Analysis/PompeiuIntegrandIntegrability.lean`, 140 LOC — `integrable_pompeiuIntegrand_of_continuous_hasCompactSupport`, combining 1a translation reduction + 1b polar bound + bounded-α + `closedBall 0 R ⊆ closedBall z (R + ‖z‖)`; sorry-free, axiom-free). **Next chip: Chip 2** = `pompeiuKernel α` is `C^∞ ℝ` on `ℂ` (differentiation under the integral). See `HANDOFF_ITEM14.md` "ACTIVE ARC" section for the full plan to close. |
| 15 | `ofCurve_self : ofCurve P P = 0` | **STRICT-CLOSED** | Real proof reducing to `[δP − δP] = 0` in honest `Pic⁰`. |
| 16 | `ofCurve_inj` (anti-hack vs. `Jacobian := PUnit`) | **STRICT-CLOSED** | Body in `Basic.lean` line 143–144: `JacobianChallenge.ofCurve_inj_holds P h` (`Manifold/ChartDerivNeZeroImpliesNonCriticalDischarge.lean`). All-unconditional discharge chain: `PrincDivWitnessExtraction` → degree-1 mero function (via `DegreeOneFromSimpleZeroSimplePoleDischarge`) → `bijective_of_degreeFiber_eq_one` + `bijectiveAnalyticIsBiholomorphism_holds` → biholomorphism `X ≃ RiemannSphere` → `genus = 0`, contradicting `0 < genus X`. |
| 17 | `Jacobian.ofCurve_contMDiff` | **OPEN** | `sorry`. Requires item 5 plus per-curve Abel–Jacobi smoothness from `JacobianAnalyticClosureBundle`. |
| 18 | `Jacobian.pushforward_contMDiff` | **OPEN** | `sorry`. Requires item 5 plus per-curve `JacobianAnalyticPushforwardLift`. |
| 19 | `pushforward_id_apply` | **STRICT-CLOSED** | Real proof via `Pic0.pushforward_id` ↦ `Div.singletonMap_id_apply`. |
| 20 | `pushforward_comp_apply` | **STRICT-CLOSED** | Real proof via `Pic0.pushforward_comp` ↦ `Div.singletonMap_comp_apply`. |
| 21 | `Jacobian.pullback_contMDiff` | **OPEN** | `sorry`. Requires item 5 plus per-curve `JacobianAnalyticPullbackLift`. |
| 22 | `pullback_id_apply` | **STRICT-CLOSED** | Body: `JacobianChallenge.Jacobian.pullbackHonest_of_rsum_id _ P`. |
| 23 | `pullback_comp_apply` | **STRICT-CLOSED** | Body: `pullbackHonest_of_rsum_comp` with multiplicative ramification weights `manifoldRamificationIndex_comp_unconditional`. |
| 24 | `pushforward_pullback : pushforward f (pullback f P) = degree f • P` | **STRICT-CLOSED** | Body: `pushforward_pullbackHonest_of_rsum` — case-splits on `IsConstantMap f`. |

## Score

- **STRICT-CLOSED: 14 / 24** — items 1, 2, 3, 6, 7, 8, 9, 15, 16, 19, 20, 22, 23, 24.
- **STUB: 2** — items 4, 10 (placeholder discrete topology; flips mechanically with item 5).
- **OPEN: 8** — items 5, 11, 12, 13, 14, 17, 18, 21.

## The 8 OPEN items collapse to 2 substantive classical theorems

(Was 3 pre-2026-05-24 merge; BSLB became obsolete when the étale-primitives
arc merged in, leaving `DBarSolvabilityAtGenusZero X` and `C3FullInputExt X`.)

After auditing every named-hypothesis chain to its leaves (2026-05-23):

1. **Item 14's `hSP`** — `ExistsSimplePoleGermAtSomePoint X`. After
   Chip 2c-Final (2026-05-24, `Manifold/ForsterCutoffPoleConstruction.lean`),
   reduces further to **`DBarSolvabilityAtGenusZero X`** (= `H¹(X, 𝒪) = 0`
   at genus 0, equivalently solvability of `∂̄ u = α` for smooth (0,1)
   forms α at genus 0) plus a per-`p` structural hypothesis
   `ChartAtConstantOnSource p` (innocuous on concrete X). DBar is the
   actual classical-content gap. Bottom of the alternate Riemann-Roch
   chain: `RR_DimGE2_GenusZero_Germ X` (equivalent statement, not
   shorter).
2. ~~**Item 14's `BSLB`**~~ **OBSOLETE for Item 14 (2026-05-24 merge).**
   The reverse leg `S2ImpliesGenus0 X` is unconditionally discharged
   on arbitrary X by `s2ImpliesGenus0_etalePrimitivesArc`
   (`Topology/S2ImpliesGenus0FromEtalePrimitives.lean`, étale-primitives
   arc from `feat/item14-affineChartTriangleSimplex-ball`). The BSLB
   chain was a parallel route to the same conclusion and is no longer
   needed. The one-input composition
   `Topology/Item14FromHSPOnly.genus_eq_zero_iff_homeo_from_hSP` shows
   Item 14 reduces to hSP alone.
3. **C3's `C3FullInputExt X`** — bundle of Riemann bilinear relations
   + Abel's theorem + Jacobi inversion. Closes items 5/11/12/13/17/18/21
   collectively once landed. Per-curve `lattice_match` certificates
   close items 18/21.

That's it. The infrastructure is enormously over-built (1072 `.lean`
files, 182k LOC), but the genuine remaining classical content is
textbook Forster Ch. III §16–21 / Griffiths-Harris Ch. 2 §2–§3.

## Mathlib-prerequisite candidates (likely needed before strict closure)

- ~~**Whitney smooth approximation for manifold-valued maps**~~ —
  was tagged for the BSLB path; **obsolete after the 2026-05-24
  étale-primitives merge** (reverse leg discharged unconditionally
  without Whitney machinery).
- **Cauchy-Pompeiu kernel + ∂̄-solvability on disks** — would let us
  formalize Forster's elementary route to `DBarSolvabilityAtGenusZero X`
  if combined with classical content on globalization. Mathlib has
  the building blocks (rectangle Stokes, divergence thm, 2D integrals)
  but not the explicit kernel. ~1k LOC, 2–4 weeks. Useful upstream
  even outside this project. **Does not by itself close item 14** —
  globalization still requires `H¹(𝒪) = 0` at genus 0 or equivalent.
- **Riemann–Roch + Serre duality** — for item 14 `hSP` (alternate
  classical route to DBar). Multi-month Lean project; no current
  mathlib coverage.
- **Period-lattice / Hodge bilinear positivity** — for C3 `C3FullInputExt`.
- **Topological degree of proper holomorphic maps** between Riemann
  surfaces. `fibres_finite_statement` and `regular_value_exists_statement`
  are discharged unconditionally in tree.

## Local infrastructure

The repo's per-file map lives in `JacobianChallenge.lean` (the import
manifest) and the file system. `CHANGELOG.md` documents which files
landed in which session. This OPEN.md is intentionally short — the
authoritative status is the item table above + the audit docs
referenced at the top of this file.
