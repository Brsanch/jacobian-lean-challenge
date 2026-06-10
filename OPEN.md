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
[`HANDOFF_C3.md`](HANDOFF_C3.md).

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
| 5 | `instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` | **OPEN — SHIPPED CONDITIONAL** | `sorry`. Conditional on `C3FullInputExt X`. RS-case unconditional via subsingleton. See [`HANDOFF_C3.md`](HANDOFF_C3.md) "WALL DOCUMENTED" for the canonical chain (`C3FullInputExt X → JacobianAnalyticChoice X bundle → Basic.lean instance` via `Manifold/JacobianAnalyticChoice.lean:54+116` + `Manifold/JacobianAnalyticBasicLeanReduction.lean`), per-field audit, and ~40–60k LOC closure-cost estimate. |
| 6 | `Jacobian.ofCurve : X → Jacobian X` | **STRICT-CLOSED** | Body: `Q ↦ [δQ − δP]` in honest `Pic⁰`. |
| 7 | `Jacobian.pushforward f hf` | **STRICT-CLOSED** | Body: `JacobianChallenge.Jacobian.pushforward hf` in `JacobianPushforward.lean`. Descent via P1.4 on the non-constant branch + degree-zero trivialization on the constant branch. |
| 8 | `Jacobian.pullback f hf` | **STRICT-CLOSED** | Body: `Jacobian.pullbackHonest_of_rsum`, with `Pic0.pullbackWeighted` descent obligation discharged unconditionally by `Pic0.divPullbackWeighted_descent_of_smooth`. |
| 9 | `ContMDiff.degree f hf : ℕ` | **STRICT-CLOSED** *(post-zzITEM9, 2026-05-12)* | Body: `JacobianChallenge.ContMDiff.degreeFiber f hf`. Well-definedness across regular witnesses via `degreeFiber_eq_card_of_regular_witness`. |

## Theorems (Prop) — Basic.lean items 10–24 in OPEN.md numbering

| # | Item | Status | Notes |
|---|---|---|---|
| 10 | `instance : T2Space (Jacobian X)` | **STUB** | Discrete ⇒ T2 is honest, but the topology itself is wrong (item 4). Flips with item 5. |
| 11 | `instance : CompactSpace (Jacobian X)` | **OPEN — SHIPPED CONDITIONAL** | `sorry`. Same chain as item 5; conditional on `C3FullInputExt X`. RS-case unconditional via subsingleton. See [`HANDOFF_C3.md`](HANDOFF_C3.md). |
| 12 | `instance : IsManifold ... ω (Jacobian X)` | **OPEN — SHIPPED CONDITIONAL** | `sorry`. Same chain as item 5. See [`HANDOFF_C3.md`](HANDOFF_C3.md). |
| 13 | `instance : LieAddGroup ... ω (Jacobian X)` | **OPEN — SHIPPED CONDITIONAL** | `sorry`. Same chain as item 5 plus smoothness of group ops (auto from analytic Jacobian). See [`HANDOFF_C3.md`](HANDOFF_C3.md). |
| 14 | `genus_eq_zero_iff_homeo` (anti-hack vs. `genus := 0`) | **OPEN — SHIPPED CONDITIONAL** | `sorry`. Conditional on `ExistsMeroSimplePole_GenusZero X` (Forster Thm 16.9). Forward + reverse legs are both built; chain reduces to ONE classical theorem with equivalent textbook names (`hSP X`, `DBarSolvabilityAtGenusZero X` + `ChartAtConstantOnSource`, `RR_DimGE2_GenusZero X`, `Nonempty (HolomorphicEquiv X RS)` at genus = 0). RS-case unconditional via the étale-primitives arc. See [`HANDOFF_ITEM14.md`](HANDOFF_ITEM14.md) for canonical chain + audit. |
| 15 | `ofCurve_self : ofCurve P P = 0` | **STRICT-CLOSED** | Real proof reducing to `[δP − δP] = 0` in honest `Pic⁰`. |
| 16 | `ofCurve_inj` (anti-hack vs. `Jacobian := PUnit`) | **STRICT-CLOSED** | Body in `Basic.lean` line 143–144: `JacobianChallenge.ofCurve_inj_holds P h` (`Manifold/ChartDerivNeZeroImpliesNonCriticalDischarge.lean`). All-unconditional discharge chain: `PrincDivWitnessExtraction` → degree-1 mero function (via `DegreeOneFromSimpleZeroSimplePoleDischarge`) → `bijective_of_degreeFiber_eq_one` + `bijectiveAnalyticIsBiholomorphism_holds` → biholomorphism `X ≃ RiemannSphere` → `genus = 0`, contradicting `0 < genus X`. |
| 17 | `Jacobian.ofCurve_contMDiff` | **OPEN — SHIPPED CONDITIONAL** | `sorry`. Conditional on `C3FullInputExt X` (its `JacobianAnalyticClosureBundle` field). See [`HANDOFF_C3.md`](HANDOFF_C3.md). |
| 18 | `Jacobian.pushforward_contMDiff` | **OPEN — SHIPPED CONDITIONAL** | `sorry`. Conditional on `C3FullInputExt X` + per-curve `C3FullInputCurve B_X B_Y f hf` (period-pairing adjunction, ~2–4k LOC classical). See [`HANDOFF_C3.md`](HANDOFF_C3.md). |
| 19 | `pushforward_id_apply` | **STRICT-CLOSED** | Real proof via `Pic0.pushforward_id` ↦ `Div.singletonMap_id_apply`. |
| 20 | `pushforward_comp_apply` | **STRICT-CLOSED** | Real proof via `Pic0.pushforward_comp` ↦ `Div.singletonMap_comp_apply`. |
| 21 | `Jacobian.pullback_contMDiff` | **OPEN — SHIPPED CONDITIONAL** | `sorry`. Conditional on `C3FullInputExt X` + per-curve `C3FullInputCurve B_X B_Y f hf`. See [`HANDOFF_C3.md`](HANDOFF_C3.md). |
| 22 | `pullback_id_apply` | **STRICT-CLOSED** | Body: `JacobianChallenge.Jacobian.pullbackHonest_of_rsum_id _ P`. |
| 23 | `pullback_comp_apply` | **STRICT-CLOSED** | Body: `pullbackHonest_of_rsum_comp` with multiplicative ramification weights `manifoldRamificationIndex_comp_unconditional`. |
| 24 | `pushforward_pullback : pushforward f (pullback f P) = degree f • P` | **STRICT-CLOSED** | Body: `pushforward_pullbackHonest_of_rsum` — case-splits on `IsConstantMap f`. |

## Score

- **STRICT-CLOSED: 14 / 24** — items 1, 2, 3, 6, 7, 8, 9, 15, 16, 19, 20, 22, 23, 24.
- **STUB: 2** — items 4, 10 (placeholder discrete topology; flips mechanically with item 5).
- **OPEN: 8** — items 5, 11, 12, 13, 14, 17, 18, 21.

## The 8 OPEN items collapse to 2 substantive classical theorems

**Canonical framing (2026-05-26):** the two walls are:

1. **Item 14's wall** — **`ExistsMeroSimplePole_GenusZero X`** =
   Forster Thm 16.9: compact connected genus-0 Riemann surface admits
   a non-constant meromorphic function with a single simple pole.
   Defined at `Topology/RiemannRochGenusZeroDecomposition.lean:101`.
   Equivalent textbook names (any closes Item 14 on abstract X via
   in-tree transport): `hSP X` = `ExistsSimplePoleGermAtSomePoint X`,
   `DBarSolvabilityAtGenusZero X` + `ChartAtConstantOnSource`,
   `RR_DimGE2_GenusZero X`, `Nonempty (HolomorphicEquiv X RiemannSphere)`
   at genus = 0. These are all textbook-equivalent (Dolbeault ↔ Serre
   duality ↔ RR ↔ uniformization). **All structural reductions are
   unconditional in tree and compile-verified.** Item 14 is **shipped
   conditional** on this named hypothesis per the 2026-05-26 decision.
   Authoritative LOC audit: abstract-X closure floor ~28k–35k LOC
   (Arc 1, RR + Serre duality); the ~10k Behnke–Stein arc is **RS-only
   and does not advance abstract-X Item 14** (RS is already closed).
   **Trace verified (2026-05-28):** the wall is `H¹(X, 𝒪) = 0` at
   genus 0 = Serre duality — `DBarSolvabilityAtGenusZero X` is
   defined-once / consumed-once / never-discharged, and the Pompeiu
   arc proves the axiom-free `∂̄(globalSolutionCandidate) = α +
   outerRingLeakage` identity (`Manifold/OuterRingLeakage.lean`) whose
   residual leakage vanishes only given the global cohomology
   vanishing. See `HANDOFF_ITEM14.md` "WALL DOCUMENTED" + canonical
   ACTIVE ARC + "Trace verification (2026-05-28)" for the chain proof,
   file:line citations, and arc-by-arc audit.

2. **C3's `C3FullInputExt X`** — bundle of Riemann bilinear relations
   + Abel's theorem + Jacobi inversion + AbelJacobi smoothness +
   AbelJacobi injectivity. Closes items 5/11/12/13/17 collectively
   once landed. Per-curve `C3FullInputCurve B_X B_Y f hf` (period-
   pairing adjunction) closes items 18/21. Items 5/11/12/13/17/18/21
   are **shipped CONDITIONAL** on these named hypotheses per the
   2026-05-26 ship-conditional decision (analog of Item 14). RS-case
   unconditionally closed via subsingleton. Authoritative LOC audit
   (2026-05-26, four parallel decomposition passes): ~44–75k LOC across full
   C3 cluster on abstract X, midpoint ~57k (~40–60k after shared-
   structure deduplication). Equivalent textbook content: Forster
   Ch. III §16-21 + Griffiths-Harris Ch. 2 §2-§3. See
   [`HANDOFF_C3.md`](HANDOFF_C3.md) "WALL DOCUMENTED" for the
   canonical chain, per-field discharge status with file:line cites,
   highest-leverage near-term chips, and structural-rewire deferral
   reasoning. **Update 2026-06-09:** `TLAbelConverseHypothesis L`
   (formerly priced as a ~500–800 LOC Weierstrass-σ arc) is now a
   THEOREM given `TLDivSumHypothesis L`
   (`Manifold/TLAbelConverseFromTLDivSum.lean`, chord-and-tangent via
   mathlib's ℘ + in-tree residue theorem; ~1,850 LOC across 6 files).
   The full T_L C3 closure
   (`nonempty_C3FullInputExtSymp_complexTorus_of_TLDivSum`) is
   conditional on the SINGLE named hypothesis `TLDivSumHypothesis L`
   (forward Abel, ~2–4k LOC contour-integration arc). No Basic.lean
   item flips; the named-hypothesis pile for T_L shrinks 2 → 1.

**Historical framing kept below for git-blame continuity:**

(Pre-2026-05-24 merge there were 3 walls; BSLB became obsolete when
the étale-primitives arc merged in. Pre-canonical the Item 14 wall
was named `DBarSolvabilityAtGenusZero X`; canonical renames it
`ExistsMeroSimplePole_GenusZero X` per Forster's textbook name. The
reverse leg `S2ImpliesGenus0 X` is unconditionally discharged on
arbitrary X by `s2ImpliesGenus0_etalePrimitivesArc`
(`Topology/S2ImpliesGenus0FromEtalePrimitives.lean`); the one-input
composition `Topology/Item14FromHSPOnly.genus_eq_zero_iff_homeo_from_hSP`
shows Item 14 reduces to hSP alone.)

The infrastructure is enormously over-built (1072 `.lean` files,
182k LOC), but the genuine remaining classical content is textbook
Forster Ch. III §16–21 / Griffiths-Harris Ch. 2 §2–§3.

## Mathlib-prerequisite candidates (likely needed before strict closure)

- ~~**Whitney smooth approximation for manifold-valued maps**~~ —
  was tagged for the BSLB path; **obsolete after the 2026-05-24
  étale-primitives merge** (reverse leg discharged unconditionally
  without Whitney machinery).
- **Cauchy-Pompeiu kernel + ∂̄-solvability on disks** — **DONE in tree
  for the local statement** (`Analysis/PompeiuKernelCauchyPompeiu.lean`,
  axiom-free) and patched to a global candidate. **Does not by itself
  close item 14** — the partition-of-unity patch leaves a residual
  `outerRingLeakage` term (`Manifold/OuterRingLeakage.lean`) that
  vanishes only given the global `H¹(𝒪) = 0` at genus 0 (Serre
  duality). Trace 2026-05-28 confirms the Pompeiu arc stops exactly at
  this wall; no in-tree cutoff/partition construction crosses it.
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
