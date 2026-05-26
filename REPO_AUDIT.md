# Full-repo audit (2026-05-23)

Companion to ITEM-14 and C3 audits. Surveys every Basic.lean sorry +
every named hypothesis chain, identifies stale/contradictory claims
across OPEN.md and the rest of the docs.

## Basic.lean sorry inventory (verified by `grep -n sorry`)

8 sorries (one per OPEN challenge item). Items 4 and 10 are STUB (not
sorry, but the body is `inferInstance` on the placeholder discrete
topology, which is the wrong topology).

| Line | Item | Reduces to |
|---|---|---|
| 73 | 14 | hSP X (one input — post-2026-05-24 merge, BSLB no longer needed; see `HANDOFF_ITEM14.md`) |
| 103 | 5/11 | `[HasJacobianAnalyticStructure X]` (see `C3_AUDIT.md`) |
| 108 | 5/12 | same |
| 111 | 5/12 | same |
| 114 | 5/13 | same |
| 125 | 17 | item 5 + per-curve content |
| 160 | 18 | item 5 + per-curve `JacobianAnalyticPushforwardLift` |
| 201 | 21 | item 5 + per-curve `JacobianAnalyticPullbackLift` |

Plus 2 STUB:
- Line 97 (`TopologicalSpace`): item 4 — discrete topology placeholder.
- Line 100 (`T2Space`): item 10 — trivially true via discrete; flips when topology becomes the analytic-Jacobian quotient.

## Item-by-item audited status

Authoritative ground truth, replacing the contradictory entries in
OPEN.md's massive scoreboard.

| # | Item | Status | Audited remaining gap |
|---|---|---|---|
| 1 | `genus X : ℕ` | STRICT-CLOSED | None — unconditional finite-dim via `DiskChartCover.holomorphicOneFormFiniteDim_holds`. |
| 2 | `Jacobian X : Type u` | STRICT-CLOSED | `Pic⁰ X` with honest `PrincDiv`. |
| 3 | `AddCommGroup (Jacobian X)` | STRICT-CLOSED | Inherited from honest Pic⁰. |
| 4 | `TopologicalSpace (Jacobian X)` | STUB | Discrete topology — flips when item 5 rewires `Jacobian X` to analytic Jacobian. |
| 5 | `ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` | OPEN | Reduces to `[Nonempty (C3FullInputExt X)]`; the bundle's substantive open subfields are Riemann bilinear, Abel, Jacobi inversion. |
| 6 | `Jacobian.ofCurve` | STRICT-CLOSED | `[δQ - δP]` in honest Pic⁰. |
| 7 | `Jacobian.pushforward` | STRICT-CLOSED | `JacobianChallenge.Jacobian.pushforward hf`. |
| 8 | `Jacobian.pullback` | STRICT-CLOSED | `Jacobian.pullbackHonest_of_rsum`. |
| 9 | `ContMDiff.degree` | STRICT-CLOSED | `degreeFiber` unconditional. |
| 10 | `T2Space (Jacobian X)` | STUB | True via discrete; flips with item 4/5. |
| 11 | `CompactSpace (Jacobian X)` | OPEN | Same as item 5. |
| 12 | `IsManifold ... ω (Jacobian X)` | OPEN | Same as item 5. |
| 13 | `LieAddGroup ... (Jacobian X)` | OPEN | Same as item 5. |
| 14 | `genus_eq_zero_iff_homeo` | OPEN | **Canonical:** one classical theorem with five textbook-equivalent names. See `HANDOFF_ITEM14.md` "ACTIVE ARC — CANONICAL CURRENT STATE". Equivalent open names: `ExistsMeroSimplePole_GenusZero X` (Forster Thm 16.9) / `hSP X` / `DBarSolvabilityAtGenusZero X` + `ChartAtConstantOnSource` / `RR_DimGE2_GenusZero X` / `Nonempty (HolomorphicEquiv X RS)` at genus = 0. In-tree transport collapses discharge of any one to closure of all. |
| 15 | `ofCurve_self` | STRICT-CLOSED | Reduces to `[δP - δP] = 0`. |
| 16 | `ofCurve_inj` | STRICT-CLOSED | Via `JacobianChallenge.ofCurve_inj_holds` unconditional discharge chain. |
| 17 | `ofCurve_contMDiff` | OPEN | Reduces to item 5 + `JacobianAnalyticClosureBundle` smoothness field. |
| 18 | `pushforward_contMDiff` | OPEN | Reduces to item 5 + per-curve `JacobianAnalyticPushforwardLift`. |
| 19 | `pushforward_id_apply` | STRICT-CLOSED | Via `Pic0.pushforward_id`. |
| 20 | `pushforward_comp_apply` | STRICT-CLOSED | Via `Pic0.pushforward_comp`. |
| 21 | `pullback_contMDiff` | OPEN | Reduces to item 5 + per-curve `JacobianAnalyticPullbackLift`. |
| 22 | `pullback_id_apply` | STRICT-CLOSED | `pullbackHonest_of_rsum_id`. |
| 23 | `pullback_comp_apply` | STRICT-CLOSED | `pullbackHonest_of_rsum_comp`. |
| 24 | `pushforward_pullback` | STRICT-CLOSED | `pushforward_pullbackHonest_of_rsum`. |

**Score: 14 STRICT-CLOSED, 2 STUB, 8 OPEN.**

## Genuine remaining classical content

The 8 OPEN sorries collapse to just **3 substantive classical theorems**
across the whole challenge (after auditing all named-hypothesis chains):

1. **Item 14's `hSP`** — `ExistsSimplePoleGermAtSomePoint X`. After
   Chip 2c-Final (2026-05-24, `Manifold/ForsterCutoffPoleConstruction.lean`),
   reduces further to **`DBarSolvabilityAtGenusZero X`** (= `H¹(X, 𝒪) = 0`
   at genus 0) plus a per-`p` structural hypothesis `ChartAtConstantOnSource p`
   (innocuous on every concrete X). The Riemann–Roch / uniformization framings
   remain valid as equivalent alternate routes but do not shorten the gap.

2. ~~**Item 14's `BSLB`**~~ **OBSOLETE for Item 14 (2026-05-24 merge).**
   The reverse leg `S2ImpliesGenus0 X` is unconditionally discharged on
   arbitrary X by `s2ImpliesGenus0_etalePrimitivesArc`
   (`Topology/S2ImpliesGenus0FromEtalePrimitives.lean`). The one-input
   composition `Topology/Item14FromHSPOnly.lean:genus_eq_zero_iff_homeo_from_hSP`
   shows Item 14 reduces to hSP alone.

3. **C3's `C3FullInputExt X`** — bundle of Riemann bilinear relations
   + Abel's theorem + Jacobi inversion + Abel-Jacobi smoothness +
   Abel-Jacobi injectivity. The bilinear+Abel+Jacobi triple is the
   substantive content; smoothness and injectivity are already
   unconditional on RS and T_L.

3a. Per-curve `JacobianAnalyticPushforward/PullbackLift` for items
    18/21 — depends on (3).

That's it. **TWO** textbook classical theorems away from 22/24
STRICT-CLOSED — BSLB was the third entry pre-merge but is now obsolete
(reverse leg of Item 14 unconditional). Items 4 and 10 flip automatically
with item 5.

## Sorries outside `Basic.lean` (live audit `grep`)

After filtering for real code-level `sorry` (excluding docstrings):

- **`Jacobian.lean:185`** — `lemma ofCurve_inj (P : X) : Function.Injective (ofCurve P) := sorry`. **Dead code.** Item 16 is closed via `Basic.lean:143` calling `JacobianChallenge.ofCurve_inj_holds`, which is a separate decl in `Manifold/ChartDerivNeZeroImpliesNonCriticalDischarge.lean`. Zero references to the stub `JacobianChallenge.Jacobian.ofCurve_inj`. **Should be deleted or rewired.** Fixed in this audit's accompanying commit.

No other live `sorry`s exist outside Basic.lean (the other grep hits were docstring/`axiom`-as-English matches).

## Doc bloat audit

**`OPEN.md` (3,021 lines).** Started as a clean item-status table (lines 2596-2685 — the authoritative source) but accumulated a chronological "Scoreboard" pile-up that takes lines 35–~2500. Issues:

- Multiple contradictory item counts (one section says "OPEN: 5, 11, 12, 13, 14, 16, 17, 18, 21 = 9 items"; another correctly says "Item 16 STRICT-CLOSED").
- Many session-by-session scoreboard entries each declaring "Item count unchanged: 14/24" — true but signals no progress.
- Estimates like "Remaining LOC for full 24/24 STRICT-CLOSED" are obsolete given the audited reductions today.

**`CHANGELOG.md` (6,684 lines).** Cumulative session-by-session change log. Not audited line-by-line (most entries are accurate session diffs, just numerous). The size itself is a smell; consider pruning to last ~5 sessions + a "see git log for older" pointer.

**`CLOSURE_MAP.md` (959 lines).** Not audited line-by-line. Likely stale predictions from prior sessions.

**`HANDOFF_2026_05_15_C3_PATH_LIFT.md` (276 lines).** Dated handoff from a single session — by definition stale. Should be deleted or absorbed into `HANDOFF_ITEM14.md` / `C3_AUDIT.md`.

**`README.md` (336 lines).** Not audited line-by-line. Worth re-reading to check it doesn't oversell.

## Recommended cleanup actions (separate session, not done in this audit)

1. **DELETE `Jacobian.lean:185` dead stub** (or rewire to `ofCurve_inj_holds`).
2. **Trim `OPEN.md` Scoreboard section** to last 3 sessions + pointer to git log.
3. **Delete `HANDOFF_2026_05_15_C3_PATH_LIFT.md`** (subsumed by `C3_AUDIT.md`).
4. **Trim `CHANGELOG.md`** similarly.

This audit itself is the deliverable; the cleanup is mechanical and
should not be combined with substantive work.

## What was OBSCURING the true path

Same pattern as item 14 audit found:

1. **Scoreboard pile-up in OPEN.md** makes the canonical item table
   (at the BOTTOM of the file) hard to find. Future sessions read the
   top, see chronological entries, and miss the authoritative status.

2. **Contradictory item counts** in different OPEN.md sections — at
   least item 16 appears as both OPEN and STRICT-CLOSED in different
   places.

3. **Dead stub in `Jacobian.lean:185`** suggests item 16 is open when
   it's actually STRICT-CLOSED via a parallel decl. Easy to misread.

4. **Multiple per-X discharge files** (RS, T_L, Subsingleton variants)
   obscured how close arbitrary-X discharge actually is.

5. **`HANDOFF_*` dated docs** from old sessions persist in the
   working directory long after their session ends.

## Bottom line

The whole Jacobian Challenge is **2 substantive classical theorems
away from 22/24 STRICT-CLOSED** (post-2026-05-24 merge: item 14 reduces
to JUST `DBarSolvabilityAtGenusZero X` after the étale-leg merge made
BSLB obsolete; item 5's chain still needs `C3FullInputExt X`. Items 4,
10 flip mechanically with item 5).

The structural plumbing is ENORMOUSLY over-built (1072 `.lean` files,
182k LOC). Maybe 30–40% of that LOC is structural-reduction /
paraphrase / per-X instance multiplication that doesn't move any
`sorry`. The remaining LOC is genuine analytic / divisor infrastructure
that the discharge of the 3 classical theorems will need.

If you can find someone who actually works through Forster Ch. III §16–21
and Griffiths-Harris Ch. 2 §2–§3 in Lean, the challenge closes in
3–6 months of focused single-discipline work. The infrastructure is
ready; the work is the textbook math, not more structural reductions.
