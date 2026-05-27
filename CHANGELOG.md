# Changelog

## 2026-05-26 — v0.4 spec alignment (notation swap; mathlib pin unchanged)

Updated `JacobianChallenge/Basic.lean`'s 5 instance/lemma signatures
that use the model-with-corners notation, from v0.3's `modelWithCornersSelf
ℂ (Fin (genus X) → ℂ)` to v0.4's `𝓘(ℂ, Fin (genus X) → ℂ)`. Affected:
items 12 (`IsManifold`), 13 (`LieAddGroup`), 17 (`ofCurve_contMDiff`),
18 (`pushforward_contMDiff`), 21 (`pullback_contMDiff`).

Per Buzzard's v0.4 changelog (2026-05-21 gist revision): "v0.4 is
syntactically identical to v0.3" — the swap is purely cosmetic and the
two notations are definitionally equal in mathlib.

Mathlib pin **NOT bumped**: stays at v0.3's `8e3c989...` (2026-04-15)
rather than v0.4's `548398201a...` (2026-05-15). Reasoning documented
in `lakefile.toml` pin comment. Bumping the pin would require a
full-repo recompile from source (no `cache get` per CLAUDE.md
apfsd-panic constraint) — a multi-day commitment with breakage risk,
not justified by Buzzard's own "syntactically identical" assessment of
the math content.

`Basic.lean` compile-verified clean (`LEAN_NUM_THREADS=1 lake env lean
JacobianChallenge/Basic.lean` → exit 0) after the swap.

## 2026-05-26 — C3 SHIPPED CONDITIONAL on `C3FullInputExt X` + per-curve `C3FullInputCurve` + HANDOFF_C3 canonical

**Decision**: ship items 5/11/12/13/17/18/21 (the Jacobian-side
ChartedSpace + related instances + holomorphicity cluster) CONDITIONAL
on the named classical hypotheses `C3FullInputExt X` (for items
5/11/12/13/17) and per-curve `C3FullInputCurve B_X B_Y f hf` (for items
18/21). The C3 analog of the Item 14 ship-conditional decision. RS-case
unconditionally closed via subsingleton route.

### Authoritative four-agent C3 audit

Four parallel sub-agents using the same Pompeiu calibration (~6,500
LOC/substantial classical theorem, measured from 6,587-LOC Pompeiu chain).
Per-field findings (every cell file:line verified):

| Field | RS | ℂ⧸L | Arbitrary X (remaining) |
|---|---|---|---|
| `PeriodLatticeAnalyticHypotheses` | ✅ | ✅ | ~23–41k LOC (mid 32k) — 4 named atoms: SmoothSymplecticBasis, riemannBilinear, SubdivisionTelescopingTo2Simplex_named, SmoothHurewiczHypothesis |
| `AbelHypothesis` | ✅ unconditional via genus 0 | conditional on `TLDivSumHypothesis L` (~2–4k LOC) | ~4–10k LOC (mid 7k) via `AbelLatticeWitness X α h` |
| `JacobiInversion` (surj+inj) | ✅ | surj ✅; inj conditional on `TLAbelConverseHypothesis L` (~500–800 LOC — Weierstrass-σ; uses existing mathlib ℘) | ~13–16.5k LOC (theta or compactness/open-mapping route) |
| `AbelJacobiSmoothness` | ✅ | ✅ unconditional | ~1.5–3k LOC (wiring chip) |
| `AbelJacobiInjective` | ✅ | ✅ unconditional | ~300 LOC if Abel converse done; ~6.5k standalone |
| Structural rewire (Basic.lean Jacobian X → fire analytic-Jacobian instances) | — | — | ~400–800 LOC (route 2) or ~1,500+ (route 1). **DEFERRED** — strict-signature incompatible per `feedback_jacobian_strict_closed_bar`. |
| Per-curve `lattice_match` (items 18/21 strict-closed without per-curve typeclass arg) | — | — | ~2–4k LOC classical (period-pairing adjunction `∫_{f_*γ} α = ∫_γ f^*α`) |

**Total C3 cluster on abstract X**: ~44–75k LOC (midpoint ~57k), or
~40–60k after shared-structure deduplication. Comparison: Item 14
abstract-X = ~28–50k LOC. C3 is larger but closes 7 items vs Item 14's
1 — higher scoreboard leverage per LOC.

**Highest-leverage near-term chips** (not full closure):
1. Weierstrass-σ on T_L (~500–800 LOC) — discharges `TLAbelConverseHypothesis L`.
2. `TLDivSumHypothesis L` discharge (~2–4k LOC) — makes `AbelHypothesis` on T_L unconditional.
3. Structural rewire (DEFERRED, ~400–800 LOC if feasible) — would auto-discharge items 5/11/12/13 on RS via typeclass mechanism.

### Documentation changes

* **`HANDOFF_C3.md`** — NEW canonical doc. Mirror of `HANDOFF_ITEM14.md`
  "WALL DOCUMENTED" section. Per-field discharge status with file:line,
  authoritative LOC audit, highest-leverage chips, structural-rewire
  deferral reasoning, mathlib state, related-canonical-docs index.
* **`OPEN.md`** — Items 5/11/12/13/17/18/21 rows updated with
  "SHIPPED CONDITIONAL" status + canonical pointer. Bottom-line
  C3 framing rewritten with full named-hypothesis list + audit numbers.
* **`REPO_AUDIT.md`** — same item rows updated.
* **`C3_AUDIT.md`** — analytical content folded into HANDOFF_C3
  canonical (file subsequently removed during pre-release cleanup).
* **`README.md`** — Status section updated to canonical C3 framing.
* **`JacobianChallenge/Basic.lean`** — comment blocks added at the
  7 sorry sites (lines 137/142/145/148/159/194/235) documenting the
  closure chain (`C3FullInputExt X` + per-curve `C3FullInputCurve`)
  and pointing to HANDOFF_C3. Sorries stay — Buzzard's strict signature
  does not admit added typeclass args.

### Why the structural rewire was deferred

The audit verified Basic.lean's instance signatures (lines 137/142/145/148/
159/194/235) take only the ambient `[TopologicalSpace X] [T2Space X]
[CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]`
typeclass args. Adding `[Nonempty (C3FullInputExt X)]` would change
Buzzard's signature, which the strict-closed bar per
`feedback_jacobian_strict_closed_bar` does not admit. The heavier
route-1 rewire (redefining `Jacobian X = JacobianAnalyticChoice X`)
would break the existing `Pic⁰`-based `ofCurve`/`pushforward`/`pullback`
discharges of items 6/7/8/22 — net regression. Same finish as Item 14.

## 2026-05-26 — Item 14 SHIPPED CONDITIONAL on `ExistsMeroSimplePole_GenusZero X` + doc consolidation

**Decision**: ship Item 14 conditional on the named classical
hypothesis `ExistsMeroSimplePole_GenusZero X` (= Forster Thm 16.9)
and document the wall. The chip-velocity phase for Item 14
abstract-X closure is over; remaining work is multi-thousand-LOC
classical-mathlib-grade content. Per Buzzard's challenge spirit,
packaging difficult classical theorems as named opens is the
appropriate finish at this mathlib pin.

### Authoritative LOC audit (commit `88270f7`)

Four parallel sub-agents with 6,500-LOC-per-substantial-theorem
calibration from the measured Pompeiu chain (`Analysis/Pompeiu*.lean`
+ `Analysis/InvNorm*.lean` = 6,587 LOC, 250 declarations, 1 substantial
theorem `partialZBar_pompeiuKernel_eq_self`). Findings:

* **Arc 1 (RR + Serre)**: ~28k–35k LOC remaining for abstract-X
  closure (Forster Ch.15-17 decomposition); ~16.5k LOC of relevant
  in-tree scaffolding already paid. Sub-theorems: coherent analytic
  sheaves, Cartan-Serre finiteness, Leray-on-Stein, RR index, Serre
  duality.
* **Arc 2 (Behnke-Stein on disk + Cousin I)**: ~10k LOC for RS-only
  closure (McMullen Berkeley 241/96 Thms 7.1-7.6); abstract X bundles
  with uniformization step = ~38k–56k LOC total. Pompeiu Phase A
  + bridges = 7,560 LOC reusable; 5,373 LOC partition-Pompeiu chain
  is mostly sunk cost for this arc.
* **Arc 3 (Dirichlet / Green's, Forster Ch.27-28)**: ~26k–46k LOC
  remaining; requires Sobolev-on-manifolds + Laplace-Beltrami +
  Rellich-Kondrachov + Dirichlet principle + Weyl's lemma + Green's
  function — none in mathlib at pin or HEAD; each is its own
  mathlib-scale sub-project.
* **External survey**: pin is ~6 weeks old (2026-04-15 vs.
  currentDate 2026-05-26). Mathlib HEAD has incremental sheaf-cohomology
  API; pin-bump saves <1k LOC. No external Lean project formalizing
  RS/RR/Serre/Hodge/uniformization. Joël Riou's derived-categories
  foundation in mathlib, but Serre duality "on roadmap, not implemented".

### Documentation changes (commits `17d4104`, `88270f7`, `ccee13b`)

Consolidates Item 14 frontier story into a single canonical source:

* `HANDOFF_ITEM14.md` — "WALL DOCUMENTED — SHIPPED CONDITIONAL"
  header above canonical "ACTIVE ARC — CANONICAL CURRENT STATE"
  section, with `ExistsMeroSimplePole_GenusZero` definition site
  + full chain entry-point (file:line for each link) + textbook-
  equivalent-names list + arc-by-arc audit numbers.
* `README.md` Status — canonical framing (Item 14 conditional, RS-case
  unconditional, pointer to HANDOFF).
* `JacobianChallenge/Basic.lean` — comment block above the
  `genus_eq_zero_iff_homeo` `sorry` documenting the closure chain
  and named hypothesis the sorry is gated on. `sorry` stays
  (Buzzard's signature has no hypothesis slot; consuming as `axiom`
  deliberately avoided). Compile verified.
* `OPEN.md` + `REPO_AUDIT.md` Item 14 rows — one-line canonical
  pointers; pre-canonical session-by-session narrative preserved
  as "Historical session log follows".
* `OPEN.md` "Bottom line" — 2-walls framing rewritten to canonical
  name `ExistsMeroSimplePole_GenusZero X` (Forster Thm 16.9) with
  textbook-equivalent-names list explicit.
* Audit docs (`DBAR_CONSUMER_AUDIT`, `REARCHITECTURE_AUDIT`,
  `UNIFORMIZATION_ROUTE_AUDIT`, `HSP_AUDIT`) — SUPERSEDED banners
  pointing to HANDOFF canonical.
* `Item14FinalComposition.lean` + `BijectiveAnalyticToBiholomorphism.lean`
  docstrings — updated to reflect 3 of 4 inputs of the four-input
  chain unconditionally discharged. Both compile-verified.

### Verification

Compile-verified (`LEAN_NUM_THREADS=1 lake env lean FILE.lean`,
exit 0): `Topology/HTopFromSubsingleton.lean` (the three
`*_holds_unconditional` discharges compose to unconditional
`DegreeOneIsBiholomorphic_RS X`); `Manifold/BijectiveAnalyticToBiholomorphism.lean`;
`Topology/Item14FinalComposition.lean`; `JacobianChallenge/Basic.lean`.

## Older history

Per-commit history before 2026-05-26 is preserved in the git log; the
verbose session-by-session chip narrative has been trimmed from this
file. For the per-commit reasoning trail, use `git log --oneline` and
`git log -p`.
