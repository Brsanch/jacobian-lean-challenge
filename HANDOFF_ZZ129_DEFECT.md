# Handoff: `RegularValueWitnessReg` architectural defect (introduced ZZ129, surfaced ZZ170/ZZ171)

## Status: RESOLVED 2026-05-08 (ZZ172)

The structural fix landed on `main` at `030b1b3` (merge of `feat/zz172-degree-fix`,
commit `a25a43f`). CI green on first push (14m45s). Items below describe the
defect history and the chip plan; what was actually executed in ZZ172:

- `RegularValueWitnessReg` no longer takes `C : Set Y`. `is_regular` is now the
  chart-pullback-derivative-nonzero certificate inlined in the structure
  (matching the shape ZZ169's `LocalSheetData.ofContMDiffMfderivNeZero`
  consumes).
- `fibre_card_well_defined_at_regular_statement` drops the `∀ C` quantifier.
- Universally-false `h_C_fin` hypothesis removed from ZZ155 (`FibreCardWellDefinedAtRegular.lean`)
  and ZZ160 (`HurwitzWellDefinedFromHPath.lean`). Composers now take a
  per-`f` packaging existential.
- `degreeFiber_eq_witness_card_at_regular` bridge (`DegreeUnconditional.lean`)
  updated: `h_choice_reg` is the analytic certificate, not `value ∉ C`.

Remaining chip plan (see below): ZZ176 (compose unconditional discharge of
the corrected statement), ZZ177 (Basic.lean Pic0.pullback swap), ZZ178
(items 22/24 fall-out).

## TL;DR

Items 8/9/22/24 STRICT-CLOSE is blocked on a **provably false theorem statement** in `JacobianChallenge/Manifold/Degree.lean` (commit `4f88a7f7`, ZZ129). The defect surfaced when ZZ170 tried to discharge the composer ZZ155 unconditionally. Fix is multi-file but bounded (~5-8 chips). All the analytic content needed to discharge a *correctly-stated* theorem is in main as of HEAD `8d5e0b6`. The blocker is purely the broken type, not missing math.

## The defect

Commit `4f88a7f7` (ZZ129, dispatched 2026-05-07 to "strengthen `RegularValueWitness` with a regular-value certificate") introduced two problematic objects in `JacobianChallenge/Manifold/Degree.lean`:

```lean
structure RegularValueWitnessReg
    {X : Type u} {Y : Type v} (f : X → Y) (C : Set Y) where
  toWitness : RegularValueWitness f
  is_regular : toWitness.value ∉ C   -- <-- wrong predicate
```

```lean
def fibre_card_well_defined_at_regular_statement (X) (Y) ... : Prop :=
  ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ IsConstantMap f →
    ∀ (C : Set Y) (w₁ w₂ : RegularValueWitnessReg f C), w₁.card = w₂.card
```

**The bug**: `is_regular` certifies `value ∉ C` for an *arbitrary user-chosen* `C`, not against the canonical `critical_values f`. The consumer is free to pick `C := ∅` (or any set disjoint from critical values), and then a witness sitting at a critical point of `f` satisfies `value ∉ C` while having fibre cardinality strictly below the generic value.

## Counterexample

Take `f : RiemannSphere → RiemannSphere`, `f(z) = z²`. Critical values: `{0, ∞}`.

- Consumer picks `C := ∅`.
- `w₁ : RegularValueWitnessReg f ∅` with `value = 1`, `fiber = {1, -1}`, `card = 2`. Satisfies `1 ∉ ∅` ✓.
- `w₂ : RegularValueWitnessReg f ∅` with `value = 0`, `fiber = {0}`, `card = 1`. Satisfies `0 ∉ ∅` ✓.
- `w₁.card = 2 ≠ 1 = w₂.card`.

The theorem statement is provably false. No proof exists.

## Why it wasn't caught earlier

ZZ129's chip prompt asked for "a regular-value certificate added to `RegularValueWitness`." The agent added a certificate, but the certificate it added — `value ∉ C` for an arbitrary `C` — is vacuously satisfiable and doesn't carry the analytic regularity content that the *name* implies. I merged ZZ129 without auditing what `is_regular` actually meant against `critical_values f`. Standard audit-flag pattern (ZZ95, ZZ104, ZZ153 caught) but I missed this one.

The defect propagated through ZZ134 (`fibre_card_well_defined_on_regular_subset_holds_of_locallyConstant`), ZZ155 (`fibre_card_well_defined_at_regular_holds_of_lc_ncard_and_topo`), ZZ160 (`fibre_card_well_defined_at_regular_holds_of_h_path`). All these composers take a `h_C_fin : ∀ f hf hnc, ∀ C, C.Finite` hypothesis which is **also universally false** (asserts every subset of Y is finite) — the bogus hypothesis was hiding the unsoundness of the theorem statement they were trying to prove.

## What's actually in main and usable

The session built ~3.5k LOC of correctly-stated, sorry/axiom-free analytic content that **will compose with the corrected theorem**:

- `Manifold/AnalyticLocalNormalForm.lean` (ZZ151) — Hurwitz local model `f = w₀ + ψ^k`
- `Manifold/LocalBiholomorphism.lean` (ZZ152) — `AnalyticAt.exists_local_biholomorphism`
- `Manifold/ChartedSpaceLocPathConnected.lean` (ZZ162) — `LocPathConnectedSpace ℂ` + ChartedSpace lift
- `Manifold/ConnectedManifoldPathConnected.lean` (ZZ163)
- `Manifold/IsPathConnectedBallMinusCountable.lean` (ZZ164b) — ball-restricted puncture lemma
- `Manifold/ChartRestrictionToBall.lean` (ZZ164c)
- `Manifold/PathSubdivisionByCharts.lean` (ZZ165b) + `PathSubdivisionByBallCharts.lean` (ZZ165c)
- `Manifold/ChartOverlapAvoidance.lean` (ZZ165d) + `ChartOverlapAvoidanceFull.lean` (ZZ165e)
- `Manifold/PathConnectedComplFinite.lean` (ZZ165) — **unconditional** `IsPathConnected (Cᶜ : Set Y)` for connected complex 1-manifold + finite C
- `Manifold/HTopoUnconditional.lean` (ZZ166) — **unconditional** `h_topo`
- `Manifold/LocalSheetDataFromContMDiff.lean` (ZZ169, ~360 LOC) — manifold-transport: `LocalSheetData.ofContMDiffMfderivNeZero` from chart-pullback-deriv-nonzero

Plus the previously-merged `FibresFiniteUnconditional`, `RegularValueExistsUnconditional`, `CriticalSetFiniteUnconditional` (the latter only for `MeromorphicNonzero X → RiemannSphere`).

## Recommended fix

Drop `C` from `RegularValueWitnessReg` and replace `is_regular : value ∉ C` with the analytic condition directly:

```lean
structure RegularValueWitnessReg (f : X → Y) where
  value : Y
  fiber_finite : (f ⁻¹' {value}).Finite
  is_regular : ∀ x ∈ f ⁻¹' {value}, 
    deriv ((chartAt ℂ value) ∘ f ∘ (chartAt ℂ x).symm) 
          ((chartAt ℂ x) x) ≠ 0
```

This composes cleanly with ZZ169 (`LocalSheetData.ofContMDiffMfderivNeZero`) which already takes the chart-pullback-deriv form.

Drop the `C` parameter from `fibre_card_well_defined_at_regular_statement`:

```lean
def fibre_card_well_defined_at_regular_statement (X) (Y) ... : Prop :=
  ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ IsConstantMap f →
    ∀ (w₁ w₂ : RegularValueWitnessReg f), w₁.card = w₂.card
```

## Chip plan

1. **ZZ172**: Modify `Degree.lean` — drop `C` from `RegularValueWitnessReg`, replace `is_regular` body with analytic form, drop `C` from theorem statement. Update `RegularValueWitnessReg.{card,value,fiber_finite}` accessors. (~50-100 LOC in `Degree.lean`, breaks every consumer.)
2. **ZZ173**: Fix `Manifold/FibreCardOnRegularSubset.lean` (ZZ134) consumer — drop `∀ C` quantifier in `fibre_card_well_defined_on_regular_subset_holds_of_locallyConstant`; drop `h_supp`/`h_C_fin` plumbing. Use chart-pullback-deriv condition.
3. **ZZ174**: Fix `Manifold/FibreCardWellDefinedAtRegular.lean` (ZZ155) — same shape change.
4. **ZZ175**: Fix `Manifold/HurwitzWellDefinedFromHPath.lean` (ZZ160) — same.
5. **ZZ176**: Compose ZZ169 + ZZ165 + ZZ166 + corrected ZZ155/160 → unconditional `fibre_card_well_defined_at_regular_holds_unconditional`. Should be ~50-100 LOC if the types align.
6. **ZZ177**: Retry Basic.lean Pic0.pullback swap (ZZ167's blocked half). Need to check if `Pic0.pullback (f, hf, N, hN)`'s type-shape (`→+` vs `→ₜ+` from Basic.lean's `pullback_contMDiff`) reconciles. Also need `hN` constant-fibre-cardinality witness — should now be available unconditionally from ZZ176.
7. **ZZ178**: Verify items 22/24 fall out from `Pic0.pushforward_pullback = N • id` in `Divisor/FiberPullback.lean`.

## Critical-values for general Y

The recommended fix above bypasses the need for a general `critical_values : (X → Y) → Set Y` — the analytic condition replaces it. But if ZZ134's proof structure makes that impossible, the fallback is to define `critical_values f := {y | ∃ x ∈ f ⁻¹' {y}, deriv-at-chart-pullback = 0}` and prove it's finite for compact X → Y via the analytic identity theorem.

## Caveats

- The `Pic0.pullback` swap in `Basic.lean` (item 8) has a **second** blocker beyond the critical-set issue: `Basic.lean`'s `pullback_contMDiff` requires `Jacobian Y →ₜ+ Jacobian X` (continuous additive group hom), but `Divisor/FiberPullback.lean`'s `Pic0.pullback (f, hf, N, hN)` returns `Pic0 Y →+ Pic0 X` (just additive). This is per ZZ167's residuals. May need a `Pic0.pullback`-as-`→ₜ+` constructor (~50-100 LOC) on top of the chain above.
- `ContMDiff.degree`'s body in `Basic.lean` is currently `degreeFiber f hf` (honest, post-ZZ167) but well-definedness still relies on the broken theorem. Once the theorem is corrected and discharged, item 9's strict-closure flips automatically.
- `pullback_id_apply` in `Basic.lean:190` is still `sorry` because the current pullback body is the zero-stub. Fixes when the swap lands.

## Forward-projection caveat

Today's session over-projected closure several times. The above plan assumes:
- No more architectural surprises in ZZ134/ZZ155/ZZ160's *proof bodies* (only signature edits)
- No new mathlib gaps surface in the chart-pullback-deriv reformulation
- The `→+` vs `→ₜ+` reconciliation is mechanical

Each is plausible but unverified. Treat the chip plan as "next-action list," not a timeline.

## Repo state at handoff

- HEAD: `8d5e0b6` (post-ZZ169 merge)
- LOC: 38,775 across 174 files
- STRICT-CLOSED: 0/24
- The 4 cluster walls + Hurwitz wall progress: see OPEN.md cluster-audit verdict (~60-80% R5; 5-10% Hodge; ~50% Hurwitz pre-defect, blocked by this defect; ~5% Surface; ~15-25% Period-lattice).
