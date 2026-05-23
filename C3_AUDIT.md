# C3 deep audit (2026-05-23)

Companion to the item-14 audit. Same fresh-eyes lens: what's actually in
tree, what would actually flip Basic.lean sorries.

## Basic.lean sorries C3 targets

Beyond item 14 (line 73 — `genus_eq_zero_iff_homeo`, audited separately),
Basic.lean has 7 sorries:

| Line | Sorry | OPEN.md item |
|---|---|---|
| 103 | `instance : CompactSpace (Jacobian X)` | ~5 |
| 108 | `instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` | ~6 |
| 111 | `instance : IsManifold ... ω (Jacobian X)` | ~7 |
| 114 | `instance : LieAddGroup ... (Jacobian X)` | ~8 |
| 125 | `ofCurve_contMDiff` | 17 |
| 160 | `pushforward_contMDiff` | 18 |
| 201 | `pullback_contMDiff` | 21 |

Plus item 16 (`ofCurve_inj`) was reverted to OPEN per OPEN.md.

## What's UNCONDITIONAL in tree (verified sorry-free 2026-05-23)

- `FiniteDimensional ℂ (HolomorphicOneForm X)` via `DiskChartCover.holomorphicOneFormFiniteDim_holds`.
- `Subsingleton (Pic0 RiemannSphere)` (so `Subsingleton (Jacobian RiemannSphere)`).
- All Basic.lean Jacobian sorries are discharged on RS via the subsingleton route
  ([`Manifold/JacobianRiemannSphereInstances.lean`](JacobianChallenge/Manifold/JacobianRiemannSphereInstances.lean),
  [`Manifold/JacobianSubsingletonInstances.lean`](JacobianChallenge/Manifold/JacobianSubsingletonInstances.lean)).
- The whole `CanonicalAnalyticJacobianAnonymous X` machinery
  ([`Manifold/HasJacobianAnalyticStructure.lean`](JacobianChallenge/Manifold/HasJacobianAnalyticStructure.lean))
  with all 7 manifold-instance fields (AddCommGroup, TopologicalSpace,
  T2Space, CompactSpace, ChartedSpace, IsManifold, LieAddGroup) under
  `[HasJacobianAnalyticStructure X]`.
- `HasJacobianAnalyticStructure RiemannSphere` and `HasJacobianAnalyticStructure (ℂ ⧸ L)`
  unconditional instances.
- Items 16/17/18/21 closed at the AnalyticJacobian level via
  [`Manifold/JacobianAnalyticBasicLeanReduction.lean`](JacobianChallenge/Manifold/JacobianAnalyticBasicLeanReduction.lean)
  from a `JacobianAnalyticClosureBundle` + per-curve lifts.

## The cleanest in-tree reduction (per OPEN.md + traced)

All Basic.lean Jacobian-side sorries reduce to:
- **`[Nonempty (C3FullInputExt X)]`** — a single classical existence input
  bundling: basis (auto from item 1), period-lattice discreteness
  (Riemann bilinear), Abel-Jacobi input, Abel's theorem, Jacobi
  inversion, plus the smoothness + injectivity extension.
- **per-curve `Nonempty (C3FullInputCurve B_X B_Y f hf)`** — for items
  18 and 21 (pushforward/pullback functoriality).

The structural plumbing chain is complete: `C3FullInputExt X` →
`JacobianAnalyticChoice X` → all 7 instances on a Choice-style analytic
Jacobian → `picZeroEquiv : Pic⁰ X ≃+ JacobianAnalyticChoice X` AddEquiv
bridge to `Basic.lean`'s `Jacobian X = Pic⁰ X`.

## The remaining classical content (genuine open work)

`C3FullInputExt X` bundle has these named fields, none in mathlib:

1. **`PeriodLatticeAnalyticHypotheses`** (= "discreteness")
   ([`Manifold/PeriodLatticeFromPairing.lean:182`](JacobianChallenge/Manifold/PeriodLatticeFromPairing.lean)) —
   4 named subfields:
   - `isClosed` (period image closed in ℂᵍ);
   - `rank_eq` (ℤ-rank = 2g);
   - `discreteTopology`;
   - `isZLattice` (ℝ-span = ⊤).

   Classical content: **Riemann bilinear relations** + **integral
   homology basis** (H₁(X; ℤ) ≅ ℤ²ᵍ). Not in mathlib. On RS vacuous
   (genus 0); on T_L explicit (concrete lattice).

2. **`AbelHypothesis`** (Abel's theorem on compact Riemann surfaces)
   — image of any principal divisor in the period lattice is 0.
   On RS vacuous; on T_L reduces to `TLDivSumHypothesis`
   (Abel for elliptic curves = ∮ d log f = 0 on period parallelogram).
   Classical theorem, not in mathlib.

3. **`JacobiInversion`** (Jacobi inversion theorem) — the period map
   `Pic⁰ X → Cᵍ/Λ` is surjective. Equivalent to the Weierstrass-σ
   existence theorem on T_L (genus 1 case).
   Classical theorem, not in mathlib.

4. **`AbelJacobiSmoothness`** + **`AbelJacobiInjective`** — both
   discharged unconditionally on RS and T_L (recent sessions),
   classical content for general X.

For items 18/21 (per-curve C3FullInputCurve): adds a `lattice_match`
certificate for the per-curve period-pairing adjunction.

## What was the user's "close to closing" memory?

Most likely: **the C3 structural reduction was nearly complete** —
ONE typeclass `[Nonempty (C3FullInputExt X)]` would flip 6+ Basic.lean
sorries simultaneously. This was achieved in tree as a typeclass-driven
bundle; the actual rewire of `JacobianChallenge.Jacobian X` from
`Pic⁰ X` to a definition that fires the analytic-Jacobian instances
is the remaining structural step.

The honest open work remaining is the actual classical content:
- Riemann bilinear relations on arbitrary X (= `PeriodLatticeAnalyticHypotheses`).
- Abel's theorem on arbitrary X.
- Jacobi inversion on arbitrary X.

These are textbook content (Forster Ch. III §16-21, Griffiths-Harris
Ch. 2 §2-§3) — each is a major theorem, multi-session work, but
**no mathlib-class theorem is missing**. The analytic-Jacobian
structure mathlib has via `OnePoint`, `Submodule.span`, etc. is
sufficient.

## What's been historically obscuring this

Looking at OPEN.md + the prior MEMORY.md "Current Status" wall (now
deleted):

- Session-by-session entries each declared "Item 14 reduces to N
  inputs" with N decreasing — true but misleading, because the
  remaining inputs were not getting smaller-content, just smaller-count.
- Same pattern with C3: many sessions reduced
  `C3FullInputSymp` → `C3FullInputExtSymp` → ... → packaged into
  `SmoothHomologyDataPackage` etc. The reduction count went down;
  the underlying classical content did not.
- The `JacobianGenusZeroInstancesAuto` + `JacobianSubsingletonInstances`
  + `JacobianRiemannSphereInstances` triple of discharge files
  collectively close ALL of Basic.lean's Jacobian sorries on RS
  unconditionally. This was not surfaced clearly in prior status docs.
- The 2026-05-20 entry mentions "[HasJacobianAnalyticStructure X]
  instance lands" as the blocker — that's correct, but the framing
  obscured how close the rewire actually is.

## Next-session work order (anti-paraphrase)

If user wants C3 closure on arbitrary X:

1. **Discharge `PeriodLatticeAnalyticHypotheses` on arbitrary X** — the
   single hardest classical input. Multi-session arc (Riemann bilinear
   relations). Once done, items 5/6/7/8 of Basic.lean (Jacobian-as-
   manifold) all flip via the existing rewire infrastructure.

2. **Discharge `AbelHypothesis` + `JacobiInversion` on arbitrary X** —
   second multi-session arc. Once done, items 16/17 flip (Abel-Jacobi
   injectivity + smoothness).

3. **Per-curve `lattice_match` certificates** for items 18/21
   (pushforward/pullback functoriality). Smaller arc, depends on 1+2.

## Discipline reminder

Do not write more `C3*From*` paraphrase chips. The chain has been
factored enough; the gap is genuine classical content. See
[`tools/chip-prompt-preamble.md`](tools/chip-prompt-preamble.md) for
the anti-paraphrase gates.
