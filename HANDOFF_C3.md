# C3 — handoff

## ✅ WALL DOCUMENTED — SHIPPED CONDITIONAL (2026-05-26)

**Status decision**: Items 5/11/12/13/17/18/21 of `Basic.lean` (the
Jacobian-side typeclass-instance + holomorphicity cluster) are shipped
CONDITIONAL on the named classical hypotheses `C3FullInputExt X` (for
items 5/11/12/13/17) and per-curve `C3FullInputCurve B_X B_Y f hf`
(for items 18/21). All structural reductions are unconditional and
compile-verified in tree; the remaining gap is genuine classical
content (Riemann bilinear / Abel / Jacobi inversion / period-pairing
adjunction) requiring multi-thousand-LOC mathlib-grade infrastructure
not at this pin.

The structural rewire chip (~400–800 LOC of Equiv-transport that
would let items 5/11/12/13 auto-discharge on `RiemannSphere` via
`[Nonempty (C3FullInputExt X)]` typeclass) was investigated and
**deferred**: Basic.lean's instance signatures (lines 137/142/145/148/
159/194/235) take only the ambient `[TopologicalSpace X] [T2Space X]
[CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold
𝓘(ℂ) ω X]` typeclass args. Adding a `[Nonempty (C3FullInputExt X)]`
constraint would change Buzzard's signature, which the strict-closed
bar does not admit. The
heavier rewire-by-redefinition (route 1, ~1,500+ LOC redefining
`Jacobian X = JacobianAnalyticChoice X`) would break the existing
`Pic⁰`-based `ofCurve`/`pushforward`/`pullback` discharges of items
6/7/8/22 — net regression. Same finish as Item 14: sorries stay,
comment blocks document the chain.

This is the C3 analog of the Item 14 ship-conditional decision. Per
Buzzard's challenge spirit, packaging difficult classical theorems as
named open hypotheses is the appropriate finish at this mathlib pin.

* **Items 5/11/12/13/17/18/21 on `X = RiemannSphere`**: UNCONDITIONALLY
  closed via the subsingleton route — `Subsingleton (Pic⁰ RiemannSphere)`
  ([`Manifold/Pic0RiemannSphereSubsingleton.lean:163`](JacobianChallenge/Manifold/Pic0RiemannSphereSubsingleton.lean#L163))
  + [`Manifold/JacobianRiemannSphereInstances.lean`](JacobianChallenge/Manifold/JacobianRiemannSphereInstances.lean)
  + [`Manifold/JacobianSubsingletonInstances.lean`](JacobianChallenge/Manifold/JacobianSubsingletonInstances.lean).
  These provide every instance + every smoothness lemma on the concrete
  `Jacobian RiemannSphere` via the typeclass `Subsingleton`, not the
  `Basic.lean` signature itself.
* **Items 5/11/12/13/17 on abstract X**: conditional on
  `C3FullInputExt X` via the chain documented below.
* **Items 18/21 on abstract X**: additionally conditional on per-curve
  `C3FullInputCurve B_X B_Y f hf` (period-pairing adjunction under
  holomorphic `f`).
* **The chain entry-points (file:line for each link)**:
  `C3FullInputExt X` →
  [`Manifold/JacobianAnalyticChoice.lean:54+116`](JacobianChallenge/Manifold/JacobianAnalyticChoice.lean#L54)
  (`JacobianAnalyticChoice X` instance bundle + `picZeroEquiv` AddEquiv) →
  [`Manifold/JacobianAnalyticBasicLeanReduction.lean:70+113+134`](JacobianChallenge/Manifold/JacobianAnalyticBasicLeanReduction.lean#L70)
  (`analyticJacobian_ofCurve_contMDiff_of_bundle` /
  `analyticJacobian_pushforward_contMDiff_of_lift` /
  `analyticJacobian_pullback_contMDiff_of_lift`).
  For per-curve items 18/21:
  `C3FullInputCurve` →
  [`Manifold/C3FullInputCurve.lean:50+78+128`](JacobianChallenge/Manifold/C3FullInputCurve.lean#L50)
  (`toPushforwardLift` / `toPullbackLift`).

### Per-field status (verified cell-by-cell, 2026-05-26 deep audit)

`C3FullInputExt X` bundles 5 named fields. Per-X discharge status:

| Field | RS | ℂ⧸L (genus-1 torus) | Arbitrary X (remaining LOC) | Defined at |
|---|---|---|---|---|
| `PeriodLatticeAnalyticHypotheses` | ✅ unconditional via `trivial_at_genus_zero` ([`PeriodLatticeSymplecticBundle.lean:270`](JacobianChallenge/Manifold/PeriodLatticeSymplecticBundle.lean#L270)) | ✅ unconditional (explicit complex-torus chain) | **~23–41k LOC (mid 32k)**: 4 named atoms — `SmoothSymplecticBasis` (~8–15k), `riemannBilinear` (~6–10k), `SubdivisionTelescopingTo2Simplex_named` (~3–6k), `SmoothHurewiczHypothesis` (~6–10k) | [`Manifold/PeriodLatticeFromPairing.lean:182`](JacobianChallenge/Manifold/PeriodLatticeFromPairing.lean#L182) |
| `AbelHypothesis` | ✅ unconditional via `abelHypothesis_of_genus_zero` ([`Manifold/AbelHypothesisGenusZero.lean:113`](JacobianChallenge/Manifold/AbelHypothesisGenusZero.lean#L113)) | conditional on `TLDivSumHypothesis L` (**~2–4k LOC** — Liouville on fundamental parallelogram) | **~4–10k LOC (mid 7k)** via `AbelLatticeWitness X α h` — pushforward 1-form + residue on ℙ¹ + level-set chain | [`Manifold/AbelJacobiPic0.lean:73`](JacobianChallenge/Manifold/AbelJacobiPic0.lean#L73) |
| `JacobiInversion` (surj + inj) | ✅ via subsingleton | surj ✅ unconditional; inj conditional on `TLAbelConverseHypothesis L` (**~500–800 LOC** — Weierstrass-σ; uses mathlib's existing ℘) | **~13–16.5k LOC** (surj ~6.5–10k via theta or compactness/open-mapping + inj ~6.5k via Abel converse + ~2k mathlib-grade `Symᵍ X` charted-manifold) | [`Manifold/AbelJacobiIso.lean:70`](JacobianChallenge/Manifold/AbelJacobiIso.lean#L70) |
| `AbelJacobiSmoothness` | ✅ on RS | ✅ unconditional ([`Manifold/AbelJacobiSmoothnessComplexTorus.lean`](JacobianChallenge/Manifold/AbelJacobiSmoothnessComplexTorus.lean), 352 LOC) | **~1.5–3k LOC** (wiring chip; PathPrimitive/ChartLocal infra ~5,500 LOC already paid) | [`Manifold/JacobianAnalyticOfCurveContMDiff.lean:80`](JacobianChallenge/Manifold/JacobianAnalyticOfCurveContMDiff.lean#L80) |
| `AbelJacobiInjective` | ✅ vacuous | ✅ unconditional ([`Manifold/AbelJacobiInjectiveComplexTorus.lean:52`](JacobianChallenge/Manifold/AbelJacobiInjectiveComplexTorus.lean#L52), 118 LOC) | **~300 LOC if Abel converse done** (as part of JacobiInversion); ~6.5k standalone | [`Manifold/JacobianAnalyticOfCurveInjective.lean:54`](JacobianChallenge/Manifold/JacobianAnalyticOfCurveInjective.lean#L54) |

Plus structural pieces:

| Piece | Cost | Notes |
|---|---|---|
| **Structural rewire** of `Jacobian X = Pic⁰ X` to fire analytic-Jacobian instances | **~400–800 LOC (route 2)** or ~1,500+ (route 1). **DEFERRED** — strict-signature incompatible: Basic.lean instance signatures admit no extra typeclass argument, and a redefinition of `Jacobian X` would regress items 6/7/8/22 that currently discharge against `Pic⁰`. | All instances + `picZeroEquiv` already in tree at `JacobianAnalyticChoice.lean`; the rewire is the consumer side. |
| **Per-curve `lattice_match`** (items 18/21 strict-closed without per-curve typeclass arg) | **~2–4k LOC** classical (period-pairing adjunction `∫_{f_*γ} α = ∫_γ f^*α`) | Algebraic side in `HolomorphicOneFormPullbackMatrix.lean:103`; genuinely-open part is the integral identity on cycles. |

### Authoritative LOC totals

Sum across all classical content for full C3 cluster on abstract X:

```
PeriodLattice (32k mid)             ~23–41k LOC
AbelHypothesis (7k mid)              ~4–10k
JacobiInversion (14.75k mid)         ~13–16.5k
AbelJacobiSmoothness (2.25k mid)     ~1.5–3k
AbelJacobiInjective                  ~300 (if Abel converse done)
Structural rewire (DEFERRED)         ~400–800 or 1,500+
Per-curve lattice_match              ~2–4k
                                    -----------
Total range                          ~44–75k LOC
Midpoint                             ~57k LOC
```

**Shared structure adjustment**: Riemann bilinear (in PeriodLattice)
feeds Jacobi injectivity; Abel converse (in JacobiInversion) overlaps
Abel's theorem; smooth-Hurewicz prerequisite is shared. After
deduplication, **realistic total ~40–60k LOC** for full C3 cluster on
abstract X.

**Comparison to Item 14**: C3 (~40–60k LOC) is larger than Item 14
(~28–50k LOC) but closes **7 items vs Item 14's 1** — higher
scoreboard leverage per LOC.

**Wall-clock estimate** at this repo's measured chip velocity
(~2,250 LOC/session sustained from the 2026-05-26 partition-Pompeiu
session): ~20–30 sessions of dedicated focus = **~5–8 months at
current cadence**, longer if mathlib-grade prerequisites need to ship
upstream.

### Highest-leverage near-term chips (no full C3 commitment)

The audits surfaced three chips much smaller than the full cluster
that produce real progress:

1. **Weierstrass-σ on T_L (~500–800 LOC)** — discharges
   `TLAbelConverseHypothesis L`, making `JacobiInversion.injective` on
   T_L unconditional. Uses mathlib's existing ℘ infrastructure
   (`Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`).
   **Single highest-leverage gap** per the Jacobi audit. Self-contained
   classical content with no further prerequisites.
2. **`TLDivSumHypothesis L` discharge (~2–4k LOC)** — Liouville on
   fundamental parallelogram. Makes `AbelHypothesis` on T_L
   unconditional. "Lowest-hanging C3 fruit by calibration" per the
   Abel audit.
3. **Structural rewire (~400–800 LOC, possibly ~1,500+)** — DEFERRED
   pending strict-signature confirmation. Would flip items 5/11/12/13
   to typeclass-conditional closure on `[Nonempty (C3FullInputExt X)]`
   so they auto-discharge on RS via the subsingleton route at instance
   resolution time. **Risk**: incompatible with Buzzard's strict-closed
   bar.

None of (1)/(2) alone closes a Basic.lean item, but both produce
durably valuable infrastructure and shrink the T_L-side gap to zero.

### Mathlib state (pin 2026-04-15)

- ✅ `Module.ZLattice` infrastructure (`IsZLattice`, `ZSpan.span_top`,
  `instDiscreteTopology`, `ZLattice.rank`, basis).
- ✅ Weierstrass ℘ on T_L (`Mathlib/Analysis/SpecialFunctions/Elliptic/
  Weierstrass.lean` — `PeriodPair.weierstrassP`, derivative, cubic
  relation g₂/g₃).
- ✅ 1- and 2-variable Jacobi theta (`Mathlib/NumberTheory/ModularForms/
  JacobiTheta/{OneVariable,TwoVariable}.lean`).
- ⚠️ Abstract sheaf cohomology (Čech, Mayer-Vietoris, flasque) present
  but not specialized to analytic Riemann surfaces. Joël Riou's
  derived-categories foundation merged; Serre duality on roadmap, not
  implemented.
- ❌ Integral singular homology of compact 2-manifolds (`H₁(X;ℤ) ≅ ℤ^{2g}`).
- ❌ Smooth-Hurewicz / smooth-singular comparison on Riemannian
  manifolds.
- ❌ Surface classification (`compact connected oriented 2-manifold ≃ Σ_g`).
- ❌ Riemann theta on `ℂ^g`, vector of Riemann constants.
- ❌ Riemann-Roch / Serre duality on compact Riemann surfaces.
- ❌ Weierstrass σ-function.
- ❌ `Sym^g X` as charted complex manifold of dimension g.
- ❌ Period-pairing integration over cycles (repo-local
  `PeriodPairingData.ofSmoothCycle`).

Pin bump to HEAD (~6 weeks of delta) saves at most a few hundred LOC
of categorical scaffolding; the analytic-instantiation gaps above are
all unaffected.

### Trace verification (2026-05-28)

A symbol-level trace resolved this audit's first open unknown and
re-confirmed the honesty of the cluster:

- **`PeriodPairingData.ofSmoothCycle` is a working integration
  definition, NOT a hypothesis bundle.** `ofSmoothCycle`
  (`Manifold/PeriodPairingDataFromSmoothCycle.lean:64`) sets
  `H1 := SmoothCycle 𝓘(ℝ,ℂ) X` (= `ker (SmoothChain.boundary)`,
  `Manifold/SmoothCycle.lean:51`) and `pairing := complexPeriodBilinear`,
  which bottoms out at `complexPeriod → SmoothCycle.integrate →
  SmoothPath.integrate = ∫₀¹ ω(γt)(γ't) dt` (mathlib `intervalIntegral`,
  `Manifold/SmoothPathIntegral.lean:117`), axiom-free. **The flagged
  "+3–8k hidden LOC under that name" risk is retired** — the period
  integration is genuine, so the LOC totals above are not stub-inflated.
- **`C3FullInputExt X` is never constructed free for arbitrary X.** The
  arbitrary-X composite
  (`nonempty_c3FullInputExtSymp_of_hodgeChainViaStandardForm_and_AJ_hypotheses`,
  `Manifold/C3FullInputExtSympFromHodgeChainViaStandardForm.lean:61`) is an
  honest *reduction* that still consumes `SmoothSymplecticBasis`,
  `SmoothHurewiczHypothesis`, `CompleteHodgeRiemannHypothesis`, Abel,
  Jacobi-inversion, smoothness, and injectivity all as hypotheses. The
  four named atoms remain the genuine frontier; no vacuous discharge.
- **`Jacobian X = Pic⁰ X` is honest.** Active `PrincDiv X =
  PrincDivHonestCandidate X = AddSubgroup.closure (range
  principalDivisorMap)` (`Divisor/PrincipalDivisorRange.lean:437`), not
  `⊥`. (The `Basic.lean` "principal-divisor subgroup is ⊥" docstring is
  a stale comment — see OPEN.md item 2.)

### What was NOT investigated in this audit

- The exact LOC cost of the route-1 structural rewire (redefining
  `Jacobian X`). The audit puts it at ~1,500+ LOC but didn't trace the
  full consumer cascade in `Basic.lean` items 6/7/8/22.
- Whether Buzzard would accept a typeclass-argument signature change
  on items 5/11/12/13 (would make route 2 rewire viable). This is a
  Buzzard-policy question; not something the repo can answer.

### Confidence and failure modes

- **High confidence**: per-field discharge status (every cell file:line
  verified); in-tree LOC counts (`wc -l`); definition sites; mathlib
  gaps (each grepped); strict-signature constraint on Basic.lean
  instances (read end-to-end).
- **Medium confidence (±50%)**: per-field remaining-LOC estimates. The
  ~57k midpoint has a real ±50% band → 30k–85k. PeriodLattice atoms
  are wider than the Pompeiu calibration (which is one identity), so
  factor-2 uncertainty in either direction is realistic.
- **Paraphrase risk**: PeriodLattice already has `ofFourNamedAtoms`,
  `ofThreeNamedAtoms`, `ofThreeNamedAtomsNoAlpha`, etc. Further
  `*From*Atoms` reductions don't move the frontier. The four atoms ARE
  the frontier; chipping toward them is the only progress.

### Related canonical docs

- [`HANDOFF_ITEM14.md`](HANDOFF_ITEM14.md) — Item 14 canonical (same
  ship-conditional pattern).
- [`OPEN.md`](OPEN.md) — per-item status table; Items 5/11/12/13/17/18/21
  rows point here.
- [`REPO_AUDIT.md`](REPO_AUDIT.md) — full-repo chain-trace per sorry.
