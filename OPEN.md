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

**Current scoreboard:**

- **STRICT-CLOSED:** **12 / 24** — items **2, 3, 6, 7, 8, 9, 15, 19, 20, 22,
  23, 24**. Honest `PrincDiv := PrincDivHonestCandidate` and `Pic0`
  (honest, with manifold instances) live in
  `Divisor/PrincipalDivisorRange.lean`. `Pic0.pushforward (hf)` uses
  `JacobianPushforward.lean`; `Pic0.pullbackWeighted (h_desc)` uses
  `Pic0.divPullbackWeighted_descent_of_smooth` in `JacobianPullback.lean`.
- **STUB (placeholder topology / target / pending discharge):** items
  **1, 4, 10** = 3 items.
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

**Current repo size:** **~98,095 LOC** total in `*.lean` files
(97,625 inside `JacobianChallenge/` across 485 files + 475-line
top-level import manifest). Re-measured 2026-05-16 at main HEAD after
five chips today: `h_AJ_boundary` (+125 LOC), regular β: 0→∞
existence (+431 LOC), concrete regular level-set chain (+146 LOC),
real-model RS manifold + open-set realification (+96 LOC), and
pointwise cotangent pullback primitive (+94 LOC). Cumulative delta
vs. 2026-05-14 snapshot: +70 files / +11,201 LOC. See `CHANGELOG.md`
for the per-branch history.

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
| 1 | `genus X : ℕ` | **STUB** | Body: `JacobianChallenge.genus X = Module.finrank ℂ (HolomorphicOneForm X)`. Returns `0` by convention if `HolomorphicOneForm X` is infinite-dimensional, and finite-dimensionality on compact connected `X` is **not yet proved** (Hodge theory). The anti-hack pair (item 14, `genus_eq_zero_iff_homeo`) is **OPEN**. |
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
| 16 | `ofCurve_inj` (anti-hack vs. `Jacobian := PUnit`) | **OPEN** *(post-ZZ256 regression)* | The previous STUB proof exploited `PrincDiv X = ⊥` to make the quotient faithful. Under honest `PrincDiv` that argument fails; `Jacobian.lean`'s `ofCurve_inj` is now `sorry` (Basic.lean transitively). Genuinely requires Abel–Jacobi (Phase 2). |
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
| 9. Structural reduction `AbelGenerator ← (Z period in lattice) + (Z boundary = -principalDivisor)` | **LANDED 2026-05-15** (`Manifold/MeromorphicNonzeroAbelGeneratorFromLevelSet.lean`, 138 LOC; `abelGeneratorPeriodCondition_of_levelSet_lattice` — cycle Z+AJ has boundary 0, period vector in lattice tautologically; linearity gives AJ's period as lattice element. Named input: `h_struct` (the Z with right boundary AND lattice period). `h_AJ_boundary` (AJ chain's boundary identity) **DISCHARGED 2026-05-16** in `Manifold/PrincipalDivisorAJChainBoundary.lean` (~125 LOC; pure ℤ-linearity + `JacobianChallenge.residue_theorem`) and inlined into the step-9 proof. The β-existence input for the boundary clause of `h_struct` (smooth path 0→∞ avoiding critical values) **DISCHARGED 2026-05-16** in `Manifold/MeromorphicNonzeroRegularPath.lean` (~431 LOC; `exists_regular_path_zero_to_infty` via two `linearInChartSegment` paths through `r := some(s + i)` for generic `s`, concat'd). Concrete witness `regularLevelSetChain f hnc h0 h∞` with its boundary identity (`boundary = -principalDivisorMap f` pointwise) shipped in `Manifold/MeromorphicNonzeroConcreteLevelSetChain.lean` (~146 LOC; `Classical.choose` extraction + composition with step 7d-d). Discharging the lattice clause of `h_struct` is the residual `f_*ω + Stokes` content of full step 9.) | 400–800 |

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

Reaching the next **STRICT-CLOSED** requires landing one of:
(a) honest period lattice → `ChartedSpace` on `Jacobian` (flips items 4,
5, 10, plus 11/12/13 cascade),
(b) Abel-Jacobi (flips item 16),
(c) closed-orientable-surface classification (item 14), or
(d) Hodge L² finite-dimensionality of `HolomorphicOneForm` (item 1).
