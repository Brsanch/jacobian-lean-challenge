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
     (= `SimplyConnectedSpace StandardS2`, a small mathlib gap on
     π₁(S²) = 0), and (b) `HolomorphicOneFormSubsingletonOfSimplyConnected
     X` (the analytic chain `simply connected ⇒ closed 1-forms have
     primitives via Stokes ⇒ primitive is constant by Liouville ⇒ form
     is zero`). This route bypasses uniformization entirely.

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
~30,000–57,500 LOC.** Phase 1 essentially done (A1 + A2 discharged
2026-05-14; chart-cover lift of the C1 sub-arc remains, blocked on
the ω-level structural caveat). Phase 2 ~15.5–29.6k (period lattice
+ Abel-Jacobi, blocked on classical mathlib gaps), Phase 3 ~7.1–15k
(surface classification, blocked), Phase 4 ~6.9–12.8k (Hodge,
blocked). See `CLOSURE_MAP.md` section F.

**Current repo size:** **85,123 LOC** total in `*.lean` files
(84,728 inside `JacobianChallenge/` across 405 files + 395-line
top-level import manifest). See `CHANGELOG.md` for the per-branch
history.

**Remaining LOC to 24/24** (full breakdown in `CLOSURE_MAP.md` §F):
**~12,000–22,000 LOC** for the realistic **23/24** target (deferring
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

## Architectural issue: RR-thread linear system (resolved on `feat/linear-system-divisor`)

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

**Resolution (`feat/linear-system-divisor` branch).** The germ-field
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

## Smooth-path-connectedness sub-arc (C1 progress, 2026-05-14)

The `AbelJacobiInput α h` named-hypothesis bundle
(`Manifold/AbelJacobiPoint.lean`) is the C1 input of CLOSURE_MAP §F.3.
Its existence on a compact connected complex 1-manifold is classical
("smooth path-connectedness + a chosen base point"). The 2026-05-14
`feat/c1-smooth-path-connected` branch (merged in) lands two
primitives toward the discharge:

1. `SmoothPathConnected I X : Prop` (`Manifold/SmoothPathConnected.lean`)
   — the classical predicate "every two points of `X` joined by a
   smooth path", with `AbelJacobiInput.ofSmoothPathConnected` /
   `nonempty_of_smoothPathConnected` reducing `AbelJacobiInput α h`
   existence to `SmoothPathConnected 𝓘(ℝ, ℂ) X + Nonempty X`. This is
   the named-hypothesis layer for the sub-arc.

2. `SmoothPath.linearInChart` (`Manifold/SmoothPathLinearInChart.lean`)
   — the analytic affine constructor: given a chart `φ ∈ atlas ℂ X`,
   two points in `φ.source`, and the hypothesis that the entire
   chart-coordinate line through their images lies in `φ.target`,
   produce a `SmoothPath 𝓘(ℝ, ℂ) X` between them.

**ω-level structural caveat** documented in
`Manifold/SmoothPathLinearInChart.lean`: the `SmoothPath` structure
demands `ContMDiff ⊤` with `⊤ : WithTop ℕ∞`, which mathlib treats as
`ω` (analytic). Globally analytic functions are germ-determined, so
constant smooth extensions outside `[0, 1]` do not produce an
analytic path. This forces `linearInChart` to require the entire
chart-coordinate *line* (not merely the segment) in `φ.target`. The
hypothesis is unconditional on the affine chart of `RiemannSphere`
(target = ℂ) but generically fails on bounded chart targets.
Closing the "segment-only" case at the ω level needs either a
`SmoothPath`-side refactor (downgrade to `C^∞`) or an
analytic-continuation argument. Either is genuinely a separate chip.

**Remaining for C1 full discharge.** Chart-cover argument lifting
`linearInChart` (line-in-target hypothesis) to
`SmoothPathConnected 𝓘(ℝ, ℂ) X` on a compact connected complex
1-manifold. Estimated 400–1,000 LOC on top of the two primitives
above, modulo the ω-level structural caveat.

## C3 + C4 sub-arc progress (2026-05-14, 5 chips)

`AbelHypothesis B` (Abel forward, `Manifold/AbelJacobiPic0.lean`)
and `JacobiInversion B hAbel` (`Manifold/AbelJacobiIso.lean`) are
the C3 + C4 named hypotheses. Together they give `Pic⁰ X ≃+
AnalyticJacobian X` (`abelJacobiEquiv`) — the gate for items 4, 5,
10, 11, 12, 13.

Five chips landed today reducing the named-hypothesis content of
C3 to a single sharp atomic statement, plus closing C4 at genus 0:

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

**Net open content** after these five chips:

| Input | Open content |
|---|---|
| `AbelHypothesis B` (general genus) | `AbelGeneratorPeriodCondition B` — discharge for each `f : MeromorphicNonzero X` (Abel forward via level-set chain, ~1,000–2,500 LOC of Stokes content) |
| `AbelHypothesis B` (genus 0) | **done** |
| `JacobiInversion B hAbel` (general genus) | Abel converse (injectivity) + Jacobi inversion theorem (surjectivity) |
| `JacobiInversion B hAbel` (genus 0) | `Subsingleton (Pic0 X)` (genus-0 Abel converse, classical Pic⁰(ℙ¹) = 0) |

None of these chips flip items 4, 5, 10, 11, 12, 13 yet — those need
both halves of `Pic⁰ ≃+ AnalyticJacobian` unconditionally at the
relevant `X`. But the structural infrastructure is now in place: the
remaining work is two textbook-citable atomic discharges.

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
