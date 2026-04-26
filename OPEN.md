# OPEN

The 24 challenge items in `JacobianChallenge/Basic.lean`, mapped to Buzzard's
spec. **Four** statuses are used so the bar is visible at a glance:

- **OPEN** — `sorry` still present in `Basic.lean`.
- **STUB** — `sorry` replaced by a body that compiles against the verbatim
  signature but **is not the intended mathematics**. Either the formula is
  wrong (`pullback := 0`, `degree := 0/1 indicator`, `TopologicalSpace := ⊥`),
  or the underlying object the lemma is about is itself a stub
  (`Jacobian := Pic⁰` with `PrincDiv := ⊥`).
- **STRICT-CLOSED** — the proof body is honest and would **survive future
  honest replacement** of the upstream placeholders without re-proof. Not yet
  Buzzard-acceptable because the underlying object is still a stub, but the
  proof is real and durable.
- **BUZZARD-ACCEPTED** — the implementation is honest, the underlying object is the
  intended one, and the lemma is what a Buzzard-grade reviewer would accept
  with no further qualification. *Reaching this for any item requires either
  the residue theorem (honest `PrincDiv`) or honest period-lattice
  integration (honest `PeriodLattice` of rank 2g) plus, for items 14, 22, 24,
  additional deep classical inputs.*

**Current scoreboard (audited against `Basic.lean` HEAD `3bdce62`):**

- **STRICT-CLOSED:** 3 / 24 — items 15 (`ofCurve_self`), 19 (`pushforward_id_apply`), 20 (`pushforward_comp_apply`). *This is the headline count — what "strict-closed" means in this repo.*
- **BUZZARD-ACCEPTED:** 0 / 24
- **STUB:** 11 / 24 (items 1, 2, 3, 4, 6, 7, 10, 16, 22, 23, plus item 8 still STUB even though `Pic0.pullback` infra is landed because Basic.lean still routes through the zero stub).
- **OPEN:** 10 / 24 (sorries still in `Basic.lean`).

Do not regenerate this list from context — query this file. Update this file
whenever a status changes.

## Definitions (data) — Basic.lean items 1–9 in OPEN.md numbering

| # | Item | Status | Notes |
|---|---|---|---|
| 1 | `genus X : ℕ` | **STUB** | Body: `JacobianChallenge.genus X = Module.finrank ℂ (HolomorphicOneForm X)`. Returns `0` by convention if `HolomorphicOneForm X` is infinite-dimensional, and finite-dimensionality on compact connected `X` is **not yet proved** (Hodge theory). The anti-hack pair (item 14, `genus_eq_zero_iff_homeo`) is **OPEN**. |
| 2 | `Jacobian X : Type u` | **STUB** | Body: `Jacobian X := Pic0 X` where `Pic0 X = Div0 X ⧸ (PrincDiv X).addSubgroupOf (Div0 X)` and **`PrincDiv X := ⊥`** (placeholder; honest version requires the residue theorem). Mathematically `Jacobian X ≃ Div0 X` here, **not** the analytic Jacobian `ℂ^g / Λ`. |
| 3 | `instance : AddCommGroup (Jacobian X)` | **STUB** | Inherits from the `Pic0` quotient. The group structure is honest; the underlying type is not (item 2). |
| 4 | `instance : TopologicalSpace (Jacobian X)` | **STUB** | Discrete (`⊥`). The challenge wants the complex-manifold topology (item 5 `ChartedSpace`); discrete is not it. |
| 5 | `instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` | **OPEN** | Requires the analytic-Jacobian construction (period-lattice or honest `Pic⁰`); not landable on the current discrete-topology placeholder. The parallel `AnalyticTorus X` carries an honest `ChartedSpace` instance (`Manifold/PeriodLattice.lean`), but is not wired into `Jacobian`. |
| 6 | `Jacobian.ofCurve : X → Jacobian X` | **STUB** | Body: `Q ↦ [δQ − δP]` in `Pic⁰` (honest formula). Lands in stub `Pic⁰`, so the *object* of the map is wrong. |
| 7 | `Jacobian.pushforward f hf` | **STUB** | Body: honest `Pic⁰` pushforward via `Div.singletonMap` + descent. Object is stub `Pic⁰`. |
| 8 | `Jacobian.pullback f hf` | **STUB** | Body: zero `ContinuousAddMonoidHom`. **Wrong implementation** (honest map is the divisor fiber-sum). `Div.fiberSum` (`Divisor/FiberSum.lean`) and `Pic0.pullback (f, hf, N, hN)` (`Divisor/FiberPullback.lean`) are landed; the swap into `Basic.lean` waits on a derivation of finite-fibres + constant-card from `ContMDiff` smoothness alone. |
| 9 | `ContMDiff.degree f hf : ℕ` | **STUB** | Body: `degreeStub f hf` (0 for constant, 1 otherwise). `degreeFiber` infrastructure (with `RegularValueWitness` bundle) merged at `2985cdd` in `Manifold/Degree.lean`; not wired into `Basic.lean` yet because honest fibre-cardinality requires three classical inputs not in mathlib. |

## Theorems (Prop) — Basic.lean items 10–24 in OPEN.md numbering

| # | Item | Status | Notes |
|---|---|---|---|
| 10 | `instance : T2Space (Jacobian X)` | **STUB** | Discrete ⇒ T2 is honest, but the topology itself is wrong (item 4). |
| 11 | `instance : CompactSpace (Jacobian X)` | **OPEN** | Pic⁰ with `PrincDiv = ⊥` is `Div⁰ X`, a free abelian group on the (in general infinite) underlying set of `X`. Not compact in any sensible topology. Requires real period-lattice quotient. |
| 12 | `instance : IsManifold ... ω (Jacobian X)` | **OPEN** | Requires analytic-Jacobian construction. `AnalyticTorus X` has an honest `IsManifold` instance modulo `Λ = ⊥`; not wired into `Jacobian`. |
| 13 | `instance : LieAddGroup ... ω (Jacobian X)` | **OPEN** | Requires item 12 plus smoothness of group ops. |
| 14 | `genus_eq_zero_iff_homeo` (anti-hack vs. `genus := 0`) | **OPEN** | Genus 0 ↔ `X ≃ₜ S²`. Multi-month: requires closed-orientable-surface classification + Riemann sphere as `ChartedSpace` + bridge to geometric genus. |
| 15 | `ofCurve_self : ofCurve P P = 0` | **STRICT-CLOSED** | Real proof reducing to `[δP − δP] = 0` in `Pic⁰`. Lemma is true under any honest `PrincDiv`; proof survives. Not CLOSED only because the *target* object `Jacobian X` is itself a stub. |
| 16 | `ofCurve_inj` (anti-hack vs. `Jacobian := PUnit`) | **STUB** | Currently provable because `PrincDiv = ⊥` makes the quotient faithful — but the proof **uses the placeholder** and will not survive honest `PrincDiv` (under which the Abel–Jacobi theorem becomes load-bearing). Listed STUB rather than STRICT-CLOSED because the proof's correctness is contingent on the stub. |
| 17 | `Jacobian.ofCurve_contMDiff` | **OPEN** | Requires item 5 (`ChartedSpace`) plus a real `ofCurve`. |
| 18 | `Jacobian.pushforward_contMDiff` | **OPEN** | Requires item 5 plus a real `pushforward`. |
| 19 | `pushforward_id_apply` | **STRICT-CLOSED** | Real proof via `Pic0.pushforward_id` ↦ `Div.singletonMap_id_apply`. Functoriality of `singletonMap` is honest and survives any honest `PrincDiv` (modulo a one-line "principal divisor pushforward = principal divisor" check). |
| 20 | `pushforward_comp_apply` | **STRICT-CLOSED** | Real proof via `Pic0.pushforward_comp` ↦ `Div.singletonMap_comp_apply`. Same survives-future-honest argument as 19. |
| 21 | `Jacobian.pullback_contMDiff` | **OPEN** | Requires item 5 plus a real `pullback`. |
| 22 | `pullback_id_apply` | **OPEN** | Genuinely false for the zero-stub `pullback`; remains `sorry`. |
| 23 | `pullback_comp_apply` | **STUB** | Vacuously `0 ∘ 0 = 0`. Not STRICT-CLOSED: the proof crucially depends on `pullback` being the zero stub. |
| 24 | `pushforward_pullback : pushforward f (pullback f P) = degree f • P` | **OPEN** | Headline degree formula; fails for the current zero-pullback stub. |

## Mathlib-prerequisite candidates (likely needed before strict closure)

These are *not* part of the challenge directly, but the constructions for
items 1, 2, 5, 8, 9 will need infrastructure not in mathlib at the pin.

- **Finite-dimensionality of `HolomorphicOneForm X`** on compact connected
  Riemann surface — needed for `genus X` to be the right integer. Hodge
  theory; not yet proved.
- **Honest `PrincDiv X`** — requires the residue theorem on a compact Riemann
  surface (∑_x ord_x f = 0). The other two classical inputs are now landed:
  chart-independence of `mmeromorphicOrderAt` is unconditional in
  `Manifold/MeromorphicAt.lean`, and local finiteness lives in
  `Manifold/MeromorphicDivisor.lean` (`MMeromorphicOn.divisor`). The
  `principalDivisorMap : MeromorphicNonzero X → Div X` is built in
  `Divisor/PrincipalDivisor.lean`; the eventual honest `PrincDiv X` is
  `AddSubgroup.range principalDivisorMap` once the residue-theorem leg
  shows the range lands in `Div⁰`.
- **Honest period lattice** as a rank-`2g` `Submodule ℤ` of `ℂ^g` — requires
  H₁(X; ℤ) for compact Riemann surfaces (not in mathlib at the pin) plus
  period-pairing integration of holomorphic 1-forms over loops.
- **Topological degree of proper holomorphic maps** between Riemann surfaces.
  Three classical inputs gated, named in `Manifold/Degree.lean` as
  `Owed.degree.fibres_finite_statement`,
  `Owed.degree.regular_value_exists_statement`,
  `Owed.degree.fibre_card_well_defined_statement`.
- **`genus_eq_zero_iff_homeo`** — closed-orientable-surface classification
  plus Riemann-sphere `ChartedSpace`. Multi-month.

## Local infrastructure landed (honest, mathlib-PR-shape)

- `Manifold/Cotangent.lean` (~285 LOC) — `CotangentBundle` as dual of `Tangent.lean`, with `ContMDiffVectorBundle` instance.
- `Manifold/HolomorphicOneForm.lean` (~113 LOC) — `HolomorphicOneForm X` and `JacobianChallenge.genus X`.
- `Manifold/MeromorphicAt.lean` (~580 LOC) — `MMeromorphicAt`, `MMeromorphicOn`, `mmeromorphicOrderAt`, **unconditional** chart-independence.
- `Manifold/PathIntegral.lean` (~260 LOC) — `pathIntegralOnInterval` + 4 linearity lemmas.
- `Manifold/RiemannSphere.lean` (~625 LOC) — `OnePoint ℂ` carrier, two-chart atlas, `IsManifold 𝓘(ℂ) ω` instance, `RiemannSphere ≃ₜ S²` homeomorphism.
- `Manifold/PeriodLattice.lean` (~387 LOC) — `AnalyticTorus X := ℂ^g ⧸ ⊥` with full `ChartedSpace` + `IsManifold` instances modulo `Λ = ⊥` placeholder.
- `Manifold/RiemannSphereMobius.lean` (~204 LOC) — `z ↦ −1/z` involution.
- `Manifold/LocalMultiplicity.lean` (~155 LOC) — `degreeStub` (constant indicator).
- `Manifold/Degree.lean` (~247 LOC, 2026-04-26) — `degreeFiber` + `RegularValueWitness` + named owed classical statements.
- `Manifold/MeromorphicDivisor.lean` (~224 LOC, 2026-04-26) — `MMeromorphicOn.orderFun` + `divisor` packaging as `Function.locallyFinsuppWithin`.
- `Divisor/FiberSum.lean` (~361 LOC, 2026-04-26) — `Div.fiberSum f hf` (divisor pullback under finite-fibres) + `fiberSum_id_apply` + `fiberSum_comp_apply` (full contravariant functoriality).
- `Divisor/FiberPullback.lean` (~190 LOC, 2026-04-26) — `Pic0.pullback (f, hf, N, hN)` via `divPullback` descent under constant-fibre-cardinality.
- `Divisor/PrincipalDivisor.lean` (~115 LOC, 2026-04-26) — `MeromorphicNonzero X` + `principalDivisorMap : MeromorphicNonzero X → Div X` (the future honest input to `PrincDiv X`).
- `Topology/SurfaceGenus.lean` (~108 LOC) — `TopologicalGenus = finrank ℚ H₁` + invariance.
- `Divisor.lean` (~225 LOC) — `Div X`, `Div.degree`, `degreeHom`, `Div0`, `Pic0` modulo `PrincDiv := ⊥` placeholder.
- `Divisor/Single.lean` (~150 LOC) — `Div.single`, `degree_single = 1`, `single_sub_single_mem_Div0`.
- `Jacobian.lean` (~470 LOC) — honest `ofCurve`, honest `Pic⁰` pushforward via `Div.singletonMap`, zero-stub pullback.

**Roughly ~4,890 LOC of real local infrastructure**, none of which strict-closes any item by itself.

## Honest scoring (per the four-status bar above)

- **BUZZARD-ACCEPTED**: 0 (Buzzard would not yet accept any item without the upstream
  stubs being made honest first).
- **STRICT-CLOSED**: 3 (items 15, 19, 20 — proof bodies survive future honest
  routing; the bottleneck is the underlying `Jacobian` object).
- **STUB**: 11.
- **OPEN**: 10.

Reaching the first **BUZZARD-ACCEPTED** requires landing one of: the residue theorem
on compact Riemann surfaces, an honest period lattice, the
closed-orientable-surface classification, or honest fibre-cardinality
for proper holomorphic maps.
