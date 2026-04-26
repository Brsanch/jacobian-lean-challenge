# OPEN

The 24 challenge items in `JacobianChallenge/Basic.lean`, mapped to Buzzard's
spec. Three statuses are used:

- **OPEN** — the `sorry` is still in `Basic.lean`.
- **STUB** — the `sorry` has been replaced with a typechecking placeholder that
  satisfies the literal signature but **not** the intended mathematical
  content. Any item marked **STUB** also has its anti-hack pair (or a
  downstream identity) named so a strict reader can see what is being faked.
- **CLOSED** — the implementation is honest and survives the anti-hack lemmas
  / downstream identities. Reserved for items that a Buzzard-grade reviewer
  would actually accept.

At present **no item is CLOSED**. Items 1, 2, 3, 4, 5, 9, 12, 13, 15 are
**STUB**; the remaining items are **OPEN**. See the docstrings in
`JacobianChallenge/Jacobian.lean` and `JacobianChallenge/Manifold/LocalMultiplicity.lean`
for the explicit stub caveats.

Do not regenerate this list from context — query this file.

## Definitions (data)

| # | Item | Status | Notes |
|---|---|---|---|
| 1 | `genus X : ℕ` | **STUB** | Body filled with `JacobianChallenge.genus X = Module.finrank ℂ (HolomorphicOneForm X)`. The `Module.finrank` convention returns `0` on infinite-dim, and finite-dimensionality of `HolomorphicOneForm X` for compact connected `X` is **not yet proved** (see "Mathlib-prerequisite candidates" below). The anti-hack pair (item 14, `genus_eq_zero_iff_homeo`) is still **OPEN** — placed by Buzzard precisely to rule out hacks like `genus := 0`. The stub is *plausibly* the right value on compact `X`, but not certified. |
| 2 | `Jacobian X : Type u` | **STUB** | Body filled with `Jacobian X := Pic0 X` where `Pic0 X = Div0 X ⧸ (PrincDiv X).addSubgroupOf (Div0 X)` and **`PrincDiv X := ⊥`** (placeholder; see Divisor.lean docstring). Mathematically `Jacobian X ≃ Div0 X`, **not** the analytic Jacobian. Anti-hack pair (item 16, `ofCurve_inj`) is still **OPEN**. With the stub, `ofCurve_inj` is *false* when `genus > 0`. |
| 3 | `instance : AddCommGroup (Jacobian X)` | **STUB** | Inherits from the `Pic0` quotient. The group structure exists honestly; the underlying type does not (item 2). |
| 4 | `instance : TopologicalSpace (Jacobian X)` | **STUB** | We give it the **discrete** topology. The challenge wants the complex-manifold topology (item 7 `ChartedSpace`); discrete is not it. |
| 5 | `instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` | **OPEN** | Charts inherited from `ℂᵍ`. Requires the analytic Jacobian construction (period lattice or honest `Pic⁰`); not landable on the current placeholder topology. |
| 6 | `Jacobian.ofCurve : X → Jacobian X` | **STUB** | Body filled with `ofCurve P := constant zero`. Honest map is `Q ↦ [Q] - [P]`; needs single-point divisor constructor + one-point degree lemma in Divisor.lean. Anti-hack pair (item 16) is **OPEN** and the stub fails it. |
| 7 | `Jacobian.pushforward f hf` | **STUB** | Body filled with the zero `ContinuousAddMonoidHom`. Honest map is the functorial pushforward on `Pic⁰`; not landable without item 6's honest version. The functoriality lemmas (items 17, 19, 20, 22, 24) are all **OPEN** and the zero stub fails them. |
| 8 | `Jacobian.pullback f hf` | **STUB** | Body filled with the zero `ContinuousAddMonoidHom`. Same caveats as item 7. |
| 9 | `ContMDiff.degree f hf : ℕ` | **STUB** | Body filled with the constant-vs-non-constant indicator: `0` if constant, `1` otherwise. Honest definition is the regular-value fiber cardinality; needs chart-independence of `mmeromorphicOrderAt` (currently owed by `MeromorphicAt.lean`). Anti-hack downstream (item 24, `pushforward_pullback`) is **OPEN** and pins the numerical value of `degree`; stub fails it for any non-constant map of true degree ≥ 2. |

## Theorems (Prop)

| # | Item | Status | Notes |
|---|---|---|---|
| 10 | `instance : T2Space (Jacobian X)` | **STUB** | Discrete ⇒ T2; consistent with item 4's discrete-topology stub but not honest in the analytic-Jacobian sense. |
| 11 | `instance : CompactSpace (Jacobian X)` | **OPEN** | Pic⁰ with the placeholder `PrincDiv = ⊥` is *not* compact (it's a free abelian group on the support of `X`). The compactness instance requires a real period-lattice quotient. |
| 12 | `instance : IsManifold (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X)` | **OPEN** | Requires the analytic Jacobian construction. |
| 13 | `instance : LieAddGroup ... (Jacobian X)` | **OPEN** | Requires item 12. |
| 14 | `genus_eq_zero_iff_homeo` (anti-hack vs. `genus := 0`) | **OPEN** | Genus 0 ↔ `X ≃ₜ S²`. Multi-month mathlib gap (closed-orientable-surface classification + Riemann sphere as `ChartedSpace`). |
| 15 | `ofCurve_self : ofCurve P P = 0` | **STUB** | Trivially `rfl` because `ofCurve P` is the constant-zero stub from item 6. The lemma is correct *as stated*, but `ofCurve` itself is not. |
| 16 | `ofCurve_inj` (anti-hack vs. `Jacobian := PUnit`) | **OPEN** | `ofCurve P` injective when `0 < genus X`. **False for the current item-6 stub**; remains `sorry` and is the strict-reader's check that item 6 is not honest. |
| 17 | `Jacobian.ofCurve_contMDiff` | **OPEN** | Requires item 5 (`ChartedSpace`) plus a real `ofCurve`. |
| 18 | `Jacobian.pushforward_contMDiff` | **OPEN** | Requires item 5 plus a real `pushforward`. |
| 19 | `pushforward_id_apply` | **OPEN** | Functoriality (identity). Fails for the zero stub of item 7. |
| 20 | `pushforward_comp_apply` | **OPEN** | Functoriality (composition). Vacuously true for the zero stub but deliberately not shipped. |
| 21 | `Jacobian.pullback_contMDiff` | **OPEN** | Requires item 5 plus a real `pullback`. |
| 22 | `pullback_id_apply` | **OPEN** | Symmetric to item 19. |
| 23 | `pullback_comp_apply` | **OPEN** | Symmetric to item 20. |
| 24 | `pushforward_pullback : pushforward f (pullback f P) = degree f • P` | **OPEN** | The headline degree formula and the strict-reader's check that items 7, 8, 9 are honest. Fails for the current stubs. |

## Mathlib-prerequisite candidates (likely needed before items above)

These are *not* part of the challenge directly, but the constructions for
items 1, 2, 5, 6, 7, 8, 9 will need infrastructure not in mathlib at the
pinned commit. Each is plausibly a standalone mathlib PR.

- `HolomorphicOneForm` as a complex vector space — done locally in
  `JacobianChallenge/Manifold/HolomorphicOneForm.lean` (~113 LOC) on top of
  the local `CotangentBundle` (`JacobianChallenge/Manifold/Cotangent.lean`,
  ~217 LOC, mathlib-PR-shape — dual of `Mathlib.Geometry.Manifold.VectorBundle.Tangent`).
  This part is *real* code, not a stub.
- `MeromorphicAt` on a complex manifold — *partial* local at
  `JacobianChallenge/Manifold/MeromorphicAt.lean` (~377 LOC). Has
  `MMeromorphicAt`, `MMeromorphicOn`, `mmeromorphicOrderAt`,
  `add/mul/neg/sub/zero/const`, `mono/union`, **conditional chart-independence**
  via `MMeromorphicAt.iff_of_chart` and `mmeromorphicOrderAt_eq_of_chart`
  (parametrized by an explicit `AnalyticAt` + `deriv ≠ 0` hypothesis).
  **Owed:** the *automatic* discharge of analyticity from `[IsManifold I ω M]`
  (the `OpenPartialHomeomorph` ↔ analytic-groupoid bridge), plus
  `inv/pow/zpow/const_smul/div` and `MMeromorphicOn.divisor` →
  `Function.locallyFinsuppWithin`. The conditional pieces are *real*; the
  automatic discharge is owed.
- Finite-dimensionality of `HolomorphicOneForm X` on compact connected
  Riemann surface — needed for `genus X` to be the right integer (without it,
  `Module.finrank` returns 0 by convention on infinite-dim). **Not yet
  proved.**
- `Divisor` infrastructure — *partial* local at `JacobianChallenge/Divisor.lean`
  (~225 LOC). Has `Div X` (abbrev for `Function.locallyFinsuppWithin (Set.univ) ℤ`),
  `supportFinset`, `degree`, `degree_zero`, `degree_add`, `degreeHom`, `Div0`,
  `PrincDiv := ⊥` (placeholder), `Pic0`, `Pic0.instAddCommGroup`. **Owed:**
  the honest `principalDivisor` and the proof that it lands in `Div0`
  (residue theorem on a compact Riemann surface). Real code modulo the
  `PrincDiv` placeholder.
- `principalDivisor` and the residue-theorem identity (compact Riemann
  surface ⇒ ∑ ord_x f = 0) — multi-PR work, not in scope.
- The period lattice as a `Submodule ℤ` of the dual of `HolomorphicOneForm`
  — needed for the `(Fin g → ℂ) ⧸ PeriodLattice` construction of `Jacobian X`.
- Topological degree of proper holomorphic maps between Riemann surfaces
  (currently mathlib only has degree for `S^n → S^n`). The pinned scoping
  agent recommended a *generic-fiber cardinality* construction off
  `mmeromorphicOrderAt`-on-manifold; that route requires the chart-
  independence above.
- `genus_eq_zero_iff_homeo` (challenge item 14) requires the topological
  classification of compact connected orientable surfaces — multi-month
  mathlib gap. Not in scope.

Track each prereq as it is identified, and prefer landing it as a mathlib PR
rather than carrying a private copy; the PR review process is the validation
mechanism this repo otherwise lacks.

## Honest scoring

- Real, mathlib-PR-shape infrastructure that would survive an adversarial
  review: `Cotangent.lean` (~217), `HolomorphicOneForm.lean` (~113),
  `MeromorphicAt.lean` conditional chart-independence (~377),
  `Divisor.lean` modulo the `PrincDiv` placeholder (~225). Roughly **~930
  LOC of real content**.
- Type-skeleton stubs that compile but are not honest implementations:
  `Jacobian.lean` (~218), `LocalMultiplicity.lean` (~155). Roughly
  **~373 LOC of stubs**.
- Items literally `:= sorry`-free in `Basic.lean`: 9 (items 1, 2, 3, 4, 6,
  7, 8, 9, 10, 15). Items honestly closed in Buzzard's strict sense:
  **0**.
