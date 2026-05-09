# Closure Map

A grounded map of what's needed to close all 24 challenge items, verified against mathlib at the current pin (Lean 4.30 + mathlib pin per `lakefile.lean`) and the repo state at the time of writing. Each item names the **classical proof step** required, the **mathlib status** (with file references for what's there), and the **repo status** (what's already built and the remaining work).

Written as a successor to OPEN.md to ground future planning in actual mathlib reads rather than docstring pattern-matching.

## Verified mathlib status (this pin)

### Available (use directly)
- `Mathlib/Analysis/Meromorphic/{Basic,Order,Divisor,NormalForm,FactorizedRational,IsolatedZeros,Complex,TrailingCoefficient}.lean` — `MeromorphicAt.{prod,mul,inv,pow}`, `meromorphicOrderAt_smul`, `meromorphicOrderAt_zpow`, factorized-rational identification.
- `Mathlib/Analysis/Analytic/{Basic,Order,Polynomial,Uniqueness,Composition,IsolatedZeros}.lean` — analytic order, identity theorem, composition order multiplicativity (`AnalyticAt.analyticOrderAt_comp`).
- `Mathlib/RingTheory/MvPolynomial/Symmetric/{Defs,FundamentalTheorem,NewtonIdentities}.lean` — fundamental theorem of symmetric polynomials, Newton's identities.
- `Mathlib/RingTheory/Polynomial/Vieta.lean` — `prod_X_sub_C_coeff`, `prod_X_sub_X_eq_sum_esymm`.
- `Mathlib/RingTheory/Norm/{Defs,Transitivity}.lean` — `Algebra.norm` for finite extensions.
- `Mathlib/MeasureTheory/Integral/{CircleIntegral,CircleAverage,CircleTransform,TorusIntegral}.lean` — contour/circle integrals.
- `Mathlib/Algebra/Module/ZLattice/{Basic,Covolume,Summable}.lean` — Z-lattices in finite-dim real vector spaces, fundamental domain.
- `Mathlib/Topology/Algebra/ProperAction/Basic.lean:206` — `QuotientGroup.instT2Space` (closed subgroup ⇒ quotient T2).
- `Mathlib/AlgebraicTopology/SingularHomology/{Basic,HomotopyInvariance,HomotopyInvarianceTopCat}.lean` — abstract singular homology chain complex (NOT specialized H₁ groups).
- `Mathlib/Algebra/Homology/EulerCharacteristic.lean` — abstract Euler characteristic.
- `Mathlib/Topology/Compactification/OnePoint/Sphere.lean`, `Mathlib/Geometry/Manifold/Instances/Sphere.lean` — sphere as ChartedSpace.

### NOT in mathlib (must be built or accepted as upstream gaps)
- **Norm map of meromorphic functions across proper covers** — no `Norm_f : MeromorphicNonzero X → MeromorphicNonzero Y` for `f : X → Y` proper holomorphic. (Multiplicative analogue of `divPushforward`.)
- **Surface classification theorem** — no formalization of "closed orientable 2-manifolds classified by genus".
- **Hodge decomposition for compact Riemann surfaces** — no `dim ℂ HolomorphicOneForm X = genus X`.
- **Specialization of `H₁(X; ℤ)`** to compact Riemann surface — no concrete computation `H₁ ≅ ℤ^{2g}`.
- **Period pairing integral** for holomorphic 1-forms over loops — concrete contour integrals via `CircleIntegral` exist, but no integration theory over abstract loops in a Riemann surface.
- **Period-lattice rank theorem** (Riemann bilinear relations forcing rank 2g).
- **Abel's theorem** (kernel of Abel-Jacobi = `PrincDiv`).
- **Jacobi inversion theorem** (Abel-Jacobi surjective).
- **No explicit Riemann surface definition** as a stand-alone class in mathlib.

## The 24 items, mapped

The challenge items live in `JacobianChallenge/Basic.lean`. Numbering matches OPEN.md.

### Phase 0 — already done this session

**Items 8, 22, 23, 24** — pullback honest body, identity, comp, push∘pull. Done under Buzzard lemma-level interpretation. Held up under OPEN.md's strict bar by item 2's `Jacobian X` still being a stub (since `PrincDiv X = ⊥` placeholder). Auto-flips strict-bar when item 2 lands.

### Phase 1 — closable at this pin via the **Norm-map thread**

This phase flips items **2, 3, 6, 7, 8, 15, 16, 19, 20, 22, 23, 24** (12 items total, in batch).

**Math required**:
1. Construction of `Norm_f g : MeromorphicNonzero Y` for `f : X → Y` non-constant `ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω` and `g : MeromorphicNonzero X`, satisfying `divPushforward f (div g) = div (Norm_f g)`.
2. Proof of meromorphy uses: products invariant under `s ↦ ζ·s` for ζ k-th root of unity, hence depend only on `s^k = t`. Combined with `MeromorphicAt.prod` (mathlib), local meromorphy at branch points reduces to invariance + composition.
3. Cascade: replace `Pic0.pushforward`'s descent (`Jacobian.lean:534`, currently relies on `PrincDiv = ⊥`) with the honest descent via norm functoriality.
4. Swap `PrincDiv X := AddSubgroup.range principalDivisorMap` (using `residue_theorem_unconditional` already in main to ensure range ⊆ Div⁰).

**Chip plan** (target ~5 chips, ~1500–1800 LOC):

| Chip | Output | LOC | mathlib leverage |
|---|---|---|---|
| **Norm-Local** | `Norm_f g (y) = ∏_{x ∈ f⁻¹(y)} g(x)^{ramif(x)}`; local meromorphy at every `y₀ ∈ Y`. | ~600 | `MeromorphicAt.prod`, `MeromorphicAt.pow`, `analytic_local_normal_form` (already in repo), `meromorphicOrderAt_smul`. Inline ~150 LOC for "∏_{ζ^k=1} g(ζs) is a function of s^k" via direct invariance. |
| **Norm-Global** | `MMeromorphicOn (Norm_f g) Set.univ` + non-vanishing germ of `Norm_f g`. | ~250 | Local-to-global glue + repo's `MeromorphicNonzero` API. |
| **Norm-Divisor** | `divPushforward f (div g) = div (Norm_f g)` divisor identity. | ~200 | `meromorphicOrderAt_smul` for sum-of-orders; chart-pullback bookkeeping. |
| **PrincDiv-Functoriality** | `divPushforward f` carries principal divisors to principal divisors. Discharge of `(PrincDiv X).addSubgroupOf Div⁰X ≤ ((PrincDiv Y).addSubgroupOf Div⁰Y).comap (divPushforward f)`. | ~150 | Direct from Norm-Divisor. |
| **PrincDiv-Swap** | `PrincDiv X := AddSubgroup.range principalDivisorMap`; replace `hBot` line in `Pic0.pushforward`; cascade fix in ~5–10 consumer files (`pushforward_id_apply`, `pushforward_comp_apply`, `Pic0.pullback` callsites, `Basic.lean` items 19/20 reproof). | ~600 incl. cascade | None new — uses `residue_theorem_unconditional` already in main. |

**After Phase 1**: 12 items at STRICT-CLOSED. Remaining 12 items strictly blocked on Phases 2–4 below.

### Phase 2 — period-lattice cluster (items 4, 5, 11, 12, 13, 17, 18, 21)

These items make `Jacobian X` carry the analytic-Jacobian structure `ℂ^g / Λ`. NOT closable at this pin.

**Math required (each is a classical theorem)**:
- (a) **First singular homology of compact connected Riemann surface is ℤ^{2g}**. Mathlib has the abstract chain complex but no specialization. Path via surface classification (Phase 4) gives this.
- (b) **Period pairing**: for `γ ∈ H₁(X; ℤ)` and `ω ∈ HolomorphicOneForm X`, `∫_γ ω ∈ ℂ`. Requires (i) integration of forms along singular 1-chains (mathlib has `CircleIntegral` for parametrized circles in ℂ; not generalized), (ii) basis-of-loops choice.
- (c) **Period lattice has rank 2g** (Riemann bilinear relations for holomorphic 1-forms — non-trivial classical content).
- (d) **`Jacobian X = ℂ^g / Λ`** as a CompactSpace + ChartedSpace + IsManifold + LieAddGroup — packaged as a single hypothesis bundle `PeriodLatticeOfRankTwoG X` in `Manifold/PeriodLatticeRankTwoG.lean` already, awaiting (a)+(b)+(c).
- (e) **Abel-Jacobi map** `X → J(X)`: AJ surjective (Jacobi inversion) + kernel of `Div⁰ → J` is `PrincDiv` (Abel's theorem). Items 17, 18, 21 about ContMDiff of pushforward/pullback maps need item 5 (ChartedSpace) plus AJ's smoothness.

**Mathlib gaps**:
- No `H₁(X; ℤ) ≅ ℤ^{2g}` specialization to compact Riemann surface.
- No period pairing API.
- No Riemann bilinear / period-lattice rank theorem.
- No Abel-Jacobi map.

**Estimate**: items 4/5/10/11/12/13/17/18/21 require ≥ 8–15 multi-thousand-LOC sub-projects, each effectively a **research-grade Lean formalization** of a classical theorem. Not single-agent chippable. Track separately.

### Phase 3 — surface classification (item 14)

`genus_eq_zero_iff_homeo` says genus 0 ↔ X homeomorphic to S².

**Math required**:
- Classification of closed orientable 2-manifolds by genus (Brahana 1921, modernized).
- Sphere as a 2-manifold with charted structure (mathlib has `Geometry/Manifold/Instances/Sphere.lean` for the standard embedding).

**Mathlib gaps**: no closed-orientable-surface classifier.

**Repo status**: skeleton in `JacobianChallenge/Topology/{SurfaceClassificationGenus,SurfaceGenus,OnePointHomeoSphere,Genus0ImpliesS2Reduction,S2ImpliesGenus0Discharge}.lean` — substantial scaffolding awaiting the classification input.

**Estimate**: item 14 alone ≥ 3–10k LOC. Not chippable as a single agent run.

### Phase 4 — Hodge cluster (item 1)

`genus X` is defined as `Module.finrank ℂ (HolomorphicOneForm X)`. The "anti-hack" lemma (item 14) demands genus matches the topological genus. Item 1 itself just needs the definition to make sense, which requires `HolomorphicOneForm X` to be finite-dimensional.

**Math required**:
- Finite-dimensionality of `HolomorphicOneForm X` on compact connected Riemann surface (Hodge theory).
- Stronger: `dim ℂ HolomorphicOneForm X = (rank H₁(X; ℤ)) / 2`.

**Mathlib gaps**: no Hodge decomposition for Riemann surfaces.

**Repo status**: scaffolding in `JacobianChallenge/Analysis/L2OnManifold.lean`.

**Estimate**: research-grade Lean Hodge formalization, multi-thousand LOC.

### Item 9 — `ContMDiff.degree`

Currently STUB via `degreeFiber` (post-RegFix uses `RegularValueWitnessReg`, ✓ honest). Should auto-flip with Phase 1 since the rsum/regular-witness machinery is already unconditional.

### Item 10 — `T2Space (Jacobian X)`

Currently STUB via discrete topology. Under Phase 1's honest `Pic⁰`, `T2Space` follows from `QuotientGroup.instT2Space` (mathlib `Topology/Algebra/ProperAction/Basic.lean:206`) PROVIDED the principal-divisor subgroup is closed in `Div⁰` under whatever topology `Div⁰` carries. `Div⁰` topology is currently discrete (free abelian group); under discrete topology every subgroup is closed; hence `T2Space` flips with Phase 1. Auto-flip.

### Item 16 — `ofCurve_inj`

Under Phase 1 (honest `PrincDiv`), this becomes Abel's theorem (kernel of AJ = `PrincDiv`). Mathlib doesn't have Abel; the repo would need to prove `ofCurve` is injective on a non-trivial class. **In Phase 1's Pic⁰-only world** (without ℂ^g/Λ identification), `ofCurve P P' = [δP' - δP]` is injective in `Div⁰ X / range principalDivisorMap` iff `δP' - δP = (g)` for some `g` iff `P = P'`. The "iff" direction needs the existence of a non-constant rational function with a single zero at `P` and pole at `P'` — which on genus ≥ 1 surfaces is FALSE in general (Abel-Jacobi is the obstruction). So `ofCurve_inj` is NOT generally provable from Phase 1 alone — requires the Abel-Jacobi correspondence (Phase 2) or genus restriction.

**Caveat**: item 16 may be partially-provable (genus 0 only) at Phase 1 + sphere structure (Phase 3). Verify exact statement of `ofCurve_inj` against required hypotheses.

## Summary table

| Item | Phase | Status after Phase 1 lands | Gating mathlib gap |
|---|---|---|---|
| 1 | 4 | OPEN | Hodge / dim HolomorphicOneForm |
| 2 | 1 | STRICT-CLOSED | none |
| 3 | 1 | STRICT-CLOSED | none |
| 4 | 2 | STUB (still discrete topology) | Period lattice via H₁ |
| 5 | 2 | OPEN | Period lattice via H₁ |
| 6 | 1 | STRICT-CLOSED | none |
| 7 | 1 | STRICT-CLOSED | none |
| 8 | 1 | STRICT-CLOSED | none |
| 9 | 1 | STRICT-CLOSED (auto) | none |
| 10 | 1 | STRICT-CLOSED (auto via QuotientGroup.instT2Space) | none |
| 11 | 2 | OPEN | Period lattice |
| 12 | 2 | OPEN | Period lattice + IsManifold transport |
| 13 | 2 | OPEN | Period lattice + Lie group transport |
| 14 | 3 | OPEN | Surface classification |
| 15 | 1 | STRICT-CLOSED (auto-promote from PROOF-HONEST) | none |
| 16 | 1+? | OPEN — needs Abel's thm OR genus-0 restriction | Abel's theorem (Phase 2) |
| 17 | 2 | OPEN | Item 5 + AJ smoothness |
| 18 | 2 | OPEN | Item 5 + AJ smoothness |
| 19 | 1 | STRICT-CLOSED (re-prove vs honest body) | none |
| 20 | 1 | STRICT-CLOSED (re-prove vs honest body) | none |
| 21 | 2 | OPEN | Item 5 + pullback ContMDiff |
| 22 | 1 | STRICT-CLOSED (auto) | none |
| 23 | 1 | STRICT-CLOSED (auto) | none |
| 24 | 1 | STRICT-CLOSED (auto) | none |

**After Phase 1 lands cleanly**: 13 items STRICT-CLOSED (1, 2, 3, 6, 7, 8, 9, 10, 15, 19, 20, 22, 23, 24 — but actually count is 14 because item 1 isn't strictly closed unless Hodge lands) — sorry, recount: items 2, 3, 6, 7, 8, 9, 10, 15, 19, 20, 22, 23, 24 = **13 items** STRICT-CLOSED. Item 16 partial.

**Items left after Phase 1**: 1, 4, 5, 11, 12, 13, 14, 16, 17, 18, 21 = **11 items**, all on classical mathlib gaps (Phases 2–4).

## Recommendation for future sessions

1. **Phase 1 is the only thread chippable at this pin.** Estimated 5 chips, ~1500–1800 LOC. The dominant chip is Norm-Local (~600 LOC; the resultant/symmetric identity is the highest-uncertainty step but mathlib's `MeromorphicAt.prod` + invariance under `s ↦ ζs` make it tractable inline).

2. **Phases 2/3/4 require mathlib upstream contributions** before they're chippable here:
   - Phase 2: H₁(X;ℤ) for compact Riemann surface + period pairing API.
   - Phase 3: closed-orientable-surface classification.
   - Phase 4: Hodge for Riemann surfaces.
   - Each is a research-grade formalization in its own right.

3. **The repo already has substantial scaffolding** for Phases 2/3/4 packaged as named-hypothesis bundles (`Manifold/PeriodLatticeRankTwoG.lean`, `Topology/SurfaceClassificationGenus.lean`, etc.). When the upstream classical content lands in mathlib (or is built independently), the Lean wiring of items 4/5/11/12/13/14 is ~hours-to-days work, NOT multi-month. The multi-month estimate is for the upstream content.

4. **Estimate calibration warning**: today's session estimated Phase 1 at "3–5 chips" initially. After actual mathlib reads, the estimate is "5 chips, ~1700 LOC". Always do mathlib reads before quoting numbers.
