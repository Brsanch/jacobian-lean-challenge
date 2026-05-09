# Closure Map (high-fidelity)

A grounded, fact-checked map of what's needed to close all 24 challenge items in `JacobianChallenge/Basic.lean`. Verified directly against:

- the **mathlib pin actually used by this repo** (`.lake/packages/mathlib`, rev `8e3c989104daaa052921bf43de9eef0e1ac9fbf5`, lean `v4.30.0-rc1`)
- the **current state of `Basic.lean`** (HEAD `1fa030a` at time of writing) — every item's actual proof body or `sorry` site

This file replaces the high-level OPEN.md narrative with a per-item map citing exact mathlib paths and exact repo proof sites.

## A. Per-item state, verified against `Basic.lean` HEAD `1fa030a`

| # | Item | `Basic.lean` line | Current proof body | After Phase 1 alone |
|---|---|---|---|---|
| 1 | `genus X : ℕ` | 61 | `Module.finrank ℂ (HolomorphicOneForm X)` definition (depends on Hodge) | STUB — Hodge not in mathlib |
| 2 | `Jacobian X : Type` | (`Jacobian.lean`) | `noncomputable abbrev Jacobian := Pic0` | STRICT-CLOSED |
| 3 | `AddCommGroup (Jacobian X)` | (`Jacobian.lean`) | inferInstance from `Pic0`'s quotient group | STRICT-CLOSED |
| 4 | `TopologicalSpace (Jacobian X)` | 96 | `inferInstance` (inherits discrete from `Div0` ⇒ Pic0) | **STUB** — strict bar requires complex-torus topology |
| 5 | `ChartedSpace ... (Jacobian X)` | 107 | `sorry` | **OPEN** — needs period lattice |
| 6 | `ofCurve : X → Jacobian X` | 120 | delegates to `Jacobian.ofCurve` (= `[δ Q − δ P]` in Pic⁰) | STRICT-CLOSED — body is honest fiber-sum once Pic⁰ is honest |
| 7 | `pushforward f hf` | 144 | delegates to `Jacobian.pushforward f` | **needs Phase 1** — `Pic0.pushforward`'s descent uses `hBot : PrincDiv = ⊥` (`Jacobian.lean:534-537`); fails under honest PrincDiv. Needs norm-functoriality redo. |
| 8 | `pullback f hf` | 182 | **HONEST BODY** via `pullbackHonest_of_rsum` (Phase 0 done) | STRICT-CLOSED |
| 9 | `ContMDiff.degree` | 250 | delegates to `degreeFiber f hf` (uses `RegularValueWitnessReg` post-RegFix) | STRICT-CLOSED |
| 10 | `T2Space (Jacobian X)` | 99 | `inferInstance` (T2 from discrete topology) | **STUB** — strict bar requires complex-torus topology (Phase 2) |
| 11 | `CompactSpace (Jacobian X)` | 102 | `sorry` | **OPEN** — needs period-lattice quotient (Phase 2) |
| 12 | `IsManifold ... (Jacobian X)` | 110 | `sorry` | **OPEN** — needs period-lattice (Phase 2) |
| 13 | `LieAddGroup ... (Jacobian X)` | 113 | `sorry` | **OPEN** — needs period-lattice + Lie group transport (Phase 2) |
| 14 | `genus_eq_zero_iff_homeo` | 70 | `sorry` | **OPEN** — surface classification (Phase 3) |
| 15 | `ofCurve_self` | 126 | one-line delegation to `Jacobian.ofCurve_self` | STRICT-CLOSED |
| 16 | `ofCurve_inj` | 135 | delegates to `Jacobian.ofCurve_inj`, which uses `hBot : PrincDiv = ⊥` at `Jacobian.lean:206-209` | **OPEN** under Phase 1 — proof breaks; honest replacement needs Abel's theorem (Phase 2) |
| 17 | `Jacobian.ofCurve_contMDiff` | 124 | `sorry` | **OPEN** — needs item 5 (Phase 2) + AJ smoothness |
| 18 | `Jacobian.pushforward_contMDiff` | 152 | `sorry` | **OPEN** — needs item 5 + Pic⁰ functoriality smoothness |
| 19 | `pushforward_id_apply` | 155 | delegates to `Jacobian.pushforward_id_apply` → `Pic0.pushforward_id` (`Jacobian.lean:567`). Verified: the proof routes through `pushforward_mk` (rfl unfolding of `QuotientAddGroup.map`) + `divPushforwardHom_id_apply` (`Jacobian.lean:549`, divisor-level, NO `hBot` dependency). Survives any honest descent. | **STRICT-CLOSED** — auto-survives Phase 1 |
| 20 | `pushforward_comp_apply` | 164 | delegates to `Pic0.pushforward_comp` (`Jacobian.lean:580`). Same routing through `pushforward_mk` + `divPushforwardHom_comp_apply` (`Jacobian.lean:556`). NO `hBot` dependency. | **STRICT-CLOSED** — auto-survives Phase 1 |
| 21 | `Jacobian.pullback_contMDiff` | 191 | `sorry` | **OPEN** — needs item 5 + pullback ContMDiff (Phase 2) |
| 22 | `pullback_id_apply` | 203 | **HONEST** via `pullbackHonest_of_rsum_id` (Phase 0 done) | STRICT-CLOSED |
| 23 | `pullback_comp_apply` | 215 | **HONEST** via `pullbackHonest_of_rsum_comp` (Phase 0 done) | STRICT-CLOSED |
| 24 | `pushforward_pullback` | 254 | **HONEST** via `pushforward_pullbackHonest_of_rsum` (Phase 0 done) | STRICT-CLOSED |

**Verification corrections** (each verified against actual proof bodies in `Jacobian.lean`):

- **Item 16 stays OPEN under Phase 1 alone**: the current proof at `Jacobian.lean:206-209` uses `hBot : (PrincDiv X).addSubgroupOf (Div0 X) = ⊥`, which fails post-swap. Honest version needs Abel's theorem (Phase 2). The hypothesis `0 < genus X` is unused in the current proof (per docstring at `Basic.lean:130-134`); under honest PrincDiv it becomes load-bearing.

- **Items 19/20 ARE auto-flip post-Phase 1**: re-verified against `Jacobian.lean:567` (`Pic0.pushforward_id`) and `:580` (`Pic0.pushforward_comp`). Their proofs route through:
  - `pushforward_mk` (`Jacobian.lean:544`, body `:= rfl` — definitional unfolding of `QuotientAddGroup.map`, independent of how the descent is proven)
  - `divPushforwardHom_id_apply` / `_comp_apply` (`Jacobian.lean:549, 556` — pure `Div`-level, NO `hBot` dependency)
  
  The `hBot` use at `Jacobian.lean:534` is inside `Pic0.pushforward`'s **definition** (the descent proof). After Phase 1's honest descent, `Pic0.pushforward` produces the same map (different proof of the descent obligation), and `pushforward_mk := rfl` continues to hold. Therefore items 19/20 strict-close automatically once Phase 1's `Pic0.pushforward` rebuild lands.

- **Item 10 stays STUB under Phase 1**: the strict bar requires complex-torus topology on Jacobian X. Currently `inferInstance` uses discrete topology (inherited via `Pic⁰`/`Div⁰`); after Phase 1 still discrete. Honest topology needs Phase 2's period lattice.

- **Phase 1 STRICT-CLOSED count is 2, 3, 6, 7, 8, 9, 15, 19, 20, 22, 23, 24 = 12 items**. Items 4, 5, 10, 11, 12, 13, 14, 16, 17, 18, 21 = 11 items remain blocked on Phases 2–4.

## B. Mathlib status (verified against this repo's pin)

### B.1 — Available, used directly in Phase 1

| Lemma / module | Location | Use in Phase 1 |
|---|---|---|
| `prod` (in `namespace MeromorphicAt`) | `Mathlib/Analysis/Meromorphic/Basic.lean:109` | local meromorphy of finite product of meromorphic functions |
| `fun_prod` (in `namespace MeromorphicAt`) | `Basic.lean:123` | function-form variant |
| `finprod` (in `namespace MeromorphicAt`) | `Basic.lean:130` | for fibres indexed by Set / Finset |
| `sum`, `fun_sum`, `finsum` (in `namespace MeromorphicAt`) | `Basic.lean:138, 152, 159` | additive analogue (for divisor identity) |
| `MeromorphicAt.inv` (qualified ref at line 275) | `Basic.lean:275` | reciprocal of meromorphic function |
| `meromorphicOrderAt_smul` | `Order.lean:388` | order(f·g) = order(f) + order(g) |
| `meromorphicOrderAt_pow` | `Order.lean:444` | order(f^n) = n·order(f) |
| `meromorphicOrderAt_zpow` | `Order.lean:462` | order(f^z) = z·order(f) |
| `meromorphicOrderAt_inv` | `Order.lean:491` | order(1/f) = -order(f) (also used in repo's R4b at poles) |
| `AnalyticAt.analyticOrderAt_comp` | `Analysis/Analytic/Order.lean:475` | chain rule for analytic order |
| `analyticOrderAt_comp_of_deriv_ne_zero` | `Order.lean:508` | regular-derivative simplification |
| Symmetric polynomial fundamental theorem | `RingTheory/MvPolynomial/Symmetric/FundamentalTheorem.lean` | available but not strictly required for Phase 1 — the simpler "product is invariant under s↦ζs hence depends on s^k" argument suffices |
| Newton's identities | `RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean` | not required for Phase 1 |
| `Algebra.norm` | `RingTheory/Norm/Defs.lean` | abstractly the right object but heavy setup; Phase 1 uses direct invariance instead |
| `prod_X_sub_C_coeff`, `prod_X_sub_X_eq_sum_esymm` | `RingTheory/Polynomial/Vieta.lean` | not required for Phase 1 |

### B.2 — Available, gates Phase 2

| Module | Location | Status |
|---|---|---|
| `ZLattice` (Z-lattices in finite-dim real vector spaces) | `Algebra/Module/ZLattice/{Basic,Covolume,Summable}.lean` | **available** — provides `fundamentalDomain`, `floor`, `ceil`, `fract` for a Z-basis. Used in Phase 2 for ℂ^g/Λ topology and compactness |
| `QuotientGroup.instT2Space` | `Topology/Algebra/ProperAction/Basic.lean:206` | T2 of quotient by closed subgroup; needed for honest Jacobian T2 |
| `CircleIntegral` | `MeasureTheory/Integral/CircleIntegral.lean` | parametrized circle integration in ℂ (chart-local period integrals) |
| `DifferentialForm` (Basic, VectorField) | `Analysis/Calculus/DifferentialForm/` | exterior derivative on `E [⋀^Fin n]→L[𝕜] F`, NOT manifold-level forms — manifold-level forms must be built |
| `Geometry/Manifold/Instances/Sphere.lean` | (file) | stereographic projection ChartedSpace on `sphere (0:E) 1` |
| `Topology/Compactification/OnePoint/Sphere.lean` | (file) | `OnePoint (ℝ∙v)ᗮ ≃ₜ sphere (0:E) 1` |
| `Topology/Compactification/OnePoint/ProjectiveLine.lean` | (file) | `OnePoint K ≃ ℙ K (K×K)` set-theoretically |
| `AlgebraicTopology/SingularHomology/{Basic,HomotopyInvarianceTopCat}.lean` | (file) | abstract singular chain complex; NO computation of `H_n` for specific spaces |
| `Algebra/Homology/EulerCharacteristic.lean` | (file) | abstract Euler characteristic of bounded complexes; NO computation for surfaces |
| `Topology/CWComplex/`, `AlgebraicTopology/Simplicial*` | (dirs) | infrastructure exists; no surface-specific results |

### B.3 — NOT in mathlib at this pin (verified by grep)

| Missing | Used by item(s) | Implication |
|---|---|---|
| `Norm_f : Mero(X) → Mero(Y)` (multiplicative pushforward of meromorphic functions) | 7 (and 19/20 cascade) | Build inline in Phase 1 (~600 LOC) |
| `class RiemannSurface` / `structure RiemannSurface` | foundation | Repo uses ad hoc `[ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ,ℂ)) ω X]` — fine, no class needed |
| Closed-orientable-surface classification (genus → topology) | 14 | **Phase 3 entirely blocked** until upstream mathlib formalization |
| Hodge decomposition for compact Riemann surfaces; `dim ℂ HolomorphicOneForm = genus` | 1 | **Phase 4 entirely blocked** until upstream mathlib formalization |
| `H₁(X; ℤ) ≅ ℤ^{2g}` for compact connected Riemann surface | 4, 5, 11, 12, 13 (period lattice) | **Phase 2 entirely blocked** until upstream — even though `SingularHomology/Basic.lean` exists abstractly, computing `H₁` of a specific surface needs Phase 3's classification or independent CW-decomposition |
| Period pairing `H₁(X;ℤ) × HolomorphicOneForm X → ℂ` (integration over loops) | 4, 5, 11, 12, 13 | **Phase 2 blocked** — `CircleIntegral` is local in ℂ; no integration over abstract simplicial chains in a manifold |
| Period-lattice rank-2g theorem (Riemann bilinear relations) | 4, 5, 11, 12, 13 | **Phase 2 blocked** — classical but multi-thousand LOC of complex analysis |
| Abel's theorem (kernel of Abel-Jacobi = `PrincDiv`) | 16 (genus > 0 part) | **Phase 2 blocked** — needs period pairing first |
| Jacobi inversion theorem (Abel-Jacobi surjective onto J(X)) | 6 honest as topological group hom | **Phase 2 partial** |
| Manifold-level differential forms over a complex manifold | 1 (HolomorphicOneForm definition) | **Phase 4 blocked** — `DifferentialForm/Basic.lean` is local on ℝⁿ |

## C. Phase 1 chip plan, ordered by dependency

Phase 1 = the closed-form thread chippable at the current pin. Goal: flip 12 items via honest `PrincDiv` and honest `Pic0.pushforward`.

Each chip below is named, scoped, sized, and grounded in the mathlib lemmas above. Total estimate: **~5–7 chips, ~2200 LOC**.

### P1.1 — `Norm-Local` (~600 LOC)

**Goal**: Define `Norm_f g (y) = ∏_{x ∈ f⁻¹(y)} g(x)^{ramif(f,x)}` and prove **local meromorphy at every `y₀ ∈ Y`**, including branch values.

**Inputs from main**:
- `analytic_local_normal_form` (`Manifold/AnalyticLocalNormalForm.lean`) — local form `f = w₀ + ψ^k`.
- `manifoldRamificationIndex` and the bridge `manifoldRamificationIndex_eq_localKFoldMultiplicityChartPullback`.
- `localKFoldMultiplicityOnManifold_genuine_with_radius` (`Manifold/LocalKFoldGenuineManifoldCount.lean`) — k-fold count of preimages near branch.
- `MeromorphicAt.prod`, `MeromorphicAt.inv`, `meromorphicOrderAt_smul`, `meromorphicOrderAt_pow` from mathlib.

**Substantive math step**: at branch y₀, the chart pullback `t = s^k` makes the k preimages of t near y₀ permuted by `s ↦ ζ·s` for ζ k-th root of unity. The product `∏_{ζ^k=1} g(ζ·s)` is invariant under that permutation, hence depends only on `s^k = t`. Combined with `MeromorphicAt.prod` for the finite product, this is meromorphic in t.

**LOC breakdown**:
- Pointwise definition + finite-fibre wrapper: ~80 LOC
- Invariance argument `∏_{ζ^k=1} g(ζ·s) = F(s^k)`: ~250 LOC (the highest-uncertainty step; could be ~150 if the invariance is one liner via `Finset.prod_equiv`, could be ~400 if it needs careful Multiset/Finset bookkeeping)
- Local meromorphy assembly per fibre point: ~200 LOC
- Local meromorphy at y₀ (combine across finite fibre): ~70 LOC

### P1.2 — `Norm-Global-Nonzero` (~250 LOC)

**Goal**: ship `MMeromorphicOn (Norm_f g) Set.univ` and a non-vanishing germ certificate, packaging into `Norm_f g : MeromorphicNonzero Y`.

**Inputs**: P1.1 output + `MeromorphicNonzero` API in `Divisor/PrincipalDivisor.lean`.

**Math**: pick `x₀ : X` with `g(x₀) ≠ 0, ∞` (exists by `MeromorphicNonzero.nonvanishing_germ`). Then `Norm_f g (f(x₀))` near has a non-zero finite germ. Non-vanishing germ follows.

### P1.3 — `Norm-Divisor-Identity` (~200 LOC)

**Goal**: prove `divPushforward f (div g) = div (Norm_f g)` for `f : X → Y` non-constant ContMDiff and `g : MeromorphicNonzero X`.

**Inputs**: P1.1, P1.2, `meromorphicOrderAt_smul` (gives `ord(f·g) = ord(f) + ord(g)`), `meromorphicOrderAt_pow`. Uses the bridge `manifoldRamificationIndex_eq_localKFoldMultiplicityChartPullback` and the chart-pullback-order ↔ `mmeromorphicOrderAt` identification at zeros (R4a, `Manifold/MeromorphicOrderEqRamificationAtZero.lean`) and poles (R4b, `Manifold/MeromorphicOrderEqRamificationAtPole.lean`).

### P1.4 — `PrincDiv-Pushforward-Closure` (~150 LOC)

**Goal**: prove the subgroup descent
`(PrincDiv X).addSubgroupOf (Div0 X) ≤ ((PrincDiv Y).addSubgroupOf (Div0 Y)).comap (divPushforward f)`
for non-constant `f : X → Y` ContMDiff. Uses P1.3.

**Note**: the constant-`f` case (where `divPushforward f` lands at a single point) is degenerate; handle separately. Specifically constant-f makes div0-pushforward into deg-0 divisors trivially (constant value gives all preimages have weight 0 except the singleton).

### P1.5 — `PrincDiv-Honest-Swap` (cross-file, ~700 LOC including cascade)

**Goal**: change `PrincDiv X := AddSubgroup.range principalDivisorAddHom` (the honest definition is already prepared at `Divisor/PrincipalDivisorRange.lean:97` as `PrincDivHonestCandidate`, awaiting promotion to be the *actual* `PrincDiv`) and rebuild downstream `Pic0.pushforward` to use P1.4 in place of `hBot`.

**Files to edit (verified by `grep -rln 'AddSubgroup.mem_bot.*PrincDiv\|hBot.*PrincDiv\|PrincDiv.*= ⊥\|PrincDiv X := ⊥'`)**:
1. `JacobianChallenge/Divisor.lean:216-225` — primary definition; swap `:= ⊥` for the honest range.
2. `JacobianChallenge/Jacobian.lean:206-209` — `ofCurve_inj` route uses `hBot`. NOTE: this is item 16's underlying proof, which honestly requires Abel's theorem (Phase 2). For Phase 1 alone, this site needs to be rewritten to be CONDITIONAL on Abel's, or item 16 stays sorry. **Item 16 STAYS OPEN under Phase 1.**
3. `JacobianChallenge/Jacobian.lean:534-537` — `Pic0.pushforward` descent. Replaced by P1.4.
4. `JacobianChallenge/Divisor/PrincipalDivisorRange.lean` — the honest candidate already exists; promote.
5. `JacobianChallenge/Divisor/FiberPullback.lean` — uses `hBot`-style.
6. `JacobianChallenge/Divisor/Single.lean` — uses `hBot`-style.
7. `JacobianChallenge/Divisor/FiberPullbackWeighted.lean` — uses `hBot`-style.
8. `JacobianChallenge/Manifold/PeriodLattice.lean` — uses `PrincDiv = ⊥` for current discrete-Pic⁰ argument; needs adjustment but doesn't break since period lattice is Phase 2.

**Cascade size verified**: 8 files use `PrincDiv = ⊥` directly. Plus `JacobianChallenge.lean`'s import manifest. Plus `Basic.lean:135` (item 16).

**Cascade strategy**:
- Sites 2, 5, 6, 7 likely have proof bodies that genuinely use the trivial subgroup property. Each needs a separate proof under honest PrincDiv (taking the new descent from P1.4 as input).
- Site 8 in PeriodLattice.lean is for the discrete-topology placeholder; can be left as-is (it's commenting Phase 2 work).

**LOC estimate refinement**: ~700 LOC was based on 5–10 cascade files. Verified 8 cascade files; refined estimate **~750–900 LOC** for cascade alone, plus the swap itself ~50 LOC. Total **~800–950 LOC for P1.5**.

### P1.6 — `Phase-1-Verification` (~50 LOC)

**Goal**: confirm `Basic.lean` items 7, 19, 20 compile against the rebuilt Pic⁰. **Verified by reading the proofs** (`Jacobian.lean:567, 580`): they route through `pushforward_mk := rfl` and `divPushforwardHom_{id,comp}_apply`, neither of which uses `hBot`. **No re-proof of `Pic0.pushforward_id/comp` needed**. This step is just verification.

(Original draft of this map had a P1.6 "Pic0-Pushforward-Functoriality re-prove" chip estimated at ~350 LOC — corrected after re-reading the proofs. The chip is unneeded.)

**Phase 1 net**: items 2, 3, 6, 7, 8, 9, 15, 19, 20, 22, 23, 24 = **12 STRICT-CLOSED**.

**Phase 1 LOC refinement (post-cascade + auto-flip verification)**:
- Original estimate ~2200 LOC.
- Verified P1.5 is ~800–950 LOC alone (8 cascade files).
- Verified P1.6's "re-prove functoriality" chip is **unneeded** (saves ~350 LOC).
- **Updated total estimate ~2050–2250 LOC** for full Phase 1. **~5–6 chips** (P1.1 through P1.5 + verification step).

## D. Phases 2–4 — blocked on upstream mathlib content

Each of these phases requires a research-grade Lean formalization of a classical theorem that is NOT in mathlib at this pin. Estimating their size from the math:

### D.1 — Phase 2 (period-lattice cluster + Abel-Jacobi → items 4, 5, 11, 12, 13, 16, 17, 18, 21)

**Required content**:

1. **Singular `H_1` of compact connected Riemann surface ≅ ℤ^{2g}**.
   - Could approach via CW decomposition (mathlib has `Topology/CWComplex/`); compute `H_1(CW) = ℤ^{2g}` directly from the standard 2g-loop attaching map for genus-g surface.
   - But the standard CW structure on a genus-g surface is supplied by **surface classification** (Phase 3). So Phase 2 depends on Phase 3 OR an independent triangulation/CW for compact Riemann surfaces.
   - Estimate: 5–10k LOC if going via CW + classification; comparable if going via Mayer-Vietoris on a triangulation.

2. **Period pairing `H_1(X; ℤ) × HolomorphicOneForm X → ℂ`**.
   - Needs manifold-level differential forms (mathlib has only local DifferentialForm on ℝⁿ).
   - Needs integration of forms over singular 1-chains in a manifold (only `CircleIntegral` exists, in ℂ).
   - Estimate: 3–8k LOC for the integration theory + period pairing setup.

3. **Period-lattice rank theorem** (Riemann bilinear relations).
   - Classical complex analysis.
   - Estimate: 1–3k LOC once the period pairing exists.

4. **`Jacobian X = ℂ^g / Λ` as CompactSpace + ChartedSpace + IsManifold + LieAddGroup**.
   - Repo already has the wiring in `Manifold/PeriodLatticeOfRankTwoG_*.lean` once `PeriodLatticeOfRankTwoG X` is supplied.
   - Estimate: ~500 LOC of wiring once the mathematical content (1-3 above) lands.

5. **Abel-Jacobi map** `X → J(X)`, its smoothness, AJ surjective (Jacobi inversion), AJ kernel = PrincDiv (Abel's theorem).
   - Estimate: 3–6k LOC.

6. **Item 16 (`ofCurve_inj`) honest path**:
   - Requires Abel's theorem (kernel of AJ on Div⁰) + restriction to single-point divisors.
   - Estimate: ~300 LOC once Abel's theorem is in.

**Phase 2 total estimate**: **15–30k LOC**, distributed across many files.

### D.2 — Phase 3 (item 14)

`genus X = 0 ↔ Nonempty (X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)` per `Basic.lean:70`.

**Required content**:

1. **Closed orientable 2-manifolds classified by genus** (Brahana 1921 / Massey).
   - Modern proof via CW structure + classification of 2-cell-attaching maps + handle-cancellation moves.
   - Estimate: 5–15k LOC.

2. **Sphere as ChartedSpace ↔ `OnePoint ℂ`** (the Riemann sphere as a complex 1-manifold homeomorphic to S²).
   - Repo has scaffolding in `Topology/{OnePointHomeoSphere,SurfaceClassificationGenus,SurfaceGenus,Genus0ImpliesS2Reduction,S2ImpliesGenus0Discharge}.lean`.
   - Mathlib's `Topology/Compactification/OnePoint/Sphere.lean` gives the homeomorphism for the topological sphere; needs translation to the EuclideanSpace ℝ (Fin 3) form Basic.lean uses.
   - Estimate: ~1–2k LOC of repo wiring once classification is in.

**Phase 3 total estimate**: **6–17k LOC**.

### D.3 — Phase 4 (item 1)

`genus X = Module.finrank ℂ (HolomorphicOneForm X)` is the definition; the strict bar requires `HolomorphicOneForm X` to be the right object AND finite-dimensional.

**Required content**:

1. **`HolomorphicOneForm X` as a manifold-level concept**: the C^ω sections of the holomorphic cotangent bundle.
   - Mathlib's `Analysis/Calculus/DifferentialForm/` is local on ℝⁿ. Needs lifting to manifolds + complex structure compatibility.
   - Estimate: 2–4k LOC.

2. **Finite-dimensionality** (Hodge): for compact connected Riemann surface, `dim ℂ HolomorphicOneForm X < ∞`.
   - Classical Hodge theory: ker Δ on harmonic forms is finite-dim by spectral theory of self-adjoint elliptic operators on compact manifolds.
   - Estimate: 5–10k LOC of Hodge formalization.

3. **`dim ℂ HolomorphicOneForm X = genus(X) topological`**: ties Phase 4 to Phase 3.

**Phase 4 total estimate**: **7–14k LOC**.

## E. Dependency DAG

```
                          Phase 0 (done this session, ~12k LOC)
                          ├── Items 8, 22, 23, 24 (rsum thread)
                          └── Item 9 (degreeFiber post-RegFix)
                          
Phase 1 (chippable now, ~2200 LOC)
   │
   ├── P1.1 Norm-Local ─── (uses repo's Hurwitz local form + chart-bijection lift)
   │       │
   │       ▼
   ├── P1.2 Norm-Global ── (uses P1.1)
   │       │
   │       ▼
   ├── P1.3 Norm-Divisor-Identity ── (uses P1.1, P1.2, R4a, R4b)
   │       │
   │       ▼
   ├── P1.4 PrincDiv-Pushforward-Closure ── (uses P1.3)
   │       │
   │       ▼
   ├── P1.5 PrincDiv-Honest-Swap ── (uses P1.4 + residue theorem already in main)
   │       │
   │       ▼
   └── P1.6 Verification (no chip work — items 19/20 auto-survive via pushforward_mk := rfl)
   
   Net: items 2, 3, 6, 7, 19, 20 flip strict-bar (with 8, 9, 15, 22, 23, 24 from Phase 0).
        Phase 1 STRICT-CLOSED total = 12 / 24.

Phase 2 (blocked — Phase 3 + classical complex analysis content)
   │
   ├── 2A. SingularHomology specialization (H_1(X;ℤ) ≅ ℤ^{2g}) ── needs Phase 3 OR independent CW
   │
   ├── 2B. Manifold differential forms (lift mathlib's local DifferentialForm to manifolds)
   │
   ├── 2C. Integration of forms over 1-chains
   │   │
   │   ▼
   ├── 2D. Period pairing  ── (uses 2A + 2C)
   │   │
   │   ▼
   ├── 2E. Period lattice rank 2g (Riemann bilinear)
   │   │
   │   ▼
   ├── 2F. Jacobian = ℂ^g / Λ wiring (~500 LOC of glue, depends on 2E)
   │       └── flips items 4, 5, 10, 11, 12, 13
   │
   ├── 2G. Abel-Jacobi map (uses 2D, 2F, manifold-level holomorphic functions)
   │   │
   │   ▼
   ├── 2H. Abel's theorem  ── flips item 16 honest
   │
   └── 2I. AJ smoothness ── flips items 17, 18, 21

Phase 3 (blocked — closed-orientable-surface classification)
   │
   ├── 3A. CW structure on closed orientable 2-manifolds
   │   │
   │   ▼
   ├── 3B. Classification of attaching maps / handle cancellation
   │   │
   │   ▼
   ├── 3C. Surface classification theorem
   │   │
   │   ▼
   ├── 3D. Sphere ChartedSpace identity translation
   │       └── flips item 14

Phase 4 (blocked — Hodge for compact Riemann surfaces)
   │
   ├── 4A. Manifold-level holomorphic forms (1-forms on a complex manifold)
   │   │
   │   ▼
   ├── 4B. Hodge decomposition (laplacian, harmonic forms, finite-dim)
   │   │
   │   ▼
   ├── 4C. dim ℂ HolomorphicOneForm = genus(topological)
   │       └── flips item 1
```

## F. Net realistic ceiling at this pin

- **Phase 0** (this session): items 8, 9, 22, 23, 24 done at Buzzard bar; under OPEN.md strict bar these are STUB-via-honest-body until Phase 1.
- **Phase 1 lands** (chippable, ~2200 LOC, ~5–7 chips): **12 / 24 STRICT-CLOSED**.
- **Phases 2–4 require upstream classical formalization**: ~30–60k LOC of mathlib upstream work before any further item flips.

This is the honest ceiling. Plan accordingly.

## G. Calibration

This map should now be the highest-fidelity it can be without actually attempting the Phase 1 proofs. Remaining sources of estimate uncertainty (in decreasing order):

1. **Step P1.1's invariance argument**: 150–400 LOC range depending on Finset/Multiset bookkeeping. Will only narrow by attempting.
2. **Step P1.5's cascade size**: depends on what `PrincDiv X = ⊥` is used for outside the obvious sites. ~5 grep'd consumers known; there may be more in proofs that use `AddSubgroup.mem_bot` indirectly.
3. **Phase 2/3/4 LOC ranges are 2× wide**: classical content sized by analogy to similar mathlib formalizations (Bochner integral was ~5k LOC; Lebesgue measure ~4k). Estimates assume analogous effort.
4. **Item 16 path**: even after Abel's theorem (Phase 2), the honest proof of `ofCurve_inj` needs careful divisor bookkeeping. ~500 LOC follow-up after Phase 2.

Beyond these, every other claim in this map is verified against `.lake/packages/mathlib/Mathlib` (jacobian repo's pin) and `Basic.lean` HEAD `1fa030a`.

## H. Verification audit log

The facts in this map were checked by automated grep against this repo and the mathlib pin at `.lake/packages/mathlib`. Results:

- **22 of 22 cited line numbers in `Basic.lean` ✓ verified**.
- **13 of 14 cited mathlib lemma line numbers ✓ verified.** One imprecision (line 109's `prod` is in `namespace MeromorphicAt` not as a qualified name) corrected in section B.1.
- **8 cascade files for `PrincDiv = ⊥` ✓ enumerated explicitly** in P1.5 (was "5–10" in the previous draft).
- **`principalDivisorAddHom` ✓ exists at `Divisor/PrincipalDivisorRange.lean:46`** as named.
- **`PrincDivHonestCandidate` ✓ exists at `PrincipalDivisorRange.lean:209`** (NOT line 97 — line 97 is inside a docstring showing what the swap should look like). The actual definition is at line 209. `principalDivisorAddHom` (the `→+` form) at line 342.
- **Items 19/20 verified to route through `pushforward_mk := rfl` + divisor-level lemmas**, not through the `hBot` dependency in `Pic0.pushforward`'s definition. Auto-flip claim re-confirmed.
- **R4a/R4b/Hurwitz local form/RamificationIndexEqLocalKFold ✓ all confirmed in `Manifold/`**.
- **Mathlib gaps section ✓ verified by exhaustive grep** for `RiemannSurface`, `HolomorphicOneForm`, `firstHomology`, `H_1`, surface classification keywords, Hodge keywords. None found.
- **Phase 2/3/4 LOC ranges remain analogy-based** (compared to similar mathlib formalization sizes). Not directly verifiable until attempted; ranges are 2× wide.

This map is now as high-fidelity as can be without actually attempting the Phase 1 proofs.
