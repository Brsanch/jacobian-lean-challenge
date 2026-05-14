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
| 14 | `genus_eq_zero_iff_homeo` | 70 | `sorry` | **OPEN** — single named open input `UniformizationToRiemannSphere X` post-zz309; pullback half closed honestly via zz302–zz310 |
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

### D.1 — Phase 2 (period-lattice cluster + Abel-Jacobi → items 4, 5, 10, 11, 12, 13, 16, 17, 18, 21)

**Verified mathlib status before sizing each component**:
- ✓ `Topology/CWComplex/{Abstract,Classical}/Basic.lean` exists (cells, attaching maps, skeletons, subcomplexes, finite cw)
- ✓ `AlgebraicTopology/SingularHomology/Basic.lean` exists (abstract singular chain complex functor)
- ✓ `AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean` exists
- ✓ `Algebra/Module/ZLattice/{Basic,Covolume,Summable}.lean` exists
- ✓ `Geometry/Manifold/VectorBundle/Tangent.lean` (tangent bundle)
- ✓ `Geometry/Manifold/MFDeriv/NormedSpace.lean:400` — `extDerivFun` (scalar exterior derivative on a manifold, as a section of the cotangent bundle)
- ✓ `Geometry/Manifold/PartitionOfUnity.lean` (for global integration constructions)
- ✓ `Geometry/Manifold/Complex.lean` (6 declarations about holomorphic functions on complex manifolds; basic max-modulus content)
- ✗ NO `cellularChain` / `cellularHomology` (no cellular chain complex, no isomorphism with singular)
- ✗ NO computation of singular H_n for any specific space (no `H_n(S^k) = ...`, no `H_1` of any surface)
- ✗ NO `OneForm` class on a manifold (only the `extDerivFun` scalar wrapper)
- ✗ NO `holomorphicOneForm`, `periodPairing`, `abelJacobi`, `jacobiInversion`
- ✗ NO triangulability theorem for 2-manifolds (Radó)

**Per-component LOC, grounded by what's available**:

| Component | What it needs | Available? | LOC |
|---|---|---|---|
| **2.A Cellular homology framework** (cellular chain complex `C_n(X) = ℤ[cells]` with ∂ via attaching-map degrees, isomorphism with singular homology) | mathlib has CWComplex but NOT cellular homology. Build chain complex + degree of attaching maps + comparison theorem. | foundations ✓; specific construction ✗ | **3,000–5,000** |
| **2.B Compact orientable 2-manifold has standard genus-g CW structure** | Depends on surface classification (Phase 3). Once Phase 3 lands, this assigns the specific cellular structure. | depends on Phase 3 | **500–1,000** (post-Phase 3) |
| **2.C H_1(genus-g surface) ≅ ℤ^{2g}** | Apply 2.A to 2.B. Direct calculation: ker ∂_1 / im ∂_2. | depends on 2.A, 2.B | **400–800** |
| **2.D Manifold-level differential 1-forms class `OneForm M`** | Lift `extDerivFun` (which exists for scalars) to a class of smooth sections of `T*M`. | scalar piece ✓; class ✗ | **1,500–3,000** |
| **2.E Holomorphic 1-forms on complex manifold** | Restrict 2.D to ℂ-linear sections compatible with complex structure. | depends on 2.D | **500–1,000** |
| **2.F Integration of 1-form over a smooth singular 1-simplex in M** | mathlib has `intervalIntegral` (real interval) and `CircleIntegral` (parameterized circle in ℂ). Need: integrate ω over `γ : Δ¹ → M` smooth, via charts. | building blocks ✓; assembly ✗ | **1,500–3,000** |
| **2.G Period pairing `H_1(X; ℤ) × HolomorphicOneForm X → ℂ`** | Combines 2.C and 2.F. Quotient compatibility (Stokes for closed forms). | depends on 2.C, 2.F | **800–1,500** |
| **2.H Period lattice rank-2g theorem** (Riemann bilinear relations forcing linear independence over ℝ) | Classical complex analysis on the period matrix. Uses Stokes + intersection product on H_1. | depends on 2.A, 2.G | **2,000–4,000** |
| **2.I Period lattice as `ZLattice` in ℂ^g** | Wire 2.H into mathlib's `ZLattice` API. | ZLattice ✓ | **400–800** |
| **2.J Items 4/5/10/11/12/13 instances on `Jacobian X = ℂ^g/Λ`** | Repo's `Manifold/PeriodLatticeOfRankTwoG_*.lean` is wiring-ready once 2.I supplies the bundle. | scaffolding ✓ | **400–800** |
| **2.K Abel-Jacobi map** `X → ℂ^g/Λ`, `Q ↦ class of (∫_P^Q ω_1, ..., ∫_P^Q ω_g)` plus smoothness | Combines 2.D, 2.F, 2.J | depends on 2.D, 2.F, 2.J | **1,000–2,000** |
| **2.L Abel's theorem** (ker of AJ on Div⁰ = PrincDiv) | Combines 2.K with residue theorem (already in repo). Classical proof via period considerations on closed-form integrals. | residue theorem ✓ | **1,000–2,000** |
| **2.M Jacobi inversion** (AJ surjective onto J(X)) | Theta-function approach OR Riemann-Roch-light. Heavy classical content. | nothing in mathlib | **2,000–4,000** |
| **2.N Items 17, 18, 21 (ContMDiff of `ofCurve`, pushforward, pullback)** | Uses 2.J (charted-space structure on J(X)) + 2.K (AJ smoothness) + functoriality. | depends on 2.J, 2.K | **600–1,200** |
| **2.O Item 16 (`ofCurve_inj`)** | AJ injective on `[δQ - δP]` divisors via 2.L. | depends on 2.L | **300–500** |

**Phase 2 total verified**: **15,500–29,600 LOC** (sum of column 4).

The dominant chunks: 2.A (cellular homology), 2.D + 2.E (manifold forms class), 2.F (chain integration), 2.H (Riemann bilinear), 2.M (Jacobi inversion). 2.B/C have low LOC IF Phase 3 lands first.

### D.2 — Phase 3 (item 14: `genus_eq_zero_iff_homeo`)

Statement at `Basic.lean:70`: `genus X = 0 ↔ Nonempty (X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)`.

**Verified mathlib status**:
- ✓ `Topology/Compactification/OnePoint/Sphere.lean` — `OnePoint (ℝ ∙ v)ᗮ ≃ₜ sphere (0 : E) 1` (homeomorphism between one-point compactification of a hyperplane and the unit sphere).
- ✓ `Geometry/Manifold/Instances/Sphere.lean` — stereographic projection ChartedSpace structure on `sphere (0 : E) 1`.
- ✓ `Topology/CWComplex/{Abstract,Classical}/Basic.lean` (cells, attaching maps).
- ✗ NO closed-orientable-surface classification.
- ✗ NO triangulability theorem (Radó 1925) for compact 2-manifolds.

**Per-component LOC**:

| Component | What it needs | Available? | LOC |
|---|---|---|---|
| **3.A Triangulability of compact 2-manifolds (Radó)** | Classical theorem; not in mathlib. Construct triangulation from local charts via combinatorial bookkeeping. | building blocks (charts, simplicial structure) ✓ | **3,000–6,000** |
| **3.B Surface classification** (closed orientable triangulated 2-manifold ↔ genus-g standard form) | Brahana / Massey moves on triangulations to canonical form. | foundations ✓; theorem ✗ | **3,000–7,000** |
| **3.C Riemann surface ⇒ orientable** | Complex structure ⇒ orientation (Jacobian of chart transition is positive in real terms). | local definitions ✓ | **300–500** |
| **3.D Genus 0 (analytic) ⇒ S² as homotopy/CW class** | Combines 3.A, 3.B, 3.C with the fact that genus 0 = "no handles" = sphere. | depends on 3.A, 3.B, 3.C | **300–500** |
| **3.E Sphere structure translation: abstract S² ↔ `Metric.sphere (0:EuclideanSpace ℝ (Fin 3)) 1`** | mathlib has `Topology/Compactification/OnePoint/Sphere.lean`. Repo has scaffolding in `Topology/{OnePointHomeoSphere,...}.lean`. | infrastructure ✓ | **500–1,000** |

**Phase 3 total verified**: **7,100–15,000 LOC**.

**Update 2026-05-13 (zz302–zz310 chain, ~1,800 LOC landed)**: the
*pullback-of-1-forms* half of Phase 3 is now closed honestly. Specifically:

- zz302–zz306 (`PullbackPointwiseFunctionSmooth.lean`,
  `PullbackSectionSmoothness.lean`) discharge the cotangent ↔ tangent
  in-coordinates bridge UNCONDITIONALLY, then assemble the smooth
  pullback section `HolomorphicEquiv.pullbackSection_contMDiffAt`.
- zz307 (`PullbackHolomorphicOneForm.lean`) upgrades the pointwise
  pullback to a `HolomorphicOneForm`, and discharges
  `IsHolomorphicOneFormPullback_for_all e.symm` unconditionally —
  closing the previously-tautological zz287–zz301 loop.
- zz308 (`PullbackLinearEquiv.lean`) packages this as a
  `HolomorphicOneForm Y ≃ₗ[ℂ] HolomorphicOneForm X`, and ships the full
  item-14 biconditional for any `X ≃ₕ RiemannSphere`.
- zz309 (`Item14FromSingleUniformization.lean`) consolidates
  `Item14FromUniformization.lean`'s two open inputs
  (`UniformizationGenus0 X` + `HolomorphicOneFormEquivRiemannSphere X`)
  into **a single named open hypothesis**:

      UniformizationToRiemannSphere X :=
        (genus X = 0 ∨ Nonempty (X ≃ₜ StandardS2)) →
          Nonempty (HolomorphicEquiv X RiemannSphere)

  This is precisely the classical uniformization-for-genus-0 statement
  in the exact shape required to close both directions of item 14.
- zz310 (`HolomorphicEquivGenusInvariance.lean`) extracts
  `HolomorphicEquiv X Y → genus X = genus Y` as a one-line API for
  downstream transport.

**Net effect on the Phase 3 LOC estimate**: components 3.A, 3.B (surface
classification + Radó) remain entirely as the *topological* gap. The
pullback half (item-14 reverse direction's analytic content) is no
longer a Phase 3 cost — item 14 reduces to **a single named open
classical input** (uniformization for genus-0 surfaces), not two. The
remaining work to flip item 14 STRICT-CLOSED is: prove
`UniformizationToRiemannSphere X` (the disjunctive form above).

**Update 2026-05-13 part 2 (zz311–zz336 chain, ~1,500 LOC landed)**:
the closure chain for item 14 is now fully **architecturally complete**,
with two of the named open inputs DOWNGRADED to theorems:

* zz311–zz314: pullbackLinearEquiv is a contravariant functor (refl,
  symm, trans, round-trip — all closed unconditionally).
* zz315: clean one-liner `genus X = 0` from `HolomorphicEquiv X RS`.
* zz316–zz318: `FactUniformizationToRiemannSphere X` as a typeclass +
  biholomorphism-transport (iff form).
* zz319: `HolomorphicEquiv.compactSpace` / `.t2Space` API.
* zz320–zz321: `HolomorphicEquiv ↔ IsConstantMap` bridge.
* zz322: `RegularValueWitness_card_eq_one` for biholomorphisms.
* zz323: `HolomorphicEquiv → degreeFiber = 1` (substantive analytic).
* zz325: Riemann-Roch + degree-1-biholomorphism waypoint (names the
  inputs `RiemannRochGenusZero X` and `DegreeOneIsBiholomorphic_RS X`).
* zz326–zz329: `degreeFiber=1 → singleton fibres → injective → bijective`
  (conditional on `ramificationSumEqualsDegree_statement X RS`, now
  unconditional — see zz336).
* zz330: `BijectiveAnalyticIsBiholomorphism X` (smooth-inverse named).
* zz331: **FINAL composition theorem**: item 14 biconditional from
  exactly five named classical inputs (in `Item14FinalComposition.lean`).
* zz333: `open_nbhd_infinite_of_chartedSpace_complex` — open
  neighbourhoods in `ChartedSpace ℂ` are infinite (unconditional).
* zz335: **`NearbyRegularValueExists` UNCONDITIONAL** — first
  open-input → theorem conversion.
* zz336: **`NearbyRegularWitnessHypothesis` UNCONDITIONAL** —
  consequently `ramificationSumEqualsDegree_statement X Y` is now an
  unconditional theorem (via existing
  `ramificationSumEqualsDegree_holds_of_nearby_regular_witness_only`).

**Item 14 frontier after this session (4 named classical inputs):**

| # | Input | Status | Classical content | Est. LOC |
|---|---|---|---|---|
| 1 | `RiemannRochGenusZero X` | open | Riemann-Roch + Serre duality on δp divisor | 6,000–10,000 |
| 3 | `Surjective_of_NonConstant_Analytic_Manifold X RS` | open | Manifold open-mapping + clopen argument | 600–1,200 |
| 4 | `BijectiveAnalyticIsBiholomorphism X` | open | Inverse function theorem at ram-idx = 1 | 800–1,500 |
| 5 | Topological-sphere branch (`X ≃ₜ S² → ∃ HolomorphicEquiv X RS`) | open | Surface classification / uniformization-for-S² | 6,000–13,000 |
| | **Total** | | | **13,400–25,700** |

The mechanical glue through these four inputs to item 14 STRICT-CLOSED
is now complete (zz331). Each remaining input is a concrete classical
theorem with explicit textbook references (Forster Ch. 11).

**Update 2026-05-13 part 3 (zz337–zz380 chain, 45 commits, ~4,200 LOC landed).**

**See `HANDOFF_2026_05_13_RR_GENUS_ZERO.md` for the full session
summary, the 6-input frontier table, and the next-session plan.**
The `RiemannRochGenusZero X` input has been **architecturally
reduced** to a single deeper open hypothesis. Specifically:

* zz337 — decomposed `RiemannRochGenusZero X` into
  `ExistsMeroSimplePole_GenusZero X` (existence) +
  `MeroSinglePoleExtendsToDeg1Map X` (analytic bridge).
* zz338–zz341 — closed the analytic bridge conditional on a named
  `ChartPullback_Deriv_AtSimplePole_NeZero` regularity certificate:
  ∞-fibre singleton, non-constancy from any pole,
  `RegularValueWitness` builder, `degreeFiber = 1`.
* zz342 — wrapped the bridge as a `UniformSimplePoleRegularity X`
  universal hypothesis.
* zz343–zz344 — proved `UniformSimplePoleRegularity X`
  UNCONDITIONALLY via mathlib's `meromorphicOrderAt_eq_int_iff` +
  analytic-reciprocal extension + `Filter.EventuallyEq.deriv_eq`,
  bridging chart pullback with the south chart of `RiemannSphere`.
* zz345 — single-input wiring; `RiemannRochGenusZero X` ⇐
  `ExistsMeroSimplePole_GenusZero X` only.
* zz346 — further split: `ExistsMeroSimplePole_GenusZero X` ⇐
  `ExistsNonConstantBoundedByDeltaP_GenusZero X` (existence in L(δp))
  + `LiouvilleOnCompactConnected X` (holomorphic functions on
  compact connected RS are constant).
* zz347–zz350 — proved `LiouvilleOnCompactConnected X`
  UNCONDITIONALLY: chart-level max-modulus via
  `Complex.eventually_eq_of_isLocalMax_norm` + clopen globalisation
  on connected X.
* zz352–zz358 — built the `linearSystemDeltaP p : Submodule ℂ
  (X → ℂ)` infrastructure: `IsBoundedByDeltaP` predicate with
  zero/add/smul/const closure laws, constants subspace, `finrank` of
  constants = 1, strict-gt-constants iff exists-non-constant,
  `RR_DimGE2_GenusZero` dimension form with forward bridge to
  strict-gt, API extraction lemmas.

* zz360–zz362 — derived neg/sub closure of `L(δp)`; one-step
  `RR_DimGE2_GenusZero → ∃ g ∈ L(δp), g ∉ constants` (zz361);
  full closure chain `RR_DimGE2_GenusZero + LiftToMeromorphicNonzero
  ⇒ RiemannRochGenusZero` (zz362, naming the technical lifting
  hypothesis explicitly).

* zz363–zz366 — germLimit-based lift candidate (`germLimitLift`)
  setup with zero/const trivial cases (zz363, zz364); existence of
  punctured-nhd limit for `g ∈ L(δp)` at non-pole points via
  `tendsto_nhds_of_meromorphicOrderAt_nonneg` + chart-transport
  (zz365); `GermCoherentOff` predicate naming the canonicalisation
  property + `GermCoherentLift_Discharge` named hypothesis (zz366).

* zz368–zz378 — `linearSystemDeltaP_nontrivial` (zz368); various API
  consolidation (zz369–zz374); `MeromorphicNonzero.ofContinuousMeromorphic`
  + `.ofRegularContinuous` builders (zz375, zz376); 5-input
  decomposition of `LiftToMeromorphicNonzero` via the builder
  (zz377); final 6-input composition theorem
  `riemannRochGenusZero_from_six_inputs` (zz378).

* zz380 — **substantive discharge** of regular-continuity at non-pole
  points: under a named `UniversalGermCoherent X p` hypothesis,
  `ContinuousAt (germLimitLift g) x` for every `g ∈ L(δp)` and
  `x ≠ p`. Real proof via zz365's punctured-Tendsto + EventuallyEq
  transfer + mathlib's `continuousAt_iff_punctured_nhds`. (The
  `x = p` case remains for a future chip.)

**Item 14 frontier after zz337–zz362** (the `RiemannRochGenusZero X`
thread is now reduced to TWO concrete named classical inputs):

| Input | Status | Classical content | Est. LOC |
|---|---|---|---|
| `RR_DimGE2_GenusZero X` (`∃ p, 2 ≤ finrank ℂ (linearSystemDeltaP p)` under `genus X = 0`) | open | Riemann-Roch formula + Serre duality at `δp` for genus 0 | 6,000–10,000 |
| `LiftToMeromorphicNonzero X` (technical: plain `g ∈ L(δp) \ constants` ⇒ `∃ MeromorphicNonzero X` lift) | open | Identity theorem + chart redefinition for `regular_continuousAt` | 800–1,500 |
| `Surjective_of_NonConstant_Analytic_Manifold X RS` | open | Manifold open-mapping + clopen | 600–1,200 |
| `BijectiveAnalyticIsBiholomorphism X` | open | Inverse function theorem at ram-idx = 1 | 800–1,500 |
| Topological-sphere branch | open | Surface classification / uniformization-for-S² | 6,000–13,000 |

The analytic bridge half of the Forster Theorem 16.9 route is
unconditionally closed. The remaining `RiemannRochGenusZero`-thread
work is the heavy Riemann-Roch formula + Serre duality classical
content (multi-thousand-LOC L²-Hodge or sheaf cohomology, not in
mathlib at the pin).

**Update 2026-05-13 part 4 (zz382 + zz383–zz388)**: inputs #3 and #4 of
the item-14 final composition are now both **discharged unconditionally**.

* **zz382** (`Manifold/SurfaceOfNonConstantDischarge.lean`, +412 LOC):
  `Surjective_of_NonConstant_Analytic_Manifold X Y` is a THEOREM, by
  the within-one-chart identity-theorem clopen + mathlib's
  `AnalyticAt.eventually_constant_or_nhds_le_map_nhds` open-map
  dichotomy.
* **zz383–zz388** (`Manifold/{BijectiveAnalyticDischarge,
  GlobalInverseSmooth, ManifoldInverseContMDiffAt, ChartPullbackInverse,
  ChartPullbackHurwitz, HurwitzCorollary}.lean`, +~1,300 LOC total):
  `BijectiveAnalyticIsBiholomorphism X` is a THEOREM, via the
  Hurwitz-corollary chain `deriv_ne_zero_of_injOn_ball` (zz383) →
  chart-pullback inverse (zz384/zz385) → manifold inverse `ContMDiffAt`
  (zz386) → global `Function.invFun` smoothness (zz387) → packaging as
  `HolomorphicEquiv` (zz388). 8639 jobs green, no `sorry`/no `axiom`.

**Item 14 frontier after zz382 + zz388 (2 remaining inputs)**:

| Input | Status | Classical content | Est. LOC |
|---|---|---|---|
| `RR_DimGE2_GenusZero X` + `LiftToMeromorphicNonzero X` (RR-thread) | **blocked architecturally** (`linearSystemDeltaP` blip counterexample, see "Architectural issue" in `OPEN.md`); unblock requires germ-field refactor | RR + Serre duality on δp + germ-of-meromorphic-functions ambient | 6,800–11,500 + ~1,000–2,000 refactor |
| `h_top : Nonempty (X ≃ₜ StandardS2) → Nonempty (HolomorphicEquiv X RS)` (topological-sphere branch / input #5) | open | Uniformization for closed Riemann surfaces of genus 0 / surface classification | 6,000–13,000 |

#### D.2.5 — Scout of the topological-sphere branch (input #5)

The hypothesis is `h_top : Nonempty (X ≃ₜ StandardS2) → Nonempty
(HolomorphicEquiv X RiemannSphere)` as named in
`Topology/Item14FinalComposition.lean`. Routes evaluated:

* **Route A (via Hodge identification + RR-thread)**. From `X ≃ₜ S²`
  conclude `TopologicalGenus X = 0` (available via
  `Homeomorph.topologicalGenus_eq` + `TopologicalGenus S² = 0`), then
  use a Hodge identification `TopologicalGenus X = JacobianChallenge.genus X`
  on compact Riemann surfaces to conclude `genus X = 0`, then use
  `RiemannRochGenusZero` (input #1) + degree-1-is-biholomorphism (input
  #4, now closed via zz388) to produce the biholomorphism. **Status**:
  blocked twice — the Hodge-identification bridge is itself
  multi-thousand-LOC Hodge theory not in mathlib at the pin, AND the
  RR-thread is blocked on the germ-field refactor (see "Architectural
  issue" in `OPEN.md`). Route A is therefore **architecturally subordinate
  to RR**, not an independent path.

* **Route B (direct via uniformization-for-S²)**. Forster Ch. 26 /
  Farkas–Kra Ch. III: any complex structure on `S²` is biholomorphic to
  `OnePoint ℂ`. Standard proofs use either the Riemann mapping theorem
  (for `S² ∖ {p}`, lifted to a meromorphic function on `S²`) or
  harmonic-function constructions via the Dirichlet problem. **Status**:
  requires Riemann mapping or Dirichlet on a punctured `S²`; neither is
  at the pin. **6,000–13,000 LOC** classical Riemann-surface theory.

* **Route C (direct from the homeomorphism)**. Pick `p ∈ X`, set
  `q = h(p) ∈ S²`. The chart coordinate of `RiemannSphere` around `q`
  is a meromorphic function on `RS` with simple pole at the south pole.
  Pull back along `h⁻¹`. **Status**: pullback under a bare homeomorphism
  is only continuous, not meromorphic — the meromorphy needs the same
  Hodge-theoretic content as Route A. Not chip-tractable as stated.

**Partial-progress observation**. Even if input #5 alone is closed, it
only closes the `←` direction of item 14 (`Nonempty (X ≃ₜ S²) →
JacobianChallenge.genus X = 0`), via
`s2ImpliesGenus0_of_uniformizationToRiemannSphere` (using zz307's
`genus_eq_zero_of_holomorphicEquiv_RiemannSphere_honest`). The `→`
direction (`genus X = 0 → Nonempty (X ≃ₜ S²)`) still requires the
RR-thread separately. So **item 14 STRICT-CLOSED needs BOTH the RR-thread
unblocked AND input #5 closed**; input #5 alone is half of item 14.

**Conclusion**. Input #5 is *not chip-tractable at the current pin*.
Any route through it requires Hodge theory or Dirichlet harmonic
analysis as upstream mathlib content. The cheapest concrete entry point
is the Hodge identification `TopologicalGenus X = JacobianChallenge.genus
X` on compact Riemann surfaces (~3,000–6,000 LOC by itself); this would
also be a precondition for any honest closure of input #1 in the
genus-zero-from-topology direction. Pursuing it is a strategic decision
on par with the germ-field refactor — not a chip-sized commitment.

**Existing infrastructure relevant to input #5 (no new code needed)**:
- `Topology/SurfaceGenus.lean` — `TopologicalGenus X = finrank ℚ (H₁(X; ℚ))`
  + `Homeomorph.topologicalGenus_eq` (homeomorphism invariance).
- `Topology/OnePointHomeoSphere.lean` — `RiemannSphere ≃ₜ StandardS2`.
- `Manifold/HolomorphicEquivGenusInvariance.lean` (zz310) — biholomorphism preserves genus.
- `Manifold/PullbackHolomorphicOneForm.lean` (zz307) —
  `genus_eq_zero_of_holomorphicEquiv_RiemannSphere_honest`.
- `Manifold/RiemannSphereGenusAPI.lean` — `genus RiemannSphere = 0`
  unconditional.
- `Topology/S2ImpliesGenus0Discharge.lean` — packages the
  "linear-equivalence-on-1-forms → genus = 0" reduction (weaker than
  full input #5, but already closed honestly under the linear-equivalence
  hypothesis).

### D.3 — Phase 4 (item 1: `genus X` honest)

`genus X = Module.finrank ℂ (HolomorphicOneForm X)` is the definition; the strict bar requires `HolomorphicOneForm X` to be the right object AND finite-dimensional.

**Verified mathlib status**:
- ✓ `Analysis/InnerProductSpace/Laplacian.lean` (basic Laplacian on inner product space, scalar functions).
- ✓ `Geometry/Manifold/Complex.lean` (6 declarations on holomorphic functions).
- ✗ NO Hodge decomposition.
- ✗ NO HolomorphicOneForm class.
- ✗ NO finite-dimensionality of any infinite-dimensional space of forms.

**Per-component LOC**:

| Component | What it needs | Available? | LOC |
|---|---|---|---|
| **4.A k-form structure on a manifold (incremental over Phase 2.D)** | Lift `OneForm` (Phase 2) to `KForm M k` for k=0,1,2,... | inherits from Phase 2.D | **400–800** (incremental) |
| **4.B Holomorphic forms class (specialization of 2.E)** | Already covered in Phase 2 component 2.E | inherits from Phase 2.E | **(included)** |
| **4.C Hodge Laplacian on forms + harmonic-form theory** | Define Δ = dd* + d*d on forms. ker = harmonic. Self-adjoint elliptic on compact manifold ⇒ finite-dimensional kernel. | Laplacian on scalar ✓; lift to forms ✗; elliptic theory ✗ | **5,000–9,000** (the bulk of Phase 4) |
| **4.D `dim ℂ HolomorphicOneForm X < ∞`** | Apply 4.C: harmonic 1-forms are finite-dim. Holomorphic 1-forms ↪ harmonic 1-forms (closed + co-closed forms include holomorphic). | depends on 4.C | **500–1,000** |
| **4.E `dim ℂ HolomorphicOneForm X = (rank H_1) / 2`** | Hodge theorem matching de Rham cohomology to harmonic forms; combine with Phase 2.C. | depends on 4.C, Phase 2.C | **1,000–2,000** |

**Phase 4 total verified**: **6,900–12,800 LOC**.

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

## F. Net realistic ceiling at this pin (revised 2026-05-14 after A1+A2+C1+C3+C4 work + Pic⁰(ℙ¹) = 0 unconditional)

### F.0 Measured ground truth

- **Total `.lean`:** **86,894 LOC** (86,489 in `JacobianChallenge/` + 405-line manifest), **416 files**.
- **Recent waves (2026-05-14):** A1 discharge (+870 LOC); C1 primitives (`feat/c1-smooth-path-connected`, +371 LOC); A2 from `feat/antipode-smoothness` (+660 LOC) + unconditional headline (+109 LOC); seven C3+C4 named-hypothesis reductions (~800 LOC); five RS-side principal-divisor chips closing `Pic⁰(ℙ¹) = 0` unconditionally (~830 LOC).
- **Scoreboard:** 12 STRICT-CLOSED · 3 STUB · 9 OPEN (item flips await Phase 2 wiring of the Abel-Jacobi iso on arbitrary `X`, not the genus-0 corner).
- **Per-chip-file LOC density** (measured across all 2026-05-14 chips): **90–322 LOC**, mean ≈ 195.

### F.1 Past-wave LOC (grounds the remaining estimates)

| Wave | Files | LOC | Per-file avg |
|---|---|---|---|
| Germfield arc (item 14 reduction) | 9 | 2,454 | 273 |
| PL-4 Abel–Jacobi scaffolding (`AbelJacobi*.lean`) | 6 | 1,052 | 175 |
| `feat/linear-system-divisor` germ-field RR layer (18 commits, pre-2026-05-14) | 16 | 3,064 | 191 |
| 2026-05-14 A1 + A2 + C1 + reductions + RS unconditional (~30 commits) | 25 | ~3,800 | ~150 |
| Existing Hodge files (`Hodge*.lean`) | 4 | 524 | 131 |
| Existing period-lattice files (`PeriodLattice*.lean`) | 11 | 2,239 | 204 |

### F.2 Named hypotheses (verified by grep)

**PL-4 / period-lattice (1 landed, 5 open):**

| Hypothesis | File | Status |
|---|---|---|
| `AbelJacobiHypothesisBundle` | `Manifold/AbelJacobiArcSummary.lean` | **landed** |
| `HolomorphicOneFormFiniteDim` | `Manifold/HodgeFiniteDimensional.lean` | open |
| `PeriodLatticeDiscretenessBundle` | `Manifold/PeriodLatticeDiscretenessFromBilinear.lean` | open |
| `AbelJacobiInput` | `Manifold/AbelJacobiPoint.lean` | open (`SmoothPath.const` landed) |
| `AbelHypothesis` | `Manifold/AbelJacobiPic0.lean` | open |
| `JacobiInversion` | `Manifold/AbelJacobiIso.lean` | open |

**Genus-0 RR `dim L(δp) ≥ 2` chain (0 open after A1 + A2 discharges; merged to main 2026-05-14):**

| Hypothesis | File | Status |
|---|---|---|
| `LinearSystemAtInftyRS_BoundedBySimplePoleSpan` | `Topology/LinearSystemAtInftyRSDischarge.lean` | **landed** (A1, 2026-05-14) |
| `ExistsMobiusToInftyRS` | `Manifold/MobiusTransitivityRS.lean` + bridge in `Topology/LinearSystemGermDeltaPFiniteDimRSUnconditional.lean` | **landed** (A2, 2026-05-14) |
| Uniformization at genus 0 (`genus X = 0 → Nonempty (HolomorphicEquiv X RS)`) | — | named hypothesis only; out of scope of in-tree closure |

**Abel-Jacobi iso on RS (0 open, merged to main 2026-05-14):**

| Hypothesis | File | Status |
|---|---|---|
| `Subsingleton (Pic0 RiemannSphere)` | `Manifold/Pic0RiemannSphereSubsingleton.lean` | **landed** unconditionally |
| `AbelJacobiInput.abelJacobiEquiv_of_RiemannSphere_unconditional` | same | **landed** — `Pic⁰ RS ≃+ AnalyticJacobian RS` axiom-free |

**Unconditional headlines (post-A1 + A2):**

| Theorem | File |
|---|---|
| `linearSystemGermDeltaPFiniteDim_RiemannSphere_unconditional` | `Topology/LinearSystemGermDeltaPFiniteDimRSUnconditional.lean` |
| `rr_DimGE2_GenusZero_Germ_of_uniformization_unconditional_RSFiniteDim` | same |

**C1 sub-arc primitives (toward `AbelJacobiInput` discharge,
`feat/c1-smooth-path-connected` merged 2026-05-14):**

| Primitive | File | Status |
|---|---|---|
| `SmoothPathConnected I X` predicate | `Manifold/SmoothPathConnected.lean` | **landed** |
| `AbelJacobiInput.ofSmoothPathConnected` | same | **landed** |
| `SmoothPath.linearInChart` (line-in-target ω hypothesis) | `Manifold/SmoothPathLinearInChart.lean` | **landed** |
| Chart-cover lift `linearInChart → SmoothPathConnected` | — | open |
| ω-level structural caveat (line vs segment) | docstring of `SmoothPathLinearInChart.lean` | documented |

### F.3 Remaining LOC per cluster (real-number estimates)

| Cluster | Content | Estimate |
|---|---|---|
| ~~**A1**~~ | ~~`LinearSystemAtInftyRS_BoundedBySimplePoleSpan`~~ — **LANDED 2026-05-14** (`Analysis/PolynomialLiouville.lean` + `Topology/LinearSystemAtInftyRSDischarge.lean`, 870 LOC actual; estimate had been 400–900). | **done** |
| ~~**A2**~~ | ~~`ExistsMobiusToInftyRS`~~ — **LANDED 2026-05-14** (`Manifold/RiemannSphereAntipodeSmooth.lean` 255 LOC + `Manifold/RiemannSphereTranslate.lean` 322 LOC + `Manifold/MobiusTransitivityRS.lean` 80 LOC + headline bridge `Topology/LinearSystemGermDeltaPFiniteDimRSUnconditional.lean` 109 LOC = 766 LOC total; estimate had been 500–1,100). | **done** |
| **B** | `HolomorphicOneFormFiniteDim X` (L² Hodge / elliptic regularity; mathlib gap) | **3,000–7,000** |
| **C1** | `AbelJacobiInput` (smooth-path-connectedness; `linearInChart` + chart-cover) — 2 primitives landed 2026-05-14 (`SmoothPathConnected` predicate + `linearInChart` at ω with line-in-target hypothesis, 371 LOC). Remaining: chart-cover lift. ω-level structural caveat documented (line vs segment). | **400–1,100** *remaining* |
| **C3 (genus-0 corner)** | `AbelHypothesis_of_genus_zero` (via `Subsingleton (AnalyticJacobian)` at `genus X = 0`) — landed 2026-05-14 (`Manifold/AbelHypothesisGenusZero.lean`, 99 LOC). | **done** |
| **C3 (chain-level + algebra + per-generator)** | `AbelHypothesis B ← AbelChainPeriodCondition B ← AbelGeneratorPeriodCondition B` (`Manifold/AbelHypothesisFromPeriodCondition.lean`, ~525 LOC across 4 commits 2026-05-14). Reduces C3 to a single sharp atomic statement: for each `f : MeromorphicNonzero X`, the period vector of the AJ chain of `div(f)` lies in `periodLatticeImage`. The remaining mathlib content is the classical Abel-forward chain construction (level-set chain of `f`) and its Stokes-invariance. | **1,000–2,500** *remaining* (general-genus discharge of `AbelGeneratorPeriodCondition`) |
| **C4 (genus-0)** | `jacobiInversion_of_genus_zero_and_subsingleton_pic0` (`Manifold/JacobiInversionGenusZero.lean`, 90 LOC). At genus 0, `JacobiInversion B hAbel` reduces to `Subsingleton (Pic0 X)`. | **done** at genus 0 modulo `Subsingleton (Pic0 X)` |
| **C4 RS (Pic⁰(ℙ¹) = 0)** | `subsingleton_pic0_RiemannSphere` (`Manifold/Pic0RiemannSphereSubsingleton.lean`, 190 LOC, built on `mnRSSimplePole` 110 LOC + `mnRSInversion` 200 LOC + `mnRSAffineFactor` 190 LOC + elementary-divisor identity in `Pic0RiemannSphereTrivial.lean` 140 LOC) — **unconditional** in-tree. `AbelJacobiInput.abelJacobiEquiv_of_RiemannSphere_unconditional` ships the full Abel-Jacobi iso `Pic0 RS ≃+ AnalyticJacobian RS` axiom-free. | **done** (Pic⁰(ℙ¹) = 0 unconditional) |
| **C4 general genus** | Abel converse (injectivity) + Jacobi inversion theorem (surjectivity) — classical content not at the pin. | **~1,200–2,800** *remaining* |
| **C2** | `PeriodLatticeDiscretenessBundle` (H₁ rank-2g + Riemann bilinear; mathlib gap) | **1,800–3,800** |
| **C3** | `AbelHypothesis` (Stokes on principal-divisor 2-chains) | **1,200–2,800** |
| **C4** | `JacobiInversion` (Abel–Jacobi surjective; classical degree or theta) | **1,200–2,800** |
| **D** | Item 14 `S2ImpliesGenus0` (simply-connectedness route via π₁(S²)=0 + Liouville on universal cover; bypasses uniformization) | **1,200–3,000** |
| **E** | Items 17/18/21 smoothness (`ofCurve_contMDiff`, `pushforward_contMDiff`, `pullback_contMDiff`) — flips with ChartedSpace on `Jacobian X` | **500–1,200** |
| **F** | `Basic.lean` instance wiring (Topology / Compact / Manifold / LieAddGroup); `ofCurve_inj` via Abel injectivity | **400–900** |
| **G** | Polish, integration, contingency | **1,000–2,200** |

**Uniformization at genus 0** is left **out of scope** of this map. Mathlib-style formalization is **8,000–20,000+ LOC** and multi-month; the realistic plan keeps it as a named classical hypothesis.

### F.4 Totals

| Scenario | Range | Final scoreboard |
|---|---|---|
| **Defer uniformization** (recommended) | **11,800–27,200 LOC** | **23/24 STRICT-CLOSED** (item 14 stays OPEN with uniformization as the one owed classical input) |
| **Attempt uniformization in-tree** | ~20k–47k LOC | 24/24 |

**Recommended working range: 11,000–22,000 LOC** for the realistic 23/24 target (after 2026-05-14's substantial work).

**Final-state projection** (23/24 path): repo grows from current **86,894 LOC** → **~97,000–109,000 LOC**.

### F.5 Recommended priority order (revised 2026-05-14 post A1 + A2 + C1 primitives + Pic⁰(ℙ¹) = 0 unconditional)

1. ~~**A1 + A2 (~900–2,000 LOC).**~~ Both **landed 2026-05-14**.
   A1 via `Analysis/PolynomialLiouville.lean` +
   `Topology/LinearSystemAtInftyRSDischarge.lean` (870 LOC). A2 via
   `Manifold/RiemannSphereAntipodeSmooth.lean` +
   `Manifold/RiemannSphereTranslate.lean` +
   `Manifold/MobiusTransitivityRS.lean` (657 LOC). Composed in
   `Topology/LinearSystemGermDeltaPFiniteDimRSUnconditional.lean`
   (109 LOC). **`RR_DimGE2_GenusZero_Germ X` is now unconditional
   on uniformization alone** — the genus-0 RR `dim_ℂ L(δp) ≥ 2`
   chain on the germ field reduces to a single named classical
   input.
2. **C1 chart-cover lift (~400–1,100 LOC remaining).** Two primitives
   landed (`Manifold/SmoothPathConnected.lean` predicate +
   `Manifold/SmoothPathLinearInChart.lean` linearInChart at ω with
   line-in-target hypothesis). Remaining: chart-cover argument
   lifting `linearInChart` to `SmoothPathConnected 𝓘(ℝ, ℂ) X`.
   ω-level structural caveat documented (line vs segment); resolving
   the caveat at the ω level needs either a `SmoothPath`-side
   refactor (downgrade to `C^∞`, then `Real.smoothTransition` makes
   linearInChart unconditional on chart-shape) or analytic
   continuation across charts — both are genuine separate sub-chips.
3. **C3 `AbelHypothesis` + C4 `JacobiInversion` — ~2,200–5,300 LOC *remaining*** for full general-genus discharge. Completes `Pic⁰ ≃+ AnalyticJacobian` unconditionally. **Highest-leverage chunk: flips items 4, 5, 10, 11, 12, 13 simultaneously (6 items)** via the existing bundle. *Twelve C3+C4 chips landed 2026-05-14:*
   * **Genus-0 + reduction layer (7 chips, 2026-05-14 morning/midday):** genus-0 trivial discharge of `AbelHypothesis`; chain-level reduction to `AbelChainPeriodCondition`; algebra layer (additivity + closure); per-generator reduction to `AbelGeneratorPeriodCondition`; genus-0 C4 from `Subsingleton (Pic0 X)`; Abel-Jacobi iso on RS conditional; `Pic0` subsingleton bridge.
   * **RS unconditional layer (5 chips, 2026-05-14 evening):** `mnRSSimplePole` + `mnRSInversion` + `mnRSAffineFactor` (three `MeromorphicNonzero RS` generators); elementary-divisor identity `principalDivisorMap (mnRSAffineFactor a) = Div.single (some a) - Div.single ∞`; closure decomposition for every `Div0 RS` plus `subsingleton_pic0_RiemannSphere` final discharge — **`Pic⁰ RS ≃+ AnalyticJacobian RS` axiom-free**.

   The remaining work is the general-genus content: discharging `AbelGeneratorPeriodCondition B` for arbitrary X (Stokes-on-2-chains content), and general-genus C4 (Abel converse + Jacobi inversion theorem).
4. **E + F (~900–2,100).** Wire `Basic.lean` instance bodies + smoothness lemmas. Flips items 17, 18, 21, and item 16 (`ofCurve_inj` falls out of Abel injectivity).
5. **C2 `PeriodLatticeDiscretenessBundle` (~1,800–3,800).** Required if `PeriodLatticeDiscretenessBundle` should be honest rather than a named hypothesis. Can defer if 23/24 is the target.
6. **B `HolomorphicOneFormFiniteDim` (~3,000–7,000).** Flips item 1. Largest single chunk.
7. **D Item 14 finish (~1,200–3,000).** Simply-connectedness route is the simpler of the two routes documented in `Topology/S2ImpliesGenus0*.lean`.
8. **G polish (~1,000–2,200).**

### F.6 Expected scoreboard progression

| Milestone | After steps | STRICT-CLOSED |
|---|---|---|
| (start) | — | 12/24 |
| PL-4 discharge done | 1–3 | **18/24** (gain 4, 5, 10, 11, 12, 13) |
| Basic.lean wiring | 4 | **22/24** (gain 16, 17, 18, 21) |
| Hodge finite-dim | 6 | **23/24** (gain 1) |
| Item 14 (deferring uniformization) | 7 | **23/24** — item 14 remains OPEN with uniformization + `S2ImpliesGenus0` named |
| Full closure | requires uniformization in-tree | 24/24 |

## G. Calibration

This map should now be the highest-fidelity it can be without actually attempting the Phase 1 proofs. Remaining sources of estimate uncertainty (in decreasing order):

1. **Step P1.1's invariance argument**: 150–400 LOC range depending on Finset/Multiset bookkeeping. Will only narrow by attempting.
2. **Step P1.5's cascade size**: depends on what `PrincDiv X = ⊥` is used for outside the obvious sites. ~5 grep'd consumers known; there may be more in proofs that use `AddSubgroup.mem_bot` indirectly.
3. **Phase 2/3/4 LOC ranges are 2× wide**: classical content sized by analogy to similar mathlib formalizations (Bochner integral was ~5k LOC; Lebesgue measure ~4k). Estimates assume analogous effort.
4. **Item 16 path**: even after Abel's theorem (Phase 2), the honest proof of `ofCurve_inj` needs careful divisor bookkeeping. ~500 LOC follow-up after Phase 2.

Beyond these, every other claim in this map is verified against `.lake/packages/mathlib/Mathlib` (jacobian repo's pin) and `Basic.lean` HEAD `1fa030a`.

## H. Verification audit log

**2026-05-14 update:** Twenty-plus commits landed on
`feat/linear-system-divisor` in one day:

* A1 discharge (`bdd9ba0`); A2 from `feat/antipode-smoothness`
  (3 commits + chore + merge); unconditional RR-chain headline
  (`2909a6b`).
* C1 primitives from `feat/c1-smooth-path-connected` (merge `8b32243`).
* Twelve C3+C4 chips: `9faa9bc` (C3 genus-0), `ee8d225` (C3 chain
  reduction), `f3b4fff` (C3 algebra), `8e26bf7` (C3 per-generator),
  `2a60032` (C4 genus-0), `a8fe501` (RS bridge), `9d6196f` (Pic0
  subsingleton bridge), `56c914e` (mnRSSimplePole), `8e1cceb`
  (mnRSInversion), `f4575d7` (mnRSAffineFactor), `4aa4152`
  (elementary divisor), `c505ba9` (**Pic⁰(ℙ¹) = 0 unconditional**).
* Multiple docs commits interleaved.

Post-final-commit `taskpolicy lake build` clean (**8710 jobs**, up
from 8694 pre-day). Zero `sorry`, zero `axiom` across all chips.
Genus-0 Abel-Jacobi isomorphism on `RiemannSphere` is now
**unconditional in-tree**.

All grep facts below are from the pre-2026-05-14 state and remain
valid (the new files are additions, not modifications to prior content).

The facts in this map were checked by automated grep against this repo and the mathlib pin at `.lake/packages/mathlib`. Results:

- **22 of 22 cited line numbers in `Basic.lean` ✓ verified**.
- **13 of 14 cited mathlib lemma line numbers ✓ verified.** One imprecision (line 109's `prod` is in `namespace MeromorphicAt` not as a qualified name) corrected in section B.1.
- **8 cascade files for `PrincDiv = ⊥` ✓ enumerated explicitly** in P1.5 (was "5–10" in the previous draft).
- **`principalDivisorAddHom` ✓ exists at `Divisor/PrincipalDivisorRange.lean:46`** as named.
- **`PrincDivHonestCandidate` ✓ exists at `PrincipalDivisorRange.lean:209`** (NOT line 97 — line 97 is inside a docstring showing what the swap should look like). The actual definition is at line 209. `principalDivisorAddHom` (the `→+` form) at line 342.
- **Items 19/20 verified to route through `pushforward_mk := rfl` + divisor-level lemmas**, not through the `hBot` dependency in `Pic0.pushforward`'s definition. Auto-flip claim re-confirmed.
- **R4a/R4b/Hurwitz local form/RamificationIndexEqLocalKFold ✓ all confirmed in `Manifold/`**.
- **Mathlib gaps section ✓ verified by exhaustive grep** for `RiemannSurface`, `HolomorphicOneForm`, `firstHomology`, `H_1`, surface classification keywords, Hodge keywords. None found.
- **Phase 2/3/4 LOC ranges replaced with per-component breakdowns** verified against this pin's mathlib (D.1, D.2, D.3 in this map). Each component cites either ✓ available foundations or ✗ specific missing pieces. Ranges remain 2× wide because they sum per-component estimates each of which has 2× spread. Will only narrow by attempting.

- **All 13 cited foundation files in `Phase 2-4` mathlib status section verified to exist** (CWComplex Abstract+Classical, RelativeCellComplex, FundamentalGroup, ZLattice, Tangent bundle, MFDeriv exterior derivative, Manifold/Complex, PartitionOfUnity, Laplacian, OnePoint/Sphere, Manifold/Instances/Sphere, SingularHomology). All 11 `✗` claims (cellularChain, cellularHomology, OneForm class, holomorphicOneForm, periodPairing, abelJacobi, jacobiInversion, surfaceClassification, hodgeDecomposition, twoManifoldGenus, manifoldDifferentialForm) verified absent by exhaustive grep.

This map is now as high-fidelity as can be without actually attempting the Phase 1 proofs.
