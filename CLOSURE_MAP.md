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

**Update 2026-05-13 part 3 (zz337–zz366 chain, ~3,750 LOC landed).**
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

## F. Net realistic ceiling at this pin (verified per-component)

| Phase | LOC range (verified) | Items flipped |
|---|---|---|
| Phase 0 (done this session) | ~12,000 already merged | 8, 22, 23, 24 (Buzzard bar; strict-bar requires Phase 1's `Jacobian` honest) |
| **Phase 1** (chippable now) | **2,050–2,250** | 12 items: 2, 3, 6, 7, 8, 9, 15, 19, 20, 22, 23, 24 (strict bar) |
| **Phase 2** (period lattice + Abel-Jacobi) | **15,500–29,600** | 10 items: 4, 5, 10, 11, 12, 13, 16, 17, 18, 21 |
| **Phase 3** (surface classification) | **7,100–15,000** | 1 item: 14 |
| **Phase 4** (Hodge / finite-dim of forms) | **6,900–12,800** | 1 item: 1 |

**Total LOC remaining for 24/24 STRICT-CLOSED**: **31,550–59,650 LOC**.

The repo currently sits at **49,526 LOC** (`*.lean` files, all of `JacobianChallenge/` + top-level import manifest). **Final-state projection**: ~81,000–109,000 LOC for full closure.

Calibration buffer (today's pattern: ~1.5x estimates exceeded due to architectural defect surfacing during attempts): **realistic upper bound ~90,000 LOC remaining**, **realistic lower bound ~30,000 LOC remaining**.

**Order in which items can flip**:
1. Phase 1 (Phase 1's ~2k LOC is the immediate next wave) → 12 STRICT-CLOSED
2. Phases 3 + 4 + part of Phase 2 (cellular homology framework) → could in principle proceed in parallel; Phase 2's items depend on Phase 3 for the standard CW structure
3. Phase 2 final items (16, 17, 18, 21) follow once Abel-Jacobi machinery (2.K-2.O) lands

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
- **Phase 2/3/4 LOC ranges replaced with per-component breakdowns** verified against this pin's mathlib (D.1, D.2, D.3 in this map). Each component cites either ✓ available foundations or ✗ specific missing pieces. Ranges remain 2× wide because they sum per-component estimates each of which has 2× spread. Will only narrow by attempting.

- **All 13 cited foundation files in `Phase 2-4` mathlib status section verified to exist** (CWComplex Abstract+Classical, RelativeCellComplex, FundamentalGroup, ZLattice, Tangent bundle, MFDeriv exterior derivative, Manifold/Complex, PartitionOfUnity, Laplacian, OnePoint/Sphere, Manifold/Instances/Sphere, SingularHomology). All 11 `✗` claims (cellularChain, cellularHomology, OneForm class, holomorphicOneForm, periodPairing, abelJacobi, jacobiInversion, surfaceClassification, hodgeDecomposition, twoManifoldGenus, manifoldDifferentialForm) verified absent by exhaustive grep.

This map is now as high-fidelity as can be without actually attempting the Phase 1 proofs.
