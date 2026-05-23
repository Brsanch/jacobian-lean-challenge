# Item 14 classical proof map — stacked at full granularity

Honest map of what's needed to close [`Basic.lean:73`](JacobianChallenge/Basic.lean)
(`genus_eq_zero_iff_homeo`). Produced 2026-05-23 after audit showed the
repo had ballooned to 183k LOC via paraphrase chips while the real
classical content sat untouched.

## Mathlib reality check (grepped 2026-05-23)

**Present in mathlib:**

| Concept | Files | Use for our case |
|---|---|---|
| `AnalyticAt` / `AnalyticOnNhd` | 45 + 49 | Holomorphic functions on ℂ-open sets — for chart-local primitives, Cauchy integrals. |
| `Complex.CauchyIntegral` | 12 | Cauchy integral / residue theorem — for period vanishing on simply-connected charts. |
| `MeromorphicAt` / `MeromorphicOn` | 18 | Meromorphic functions — for the simple-pole germ at the heart of `hSP`. |
| `ContMDiffSection` | 1 | Sections of vector bundles — our `HolomorphicOneForm X` already uses it. |
| `CotangentSpace` | 11 | Cotangent bundle — our `HolomorphicOneForm` evaluation. |
| `fundamentalGroup` / `SimplyConnected` | 11 + 3 | π₁ — for the reverse-leg simply-connected hypothesis. |
| `OnePoint` | 14 | One-point compactification — our `RiemannSphere := OnePoint ℂ`. |

**Absent from mathlib (must be built or deferred):**

| Concept | Status |
|---|---|
| `RiemannSurface` (as a class abstraction) | 0 matches — our `[ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]` is the substitute. |
| Riemann-Roch theorem | 0 matches — must be built; `hSP` is the genus-0 specialization. |
| Dolbeault complex / cohomology | 0 matches — `dbarOperator` partially started in tree. |
| Hodge theory (analytic, on Riemann surfaces) | 0 matches (Perfectoid/de-Rham matches are unrelated arithmetic geometry). |
| Uniformization theorem | 0 matches. |

So the bloat is partly justified — we *do* have to build a lot of this. But
the paraphrase-chip pattern (renaming named hypotheses) is bloat ON TOP
of the legitimate infrastructure. Audit estimate: of the 183k LOC, maybe
80–100k is genuinely classical-content infrastructure and 80–100k is
paraphrase / per-X duplication / parallel routes.

## The classical proof of item 14 (Forster Ch. III, §10–§16 outline)

### Forward leg: `genus = 0 → Nonempty (X ≃ₜ S²)`

1. **Riemann–Roch on compact Riemann surface X of genus g, divisor D:**
   `dim L(D) − dim L(K − D) = deg D − g + 1`,
   where K is the canonical divisor (deg K = 2g − 2).
2. **Genus-0 specialization (Forster §16.10):** for `D = [p]` (any
   point), `deg D = 1`, so `dim L(K − D) = 0` (since `deg(K − D) = −3 < 0`
   for g = 0). Hence `dim L([p]) = 1 − 0 + 1 = 2`.
3. Constants ⊂ L([p]) gives dim ≥ 1; the extra dim from RR gives a
   **non-constant meromorphic function `f` with a simple pole at `p`
   and holomorphic elsewhere**. (This is `hSP`.)
4. `f : X → ℂP¹` is a meromorphic function — extend `f(p) = ∞`.
5. **`f` has degree 1** (single simple pole, no other poles, takes each
   value once by counting zeros).
6. **Degree-1 holomorphic map ⟹ biholomorphism** (standard: injective +
   surjective + holomorphic between compact Riemann surfaces).
7. `X ≃ ℂP¹ ≃ₜ S²`.

### Reverse leg: `Nonempty (X ≃ₜ S²) → genus = 0`

1. `X ≃ₜ S²` ⟹ `SimplyConnectedSpace X` (S² is simply connected).
2. **Every closed holomorphic 1-form ω on simply-connected X has trivial
   monodromy** ⟹ **has a global holomorphic primitive `F`** with
   `dF = ω`. (Stokes / monodromy theorem.)
3. **Holomorphic function on compact connected complex manifold is
   constant** (maximum modulus principle, or by Liouville on the
   universal cover when X is compact). So `F = const`.
4. Hence `ω = dF = 0`.
5. So `H⁰(X, Ω¹) = 0`, i.e. `genus X = 0`.

## The 5 substantive theorems item 14 actually needs

If you closed these five, item 14 closes. Everything else is glue.

### T1. `existsSimplePoleGermAtSomePoint_of_genusZero` (= `hSP` on arbitrary X)

**Statement (Lean):**
```
theorem hSP_of_genusZero [CompactSpace X] [ConnectedSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (h_genus : JacobianChallenge.genus X = 0) :
    MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X
```

**Classical content:** Riemann–Roch dim bound at g = 0. Single application of
`dim L([p]) ≥ 2`.

**Pre-reqs in tree (need building or audit):**
- `dim L(D)` defined for a divisor D on X — partial in `Divisor/` namespace.
- Riemann–Roch inequality `dim L(D) ≥ deg D − g + 1` for compact connected
  Riemann surface — **not in tree**. Even the genus-0 special case (degree of K = −2)
  is missing.
- Bridge "non-zero element of `L([p])` with `[p]` reduced ⟹ simple-pole germ".

**Realistic Lean cost:** 2–5k LOC if Riemann–Roch is built from
divisor degree + finite-dim L(D) + Serre duality. (~5k for Serre
duality, ~1k for the dim bound itself, ~1k for the simple-pole
extraction.)

**Mathlib leverage:** `MeromorphicAt` / `MeromorphicOn` for the germ
side; `Module.finrank` for the dim side; nothing for Riemann–Roch
proper.

### T2. `degreeOneHolomorphic_isBiholomorphism` (forward, step 5–6)

**Statement:** A holomorphic map `f : X → Y` between compact connected
Riemann surfaces of degree 1 is a biholomorphism.

**Classical content:** Branch-point count via Riemann–Hurwitz; injective +
surjective via degree.

**Status in tree:** `BijectiveAnalyticToBiholomorphism.lean` exists.
**Audit needed.**

**Realistic Lean cost:** Likely already mostly in tree; ~500 LOC to
finish.

### T3. `ℂP¹ ≃ₜ S²` (= `RiemannSphere ≃ₜ StandardS2`)

**Statement (Lean):**
```
theorem riemannSphere_homeo_standardS2 :
    Nonempty (RiemannSphere ≃ₜ StandardS2)
```

**Classical content:** Stereographic projection + extending to the
one-point compactification.

**Status in tree:** Should be discharged somewhere; per the existing
2-input lemmas (`Item14ForRiemannSphereVia2InputChip.lean`) it's
required to compose. **Audit needed.**

**Realistic Lean cost:** 200–800 LOC for the explicit stereographic
projection + extension.

**Mathlib leverage:** `OnePoint` / `Compactification` machinery — likely
allows the homeomorphism as a corollary of stereographic projection
ℂ ≃ S² ∖ {∞}.

### T4. `holomorphicPrimitive_of_simplyConnected` (reverse leg, step 2)

**Statement (Lean, ideal form):**
```
theorem holomorphic_primitive_of_simply_connected
    [SimplyConnectedSpace X] [CompactSpace X] [ConnectedSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (om : HolomorphicOneForm X) :
    ∃ F : X → ℂ, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F ∧
      ∀ x : X, mfderiv 𝓘(ℂ) 𝓘(ℂ) F x = om.eval x
```

**Classical content:** Trivial monodromy on simply-connected base + Cauchy
local primitives + analytic continuation.

**Status in tree:** Substantial machinery for `pathPrimitive`,
`LoopPeriodVanishes`, `BasedSmoothLoopsBoundHypothesis`, the new
chip-D arc. The current formulation goes through
`SimplyConnected → BSLB → LoopPeriodVanishes`. But the BSLB layer is
itself unproved on general simply-connected X — it's a deferred
classical hypothesis.

**Real bottleneck:** The simply-connected case of the loop-period
vanishing is *much easier* than the general BSLB formulation —
literally: π₁(X) = 0 + ω closed ⟹ ∫_γ ω = 0 for every loop γ, by null-homotopy
+ Stokes (= integral of dω over the null-homotopy disc).

**Realistic Lean cost:** 1.5–3k LOC if attacked directly via π₁ = 0,
null-homotopy, and integrating over the homotopy. The current BSLB
route is much higher cost because it imposes *smooth* bordism — but
Whitney approximation gives smoothness for free.

**Mathlib leverage:** `fundamentalGroup`, `SimplyConnected`, Cauchy
integral; missing: Stokes for smooth 2-chains on manifolds (partial in
tree as `holomorphicStokesHypothesis_holds_unconditional`).

### T5. `holomorphicConstant_of_compact_connected` (reverse leg, step 3)

**Statement (Lean):**
```
theorem holomorphic_function_constant
    [CompactSpace X] [ConnectedSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (F : X → ℂ) (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) :
    ∃ c : ℂ, F = fun _ => c
```

**Classical content:** Maximum modulus principle on a compact connected
complex manifold.

**Status in tree:** Should be there — `MaxModulus.lean` or similar.
**Audit needed.**

**Realistic Lean cost:** ~500 LOC if MaxModulus is in tree; ~2k LOC
otherwise.

**Mathlib leverage:** `IsMaxOn.contDiffOn_isLocalMax_eq_const` style
results on ℂ — needs lifting through charts to a manifold-level
statement.

## Summary cost estimate

| Theorem | Lean LOC (realistic) |
|---|---|
| T1 — `hSP_of_genusZero` (Riemann–Roch g=0) | 2,000–5,000 |
| T2 — `degreeOneHolomorphic_isBiholomorphism` | 500–1,500 (mostly in tree) |
| T3 — `riemannSphere_homeo_standardS2` | 200–800 |
| T4 — `holomorphic_primitive_of_simply_connected` | 1,500–3,000 |
| T5 — `holomorphic_function_constant` | 500–2,000 |
| Item-14 final glue file | 200–500 |
| **Total** | **~5k–13k LOC** |

For comparison, the "named hypothesis + 2-input reformulation" approach
has consumed ~50k LOC across multiple sessions and **closes zero `sorry`
in `Basic.lean`**.

## Audit results (2026-05-23, same session)

| T# | Status | File |
|---|---|---|
| T2 | RS-conditional; need arbitrary-X audit | [Item14FinalComposition.lean:66](JacobianChallenge/Topology/Item14FinalComposition.lean) — `degreeOneIsBiholomorphic_RS_of_conditionals` (RS, conditional) |
| T3 | **CLOSED on RS unconditionally** | [Manifold/RiemannSphere.lean:533](JacobianChallenge/Manifold/RiemannSphere.lean) — `RiemannSphere.toSphereHomeo` via mathlib's `onePointEquivSphereOfFinrankEq` (zero new infrastructure, sorry-free) |
| T5 | **CLOSED on arbitrary X unconditionally** | [Topology/HolomorphicLocallyConstantDischarge.lean:137](JacobianChallenge/Topology/HolomorphicLocallyConstantDischarge.lean) — `liouvilleOnCompactConnected_holds`, sorry-free; based on `holomorphicLocallyConstant_holds` via global max + max-modulus principle |
| T1 | **Reduced to ONE named hypothesis** | [Topology/HolomorphicLocallyConstantDischarge.lean:144](JacobianChallenge/Topology/HolomorphicLocallyConstantDischarge.lean) — `riemannRochGenusZero_from_existsBoundedByDeltaP` reduces RR-g0 to `ExistsNonConstantBoundedByDeltaP_GenusZero X` (the actual classical content) |
| T4 | **Open arc** | The chain `SimplyConnected → BSLB → LoopPeriodVanishes → holomorphic primitive` exists structurally but `BSLB` on arbitrary simply-connected X is open classical content. The shorter classical proof (π₁ = 0 + null-homotopy + Stokes on disc) is NOT in tree. |

**Updated cost estimate after audit:** the gap is much narrower than the
initial 5–13k LOC top-down estimate.

| Theorem | Lean LOC remaining | What's missing |
|---|---|---|
| T1 | 1,500–4,000 | Discharge `ExistsNonConstantBoundedByDeltaP_GenusZero` on arbitrary X — = the Riemann–Roch dim bound at g=0. Pre-reqs partly in tree (`Divisor/`). |
| T2 | 200–800 | Generalize `degreeOneIsBiholomorphic` from RS to arbitrary compact connected RS. |
| T3 | 0 | Done. |
| T4 | 1,500–3,000 | Either (a) discharge `BSLB` on simply-connected X classically, OR (b) write the direct π₁-based proof and bypass BSLB entirely. |
| T5 | 0 | Done. |
| Glue file (`Basic.lean` sorry removal) | 200–500 | Once T1+T2+T4 land, compose into the universal `genus_eq_zero_iff_homeo`. |
| **Total remaining** | **~3.5k–8.3k LOC** | Two real classical arcs, both multi-session. |

## The actual next-session work order (anti-paraphrase, post-audit)

1. **Audit T1's `ExistsNonConstantBoundedByDeltaP_GenusZero`** —
   trace it back to the underlying Riemann–Roch dim bound; check how
   much divisor/Serre-duality machinery is already in tree (`Divisor/`,
   `LinearSystemAtInftyRSDischarge.lean`, etc.).
2. **Audit T4** — confirm the direct π₁-based proof is shorter than
   the BSLB approach. If yes, abandon the BSLB structural arc and
   write the direct proof.
3. **Pick T1 or T4 and commit to one 2–3k LOC working file.** Multi-session.
   No new chips, no named hypotheses, no paraphrase reformulations.
4. After one of T1/T4 lands, generalize T2 (~500 LOC), then write the
   glue file removing `Basic.lean:73`'s `sorry`.

## STOP writing chips that:

- introduce a new named hypothesis (any new `class`, `structure`,
  `def Prop`),
- reduce one named-hypothesis count to another (any `_from_N_inputs`
  reformulation),
- validate via a parallel route on RS / T_L / Subsingleton,
- ship a per-X instance (RS / T_L) that doesn't compose with same-session
  general-X discharge.

The chip-prompt-preamble at [`tools/chip-prompt-preamble.md`](tools/chip-prompt-preamble.md)
now has 7 hard anti-paraphrase gates. Any future chip on item 14
that fails them is REJECTED.

## Memory link

[[feedback-lean-paraphrase-antipattern]] in NoetherSolve memory codifies
the lesson learned from this audit. Apply to other Lean-proof repos
(sqg-lean-proofs, ns-lean-proofs) as well.
