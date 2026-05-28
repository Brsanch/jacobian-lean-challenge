# Item 14 — wall documentation

## Status: shipped conditional on `ExistsMeroSimplePole_GenusZero X`

Item 14 (`genus_eq_zero_iff_homeo`, `Basic.lean` line 105) is shipped
**conditional** on the named classical hypothesis
`ExistsMeroSimplePole_GenusZero X` (= Forster Theorem 16.9: a compact
connected genus-0 Riemann surface admits a non-constant meromorphic
function with a single simple pole). All structural reductions on both
legs are unconditional in tree and compile-verified; the remaining gap
is the classical theorem itself, which requires multi-thousand-LOC
mathlib-grade infrastructure that does not exist at this pin or any
publicly-visible mathlib HEAD.

On the concrete `X = RiemannSphere`, Item 14 is **unconditionally
closed** via
[`Topology/Item14ForRiemannSphere.lean`](JacobianChallenge/Topology/Item14ForRiemannSphere.lean).

## Equivalent textbook names of the same wall

The Item 14 frontier reduces (via in-tree transport) to any one of
these textbook-equivalent classical statements; closing any closes the
others.

* `ExistsMeroSimplePole_GenusZero X` — Forster Thm 16.9 (canonical name,
  defined at
  [`Topology/RiemannRochGenusZeroDecomposition.lean:101`](JacobianChallenge/Topology/RiemannRochGenusZeroDecomposition.lean#L101))
* `ExistsSimplePoleGermAtSomePoint X` — the germ form, `hSP X`
* `DBarSolvabilityAtGenusZero X` + `ChartAtConstantOnSource` — the
  Dolbeault form, `H¹(X, 𝒪) = 0` at genus 0
* `RR_DimGE2_GenusZero X` — the Riemann–Roch dimension inequality at
  genus 0
* `Nonempty (HolomorphicEquiv X RiemannSphere)` at `genus X = 0` —
  uniformization

These are textbook-equivalent (Dolbeault ↔ Serre duality ↔
Riemann–Roch ↔ uniformization).

## Closure chain (file:line)

```
ExistsMeroSimplePole_GenusZero X   (Forster Thm 16.9, OPEN)
  → RiemannRochGenusZero X         Topology/RiemannRochGenusZeroSingleInput.lean:54
  → UniformizationToRiemannSphere X (genus = 0 branch)
                                   Topology/UniformizationFromRiemannRoch.lean
  + S²-branch hypothesis            (OPEN; equivalent classical content)
  → genus_eq_zero_iff_homeo         Topology/Item14FromSingleUniformization.lean:168
                                    + Topology/Item14ClassTransport.lean
                                    + Topology/Item14ForRiemannSphere.lean (closes RS case)
```

## In-tree unconditional discharges (compile-verified)

| Fact | File:line |
|---|---|
| `surjective_of_NonConstant_Analytic_Manifold_holds` | [`Manifold/SurjectiveOfNonConstantDischarge.lean:391`](JacobianChallenge/Manifold/SurjectiveOfNonConstantDischarge.lean#L391) |
| `nearbyRegularWitnessHypothesis_holds_unconditional` | [`Manifold/NearbyRegularWitnessHolds.lean:32`](JacobianChallenge/Manifold/NearbyRegularWitnessHolds.lean#L32) |
| `ramificationSumEqualsDegree_holds_unconditional` | [`Manifold/RamificationSumEqualsDegreeUnconditional.lean:471`](JacobianChallenge/Manifold/RamificationSumEqualsDegreeUnconditional.lean#L471) |
| `bijectiveAnalyticIsBiholomorphism_holds` | [`Manifold/BijectiveAnalyticToBiholomorphismDischarge.lean`](JacobianChallenge/Manifold/BijectiveAnalyticToBiholomorphismDischarge.lean) |
| `DegreeOneIsBiholomorphic_RS X` (composed) | [`Topology/Item14FinalComposition.lean:66`](JacobianChallenge/Topology/Item14FinalComposition.lean#L66) |
| `existsSimplePoleGermAtSomePoint_of_holomorphicEquiv_RS` | [`Topology/ExistsSimplePoleGermFromHolomorphicEquivRS.lean:172`](JacobianChallenge/Topology/ExistsSimplePoleGermFromHolomorphicEquivRS.lean#L172) |
| Reverse leg `S2ImpliesGenus0 X` (étale-primitives arc) | [`Topology/S2ImpliesGenus0FromEtalePrimitives.lean`](JacobianChallenge/Topology/S2ImpliesGenus0FromEtalePrimitives.lean) |
| Item 14 on `X = RiemannSphere` | [`Topology/Item14ForRiemannSphere.lean`](JacobianChallenge/Topology/Item14ForRiemannSphere.lean) |
| 1-input composition of Item 14 from `hSP` | [`Topology/Item14FromHSPOnly.lean`](JacobianChallenge/Topology/Item14FromHSPOnly.lean) |

Verified by compile: `LEAN_NUM_THREADS=1 lake env lean
JacobianChallenge/Topology/HTopFromSubsingleton.lean` exits 0,
confirming the three `*_holds_unconditional` discharges compose into
unconditional `DegreeOneIsBiholomorphic_RS X`.

## Closure-cost audit (2026-05-26)

Four parallel decomposition agents using a per-substantial-theorem
calibration of **~6,500 LOC** (measured from the in-tree Pompeiu
kernel chain: 6,587 LOC across 250 declarations producing one
substantial classical theorem, the Cauchy–Pompeiu identity on ℂ).

Three classical arcs to close `ExistsMeroSimplePole_GenusZero X` on
abstract X:

| Arc | In-tree scaffolding (reusable) | Remaining for closure | Notes |
|---|---|---|---|
| **1. Riemann–Roch + Serre duality** (Forster Ch. III §15–17) | ~16,500 LOC | **~28,000–35,000 LOC** | Build coherent analytic sheaves, Cartan–Serre finiteness, Leray on Stein covers, RR index formula, Serre duality. Each is a substantial classical sub-project. Mathlib has abstract Grothendieck-topos sheaf cohomology (~334 LOC) but no analytic-RS instantiation. |
| **2. Behnke–Stein on disk + Cousin I** (McMullen Berkeley 241/96 §7) | ~7,560 LOC (Pompeiu Phase A + bridges) | **~10,000 LOC (RS-only) — does NOT advance Item 14** | Phase B (Dolbeault on Δ) + Phase C (Cousin I / Laurent on `ℂ*`) + Phase D (RS atlas assembly) + Phase E.1 (specialize). Discharges the named hypothesis for the concrete `X = RiemannSphere` only. **But Item 14 on `RiemannSphere` is already unconditionally closed** (`Topology/Item14ForRiemannSphere.lean`), so this ~10k buys nothing for the *open* (abstract-X) statement. The "reduce abstract X to RS" step is **uniformization**, which is itself one of the five equivalent names of the wall (circular — it is not a cheaper sub-step). **The real floor for abstract-X Item 14 is Arc 1 (~28–35k LOC), not this ~10k.** |
| **3. Dirichlet's principle / Green's function** (Forster Ch. 27–28) | ~3,000–5,000 LOC | **~26,000–46,000 LOC** | Build Riemannian metric + Laplace–Beltrami on a charted 2-manifold, full variational `H¹(M)` with Rellich–Kondrachov, direct method of CoV, Weyl's lemma, Green's function. Each piece is its own mathlib-grade sub-project; mathlib has none of them at pin or HEAD. |

The audits show no closure arc is chip-sized. All are multi-month
formalization commitments of classical mathlib-grade content.

### Trace verification (2026-05-28): Serre duality is the confirmed blocker

A symbol-level trace of the Pompeiu → `DBarSolvabilityAtGenusZero X`
chain confirms (not just by reasoning, but by what is and isn't in
tree) that the wall is the global vanishing `H¹(X, 𝒪) = 0`, i.e. one
direction of Serre duality:

- `DBarSolvabilityAtGenusZero X`
  (`Manifold/ExistsSimplePoleGermFromGenusZeroDBarSolvability.lean:121`)
  is **defined once, consumed once** as the hypothesis `h_dbar`
  (`Manifold/ForsterCutoffPoleConstruction.lean:1357`), and **never
  concluded by any theorem**. It is a pure named hypothesis. Its
  statement is "genus 0 → ∂̄ is globally surjective on smooth (0,1)-forms",
  which *is* `H¹(X, 𝒪) = 0` at genus 0.
- The Pompeiu arc delivers the **local** solution
  (`partialZBar_pompeiuKernel_eq_self`, axiom-free) and patches it by
  partition of unity into `globalSolutionCandidate`, proving the
  axiom-free identity
  `partialZBarManifold (globalSolutionCandidate P α χs) y = α y + outerRingLeakage P α χs y`
  (`Manifold/OuterRingLeakage.lean`).
- The error `outerRingLeakage = Σᵢ ∂̄χᵢ · Kᵢ(...)` does not vanish.
  Killing it requires solving a *second* global ∂̄-problem — exactly
  `H¹(X, 𝒪) = 0`. On non-compact/Stein surfaces this is free (classical
  Behnke–Stein); **compact is precisely where it is not**, and at genus
  0 the vanishing is Serre duality (`H¹(𝒪) ≅ H⁰(Ω¹)* = 0`).

So the Pompeiu work is complete up to — and stops exactly at — the
Serre-duality wall. No in-tree partition/cutoff construction closes the
gap (see also `Manifold/GlobalSolutionUnderChartConst.lean` and
`Manifold/OuterRingLeakage.lean` documenting the residual leakage). The
only levers are: formalize Serre duality / RR (Arc 1, multi-month), or
a mathlib pin bump once Serre duality lands upstream.

External infrastructure scan (2026-05-26): no public Lean project
formalizes Riemann surface theory, sheaf cohomology of analytic
sheaves, Riemann–Roch on compact RS, Sobolev on manifolds, or
uniformization. Joël Riou's derived-categories foundation is merged in
mathlib HEAD; Serre duality is on the mathlib roadmap but not
implemented. Pin bump from this repo's v0.3 pin (`8e3c989...`,
2026-04-15) to the v0.4 pin (`548398201a...`, 2026-05-15) saves at
most a few hundred LOC of categorical scaffolding.

## Implications for chip work

There is no chip-sized step left between the current state and Item 14
abstract-X closure. Further progress either commits to a multi-month
classical formalization arc, or documents the wall and accepts the
conditional closure framing.

Further *structural* reduction of the named hypothesis to additional
named hypotheses (paraphrase chips of the form
`*_From_NamedAtoms` / `*_via_Subsingleton`) does not move the
frontier and is not productive.

## Related canonical docs

- [`HANDOFF_C3.md`](HANDOFF_C3.md) — C3-cluster canonical (items
  5/11/12/13/17/18/21).
- [`OPEN.md`](OPEN.md) — per-item status table.
- [`REPO_AUDIT.md`](REPO_AUDIT.md) — full-repo chain-trace per sorry.
- [`HSP_AUDIT.md`](HSP_AUDIT.md) — deeper synthesis of the hSP
  sub-tree (older, but the §4 synthesis is still useful as
  background).
- [`REARCHITECTURE_AUDIT.md`](REARCHITECTURE_AUDIT.md) — the
  no-lighter-classical-alternative analysis.
