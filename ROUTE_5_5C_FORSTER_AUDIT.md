# Forster Ch.12-14 / Griffiths-Harris audit before Sub-chip 5.5c-I-c

**Date**: 2026-05-26.
**Context**: Before committing 200-350 LOC to Sub-chip 5.5c-I-c
(partition sum at the OmegaForm level), audit whether the OmegaForm
Option-b route can actually discharge `DBarSolvabilityAtGenusZero X`
on abstract `[ChartedSpace ℂ X]`.

## The named hypothesis (verbatim)

```lean
def DBarSolvabilityAtGenusZero : Prop :=
  JacobianChallenge.genus X = 0 →
  ∀ α : X → ℂ,
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α →
    ∃ u : X → ℂ,
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u ∧
      ∀ x : X, partialZBarManifold u x = α x
```

`partialZBarManifold f x` is defined
([`PartialZBarManifold.lean:72`](JacobianChallenge/Manifold/PartialZBarManifold.lean#L72))
via the **chart at the evaluation point** `x`:

```
partialZBarManifold f x := partialZBar (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
                                       ((extChartAt 𝓘(ℂ, ℂ) x) x)
```

The file docstring (lines 23-30) explicitly notes this operator is
**not** a function on X — it is the canonical-chart trivialization of
a section of the (0,1)-form bundle. So `partialZBarManifold u x = α x`
identifies the canonical chart-x view of `∂̄u` with `α(x)` *at each
point in its own chart*.

## What the partition sum actually computes

Build `v_i := (χ_i : ℂ) · pompeiuKernel (chartPullbackZero i.val (ρ_i α)) ∘ chart_{i.val}`
(Sub-chip 5.4b) and `u := Σ_i v_i` (assembly layer).

For any `y : X`:

```
partialZBarManifold u y = Σ_i partialZBarManifold v_i y                       (linearity)
                        = Σ_i partialZBarManifoldAtChart i.val v_i y
                            / conj(τ_{i.val→y}((chart_{i.val}) y))             (5.5a transfer)
```

Per-`i` cases:
* `y ∈ support(ρ_i)`: `partialZBarManifoldAtChart i.val v_i y = (ρ_i α)(y)`
  (Sub-chip 5.5b), so contribution is
  `(ρ_i α)(y) / conj(τ_{i.val→y}((chart_{i.val}) y))`.
* `y ∉ tsupport(χ_i)`: `partialZBarManifold v_i y = 0`
  (assembly "trivial vanishing case").
* `y ∈ tsupport(χ_i) \ support(ρ_i)` (the **outer ring** of the cutoff):
  generally non-zero. This is the cutoff-leakage error term.

Summing:

```
partialZBarManifold u y
  = Σ_{i: y ∈ supp ρ_i} (ρ_i α)(y) / conj(τ_{i.val→y}((chart_{i.val}) y))
  + Σ_i [outer-ring-of-χ_i contribution at y]
```

For this to equal `α(y)`:

1. The outer-ring error must vanish or be cancelled.
2. The transition factors `conj(τ_{i.val→y})` must combine to 1 under
   the partition weights — i.e.
   `Σ_i ρ_i(y) / conj(τ_{i.val→y}((chart_{i.val}) y)) = 1`.

Neither holds in general for abstract `[ChartedSpace ℂ X]`. (2) is a
specific identity on chart-transition derivatives that has no
elementary partition-of-unity proof; it is essentially equivalent to
asking the cover to be "compatible" in a sense that pure smooth
partition-of-unity does not provide.

## Classical comparison

### Forster, *Lectures on Riemann Surfaces*, §12-14

* §12-13: differential forms are sections of the (1,0) / (0,1)
  cotangent bundles. The function-to-form identification is *implicit*
  via choice of a frame `dz̄`, which is chart-dependent and globalizes
  only as a section.
* §14 ("Solution of `∂̄u = ω` in a disk and on a compact Riemann
  surface"): for a compact RS,
  * Local solutions on disks (or annuli) come from the **Pompeiu
    integral** (already proven, Chip 3c-F-4 + Chip 4).
  * Globalization is via **Behnke-Stein spreading**: solve on a
    nested family `K_1 ⊂ K_2 ⊂ ...`, correct each step by a
    holomorphic adjustment on a slightly smaller domain, sum into a
    geometric series that converges uniformly on compacts.
  * Partition-of-unity does **not** appear in Forster's argument. The
    transition-factor obstruction observed above is exactly why.

### Griffiths-Harris, *Principles of Algebraic Geometry*, §0.4-0.5

Same picture: (0,1)-forms are sections, Dolbeault's theorem `H^q(X,
Ω^p) ≅ H^{p,q}_{∂̄}(X)` is proven via fine resolutions, and the
function-level identification only appears in the chart-by-chart
formula. The Hodge theorem (their §0.6) is invoked for the global
solvability statement.

### Consensus

The cleanest classical paths to `H^1(X, O) = 0` for a compact genus-0
RS are:

(α) **Hodge theory / L²-∂̄**: build u via Green's function of the
    Laplacian. Not feasible at this mathlib pin (no L² Hodge).
(β) **Behnke-Stein iteration**: classical, elementary, but heavy
    (~800-1200 LOC, geometric-series convergence on nested compacts).
(γ) **Uniformization → single chart**: X ≃ ℂℙ¹ ≃ ℂ ∪ {∞}; cover the
    finite part by ONE chart, solve Pompeiu on ℂ globally, extend
    across ∞. Requires uniformization (big theorem) OR specializing
    to a concrete X (e.g. RiemannSphere with its 2-chart atlas).

## Where this leaves Sub-chip 5.5c-I-c

The partition-of-unity-at-the-OmegaForm-level approach — as currently
sketched — is **not classical** and does **not** close the loop on
abstract `[ChartedSpace ℂ X]`. The transition-factor obstruction is
real and cannot be removed by adding more OmegaForm structure.

Concrete options going forward:

1. **Specialize discharge to a concrete X** (e.g. `RiemannSphere`).
   The 2-chart atlas has `chartAt ℂ y` locally constant on each
   chart's interior, and Path (γ) is direct: lift α to ℂ via the
   finite chart, apply Pompeiu globally, smoothly extend at ∞ using
   compact support of `α ∘ chart₀.symm` outside a compact set.
   Loses abstract X generality but discharges
   `DBarSolvabilityAtGenusZero RiemannSphere` directly, ~600-1000
   LOC, no Behnke-Stein iteration.

2. **Build Behnke-Stein iteration (Route III)**. Heaviest path.
   ~800-1200 LOC of analytic infrastructure (Schauder-type estimates,
   nested compacts, geometric-series convergence). Works on abstract
   compact genus-0 RS without uniformization. The existing Pompeiu
   infrastructure (Chips 1-4) is reusable for the disk-level solver.

3. **Reformulate `DBarSolvabilityAtGenusZero`** to a statement the
   partition-sum genuinely satisfies (e.g. asserting equality of
   OmegaForm sections, not functions). Requires auditing all
   downstream consumers (`ForsterCutoffPoleConstruction`,
   `ExistsSimplePoleGermFromGenusZeroDBarSolvability`,
   `Item14FromHSPOnly`) to verify they can consume the weaker form.
   Risk: the function-level equality is what those consumers use for
   the §16.9 simple-pole construction; a section-level equality may
   not directly substitute.

4. **Drop Sub-chip 5.5c entirely and abandon Route I**. The 5.5c-I
   sub-chips already landed (5.5c-I-a, -b def+cocycle, -b-smoothness,
   -b-final = ~1140 LOC of OmegaForm record + ofChartLocalFunction
   constructor) are not wasted *if* a future bundle-based route uses
   them, but they do not close `DBarSolvabilityAtGenusZero` on their
   own.

## Recommendation

Route I (Option b) as previously framed cannot close
`DBarSolvabilityAtGenusZero` on abstract X. The honest options are
(1) specialize discharge to `RiemannSphere`, or (2) Behnke-Stein
iteration.

(1) is shorter and reuses Chips 1-4 most directly.
(2) is more general (any abstract genus-0 X) but heavier.

The user decision is which trade-off matches the project's intent:
"discharge the named hypothesis for any X with genus 0" (→ 2 or 3)
or "discharge for the concrete X we plug into Item 14's headline
statement" (→ 1).
