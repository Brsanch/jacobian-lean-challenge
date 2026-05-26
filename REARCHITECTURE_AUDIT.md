# Re-architecture audit — alternatives to `DBarSolvabilityAtGenusZero`

**Date**: 2026-05-26.
**Context**: After `DBAR_CONSUMER_AUDIT.md` showed that abstract-`X`
discharge of `DBarSolvabilityAtGenusZero X` is multi-month / multi-
thousand-LOC work at this mathlib pin, the user asked: are there
alternative classical paths to `hSP X` (∃ a meromorphic function on
`X` with a simple pole at exactly one point) that **avoid the
`H¹(X, O) = 0` route entirely**?

## What the current chain actually requires

The repo has already factored Item 14's forward leg as:

```
genus X = 0 + hSP X + (FiniteDim of HolomorphicOneForm X, unconditional)
    ↓ (genus0ImpliesS2_from_existsSimplePoleGerm_and_finiteDim)
Genus0ImpliesS2 X
    ↓ (combined with unconditional reverse leg)
Item 14 biconditional
```

The **only** open input is `hSP X`. The DBarSolvability route is
**one specific way** to discharge `hSP X` (via Forster §16.9
cutoff). Re-architecting means: find a different discharge of
`hSP X`.

`hSP X` says: there exists `p : X` and a meromorphic
`f : MMer X` with `mmeromorphicOrderAt 𝓘(ℂ, ℂ) f p = -1` and
`mmeromorphicOrderAt 𝓘(ℂ, ℂ) f x ≥ 0` for all `x ≠ p`.

Note: `genus X = 0` here is the **geometric genus**
`dim_ℂ H⁰(X, Ω)` (see `Basic.lean:62`), NOT the topological genus.

## Classical proofs of `hSP X` on compact genus-0 RS

### Path A — `H¹(X, O) = 0` + Forster §16.9 cutoff (current route)

Already analyzed in `DBAR_CONSUMER_AUDIT.md`. Multi-month at this
pin (uniformization or Hodge or equivalent).

### Path B — Riemann-Roch / divisor cohomology

**Statement**: For any divisor `D` on compact RS `X`,
`dim H⁰(X, O(D)) - dim H¹(X, O(D)) = deg D + 1 - g`.

For `g = 0` and `D = [p]` (degree 1), `dim H⁰(O(p)) ≥ deg + 1 - g
= 2`. So there exists a non-constant meromorphic function with at
most a simple pole at `p`. Its pole order at `p` is exactly 1
(degree-counting: a constant + something of order ≥ 0 elsewhere
must use the pole). Hence `hSP X`.

**Required infrastructure**:

* `H¹(X, O(D))` — sheaf cohomology with twists, not at this pin.
* Riemann-Roch itself, not at this pin.
* `H¹(X, O(D)) = H⁰(X, K - D)*` (Serre duality), not at this pin.

**Cost estimate**: comparable to or higher than DBarSolvability
(Serre duality uses Hodge or sheaf-cohomology of compact complex
manifolds; Riemann-Roch builds on top). Multi-month / multi-
thousand LOC.

### Path C — Green's function / harmonic theory

**Statement**: For compact RS `X` and any `p ∈ X`, there exists a
**Green's function** `G_p : X → ℝ` harmonic on `X \ {p}` with
logarithmic singularity at `p`, i.e., `G_p(z) ~ log|z - p|` in any
chart near `p`. Then `dG_p` is a closed 1-form, its `(1, 0)`-part
`∂ G_p` is a meromorphic 1-form with a simple pole at `p`, and
integrating gives a meromorphic function with simple pole at `p`.

**Required infrastructure**:

* `Laplacian` on a Riemannian / Kähler manifold, in particular the
  conformal Laplacian on a compact RS.
* `L²` Sobolev spaces + weak derivatives.
* Hodge / Dirichlet variational principle for the Green's function.

**At this mathlib pin**: `Laplacian` is mostly missing for general
manifolds; L² Sobolev infrastructure thin. Cost comparable to
DBarSolvability.

### Path D — Direct via uniformization

**Statement**: `X compact + connected + genus 0 → X ≃_holomorphic ℂℙ¹`.

Then the standard coord `z : ℂℙ¹ → ℂ ∪ {∞}` is a meromorphic
function with a simple pole at `∞`. Pull back via the
biholomorphism to get `hSP X`.

**Required infrastructure**: uniformization theorem for genus-0
compact RS. Multi-year mathlib project.

### Path E — Algebraic-topology + Riemann-Hurwitz

**Statement attempted**: from genus 0 + compact connected complex
1-manifold, deduce `X ≃_top S²` directly via Euler characteristic
+ surface classification, then transport the standard meromorphic
function from `S²` via the topological homeomorphism.

**Problem**: this requires (i) "geometric genus = topological
genus" (an Hodge-theoretic identity), and (ii) transport of a
meromorphic function across a HOMEOmorphism, which does not
preserve the complex structure. (E) does not actually work without
something like the Newlander-Nirenberg / uniformization.

### Path F — Use the Buzzard challenge's freebie inputs

**Statement**: the Buzzard challenge gist (`Basic.lean`) ships
specific signatures + named hypotheses. Are there ALREADY-DEFINED
hypotheses elsewhere in the challenge gist that, combined with
`genus X = 0`, give `hSP X`?

Audit: searched the repo for non-trivial Props that could substitute.
Found: `RiemannSphereGenus`, `S2ImpliesGenus0`, `HolomorphicOneFormFiniteDim`,
`ChartAtConstantOnSource`. None of these directly imply `hSP X`
without going through `H¹(X, O) = 0` or one of paths A-E.

## Composite finding

**No known classical proof of `hSP X` on abstract compact genus-0 RS
avoids the entire `H¹(X, O) = 0` machinery.** Paths A-D all require
infrastructure comparable to or harder than DBarSolvability. Paths E
and F do not work.

The classical literature on the existence of meromorphic functions
on compact RS uniformly factors through one of:

1. Riemann-Roch (Path B).
2. Hodge / harmonic theory (Path C).
3. Uniformization (Path D).
4. `H¹(X, O) = 0` directly (Path A).

These are mutually convertible via standard equivalences (Dolbeault,
Serre duality, Hodge), so the difficulty is roughly invariant.

## What "re-architecting" can realistically mean

Three weaker options that DO have concrete content:

### Option R1 — Discharge `hSP X` by a "global" named hypothesis

Replace `DBarSolvabilityAtGenusZero X` (which goes through Forster
cutoff to `hSP X`) with a NEW named hypothesis whose only role is
to imply `hSP X` directly:

```lean
def RiemannExistenceTheoremGenusZero : Prop :=
  JacobianChallenge.genus X = 0 → hSP X
```

This **renames** the obligation without resolving it. Item 14
closure remains conditional on a named classical hypothesis;
just the label changes. May be cleaner for the challenge submission
since the named hypothesis matches a textbook statement directly.

**Cost**: ~50-100 LOC (just the renaming + a small adapter).

**Pro**: makes the challenge's irreducible content explicit.
**Con**: doesn't close anything new; just relabels the wall.

### Option R2 — Specialize Item 14 to RiemannSphere

Re-formulate Item 14 only for the concrete `RiemannSphere`. The
biconditional becomes `genus RiemannSphere = 0 ↔ Nonempty
(RiemannSphere ≃ₜ StandardS2)`. Reverse direction unconditional;
forward direction: `dim H⁰(RS, Ω) = 0 → RS ≃ₜ S²`. For the concrete
RS construction, `dim H⁰(RS, Ω) = 0` is computable (and presumably
already proven somewhere in the repo's `RiemannSphereGenus.lean`),
and `RS ≃ₜ S²` is a structural property.

**Cost**: scope-narrowing; abandons the universal-`X` content of
Item 14. The challenge response would be "Item 14 closed for the
concrete X = RiemannSphere".

**Pro**: actually closes something concrete with no named hypothesis.
**Con**: not the universal statement Buzzard's challenge asks for.

### Option R3 — Document the wall + ship Phase A

Accept that abstract-`X` Item 14 closure is permanently bottlenecked
at this mathlib pin. Document the four-path equivalence in
`OPEN.md` clearly. Ship Phase A (already landed) as standalone
analytic infrastructure (`H¹(Δ, O) = 0` once Phase B lands). Don't
make further claims about Item 14 progress.

**Cost**: 0 LOC beyond documentation.

**Pro**: most honest.
**Con**: no new closure.

## Recommendation

Re-architecting in the sense the user might have hoped for — a
mathematically lighter alternative to DBarSolvability that closes
the same conclusion — **does not exist**. The classical literature
uniformly factors through equivalently-hard machinery.

The honest options are R1 (relabel the wall), R2 (specialize to
concrete X), or R3 (document the wall).

If the project intent is "make the challenge response as honest as
possible about what's open at this mathlib pin", R3 + R1 in
combination is the best. R2 is a real closure but at the cost of
universal-`X` scope.
