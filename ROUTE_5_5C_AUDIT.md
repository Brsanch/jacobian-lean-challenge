# Route audit for Sub-chip 5.5c

**Date:** 2026-05-26
**Branch:** `feat/item14-forward-dbar-mul`
**Decision being supported:** which of the three routes (I/II/III) outlined in
HANDOFF_ITEM14.md should Sub-chip 5.5c take.

This is a planning audit, kept in-repo per project discipline. **No code
changes in this commit.** The audit either survives subsequent work as a
historical record, or is pruned when 5.5c lands.

## Standing constraint

The named hypothesis to discharge is

```
DBarSolvabilityAtGenusZero X
```

for an **arbitrary** compact connected complex 1-manifold `X` of genus 0
— specifically as the statement "for any C^∞ compactly supported
`α : X → ℂ`, there exists smooth `u : X → ℂ` with `partialZBarManifold u y
= α y` for all `y`". The chip-flow upstream is `item-14 → hSP X →
DBarSolvabilityAtGenusZero X + ChartAtConstantOnSource p` (Chip 2c-Final,
`Manifold/ForsterCutoffPoleConstruction.lean`).

This is not a chip about a specific X (e.g. `RiemannSphere`, `ℂ/L` torus);
it is about the universal statement on every X satisfying the genus-0
hypothesis. Discharging it on a single concrete X does not close the chain.

## Why 5.5a + 5.5b alone do not extend to a partition-sum proof

Sub-chip 5.5b ships, on `support (P.rhoC i)`,

```
partialZBarManifoldAtChart i.val (localPompeiuSolutionGlobal P i α χ_i) y
  = (P.rhoC i * α) y.
```

For the global candidate `u := Σ_j v_j`, the chart-anchored sum
distributes (Sub-chip 5.5a, `partialZBarManifoldAtChart_finset_sum`):

```
partialZBarManifoldAtChart i.val u y
  = Σ_j partialZBarManifoldAtChart i.val v_j y.
```

For `j = i` with `y ∈ support (P.rhoC i)`, the summand is `(ρ_i α)(y)`
by 5.5b. For `j ≠ i`, the v_j summand was built via chart-`x_j`; the
chart-`x_i` view requires a Leibniz expansion of `v_j ∘ chart_xi.symm`,
where one factor is `pompeiuKernel(...) ∘ (chart_xj ∘ chart_xi.symm)`.
Applying `partialZBar_comp_of_differentiableAt` to this composition
(chart transitions are ℂ-holomorphic, supplying ℂ-differentiability of
the inner factor) gives a factor

```
conj(τ_{j,i}(y)) := conj(deriv (chart_xj ∘ chart_xi.symm) ((chart_xi) y)).
```

Multiplying by partition-of-unity:

```
partialZBarManifoldAtChart i.val u y
  = Σ_j ρ_j(y) · α(y) · conj(τ_{j,i}(y)) + cutoff_annulus_errors.
```

For this to equal `α(y) · conj(τ_i(y))` (the RHS that the transfer
lemma `partialZBarManifoldAtChart_eq_manifold_mul_transition` then
converts into `partialZBarManifold u y = α(y)`), one would need

```
Σ_j ρ_j(y) · τ_{j,i}(y) = τ_i(y),
```

where `τ_i(y) := deriv(chart_y ∘ chart_xi.symm)((chartAt ℂ i.val) y)`.
This is **not generally true**: the LHS is a partition-weighted average
of derivatives of *chart-x_j ∘ chart-x_i.symm* transitions; the RHS is
a single derivative of *chart-y ∘ chart-x_i.symm*. The chart_y on the
RHS is the canonical chart at `y`, not a partition-weighted average of
construction charts.

Path A relocates the τ from "chart-y per-i in the original equation"
to "chart-anchored per-(j,i) in the partition sum". The relocation
does not produce a cancellation; the same geometric obstruction
re-emerges.

The structural cause is the function-vs-(0,1)-form ambiguity for α
discussed in `PartialZBarManifold.lean`'s docstring (`partialZBarManifold`
is explicitly **not** chart-invariant as a function; it is a (0,1)-form
coefficient in a chosen chart). 5.5b is genuinely useful (factor-free
per-summand in its OWN construction chart), but cross-summand
assembly across distinct construction charts inherits the (0,1)-form
transformation rule.

## Mathlib audit (2026-05-26 pin)

### What's in mathlib

* `Mathlib/Geometry/Manifold/PartitionOfUnity.lean` — smooth partitions of
  unity subordinate to open covers. **Used by Sub-chip 5.2.**
* `Mathlib/Geometry/Manifold/Complex.lean` — `MDifferentiable.isLocallyConstant`
  + `exists_eq_const_of_compactSpace` for holomorphic functions on
  compact complex manifolds. Maximum-modulus / Liouville-flavored. **Does
  NOT contain Dolbeault, sheaf cohomology, or Behnke-Stein.**
* `Mathlib/Topology/Compactification/OnePoint/Sphere.lean` +
  `OnePoint/ProjectiveLine.lean` — `OnePoint ℂ ≃ ℙ ℂ (ℂ × ℂ)` as a
  set-theoretic equivalence and topology. **No complex manifold
  structure** on `OnePoint ℂ` here; the repo's `Manifold/RiemannSphere.lean`
  supplies the two-chart `ChartedSpace ℂ` instance.
* `Mathlib/Geometry/Manifold/Sheaf/{Basic,LocallyRingedSpace,Smooth}.lean`
  — structure sheaf of smooth functions, locally ringed space structure
  on a smooth manifold. **No sheaf cohomology** computations.
* `Mathlib/Geometry/Manifold/VectorBundle/` — vector bundles on smooth
  manifolds; covariant derivatives. **No holomorphic line/vector
  bundles**, no `(0,1)`-form bundle.

### What's not in mathlib

A series of `find .lake/packages/mathlib/Mathlib -iname '*Dolbeault*' -o
-iname '*BehnkeStein*' -o -iname '*Uniformiz*'` returns zero matches
relevant to compact-Riemann-surface analysis. Concretely missing:

* **Dolbeault cohomology.** No `H^{0,1}_{\bar\partial}`, no Dolbeault
  isomorphism, no Hodge decomposition on RS.
* **Sheaf cohomology of the structure sheaf.** Mathlib has the
  smooth-function sheaf as locally-ringed-space data, but neither the
  analytic structure sheaf `𝒪_X` nor its `H^1`. The fact `H^1(ℂℙ^1, 𝒪) = 0`
  (which IS what `DBarSolvabilityAtGenusZero X` amounts to for X = ℂℙ^1)
  is not derivable from the current mathlib content.
* **Behnke-Stein theorem.** "Every non-compact Riemann surface is Stein"
  (and hence has `H^1(𝒪) = 0`) is not in mathlib in any form. Its
  Forster Ch. 14 proof (which is what we need for `DBarSolvabilityAtGenusZero`
  on arbitrary genus-0 compact RS via uniformization) goes through
  spreading + geometric convergence — substantial analytic content.
* **Riemann uniformization theorem.** "Every simply-connected RS is
  biholomorphic to ℂ, ℂℙ^1, or 𝔻." Not in mathlib. The compact-genus-0
  case (X ≃ ℂℙ^1) is not stated or proved in mathlib.

### What's in mathlib that we CAN use

* `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` —
  the DCT, used heavily in the Pompeiu kernel chips.
* `analyticAt_chart_transition_of_isManifold` — chart transitions are
  ℂ-analytic on a holomorphic atlas. Used by Sub-chip 5.4c-final.
* `SmoothPartitionOfUnity.exists_isSubordinate` — used by Sub-chip 5.2.
* `Filter.EventuallyEq.fderiv_eq` — germ-dependence of `fderiv`. Used
  throughout the partialZBar / partialZBarManifold germ arguments.
* `ContDiff` / `ContMDiff` interaction with chart pullback. Used by
  Sub-chips 5.3b, 5.4b.

None of these provide a shortcut around the (0,1)-form bookkeeping or
the Behnke-Stein / uniformization step.

## In-repo audit

### What this repo already has

* `Manifold/RiemannSphere.lean` — `RiemannSphere := OnePoint ℂ` with an
  explicit two-chart atlas, `ChartedSpace ℂ RiemannSphere` instance,
  `CompactSpace`, `T2Space`, `ConnectedSpace`. Plus a `Manifold/`
  network of subsidiary files: `RiemannSphereChartNHolomorphy.lean`,
  `RiemannSphereChartSCoeffOverlap.lean`,
  `RiemannSphereChartSymmSmooth.lean`,
  `RiemannSphereLiouvilleFromSouthChart.lean`,
  `RiemannSphereMobius.lean`, `RiemannSphereAntipodeSmooth.lean`,
  etc. (~ 12 files). This is enough to talk about `X = RiemannSphere`
  as a concrete object and to manipulate atlas / chart-pullback data.
* `HolomorphicEquiv` API: `Manifold/HolomorphicEquivConstructor.lean`,
  `HolomorphicEquivTopologyTransport.lean`,
  `HolomorphicEquivSubsingletonTransfer.lean`,
  `HolomorphicOneFormPullbackAPI.lean`, etc. — manipulating
  holomorphic equivalences between complex 1-manifolds. Designed to
  transport theorems X ≃ Y from one side to the other.
* `Topology/RRDimGE2FromUniformizationAndFiniteDim.lean` — explicit
  consumer of `genus X = 0 → Nonempty (HolomorphicEquiv X RiemannSphere)`
  as a hypothesis (the "uniformization-style" axiom). Documents that
  the repo has historically treated uniformization as a named input,
  not something proved.
* `Manifold/RR_AUDIT.md` (memory pointer `feedback_jacobian_check_existing_discharges_first`,
  referenced 2026-05-24): the RR-direct route from `hSP X` to
  `RiemannRochGenusZero X` was ruled out specifically because every
  in-tree route to `RR-direct` consumes either `hSP X` or
  `Nonempty (HolomorphicEquiv X RS)`. Uniformization-as-axiom is a
  known dead end at this gate. The Pompeiu arc was selected precisely
  because it avoids this.

### What this repo does NOT have

* No Behnke-Stein theorem, no Stein-manifold theory.
* No Dolbeault cohomology, no sheaf cohomology of `𝒪_X`.
* No proof of `genus X = 0 → X ≃ RiemannSphere` for arbitrary `X`.
* No `(0,1)`-form bundle / chart-coefficient theory with explicit
  transition rule encoded as bundle data.

The repo has accumulated **a lot of biholomorphism + transport
infrastructure** (the `HolomorphicEquiv*` files), but every use of it
gates on a hypothesis the chain ultimately cannot supply
unconditionally.

## Forster Ch. 14 review

Forster's *Lectures on Riemann Surfaces* §14 ("Behnke-Stein on noncompact
Riemann surfaces") proves `H^1(X, 𝒪) = 0` for noncompact X. The argument
on a compact genus-0 X (= ℂℙ^1) is handled separately in §15-§16 via
Riemann-Roch / uniformization. The §14 argument's structure (relevant
here because the "spreading-function" technique is what Path III would
formalize):

1. **Exhaustion.** Choose a sequence of relatively-compact open sets
   `K_1 ⊂ K_2 ⊂ ⋯` with `⋃ K_n = X`.
2. **Stein patch.** Each K_n can be chosen relatively-compact-with-smooth-
   boundary; on each K_n separately, `∂̄ u = α` is solvable (Cauchy
   integral / direct Pompeiu).
3. **Patching error.** Solving on K_{n+1} extends K_n's solution,
   but the extensions may not agree pointwise; the difference is a
   holomorphic function on K_n (since both sides satisfy ∂̄ = α).
4. **Runge approximation.** Approximate the holomorphic difference
   uniformly on K_n by a holomorphic function on K_{n+1} (Runge's
   theorem on RS).
5. **Convergent telescoping.** Adjust each step's correction so the
   telescoping series converges uniformly on compact subsets, giving
   a global smooth limit.

The critical analytical content is **Runge's approximation theorem on
Riemann surfaces** and the convergent series construction. Forster
doesn't use (0,1)-form bundle theory explicitly, but he DOES work
chart-locally with explicit transition factors, and the convergence
argument requires uniform estimates on Cauchy integrals that absorb
the transition factors.

Crucially: **§14 is for non-compact X.** Compact-genus-0 X requires
either (a) the §15-§16 path through uniformization, or (b) a direct
proof on ℂℙ^1 (single-chart cover of `ℂℙ^1 \ {∞}`, smooth extension
at ∞). Path (b) is essentially **Path II** in our taxonomy and **only
discharges DBarSolvabilityAtGenusZero on X = RiemannSphere**, not on
arbitrary X.

### Implication for the chip

`DBarSolvabilityAtGenusZero X` as currently named in the chain
quantifies over arbitrary X. Closing it requires either:

* uniformization (X ≃ ℂℙ^1) + Path II on ℂℙ^1, or
* a direct sheaf-theoretic argument (`H^1(𝒪_X) = 0` from genus = 0
  + compact + connected), which requires Dolbeault + Hodge theory or
  equivalent, or
* a Behnke-Stein-style argument on compact X (Forster §14 is for
  non-compact, so this would have to be adapted — probably not a
  clean re-export).

All three are multi-thousand-LOC classical projects on this mathlib
pin.

## Honest evaluation of the three routes

### Route I — (0,1)-form theory build-out

**Goal:** Encode α as a (0,1)-form (section of a chart-coefficient
family with explicit transition rule); define `partialZBarManifold`
as a (0,1)-form-valued operator. Then the partition-of-unity
identity `Σ_j ρ_j α = α` holds as (0,1)-forms automatically.

**Required infrastructure (audited, not in mathlib at pin):**

* Definition of `(0,1)`-form on a complex 1-manifold (chart-coefficient
  family + transition rule + chart-independence proof). ~300-400 LOC.
* Functoriality of `∂̄` on this bundle, including a manifold-side
  Leibniz that handles the (0,1)-form output. ~300-400 LOC.
* Partition-of-unity as an identity on (0,1)-forms (i.e.,
  `Σ_j (ρ_j · α-as-form) = α-as-form` as forms). ~150-200 LOC.
* Pompeiu kernel re-stated as a (0,1)-form-to-function inverse with
  the chart-transformation built in (alternatively: restate Chip 4
  in the new framework). ~200-400 LOC.

**Total estimate (LOC are coarse, derived from "what's not in
mathlib that I'd have to write"):** ~1000-1500 LOC of bundle theory.

**Then the partition sum closes cleanly** under the (0,1)-form
transformation rule. Sub-chips 5.5c-e + 5.6 collapse to ~300-500 LOC
in the new framework.

**Buzzard-acceptability:** clean — this is the textbook formulation.

**Risks:** (a) the bundle-as-chart-coefficient encoding may have
typeclass / coercion friction in Lean 4 that mathlib hasn't paved
through (the `Riemannian` and `VectorBundle` directories in mathlib
are limited); (b) the rewrite of Chips 3c-F / 4 into the new framework
is non-trivial and may cascade.

### Route II — single-chart genus-0 globalization

**Goal:** Solve `∂̄ u = α` on `X \ {p_∞}` via a single-chart Pompeiu
kernel, then extend smoothly across `p_∞` using compact support of α.

**Required infrastructure:**

* Reduction `genus X = 0 → ∃ p, ChartedSpace ℂ X has a single chart
  covering X \ {p}` — this **is essentially uniformization** for
  arbitrary X. **Not in mathlib, not in repo.**
* Single-chart Pompeiu solution + smooth extension at the puncture
  (compact support of α ⇒ α vanishes near p_∞ ⇒ the chart-local
  Pompeiu solution can be extended by 0 in a neighborhood of p_∞).

**Critical observation:** the "reduction to a single chart covering
X \ {p}" is uniformization. For X = `RiemannSphere` concretely, this
is trivial (the two-chart atlas in `Manifold/RiemannSphere.lean`
already gives charts covering RS \ {∞} and RS \ {0}). But for
**arbitrary** X with `genus X = 0`, asserting the single-chart cover
**IS** asserting `X ≃ RiemannSphere`, which is uniformization.

**Estimate (assuming uniformization-as-axiom):** ~600-1000 LOC for
the single-chart Pompeiu + extension argument **plus** an unproved
named hypothesis `Nonempty (HolomorphicEquiv X RiemannSphere)` —
which the RR-audit (`RR_AUDIT.md`) ruled out as a path forward.

**Buzzard-acceptability:** **rejected** if uniformization is left
as a named hypothesis. Uniformization is multi-thousand-LOC classical
content; introducing it as a named axiom at this gate is the same
move that the RR-audit ruled out.

### Route III — Behnke-Stein-style iteration (Forster Ch. 14 adapted)

**Goal:** Use the Pompeiu + partition-of-unity construction
(5.1–5.5b), accept the τ-laden error `δ_0 = α - "u_0's ∂̄"`, prove
the error is uniformly smaller in some norm, iterate to convergence.

**Critical observation:** Forster Ch. 14 is for **non-compact** X.
The argument relies on an exhaustion of X by relatively-compact opens
and Runge approximation, neither of which carries over to compact X
without modification. The classical compact-genus-0 result goes through
Riemann-Roch / uniformization, NOT Behnke-Stein iteration. **The
"Behnke-Stein for compact X" framing in the original Sub-chip 5.5 plan
was probably overstated** — Forster does not state or prove such a
theorem.

If one tries to adapt the spreading argument to compact X anyway: the
partition-of-unity error has support in the union of cutoff annuli,
which on a compact X cannot be made arbitrarily small in measure (the
annuli are determined by the chart cover and don't shrink). The
geometric-series convergence step has no obvious analogue.

**Estimate:** unknown — would require either (a) a novel adaptation
of Forster's argument to compact X (research-level uncertainty), or
(b) using a different convergence argument from sheaf theory or
elliptic theory.

**Buzzard-acceptability:** if a novel adaptation works, clean. If not,
the route is structurally broken on compact X.

## Recommendation

After this audit, **Route I (0,1)-form theory build-out)** is the most
defensible technically:

1. It produces correct, textbook-canonical mathematics.
2. The LOC cost (~1000-1500) is large but bounded — it's a definite
   pile of bundle theory, not an open-ended classical-content build.
3. It composes cleanly with the existing Pompeiu kernel work (Chips
   1-4); the chart-local computations stay the same, only the
   wrapping changes.
4. It avoids the uniformization gate that ruled out Route II at the
   RR-audit.
5. It avoids the structural-compactness mismatch in Route III.

**Route II is rejected** for the same reason RR-direct was rejected:
it relabels the gap as uniformization.

**Route III is at high risk of being structurally wrong** (Forster
Ch. 14's argument is for non-compact RS; the partition-of-unity
error on compact X does not have a Forster-style smaller-support
iteration without significant adaptation).

**However**, before committing to Route I's LOC cost, two
preliminary checks would be valuable:

1. **Mathlib trajectory check.** Mathlib has limited but growing
   manifold-VectorBundle infrastructure. A clean encoding of
   `(0,1)`-form-as-bundle that aligns with mathlib's roadmap would
   make Route I lower-risk and possibly upstream-able. If a sketch
   shows the encoding fights mathlib's existing `Riemannian`,
   `VectorBundle`, or `CovariantDerivative` setups, Route I may be
   even more expensive than estimated.

2. **Buzzard-spec re-check.** The named hypothesis
   `DBarSolvabilityAtGenusZero X` could conceivably be split into
   two: (a) a `(0,1)`-form-level statement that the partition-of-
   unity argument SHOULD discharge, and (b) a residual function-vs-
   form bridge that documents the type-level conversion. If the
   item-14 chain can be re-aimed at (a) and the bridge (b) is a
   small lemma about (0,1)-forms-with-compact-support being
   representable by functions, the bundle build could be scoped
   to "just enough (0,1)-forms to make the partition sum land",
   not "full Dolbeault theory."

Both checks are 1-session research items that should precede the
chip work.

## Concrete next step

Before any code in 5.5c, do a 1-session deeper read of:

* `Mathlib/Geometry/Manifold/VectorBundle/Basic.lean` and its
  Riemannian-bundle and CovariantDerivative companions, to see what
  bundle infrastructure mathlib offers as a foundation. (A `(0,1)`-form
  bundle is a complex line bundle with a specific transition rule;
  if mathlib has a clean `ComplexLineBundle` or `HolomorphicVectorBundle`
  primitive, Route I shortens.)
* Repo's `Manifold/HolomorphicOneFormChartCoeff*.lean` and
  `HolomorphicOneFormLocalPrimitive.lean` — the repo already has a
  chart-coefficient encoding for holomorphic (1,0)-forms. The
  (0,1)-form analogue may be a straightforward dual / conjugate
  construction.

The output of that read should be a sketched skeleton of the (0,1)-form
encoding (Lean signatures + 1-2 paragraph proofs sketched) that this
audit document then either ratifies (commit and start 5.5c-I) or
displaces (re-evaluate Route I's cost based on the actual encoding
friction).

**This audit's working conclusion**, pending the read above:
**Route I (with mathlib- / repo-aligned encoding) is the path.**
Route II is rejected on uniformization grounds. Route III is at
high structural risk on compact X and is not recommended.

5.5a + 5.5b remain landed primitives — they are useful in Route I
(the chart-anchored ∂̄ is the natural pre-bundle operator; the
transfer lemma is the natural bridge from bundle data to chart
representatives). No work is wasted.
