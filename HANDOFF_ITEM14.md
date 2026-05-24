# Item 14 — handoff

Last refreshed: 2026-05-24 (forward-leg **Chip 2c off-pole identity
landed** in commit `70ef6ee` —
`partialZBarManifold_g₀_eq_α_off_pole : y ≠ p → ∂̄(g₀) y = α y` is now
unconditional, via the chart-transition discharge of `chartInv` and the
Leibniz spec from Chip 1. Chip 2c WIP scaffolding + vanishing lemmas
(commit `213ada1`) and Chip 2b CR-converse bridge (commit `7cb9f19`)
are already in place. Two pieces remain to close Chip 2c entirely:
(i) `α` smooth-real on X (chart-transition smoothness on the annulus —
the on-source and off-tsupport pieces are done), and (ii) the final
assembly via `DBarSolvabilityAtGenusZero` + consolidator.

## Where this branch is

Branch: `feat/item14-forward-dbar-mul` (pushed to
`origin/feat/item14-forward-dbar-mul`, based on `origin/main`).

This branch is the **forward-leg work** for item 14
(`Genus0ImpliesS2 X`). The reverse-leg work
(`S2ImpliesGenus0 X`) lives on a separate branch
`feat/item14-affineChartTriangleSimplex-ball` and is independent —
do not mix the two arcs in one branch / PR.

## Item 14 reduction (unchanged)

Item 14 is `Basic.lean:73` —

```
genus_eq_zero_iff_homeo : genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2)
```

closes on arbitrary compact connected complex 1-manifold X via
[`Item14ViaSubsingletonFromBSLBAndAdmissibility.lean`](JacobianChallenge/Topology/Item14ViaSubsingletonFromBSLBAndAdmissibility.lean)
once the two named hypotheses are discharged:

1. **`hSP X`** ≡ `ExistsSimplePoleGermAtSomePoint X` — forward-leg
   target. **This branch is working on it.**

2. **`BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀`** — reverse-leg
   target. Worked on the other branch
   (`feat/item14-affineChartTriangleSimplex-ball`); see that branch's
   `HANDOFF_ITEM14.md` for current state of the Alt-B étale-space
   monodromy arc.

`h_admit` (the third Item-14 input) is auto-provided by the
`HasAdmissibleChartCover` typeclass instance shipped 2026-05-23.

## Forward leg — strategy

`hSP X` reduces classically through the chain in `HSP_AUDIT.md` §4.5
to a **single smaller named hypothesis**:

```
DBarSolvabilityAtGenusZero X  :=
  genus X = 0 → ∀ α smooth-real, ∃ u smooth-real, ∀ x, ∂̄ u x = α x
```

(equivalently `H¹(X, O) = 0` at genus 0 + Dolbeault isomorphism).
The bridge from `DBarSolvabilityAtGenusZero X` to `hSP X` is **the
Forster §16.9 cutoff + correction construction**:

```
Pick p : X. Let φ := chartAt ℂ p, c₀ := φ p.
Pick smooth bump χ : SmoothBumpFunction 𝓘(ℝ, ℂ) p with
  χ ≡ 1 on Metric.ball c₀ rIn   (some 0 < rIn < rOut < chartBallRadius p)
  χ ≡ 0 outside Metric.ball c₀ rOut.
Define g₀ : X → ℂ by:
  g₀ x = χ x · (φ x - c₀)⁻¹     where defined
  g₀ x = 0                       where χ x = 0   (extends globally smoothly off p)
Let α := ∂̄ g₀. By Leibniz + holomorphic specialization (g₀ holomorphic
on chart minus p, χ smooth):
  α x = (∂̄ χ x) · g₀ x   on chart-source
      = 0                outside support of χ.
∂̄ χ vanishes on B(c₀, rIn) (χ ≡ 1 there) AND outside B(c₀, rOut) (χ ≡ 0).
So α has compact support strictly inside the annulus B(c₀, rOut) \ B(c₀, rIn),
which is bounded away from p. α extends smoothly to all of X.

Apply DBarSolvabilityAtGenusZero with α → get smooth u with ∂̄ u = α.
Set f := g₀ - u (as a function X → ℂ, with f(p) junk).
Then ∂̄ f = 0 on X \ {p}, so f is ℂ-MDifferentiable (holomorphic) there.
Near p: α ≡ 0 on B(c₀, rIn), so ∂̄ u ≡ 0 there too, so u is holomorphic on
B(p, rIn). Hence chart-pullback `u ∘ chart.symm` is analytic at c₀.
At p: chart-pullback of f equals (z - c₀)⁻¹ - (u ∘ chart.symm)(z) near c₀.
The first term has order -1, the second is analytic with order ≥ 0,
so f has meromorphic order -1 at p — i.e. a simple pole.

Therefore `f` is a global meromorphic function on X with a simple pole
at p and holomorphic elsewhere. Its germ supplies hSP X.
```

This proof is genuine classical content (textbook Forster Thm 16.9),
not a paraphrase. The named hypothesis it leaves open is one mathlib-
sheaf-cohomology chip away from full classicality.

## Chip 1 — DONE (this branch)

Commit `8f8d05a feat(manifold): partialZBarManifold — manifold lift of ∂̄ with Leibniz`.

New file:
[`JacobianChallenge/Manifold/PartialZBarManifold.lean`](JacobianChallenge/Manifold/PartialZBarManifold.lean)
(215 LOC, sorry-free, in library).

Lifts the chart-free `partialZBar` (already on main) to manifold-side
`partialZBarManifold : (X → ℂ) → X → ℂ` via canonical `extChartAt`
chart pullback, and ships the operations Chip 2 needs:

| Lemma | Statement | Use in Chip 2 |
|---|---|---|
| `partialZBarManifold_mul` | `∂̄(f·g) x = ∂̄f x · g x + f x · ∂̄g x` | Computing `∂̄(χ · g₀)` symbolically |
| `partialZBarManifold_mul_of_chartPullback_differentiableAt_right` | `∂̄(f·g) x = ∂̄f x · g x` when `g ∘ chart.symm` is ℂ-diff at chart x | Dropping the `χ · ∂̄g₀` term off the pole |
| `partialZBarManifold_eq_zero_of_chartPullback_differentiableAt` | `∂̄f x = 0` on chart-holomorphic | Asserting `∂̄(g₀) = 0` on chart minus p |
| `partialZBarManifold_{add, sub, neg, const, zero}` | algebraic glue | Various |

Plus the chart-free `partialZBar_*` arsenal already on main (`PartialZBar.lean`
+ `PartialZBarChainRule.lean`).

## Chip 2 — DONE (this branch, two commits, 2026-05-24)

**File added**: [`JacobianChallenge/Manifold/ExistsSimplePoleGermFromGenusZeroDBarSolvability.lean`](JacobianChallenge/Manifold/ExistsSimplePoleGermFromGenusZeroDBarSolvability.lean)
(511 LOC, sorry/axiom-free, in library, full-build green).

### Commit 7348c06 — DBar definition + chart-side order keystone

* **`DBarSolvabilityAtGenusZero X : Prop`** — the named classical
  hypothesis (`genus X = 0 → ∀ α smooth-real, ∃ u smooth-real,
  partialZBarManifold u = α pointwise`). Isolates `H¹(X, O) = 0` at
  genus 0 / the Dolbeault statement.
* **`meromorphicOrderAt_inv_sub_const_eq_neg_one`** —
  `meromorphicOrderAt ((z-c)⁻¹) c = -1` (the classical pole order
  computation, chart-side `ℂ → ℂ`).
* **`meromorphicOrderAt_inv_sub_const_sub_analytic_eq_neg_one`** —
  `meromorphicOrderAt ((z-c)⁻¹ - h z) c = -1` for `h` analytic at `c`.
  The pole term dominates any analytic correction. Via
  `meromorphicOrderAt_add_eq_left_of_lt`.
* Manifold-side wrappers: `mmeromorphicAt_chart_inv_sub_const_sub_analytic`
  and the corresponding order = -1 variant — for use by Chip 2c.

### Commit dfdd5c3 — Forster §16.9 consolidator (assembly lemma)

* **`existsSimplePoleGermAtSomePoint_of_chartPullback_data`** — the
  unconditional assembly lemma. Given:
  - a point `p : X`,
  - a function `f : X → ℂ`,
  - an analytic-at-`(chartAt ℂ p) p` correction `h : ℂ → ℂ`,
  - **(H1)** `(f ∘ (chartAt ℂ p).symm) =ᶠ[𝓝[≠] ((chartAt ℂ p) p)] (fun z => (z - (chartAt ℂ p) p)⁻¹ - h z)`,
  - **(H2)** `∀ x ≠ p, AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)`,

  the conclusion `ExistsSimplePoleGermAtSomePoint X` follows
  unconditionally. The assembly does all the MMer / germ /
  `linearSystemGermDeltaP` bookkeeping — order = -1 at p via the
  Commit-7348c06 keystone + chart-pullback congr; order ≥ 0 at every
  `x ≠ p` from H2 via `AnalyticAt.meromorphicOrderAt_nonneg`.
* **`simplePoleGermExtensionHypothesis_of_chartPullback_data`** —
  packaged genus-conditional form returning
  `SimplePoleGermExtensionHypothesis X`.

## Chip 2c — split status (2026-05-24)

Chip 2c is large enough that it's split across multiple commits. The
landed pieces:

* **Commit `213ada1` (Chip 2c WIP):** definitions of `g₀`, `bC`,
  `chartInv`, `α`; vanishing of `partialZBarManifold (bC p b)` and `α`
  in a nbhd of `p` and off `tsupport b`; smoothness of `bC` globally.
  (~265 LOC.)
* **Commit `70ef6ee` (this commit's predecessor):** off-pole identity
  `partialZBarManifold_g₀_eq_α_off_pole : y ≠ p → ∂̄g₀ y = α y`. Routes
  through:
    - manifold-side `partialZBarManifold` congruence under `=ᶠ[𝓝 x]`,
    - chart-transition ℂ-differentiability of `chartInv` off the pole
      (via `analyticAt_chart_transition_of_isManifold` in
      `MeromorphicAt.lean` + chart injectivity),
    - ℝ-differentiability of `bC`'s chart-y pullback (`ContMDiff` +
      `contMDiffOn_extChartAt_symm` + vector-space `ContMDiffAt =
      ContDiffAt`),
    - Leibniz spec from Chip 1
      (`partialZBarManifold_mul_of_chartPullback_differentiableAt_right`).
  (~225 LOC, single file, sorry/axiom-free, full lake build green.)

**Two pieces remain to close Chip 2c entirely:**

### Remaining (i) — α smooth-real on X

`α := partialZBarManifold (bC p b) y * chartInv p y` needs to be
`ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α` (the input regularity required by
`DBarSolvabilityAtGenusZero`). The on-source-near-p and off-tsupport
parts are already done as `α_eventuallyEq_zero_near_p` /
`α_eventuallyEq_zero_off_tsupport` (eventually-eq zero gives smoothness
on those open sets trivially). The **annulus** part —
`{y ∈ chart_p.source | 0 < ‖chart_p y − c₀‖}` ∩ `tsupport b` — is where
the work is.

**Foundation in tree (commit `93b6676`):**

  `partialZBar_contDiffAt_of_contDiffAt :
     ContDiffAt ℝ ⊤ f z → ContDiffAt ℝ ⊤ (partialZBar f) z`

is the chart-side (`ℂ → ℂ`, no manifold) regularity bridge — built
via `ContDiffAt.fderiv_right` + `ContDiffAt.clm_apply` + scalar/add.
This gives `ContDiffOn ℝ ⊤ (partialZBar (bC ∘ chart_p.symm))
chart_p.target` after pointwise + ContDiffOn assembly. This is the
chart-p-relative ∂̄ of `bC ∘ chart_p.symm`.

**Obstacle for lifting to manifold-side α smoothness**:
`partialZBarManifold f x` is defined as
`partialZBar (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) ((extChartAt 𝓘(ℂ, ℂ) x) x)`,
i.e., it uses **`chartAt ℂ x`** (the canonical chart at `x`).
Mathlib's `ChartedSpace` does NOT guarantee that `chartAt` is locally
constant; for two nearby points `y` and `y'`, `chartAt ℂ y` and
`chartAt ℂ y'` may be entirely different charts. Smoothness of
`y ↦ partialZBarManifold (bC) y` as a function of `y` therefore needs
either (a) `chartAt` locally constant on chart sources (true for
concrete instances like `RiemannSphere`, see
`RiemannSphere.lean:363` — `chartAt' x := OnePoint.rec chartS (fun _ ↦ chartN) x`
is constant on the `coe`-image and on `{∞}` separately), or (b) the
chart-transition factor `conj (deriv (chart_p ∘ chartAt y.symm))` to be
*itself* a smooth function of `y`, non-trivial when `chartAt y` varies
with `y`.

**Three resolution options for the next session:**

1. **Add a `LocallyConstantChartAt` assumption** (or specialize to
   concrete X like `RiemannSphere`/`ℂ ⧸ L` where this is automatic).
   Weakens the final theorem from arbitrary X to "nice-chartAt" X.
   Simplest path; matches what is already used elsewhere in the repo
   for similar issues.

2. **Use mfderiv-based intrinsic ∂̄** instead of
   `partialZBarManifold`. The mfderiv is chart-invariant (it's the
   intrinsic differential), and ∂̄ extracted from it via the
   `(0,1)`-part of a real-linear CLM should be smooth via standard
   mfderiv smoothness machinery in mathlib. Requires re-stating the
   off-pole identity in mfderiv terms — moderate rework.

3. **Chart-transition factor smoothness for varying `chartAt`.** Prove
   that even when `chartAt y` varies with `y`, the chart-transition
   between `chart_p` and `chartAt y` gives a smooth conjugate-derivative
   factor. Requires either a mathlib-level smoothness statement for
   `y ↦ chartAt y` (probably not available in general) or a structural
   assumption on X.

**Recommended**: option 1 (or 2). Option 3 likely requires
auxiliary mathlib-style work.

**Concrete chart-transition identity (for whichever option is picked):**
On `chart_p.source`, the chain rule gives

  `partialZBarManifold (bC p b) y = partialZBar (bC ∘ chart_p.symm)
        (chart_p y) · conj (deriv (chart_p ∘ chart_y.symm)(chart_y y))`

via `partialZBar_comp_of_differentiableAt` in `PartialZBarChainRule.lean`,
using:
  - `bC ∘ chart_p.symm` ℝ-differentiable at `chart_p y` (bC ContMDiff +
    chart smooth),
  - `chart_p ∘ chart_y.symm` ℂ-differentiable at `chart_y y` (via
    `analyticAt_chart_transition_of_isManifold`, used already in
    `chartInv_chart_pullback_differentiableAt`).

  Then `α y = chartInv y · partialZBar (bC ∘ chart_p.symm) (chart_p y)
                · conj (deriv (chart_p ∘ chart_y.symm)(chart_y y))`
  and smoothness reduces to smoothness of each factor.

### Remaining (ii) — apply DBarSolvability + consolidator

Once (i) is in hand:

* `DBarSolvabilityAtGenusZero X` applied to `(α, α_smooth)` produces
  `u : X → ℂ` with `partialZBarManifold u y = α y` for all `y` and `u`
  smooth-real globally.
* `f := g₀ - u : X → ℂ`. By the off-pole identity (this commit), for
  every `y ≠ p`: `partialZBarManifold f y = partialZBarManifold g₀ y −
  partialZBarManifold u y = α y − α y = 0` (using
  `partialZBarManifold_sub` from Chip 1 + the off-pole identity).
* **Discharge H1** (`f ∘ chart_p.symm =ᶠ[nhdsWithin c₀ {c₀}ᶜ]
  (z − c₀)⁻¹ − h(z)` with `h := u ∘ chart_p.symm`): on the punctured
  inner ball (where χ ≡ 1), g₀ ∘ chart_p.symm = (z − c₀)⁻¹, and
  h ∘ chart_p.symm = u ∘ chart_p.symm by definition; subtract.
* **`h` analytic at `c₀`** (needed by consolidator's `h_an`): u's
  chart-p pullback has `partialZBar = 0` on the inner ball (since `α = 0`
  there from `α_eventuallyEq_zero_near_p`), so by Chip 2b's
  `analyticAt_of_contDiffOn_of_partialZBar_eqOn_zero` (CR converse +
  Cauchy regularity), h is `AnalyticAt ℂ` at `c₀`.
* **Discharge H2** (∀ x ≠ p, AnalyticAt ℂ (f ∘ chart_x.symm) (chart_x x)):
  f is `C^∞-ℝ` off `p` (g₀ smooth off p — needs proof — and u
  smooth-real globally), and ∂̄f = 0 off p (this commit). Chip 2b's
  bridge gives analyticity at chart_x x.
* **One-line apply** `existsSimplePoleGermAtSomePoint_of_chartPullback_data X p f h h_an h_chart_eq h_off_pole`
  to close `hSP X` from `DBarSolvabilityAtGenusZero X` at `genus X = 0`.

Estimated LOC for (i)+(ii) combined: ~400–600 LOC. (i) is the hardest;
(ii) is mostly bookkeeping over what's already landed.

## Earlier Chip 2c plan (for context, partially superseded)

**Goal**: discharge **H1** and **H2** of the Chip-2 consolidator from
the Forster §16.9 ingredients — bump function + ∂̄-solution from
`DBarSolvabilityAtGenusZero X`. This produces the original target
theorem

```lean
theorem existsSimplePoleGermAtSomePoint_of_dbarSolvability
    (h : DBarSolvabilityAtGenusZero X)
    (hg : JacobianChallenge.genus X = 0) :
    ExistsSimplePoleGermAtSomePoint X
```

as a one-line application of `existsSimplePoleGermAtSomePoint_of_chartPullback_data`.

**File to create**: `JacobianChallenge/Manifold/ForsterCutoffPoleConstruction.lean`
(or extend the existing
`ExistsSimplePoleGermFromGenusZeroDBarSolvability.lean` —
either is acceptable; new file is recommended for cleaner separation
of "geometric construction" from "assembly").

### Suggested sections

1. **Pick `p : X`** via `ConnectedSpace → Nonempty`. Fix
   `c₀ := (chartAt ℂ p) p`.

2. **Bump construction.** `SmoothBumpFunction 𝓘(ℝ, ℂ) p` is
   `Nonempty` automatically; extract `b : SmoothBumpFunction 𝓘(ℝ, ℂ) p`
   with `rIn, rOut`. The bump `χ := (b : X → ℝ)` has:
   - `χ p = 1` (and `χ ≡ 1` on `(extChartAt 𝓘(ℝ, ℂ) p) ⁻¹' ball c₀ rIn`)
   - `tsupport χ ⊆ (extChartAt 𝓘(ℝ, ℂ) p).symm '' closedBall c₀ rOut`
     (in particular, `tsupport χ ⊆ (chartAt ℂ p).source`)
   - smooth-real (`SmoothBumpFunction.contMDiff`)

3. **Local pole** `g₀ : X → ℂ`:
   ```
   g₀ x := if x ∈ (chartAt ℂ p).source
           then (χ x : ℂ) * ((chartAt ℂ p) x - c₀)⁻¹
           else 0
   ```
   Properties to prove:
   - `g₀ x = 0` outside `tsupport χ` (because `χ x = 0` there).
   - `g₀ x = ((chartAt ℂ p) x - c₀)⁻¹` for `x ∈ {y | χ y = 1} ∩ ((chartAt ℂ p).source \ {p})`
     — in particular on the inner ball minus `{p}`.
   - Chart-pullback `g₀ ∘ (chartAt ℂ p).symm` on chart target equals
     `(χ ∘ (chartAt ℂ p).symm) z * (z - c₀)⁻¹` (for `z ∈` chart target).

4. **The (0,1) form** `α := partialZBarManifold g₀ : X → ℂ`.
   Claim: `α` is smooth-real and supported strictly inside the
   annulus `{x | x ∈ chart.source ∧ rIn < dist (chartAt ℂ p x) c₀ < rOut}`
   — bounded away from `p`. Proof:
   - On the inner ball `{x | dist (chart x) c₀ < rIn}` (where `χ = 1`):
     `g₀ = (chart - c₀)⁻¹` which is chart-holomorphic off `p`. By Chip 1's
     `partialZBarManifold_eq_zero_of_chartPullback_differentiableAt`, `α = 0` there.
     (At `p` itself, the chart pullback is unbounded so the formula is
     ill-defined — handle by setting `α p := 0` if needed, since the
     inner ball is open around `p` and `α` is constant 0 on a
     neighborhood except possibly at `p`; conclude `α p = 0` by
     continuity / smoothness extension.)
   - Outside `tsupport χ` (open): `g₀ ≡ 0` on a neighborhood, hence
     `partialZBarManifold g₀ = 0` there.
   - On the annulus: `g₀ = χ · (chart - c₀)⁻¹` and Chip 1's
     `partialZBarManifold_mul_of_chartPullback_differentiableAt_right`
     gives `α x = (partialZBarManifold χ x) · ((chart x) - c₀)⁻¹`
     (smooth-real, since χ is smooth-real and `(chart - c₀)⁻¹` is
     chart-holomorphic on the annulus).

5. **Apply DBar.** `h hg α` gives smooth-real `u : X → ℂ` with
   `partialZBarManifold u = α` pointwise.

6. **Define** `f := g₀ - u : X → ℂ`. Discharge consolidator
   hypotheses:

   - **(H1) chart-pullback at `p`.** On the punctured inner ball,
     `χ ≡ 1` so `g₀ ∘ chart.symm (z) = (z - c₀)⁻¹` for `z ≠ c₀` near
     `c₀`. Therefore
     `f ∘ chart.symm (z) = (z - c₀)⁻¹ - u ∘ chart.symm (z)`
     on the punctured inner ball. Set `h_chart := u ∘ (chartAt ℂ p).symm`
     (this is the `h : ℂ → ℂ` of the consolidator). Need:
     `AnalyticAt ℂ h_chart c₀`.

   - **`h_chart` analytic at `c₀`.** Since `α = 0` on the inner ball,
     `partialZBarManifold u = 0` on the inner ball, so the chart
     pullback `h_chart = u ∘ chart.symm` has chart-pullback `∂̄ = 0`
     on the chart image of the inner ball. By the chart-side CR
     converse (`differentiableAt_complex_of_dbarChart_eq_zero` —
     bridge `dbarChart = partialZBar` locally via the one-line
     `unfold + ring` lemma; **do not** import the orphaned dbar
     subtree). `h_chart` is ℂ-differentiable on an open ball around
     `c₀`, hence analytic at `c₀`.

   - **(H2) analytic off `p`.** For `x ≠ p`, the chart pullback
     `f ∘ (chartAt ℂ x).symm` at `(chartAt ℂ x) x`:
     - `g₀ ∘ (chartAt ℂ x).symm` is smooth-real on a neighborhood
       (smoothness-of-g₀ + chart-transition + smoothness of `(chart -
       c₀)⁻¹` away from `p`).
     - `partialZBarManifold g₀ = α` and `partialZBarManifold u = α`
       on all of `X`, so `partialZBarManifold (g₀ - u) = 0`
       pointwise, hence chart-pullback `(f ∘ (chartAt ℂ x).symm)` has
       `∂̄ = 0` at `(chartAt ℂ x) x`. By CR converse +
       smoothness on a neighborhood, ℂ-differentiable on an open set,
       hence analytic at `(chartAt ℂ x) x`.

7. **Apply consolidator.** One-line: `existsSimplePoleGermAtSomePoint_of_chartPullback_data X p f h_chart h_an h_chart_eq h_off_pole`.

### Estimated LOC

~400–700 LOC for the discharge. Bulk is in step 4 (∂̄ of `χ • (chart-c₀)⁻¹`)
and step 6's CR-converse-bridge step. Step 7 is one line.

**No further split needed** — the consolidator collapses the closing
step to one application, so a single commit lands the full target.

### Risks (resolved in Chip 1 planning, summarized for Chip 2)

| Risk | Resolution |
|---|---|
| `SmoothBumpFunction` model mismatch (mathlib is ℝ-side; X is ℂ) | Use `IsManifold 𝓘(ℝ, ℂ) ω X` instance already in tree (see `SheetCotPullbackContMDiffAtReal.lean:57`); downgrade ω → ∞ for `SmoothBumpFunction.contMDiff`. |
| `MMeromorphicAt` chart-independence is owed | Use canonical-chart pullback definition only (`MeromorphicAt.lean:85`). All our chart references are canonical; no transport between charts needed. |
| Building MMer via arithmetic of MMers | Not viable (see step 9 above). Build directly with `MMer.mk` from a manifest `MMeromorphicOn` proof. |
| Inner-ball u holomorphic | Falls out of CR converse + α ≡ 0 on `B(p, rIn)`. Use chart-side `differentiableAt_complex_of_dbarChart_eq_zero` + one-line `dbarChart = partialZBar` bridge. |

### Tools / files to consult on entry (for Chip 2c)

- `tools/chip-prompt-preamble.md` — 7 anti-paraphrase gates.
- `HSP_AUDIT.md` — full hSP chain; §4.5 has the audit's recipe (Chips 2 + 2c).
- `JacobianChallenge/Manifold/ExistsSimplePoleGermFromGenusZeroDBarSolvability.lean` — **Chip 2 deliverable; the consolidator `existsSimplePoleGermAtSomePoint_of_chartPullback_data` is the landing pad. Read its hypotheses (H1 = `h_chart_eq`, H2 = `h_off_pole`) — they are exactly Chip 2c's targets.**
- `JacobianChallenge/Manifold/PartialZBar.lean` — chart-side ∂̄ + Leibniz + Forster spec.
- `JacobianChallenge/Manifold/PartialZBarManifold.lean` — **Chip 1 deliverable; consume directly** (`partialZBarManifold_mul`, `_mul_of_chartPullback_differentiableAt_right`, `_eq_zero_of_chartPullback_differentiableAt`).
- `.lake/packages/mathlib/Mathlib/Geometry/Manifold/BumpFunction.lean` — `SmoothBumpFunction 𝓘(ℝ, ℂ) p` API. `Nonempty` instance is automatic; `eq_one`, `support_eq_inter_preimage`, `tsupport_subset_chartAt_source`, `eventuallyEq_one_of_dist_lt`, `eventuallyEq_one`, `contMDiff` (in `Mathlib/Geometry/Manifold/ContMDiff/Atlas.lean` neighborhood).
- `JacobianChallenge/Manifold/ConvexBallChartAtMaximalAtlas.lean` — `convexBallChartAt p` (chart with convex ℂ-target ball, in maximal atlas) — useful but optional; the canonical chart at `p` suffices.
- `JacobianChallenge/Manifold/SimplePoleAnalyticReciprocal.lean` — analytic-reciprocal core at ℂ-side simple pole.
- `JacobianChallenge/Manifold/RiemannSphereSimplePole.lean` — base-case construction on RS (sanity check for the Chip 2c discharge applied to `X = RiemannSphere`).
- `JacobianChallenge/Manifold/MeromorphicFunctionField.lean` — `MMer`, germ quotient, arithmetic (consumed by the consolidator; Chip 2c doesn't need to touch this).
- `JacobianChallenge/Manifold/MeromorphicAt.lean` — `MMeromorphicAt` definition + chart-independence (already discharged for `[IsManifold 𝓘(ℂ, ℂ) ω X]`).
- `JacobianChallenge/Topology/RRStrictLtFromSimplePole.lean:119` — `ExistsSimplePoleGermAtSomePoint` definition.

## Discipline

- **No paraphrase chips.** No more "from N inputs" reformulations of
  `hSP X` or `DBarSolvabilityAtGenusZero`. Each commit must move a
  named hypothesis on arbitrary X by genuine classical content. See
  `tools/chip-prompt-preamble.md`.
- **No bundles.** Forward leg and reverse leg are independent — don't
  mix them in a single PR.
- **Local verify primary** (per `feedback_default_workflow_lean.md`):
  `LEAN_NUM_THREADS=1 lake env lean FILE.lean`. Never `lake build`
  (parallel default → apfsd panic per CLAUDE.md).
- **Don't re-adopt the orphan dbar subtree.** Files `DBarOperator.lean`,
  `DBarManifold.lean`, `DBarManifoldMDiff.lean`, `DBarChartChainRule.lean`
  exist in `JacobianChallenge/Manifold/` but are NOT in the library
  import tree (`JacobianChallenge.lean` doesn't import them). They are
  superseded by the `partialZBar` subtree. Chip 2 should consume
  `partialZBarManifold` (Chip 1) directly. If a chart-side CR converse
  is needed, bridge to `dbarChart` via a one-line `unfold + ring`
  lemma inside the Chip 2 file rather than importing the orphan
  subtree.

## Reverse leg (other branch — for context, not to touch here)

The reverse leg `S2ImpliesGenus0 X` was reduced on
`feat/item14-affineChartTriangleSimplex-ball` to a single named
hypothesis `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀` (every
smooth loop on simply-connected X bounds *some* smooth 2-chain).
That branch's Alt-B étale-space monodromy arc (Chips 1–4e landed; Chip 4
mathlib-monodromy application pending) is the work to finish there.
See its `HANDOFF_ITEM14.md` and `AUDIT_LOOP_PERIOD_VANISHES.md` for
state.

## Worktree commands

```bash
git worktree list      # confirm worktree still pinned
cd "/Volumes/4TB SD/ClaudeCode/jacobian-lean-challenge-item14"
git switch feat/item14-forward-dbar-mul   # forward leg
git switch feat/item14-affineChartTriangleSimplex-ball   # reverse leg
```

The original checkout at `/Volumes/4TB SD/ClaudeCode/jacobian-lean-challenge`
is used by parallel sessions on different branches. Don't `cd` into it.
