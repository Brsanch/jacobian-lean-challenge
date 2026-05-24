# Item 14 — handoff

Last refreshed: 2026-05-24 (forward-leg Chip 1 landed on this branch).

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

## Chip 2 — concrete launch (next session)

**File to create**: `JacobianChallenge/Manifold/ExistsSimplePoleGermFromGenusZeroDBarSolvability.lean`

**Target theorem**:

```lean
theorem existsSimplePoleGermAtSomePoint_of_dbarSolvability
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X] [IsManifold (𝓘(ℝ, ℂ)) ω X]
    (h : DBarSolvabilityAtGenusZero X)
    (hg : JacobianChallenge.genus X = 0) :
    ExistsSimplePoleGermAtSomePoint X
```

Where `DBarSolvabilityAtGenusZero X` is a new `def Prop` introduced in
this same file (precise shape — see "Risk 3 in plan" notes below).

### Suggested sections

1. **`def DBarSolvabilityAtGenusZero (X) : Prop`** — `genus X = 0 →
   ∀ α : X → ℂ, smooth-real → ∃ u, smooth-real ∧ ∂̄u = α everywhere`.
   Use `partialZBarManifold u x = α x` for the ∂̄ identity (not chart-side).

2. **Pick `p : X`** via `ConnectedSpace → Nonempty`.

3. **Bump construction.** Use mathlib's `SmoothBumpFunction 𝓘(ℝ, ℂ) p`
   (requires `[IsManifold 𝓘(ℝ, ℂ) ∞ X]` — downgrade from ω instance).
   Pick `rIn < rOut < chartBallRadius p` so support sits in
   `convexBallChartAt p` source.

4. **Local pole** `g₀ : X → ℂ` — write as `χ • (1/(φ - c₀))` extended
   by zero. Show: globally smooth-real off `p`, equals `(φ - c₀)⁻¹`
   on `B(p, rIn)`.

5. **`α := partialZBarManifold g₀ : X → ℂ`** — show smooth-real
   everywhere on X, with α x = 0 on `B(p, rIn)` (because χ ≡ 1 there
   and `(φ-c₀)⁻¹` is chart-holomorphic) AND outside support of bump
   (because g₀ ≡ 0 there). Uses Chip 1's `partialZBarManifold_mul` +
   `_mul_of_chartPullback_differentiableAt_right` (with `g := 1/(φ-c₀)`
   ℂ-holomorphic on chart minus p).

6. **Apply `h hg α`** → smooth `u : X → ℂ` with `partialZBarManifold u
   x = α x` everywhere.

7. **Corrected pole** `f := g₀ - u`. ∂̄f = 0 globally → f is
   ℂ-MDifferentiable on `X \ {p}` (CR converse). Note: CR converse on
   manifold side currently lives only in `DBarManifoldMDiff.lean`
   (orphaned older subtree); the chart-side
   `differentiableAt_complex_of_dbarChart_eq_zero` from
   `DBarOperator.lean` + the `dbarChart = partialZBar` bridge
   (one-liner — `unfold` + `ring`) is the cleanest path. Chip 2 should
   write that one-line bridge locally; **do not** wire in the orphaned
   `dbar` subtree.

8. **Inner-ball u holomorphic.** α ≡ 0 on `B(p, rIn)` implies
   `partialZBarManifold u = 0` there, so `u ∘ chart.symm` is ℂ-diff
   on an open ball in chart-image, hence analytic at c₀.

9. **MMer construction.** Build `MMer X` directly for `f` —
   `MMeromorphicAt 𝓘(ℂ, ℂ) f x` via canonical-chart pullback per
   `MeromorphicAt.lean:85`. Two cases:
   - **At `p`**: chart-at-p pullback of f equals `(z-c₀)⁻¹ - (u ∘
     chart.symm)(z)` on a punctured neighborhood. u ∘ chart.symm is
     analytic at c₀ (step 8). Apply `MeromorphicAt` of inverse +
     analytic difference; `meromorphicOrderAt = -1` via
     `meromorphicOrderAt_add_of_lt`.
   - **At `x ≠ p`**: f is ℂ-MDifferentiable on a NEIGHBORHOOD of x
     (step 7 gives MDifferentiable on `X \ {p}` which is open), hence
     chart-pullback `f ∘ chartAt(x).symm` is ℂ-DifferentiableOn an
     open set, hence analytic at `(chartAt x) x`, hence meromorphic
     with order ≥ 0.

   **DO NOT** try to build `MMer f = MMer g₀ - MMer u`. Neither `g₀`
   nor `u` alone is an MMer (both are smooth-real but generally not
   chart-holomorphic). The cancellation makes only `g₀ - u`
   meromorphic. Verified during Chip 1 planning — see "Risk 3" in
   the chat log of session 2026-05-24.

10. **Germ + membership.** Take germ of f, verify `∈
    linearSystemGermDeltaP p` (order ≥ 0 off p), conclude
    `ExistsSimplePoleGermAtSomePoint X`.

### Estimated LOC and session count

~800–1100 LOC total. Likely splits at a natural boundary (e.g. between
step 5 and step 6, or between step 9 cases) into 2 commits. Each
commit must close to a substantive theorem statement — **no
setup-only commits per anti-paraphrase gates**.

### Risks (resolved in Chip 1 planning, summarized for Chip 2)

| Risk | Resolution |
|---|---|
| `SmoothBumpFunction` model mismatch (mathlib is ℝ-side; X is ℂ) | Use `IsManifold 𝓘(ℝ, ℂ) ω X` instance already in tree (see `SheetCotPullbackContMDiffAtReal.lean:57`); downgrade ω → ∞ for `SmoothBumpFunction.contMDiff`. |
| `MMeromorphicAt` chart-independence is owed | Use canonical-chart pullback definition only (`MeromorphicAt.lean:85`). All our chart references are canonical; no transport between charts needed. |
| Building MMer via arithmetic of MMers | Not viable (see step 9 above). Build directly with `MMer.mk` from a manifest `MMeromorphicOn` proof. |
| Inner-ball u holomorphic | Falls out of CR converse + α ≡ 0 on `B(p, rIn)`. Use chart-side `differentiableAt_complex_of_dbarChart_eq_zero` + one-line `dbarChart = partialZBar` bridge. |

### Tools / files to consult on entry

- `tools/chip-prompt-preamble.md` — 7 anti-paraphrase gates.
- `HSP_AUDIT.md` — full hSP chain; §4.5 has the audit's chip-2 recipe.
- `JacobianChallenge/Manifold/PartialZBar.lean` — chart-side ∂̄ + Leibniz + Forster spec.
- `JacobianChallenge/Manifold/PartialZBarManifold.lean` — **Chip 1 deliverable; consume directly.**
- `JacobianChallenge/Manifold/ConvexBallChartAtMaximalAtlas.lean` — `convexBallChartAt p` (chart with convex ℂ-target ball, in maximal atlas).
- `JacobianChallenge/Manifold/SimplePoleAnalyticReciprocal.lean` — analytic-reciprocal core at ℂ-side simple pole.
- `JacobianChallenge/Manifold/RiemannSphereSimplePole.lean` — base-case construction on RS (template for what we're producing on X).
- `JacobianChallenge/Manifold/MeromorphicFunctionField.lean` — `MMer`, germ quotient, arithmetic.
- `JacobianChallenge/Manifold/MeromorphicAt.lean` — `MMeromorphicAt` definition + closure lemmas; chart-independence is owed.
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
