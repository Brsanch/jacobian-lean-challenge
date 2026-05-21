# Item 14 classical-content handoff

## Worktree setup (read first)

This file lives in the dedicated worktree:

```
/Volumes/4TB SD/ClaudeCode/jacobian-lean-challenge-item14
```

pinned to branch `feat/item14-classical-content`. The original checkout
at `/Volumes/4TB SD/ClaudeCode/jacobian-lean-challenge` is used by a
parallel session on a different branch (last seen: `wip/chip7-from-origin`,
C3 / period-lattice / Hodge-Riemann arc).

**All work happens in this worktree.** Never `cd` into the original
checkout; never run `git switch` here without thinking about whether the
other session needs the branch. The worktree's purpose is to keep our
working tree's branch state independent of the parallel session.

`git worktree list` should always show both:

```
/Volumes/4TB SD/.../jacobian-lean-challenge         [<other-branch>]
/Volumes/4TB SD/.../jacobian-lean-challenge-item14  [feat/item14-classical-content]
```

## 2026-05-20 session progress: Dolbeault chips 2–8 landed (local on branch)

Branch advanced 7 chips beyond `66f5199` (handoff baseline). All
single-file `LEAN_NUM_THREADS=1 lake env lean …` clean, no axiom, no
sorry. Branch is local-only — not pushed.

```
a4264bf feat(item-14): dbar ℂ-linearity in function argument (Dolbeault chip 8)
b8eb5af feat(item-14): dbar chain rule for holomorphic inner (Dolbeault chip 7)
df171c0 feat(item-14): manifold-side dbar biconditional (Dolbeault chip 6)
881a216 feat(item-14): CR converse — dbarChart=0 ⇒ holomorphic (Dolbeault chip 5)
db191f9 feat(item-14): MDifferentiableAt ⇒ dbar = 0 (Dolbeault chip 4)
a9a3383 feat(item-14): manifold dbar operator (Dolbeault chip 3)
1490361 feat(item-14): dbarChart_eq_zero_of_hasDerivAt (Dolbeault chip 2)
```

**What landed.** The chart-side and manifold-level `dbar` operator with
full biconditional `MDifferentiableAt ↔ dbar = 0`, ℂ-linearity, additivity,
plus the **Wirtinger chain rule** `dbarChart (f ∘ g) z₀ = conj g' *
dbarChart f (g z₀)` when `g` is holomorphic. The latter (chip 7) gives
chart-independence of `dbar = 0` at the chart level: for any holomorphic
transition with nonzero derivative, the vanishing of ∂̄ is preserved.

**What's open and ranked.**

1. **Manifold-level chart-independence of `dbar = 0`** under
   `[IsManifold 𝓘(ℂ, ℂ) ω X]`. Need: chart transitions on a complex
   1-manifold have nonzero derivative everywhere on their source.
   This is the inverse-function-theorem application
   `id = ψ ∘ φ⁻¹ ∘ φ`. Routing through `contDiffGroupoid ω` membership
   gives `ContDiffOn ℂ ω` for both directions, hence `hasDerivAt` with
   non-zero `g'`. Apply chip 7 to conclude. Self-contained next chip.
2. **(0,1)-form bundle.** Define the antiholomorphic-cotangent
   bundle on a complex 1-manifold and `dbar` as a map from smooth
   ℂ-valued functions to smooth (0,1)-forms. Significant Lean
   infrastructure.
3. **L²-Hodge setup → H¹(X, O) = 0 at genus 0.** The deep classical
   step. Forster §16 / Griffiths-Harris §0.6. Multi-session arc, each
   step itself a classical theorem (Fredholm theory, Dolbeault
   isomorphism, …).
4. **hSP via the cutoff + ∂̄-solve recipe** (step 12 of the prior
   roadmap, now closer-in once L²-Hodge is staged).

The honest assessment from the prior handoff stands: closing item 14
strictly in tree is multi-session classical work. Each chip is one
piece of that arc.

## Prior session's commits on this branch

Twelve commits ahead of `origin/main`, interleaved with two from the
parallel session that landed here before the worktree split:

```
47b4965 feat(classical): CompleteHodgeRiemannViaStandardForm (chip 11)   ← parallel session
5116a83 feat(item-14): foundational dbar operator infrastructure (first chip of Dolbeault arc)
20c271b feat(item-14): precisely-named classical hypothesis for simple-pole germ extension
9064872 feat(item-14): closure from [HasBSLB] + [HasAdmissibleChartCover] + hSP (class-driven)
cf8090e feat(item-14): typeclass-driven Subsingleton(ω) from [HasBSLB] + [HasAdmissibleChartCover]
dc744c9 feat(classical): PeriodSigmaRealLI chip 2C - Σ → ℝ-LI of period vectors  ← parallel session
2991f11 feat(item-14): closure from hSP + BSLB + universal admissibility via Subsingleton
47ad141 feat(item-14): Subsingleton(ω) from BSLB + universal PathPrimitiveAdmissibleChartCover
bde48ec feat(item-14): parallel route via Subsingleton(ω) from BSLB chain
67085df feat(classical): PeriodSigmaInvertibility chip 2B                  ← parallel session
f33bb84 feat(item-14): RS smoke test for BSLB+pathPrimitive 3-input route
52dd84c feat(item-14): Subsingleton(ω) and item 14 closure from BSLB + path-primitive
```

The parallel-session commits don't conflict with item 14 work; they just
happen to be on this branch's history.

## Item 14 dependency map (current state of openness)

Item 14 = `genus X = 0 ↔ Nonempty (X ≃ₜ S²)`. All Lean architectural
factoring is exhausted. The remaining open content is genuinely
classical:

- **Forward leg (`genus = 0 → ≃ₜ S²`)** has **one** way:
  `hSP : ExistsSimplePoleGermAtSomePoint X` (Riemann-Roch existence of
  a simple-pole germ at some point). Equivalent to `RR_DimGE2_GenusZero_Germ
  X`. No alternative — uniformization for genus-0 surfaces is what
  produces hSP classically.
- **Reverse leg (`≃ₜ S² → genus = 0`)** has **two** ways:
  - `h_top` (topological-sphere uniformization: `Nonempty (X ≃ₜ S²) →
    Nonempty (HolomorphicEquiv X RS)`), or
  - `Subsingleton (HolomorphicOneForm X)` from `SimplyConnectedSpace X`,
    which routes through BSLB + path-primitive analytic content.

For `X = RiemannSphere` specifically, both legs are unconditional in
tree (smoke-tested in `Topology/Item14RiemannSphereViaBSLBPathPrimitive.lean`).

## What the prior session attacked

Started the Dolbeault arc toward discharging `hSP` via
`H¹(X, O) = 0` at genus 0 + ∂̄-equation solvability.

- `Manifold/DBarOperator.lean` (commit 5116a83) — `dbarChart` chart-side
  ∂̄ operator + linearity (`_add`, `_neg`, `_const`, `_zero`).
- `Manifold/SimplePoleConstructionFromChart.lean` (commit 20c271b) —
  `SimplePoleGermExtensionHypothesis X` precisely-named classical input.

The holomorphic-zero theorem `dbarChart_eq_zero_of_hasDerivAt` is
**deferred** because of an unresolved `IsScalarTower ℝ ℂ ℂ` synthesis
failure in `HasFDerivAt.restrictScalars ℝ`.

## The IsScalarTower obstacle (debug starting point)

Mathlib's `Mathlib/Analysis/Complex/RealDeriv.lean` line 53-55 uses
exactly the same idiom successfully:

```lean
have B :
    HasStrictFDerivAt e ((ContinuousLinearMap.smulRight 1 e' : ℂ →L[ℂ] ℂ).restrictScalars ℝ)
      (ofRealCLM z) :=
  h.hasStrictFDerivAt.restrictScalars ℝ
```

In our file the analogous call:

```lean
have hfd_real : HasFDerivAt f
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) f').restrictScalars ℝ) z₀ :=
  hf.hasFDerivAt.restrictScalars ℝ
```

fails with `failed to synthesize instance IsScalarTower ℝ ℂ ℂ` despite
the high-priority `IsScalarTower.right` instance in
`Mathlib.Algebra.Algebra.Defs`. Multiple imports tried (`Algebra.Defs`,
`Complex.Conformal`, `LinearAlgebra.Complex.Module`); none unblock it.
`letI : IsScalarTower ℝ ℂ ℂ := inferInstance` itself succeeds, but the
subsequent `restrictScalars` call still errors.

**Recommended debug next steps:**

1. Add `set_option trace.Meta.synthInstance true` before the failing
   line and read the trace to see why synth fails.
2. Compare the elaboration context at the failing line to mathlib's
   working site (variables in scope, namespace, etc.).
3. Try `(hf.hasFDerivAt : HasFDerivAt f _ z₀).restrictScalars ℝ` with
   explicit type ascription on `hf.hasFDerivAt` to nudge unification.
4. Try wrapping the proof in a `section` that opens
   `RestrictScalars` mathlib namespace (if there is one).
5. Last resort: bypass `restrictScalars` and prove the values directly
   via `fderiv_eq_deriv_mul` style + manual ℝ-Fréchet derivative
   construction.

## Next chip after `dbarChart_eq_zero_of_hasDerivAt` lands

The roadmap for the Dolbeault arc (each chip a separate file):

1. ✅ `DBarOperator.lean` — chart-side definition + linearity (committed).
2. **Next**: holomorphic ⇒ `dbarChart = 0` (the IsScalarTower one above).
3. Lift `dbarChart` from chart to manifold: `dbar f x` for `f : X → ℂ`
   on a complex 1-manifold, via chart pullback.
4. Define `dbar` of smooth forms on `X` (`Ω^0 → Ω^(0,1)`).
5. Set up L² inner product on smooth sections.
6. Prove `dbar` is closed (image in L²) — key analytic input.
7. Adjoint `dbar*` on `Ω^(0,1)`.
8. Laplacian `Δ_dbar = dbar* dbar + dbar dbar*` on `Ω^0`. Fredholm.
9. Hodge decomposition: `Ω^(0,1) = im(dbar) ⊕ ker(Δ_dbar)`.
10. `ker(Δ_dbar on Ω^(0,1)) ≅ H¹(X, O)` (Dolbeault iso).
11. At genus 0: `H¹(X, O) ≅ H⁰(X, Ω¹)^* = 0`, hence solvability
    `dbar u = h` for any `h ∈ Ω^(0,1)`.
12. Construct `hSP` via the chart bump + ∂̄-solve recipe in
    `SimplePoleConstructionFromChart.lean`'s docstring.

Each step is a chip. None are at the mathlib pin. Realistic scope:
multi-session arc.

## Standing constraints for the new session

- **Branch discipline:** stay on `feat/item14-classical-content` in this
  worktree. If you need to push, `git push -u origin feat/item14-classical-content`
  (the branch is local-only — no upstream yet).
- **Don't touch `JacobianChallenge.lean` (umbrella) without coordinating**:
  the parallel session frequently modifies it. Their edits are on
  different branches but stash conflicts will happen if both touch the
  same lines.
- **Don't claim "PUSHED" without verifying** (`feedback_verify_push_before_claiming`).
- **No fabricated LOC estimates** (`feedback_no_fabricated_loc_estimates`).
  Each chip is its own size; report measured size after the fact.
- **Single-file verify**: `LEAN_NUM_THREADS=1 lake env lean <file>` for
  iteration; throttled `taskpolicy -b nice -n 19 lake build <module>` for
  the duplicate-name catch before push.
- **No `du -sh` on `.lake`** — instant kernel panic (CLAUDE.md).
- The chip discipline from the prior session: pick ONE classical input
  and push on it, don't ping-pong between architectural shuffles. The
  prior session shipped 11 chips but most were consolidation; only
  DBarOperator started real classical infrastructure.

## Worktree commands cheat sheet

```bash
# From anywhere
git worktree list                # confirm both worktrees still pinned

# Enter the item-14 worktree
cd "/Volumes/4TB SD/ClaudeCode/jacobian-lean-challenge-item14"

# When done with the worktree (only if abandoning the branch)
git worktree remove "/Volumes/4TB SD/ClaudeCode/jacobian-lean-challenge-item14"
```
