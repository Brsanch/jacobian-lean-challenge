# T4 — Holomorphic primitive on simply-connected X
## Multi-session work plan (no chips, no paraphrase)

Honest scope after audit. T4 (= `holomorphic_primitive_of_simply_connected`)
is the reverse-leg open arc for item 14. The classical proof is:

> On simply-connected X, every closed holomorphic 1-form ω has a global
> holomorphic primitive F (`dF = ω`). Because X is compact connected,
> `F = const`, hence `ω = 0`. Hence `H⁰(X, Ω¹) = 0`, i.e. `genus X = 0`.

The Lean obstruction is **converting continuous null-homotopy to smooth
null-bordism** so that Stokes applies. This is **Whitney smooth
approximation rel boundary** on a *manifold*-valued map. Status:

- **Mathlib has finite-dim Whitney smooth approximation** at
  [`Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`](.lake/packages/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean):
  - `Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le` —
    smooth approx of continuous `E → F` for finite-dim `E`, Banach `F`.
  - `UniformContinuous.exists_contDiff_dist_le` — uniform-distance form.
- **Mathlib does NOT have manifold-valued Whitney** — continuous
  `K → M` smoothly approximable for general smooth manifold `M`.
- **The chart-contained case** (when `f '' K` lies in a single chart
  source) reduces to mathlib by chart pullback. But the general case
  needs a chart-cover + partition-of-unity gluing argument.
- The in-tree BSLB arc (the existing reverse-leg infrastructure) has the
  same blocker — per [`HANDOFF_ITEM14.md`](HANDOFF_ITEM14.md): "sub-arcs
  from Lebesgue subdivision are only chart-contained on `[0,1]` but the
  bordism machinery needs global chart-containment". The three options
  listed (Smooth2Simplex refactor, finer SmoothPath, strong-hypothesis
  pattern) all require multi-session work.

## Realistic multi-session plan

This is a 4–8 working session arc. Each session targets ONE substantive
file, no chips, no new named hypotheses.

### Session 1 — Chart-contained Whitney smooth approximation
File: `Manifold/SmoothApproxChartContained.lean` (~600–1200 LOC).

Statement:
```
theorem exists_contMDiff_approx_of_continuous_chartContained
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X] [T2Space X]
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : K → X) (hf_cts : Continuous f)
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_contained : ∀ k : K, f k ∈ φ.source)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : K → X, ContMDiff (𝓘(ℝ, E)) (𝓘(ℂ, ℂ)) ω g ∧
      (∀ k, dist ((φ : X → ℂ) (g k)) ((φ : X → ℂ) (f k)) < ε) ∧
      (∀ k : K, g k ∈ φ.source)
```

Proof sketch:
1. Pull `f` back through `φ`: `φ ∘ f : K → ℂ` is continuous.
2. By mathlib's `Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le`,
   there's a smooth `g̃ : K → ℂ` with `dist (g̃ k) ((φ ∘ f) k) < ε`.
3. By choosing ε small enough (compactness of f(K) inside open φ.source +
   distance to ∂φ.target), `g̃` lands in `φ.target`.
4. Define `g := φ.symm ∘ g̃`. Smoothness comes from `contMDiffOn_symm_of_mem_maximalAtlas`.
5. Distance bound: ε can be chosen smaller than `dist (φ ∘ f K) ∂φ.target` by compactness.

Pre-reqs to check this session:
- Confirm mathlib's `Continuous.exists_contDiff_dist_le_*` matches our K (compact)
- Confirm chart-inverse smoothness in tree.

### Session 2 — Chart-cover Lebesgue subdivision + partition of unity
File: `Manifold/PartitionOfUnitySubdivision.lean` (~800–1500 LOC).

Statement: given a continuous `f : [0,1]ⁿ → X`, subdivide `[0,1]ⁿ` into
small cubes each chart-contained, build a smooth POU subordinate to the
cover, glue chart-contained smooth approximations.

This is the heart of manifold-valued Whitney. Standard but nontrivial.

Pre-reqs: mathlib's `SmoothPartitionOfUnity` infrastructure.

### Session 3 — Smooth Whitney for [0,1]ⁿ → X
File: `Manifold/SmoothApproxIntervalCube.lean` (~500–1000 LOC).

Composes sessions 1 + 2 into a clean theorem: any continuous
`f : [0,1]ⁿ → X` is uniformly close to a smooth `g : [0,1]ⁿ → X`.

Includes the "rel boundary" version: if `f` is already smooth on a
neighborhood of `∂[0,1]ⁿ`, the approximation preserves that.

### Session 4 — Continuous null-homotopy ⟹ smooth null-bordism
File: `Manifold/SmoothNullBordismOfContinuousNullHomotopy.lean` (~500–800 LOC).

Statement: on a complex 1-manifold X, a smooth loop γ with a continuous
null-homotopy to the constant loop has a smooth null-bordism (i.e.
`single γ ∈ stokesBoundaries 𝓘(ℝ, ℂ) X`).

Uses session 3's smooth approx applied to the null-homotopy disc, with
γ kept smooth on the boundary by the rel-boundary version.

### Session 5 — BSLB on simply-connected X (the actual T4)
File: `Manifold/BasedSmoothLoopsBoundOfSimplyConnected.lean` (~300–500 LOC).

Statement:
```
theorem basedSmoothLoopsBoundHypothesis_of_simplyConnected
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    [SimplyConnectedSpace X] (x₀ : X) :
    BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀
```

Proof: every smooth loop is continuously null-homotopic (mathlib's
`simply_connected_iff_loops_nullhomotopic`), then session 4 gives the
smooth null-bordism.

### Session 6 — Item-14 reverse leg unconditional
File: `Topology/Item14ReverseLegFromSimplyConnected.lean` (~200–400 LOC).

Composes: `(X ≃ₜ S²)` ⟹ `[SimplyConnectedSpace X]` ⟹ (session 5)
`BasedSmoothLoopsBoundHypothesis` ⟹ (existing chip-D-arc machinery)
`pathPrimitive` smooth + FTC ⟹ T5 (`liouvilleOnCompactConnected_holds`)
⟹ `om = 0` for all `om` ⟹ `genus X = 0`.

This closes the reverse leg of item 14 on arbitrary X. The forward leg
still needs T1 (Riemann–Roch), a separate multi-session arc.

## Estimated total LOC

~2.9k–5.6k LOC across 6 sessions for the T4 reverse-leg arc alone.

## What I will NOT do across these sessions

Per the anti-paraphrase gates in [`tools/chip-prompt-preamble.md`](tools/chip-prompt-preamble.md):
- No new named hypotheses (`class`, `structure`, `def Prop`).
- No "from N inputs" reformulations.
- No parallel routes / per-X-only instances.
- No chips that bridge named hypothesis A to named hypothesis B
  without proving classical content.

Each session ends with a substantive classical theorem closed on
arbitrary X, plus the working file's LOC measurement.

## Why not start session 1 right now in this turn

Because committing a partial session-1 file mid-turn with mixed
audit/code work would re-create the chip pattern. Session 1 deserves
its own focused turn (~600–1200 LOC of dedicated work).

When the user says "go", session 1 starts. Without that explicit signal,
this plan stands as the next-session entry point.
