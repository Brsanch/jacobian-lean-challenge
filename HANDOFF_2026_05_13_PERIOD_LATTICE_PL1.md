# Handoff 2026-05-13 — Period-lattice arc PL-1 + Germfield arc to main

Session HEAD: **`8f4e0a7`** (main). 5 pushes today, all CI-clean.

## What landed

### Germfield arc (item 14 reduction) — `2e5cfb4..main`

9 chips closing the architectural reduction of item 14's
`genus_eq_zero_iff_homeo` from 5 named classical hypotheses to **one
classical input** plus a structural typeclass:

- **Classical input:** `ExistsSimplePoleGermAtSomePoint X` — existence of a
  meromorphic germ with a single simple pole somewhere on `X`.
- **Structural typeclass:** `[Subsingleton (HolomorphicOneForm X)]` — `X`
  carries no nonzero holomorphic 1-forms (Hodge-theoretic content; an
  unconditional `instance` is supplied for `X = RiemannSphere` in
  `Manifold/HodgeRiemannSphereInstance.lean`).

The capstone is `genus_eq_zero_iff_homeo_from_existsSimplePoleGerm_and_subsingleton`
in `Topology/HTopFromSubsingleton.lean`, which delivers item 14's biconditional
from the single classical input plus the typeclass, with `h_top` discharged
vacuously.

### Period-lattice arc PL-1 — `60ba76d`, `df0227c`, `8f4e0a7`

Two new files closing the first chip of the Abel-Jacobi arc:

**`Manifold/ComplexManifoldRealification.lean`** (~135 LOC):
- `instance complexManifoldRealification : IsManifold 𝓘(ℝ, ℂ) n X` from
  `[ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]`.
- Route: `isManifold_of_contDiffOn` ← `ContDiffOn.of_le` ←
  `ContDiffOn.restrict_scalars` applied to the existing holomorphic
  chart-compatibility.

**`Manifold/HolomorphicOneFormRealComponent.lean`** (~400 LOC):
- `realPartCLM`, `imagPartCLM : (ℂ →L[ℂ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℝ)` — bundled
  fibrewise CLMs.
- `tangentBundleCore_coordChange_restrictScalars_eq` — `T_ℝ =
  T_ℂ.restrictScalars ℝ` for the two manifold structures' chart-transition
  derivatives.
- `cotangentBundleCore_coordChange_realPartCLM` / `_imagPartCLM` — the
  cotangent coordinate change commutes with the fibrewise CLMs.
- `realPart_chart_rep_eq_eventually` / `_imag` — packages the
  commutativity as a `Filter.EventuallyEq` around each point.
- `om_chart_rep_contMDiffAt_complex` — extracts the ℂ-chart-coord rep
  smoothness from `om`'s built-in section smoothness via
  `cotangentSection_contMDiffAt_iff`.
- `ContMDiffAt_restrictScalars_to_real` — manifold-level scalar
  restriction `ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, F) n f x₀ → ContMDiffAt 𝓘(ℝ, ℂ)
  𝓘(ℝ, F) n f x₀`.
- `realPart_section_contMDiff` / `_imag` — section smoothness over the
  real cotangent bundle.
- **Deliverable**: `realComponent`, `imagComponent : HolomorphicOneForm X
  → SmoothOneForm 𝓘(ℝ, ℂ) X`.

## Open instance hazards to keep in mind

1. **`NormedSpace ℝ ℂ` diamond**: `NormedSpace.complexToReal` has priority
   900; in many contexts it wins synth over `NormedAlgebra.toNormedSpace`
   and breaks `IsScalarTower.right`'s unifier. Fix: `letI : NormedSpace ℝ
   ℂ := @NormedAlgebra.toNormedSpace ℝ ℂ _ _ _` per def at every
   `restrictScalars` site. Recurs throughout `HolomorphicOneFormRealComponent`.

2. **`IsScalarTower ℝ ℂ (ℂ →L[ℂ] ℂ)`** does *not* synthesize automatically
   via `IsScalarTower.complexToReal` despite all required typeclass
   prerequisites being in scope. Worked around by proving manually with
   `ContinuousLinearMap.ext` + `smul_assoc r c (φ v)`.

3. **`TotalSpace.mk' F x (om.realPart x)`** defaults to the **trivial**
   bundle topology since `om.realPart x : ℂ →L[ℝ] ℝ` doesn't carry the
   cotangent fiber-bundle inference. Fix: explicit type ascription on the
   value AND the result:
   ```
   (TotalSpace.mk' (ℂ →L[ℝ] ℝ) x (om.realPart x : CotangentSpace 𝓘(ℝ, ℂ) x) :
     TotalSpace (ℂ →L[ℝ] ℝ) (CotangentSpace 𝓘(ℝ, ℂ)))
   ```

## What's next on the period-lattice arc

PL-2 (closed-chain restriction + Stokes-style boundary-invariance → factor
pairing through `H₁`): needs Stokes on Riemann surfaces, ~600-1,200 LOC.

PL-3 (rank-2g + discreteness of period lattice image): needs Riemann
bilinear relations + surface classification, ~1,500-3,000 LOC.

PL-4 (`Pic0 X ≃ AnalyticTorus X`, the Abel-Jacobi map proper): needs
PL-1, PL-2, PL-3, ~800-1,500 LOC.

See memory file `jacobian_period_lattice_arc.md` for the full multi-session
plan.

## Build status

8650 jobs, clean. `lake build` runs in ~36s incrementally.

## Session commits (in order)

1. `2e5cfb4` — Germfield arc merge: Item 14 from 1 classical input + Subsingleton.
2. `60ba76d` — `complexManifoldRealification` manifold-structure bridging.
3. `df0227c` — `realPartCLM` / `imagPartCLM` bundled `ℝ`-linear maps.
4. `8f4e0a7` — Bundled `realComponent` / `imagComponent` with full section smoothness.
