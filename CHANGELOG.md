# Changelog

## 2026-05-13 — Period-lattice arc PL-1 closed + germfield arc to main

**Germfield arc (item 14 reduction)** — `2e5cfb4..main`:
- 9 chips landed reducing item 14's `genus_eq_zero_iff_homeo` from 5 named
  classical hypotheses to **one classical input**
  (`ExistsSimplePoleGermAtSomePoint X`) modulo the **structural typeclass**
  `[Subsingleton (HolomorphicOneForm X)]`.
- New files: `Manifold/MeromorphicFunctionField.lean`,
  `Manifold/MeromorphicFunctionGermCanonicalize.lean`,
  `Manifold/MeromorphicFunctionGermIdentityCorollary.lean`,
  `Topology/LinearSystemGermDeltaP.lean`,
  `Topology/RRDimensionFormGerm.lean`,
  `Topology/RRGenusZeroGermComposition.lean`,
  `Topology/RRStrictLtFromSimplePole.lean`,
  `Topology/Item14FromGermfield.lean`,
  `Topology/HTopFromSubsingleton.lean`.

**Period-lattice arc PL-1** — `60ba76d`, `df0227c`, `8f4e0a7`:

- `Manifold/ComplexManifoldRealification.lean` — bridging
  `instance complexManifoldRealification : IsManifold 𝓘(ℝ, ℂ) n X` from
  `[IsManifold 𝓘(ℂ, ℂ) ω X]`. Unblocks `SmoothOneForm 𝓘(ℝ, ℂ) X` as the
  ambient type for the real-side period pairing.
- `Manifold/HolomorphicOneFormRealComponent.lean` (400 LOC) — the bundled
  PL-1 step in full. Provides:
  - `realPartCLM`, `imagPartCLM : (ℂ →L[ℂ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℝ)` as
    bundled continuous **ℝ**-linear maps.
  - `tangentBundleCore_coordChange_restrictScalars_eq` — the two manifold
    structures' tangent transitions related by `restrictScalars ℝ`.
  - `cotangentBundleCore_coordChange_realPartCLM` / `_imagPartCLM` —
    cotangent coordinate change commutes with the fibrewise CLMs.
  - `ContMDiffAt_restrictScalars_to_real` — manifold-level scalar
    restriction bridge.
  - `realPart_section_contMDiff` / `_imag` — section smoothness over the
    real cotangent bundle.
  - `realComponent`, `imagComponent : HolomorphicOneForm X → SmoothOneForm
    𝓘(ℝ, ℂ) X` — the bundled deliverable.

  Recurring obstacle navigated throughout: the `NormedSpace ℝ ℂ` instance
  diamond (between `NormedSpace.complexToReal` priority-900 and
  `NormedAlgebra.toNormedSpace`) breaks `IsScalarTower.right`'s unifier
  whenever the synth context has `NormedSpace ℂ ℂ` resolved first. Pinned
  with `letI : NormedSpace ℝ ℂ := @NormedAlgebra.toNormedSpace ℝ ℂ _ _ _`
  per def at every `restrictScalars` site.

  Build: 8650 jobs, clean. PL-1 unblocks the holomorphic-side period
  pairing construction (PL-2).

## v0.1.0 (2026-04-26) — initial scaffold

- Repo scaffold (`lakefile.toml`, `lean-toolchain`, CI workflows, `.gitignore`).
- Mathlib pinned to commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (the
  exact rev Buzzard's challenge gist v0.3 specifies, dated 2026-04-15).
- `JacobianChallenge/Basic.lean` contains Buzzard's challenge signature
  verbatim; every `def`/`lemma`/`theorem` is `:= sorry`. Each `sorry`
  corresponds to one open item in `OPEN.md`.
- `DEVELOPMENT.md` carries the apfsd kernel-panic rules and CI-as-default
  workflow inherited from `sqg-lean-proofs` and `ns-lean-proofs`.
