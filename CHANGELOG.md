# Changelog

## 2026-05-14 — A2 closed + genus-0 RR chain unconditional (modulo uniformization)

Merges `feat/antipode-smoothness` (parallel branch off `main`) into
the linear-system-divisor trunk and composes with the A1 discharge
that landed earlier today. The genus-0 Riemann–Roch `dim_ℂ L(δp) ≥
2` chain on the germ field is now reduced to exactly **one** named
classical input — uniformization at genus 0.

New files merged from `feat/antipode-smoothness` (660 LOC total):

* `Manifold/RiemannSphereAntipodeSmooth.lean` (255 LOC) — discharges
  the `contMDiff_antipode_TODO` follow-up from
  `RiemannSphereMobius.lean`: `ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω antipode` via
  `contMDiffAt_iff_of_mem_source` on the three-case `OnePoint.rec`
  split (chart pairs at `∞`, at `coe 0`, and at `coe w` with `w ≠
  0`; chart-coord maps `z ↦ -z` for the first two and `z ↦ -z⁻¹`
  for the third). Packages as `antipodeEquiv : HolomorphicEquiv RS RS`
  (self-inverse).
* `Manifold/RiemannSphereTranslate.lean` (322 LOC) — `translateBy c`
  on RS (fixing `∞`, `coe z ↦ coe (z + c)`) as `ContMDiff 𝓘(ℂ) 𝓘(ℂ)
  ω` and packaged as `translateEquiv c : HolomorphicEquiv RS RS`
  with inverse `translateEquiv (-c)`.
* `Manifold/MobiusTransitivityRS.lean` (80 LOC) —
  `RiemannSphere.existsMobiusToInftyRS`: ∀ `p : RS`, ∃ `e :
  HolomorphicEquiv RS RS`, `e p = ∞`. Concrete witnesses: identity
  for `p = ∞`; `translateEquiv(-z₀).trans antipodeEquiv` for `p =
  coe z₀` (sending `coe z₀ ↦ coe 0 ↦ ∞`).

New trunk-side file (this commit):

* `Topology/LinearSystemGermDeltaPFiniteDimRSUnconditional.lean`
  (109 LOC) — composes the two unconditional discharges:
  - `existsMobiusToInftyRS_holds : ExistsMobiusToInftyRS` — 1-line
    bridge identifying the in-tree theorem with the named-hypothesis
    Prop (definitionally equal, `rfl`-level).
  - `linearSystemGermDeltaPFiniteDim_RiemannSphere_unconditional :
    LinearSystemGermDeltaPFiniteDim RiemannSphere` — the headline,
    no hypothesis.
  - `rr_DimGE2_GenusZero_Germ_of_uniformization_unconditional_RSFiniteDim`
    — for any compact connected complex 1-manifold `X`, genus-0 RR
    dim ≥ 2 on the germ field reduces to genus-conditional
    uniformization alone.

**Net post-this-commit state.** The genus-0 RR `dim_ℂ L(δp) ≥ 2`
content on:

* **`RiemannSphere`**: **unconditional**.
* **Arbitrary compact connected complex 1-manifold `X`**: depends on
  **one** named classical input — `genus X = 0 → Nonempty
  (HolomorphicEquiv X RiemannSphere)` (uniformization at genus 0).

Build: 8700 jobs clean. Zero `sorry`, zero `axiom`.

## 2026-05-14 — `feat/c1-smooth-path-connected` merged: SmoothPathConnected predicate + linearInChart (ω-level)

Two-commit branch off `main` (`d97dcd5..c189052`) merged into
`feat/linear-system-divisor` after the A1 discharge below. Net +371
LOC, two new files in `JacobianChallenge/Manifold/`, zero `sorry`,
zero `axiom`. Full `taskpolicy lake build` green post-merge (8696
jobs). Disjoint from the linear-system-divisor RR work: files live
in `Manifold/SmoothPath*` only.

**Smooth-path-connectedness layer** — `Manifold/SmoothPathConnected.lean`
(177 LOC):

- `SmoothPathConnected I X : Prop` — every two points of `X` joined
  by a `SmoothPath I X`; smooth analogue of mathlib's
  `PathConnectedSpace`.
- `SmoothPathConnected.diagonal` — the `p = p` case is uniform via
  `SmoothPath.const`.
- `AbelJacobiInput.ofSmoothPathConnected` — constructor producing
  the bundle from `SmoothPathConnected 𝓘(ℝ, ℂ) X` + a chosen base
  point. Path-picker via `Classical.choose`.
- `AbelJacobiInput.nonempty_of_smoothPathConnected` — packaging:
  `Nonempty X + SmoothPathConnected 𝓘(ℝ, ℂ) X ⇒ Nonempty
  (AbelJacobiInput α h)`.
- `AbelJacobiInput.exists_smoothPath_from_basePoint` — one-sided
  back-projection.

Splits the `AbelJacobiInput α h` named-hypothesis bundle along a
textbook fault line: from "base point + per-target picker" down to
the classical predicate plus `Nonempty X`. CLOSURE_MAP §F.5 step 2
(C1) now factors through `SmoothPathConnected` as a single citable
classical input.

**Linear-in-chart primitive** — `Manifold/SmoothPathLinearInChart.lean`
(192 LOC):

- `affineSegment a b t = (1 - t) • a + t • b` — affine map `ℝ → ℂ`
  with `affineSegment_zero/one` endpoint identities.
- `contDiff_affineSegment` / `contMDiff_affineSegment` — affine maps
  are `C^ω`; manifold-side lift via `contMDiff_iff_contDiff`.
- `SmoothPath.linearInChart φ h_atlas p q hp hq h_line` — constructor
  of a `SmoothPath 𝓘(ℝ, ℂ) X` between `p, q` whose chart-coordinate
  line `{(1-t) • φ p + t • φ q : t ∈ ℝ}` lies entirely in
  `φ.target`. Ambient `t ↦ φ.symm (affineSegment (φ p) (φ q) t)`,
  smooth at ω-regularity via `contMDiffAt_symm_of_mem_maximalAtlas
  ∘ contMDiff_affineSegment`.
- `SmoothPath.linearInChart_src` / `_tgt` — endpoint identities.

**ω-level structural finding** (documented in the file's docstring
and accompanying commit):

The `SmoothPath` structure demands `ContMDiff 𝓘(ℝ, ℝ) I ⊤ f` with
`⊤ : WithTop ℕ∞`, which mathlib's `Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries`
notes equals `ω` (analytic). Globally analytic functions are
germ-determined, so the standard `C^∞` trick of smoothly extending
by constants outside `[0, 1]` does *not* produce an analytic path.
This forces `linearInChart` to require the *entire chart-coordinate
line* (not merely the segment) in `φ.target`. The hypothesis is
unconditional on the affine chart of `RiemannSphere` (target = ℂ);
on a generic Riemann surface chart with bounded target it fails.
Closing the "segment-only" case at the ω level genuinely requires
either changing the `SmoothPath` definition (downgrade to `C^∞`) or
an analytic-continuation argument; neither is in scope of this chip.

**Net post-this-merge state.** CLOSURE_MAP §F.5 step 2 (C1
`AbelJacobiInput`) factors through `SmoothPathConnected 𝓘(ℝ, ℂ) X +
Nonempty X`, with `linearInChart` as the first chart-side primitive.
Full chart-cover discharge remains open.

## 2026-05-14 — A1 closed: `LinearSystemAtInftyRS_BoundedBySimplePoleSpan` discharged

Two new files (~870 LOC total) discharging the polynomial-growth
Liouville bound at `∞` on the Riemann sphere, the first of the two
remaining classical inputs in the genus-0 RR `dim_ℂ L(δp) ≥ 2`
chain.

`Analysis/PolynomialLiouville.lean` (~180 LOC) — foundational
mathlib-style lemma: an entire `f : ℂ → ℂ` with `‖f z‖ ≤ C ‖z‖` for
`‖z‖ ≥ R₀` is an affine function `f z = f 0 + (deriv f 0) · z`.
Proven via the Cauchy first-derivative estimate
(`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`) plus basic
Liouville (`Differentiable.exists_const_forall_eq_of_bounded`) and
constancy from zero derivative (`is_const_of_deriv_eq_zero`).

`Topology/LinearSystemAtInftyRSDischarge.lean` (~690 LOC) —
discharge of `LinearSystemAtInftyRS_BoundedBySimplePoleSpan` for an
arbitrary germ in `linearSystemGermDeltaP (∞ : RS)`:

1. Affine-chart restriction `affineChartFun f := f.toFun ∘ some`,
   with `mmeromorphicOrderAt (some z) = meromorphicOrderAt
   (affineChartFun f) z`.
2. Entire normal-form representative `entireRep f := toMeromorphicNFOn
   (affineChartFun f) Set.univ`, analytic on all of `ℂ` by
   `MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd`.
3. Linear growth bound at infinity: `id ∘ (f ∘ chartS.symm)` has
   order `≥ 0` at `0` (additivity), so bounded near `0` by
   `tendsto_nhds_of_meromorphicOrderAt_nonneg`. Translating via the
   substitution `w = z⁻¹` gives `‖entireRep f z‖ ≤ M ‖z‖` for `‖z‖`
   large (limit-comparison lift across continuity).
4. Polynomial Liouville: `entireRep f w = a + b w` for all `w`.
5. Germ identity at `some 0`: `f.toFun =ᶠ[𝓝[≠] (some 0)] (a + b ·
   RSSimplePole)` by composing the chart-side EvEq with the
   polynomial identity.
6. Identity theorem (`mmeromorphicOrderAt_ne_top_forall`):
   single-point germ identity propagates globally to all of RS.
7. Final: `mk f = a • 1 + b • RSSimplePoleGerm ∈ span ℂ {1,
   RSSimplePoleGerm}`.

**Net post-this-commit state.** `LinearSystemGermDeltaPFiniteDim
RiemannSphere` reduces to a single remaining classical input
(`ExistsMobiusToInftyRS` — Möbius transitivity on RS). Combined
with uniformization at genus 0, the genus-0 RR `dim_ℂ L(δp) ≥ 2`
chain reduces to **two** named classical inputs: uniformization +
Möbius transitivity. Build: 8694 jobs clean (pre-C1 merge). Zero
`sorry`, zero `axiom`.

## 2026-05-14 — RS-FiniteDim architectural reduction (feat/linear-system-divisor cont.)

New file `Topology/LinearSystemGermDeltaPFiniteDimRSFromInputs.lean`
(~210 LOC) architecturally reduces `LinearSystemGermDeltaPFiniteDim
RiemannSphere` (the second of the two remaining classical inputs in
the genus-0 RR `dim_ℂ L(δp) ≥ 2` chain) to **exactly two** named
classical inputs:

1. `LinearSystemAtInftyRS_BoundedBySimplePoleSpan` — polynomial-growth
   Liouville bound at `∞`: `linearSystemGermDeltaP (∞ : RS) ≤
   Submodule.span ℂ {1, RSSimplePoleGerm}`. Classical content: entire
   `ℂ → ℂ` with `|f| = O(|z|)` at ∞ is a polynomial of degree ≤ 1.
   Mathlib at the pin has basic Liouville
   (`Complex.liouville_theorem_aux`) but not the polynomial-growth
   extension; Cauchy-estimate-based proof.
2. `ExistsMobiusToInftyRS` — Möbius transitivity on RS: ∀ `p : RS`,
   `∃ e : HolomorphicEquiv RS RS, e p = ∞`. Concrete witnesses are
   identity (for `p = ∞`) and antipode-composed-with-translation
   (for finite `p = z₀`); packaging requires checking smoothness on
   the two-chart atlas.

Helpers:
- `linearSystemGermDeltaP_finite_of_holomorphicEquiv` — per-point
  version of the existing `LinearSystemGermDeltaPFiniteDim.of_holomorphicEquiv`
  (the ∀-quantified one). Direct `Module.Finite.equiv` wrap of
  `linearSystemGermDeltaPLinearEquiv_via_holomorphicEquiv`.
- `linearSystemGermDeltaP_finite_of_le_span_pair` — pure linear-algebra:
  `L(δp) ≤ span ℂ {1, ψ} ⇒ Module.Finite ℂ (L(δp))`. Proof via
  `Module.Finite.span_of_finite` + `Module.Finite.of_injective` on
  `Submodule.inclusion`.

Headline `linearSystemGermDeltaPFiniteDim_RiemannSphere` composes the
two: the polynomial bound gives finiteness at `∞`; transitivity
transports it to every `p` via per-point transport.

**Post-this-commit state.** Combined with the existing
`feat/linear-system-divisor` branch, the genus-0 RR `dim_ℂ L(δp) ≥ 2`
on the germ field reduces to exactly **three** named classical inputs:
(i) uniformization at genus 0 (`genus X = 0 → Nonempty (HolomorphicEquiv
X RS)`), (ii) `LinearSystemAtInftyRS_BoundedBySimplePoleSpan`
(polynomial-growth Liouville on RS at ∞), (iii) `ExistsMobiusToInftyRS`
(Möbius transitivity on RS). All three are citable textbook content;
(ii) and (iii) are smaller-scale than (i) (which is full uniformization
theory). Zero `sorry`, zero `axiom`.

## 2026-05-14 — `feat/linear-system-divisor` branch (germ-field RR layer)

15-commit branch (`957fdd0..380ac85`) building the full architectural
reduction for genus-0 RR `dim_ℂ L(δp) ≥ 2` on the germ field. Net
+2807 LOC, zero `sorry`, zero `axiom`. After this branch, the
content reduces to exactly two classical inputs: (i) uniformization at
genus 0, and (ii) `LinearSystemGermDeltaPFiniteDim RiemannSphere`.

**L(D) ambient on the germ field** (closes the architectural issue
flagged earlier — pointwise `linearSystemDeltaP` was vacuously infinite
via "blip" elements):
- `Topology/LinearSystemDivisor.lean` — `linearSystemDivisor D :
  Submodule ℂ (MeromorphicFunctionGerm X)` for any `D : Div X`, with
  closure under `zero`/`add`/`smul`. Specialises to
  `linearSystemGermDeltaP p` at `D = Div.single p`.
- `Topology/LinearSystemDivisorConstants.lean` — `constantsToLinearSystemDivisor`
  for effective `D`, with injectivity under `ConnectedSpace`.
- `Topology/LinearSystemDivisorMono.lean` — monotonicity in `D`.
- `Topology/LinearSystemDivisorMul.lean` — multiplicative grading
  `L(D₁) · L(D₂) ⊆ L(D₁ + D₂)`.

**Dim-bound layer**:
- `Topology/LinearSystemDivisorZeroLiouville.lean` —
  `linearSystemDivisor 0 = constantsGerm X` and
  `finrank_linearSystemDivisor_zero_eq_one` (UNCONDITIONAL via
  the existing `liouvilleOnCompactConnected_holds`).
- `Topology/LinearSystemDivisorSimplePoleRank.lean` —
  `LinearIndependent ℂ ![1, ψ]` from a simple-pole germ, then
  `2 ≤ Module.rank ℂ (linearSystemGermDeltaP p)` (unconditional) and
  `RR_DimGE2_GenusZero_Germ` discharge from `ExistsSimplePoleGerm` +
  `LinearSystemGermDeltaPFiniteDim` (named hypothesis added).

**Existence side — RS base case + transport**:
- `Manifold/RiemannSphereSimplePole.lean` — explicit `RSSimplePole :
  RiemannSphere → ℂ` (`some z ↦ z`, `∞ ↦ 0`), packaged as
  `RSSimplePoleGerm` with simple pole at `∞`. Discharges
  `ExistsSimplePoleGermAtSomePoint RiemannSphere` UNCONDITIONALLY.
- `Manifold/MMeromorphicHolomorphicEquivTransport.lean` —
  `mmeromorphicOrderAt` preservation through a `HolomorphicEquiv`
  (composes existing `contMDiff_omega_analyticAt_chart_pullback` +
  `deriv_chart_pullback_ne_zero_of_injective` + mathlib's
  `meromorphicOrderAt_comp_of_deriv_ne_zero`).
- `Topology/ExistsSimplePoleGermFromHolomorphicEquivRS.lean` —
  `Nonempty (HolomorphicEquiv X RS) → ExistsSimplePoleGermAtSomePoint X`.

**Finite-dim side — transport**:
- `Manifold/MeromorphicFunctionGermHolomorphicEquivPullback.lean` —
  germ-field pullback `MeromorphicFunctionGerm Y → MeromorphicFunctionGerm
  X` via composition with `e`, preserving `orderAt`.
- `Topology/LinearSystemGermDeltaPHolomorphicEquivTransport.lean` —
  `IsBoundedByDeltaPGerm` iff under pullback; bundled `LinearMap`
  between `L(δ(e p))` and `L(δp)`.
- `Topology/LinearSystemGermDeltaPFiniteDimTransport.lean` —
  `LinearEquiv` packaging + `Module.Finite.equiv` to transport
  `LinearSystemGermDeltaPFiniteDim`.

**Final assembly**:
- `Topology/RRDimGE2FromUniformizationAndFiniteDim.lean` /
  `Topology/RRDimGE2FromUniformizationAndFiniteDimRS.lean` —
  `rr_DimGE2_GenusZero_Germ_of_uniformization_and_RSFiniteDim` and
  variants. Headline assembly.

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
