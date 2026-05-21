/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasSurfaceClassificationData

set_option linter.unusedSectionVars false

/-! # Bryan-tree analog of `AX_AnalyticCycleBasis` (mrdouglasny axiom #1)

The first axiom in `mrdouglasny/jacobian-challenge`'s axiom inventory is

> `AX_AnalyticCycleBasis x₀ : Nonempty (AnalyticCycleBasis X x₀)`

asserting that every compact connected complex 1-manifold admits a
piecewise-real-analytic symplectic ℤ-basis of `H_1(X; ℤ)`. This is the
classical content packaged by **Forster, Ch. III §16** + **Griffiths-
Harris, Ch. 0.4**.

## Bridge to Bryan's tree

Bryan's tree already names this content at the **smooth** (not piecewise-
real-analytic) level via:

* `SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ g` — data of `2g` based smooth
  loops at `p₀`.
* `SmoothHurewiczHypothesis sb` — named Prop: every smooth based loop
  is a ℤ-combination of `sb.cycleGens` modulo `stokesBoundaries`.
* `SurfaceClassificationData X` (chip 1) — bundles the two:
  `basePoint + symplecticBasis + hurewicz`.
* `HasSurfaceClassificationData X` (chip 3) — typeclass:
  `Nonempty (SurfaceClassificationData X)`.

The smooth version is **strictly weaker** than mrdouglasny's
piecewise-real-analytic version (since smooth loops include
piecewise-real-analytic ones), so a piecewise-real-analytic discharge
would supply the smooth one immediately. Conversely, the smooth
version suffices for every downstream consumer in Bryan's tree that
currently feeds the period-lattice / Abel-Jacobi / Riemann-bilinear
chain (chips 19/20/22/24/25), because chart-local analytic integration
is replaced by smooth-cycle pushforward + Stokes-on-2-chains (which
Bryan has unconditionally via chip D).

The intersection-form / symplectic-condition piece of mrdouglasny's
`AX_AnalyticCycleBasis` is split off as `AX_IntersectionForm`
(mrdouglasny axiom #9). Bryan's tree does not yet supply an
intersection form on `H_1(X; ℤ)`; the symplectic structure is encoded
*indirectly* via the bilinear period matrix `pmat (sb.cycleGens) ω`
landing in `SiegelUpperHalfSpace g` (chips 23/24's RSRP).

## Status of the discharge at general genus

* **`g = 0` (Riemann sphere):** `Nonempty (SurfaceClassificationData
  RiemannSphere)` is **unconditional** via chip 1's
  `surfaceClassificationData_RiemannSphere`, which uses the empty
  symplectic basis `Fin 0 → SmoothPath` + the unconditional
  `basedSmoothLoopsBoundHypothesis_RS_holds`.
* **`g = 1` (complex torus `T_L = ℂ ⧸ L`):** `Nonempty
  (SurfaceClassificationData (ℂ ⧸ L))` is **unconditional** via chip
  2's `surfaceClassificationData_complexTorus`, which uses
  `symplecticBasisG L = (symplecticBasis L lam₁ lam₂ _ _).reindex
  (genus_eq_one L)` + the unconditional
  `smoothHurewiczHypothesisTorus_holds_of_basis`.
* **General `g` (any compact connected complex 1-manifold):** **OPEN.**
  Discharge requires one of three classical routes (per mrdouglasny's
  file header):

  1. **(P1) Radó triangulation + surface classification** — every
     compact connected oriented topological 2-manifold of genus `g`
     admits a triangulation whose 1-skeleton includes a standard 4g-gon
     edge presentation `∏_i [α_i, β_i] = 1`; the `α_i, β_i` edges'
     homology classes form a symplectic ℤ-basis of `H_1`. **Mathlib
     does not have:** Radó's theorem (manifold triangulation) or the
     surface classification theorem.

  2. **(P2) Riemann-Roch + algebraic embedding** — every compact
     Riemann surface is projective (Riemann/Kodaira), giving an
     algebraic triangulation pulled back from `ℙ^N`. **Mathlib does
     not have:** divisors on Riemann surfaces, ampleness, sheaf
     cohomology, Riemann-Roch.

  3. **(P3) Morse theory + gradient flow** — choose a real-analytic
     Morse function `f : X → ℝ` with distinct critical values; the
     stable/unstable manifolds of the `2g` index-1 critical points
     give a piecewise-real-analytic ℤ-basis of `H_1`. **Mathlib has
     partial:** basic Morse-lemma machinery; **not in Mathlib:** the
     CW-structure-from-Morse theorem on manifolds.

  All three routes are open multi-month subprojects. The chip-31
  pre-amble of the Bryan no-axiom path is to land the bridge below;
  subsequent chips attack one of (P1)/(P2)/(P3) incrementally.

## What this file ships

* `AnalyticCycleBasisHypothesis X : Prop` — the named Prop matching
  mrdouglasny's `AX_AnalyticCycleBasis`, definitionally equal to
  `Nonempty (SurfaceClassificationData X)`.
* `AnalyticCycleBasisHypothesis.of_hasSurfaceClassificationData` /
  `.to_hasSurfaceClassificationData` — the trivial biconditional with
  the typeclass form.
* `AnalyticCycleBasisHypothesis.RiemannSphere` /
  `.complexTorus L` — RS and T_L unconditional discharges.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`AnalyticCycleBasisHypothesis X`** — Bryan-tree analog of
`mrdouglasny/jacobian-challenge`'s `AX_AnalyticCycleBasis`.

Existence of an `X`-symplectic-basis with smooth-Hurewicz, packaged
through Bryan's `SurfaceClassificationData X` bundle. At the smooth
level — a strictly weaker hypothesis than the piecewise-real-analytic
form of `AX_AnalyticCycleBasis`, but sufficient for every in-tree
downstream consumer (period-lattice, Abel-Jacobi, Riemann-bilinear). -/
def AnalyticCycleBasisHypothesis (X : Type u) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X] : Prop :=
  Nonempty (SurfaceClassificationData X)

/-- **From the typeclass form** `[HasSurfaceClassificationData X]`. -/
theorem AnalyticCycleBasisHypothesis.of_hasSurfaceClassificationData
    [HasSurfaceClassificationData X] :
    AnalyticCycleBasisHypothesis X :=
  HasSurfaceClassificationData.out

/-- **To the typeclass form.** Constructs `HasSurfaceClassificationData
X` from the named hypothesis. (Provided as a lemma so downstream
constructions parameterised by the named Prop can use typeclass
dispatch when needed.) -/
theorem AnalyticCycleBasisHypothesis.to_hasSurfaceClassificationData
    (h : AnalyticCycleBasisHypothesis X) :
    HasSurfaceClassificationData X :=
  ⟨h⟩

/-! ## RS unconditional discharge (genus 0) -/

namespace RiemannSphere

/-- **`AnalyticCycleBasisHypothesis RiemannSphere` is unconditional.**

Via the chip 3 instance `instHasSurfaceClassificationData_RiemannSphere`,
using the empty symplectic basis at genus 0. -/
theorem analyticCycleBasisHypothesis_RiemannSphere :
    AnalyticCycleBasisHypothesis RiemannSphere :=
  AnalyticCycleBasisHypothesis.of_hasSurfaceClassificationData

end RiemannSphere

/-! ## T_L unconditional discharge (genus 1) -/

namespace ComplexTorus

variable (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- **`AnalyticCycleBasisHypothesis (ℂ ⧸ L)` is unconditional.**

Via the chip 3 instance `instHasSurfaceClassificationData_complexTorus`,
which packages the explicit `symplecticBasisG L` + the unconditional
`smoothHurewiczHypothesisTorus_holds_of_basis` discharge. -/
theorem analyticCycleBasisHypothesis_complexTorus :
    AnalyticCycleBasisHypothesis (ℂ ⧸ L) :=
  AnalyticCycleBasisHypothesis.of_hasSurfaceClassificationData

end ComplexTorus

end JacobianChallenge

end
