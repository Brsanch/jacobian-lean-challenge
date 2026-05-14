/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphereSimplePole
import JacobianChallenge.Topology.MeromorphicNonzeroBuilder

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `MeromorphicNonzero RiemannSphere` for `RSSimplePole`

Packages the previously-built `RSSimplePole : RiemannSphere → ℂ`
(`Manifold/RiemannSphereSimplePole.lean`) as a `MeromorphicNonzero
RiemannSphere`. This is the first non-trivial principal-divisor
generator on the Riemann sphere: `principalDivisorMap` of this
function lands at `δ_{some 0} - δ_∞` (a single zero at `some 0`,
a simple pole at `∞`).

## Why this matters

`Subsingleton (Pic0 RiemannSphere)` — the classical `Pic⁰(ℙ¹) = 0`
— says every degree-0 divisor on RS is principal. The general
discharge constructs an explicit meromorphic representative for
each `D : Div0 RS`. This file lands the foundational generator
`δ_{some 0} - δ_∞`. Translations of this function recover
`δ_{some a} - δ_∞` for any `a : ℂ`, and inversion recovers
`δ_∞ - δ_{some a}`; together these generate `Div0 RS` as an
`AddSubgroup` (via the standard decomposition `D = Σ n_i (δ_{p_i}
- δ_{p_0})` with `Σ n_i = 0`).

## What ships

* `mnRSSimplePole : MeromorphicNonzero RiemannSphere` — the bundled
  packaging of `RSSimplePole`. Uses
  `MeromorphicNonzero.ofRegularContinuous` since `RSSimplePole` is
  *not* globally continuous (junk value `0` at `∞`, but continuous
  at every finite point, where the order is `≥ 0`).

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Filter Set OnePoint

namespace JacobianChallenge

/-- **Continuity of `RSSimplePole` at every finite point.** Near
`some z₀ : RiemannSphere`, the function locally agrees with the
coe-restriction `z ↦ z` (via the chartN inclusion `ℂ ↪ RiemannSphere`),
which is continuous. -/
lemma RSSimplePole_continuousAt_coe (z₀ : ℂ) :
    ContinuousAt RSSimplePole ((z₀ : RiemannSphere)) := by
  -- The coercion `(↑) : ℂ → RiemannSphere = OnePoint ℂ` is an open embedding,
  -- so `𝓝 (z₀ : RS) = Filter.map ↑ (𝓝 z₀)`.
  have h_nhds : 𝓝 ((z₀ : ℂ) : RiemannSphere)
      = Filter.map ((↑) : ℂ → RiemannSphere) (𝓝 z₀) :=
    ((OnePoint.isOpenEmbedding_coe (X := ℂ)).map_nhds_eq z₀).symm
  rw [ContinuousAt, h_nhds, Filter.tendsto_map'_iff]
  -- Goal: Tendsto (RSSimplePole ∘ (↑)) (𝓝 z₀) (𝓝 (RSSimplePole ↑z₀)).
  -- The composite `RSSimplePole ∘ ↑` is `id : ℂ → ℂ` by definition of RSSimplePole.
  have h_eq : (RSSimplePole ∘ ((↑) : ℂ → RiemannSphere)) = id := by
    funext z; rfl
  rw [h_eq]
  -- `RSSimplePole (↑z₀) = z₀`.
  show Filter.Tendsto (id : ℂ → ℂ) (𝓝 z₀) (𝓝 z₀)
  exact tendsto_id

/-- **`MeromorphicNonzero RiemannSphere` packaging of `RSSimplePole`.**
The underlying function is `some z ↦ z`, `∞ ↦ 0`, with a simple
zero at `some 0` and a simple pole at `∞`.

* `meromorphic`: `RSSimplePole_mmeromorphicOn`.
* `nonvanishing_germ`: order is `-1` at `∞` (a finite integer)
  and `≥ 0` at finite points, hence `≠ ⊤` everywhere.
* `regular_continuousAt`: at non-pole points (finite), continuity
  of `RSSimplePole` via `RSSimplePole_continuousAt_coe`. At `∞`,
  the order is `-1 < 0`, so the hypothesis is vacuous. -/
noncomputable def mnRSSimplePole :
    MeromorphicNonzero RiemannSphere :=
  MeromorphicNonzero.ofRegularContinuous
    (g := RSSimplePole)
    (h_mero := RSSimplePole_mmeromorphicOn)
    (h_nonvanish := by
      intro x
      induction x using OnePoint.rec with
      | infty =>
        rw [RSSimplePole_orderAt_infty]
        decide
      | coe z =>
        -- Order at finite point: chart pullback is `id`, and `id` is
        -- eventually nonzero in `𝓝[≠] z`.
        show mmeromorphicOrderAt 𝓘(ℂ, ℂ) RSSimplePole (z : RiemannSphere) ≠ ⊤
        show meromorphicOrderAt (RSSimplePole ∘ (chartAt ℂ (z : RiemannSphere)).symm)
              ((chartAt ℂ (z : RiemannSphere)) (z : RiemannSphere)) ≠ ⊤
        have h_chart : (chartAt ℂ ((z : RiemannSphere)) : OpenPartialHomeomorph RiemannSphere ℂ)
              = RiemannSphere.chartN := rfl
        rw [h_chart, RSSimplePole_comp_chartN_symm, RiemannSphere.chartN_apply_coe]
        rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero analyticAt_id.meromorphicAt]
        -- Goal: ∀ᶠ w in 𝓝[≠] z, id w ≠ 0
        -- Equivalently: w ≠ 0 eventually in 𝓝[≠] z.
        rcases eq_or_ne z 0 with rfl | hz
        · -- z = 0: punctured nbhd of 0 excludes 0, so id w = w ≠ 0 there.
          filter_upwards [self_mem_nhdsWithin] with w hw using hw
        · -- z ≠ 0: id w = w → z ≠ 0 by continuity; eventually ≠ 0 in 𝓝 z.
          have h_ev : ∀ᶠ w in 𝓝 z, (id w : ℂ) ≠ 0 :=
            continuousAt_id.eventually_ne hz
          exact h_ev.filter_mono nhdsWithin_le_nhds)
    (h_reg_cts := by
      intro x _hreg
      induction x using OnePoint.rec with
      | infty =>
        -- At ∞ the hypothesis is `0 ≤ -1`, which is false; vacuously fine.
        -- But we still need `ContinuousAt RSSimplePole ∞` for the structure to
        -- typecheck. We pick up the conclusion vacuously. — Actually `_hreg`
        -- is `0 ≤ mmeromorphicOrderAt RSSimplePole ∞ = -1`, false. So
        -- `_hreg.elim` extracts whatever we need... but the goal type is
        -- `ContinuousAt RSSimplePole ∞`. We get this from `_hreg`'s falsity:
        exfalso
        have h_neg : mmeromorphicOrderAt 𝓘(ℂ, ℂ) RSSimplePole (∞ : RiemannSphere)
            = ((-1 : ℤ) : WithTop ℤ) := RSSimplePole_orderAt_infty
        rw [h_neg] at _hreg
        exact absurd _hreg (by decide)
      | coe z =>
        exact RSSimplePole_continuousAt_coe z)

@[simp] lemma mnRSSimplePole_toFun :
    (mnRSSimplePole : MeromorphicNonzero RiemannSphere).toFun = RSSimplePole := rfl

end JacobianChallenge

end
