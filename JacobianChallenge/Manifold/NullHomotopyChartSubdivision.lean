/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathHomotopyFromSimplyConnected
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Complex.Basic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Chart-subdivision of a continuous null-homotopy

For a continuous null-homotopy `H : I × I → X` of a smooth loop on a
complex 1-manifold `X`, this file packages the foundational
combinatorics: there exists a finite `N × N` subdivision of the unit
square such that **each subcell's image under `H` is contained in a
single chart-source of `X`**.

This is the geometric setup for the Cauchy-Goursat–based discharge of
`LoopPeriodVanishes`: on each subcell, the boundary maps to a loop in
a chart; within the chart, the chart-pulled-back loop integral of a
holomorphic 1-form vanishes by Cauchy-Goursat; summing over subcells,
internal edges cancel by orientation, leaving the original loop
integral = 0.

## Main content

* `subdivide_null_homotopy_through_charts` — for any continuous map
  `H : I × I → X` into a complex 1-manifold and any chart cover of
  `X`, produce a monotone subdivision `t : ℕ → I` of `[0,1]` such that
  each subcell `[t n, t (n+1)] × [t m, t (m+1)]` maps under `H` into
  a single chart-source.

The proof is a direct application of mathlib's
`exists_monotone_Icc_subset_open_cover_unitInterval_prod_self` with
the open cover induced by `H⁻¹` of the chart sources.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology unitInterval

noncomputable section

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Chart-subdivision of a continuous map `I × I → X`.**

Given a continuous `H : I × I → X` and any point-indexed family of
chart sources covering `X`, there exists a monotone subdivision of
`[0, 1]` such that each rectangle `[t n, t (n+1)] × [t m, t (m+1)]`
maps under `H` into a single chart-source.

This is the unit-square version of the standard `Lebesgue-number`
lemma for compact open covers, applied to the pulled-back chart cover. -/
theorem subdivide_continuous_through_charts
    (H : I × I → X) (hH : Continuous H) :
    ∃ t : ℕ → I, t 0 = 0 ∧ Monotone t ∧ (∃ n, ∀ m ≥ n, t m = 1) ∧
      ∀ n m, ∃ p : X,
        Set.Icc (t n) (t (n + 1)) ×ˢ Set.Icc (t m) (t (m + 1))
          ⊆ H ⁻¹' (chartAt ℂ p).source := by
  -- Open cover of `I × I`: for each chart base point `p : X`,
  -- the preimage of `(chartAt ℂ p).source` under `H` is open.
  -- The family is indexed by `X` itself (with the trivial open chart at each point).
  set cover : X → Set (I × I) := fun p => H ⁻¹' (chartAt ℂ p).source
  have hcover_open : ∀ p : X, IsOpen (cover p) := fun p =>
    (chartAt ℂ p).open_source.preimage hH
  have hcover_univ : Set.univ ⊆ ⋃ p : X, cover p := by
    intro ⟨s, t⟩ _
    simp only [Set.mem_iUnion]
    -- For any point in `I × I`, its image `H ⟨s, t⟩` lies in its own chart source.
    exact ⟨H ⟨s, t⟩, mem_chart_source ℂ (H ⟨s, t⟩)⟩
  -- Apply mathlib's unit-square subdivision lemma.
  obtain ⟨t, h0, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self
      hcover_open hcover_univ
  -- Repackage: for each (n, m), the rectangle is contained in `cover p_nm` for some `p_nm : X`.
  refine ⟨t, h0, hmono, ⟨n, hn⟩, ?_⟩
  intro k l
  obtain ⟨p, hp⟩ := hsub k l
  exact ⟨p, hp⟩

end JacobianChallenge

end
