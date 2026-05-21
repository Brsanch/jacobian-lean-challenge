/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasConvexTargetChartCover
import JacobianChallenge.Manifold.SmoothChain
import Mathlib.Topology.UnitInterval

set_option linter.unusedSectionVars false

/-! # Lebesgue subdivision of a smooth path by a chart cover

Given a smooth path `γ : SmoothPath IM X` on a manifold `X` and an open
cover of `X` (or more generally, an open cover of the path's image)
by chart-like sets, the **Lebesgue-number lemma** gives a finite
subdivision `0 = t₀ < t₁ < … < tₙ = 1` such that each subarc
`γ '' [t_k, t_{k+1}]` lies in a single cover-set.

This is the foundational ingredient for chart-local strategies (e.g.
discharging `BasedSmoothLoopsBoundHypothesis` via per-subarc
chart-local straight-line bordism, then aggregation).

## What this file ships

* `SmoothPath.lebesgueSubdivision`: for any open cover `c : ι → Set X`
  of the closure of `γ.toPath`'s range and any smooth path `γ`, there
  exists a partition `t : ℕ → unitInterval` (eventually constant at 1)
  and a per-step index `i_k` such that `γ.toPath '' [t k, t (k+1)] ⊆
  c (i_k)`.

* `SmoothPath.lebesgueSubdivision_of_chartCover`: specialization to
  the `[HasConvexTargetChartCover X]` instance, where the cover is by
  chart sources.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology Bundle ContDiff unitInterval

namespace JacobianChallenge

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {IM : ModelWithCorners ℝ E H}
  {X : Type u} [TopologicalSpace X] [ChartedSpace H X] [IsManifold IM ⊤ X]

/-! ## Lebesgue subdivision against an arbitrary open cover -/

/-- **Lebesgue subdivision of a smooth path by an open cover.**

If `c : ι → Set X` is an open cover of `Set.range γ.toPath`, then there
exists a partition of `[0, 1]` such that each subarc lies in one
cover-set. -/
theorem SmoothPath.lebesgueSubdivision {ι : Type*}
    (γ : SmoothPath IM X)
    (c : ι → Set X) (hOpen : ∀ i, IsOpen (c i))
    (hCov : Set.range γ.toPath ⊆ ⋃ i, c i) :
    ∃ t : ℕ → unitInterval,
      t 0 = 0 ∧
      Monotone t ∧
      (∃ n, ∀ m ≥ n, t m = 1) ∧
      ∀ n, ∃ i, Set.Icc (t n) (t (n + 1)) ⊆ γ.toPath ⁻¹' c i := by
  -- The preimage cover `c' i := γ.toPath ⁻¹' c i` is an open cover of
  -- the unit interval, since `γ.toPath` is continuous and lands in
  -- `⋃ i, c i`.
  set c' : ι → Set unitInterval := fun i => γ.toPath ⁻¹' (c i)
  have hc'_open : ∀ i, IsOpen (c' i) := fun i =>
    (hOpen i).preimage γ.toPath.continuous
  have hc'_cov : (Set.univ : Set unitInterval) ⊆ ⋃ i, c' i := by
    intro t _
    have ht_range : γ.toPath t ∈ Set.range γ.toPath := ⟨t, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hCov ht_range)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  -- Apply mathlib's Lebesgue-number result on the unit interval.
  exact exists_monotone_Icc_subset_open_cover_unitInterval hc'_open hc'_cov

/-! ## Lebesgue subdivision via `HasConvexTargetChartCover` -/

variable [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **Lebesgue subdivision via a chart cover.** Under
`[HasConvexTargetChartCover X]`, any smooth path on `X` admits a
finite subdivision of `[0, 1]` such that each subarc lies in the
source of a single (convex-target) chart from the atlas. -/
theorem SmoothPath.lebesgueSubdivision_of_chartCover
    [HasConvexTargetChartCover X]
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) :
    ∃ t : ℕ → unitInterval,
      t 0 = 0 ∧
      Monotone t ∧
      (∃ n, ∀ m ≥ n, t m = 1) ∧
      ∀ n, ∃ (φ : OpenPartialHomeomorph X ℂ),
        φ ∈ atlas ℂ X ∧ Convex ℝ φ.target ∧
        Set.Icc (t n) (t (n + 1)) ⊆ γ.toPath ⁻¹' φ.source := by
  -- Index the chart cover by the atlas members that are convex-target.
  let ι : Type _ := { φ : OpenPartialHomeomorph X ℂ //
    φ ∈ atlas ℂ X ∧ Convex ℝ φ.target }
  let c : ι → Set X := fun φ => φ.val.source
  have hOpen : ∀ i : ι, IsOpen (c i) := fun i => i.val.open_source
  have hCov : Set.range γ.toPath ⊆ ⋃ i : ι, c i := by
    rintro x ⟨t, rfl⟩
    obtain ⟨φ, hφ_atlas, hφ_convex, hx⟩ :=
      HasConvexTargetChartCover.cover (X := X) (γ.toPath t)
    refine Set.mem_iUnion.mpr ?_
    refine ⟨⟨φ, hφ_atlas, hφ_convex⟩, ?_⟩
    exact hx
  -- Apply the generic lebesgueSubdivision result.
  obtain ⟨t, h0, hmono, ⟨n, hn⟩, hcover⟩ :=
    SmoothPath.lebesgueSubdivision (X := X) γ c hOpen hCov
  refine ⟨t, h0, hmono, ⟨n, hn⟩, fun k => ?_⟩
  obtain ⟨i, hi⟩ := hcover k
  exact ⟨i.val, i.property.1, i.property.2, hi⟩

end JacobianChallenge

end
