/-
Copyright (c) 2026 Jacobian Lean Challenge contributors. All rights reserved.

Foundation chip ZZ165b: any continuous path `γ : I → Y` in a `ChartedSpace H Y`
can be subdivided into finitely many sub-intervals, each entirely contained in
the source of a single chart. This is the standard topological argument
(open-cover by chart sources + Lebesgue-number lemma + interval partition),
packaged for downstream use by chips that need to lift a path against an atlas.

The combinatorics (open cover of `[0,1]` by preimages, refinement to a
monotone partition `t : ℕ → I`) is already provided by mathlib as
`exists_monotone_Icc_subset_open_cover_unitInterval`; we just specialize it
to the chart-source cover associated to the path.
-/
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.OpenOpenPartialHomeomorph.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Path

namespace JacobianChallenge.Manifold

open Set unitInterval

/--
Path subdivision by charts: any continuous path `γ : Path p q` in a charted
space `Y` over `H` admits a finite monotone partition `t : ℕ → I` with
`t 0 = 0`, eventually `t m = 1`, together with a choice of chart
`φ i ∈ atlas H Y` for each `i`, such that on every sub-interval
`Icc (t i) (t (i+1))` the path lies in the source of the chosen chart.

Strategy:
1. The family `c y := γ ⁻¹' (chartAt H (γ y)).source`, indexed by `y : I`,
   is an open cover of `I` (each `c y` is open as the preimage of an open
   set under a continuous map, and `y ∈ c y` since `γ y ∈ (chartAt H (γ y)).source`).
2. `exists_monotone_Icc_subset_open_cover_unitInterval` applied to this cover
   yields the partition together with, for each piece, a Lebesgue index
   `y i : I` whose chart contains the whole sub-interval's image.
3. Taking `φ i := chartAt H (γ (y i))` gives the required chart per piece.
-/
theorem Path.exists_chart_subdivision
    {Y H : Type*} [TopologicalSpace Y] [TopologicalSpace H] [ChartedSpace H Y]
    {p q : Y} (γ : Path p q) :
    ∃ (t : ℕ → I) (φ : ℕ → OpenPartialHomeomorph Y H),
      t 0 = 0 ∧ Monotone t ∧ (∃ N, ∀ m ≥ N, t m = 1) ∧
      (∀ i, φ i ∈ atlas H Y) ∧
      (∀ i, ∀ s ∈ Icc (t i) (t (i + 1)), γ s ∈ (φ i).source) := by
  -- Open cover of `I` by preimages of chart sources, indexed by points of `I`.
  let c : I → Set I := fun y => γ ⁻¹' (chartAt H (γ y)).source
  have hc_open : ∀ y, IsOpen (c y) := fun y =>
    (chartAt H (γ y)).open_source.preimage γ.continuous
  have hc_cover : (univ : Set I) ⊆ ⋃ y, c y := by
    intro x _
    refine mem_iUnion.mpr ⟨x, ?_⟩
    -- `γ x ∈ (chartAt H (γ x)).source` directly from `mem_chart_source`.
    exact mem_chart_source H (γ x)
  -- Refine to a finite monotone partition with one chart-index per piece.
  obtain ⟨t, ht0, ht_mono, ⟨N, htN⟩, hpiece⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hc_open hc_cover
  -- For each piece `i`, choose the Lebesgue index `y i : I` and form the chart.
  choose y hy using hpiece
  refine ⟨t, fun i => chartAt H (γ (y i)), ht0, ht_mono, ⟨N, htN⟩, ?_, ?_⟩
  · intro i; exact chart_mem_atlas H (γ (y i))
  · intro i s hs
    -- `s ∈ Icc (t i) (t (i+1))` ⊆ `c (y i) = γ ⁻¹' (chartAt H (γ (y i))).source`.
    exact hy i hs

end JacobianChallenge.Manifold
