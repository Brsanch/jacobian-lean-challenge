/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodLatticeComplexQuotientGeneric
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # `ℂ ⧸ L` as a complex 1-manifold (genus-1 complex torus)

For a discrete full-rank ℤ-lattice `L ≤ ℂ` (equivalently, a `ℤ`-submodule
of `ℂ` with `[DiscreteTopology L]` and `[IsZLattice ℝ L]`), the quotient
`ℂ ⧸ L` is a compact complex 1-manifold: the **complex torus** `T_L`,
a concrete genus-1 example for the Jacobian challenge.

This file specialises the generic complex-quotient construction
(`complex_isManifold_quotient_of_zlattice_generic` in
`PeriodLatticeComplexQuotientGeneric.lean`) to `E = ℂ`, producing the
two pieces our downstream `SmoothPath` infrastructure needs:

* `ChartedSpace ℂ (ℂ ⧸ L)` — already supplied by
  `chartedSpace_quotient_of_zlattice` (no scalar-field assumption).
* `IsManifold 𝓘(ℂ, ℂ) ω (ℂ ⧸ L)` — supplied here as an `instance`.

These two together let us treat `ℂ ⧸ L` as `X` in the
`HolomorphicOneForm X`, `SmoothPath 𝓘(ℝ, ℂ) X`, `SmoothSymplecticBasis`
etc. ecosystem. The next file builds the explicit two-loop symplectic
basis on `T_L`.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **`IsManifold 𝓘(ℂ, ℂ) ω (ℂ ⧸ L)` for a discrete full-rank lattice
`L ≤ ℂ`.** The complex torus `T_L = ℂ ⧸ L` is a smooth complex
1-manifold via the generic quotient-manifold construction. -/
noncomputable instance instIsManifold (n : WithTop ℕ∞) :
    IsManifold (𝓘(ℂ, ℂ)) n (ℂ ⧸ L) :=
  complex_isManifold_quotient_of_zlattice_generic L n

/-! ## Smoothness of `mkQ : ℂ → ℂ ⧸ L`

Specialised proof of `mkQ_contMDiff_complex` (from
`PeriodLatticeMkQContMDiff.lean`) to `E = ℂ`. The proof reuses the
same chart-symm-of-maximal-atlas argument. -/

private lemma localChartSymm_mem_atlas_C (x : ℂ) :
    (localChart L (discRadius_separates L) x).symm ∈
      atlas ℂ (ℂ ⧸ L) :=
  ⟨x, rfl⟩

private lemma localChartSymm_mem_maximalAtlas_C (n : WithTop ℕ∞) (x : ℂ) :
    (localChart L (discRadius_separates L) x).symm ∈
      IsManifold.maximalAtlas (𝓘(ℂ, ℂ)) n (ℂ ⧸ L) :=
  IsManifold.subset_maximalAtlas (localChartSymm_mem_atlas_C L x)

private lemma localChart_symm_symm_C (x : ℂ) :
    (localChart L (discRadius_separates L) x).symm.symm =
      localChart L (discRadius_separates L) x :=
  OpenPartialHomeomorph.symm_symm _

private lemma localChart_eq_mkQ_on_source_C (x : ℂ) :
    Set.EqOn (localChart L (discRadius_separates L) x)
      (L.mkQ : ℂ → ℂ ⧸ L)
      (localChart L (discRadius_separates L) x).source := by
  intro y _
  rfl

private lemma mkQ_contMDiffOn_localChart_source_C
    (n : WithTop ℕ∞) (x : ℂ) :
    ContMDiffOn (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) n
      (L.mkQ : ℂ → ℂ ⧸ L)
      (localChart L (discRadius_separates L) x).source := by
  have h :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (I := 𝓘(ℂ, ℂ)) (n := n)
      (localChartSymm_mem_maximalAtlas_C L n x)
  have htarget :
      (localChart L (discRadius_separates L) x).symm.target =
        (localChart L (discRadius_separates L) x).source :=
    (localChart L (discRadius_separates L) x).symm_target
  rw [htarget] at h
  rw [localChart_symm_symm_C L x] at h
  exact h.congr (localChart_eq_mkQ_on_source_C L x)

/-- **`L.mkQ : ℂ → ℂ ⧸ L` is `ContMDiffAt` at every `x : ℂ`** (complex
analytic model on both sides). -/
theorem mkQ_contMDiffAt
    (n : WithTop ℕ∞) (x : ℂ) :
    ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) n
      (L.mkQ : ℂ → ℂ ⧸ L) x := by
  have hmem : x ∈ (localChart L (discRadius_separates L) x).source := by
    have hr_pos : 0 < discRadius L := discRadius_pos L
    have hr2_pos : 0 < discRadius L / 2 := by linarith
    change x ∈ Metric.ball x (discRadius L / 2)
    simp [Metric.mem_ball, dist_self, hr2_pos]
  have hsrc_open : IsOpen
      (localChart L (discRadius_separates L) x).source :=
    (localChart L (discRadius_separates L) x).open_source
  exact ((mkQ_contMDiffOn_localChart_source_C L n x).contMDiffAt
    (hsrc_open.mem_nhds hmem))

/-- **`L.mkQ : ℂ → ℂ ⧸ L` is `ContMDiff` everywhere** (complex analytic
model on both sides). -/
theorem mkQ_contMDiff (n : WithTop ℕ∞) :
    ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) n
      (L.mkQ : ℂ → ℂ ⧸ L) :=
  fun x => mkQ_contMDiffAt L n x

/-- **`L.mkQ : ℂ → ℂ ⧸ L` is `ContMDiff` in the real model
`𝓘(ℝ, ℂ)`.** Follows from the complex-model version via the standard
bridge `ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) n f ↔ ContMDiff (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) n f`
(both models are over the same underlying real space and the chart
groupoid is the same). For our use here we re-derive directly from the
chart-symm-of-maximalAtlas argument with the real model. -/
theorem mkQ_contMDiff_real (n : WithTop ℕ∞) :
    ContMDiff (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) n
      (L.mkQ : ℂ → ℂ ⧸ L) := by
  intro x
  -- Same as `mkQ_contMDiffAt` but for the real model.
  -- Atlas membership of `(localChart L _ x).symm`.
  have h_atlas : (localChart L (discRadius_separates L) x).symm ∈
      atlas ℂ (ℂ ⧸ L) := ⟨x, rfl⟩
  -- The real-model `IsManifold 𝓘(ℝ, ℂ) n (ℂ ⧸ L)` comes from the
  -- real-model lattice-quotient instance (`PeriodLatticeLieGroup.lean`'s
  -- `isManifold_quotient_of_zlattice`).
  have h_max : (localChart L (discRadius_separates L) x).symm ∈
      IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) n (ℂ ⧸ L) :=
    IsManifold.subset_maximalAtlas h_atlas
  have h_symm :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (I := 𝓘(ℝ, ℂ)) (n := n) h_max
  have htarget :
      (localChart L (discRadius_separates L) x).symm.target =
        (localChart L (discRadius_separates L) x).source :=
    (localChart L (discRadius_separates L) x).symm_target
  rw [htarget] at h_symm
  rw [localChart_symm_symm_C L x] at h_symm
  have h_on : ContMDiffOn (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) n
      (L.mkQ : ℂ → ℂ ⧸ L)
      (localChart L (discRadius_separates L) x).source :=
    h_symm.congr (localChart_eq_mkQ_on_source_C L x)
  have hmem : x ∈ (localChart L (discRadius_separates L) x).source := by
    have hr_pos : 0 < discRadius L := discRadius_pos L
    have hr2_pos : 0 < discRadius L / 2 := by linarith
    change x ∈ Metric.ball x (discRadius L / 2)
    simp [Metric.mem_ball, dist_self, hr2_pos]
  have hsrc_open : IsOpen
      (localChart L (discRadius_separates L) x).source :=
    (localChart L (discRadius_separates L) x).open_source
  exact (h_on.contMDiffAt (hsrc_open.mem_nhds hmem))

end ComplexTorus

end JacobianChallenge
