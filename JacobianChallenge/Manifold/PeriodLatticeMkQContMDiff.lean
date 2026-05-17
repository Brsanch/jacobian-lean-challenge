/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodLatticeComplexQuotient
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Smoothness of the quotient projection `L.mkQ : E → E ⧸ L`

Companion to `PeriodLatticeChartedSpace.lean` (charted-space structure on
`E ⧸ L`) and `PeriodLatticeComplexQuotient.lean` (complex-`ω` analytic
manifold structure for `E = Fin g → ℂ`).

The single export here is

* `mkQ_contMDiff_complex` — the quotient projection
  `L.mkQ : E → E ⧸ L` is `ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) n` for every
  `n : WithTop ℕ∞`, where `E = Fin g → ℂ` and `L` is a discrete full-rank
  `ℤ`-lattice in `E`.

This is needed downstream by the `LieAddGroup` discharge in
`PeriodLatticeLieGroupAdd.lean` (this session): the group operations
`+ : G × G → G` and `Neg.neg : G → G` are read locally as
`mkQ ∘ +_E ∘ (chartAt × chartAt)` and `mkQ ∘ Neg.neg_E ∘ chartAt`, and
both factor through `mkQ` smoothness.

## Proof structure

Each atlas chart `(localChart L _ x).symm : G → E` has, as its `.symm`,
the partial map `localChart L _ x : E → G` whose forward equals
`L.mkQ` on `Metric.ball x (r/2)` (by definition: the underlying
`PartialEquiv` of `localChart` has `f := L.mkQ`).

By `IsManifold.subset_maximalAtlas`, `(localChart L _ x).symm` lies in
the maximal atlas. By `contMDiffOn_symm_of_mem_maximalAtlas`,
`(localChart L _ x).symm.symm = localChart L _ x` is `ContMDiffOn`
on its source `ball x (r/2)`. On that source it equals `L.mkQ`, so
`L.mkQ` is `ContMDiffOn` on every `ball x (r/2)`. Since these balls
cover `E`, `L.mkQ` is `ContMDiff` on all of `E`.
-/

open Set Metric

open scoped Manifold ContDiff

set_option diagnostics.threshold 100

namespace JacobianChallenge

variable {g : ℕ}
variable (L : Submodule ℤ (Fin g → ℂ))
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ### Atlas membership of `(localChart L _ x).symm` -/

private lemma localChartSymm_mem_atlas (x : Fin g → ℂ) :
    (localChart L (discRadius_separates L) x).symm ∈
      atlas (Fin g → ℂ) ((Fin g → ℂ) ⧸ L) :=
  ⟨x, rfl⟩

private lemma localChartSymm_mem_maximalAtlas (n : WithTop ℕ∞) (x : Fin g → ℂ) :
    (localChart L (discRadius_separates L) x).symm ∈
      IsManifold.maximalAtlas (𝓘(ℂ, Fin g → ℂ)) n ((Fin g → ℂ) ⧸ L) :=
  IsManifold.subset_maximalAtlas (localChartSymm_mem_atlas L x)

/-! ### Pointwise smoothness of `mkQ` -/

/-- `(localChart L _ x).symm.symm = localChart L _ x` on the partial-equiv
level: the inverse-of-inverse of an `OpenPartialHomeomorph` is itself. -/
private lemma localChart_symm_symm (x : Fin g → ℂ) :
    (localChart L (discRadius_separates L) x).symm.symm =
      localChart L (discRadius_separates L) x :=
  OpenPartialHomeomorph.symm_symm _

/-- `localChart L _ x` agrees with `L.mkQ` on its source `ball x (r/2)`. -/
private lemma localChart_eq_mkQ_on_source (x : Fin g → ℂ) :
    Set.EqOn (localChart L (discRadius_separates L) x)
      (L.mkQ : (Fin g → ℂ) → (Fin g → ℂ) ⧸ L)
      (localChart L (discRadius_separates L) x).source := by
  intro y _
  -- The `localChart` has underlying `PartialEquiv` with `f := L.mkQ`,
  -- by definition.
  rfl

/-- The quotient projection `L.mkQ` is `ContMDiffOn` on `ball x (r/2)`,
the source of `localChart L _ x`. -/
private lemma mkQ_contMDiffOn_localChart_source
    (n : WithTop ℕ∞) (x : Fin g → ℂ) :
    ContMDiffOn (𝓘(ℂ, Fin g → ℂ)) (𝓘(ℂ, Fin g → ℂ)) n
      (L.mkQ : (Fin g → ℂ) → (Fin g → ℂ) ⧸ L)
      (localChart L (discRadius_separates L) x).source := by
  -- `contMDiffOn_symm_of_mem_maximalAtlas` gives smoothness of
  -- `(localChart L _ x).symm.symm` on the *target* of `(localChart L _ x).symm`,
  -- which is the source of `localChart L _ x`.
  have h :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (I := 𝓘(ℂ, Fin g → ℂ)) (n := n)
      (localChartSymm_mem_maximalAtlas L n x)
  -- The target of `.symm` is the source of the original.
  have htarget :
      (localChart L (discRadius_separates L) x).symm.target =
        (localChart L (discRadius_separates L) x).source :=
    (localChart L (discRadius_separates L) x).symm_target
  rw [htarget] at h
  -- `.symm.symm = .` on the partial-equiv level.
  rw [localChart_symm_symm L x] at h
  -- Congrue along the on-source equality `localChart … = L.mkQ`.
  exact h.congr (localChart_eq_mkQ_on_source L x)

/-- The quotient projection `L.mkQ : E → E ⧸ L` is `ContMDiffAt` at every
`x : E`, with `E := Fin g → ℂ` and the complex model. -/
theorem mkQ_contMDiffAt_complex
    (n : WithTop ℕ∞) (x : Fin g → ℂ) :
    ContMDiffAt (𝓘(ℂ, Fin g → ℂ)) (𝓘(ℂ, Fin g → ℂ)) n
      (L.mkQ : (Fin g → ℂ) → (Fin g → ℂ) ⧸ L) x := by
  -- `x ∈ source` because `x ∈ ball x (r/2)` and the source is exactly that.
  have hmem : x ∈ (localChart L (discRadius_separates L) x).source := by
    -- `source = ball x (r/2)`; `x ∈ ball x (r/2)` since `r/2 > 0`.
    have hr_pos : 0 < discRadius L := discRadius_pos L
    have hr2_pos : 0 < discRadius L / 2 := by linarith
    -- Source of `localChart` is `Metric.ball x (r/2)`, by `localChart_source`.
    show x ∈ Metric.ball x (discRadius L / 2)
    simp [Metric.mem_ball, dist_self, hr2_pos]
  have hsrc_open : IsOpen
      (localChart L (discRadius_separates L) x).source :=
    (localChart L (discRadius_separates L) x).open_source
  -- ContMDiffOn-on-open + membership ⇒ ContMDiffAt.
  exact ((mkQ_contMDiffOn_localChart_source L n x).contMDiffAt
    (hsrc_open.mem_nhds hmem))

/-- The quotient projection `L.mkQ : E → E ⧸ L` is `ContMDiff` on all of
`E`, with `E := Fin g → ℂ` and the complex model. -/
theorem mkQ_contMDiff_complex (n : WithTop ℕ∞) :
    ContMDiff (𝓘(ℂ, Fin g → ℂ)) (𝓘(ℂ, Fin g → ℂ)) n
      (L.mkQ : (Fin g → ℂ) → (Fin g → ℂ) ⧸ L) :=
  fun x => mkQ_contMDiffAt_complex L n x

end JacobianChallenge
