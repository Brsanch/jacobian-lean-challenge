/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CompactnessChartCover
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! # Chip 5.2 — partition of unity subordinate to a `FiniteChartCover`

Given a `FiniteChartCover X` produced by Chip 5.1, this file bundles a
smooth ℝ-valued partition of unity `{ρ_i}_{i ∈ cover.basePoints}` with
each `ρ_i` subordinate to the chart source `(chartAt ℂ x_i).source`.

The construction is a thin wrapper over mathlib's
`SmoothPartitionOfUnity.exists_isSubordinate`: instantiate it at the
subtype `{ x : X // x ∈ cover.basePoints }`, the open cover
`U i := (chartAt ℂ i.val).source`, and the closed set `s := Set.univ`.
Compactness of `X` supplies `SigmaCompactSpace X`; Hausdorffness must
be assumed (`T2Space X`); the smooth-manifold structure
`IsManifold 𝓘(ℝ, ℂ) ⊤ X` supplies the partition-of-unity
infrastructure.

The output is wrapped in a structure `FiniteChartCoverPartition cover`
so downstream sub-chips (5.3-5.6) have a clean handle on:

* the ℝ-valued partition functions `P.rho i : X → ℝ`,
* their ℂ-valued cast `P.rhoC i : X → ℂ` (the form Chip 5.3 needs to
  multiply by α : X → ℂ),
* the four classical properties: nonnegativity, ≤ 1, sum = 1, and
  `tsupport ⊆ chart source`,
* smoothness in both flavors.

## Main definitions

* `JacobianChallenge.FiniteChartCoverPartition cover` — the bundled
  partition of unity.
* `FiniteChartCoverPartition.rho`, `rhoC` — the ℝ- and ℂ-valued
  partition functions at each base point.

## Main results

* `FiniteChartCoverPartition.exists_of_cover` — every `FiniteChartCover`
  on a compact Hausdorff smooth complex 1-manifold admits a subordinate
  partition of unity.

No `sorry`, no `axiom`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff
open Set

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℝ, ℂ) ⊤ X]

/-- A smooth partition of unity on a compact Hausdorff charted-ℂ space
`X` subordinate to a `FiniteChartCover`. Bundles the partition (indexed
by the cover's base points as a subtype) together with the
subordination property `tsupport (ρ i) ⊆ (chartAt ℂ i.val).source`. -/
structure FiniteChartCoverPartition (cover : FiniteChartCover X) where
  /-- The underlying mathlib smooth partition of unity, indexed by the
  cover's base points. -/
  partition : SmoothPartitionOfUnity {x : X // x ∈ cover.basePoints}
      𝓘(ℝ, ℂ) X Set.univ
  /-- Each partition function is supported in its corresponding chart
  source. -/
  isSubordinate : partition.IsSubordinate
      (fun i : {x : X // x ∈ cover.basePoints} => (chartAt ℂ i.val).source)

namespace FiniteChartCoverPartition

/-- **Existence.** Every `FiniteChartCover` on a compact Hausdorff
smooth complex 1-manifold admits a subordinate smooth partition of
unity. Reduces to mathlib's
`SmoothPartitionOfUnity.exists_isSubordinate` applied to the open
cover by chart sources of the cover's base points. -/
theorem exists_of_cover [CompactSpace X] (cover : FiniteChartCover X) :
    Nonempty (FiniteChartCoverPartition cover) := by
  classical
  -- Subtype indexed by the (finite) base-point set.
  let ι : Type _ := {x : X // x ∈ cover.basePoints}
  -- Open cover by chart sources at each base point.
  let U : ι → Set X := fun i => (chartAt ℂ i.val).source
  have hU_open : ∀ i, IsOpen (U i) := fun i => (chartAt ℂ i.val).open_source
  have hU_cover : (Set.univ : Set X) ⊆ ⋃ i, U i := by
    intro y _
    obtain ⟨x, hxS, hxy⟩ := cover.covers y
    exact mem_iUnion.mpr ⟨⟨x, hxS⟩, hxy⟩
  obtain ⟨f, hf⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate
      (I := 𝓘(ℝ, ℂ)) (M := X) (ι := ι)
      isClosed_univ U hU_open hU_cover
  exact ⟨{ partition := f, isSubordinate := hf }⟩

variable {cover : FiniteChartCover X} (P : FiniteChartCoverPartition cover)

/-- The ℝ-valued partition function at base point `i`. -/
def rho (i : {x : X // x ∈ cover.basePoints}) : X → ℝ :=
  fun y => P.partition i y

/-- The ℂ-valued partition function at base point `i`. Cast of the
ℝ-valued `rho i` through `Complex.ofRealCLM`, used by Chip 5.3 to
multiply with `α : X → ℂ` (the (0,1)-form chart trivialization). -/
def rhoC (i : {x : X // x ∈ cover.basePoints}) : X → ℂ :=
  fun y => ((P.rho i y : ℝ) : ℂ)

/-! ## Classical partition-of-unity properties (ℝ-valued) -/

theorem rho_nonneg (i : {x : X // x ∈ cover.basePoints}) (y : X) :
    0 ≤ P.rho i y :=
  P.partition.nonneg i y

theorem rho_le_one (i : {x : X // x ∈ cover.basePoints}) (y : X) :
    P.rho i y ≤ 1 :=
  P.partition.le_one i y

/-- The partition sums to one at every point. Since the index type is a
subtype of a `Finset`, the `finsum` over the partition coincides with
the genuine finite sum (see `finsum_eq_sum`). -/
theorem sum_rho_eq_one (y : X) : ∑ᶠ i, P.rho i y = 1 :=
  P.partition.sum_eq_one (Set.mem_univ y)

theorem tsupport_rho_subset (i : {x : X // x ∈ cover.basePoints}) :
    tsupport (P.rho i) ⊆ (chartAt ℂ i.val).source :=
  P.isSubordinate i

theorem rho_smooth (i : {x : X // x ∈ cover.basePoints}) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (P.rho i) :=
  (P.partition i).contMDiff

theorem rho_continuous (i : {x : X // x ∈ cover.basePoints}) :
    Continuous (P.rho i) :=
  (P.rho_smooth i).continuous

/-! ## ℂ-valued cast: properties -/

/-- The ℂ-valued partition function equals the ℝ-cast of the ℝ-valued
one pointwise — restatement helper. -/
theorem rhoC_eq_ofReal_rho (i : {x : X // x ∈ cover.basePoints}) (y : X) :
    P.rhoC i y = ((P.rho i y : ℝ) : ℂ) := rfl

theorem rhoC_nonneg_re (i : {x : X // x ∈ cover.basePoints}) (y : X) :
    0 ≤ (P.rhoC i y).re := by
  simp [rhoC, Complex.ofReal_re]
  exact P.rho_nonneg i y

theorem rhoC_im_eq_zero (i : {x : X // x ∈ cover.basePoints}) (y : X) :
    (P.rhoC i y).im = 0 := by
  simp [rhoC, Complex.ofReal_im]

/-- The ℂ-valued partition function has support equal to that of the
ℝ-valued one: `Complex.ofRealCLM` is injective so the cast zeros out
exactly where `rho i` does. -/
theorem tsupport_rhoC_subset (i : {x : X // x ∈ cover.basePoints}) :
    tsupport (P.rhoC i) ⊆ (chartAt ℂ i.val).source := by
  -- `rhoC i y = 0 ↔ rho i y = 0` via `Complex.ofReal_eq_zero`.
  have h_support_eq : Function.support (P.rhoC i) = Function.support (P.rho i) := by
    ext y
    simp [Function.support, rhoC, Complex.ofReal_eq_zero]
  -- Closures of equal sets are equal.
  have h_tsupport_eq : tsupport (P.rhoC i) = tsupport (P.rho i) := by
    unfold tsupport
    rw [h_support_eq]
  rw [h_tsupport_eq]
  exact P.tsupport_rho_subset i

/-- The ℂ-valued partition function is smooth as a map
`(X, 𝓘(ℝ, ℂ)) → (ℂ, 𝓘(ℝ, ℂ))`. Compose the ℝ-valued partition
function with the continuous-linear cast `Complex.ofRealCLM`. -/
theorem rhoC_smooth (i : {x : X // x ∈ cover.basePoints}) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (P.rhoC i) := by
  -- `Complex.ofRealCLM : ℝ →L[ℝ] ℂ` is smooth as a manifold map.
  have h_clm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
      (Complex.ofRealCLM : ℝ → ℂ) :=
    Complex.ofRealCLM.contMDiff
  -- Compose with `P.rho i`.
  have h_comp : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (Complex.ofRealCLM ∘ P.rho i) :=
    h_clm.comp (P.rho_smooth i)
  -- `rhoC i = Complex.ofRealCLM ∘ rho i` pointwise.
  have h_eq : P.rhoC i = Complex.ofRealCLM ∘ P.rho i := by
    funext y; rfl
  rw [h_eq]
  exact h_comp

theorem rhoC_continuous (i : {x : X // x ∈ cover.basePoints}) :
    Continuous (P.rhoC i) :=
  (P.rhoC_smooth i).continuous

/-- The ℂ-valued partition sums to one at every point. Cast of the
ℝ-valued `sum_rho_eq_one`: since the index type is finite (subtype of
a `Finset`), `finsum` over the ℂ-cast equals the cast of the `finsum`
over ℝ. -/
theorem sum_rhoC_eq_one (y : X) :
    ∑ᶠ i, P.rhoC i y = (1 : ℂ) := by
  classical
  -- Both sides equal a genuine finite sum over the (finite) subtype.
  haveI : Fintype {x : X // x ∈ cover.basePoints} := inferInstance
  have h_finsum_C : ∑ᶠ i, P.rhoC i y
      = ∑ i : {x : X // x ∈ cover.basePoints}, P.rhoC i y :=
    finsum_eq_sum_of_fintype _
  have h_finsum_R : ∑ᶠ i, P.rho i y
      = ∑ i : {x : X // x ∈ cover.basePoints}, P.rho i y :=
    finsum_eq_sum_of_fintype _
  rw [h_finsum_C]
  -- Push the ℝ → ℂ cast through the Finset.sum via `Complex.ofReal_sum`.
  have h_cast :
      ∑ i : {x : X // x ∈ cover.basePoints}, ((P.rho i y : ℝ) : ℂ)
        = ((∑ i : {x : X // x ∈ cover.basePoints}, P.rho i y : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
  calc ∑ i : {x : X // x ∈ cover.basePoints}, P.rhoC i y
      = ∑ i : {x : X // x ∈ cover.basePoints}, ((P.rho i y : ℝ) : ℂ) := rfl
    _ = ((∑ i : {x : X // x ∈ cover.basePoints}, P.rho i y : ℝ) : ℂ) := h_cast
    _ = ((∑ᶠ i, P.rho i y : ℝ) : ℂ) := by rw [h_finsum_R]
    _ = ((1 : ℝ) : ℂ) := by rw [P.sum_rho_eq_one y]
    _ = (1 : ℂ) := Complex.ofReal_one

end FiniteChartCoverPartition

end JacobianChallenge

end
