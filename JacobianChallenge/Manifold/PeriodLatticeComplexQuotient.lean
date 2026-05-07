/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodLatticeLieGroup

/-! # Complex-model `IsManifold 𝓘(ℂ, Fin g → ℂ) ω ((Fin g → ℂ) ⧸ Λ)`

Companion to `PeriodLatticeChartedSpace.lean` (charted space) and
`PeriodLatticeLieGroup.lean` (real-model `IsManifold`). For a `ℤ`-lattice
`Λ ≤ Fin g → ℂ` (viewed as a real `2g`-dimensional space) which is
`DiscreteTopology` and `IsZLattice ℝ`, the quotient
`(Fin g → ℂ) ⧸ Λ` carries the **complex-model** analytic manifold
structure modeled on `Fin g → ℂ`.

The `ChartedSpace (Fin g → ℂ) ((Fin g → ℂ) ⧸ Λ)` instance is identical
to the one supplied by `chartedSpace_quotient_of_zlattice` — it is purely
topological/set-level data and does not depend on the choice of scalar
field for the model with corners. The new content here is the
**complex-`ω`** chart-change regularity:

* Each chart-transition is, on a neighborhood of every point of its
  source, equal to a translation `x ↦ x - λ` for a fixed lattice element
  `λ ∈ Λ`. We re-prove this in the complex setting (the helper in
  `PeriodLatticeLieGroup.lean` is `private`).
* Translation by a constant on a `ℂ`-normed space is `ContDiff ℂ ω`
  (analytic), via `contDiff_id.sub contDiff_const`.

Hence the chart-transition is `ContDiff ℂ ω` on its source, and
`isManifold_of_contDiffOn` lifts this to the desired manifold instance.
-/

open Set Metric

open scoped Manifold ContDiff

namespace JacobianChallenge

variable {g : ℕ}

/-- `Fin g → ℂ` is finite-dimensional over `ℝ`. -/
instance : FiniteDimensional ℝ (Fin g → ℂ) :=
  Module.Finite.pi

variable (L : Submodule ℤ (Fin g → ℂ))
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ### Local re-proof of the chart-transition translation property

The helper `transition_eventuallyEq_translation` in
`PeriodLatticeLieGroup.lean` is `private` to that file. We re-derive the
statement here without modifying that file. -/

private lemma transition_eventuallyEq_translation_C
    {r : ℝ} (hrL : ∀ x ∈ (L : Set (Fin g → ℂ)), ‖x‖ < r → x = 0)
    (c c' : Fin g → ℂ)
    {x₀ : Fin g → ℂ}
    (hx₀ : x₀ ∈ ((localChart L hrL c).trans (localChart L hrL c').symm).source) :
    ∃ lam ∈ (L : Set (Fin g → ℂ)),
      (fun x : (Fin g → ℂ) =>
          (((localChart L hrL c).trans (localChart L hrL c').symm)) x)
          =ᶠ[nhds x₀] (fun x : (Fin g → ℂ) => x - lam) := by
  classical
  have hsrc :
      ((localChart L hrL c).trans (localChart L hrL c').symm).source
        = Metric.ball c (r / 2) ∩
            (L.mkQ : (Fin g → ℂ) → (Fin g → ℂ) ⧸ L) ⁻¹'
              (L.mkQ '' Metric.ball c' (r / 2)) := by
    change ((localChart L hrL c).toPartialEquiv.trans
            (localChart L hrL c').symm.toPartialEquiv).source = _
    rw [PartialEquiv.trans_source]
    rfl
  rw [hsrc] at hx₀
  obtain ⟨hx₀_ball, y₀, hy₀_ball, hxy₀⟩ := hx₀
  have hlam_mem : x₀ - y₀ ∈ L := by
    have : (Submodule.Quotient.mk x₀ : (Fin g → ℂ) ⧸ L) =
        Submodule.Quotient.mk y₀ := by
      simpa [Submodule.mkQ_apply] using hxy₀.symm
    exact (Submodule.Quotient.eq L).mp this
  refine ⟨x₀ - y₀, hlam_mem, ?_⟩
  set lam := x₀ - y₀ with hlam_def
  have h_x₀_minus : x₀ - lam = y₀ := by simp [hlam_def]
  have h_y₀ : x₀ - lam ∈ Metric.ball c' (r / 2) := by
    rw [h_x₀_minus]; exact hy₀_ball
  have h_ball_open_c : IsOpen (Metric.ball c (r / 2) : Set (Fin g → ℂ)) :=
    Metric.isOpen_ball
  have h_ball_open_c' : IsOpen (Metric.ball c' (r / 2) : Set (Fin g → ℂ)) :=
    Metric.isOpen_ball
  have h_translate_cont : Continuous (fun x : (Fin g → ℂ) => x - lam) :=
    continuous_id.sub continuous_const
  have h_preimage_open :
      IsOpen ((fun x : (Fin g → ℂ) => x - lam) ⁻¹' Metric.ball c' (r / 2)) :=
    h_ball_open_c'.preimage h_translate_cont
  have h_preimage_mem :
      x₀ ∈ (fun x : (Fin g → ℂ) => x - lam) ⁻¹' Metric.ball c' (r / 2) :=
    h_y₀
  set U : Set (Fin g → ℂ) := Metric.ball c (r / 2) ∩
                    (fun x : (Fin g → ℂ) => x - lam) ⁻¹' Metric.ball c' (r / 2)
  have hU_open : IsOpen U := h_ball_open_c.inter h_preimage_open
  have hU_mem : x₀ ∈ U := ⟨hx₀_ball, h_preimage_mem⟩
  have hU_nhds : U ∈ nhds x₀ := hU_open.mem_nhds hU_mem
  refine Filter.eventually_of_mem hU_nhds ?_
  intro x hxU
  obtain ⟨hx_in_ballc, hxlam_in_ballc'⟩ := hxU
  show ((localChart L hrL c).trans (localChart L hrL c').symm) x = x - lam
  have h_step1 : ((localChart L hrL c).trans (localChart L hrL c').symm) x
      = (localChart L hrL c').symm (L.mkQ x) := by
    change (localChart L hrL c').symm ((localChart L hrL c) x) = _
    rfl
  rw [h_step1]
  have h_lattice_eq : L.mkQ (x - lam) = L.mkQ x := by
    have hsub : (x - lam) - x = -lam := by abel
    have hmem : (x - lam) - x ∈ L := by
      rw [hsub]; exact L.neg_mem hlam_mem
    have heq : (Submodule.Quotient.mk (x - lam) : (Fin g → ℂ) ⧸ L) =
        Submodule.Quotient.mk x := by
      rw [Submodule.Quotient.eq L]; exact hmem
    simpa [Submodule.mkQ_apply] using heq
  -- (localChart c').symm (L.mkQ (x - lam)) = x - lam by left-inverse on the source.
  have h_apply :
      (localChart L hrL c').symm (L.mkQ (x - lam)) = x - lam := by
    have hsrc : (x - lam) ∈ (localChart L hrL c').source := hxlam_in_ballc'
    have h := (localChart L hrL c').left_inv hsrc
    -- `(localChart L hrL c') (x - lam) = L.mkQ (x - lam)` by definition.
    -- so `(localChart L hrL c').symm (L.mkQ (x - lam)) = x - lam`.
    simpa using h
  rw [h_lattice_eq] at h_apply
  exact h_apply

/-! ### Complex-`ω` chart-transition regularity -/

/-- Subtraction of a constant on a `ℂ`-normed space is `ContDiff ℂ n`. -/
private lemma contDiff_C_sub_const {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {n : WithTop ℕ∞} (c : E) :
    ContDiff ℂ n (fun x : E => x - c) :=
  contDiff_id.sub contDiff_const

/-- Chart-change between any two atlas elements is `ContDiff ℂ ω` on its
source, because it equals translation by a lattice element on a
neighborhood of every point and translation is complex-analytic. -/
private lemma contDiffOn_chart_transition_C
    {r : ℝ} (hrL : ∀ x ∈ (L : Set (Fin g → ℂ)), ‖x‖ < r → x = 0)
    (c c' : Fin g → ℂ) (n : WithTop ℕ∞) :
    ContDiffOn ℂ n
      ((localChart L hrL c).trans (localChart L hrL c').symm)
      ((localChart L hrL c).trans (localChart L hrL c').symm).source := by
  intro x₀ hx₀
  obtain ⟨lam, _hlam_mem, h_eqOn⟩ :=
    transition_eventuallyEq_translation_C L hrL c c' hx₀
  have hCD : ContDiffWithinAt ℂ n (fun x : (Fin g → ℂ) => x - lam)
      (((localChart L hrL c).trans (localChart L hrL c').symm).source) x₀ :=
    (contDiff_C_sub_const lam).contDiffWithinAt
  exact hCD.congr_of_eventuallyEq (h_eqOn.filter_mono nhdsWithin_le_nhds)
      (h_eqOn.self_of_nhds)

/-! ### Complex-model `IsManifold` instance -/

/-- **Complex-`ω` analytic manifold structure on `(Fin g → ℂ) ⧸ Λ`.**
For a discrete full-rank `ℤ`-lattice `Λ`, the quotient is a `C^n`
manifold modeled on `Fin g → ℂ` with the standard complex model
`𝓘(ℂ, Fin g → ℂ)`. The chart-changes are local translations by lattice
elements, which are complex-affine and thus `ContDiff ℂ ω`. The
underlying `ChartedSpace` instance is `chartedSpace_quotient_of_zlattice`
(re-used unchanged from the real-model file). -/
noncomputable instance complex_isManifold_quotient_of_zlattice
    (n : WithTop ℕ∞) :
    IsManifold (𝓘(ℂ, Fin g → ℂ)) n ((Fin g → ℂ) ⧸ L) := by
  refine isManifold_of_contDiffOn 𝓘(ℂ, Fin g → ℂ) n ((Fin g → ℂ) ⧸ L) ?_
  intro e e' he he'
  rcases he with ⟨c, hce⟩
  rcases he' with ⟨c', hc'e'⟩
  subst hce
  subst hc'e'
  have h := contDiffOn_chart_transition_C L (discRadius_separates L) c c' n
  simp only [mfld_simps] at h ⊢
  exact h

end JacobianChallenge
