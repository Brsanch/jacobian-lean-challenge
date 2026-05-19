/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import JacobianChallenge.Manifold.PeriodLatticeLieGroup

/-! # Generic `IsManifold 𝓘(ℂ, E) ω (E ⧸ L)` for a ℤ-lattice in any
finite-dimensional complex normed space

Generalises `PeriodLatticeComplexQuotient.lean`'s
`complex_isManifold_quotient_of_zlattice` (which fixes `E := Fin g → ℂ`)
to any finite-dimensional complex normed space `E`. The construction
is identical; we abstract the type to make the result usable for both
`E = Fin g → ℂ` (the high-dimensional period-lattice setup) and
`E = ℂ` (a one-dimensional complex torus, e.g.\ a genus-1 example).

## What this file ships

* `complex_isManifold_quotient_of_zlattice_generic` —
  `IsManifold 𝓘(ℂ, E) n (E ⧸ L)` for any complex finite-dim `E` and
  discrete full-rank ℤ-lattice `L ≤ E`.

The `ChartedSpace E (E ⧸ L)` instance is taken unchanged from
`chartedSpace_quotient_of_zlattice` (which only requires the real
structure on `E`).

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff

namespace JacobianChallenge

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- `FiniteDimensional ℝ E` follows from `FiniteDimensional ℂ E`.
Marked `local` to avoid clashing with mathlib's standard instance for
`Fin g → ℂ`; we re-derive it only as a hypothesis for the generic
construction here. -/
private lemma finiteDimensional_real_of_complex_generic :
    FiniteDimensional ℝ E :=
  Module.Finite.trans ℂ E

attribute [local instance] finiteDimensional_real_of_complex_generic

variable (L : Submodule ℤ E)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ### Chart-transition translation property (re-derived generically) -/

lemma transition_eventuallyEq_translation_generic
    {r : ℝ} (hrL : ∀ x ∈ (L : Set E), ‖x‖ < r → x = 0)
    (c c' : E)
    {x₀ : E}
    (hx₀ : x₀ ∈ ((localChart L hrL c).trans (localChart L hrL c').symm).source) :
    ∃ lam ∈ (L : Set E),
      (fun x : E =>
          (((localChart L hrL c).trans (localChart L hrL c').symm)) x)
          =ᶠ[nhds x₀] (fun x : E => x - lam) := by
  classical
  have hsrc :
      ((localChart L hrL c).trans (localChart L hrL c').symm).source
        = Metric.ball c (r / 2) ∩
            (L.mkQ : E → E ⧸ L) ⁻¹'
              (L.mkQ '' Metric.ball c' (r / 2)) := by
    change ((localChart L hrL c).toPartialEquiv.trans
            (localChart L hrL c').symm.toPartialEquiv).source = _
    rw [PartialEquiv.trans_source]
    rfl
  rw [hsrc] at hx₀
  obtain ⟨hx₀_ball, y₀, hy₀_ball, hxy₀⟩ := hx₀
  have hlam_mem : x₀ - y₀ ∈ L := by
    have : (Submodule.Quotient.mk x₀ : E ⧸ L) =
        Submodule.Quotient.mk y₀ := by
      simpa [Submodule.mkQ_apply] using hxy₀.symm
    exact (Submodule.Quotient.eq L).mp this
  refine ⟨x₀ - y₀, hlam_mem, ?_⟩
  set lam := x₀ - y₀ with hlam_def
  have h_x₀_minus : x₀ - lam = y₀ := by simp [hlam_def]
  have h_y₀ : x₀ - lam ∈ Metric.ball c' (r / 2) := by
    rw [h_x₀_minus]; exact hy₀_ball
  have h_ball_open_c : IsOpen (Metric.ball c (r / 2) : Set E) :=
    Metric.isOpen_ball
  have h_ball_open_c' : IsOpen (Metric.ball c' (r / 2) : Set E) :=
    Metric.isOpen_ball
  have h_translate_cont : Continuous (fun x : E => x - lam) :=
    continuous_id.sub continuous_const
  have h_preimage_open :
      IsOpen ((fun x : E => x - lam) ⁻¹' Metric.ball c' (r / 2)) :=
    h_ball_open_c'.preimage h_translate_cont
  have h_preimage_mem :
      x₀ ∈ (fun x : E => x - lam) ⁻¹' Metric.ball c' (r / 2) :=
    h_y₀
  set U : Set E := Metric.ball c (r / 2) ∩
                    (fun x : E => x - lam) ⁻¹' Metric.ball c' (r / 2)
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
    have heq : (Submodule.Quotient.mk (x - lam) : E ⧸ L) =
        Submodule.Quotient.mk x := by
      rw [Submodule.Quotient.eq L]; exact hmem
    simpa [Submodule.mkQ_apply] using heq
  have h_apply :
      (localChart L hrL c').symm (L.mkQ (x - lam)) = x - lam := by
    have hsrc : (x - lam) ∈ (localChart L hrL c').source := hxlam_in_ballc'
    have h := (localChart L hrL c').left_inv hsrc
    simpa using h
  rw [h_lattice_eq] at h_apply
  exact h_apply

/-! ### Complex-`ω` chart-transition regularity (generic) -/

/-- Translation by a constant on any complex normed space is `ContDiff ℂ n`. -/
private lemma contDiff_C_sub_const_generic {n : WithTop ℕ∞} (c : E) :
    ContDiff ℂ n (fun x : E => x - c) :=
  contDiff_id.sub contDiff_const

/-- Chart-change between any two atlas elements is `ContDiff ℂ n` on its
source, by reducing to translation by a lattice element. -/
private lemma contDiffOn_chart_transition_generic
    {r : ℝ} (hrL : ∀ x ∈ (L : Set E), ‖x‖ < r → x = 0)
    (c c' : E) (n : WithTop ℕ∞) :
    ContDiffOn ℂ n
      ((localChart L hrL c).trans (localChart L hrL c').symm)
      ((localChart L hrL c).trans (localChart L hrL c').symm).source := by
  intro x₀ hx₀
  obtain ⟨lam, _hlam_mem, h_eqOn⟩ :=
    transition_eventuallyEq_translation_generic L hrL c c' hx₀
  have hCD : ContDiffWithinAt ℂ n (fun x : E => x - lam)
      (((localChart L hrL c).trans (localChart L hrL c').symm).source) x₀ :=
    (contDiff_C_sub_const_generic lam).contDiffWithinAt
  exact hCD.congr_of_eventuallyEq (h_eqOn.filter_mono nhdsWithin_le_nhds)
      (h_eqOn.self_of_nhds)

/-! ### Complex-model `IsManifold` instance (generic) -/

/-- **Complex-`ω` analytic manifold structure on `E ⧸ L`** for any
finite-dimensional complex normed space `E` and any discrete full-rank
ℤ-lattice `L ≤ E`. The underlying `ChartedSpace E (E ⧸ L)` instance is
`chartedSpace_quotient_of_zlattice`, unchanged.

Stated as a `def` (not `instance`) to avoid diamond conflicts with the
existing `complex_isManifold_quotient_of_zlattice` (in
`PeriodLatticeComplexQuotient.lean`, specialized to `E = Fin g → ℂ`).
Downstream files instantiate this on the concrete `E` they need. -/
noncomputable def complex_isManifold_quotient_of_zlattice_generic
    (n : WithTop ℕ∞) :
    IsManifold (𝓘(ℂ, E)) n (E ⧸ L) := by
  refine isManifold_of_contDiffOn 𝓘(ℂ, E) n (E ⧸ L) ?_
  intro e e' he he'
  rcases he with ⟨c, hce⟩
  rcases he' with ⟨c', hc'e'⟩
  subst hce
  subst hc'e'
  have h := contDiffOn_chart_transition_generic L (discRadius_separates L) c c' n
  simp only [mfld_simps] at h ⊢
  exact h

end JacobianChallenge
