/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.IsManifold.Basic
import JacobianChallenge.Manifold.PeriodLatticeChartedSpace

/-! # `IsManifold 𝓘(ℝ, E) ⊤ (E ⧸ L)` for a `ℤ`-lattice `L` in finite-dim `E`

Builds on `PeriodLatticeChartedSpace.lean` which equips `E ⧸ L` with a
`ChartedSpace E` structure via local sections of the quotient map on small
balls. We prove that the chart-change between two such charts is locally a
translation by a lattice element, hence in particular `C^∞` (in fact analytic).

Construction:

* Each chart is `(localChart L _ c).symm` for some center `c : E`.
* The transition `localChart c ≫ₕ (localChart c').symm` is the partial map
  sending `x ∈ ball c (r/2)` to the unique `y ∈ ball c' (r/2)` with
  `L.mkQ y = L.mkQ x`.
* At any point `x₀` of the overlap, with image `y₀`, we set `λ := x₀ - y₀`.
  Then `λ ∈ L`, and on a neighborhood of `x₀` the map `x ↦ x - λ` lands in
  `ball c' (r/2)` and shares the lattice class of `x`, hence equals the
  transition by uniqueness of the local section.
* `x ↦ x - λ` is `ContDiff ℝ ⊤`, so the transition is `ContDiffWithinAt`
  at every point of its source.

Combined with `isManifold_of_contDiffOn`, this yields the manifold instance.
-/

open Set Metric

open scoped Manifold ContDiff

namespace JacobianChallenge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-! ### Computation lemmas for `localChart` -/

private lemma localChart_source
    {r : ℝ} (hrL : ∀ x ∈ (L : Set E), ‖x‖ < r → x = 0) (e : E) :
    (localChart L hrL e).source = Metric.ball e (r / 2) := rfl

private lemma localChart_target
    {r : ℝ} (hrL : ∀ x ∈ (L : Set E), ‖x‖ < r → x = 0) (e : E) :
    (localChart L hrL e).target = L.mkQ '' Metric.ball e (r / 2) := rfl

private lemma localChart_apply
    {r : ℝ} (hrL : ∀ x ∈ (L : Set E), ‖x‖ < r → x = 0) (e : E) (x : E) :
    (localChart L hrL e) x = L.mkQ x := rfl

/-- The image under `(localChart c).symm` of a class `q` in its target.
We do not unfold `invFunOn`; we only use defining properties via
`PartialEquiv.left_inv` / `right_inv`. -/
private lemma localChart_symm_apply_mkQ
    {r : ℝ} (hrL : ∀ x ∈ (L : Set E), ‖x‖ < r → x = 0) (e : E)
    {x : E} (hx : x ∈ Metric.ball e (r / 2)) :
    (localChart L hrL e).symm (L.mkQ x) = x := by
  -- `localChart c` is built from `InjOn.toPartialEquiv`, whose underlying
  -- `PartialEquiv` has `f := L.mkQ`. So `(localChart c).symm ∘ (localChart c) = id`
  -- on the source.
  have h := (localChart L hrL e).left_inv (by simpa [localChart_source] using hx)
  simpa [localChart_apply] using h

private lemma localChart_symm_mem_source
    {r : ℝ} (hrL : ∀ x ∈ (L : Set E), ‖x‖ < r → x = 0) (e : E)
    {x : E} (hx : x ∈ Metric.ball e (r / 2)) :
    L.mkQ x ∈ (localChart L hrL e).target := by
  have : (localChart L hrL e) x ∈ (localChart L hrL e).target :=
    (localChart L hrL e).map_source (by simpa [localChart_source] using hx)
  simpa [localChart_apply] using this

private lemma localChart_symm_target_eq
    {r : ℝ} (hrL : ∀ x ∈ (L : Set E), ‖x‖ < r → x = 0) (e : E) :
    (localChart L hrL e).symm.target = Metric.ball e (r / 2) :=
  (localChart L hrL e).symm_target.trans rfl

private lemma localChart_symm_source_eq
    {r : ℝ} (hrL : ∀ x ∈ (L : Set E), ‖x‖ < r → x = 0) (e : E) :
    (localChart L hrL e).symm.source = L.mkQ '' Metric.ball e (r / 2) :=
  (localChart L hrL e).symm_source.trans rfl

/-! ### Transition between two charts is locally a translation by a lattice element -/

/-- Key local property: at any point `x₀` of the overlap source, the chart-change
`localChart c ≫ₕ (localChart c').symm` agrees, on a neighborhood of `x₀`, with
translation by a fixed lattice element. -/
private lemma transition_eventuallyEq_translation
    {r : ℝ} (hrL : ∀ x ∈ (L : Set E), ‖x‖ < r → x = 0)
    (c c' : E)
    {x₀ : E}
    (hx₀ : x₀ ∈ ((localChart L hrL c).trans (localChart L hrL c').symm).source) :
    ∃ lam ∈ (L : Set E),
      (fun x : E => (((localChart L hrL c).trans (localChart L hrL c').symm)) x)
          =ᶠ[nhds x₀] (fun x : E => x - lam) := by
  classical
  -- Unfold the source.
  -- `((localChart c).trans (localChart c').symm).source =
  --    (localChart c).source ∩ (localChart c) ⁻¹' (localChart c').symm.source`
  --  = ball c (r/2) ∩ L.mkQ ⁻¹' (L.mkQ '' ball c' (r/2))`.
  have hsrc :
      ((localChart L hrL c).trans (localChart L hrL c').symm).source
        = Metric.ball c (r / 2) ∩
            (L.mkQ : E → E ⧸ L) ⁻¹' (L.mkQ '' Metric.ball c' (r / 2)) := by
    -- Compute via the underlying `PartialEquiv` machinery.
    change ((localChart L hrL c).toPartialEquiv.trans
            (localChart L hrL c').symm.toPartialEquiv).source = _
    rw [PartialEquiv.trans_source]
    rfl
  rw [hsrc] at hx₀
  obtain ⟨hx₀_ball, y₀, hy₀_ball, hxy₀⟩ := hx₀
  -- y₀ ∈ ball c' (r/2), L.mkQ y₀ = L.mkQ x₀.
  -- Define lambda = x₀ - y₀ ∈ L.
  have hlam_mem : x₀ - y₀ ∈ L := by
    have : (Submodule.Quotient.mk x₀ : E ⧸ L) = Submodule.Quotient.mk y₀ := by
      simpa [Submodule.mkQ_apply] using hxy₀.symm
    exact (Submodule.Quotient.eq L).mp this
  refine ⟨x₀ - y₀, hlam_mem, ?_⟩
  -- Show eventual equality with `x ↦ x - (x₀ - y₀)` near x₀.
  -- Need: for x close to x₀, transition x = x - (x₀ - y₀).
  -- Idea: pick a neighborhood U of x₀ such that
  --   (1) U ⊆ ball c (r/2)
  --   (2) for x ∈ U, x - (x₀ - y₀) ∈ ball c' (r/2)
  -- Then for such x: L.mkQ (x - (x₀ - y₀)) = L.mkQ x (since x₀ - y₀ ∈ L),
  -- so x - (x₀ - y₀) is the unique preimage of L.mkQ x in ball c' (r/2),
  -- and the transition equals `(localChart c').symm (L.mkQ x) = x - (x₀ - y₀)`.
  set lam := x₀ - y₀ with hlam_def
  -- Continuity of `x ↦ x - lam` and openness of ball c' (r/2):
  -- need a neighborhood of x₀ in ball c (r/2) where `x ↦ x - lam` is in ball c' (r/2).
  have h_x₀_minus : x₀ - lam = y₀ := by simp [hlam_def]
  have h_y₀ : x₀ - lam ∈ Metric.ball c' (r / 2) := by
    rw [h_x₀_minus]; exact hy₀_ball
  -- Find a ball around x₀ contained in ball c (r/2) ∩ preimage of ball c' (r/2).
  have h_ball_open_c : IsOpen (Metric.ball c (r / 2) : Set E) := Metric.isOpen_ball
  have h_ball_open_c' : IsOpen (Metric.ball c' (r / 2) : Set E) := Metric.isOpen_ball
  have h_translate_cont : Continuous (fun x : E => x - lam) :=
    continuous_id.sub continuous_const
  have h_preimage_open :
      IsOpen ((fun x : E => x - lam) ⁻¹' Metric.ball c' (r / 2)) :=
    h_ball_open_c'.preimage h_translate_cont
  have h_preimage_mem : x₀ ∈ (fun x : E => x - lam) ⁻¹' Metric.ball c' (r / 2) :=
    h_y₀
  set U : Set E := Metric.ball c (r / 2) ∩
                    (fun x : E => x - lam) ⁻¹' Metric.ball c' (r / 2)
  have hU_open : IsOpen U := h_ball_open_c.inter h_preimage_open
  have hU_mem : x₀ ∈ U := ⟨hx₀_ball, h_preimage_mem⟩
  have hU_nhds : U ∈ nhds x₀ := hU_open.mem_nhds hU_mem
  refine Filter.eventually_of_mem hU_nhds ?_
  intro x hxU
  obtain ⟨hx_in_ballc, hxlam_in_ballc'⟩ := hxU
  -- transition x = (localChart c').symm ((localChart c) x) = (localChart c').symm (L.mkQ x)
  show ((localChart L hrL c).trans (localChart L hrL c').symm) x = x - lam
  -- The transition `e₁ ≫ₕ e₂.symm` is the composition `e₂.symm ∘ e₁` on the source.
  have h_step1 : ((localChart L hrL c).trans (localChart L hrL c').symm) x
      = (localChart L hrL c').symm (L.mkQ x) := by
    change (localChart L hrL c').symm ((localChart L hrL c) x) = _
    rw [localChart_apply]
  rw [h_step1]
  -- show (localChart c').symm (L.mkQ x) = x - lam
  -- We have x - lam ∈ ball c' (r/2), and L.mkQ (x - lam) = L.mkQ x.
  have h_lattice_eq : L.mkQ (x - lam) = L.mkQ x := by
    have hsub : (x - lam) - x = -lam := by ring
    -- (x - lam) - x ∈ L ↔ Quotient.mk equal.
    have hmem : (x - lam) - x ∈ L := by
      rw [hsub]; exact L.neg_mem hlam_mem
    have heq : (Submodule.Quotient.mk (x - lam) : E ⧸ L) = Submodule.Quotient.mk x := by
      rw [Submodule.Quotient.eq L]; exact hmem
    simpa [Submodule.mkQ_apply] using heq
  -- Apply `localChart_symm_apply_mkQ` to `x - lam ∈ ball c' (r/2)`.
  have h_apply := localChart_symm_apply_mkQ L hrL c' hxlam_in_ballc'
  -- h_apply : (localChart c').symm (L.mkQ (x - lam)) = x - lam
  rw [h_lattice_eq] at h_apply
  exact h_apply

/-! ### `IsManifold` instance -/

/-- Subtraction of a constant is `C^n` everywhere. -/
private lemma contDiff_sub_const {n : WithTop ℕ∞} (c : E) :
    ContDiff ℝ n (fun x : E => x - c) :=
  contDiff_id.sub contDiff_const

/-- Chart-change between any two atlas elements is `C^∞` (in fact analytic),
because it equals translation by a lattice element on a neighborhood of every
point. -/
private lemma contDiffOn_chart_transition
    {r : ℝ} (hrL : ∀ x ∈ (L : Set E), ‖x‖ < r → x = 0)
    (c c' : E) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n
      ((localChart L hrL c).trans (localChart L hrL c').symm)
      ((localChart L hrL c).trans (localChart L hrL c').symm).source := by
  intro x₀ hx₀
  -- Get the lattice element and the local agreement.
  obtain ⟨lam, _hlam_mem, h_eqOn⟩ :=
    transition_eventuallyEq_translation L hrL c c' hx₀
  -- The map `x ↦ x - lam` is ContDiff, hence ContDiffWithinAt at x₀ on the source.
  have hCD : ContDiffWithinAt ℝ n (fun x : E => x - lam)
      (((localChart L hrL c).trans (localChart L hrL c').symm).source) x₀ :=
    (contDiff_sub_const lam).contDiffWithinAt
  -- Transfer along the eventual equality.
  exact hCD.congr_of_eventuallyEq (h_eqOn.filter_mono nhdsWithin_le_nhds)
      (h_eqOn.self_of_nhds)

/-- The quotient `E ⧸ L` of a finite-dimensional real normed space `E` by a
discrete `ℤ`-lattice `L` is a `C^n` manifold modeled on `E` (in fact analytic;
we state the form most useful for downstream elaboration). -/
noncomputable instance isManifold_quotient_of_zlattice (n : WithTop ℕ∞) :
    IsManifold 𝓘(ℝ, E) n (E ⧸ L) := by
  -- We use `isManifold_of_contDiffOn`. Charts in our atlas are exactly
  -- `(localChart L _ c).symm` for some `c : E`. The chart-change
  -- `e.symm ≫ₕ e'` is then `localChart c ≫ₕ (localChart c').symm`.
  refine isManifold_of_contDiffOn 𝓘(ℝ, E) n (E ⧸ L) ?_
  intro e e' he he'
  -- Extract the centers c, c'.
  rcases he with ⟨c, hce⟩
  rcases he' with ⟨c', hc'e'⟩
  -- e = (localChart c).symm, e' = (localChart c').symm
  subst hce
  subst hc'e'
  -- Now the chart-change is `(localChart c) ≫ₕ (localChart c').symm`,
  -- because `((localChart c).symm).symm = localChart c`.
  -- The model with corners is `𝓘(ℝ, E)`, so `I = id` and `range I = univ`.
  -- After simp, the source becomes the trans-source.
  have h := contDiffOn_chart_transition L (discRadius_separates L) c c' n
  -- Goal involves `((localChart c).symm).symm` which equals `localChart c`.
  -- Also `𝓘(ℝ,E)` is the identity model, so coercion and symm both act as `id`,
  -- and `range 𝓘(ℝ,E) = univ`. The `mfld_simps` simp set normalises this.
  simp only [mfld_simps] at h ⊢
  exact h

end JacobianChallenge
