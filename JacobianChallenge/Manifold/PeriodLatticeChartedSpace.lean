/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! # `ChartedSpace E (E ⧸ L)` for a `ℤ`-lattice `L` in finite-dimensional `E`

Companion to `PeriodLatticeCompactQuotient.lean`. We equip the quotient
`E ⧸ L` with a charted-space structure modelled on `E`, by exhibiting a
local homeomorphism on a small ball around each representative.

The construction uses three ingredients:

* `DiscreteTopology L` provides a positive radius `r > 0` such that
  `Metric.ball 0 r ∩ (L : Set E) ⊆ {0}` (the discreteness radius).
* `Submodule.isOpenMap_mkQ` makes the quotient projection
  `π = L.mkQ : E → E ⧸ L` an open map.
* On `Metric.ball e (r/2)` the map `π` is injective: any two preimages
  of the same quotient point differ by an element of `L`, but their
  difference has norm `< r`, hence equals `0`.

A continuous injection from an open set whose restriction is an open map
yields an `OpenPartialHomeomorph E (E ⧸ L)` via
`OpenPartialHomeomorph.ofContinuousOpenRestrict`.

We state the result for `Submodule ℤ E` (the shape required by
`IsZLattice ℝ`); the quotient `E ⧸ L` is automatically an additive
commutative topological group.
-/

open Set Metric

namespace JacobianChallenge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Discreteness radius -/

/-- A `DiscreteTopology` ℤ-submodule of a normed space admits a positive
radius whose open ball meets the lattice only at `0`. -/
private lemma exists_discreteness_radius (L : Submodule ℤ E) [DiscreteTopology L] :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ (L : Set E), ‖x‖ < r → x = 0 := by
  -- `DiscreteTopology L` ⇒ `{0}` is open in `L` ⇒ there is an open `V` in `E`
  -- with `Subtype.val ⁻¹' V = {0}`, hence `V ∩ L ⊆ {0}`.
  have hopen : IsOpen ({(0 : L)} : Set L) := isOpen_discrete _
  rw [isOpen_induced_iff] at hopen
  obtain ⟨V, hVopen, hVeq⟩ := hopen
  have h0V : (0 : E) ∈ V := by
    have h0 : (⟨0, L.zero_mem⟩ : L) ∈ ({(0 : L)} : Set L) := rfl
    have : (⟨0, L.zero_mem⟩ : L) ∈ ((Subtype.val : L → E) ⁻¹' V) := by
      rw [hVeq]; exact h0
    exact this
  obtain ⟨r, hr0, hrV⟩ := Metric.isOpen_iff.mp hVopen 0 h0V
  refine ⟨r, hr0, ?_⟩
  intro x hxL hxr
  have hx_in_ball : x ∈ Metric.ball (0 : E) r := by
    simp [Metric.mem_ball, dist_zero_right, hxr]
  have hxV : x ∈ V := hrV hx_in_ball
  have hxLifted : (⟨x, hxL⟩ : L) ∈ ((Subtype.val : L → E) ⁻¹' V) := hxV
  rw [hVeq] at hxLifted
  exact congrArg Subtype.val hxLifted

/-! ### Local injectivity -/

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- `L.mkQ` is injective on any open ball of radius `r/2`, where `r` is a
discreteness radius for `L`. -/
private lemma mkQ_injOn_ball
    {r : ℝ} (hrL : ∀ x ∈ (L : Set E), ‖x‖ < r → x = 0)
    (e : E) : Set.InjOn L.mkQ (Metric.ball e (r/2)) := by
  intro x hx y hy hxy
  -- `L.mkQ x = L.mkQ y` ↔ `x - y ∈ L`.
  have hxy' : (Submodule.Quotient.mk x : E ⧸ L) = Submodule.Quotient.mk y := by
    simpa [Submodule.mkQ_apply] using hxy
  have hsub : x - y ∈ L := (Submodule.Quotient.eq L).mp hxy'
  -- `‖x - y‖ < r` from triangle inequality with `e`.
  rw [Metric.mem_ball, dist_eq_norm] at hx hy
  have hxy_norm : ‖x - y‖ < r := by
    have hsplit : x - y = (x - e) - (y - e) := by ring
    calc ‖x - y‖ = ‖(x - e) - (y - e)‖ := by rw [hsplit]
      _ ≤ ‖x - e‖ + ‖y - e‖ := norm_sub_le _ _
      _ < r/2 + r/2 := by linarith
      _ = r := by ring
  have hxy_zero : x - y = 0 := hrL (x - y) hsub hxy_norm
  exact sub_eq_zero.mp hxy_zero

/-! ### Local chart construction -/

/-- The local chart on `E ⧸ L` around the image of a point `e ∈ E`,
built from a discreteness radius `r > 0`. Source is `Metric.ball e (r/2)`,
target is its image under `L.mkQ`. -/
private noncomputable def localChart
    {r : ℝ} (hrL : ∀ x ∈ (L : Set E), ‖x‖ < r → x = 0) (e : E) :
    OpenPartialHomeomorph E (E ⧸ L) := by
  classical
  set s : Set E := Metric.ball e (r/2)
  have hs_open : IsOpen s := Metric.isOpen_ball
  have hinj : Set.InjOn L.mkQ s := mkQ_injOn_ball L hrL e
  haveI : Nonempty E := ⟨0⟩
  let pe : PartialEquiv E (E ⧸ L) := hinj.toPartialEquiv L.mkQ s
  have hpe_source : pe.source = s := rfl
  refine OpenPartialHomeomorph.ofContinuousOpenRestrict pe ?_ ?_ ?_
  · -- ContinuousOn on `pe.source = s`.
    rw [hpe_source]
    exact L.mkQ.continuous.continuousOn
  · -- The set restriction is an open map.
    rw [hpe_source]
    intro U hU
    rw [isOpen_induced_iff] at hU
    obtain ⟨V, hVopen, hVeq⟩ := hU
    have himage : (s.restrict L.mkQ) '' U = L.mkQ '' (V ∩ s) := by
      ext q
      simp only [Set.mem_image, Set.restrict_apply, Subtype.exists, mem_inter_iff]
      constructor
      · rintro ⟨x, hxs, hxU, hqx⟩
        refine ⟨x, ⟨?_, hxs⟩, hqx⟩
        have h1 : (⟨x, hxs⟩ : s) ∈ U := hxU
        have h2 : (⟨x, hxs⟩ : s) ∈ (Subtype.val : s → E) ⁻¹' V := by
          rw [hVeq]; exact h1
        exact h2
      · rintro ⟨x, ⟨hxV, hxs⟩, hqx⟩
        refine ⟨x, hxs, ?_, hqx⟩
        have h2 : (⟨x, hxs⟩ : s) ∈ (Subtype.val : s → E) ⁻¹' V := hxV
        rw [← hVeq] at h2
        exact h2
    rw [himage]
    exact L.isOpenMap_mkQ _ (hVopen.inter hs_open)
  · exact hs_open

/-! ### The `ChartedSpace` instance -/

/-- For a finite-dimensional real normed space `E` and a discrete full-rank
`ℤ`-lattice `L` in `E`, the quotient `E ⧸ L` is a `ChartedSpace E`. Charts
are local sections of the quotient map on small balls. -/
noncomputable instance chartedSpace_quotient_of_zlattice :
    ChartedSpace E (E ⧸ L) := by
  classical
  -- Pick a discreteness radius once and for all.
  obtain ⟨r, hr, hrL⟩ := exists_discreteness_radius L
  refine
    { atlas := Set.range (fun e : E => (localChart L hrL e).symm)
      chartAt := fun q => (localChart L hrL q.out).symm
      mem_chart_source := ?_
      chart_mem_atlas := ?_ }
  · intro q
    -- Source of `(localChart …).symm` is target of `localChart …`,
    -- which is `L.mkQ '' Metric.ball q.out (r/2)`. We need `q ∈ that image`.
    show q ∈ (localChart L hrL q.out).symm.source
    have hsource_eq :
        (localChart L hrL q.out).symm.source = (localChart L hrL q.out).target := rfl
    rw [hsource_eq]
    -- Unfold the target.
    have htarget :
        (localChart L hrL q.out).target =
          L.mkQ '' Metric.ball q.out (r/2) := by
      rfl
    rw [htarget]
    refine ⟨q.out, ?_, ?_⟩
    · simp [Metric.mem_ball, dist_self, half_pos hr]
    · -- `L.mkQ q.out = q`.
      change L.mkQ (Quotient.out q) = q
      have hq : (Quotient.mk'' (Quotient.out q) : E ⧸ L) = q := Quotient.out_eq q
      have h1 : (Submodule.Quotient.mk (Quotient.out q) : E ⧸ L) = q := by
        rw [show (Submodule.Quotient.mk (Quotient.out q) : E ⧸ L)
              = Quotient.mk'' (Quotient.out q) from rfl]
        exact hq
      simpa [Submodule.mkQ_apply] using h1
  · intro q
    exact ⟨q.out, rfl⟩

end JacobianChallenge
