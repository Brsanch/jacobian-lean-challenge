/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusTangentCoordChangeId
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Defs

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # `mfderiv (L.mkQ : ℂ → ℂ ⧸ L) p` is the identity ℝ-linear map

For any `p : ℂ` *that lies in the chart-source-ball at `mkQ p`*
(`p ∈ ball ((mkQ p).out) (discRadius L / 2)`), the projection
`mkQ : ℂ → ℂ ⧸ L` and the chart-inverse `(chartAt ℂ (mkQ p)).symm`
agree on a neighborhood of `p`. Hence

    `mfderiv mkQ p = mfderiv ((chartAt ℂ (mkQ p)).symm) p`.

The chain rule on `(chartAt ℂ q) ∘ (chartAt ℂ q).symm = id` at the
point `p` of the target then forces

    `(mfderiv (chartAt ℂ q) (mkQ p)) ∘L (mfderiv (chartAt ℂ q).symm p)
       = id`.

We already proved `mfderiv (chartAt ℂ q) (mkQ p) = id`
(`tangentCoordChange_eq_id_on_overlap`). So
`mfderiv (chartAt ℂ q).symm p = id`, hence `mfderiv mkQ p = id`.

For `p` NOT in `ball ((mkQ p).out) (r/2)`, we shift by a lattice element
to a translate that IS in the ball (mkQ is L-periodic, hence so is its
mfderiv up to identification).

## What this file ships

* `ComplexTorus.mfderiv_mkQ_apply_in_ball` — the result for `p` in
  the chart-source ball.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## mfderiv of `chartAt ℂ (mkQ p)` at `mkQ p` is the identity -/

/-- mfderiv of `chartAt ℂ (mkQ p)` at `mkQ p` is the identity ℝ-linear
map ℂ → ℂ. Direct application of
`mfderiv_chartAt_eq_tangentCoordChange` + `tangentCoordChange_self`. -/
private lemma mfderiv_chartAt_mkQ_eq_id (p : ℂ) :
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (chartAt ℂ (L.mkQ p)) (L.mkQ p)
      : TangentSpace 𝓘(ℝ, ℂ) (L.mkQ p) →L[ℝ] ℂ)
      = ContinuousLinearMap.id ℝ ℂ := by
  -- mfderiv (chartAt H y) x = tangentCoordChange I x y x for x ∈ chart-source.
  have hmem : L.mkQ p ∈ (chartAt ℂ (L.mkQ p)).source :=
    mem_chart_source ℂ (L.mkQ p)
  rw [mfderiv_chartAt_eq_tangentCoordChange (I := 𝓘(ℝ, ℂ)) hmem]
  -- tangentCoordChange I x x x = id (via coordChange_self).
  ext v
  apply tangentCoordChange_self (I := 𝓘(ℝ, ℂ)) (x := L.mkQ p)
    (z := L.mkQ p) (v := v)
  rw [extChartAt_source]
  exact hmem

/-! ## Local agreement of `mkQ` and `(chartAt ℂ (mkQ p)).symm` -/

/-- For `p ∈ ball ((mkQ p).out) (r/2)`, the map `(chartAt ℂ (mkQ p))`
evaluated at `mkQ p` returns `p` itself. -/
private lemma chartAt_mkQ_apply_in_ball (p : ℂ)
    (hp : p ∈ Metric.ball ((L.mkQ p).out) (discRadius L / 2)) :
    (chartAt ℂ (L.mkQ p) : (ℂ ⧸ L) → ℂ) (L.mkQ p) = p := by
  -- chartAt ℂ (mkQ p) = (localChart L _ (mkQ p).out).symm.
  -- (localChart c).symm (L.mkQ p) = the unique x ∈ ball c (r/2) with L.mkQ x = L.mkQ p.
  -- Since p is in ball c (r/2) with L.mkQ p = L.mkQ p, this is p.
  show (localChart L (discRadius_separates L) (L.mkQ p).out).symm
      ((localChart L (discRadius_separates L) (L.mkQ p).out) p) = p
  exact (localChart L (discRadius_separates L) (L.mkQ p).out).left_inv hp

/-- For `p ∈ ball ((mkQ p).out) (r/2)`, `mkQ` and `(chartAt ℂ (mkQ p)).symm`
agree on a neighborhood of `p`. Specifically, both equal each other
on the entire ball `ball ((mkQ p).out) (r/2)` (containing p). -/
private lemma mkQ_eqOn_chartAt_symm (p : ℂ)
    (hp : p ∈ Metric.ball ((L.mkQ p).out) (discRadius L / 2)) :
    Set.EqOn (L.mkQ : ℂ → ℂ ⧸ L)
      ((chartAt ℂ (L.mkQ p)).symm)
      (Metric.ball ((L.mkQ p).out) (discRadius L / 2)) := by
  intro x hx
  -- (chartAt _).symm x = (localChart _).symm.symm x = (localChart _) x = L.mkQ x for x ∈ ball.
  show L.mkQ x =
      (localChart L (discRadius_separates L) (L.mkQ p).out).symm.symm x
  rfl

/-- `mkQ =ᶠ[𝓝 p] (chartAt ℂ (mkQ p)).symm` for `p` in the chart-source ball. -/
private lemma mkQ_eventuallyEq_chartAt_symm (p : ℂ)
    (hp : p ∈ Metric.ball ((L.mkQ p).out) (discRadius L / 2)) :
    (L.mkQ : ℂ → ℂ ⧸ L) =ᶠ[nhds p] (chartAt ℂ (L.mkQ p)).symm := by
  refine Filter.eventually_of_mem (U := Metric.ball ((L.mkQ p).out) (discRadius L / 2))
    (Metric.isOpen_ball.mem_nhds hp) ?_
  intro x hx
  exact mkQ_eqOn_chartAt_symm L p hp hx

/-! ## mfderiv of `(chartAt ℂ (mkQ p)).symm` at `p` (= chart-symm at chart-image) -/

/-- mfderiv of `(chartAt ℂ q).symm` at `chartAt q (q)` is the identity.

By the chain rule on `chartAt ∘ chartAt.symm = id` on the chart-target,
combined with `mfderiv (chartAt) (q) = id`. -/
private lemma mfderiv_chartAt_symm_eq_id (p : ℂ)
    (hp : p ∈ Metric.ball ((L.mkQ p).out) (discRadius L / 2)) :
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (chartAt ℂ (L.mkQ p)).symm p
      : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (L.mkQ p))
      = ContinuousLinearMap.id ℝ ℂ := by
  -- chartAt ℂ (mkQ p) (chartAt _ .symm p) = p.
  -- We know chartAt ℂ (mkQ p) (mkQ p) = p (by chartAt_mkQ_apply_in_ball).
  -- And (chartAt _).symm p = mkQ p (since they agree on ball).
  have h_symm_p_eq_mkQ_p : (chartAt ℂ (L.mkQ p)).symm p = L.mkQ p := by
    have := mkQ_eqOn_chartAt_symm L p hp hp
    exact this.symm
  -- Compose: (chartAt (mkQ p)) ∘ (chartAt (mkQ p)).symm = id on target.
  -- At p ∈ target, mfderiv of this composite is id.
  -- By chain rule: mfderiv chartAt (chartAt_symm p) ∘L mfderiv chartAt_symm p = id.
  -- chartAt_symm p = mkQ p, so mfderiv chartAt (mkQ p) ∘L mfderiv chartAt_symm p = id.
  -- mfderiv chartAt (mkQ p) = id (mfderiv_chartAt_mkQ_eq_id), so id ∘L X = id, X = id.
  -- Formal version: use mfderiv chain rule from mathlib.
  -- A cleaner approach: chartAt ∘ chartAt_symm = id on target, p ∈ target.
  have hp_target : p ∈ (chartAt ℂ (L.mkQ p)).target := by
    -- Target of chartAt = source of chartAt.symm = ball (mkQ p).out (r/2).
    show p ∈ (localChart L (discRadius_separates L) (L.mkQ p).out).symm.target
    -- .symm.target = .source.
    rw [(localChart L (discRadius_separates L) (L.mkQ p).out).symm_target]
    exact hp
  -- For atlas chart, chartAt.symm ∘ chartAt = id on source, chartAt ∘ chartAt.symm = id on target.
  -- mfderiv (chartAt ∘ chartAt.symm) p (in ℂ → ℂ direction) = id.
  -- By chain rule and h_symm_p_eq_mkQ_p + mfderiv_chartAt_mkQ_eq_id, get mfderiv chartAt.symm p = id.
  have h_chartAt_symm_diff : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      (chartAt ℂ (L.mkQ p)).symm p := by
    -- atlas chart symms are MDifferentiableAt at target points.
    have h_atlas : (chartAt ℂ (L.mkQ p) : OpenPartialHomeomorph (ℂ ⧸ L) ℂ)
        ∈ atlas ℂ (ℂ ⧸ L) := chart_mem_atlas ℂ (L.mkQ p)
    exact mdifferentiableAt_atlas_symm (I := 𝓘(ℝ, ℂ)) h_atlas hp_target
  have h_chartAt_diff : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      (chartAt ℂ (L.mkQ p)) (L.mkQ p) := by
    have h_atlas : (chartAt ℂ (L.mkQ p) : OpenPartialHomeomorph (ℂ ⧸ L) ℂ)
        ∈ atlas ℂ (ℂ ⧸ L) := chart_mem_atlas ℂ (L.mkQ p)
    exact mdifferentiableAt_atlas (I := 𝓘(ℝ, ℂ)) h_atlas (mem_chart_source ℂ (L.mkQ p))
  -- Composition. We need: mfderiv (chartAt ∘ chartAt.symm) p applied to v equals v.
  -- chartAt ∘ chartAt.symm = id on a nbhd of p (the target is open).
  have h_comp_eqOn :
      Set.EqOn ((chartAt ℂ (L.mkQ p)) ∘ (chartAt ℂ (L.mkQ p)).symm)
        (id : ℂ → ℂ) (chartAt ℂ (L.mkQ p)).target := by
    intro x hx
    show (chartAt ℂ (L.mkQ p)) ((chartAt ℂ (L.mkQ p)).symm x) = x
    exact (chartAt ℂ (L.mkQ p)).right_inv hx
  have h_target_open : IsOpen ((chartAt ℂ (L.mkQ p)).target : Set ℂ) :=
    (chartAt ℂ (L.mkQ p)).open_target
  have h_comp_eventuallyEq :
      ((chartAt ℂ (L.mkQ p)) ∘ (chartAt ℂ (L.mkQ p)).symm : ℂ → ℂ)
        =ᶠ[nhds p] id := by
    refine Filter.eventually_of_mem
      (U := (chartAt ℂ (L.mkQ p)).target)
      (h_target_open.mem_nhds hp_target) ?_
    intro x hx
    exact h_comp_eqOn hx
  have h_mfderiv_comp_eq :
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
          ((chartAt ℂ (L.mkQ p)) ∘ (chartAt ℂ (L.mkQ p)).symm) p
        = mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (id : ℂ → ℂ) p :=
    h_comp_eventuallyEq.mfderiv_eq
  rw [mfderiv_id] at h_mfderiv_comp_eq
  -- Chain rule on the LHS.
  have h_chain :
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
          ((chartAt ℂ (L.mkQ p)) ∘ (chartAt ℂ (L.mkQ p)).symm) p
        = (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (chartAt ℂ (L.mkQ p))
              ((chartAt ℂ (L.mkQ p)).symm p)).comp
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (chartAt ℂ (L.mkQ p)).symm p) := by
    -- mfderiv_comp h_diff_outer h_diff_inner.
    apply mfderiv_comp p
    · rw [h_symm_p_eq_mkQ_p]; exact h_chartAt_diff
    · exact h_chartAt_symm_diff
  rw [h_chain] at h_mfderiv_comp_eq
  -- Substitute h_symm_p_eq_mkQ_p in the outer.
  rw [h_symm_p_eq_mkQ_p] at h_mfderiv_comp_eq
  rw [mfderiv_chartAt_mkQ_eq_id L p] at h_mfderiv_comp_eq
  -- After the chain rule rewrite, h_mfderiv_comp_eq has the form
  --   (id).comp (mfderiv chartAt.symm p) = id
  -- which simplifies to mfderiv chartAt.symm p = id via ContinuousLinearMap.id_comp.
  simpa using h_mfderiv_comp_eq

/-! ## mfderiv of `mkQ` at `p` for `p` in the chart-source ball -/

/-- **`mfderiv mkQ p = id`** when `p ∈ ball ((mkQ p).out) (r/2)`. -/
theorem mfderiv_mkQ_apply_in_ball (p : ℂ)
    (hp : p ∈ Metric.ball ((L.mkQ p).out) (discRadius L / 2)) :
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (L.mkQ : ℂ → ℂ ⧸ L) p
      : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (L.mkQ p))
      = ContinuousLinearMap.id ℝ ℂ := by
  -- mkQ =ᶠ[𝓝 p] (chartAt _).symm (proved above).
  have h_eq : (L.mkQ : ℂ → ℂ ⧸ L) =ᶠ[nhds p] (chartAt ℂ (L.mkQ p)).symm :=
    mkQ_eventuallyEq_chartAt_symm L p hp
  rw [h_eq.mfderiv_eq]
  exact mfderiv_chartAt_symm_eq_id L p hp

/-! ## Generalization to all `p ∈ ℂ` via L-translation invariance -/

/-- For any lattice element `lam ∈ L`, the translation `x ↦ x + lam`
sends the smooth structure on ℂ to itself with derivative `id`. The
key fact `mkQ ∘ (· + lam) = mkQ` is the L-periodicity of the quotient
projection. -/
private lemma mfderiv_translation (p : ℂ) (lam : ℂ) :
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun x : ℂ => x + lam) p : ℂ →L[ℝ] ℂ)
      = ContinuousLinearMap.id ℝ ℂ := by
  rw [mfderiv_eq_fderiv (f := fun x : ℂ => x + lam) (x := p)]
  have h : HasFDerivAt (fun x : ℂ => x + lam)
      (ContinuousLinearMap.id ℝ ℂ) p := by
    have h_id : HasFDerivAt (fun x : ℂ => x) (ContinuousLinearMap.id ℝ ℂ) p :=
      hasFDerivAt_id p
    have h_const : HasFDerivAt (fun _ : ℂ => lam) (0 : ℂ →L[ℝ] ℂ) p :=
      hasFDerivAt_const lam p
    have h_add := h_id.add h_const
    convert h_add using 1
    ext v; simp
  exact h.fderiv

/-- `(· + lam)` is MDifferentiableAt every point (trivially, since it's
ContDiff). -/
private lemma mdifferentiableAt_translation (p : ℂ) (lam : ℂ) :
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun x : ℂ => x + lam) p := by
  rw [mdifferentiableAt_iff_differentiableAt]
  exact (differentiable_id.add_const lam).differentiableAt

/-- **L-shift invariance applied at a value `v : ℂ`.** For any
lattice element `lam ∈ L` and any `p : ℂ`, the `mfderiv` of `mkQ`
at `p + lam` applied to `v` equals the `mfderiv` of `mkQ` at `p`
applied to `v`.

The TangentSpace types `TangentSpace _ (mkQ (p + lam))` and
`TangentSpace _ (mkQ p)` are *definitionally* both ℂ (since
`TangentSpace I (_x : M) := E` ignores its base-point argument).
So the equality is at the type ℂ. -/
private lemma mfderiv_mkQ_shift_apply
    {lam : ℂ} (hlam : lam ∈ L) (p : ℂ) (v : ℂ) :
    (((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (L.mkQ : ℂ → ℂ ⧸ L) (p + lam)
        : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (L.mkQ (p + lam))) v) : ℂ)
      = (((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (L.mkQ : ℂ → ℂ ⧸ L) p
          : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (L.mkQ p)) v) : ℂ) := by
  -- `mkQ ∘ (· + lam) = mkQ` as functions (L-invariance).
  have h_fun_eq : (L.mkQ : ℂ → ℂ ⧸ L) ∘ (fun x : ℂ => x + lam) = L.mkQ := by
    funext x
    show L.mkQ (x + lam) = L.mkQ x
    rw [map_add]
    have h0 : L.mkQ lam = 0 := (Submodule.Quotient.mk_eq_zero L).mpr hlam
    rw [h0, add_zero]
  -- Chain rule on (mkQ ∘ (·+lam)) at p:
  --   mfderiv (mkQ ∘ (·+lam)) p = (mfderiv mkQ (p+lam)) ∘L (mfderiv (·+lam) p)
  -- Applied to v: = (mfderiv mkQ (p+lam)) ((mfderiv (·+lam) p) v) = (mfderiv mkQ (p+lam)) v
  -- (since mfderiv (·+lam) p v = v).
  have h_diff_lam : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      (fun x : ℂ => x + lam) p := mdifferentiableAt_translation p lam
  have h_diff_mkQ_shift : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      (L.mkQ : ℂ → ℂ ⧸ L) (p + lam) :=
    (mkQ_contMDiff_real L 1).contMDiffAt.mdifferentiableAt one_ne_zero
  have h_chain_apply :
      ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
        ((L.mkQ : ℂ → ℂ ⧸ L) ∘ (fun x : ℂ => x + lam)) p) v : ℂ)
        = ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) L.mkQ (p + lam))
            ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun x : ℂ => x + lam) p) v) : ℂ) := by
    rw [mfderiv_comp p h_diff_mkQ_shift h_diff_lam]
    rfl
  -- The translation mfderiv applied to v gives v.
  have h_trans_apply :
      ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun x : ℂ => x + lam) p) v : ℂ) = v := by
    rw [mfderiv_translation p lam]
    rfl
  rw [h_trans_apply] at h_chain_apply
  -- h_chain_apply : (mfderiv (mkQ ∘ (·+lam)) p v) = (mfderiv mkQ (p+lam) v).
  -- And mkQ ∘ (·+lam) = mkQ as functions, so the LHS = mfderiv mkQ p v.
  rw [h_fun_eq] at h_chain_apply
  -- h_chain_apply : (mfderiv mkQ p v) = (mfderiv mkQ (p+lam) v).
  exact h_chain_apply.symm

/-- **`mfderiv mkQ p` applied to any `v : ℂ` equals `v`** for any
`p : ℂ`. Generalizes `mfderiv_mkQ_apply_in_ball` to all of ℂ via the
L-shift invariance argument. -/
theorem mfderiv_mkQ_apply (p : ℂ) (v : ℂ) :
    (((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (L.mkQ : ℂ → ℂ ⧸ L) p
        : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (L.mkQ p)) v) : ℂ) = v := by
  -- Pick p₀ := (mkQ p).out. Then p₀ + (p - p₀) = p, and (p - p₀) ∈ L.
  set p₀ : ℂ := (L.mkQ p).out with hp₀_def
  set lam : ℂ := p - p₀ with hlam_def
  have h_mkQ_p₀ : L.mkQ p₀ = L.mkQ p := by
    show (Quotient.mk'' (Quotient.out (L.mkQ p)) : ℂ ⧸ L) = L.mkQ p
    exact Quotient.out_eq (L.mkQ p)
  have hlam_mem : lam ∈ L := by
    have : L.mkQ lam = 0 := by
      rw [hlam_def, map_sub, h_mkQ_p₀, sub_self]
    exact (Submodule.Quotient.mk_eq_zero L).mp this
  have h_p_eq : p₀ + lam = p := by
    rw [hlam_def]; ring
  -- p₀ is the canonical representative; ball ((mkQ p₀).out) (r/2) = ball p₀ (r/2)
  -- contains p₀ trivially.
  have h_p₀_out : (L.mkQ p₀).out = p₀ := by rw [h_mkQ_p₀]
  have h_p₀_in_ball : p₀ ∈ Metric.ball ((L.mkQ p₀).out) (discRadius L / 2) := by
    rw [h_p₀_out]
    have hr_pos : 0 < discRadius L := discRadius_pos L
    have hr2_pos : 0 < discRadius L / 2 := by linarith
    simp [Metric.mem_ball, dist_self, hr2_pos]
  -- Apply the ball version to p₀.
  have h_p₀_id : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (L.mkQ : ℂ → ℂ ⧸ L) p₀
      : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (L.mkQ p₀)) = ContinuousLinearMap.id ℝ ℂ :=
    mfderiv_mkQ_apply_in_ball L p₀ h_p₀_in_ball
  have h_p₀_apply :
      (((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (L.mkQ : ℂ → ℂ ⧸ L) p₀
          : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (L.mkQ p₀)) v) : ℂ) = v := by
    rw [h_p₀_id]
    rfl
  -- Use shift invariance.
  have h_shift := mfderiv_mkQ_shift_apply L hlam_mem p₀ v
  -- h_shift : mfderiv mkQ (p₀ + lam) v = mfderiv mkQ p₀ v (both coerced to ℂ).
  rw [h_p_eq] at h_shift
  -- h_shift : mfderiv mkQ p v = mfderiv mkQ p₀ v (in ℂ).
  rw [h_shift]
  exact h_p₀_apply

end ComplexTorus

end JacobianChallenge

end
