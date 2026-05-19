/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusTangentCoordChangeId
import JacobianChallenge.Manifold.HolomorphicOneForm

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-! # The canonical holomorphic 1-form `dz` on the complex torus

For the complex torus `T_L = ℂ ⧸ L`, the canonical holomorphic 1-form
`dz : HolomorphicOneForm T_L` is the constant section of the cotangent
bundle picking the identity `ℂ →L[ℂ] ℂ` at every point.

This section is well-defined and smooth because the cotangent
coord-change on the torus is the identity (proved in
`ComplexTorusTangentCoordChangeId.lean`): chart-changes are
translations, whose Fréchet derivative is the identity, and the
cotangent coord-change is precomposition with the (inverse of the)
tangent coord-change.

## What this file ships

* `ComplexTorus.dz L : HolomorphicOneForm (ℂ ⧸ L)` — the constant
  section.

* `ComplexTorus.dz_apply L p` — the explicit value at any point.

No `sorry`, no `axiom`. -/

open Bundle Set
open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## ContMDiff of the constant cotangent section -/

/-- **The constant cotangent section, viewed in the trivialization at
`x`, is the constant `id` on a neighborhood of `x`.**

For the cotangentBundleCore on `ℂ ⧸ L`, the local trivialization at
`x` of the constant section `fun _ => id` is given by
`y ↦ coordChange (achart y) (achart x) y id`. By
`cotangentBundleCore_coordChange_eq_id_on_overlap`, this equals `id`
constantly on the overlap of x's and y's chart-sources, which
contains a neighborhood of `x`. -/
private lemma constSection_localRep_eventuallyEq_id (x : ℂ ⧸ L) :
    (fun y : ℂ ⧸ L =>
        (cotangentBundleCore (𝓘(ℂ, ℂ)) (ℂ ⧸ L)).coordChange
          (achart ℂ y) (achart ℂ x) y (ContinuousLinearMap.id ℂ ℂ))
      =ᶠ[nhds x] (fun _ : ℂ ⧸ L => (ContinuousLinearMap.id ℂ ℂ)) := by
  -- The overlap of (chartAt x).source with itself (= (chartAt x).source) is
  -- an open nhd of x, and on it the coordChange is identity.
  have h_open : IsOpen ((chartAt ℂ x).source : Set (ℂ ⧸ L)) :=
    (chartAt ℂ x).open_source
  have h_mem : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  refine Filter.eventually_of_mem (h_open.mem_nhds h_mem) (fun y hy => ?_)
  -- For y ∈ (chartAt x).source, achart y has y in baseSet (= chartAt y .source),
  -- and y ∈ (chartAt x).source. So z ∈ overlap, and cotangent coordChange = id.
  have h_xy : y ∈ (extChartAt 𝓘(ℂ, ℂ) x).source ∩
                (extChartAt 𝓘(ℂ, ℂ) y).source := by
    refine ⟨?_, ?_⟩
    · rw [extChartAt_source]; exact hy
    · rw [extChartAt_source]; exact mem_chart_source ℂ y
  -- For the formula, we need coordChange (achart y) (achart x) y id; reverse direction.
  -- But our theorem is cotangentBundleCore.coordChange (achart x) (achart y) z = id.
  -- Apply with (x := y), (y := x).
  have h := cotangentBundleCore_coordChange_eq_id_on_overlap L y x
    (h_xy.symm) (ContinuousLinearMap.id ℂ ℂ)
  -- h: cotangentBundleCore.coordChange (achart y) (achart x) y id = id.
  exact h

/-! ## ContMDiff of the constant cotangent section as a section -/

/-- **The constant cotangent section `fun _ => id` is `ContMDiff` at
every point** for any regularity `n`. -/
private theorem const_id_cotangentSection_contMDiffAt
    (n : WithTop ℕ∞) (x : ℂ ⧸ L) :
    ContMDiffAt 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) n
      (fun y : ℂ ⧸ L =>
        TotalSpace.mk' (E := (CotangentSpace 𝓘(ℂ, ℂ) : (ℂ ⧸ L) → Type _))
          (ℂ →L[ℂ] ℂ) y
          ((ContinuousLinearMap.id ℂ ℂ : ℂ →L[ℂ] ℂ) :
            CotangentSpace 𝓘(ℂ, ℂ) y)) x := by
  -- Use the trivializationAt and contMDiffAt_section_iff.
  let e := trivializationAt (ℂ →L[ℂ] ℂ) (CotangentSpace 𝓘(ℂ, ℂ)) x
  have hxe : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  -- The trivialization e for the cotangentBundleCore is localTriv (achart ℂ x).
  -- So (e ⟨y, ξ⟩).2 = coordChange (achart y) (achart x) y ξ for y ∈ baseSet.
  rw [e.contMDiffAt_section_iff hxe]
  -- Goal: ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) n
  --         (fun y => (e ⟨y, id⟩).2) x
  -- We show this function is locally constant equal to id near x.
  have h_eq := constSection_localRep_eventuallyEq_id L x
  -- The local rep equation: (e ⟨y, id⟩).2 = coordChange (achart y) (achart x) y id
  -- on baseSet. So on baseSet, (e ⟨y, id⟩).2 = id (by h_eq).
  -- Combine via ContMDiffAt.congr_of_eventuallyEq:
  --   `(constant : ContMDiffAt const x).congr_of_eventuallyEq h_eq`
  -- yields ContMDiffAt (local_rep) x.
  refine ContMDiffAt.congr_of_eventuallyEq
    (contMDiffAt_const (c := (ContinuousLinearMap.id ℂ ℂ : ℂ →L[ℂ] ℂ))) ?_
  -- Show local_rep =ᶠ[𝓝 x] constant id.
  · -- Local-rep eventually equals constant id.
    -- (e ⟨y, id⟩).2 for cotangentBundleCore.localTriv (achart x) is exactly
    -- coordChange (indexAt y) (achart x) y id = coordChange (achart y) (achart x) y id.
    -- Combine with h_eq: this is eventually id near x.
    have h_open : IsOpen ((chartAt ℂ x).source : Set (ℂ ⧸ L)) :=
      (chartAt ℂ x).open_source
    have h_mem : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    refine Filter.eventually_of_mem (h_open.mem_nhds h_mem) (fun y hy => ?_)
    -- Goal: (e ⟨y, id⟩).2 = id.
    -- The trivializationAt is the localTriv at indexAt x = achart x.
    -- (Z.localTriv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩.
    -- So (e ⟨y, id⟩).2 = coordChange (indexAt y) (achart x) y id
    --                  = coordChange (achart y) (achart x) y id.
    have h_xy : y ∈ (extChartAt 𝓘(ℂ, ℂ) x).source ∩
                  (extChartAt 𝓘(ℂ, ℂ) y).source := by
      refine ⟨?_, ?_⟩
      · rw [extChartAt_source]; exact hy
      · rw [extChartAt_source]; exact mem_chart_source ℂ y
    have h_coord :=
      cotangentBundleCore_coordChange_eq_id_on_overlap L y x h_xy.symm
        (ContinuousLinearMap.id ℂ ℂ)
    -- h_coord: coordChange (achart y) (achart x) y id = id.
    -- (e ⟨y, id⟩).2 = coordChange (indexAt y) (achart x) y id (by localTriv_apply).
    show (e ⟨y, ContinuousLinearMap.id ℂ ℂ⟩).2 = ContinuousLinearMap.id ℂ ℂ
    -- e = (cotangentBundleCore _).localTriv (achart x).
    -- (localTriv i) p = ⟨p.1, coordChange (indexAt p.1) i p.1 p.2⟩.
    change ((((cotangentBundleCore 𝓘(ℂ, ℂ) (ℂ ⧸ L)).localTriv (achart ℂ x))
        ⟨y, ContinuousLinearMap.id ℂ ℂ⟩).2 : ℂ →L[ℂ] ℂ)
      = ContinuousLinearMap.id ℂ ℂ
    rw [VectorBundleCore.localTriv_apply]
    -- Goal: (coordChange (indexAt y) (achart x) y id) = id.
    -- indexAt y = achart H y = achart ℂ y by cotangentBundleCore definition.
    exact h_coord

/-- **The constant cotangent section `fun _ => id` is `ContMDiff` at
every regularity `n`.** -/
private theorem const_id_cotangentSection_contMDiff (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) n
      (fun y : ℂ ⧸ L =>
        TotalSpace.mk' (E := (CotangentSpace 𝓘(ℂ, ℂ) : (ℂ ⧸ L) → Type _))
          (ℂ →L[ℂ] ℂ) y
          ((ContinuousLinearMap.id ℂ ℂ : ℂ →L[ℂ] ℂ) :
            CotangentSpace 𝓘(ℂ, ℂ) y)) :=
  fun x => const_id_cotangentSection_contMDiffAt L n x

/-! ## The canonical holomorphic 1-form `dz` -/

/-- **The canonical holomorphic 1-form `dz` on `ℂ ⧸ L`.** Constant
section of the cotangent bundle picking the identity ℂ-linear map at
every point. The smoothness witness uses the proof that the cotangent
coord-change on the torus is the identity (chart changes are
translations, with identity derivative). -/
noncomputable def dz : HolomorphicOneForm (ℂ ⧸ L) where
  toFun := fun p : ℂ ⧸ L =>
    (ContinuousLinearMap.id ℂ ℂ : CotangentSpace (𝓘(ℂ, ℂ)) (M := ℂ ⧸ L) p)
  contMDiff_toFun := const_id_cotangentSection_contMDiff L ω

@[simp] lemma dz_apply (p : ℂ ⧸ L) :
    (dz L).toFun p = (ContinuousLinearMap.id ℂ ℂ :
      CotangentSpace (𝓘(ℂ, ℂ)) (M := ℂ ⧸ L) p) := rfl

/-- **`dz` is a nonzero holomorphic 1-form on `ℂ ⧸ L`.** Hence
`HolomorphicOneForm (ℂ ⧸ L)` contains at least one nonzero element,
giving the **lower bound** `1 ≤ Module.finrank ℂ (HolomorphicOneForm
(ℂ ⧸ L))` once a complementary Liouville-style upper bound is in
tree. -/
theorem dz_ne_zero : dz L ≠ 0 := by
  intro h
  -- If dz = 0, then dz.toFun p = 0 for every p. In particular for p = 0.
  have h_apply : (dz L).toFun 0 = (0 : HolomorphicOneForm (ℂ ⧸ L)).toFun 0 := by
    rw [h]
  -- (0 : HolomorphicOneForm).toFun 0 = 0 (the zero cotangent vector).
  -- But (dz L).toFun 0 = id, which is nonzero as a CLM.
  have h_id : (dz L).toFun (0 : ℂ ⧸ L)
      = (ContinuousLinearMap.id ℂ ℂ :
          CotangentSpace (𝓘(ℂ, ℂ)) (M := ℂ ⧸ L) 0) :=
    dz_apply L 0
  -- Combine.
  rw [h_id] at h_apply
  -- h_apply : id = (0 : HolomorphicOneForm).toFun 0 = 0.
  -- The CotangentSpace fiber `CotangentSpace 𝓘(ℂ,ℂ) 0` is `ℂ →L[ℂ] ℂ`.
  -- `(0 : HolomorphicOneForm).toFun 0 = 0` definitionally.
  have h_zero_toFun :
      ((0 : HolomorphicOneForm (ℂ ⧸ L)).toFun 0 :
        CotangentSpace (𝓘(ℂ, ℂ)) (M := ℂ ⧸ L) 0)
      = (0 : ℂ →L[ℂ] ℂ) := rfl
  rw [h_zero_toFun] at h_apply
  -- h_apply: id = 0 in ℂ →L[ℂ] ℂ. Apply both sides to 1 : ℂ.
  have h_one : (ContinuousLinearMap.id ℂ ℂ) (1 : ℂ) = (0 : ℂ →L[ℂ] ℂ) (1 : ℂ) := by
    rw [h_apply]
  -- LHS = 1, RHS = 0.
  simp at h_one

/-- **`HolomorphicOneForm (ℂ ⧸ L)` is nontrivial.** Direct consequence
of `dz_ne_zero` — `dz` is a nonzero element. -/
theorem nontrivial_holomorphicOneForm :
    Nontrivial (HolomorphicOneForm (ℂ ⧸ L)) :=
  ⟨dz L, 0, dz_ne_zero L⟩

end ComplexTorus

end JacobianChallenge

end
