/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathConstFromFace0
import JacobianChallenge.Manifold.SmoothPathExt
import JacobianChallenge.Manifold.SmoothPathReverse
import JacobianChallenge.Manifold.SmoothPathIntegral

set_option linter.unusedSectionVars false

/-! # Smooth 2-simplex from a smooth path via first-coordinate projection

Given `γ : SmoothPath I X`, the smooth 2-simplex
`σ_γ(x) := γ.ambient (x 0)` (depending only on the first coordinate)
has three identifiable faces:

* `face0 σ_γ = γ.reverse` (the path `t ↦ γ.ambient (1 - t)`).
* `face1 σ_γ = SmoothPath.const I X γ.src` (constant, since
  `σ_γ(0, t)` has first coord `0`).
* `face2 σ_γ = γ` (the path `t ↦ γ.ambient t`, definitionally equal
  to `γ` via the smoothness witness's `ambient_eq_on_unitInterval`).

So
```
boundary σ_γ = single γ.reverse - single (const γ.src) + single γ
            ∈ stokesBoundaries I X.
```

Combined with `single (const γ.src) ∈ stokesBoundaries` (from
`SmoothPathConstFromFace0.lean`), this gives the **forward-plus-
reverse identity**:
```
single γ + single γ.reverse ∈ stokesBoundaries I X.
```

Geometrically: `γ` and `γ.reverse` are homologous-inverse modulo
Stokes-boundaries on a smooth singular complex.

## What this file ships

* `Smooth2Simplex.ofSmoothPathFstProj γ : Smooth2Simplex I X` — the
  smooth 2-simplex.
* `face0_ofSmoothPathFstProj_eq_reverse` — `face0 σ_γ = γ.reverse`.
* `face1_ofSmoothPathFstProj_eq_const_src` —
  `face1 σ_γ = SmoothPath.const I X γ.src`.
* `face2_ofSmoothPathFstProj_eq` — `face2 σ_γ = γ`.
* `boundary_ofSmoothPathFstProj_eq` — the boundary chain identity.
* `single_smoothPath_plus_reverse_mem_stokesBoundaries` — the
  forward-plus-reverse identity (packaged as SmoothCycle membership).

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-- **Smooth 2-simplex from a smooth path via first-coordinate
projection.** -/
noncomputable def Smooth2Simplex.ofSmoothPathFstProj (γ : SmoothPath I X) :
    Smooth2Simplex I X where
  toFun := fun x : Fin 2 → ℝ => γ.ambient (x 0)
  smooth := by
    -- σ_γ is the composition of γ.ambient (smooth ℝ → X) with the
    -- continuous-linear projection `fun x : Fin 2 → ℝ => x 0`.
    have h_proj : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞
        (fun x : Fin 2 → ℝ => x 0) := by
      -- The projection `(· 0)` is a continuous linear map ℝ-linear in `x`,
      -- hence C^∞.
      have h_clm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : Fin 2 → ℝ => x 0) :=
        (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff
      exact h_clm.contMDiff
    exact γ.ambient_contMDiff.comp h_proj

variable (γ : SmoothPath I X)

@[simp] lemma Smooth2Simplex.ofSmoothPathFstProj_toFun
    (x : Fin 2 → ℝ) :
    (Smooth2Simplex.ofSmoothPathFstProj γ).toFun x = γ.ambient (x 0) := rfl

/-! ## Face identifications -/

/-- **face0 of σ_γ equals γ.reverse.** Both are smooth paths from
`γ.tgt` to `γ.src` with the same underlying toPath
`t ↦ γ.ambient (1 - t.val)`. -/
lemma face0_ofSmoothPathFstProj_eq_reverse :
    Smooth2Simplex.face0 (Smooth2Simplex.ofSmoothPathFstProj γ)
      = γ.reverse := by
  -- Apply SmoothPath.ext.
  apply SmoothPath.ext
  · -- src: face0.src = σ_γ.toFun v1 = γ.ambient 1 = γ.tgt = γ.reverse.src
    show γ.ambient ((Smooth2Simplex.v1 : Fin 2 → ℝ) 0) = γ.tgt
    show γ.ambient 1 = γ.tgt
    -- Use γ.ambient_eq_on_unitInterval at t = 1.
    have h := γ.ambient_eq_on_unitInterval
      (⟨1, by constructor <;> norm_num⟩ : unitInterval)
    show γ.ambient 1 = γ.tgt
    have hval : ((⟨1, by constructor <;> norm_num⟩ : unitInterval).val : ℝ) = 1 :=
      rfl
    rw [hval] at h
    rw [h]
    exact γ.toPath.target'
  · -- tgt: face0.tgt = σ_γ.toFun v2 = γ.ambient 0 = γ.src = γ.reverse.tgt
    show γ.ambient ((Smooth2Simplex.v2 : Fin 2 → ℝ) 0) = γ.src
    show γ.ambient 0 = γ.src
    have h := γ.ambient_eq_on_unitInterval
      (⟨0, by constructor <;> norm_num⟩ : unitInterval)
    have hval : ((⟨0, by constructor <;> norm_num⟩ : unitInterval).val : ℝ) = 0 :=
      rfl
    rw [hval] at h
    rw [h]
    exact γ.toPath.source'
  · -- toPath pointwise: face0(σ_γ)(t) = γ.ambient(1 - t.val) = γ.reverse.toPath(t).
    intro t
    show γ.ambient ((Smooth2Simplex.face0Param t.val) 0) = γ.reverse.toPath t
    -- (face0Param t.val) 0 = 1 - t.val.
    have h_param : (Smooth2Simplex.face0Param t.val) 0 = 1 - t.val := rfl
    rw [h_param]
    -- γ.reverse.toPath t = γ.toPath.symm t = γ.toPath ⟨1 - t.val, _⟩.
    show γ.ambient (1 - t.val) = (γ.reverse : SmoothPath I X).toPath t
    -- Unfold reverse.toPath = γ.toPath.symm = γ.toPath ∘ unitInterval.symm.
    have h_symm_val : (unitInterval.symm t).val = 1 - t.val := rfl
    have h_amb_eq := γ.ambient_eq_on_unitInterval (unitInterval.symm t)
    rw [h_symm_val] at h_amb_eq
    rw [h_amb_eq]
    rfl

/-- **face1 of σ_γ equals SmoothPath.const I X γ.src.** Both have
constant toPath at `γ.src` since `(face1Param t) 0 = 0`. -/
lemma face1_ofSmoothPathFstProj_eq_const_src :
    Smooth2Simplex.face1 (Smooth2Simplex.ofSmoothPathFstProj γ)
      = SmoothPath.const I X γ.src := by
  apply SmoothPath.ext
  · -- face1.src = σ_γ(v0) = γ.ambient(0) = γ.src.
    show γ.ambient ((Smooth2Simplex.v0 : Fin 2 → ℝ) 0) = γ.src
    show γ.ambient 0 = γ.src
    have h := γ.ambient_eq_on_unitInterval
      (⟨0, by constructor <;> norm_num⟩ : unitInterval)
    have hval : ((⟨0, by constructor <;> norm_num⟩ : unitInterval).val : ℝ) = 0 :=
      rfl
    rw [hval] at h
    rw [h]
    exact γ.toPath.source'
  · -- face1.tgt = σ_γ(v2) = γ.ambient(0) = γ.src.
    show γ.ambient ((Smooth2Simplex.v2 : Fin 2 → ℝ) 0) = γ.src
    show γ.ambient 0 = γ.src
    have h := γ.ambient_eq_on_unitInterval
      (⟨0, by constructor <;> norm_num⟩ : unitInterval)
    have hval : ((⟨0, by constructor <;> norm_num⟩ : unitInterval).val : ℝ) = 0 :=
      rfl
    rw [hval] at h
    rw [h]
    exact γ.toPath.source'
  · -- toPath: face1(σ_γ)(t) = γ.ambient(0) = γ.src; const.toPath(t) = γ.src.
    intro t
    show γ.ambient ((Smooth2Simplex.face1Param t.val) 0) = _
    have h_param : (Smooth2Simplex.face1Param t.val) 0 = 0 := rfl
    rw [h_param]
    show γ.ambient 0 = (SmoothPath.const I X γ.src).toPath t
    have h := γ.ambient_eq_on_unitInterval
      (⟨0, by constructor <;> norm_num⟩ : unitInterval)
    have hval : ((⟨0, by constructor <;> norm_num⟩ : unitInterval).val : ℝ) = 0 :=
      rfl
    rw [hval] at h
    rw [h]
    -- γ.toPath ⟨0, _⟩ = γ.src by Path.source'; const path at γ.src equals γ.src.
    have h_src : γ.toPath ⟨0, Set.left_mem_Icc.mpr (by norm_num : (0:ℝ) ≤ 1)⟩
        = γ.src := γ.toPath.source'
    rw [h_src]
    rfl

/-- **face2 of σ_γ equals γ.** Both have underlying toPath
`t ↦ γ.ambient t.val`, which is exactly `γ.toPath t` by the
smoothness witness's `ambient_eq_on_unitInterval`. -/
lemma face2_ofSmoothPathFstProj_eq :
    Smooth2Simplex.face2 (Smooth2Simplex.ofSmoothPathFstProj γ) = γ := by
  apply SmoothPath.ext
  · -- face2.src = σ_γ(v0) = γ.ambient(0) = γ.src.
    show γ.ambient ((Smooth2Simplex.v0 : Fin 2 → ℝ) 0) = γ.src
    show γ.ambient 0 = γ.src
    have h := γ.ambient_eq_on_unitInterval
      (⟨0, by constructor <;> norm_num⟩ : unitInterval)
    have hval : ((⟨0, by constructor <;> norm_num⟩ : unitInterval).val : ℝ) = 0 :=
      rfl
    rw [hval] at h
    rw [h]
    exact γ.toPath.source'
  · -- face2.tgt = σ_γ(v1) = γ.ambient(1) = γ.tgt.
    show γ.ambient ((Smooth2Simplex.v1 : Fin 2 → ℝ) 0) = γ.tgt
    show γ.ambient 1 = γ.tgt
    have h := γ.ambient_eq_on_unitInterval
      (⟨1, by constructor <;> norm_num⟩ : unitInterval)
    have hval : ((⟨1, by constructor <;> norm_num⟩ : unitInterval).val : ℝ) = 1 :=
      rfl
    rw [hval] at h
    rw [h]
    exact γ.toPath.target'
  · -- toPath: face2(σ_γ)(t) = γ.ambient(t.val) = γ.toPath(t) (via witness).
    intro t
    show γ.ambient ((Smooth2Simplex.face2Param t.val) 0) = γ.toPath t
    have h_param : (Smooth2Simplex.face2Param t.val) 0 = t.val := rfl
    rw [h_param]
    have h := γ.ambient_eq_on_unitInterval t
    exact h

/-! ## Boundary identity -/

/-- **Boundary identity from the path-induced 2-simplex.** -/
theorem boundary_ofSmoothPathFstProj_eq :
    Smooth2Simplex.boundary (Smooth2Simplex.ofSmoothPathFstProj γ)
      = SmoothChain.single γ.reverse
        - SmoothChain.single (SmoothPath.const I X γ.src)
        + SmoothChain.single γ := by
  unfold Smooth2Simplex.boundary
  rw [face0_ofSmoothPathFstProj_eq_reverse,
      face1_ofSmoothPathFstProj_eq_const_src,
      face2_ofSmoothPathFstProj_eq]

/-! ## The forward-plus-reverse identity -/

/-- **The chain `single γ.reverse - single (const γ.src) + single γ`
is a smooth 1-cycle.** Direct from `d² = 0`. -/
lemma single_reverse_minus_const_plus_single_mem_smoothCycle :
    SmoothChain.single γ.reverse
      - SmoothChain.single (SmoothPath.const I X γ.src)
      + SmoothChain.single γ
      ∈ JacobianChallenge.SmoothCycle I X := by
  rw [← boundary_ofSmoothPathFstProj_eq]
  rw [SmoothCycle.mem_iff]
  -- d² = 0 on `boundary₂ (single σ)`.
  have h_eq :
      Smooth2Chain.boundary₂
        (Smooth2Chain.single (Smooth2Simplex.ofSmoothPathFstProj γ))
      = Smooth2Simplex.boundary (Smooth2Simplex.ofSmoothPathFstProj γ) :=
    Smooth2Chain.boundary₂_single _
  rw [← h_eq]
  exact Smooth2Chain.boundary_boundary₂ _

/-- **The packaged SmoothCycle.** -/
noncomputable def single_reverse_minus_const_plus_single_smoothCycle :
    SmoothCycle I X :=
  ⟨SmoothChain.single γ.reverse
    - SmoothChain.single (SmoothPath.const I X γ.src)
    + SmoothChain.single γ,
    single_reverse_minus_const_plus_single_mem_smoothCycle γ⟩

/-- **The boundary-of-σ-γ SmoothCycle lies in stokesBoundaries.** -/
theorem single_reverse_minus_const_plus_single_smoothCycle_mem_stokesBoundaries :
    single_reverse_minus_const_plus_single_smoothCycle γ
      ∈ stokesBoundaries I X := by
  refine (mem_stokesBoundaries_iff (I := I) (X := X)).mpr ?_
  refine ⟨Smooth2Chain.single (Smooth2Simplex.ofSmoothPathFstProj γ), ?_⟩
  apply Subtype.ext
  show (Smooth2Chain.boundary₂Cycle
          (Smooth2Chain.single (Smooth2Simplex.ofSmoothPathFstProj γ)) :
        SmoothChain I X)
      = SmoothChain.single γ.reverse
        - SmoothChain.single (SmoothPath.const I X γ.src)
        + SmoothChain.single γ
  rw [Smooth2Chain.boundary₂Cycle_coe, Smooth2Chain.boundary₂_single]
  exact boundary_ofSmoothPathFstProj_eq γ

end JacobianChallenge

end
