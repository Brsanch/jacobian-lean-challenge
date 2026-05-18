/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2ChainStokesBoundary
import JacobianChallenge.Manifold.SmoothChainPush
import JacobianChallenge.Manifold.SmoothPathExt

set_option linter.unusedSectionVars false

/-! # Pushforward of smooth 2-simplices and 2-chains

For a smooth map `f : X → Y`, the smooth 2-simplex pushforward is
`(Smooth2Simplex.push f hf σ).toFun := f ∘ σ.toFun`, with smoothness
inherited via composition. The `ℤ`-linear extension is
`Smooth2Chain.push f hf`.

**Key compatibility.** Pushforward commutes with boundary:

* `SmoothChain.push f hf` of `Smooth2Simplex.boundary σ` equals
  `Smooth2Simplex.boundary (Smooth2Simplex.push f hf σ)`.
* `SmoothChain.push f hf` of `boundary₂ d` equals
  `boundary₂ (Smooth2Chain.push f hf d)`.

Hence the pushforward sends `stokesBoundaries I X` into
`stokesBoundaries I Y`.

## What this file ships

* `Smooth2Simplex.push f hf σ : Smooth2Simplex I Y`.
* `Smooth2Chain.push f hf : Smooth2Chain I X →ₗ[ℤ] Smooth2Chain I Y`.
* `boundary₂_push` — the commutativity at the 2-chain level.
* `SmoothPath.push_face0/face1/face2` — face pushforward identities.
* `stokesBoundaries_push` — pushforward sends `stokesBoundaries I X`
  to `stokesBoundaries I Y`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ⊤ Y]

/-! ## 2-simplex pushforward -/

/-- **Pushforward of a smooth 2-simplex along a smooth map.** -/
noncomputable def Smooth2Simplex.push
    (f : X → Y) (hf : ContMDiff I I ∞ f) (σ : Smooth2Simplex I X) :
    Smooth2Simplex I Y where
  toFun := f ∘ σ.toFun
  smooth := hf.comp σ.smooth

@[simp] lemma Smooth2Simplex.push_toFun
    (f : X → Y) (hf : ContMDiff I I ∞ f) (σ : Smooth2Simplex I X)
    (x : Fin 2 → ℝ) :
    (Smooth2Simplex.push f hf σ).toFun x = f (σ.toFun x) := rfl

/-! ## Face pushforward identities -/

/-- The face0 of the pushed simplex is the SmoothPath.push of the
original face0. -/
lemma Smooth2Simplex.face0_push
    (f : X → Y) (hf : ContMDiff I I ∞ f) (σ : Smooth2Simplex I X) :
    Smooth2Simplex.face0 (Smooth2Simplex.push f hf σ)
      = SmoothPath.push f hf (Smooth2Simplex.face0 σ) := by
  apply SmoothPath.ext
  · rfl
  · rfl
  · intro t
    rfl

/-- The face1 of the pushed simplex is the SmoothPath.push of the
original face1. -/
lemma Smooth2Simplex.face1_push
    (f : X → Y) (hf : ContMDiff I I ∞ f) (σ : Smooth2Simplex I X) :
    Smooth2Simplex.face1 (Smooth2Simplex.push f hf σ)
      = SmoothPath.push f hf (Smooth2Simplex.face1 σ) := by
  apply SmoothPath.ext
  · rfl
  · rfl
  · intro t
    rfl

/-- The face2 of the pushed simplex is the SmoothPath.push of the
original face2. -/
lemma Smooth2Simplex.face2_push
    (f : X → Y) (hf : ContMDiff I I ∞ f) (σ : Smooth2Simplex I X) :
    Smooth2Simplex.face2 (Smooth2Simplex.push f hf σ)
      = SmoothPath.push f hf (Smooth2Simplex.face2 σ) := by
  apply SmoothPath.ext
  · rfl
  · rfl
  · intro t
    rfl

/-- **Boundary of a pushed simplex equals the pushed boundary chain.** -/
theorem Smooth2Simplex.boundary_push
    (f : X → Y) (hf : ContMDiff I I ∞ f) (σ : Smooth2Simplex I X) :
    Smooth2Simplex.boundary (Smooth2Simplex.push f hf σ)
      = SmoothChain.push f hf (Smooth2Simplex.boundary σ) := by
  unfold Smooth2Simplex.boundary
  rw [Smooth2Simplex.face0_push, Smooth2Simplex.face1_push, Smooth2Simplex.face2_push]
  rw [map_add, map_sub]
  rw [SmoothChain.push_single, SmoothChain.push_single, SmoothChain.push_single]

/-! ## 2-chain pushforward -/

/-- **Pushforward of `Smooth2Chain` along a smooth map.** -/
noncomputable def Smooth2Chain.push
    (f : X → Y) (hf : ContMDiff I I ∞ f) :
    Smooth2Chain I X →ₗ[ℤ] Smooth2Chain I Y :=
  Finsupp.lmapDomain ℤ ℤ (Smooth2Simplex.push f hf)

@[simp] theorem Smooth2Chain.push_single
    (f : X → Y) (hf : ContMDiff I I ∞ f) (σ : Smooth2Simplex I X) :
    Smooth2Chain.push f hf (Smooth2Chain.single σ)
      = Smooth2Chain.single (Smooth2Simplex.push f hf σ) := by
  show Finsupp.lmapDomain ℤ ℤ (Smooth2Simplex.push f hf) (Finsupp.single σ 1) = _
  rw [Finsupp.lmapDomain_apply]
  simp [Smooth2Chain.single, Finsupp.mapDomain_single]

/-- **`boundary₂` commutes with pushforward.** -/
theorem Smooth2Chain.boundary₂_push
    (f : X → Y) (hf : ContMDiff I I ∞ f) (d : Smooth2Chain I X) :
    Smooth2Chain.boundary₂ (Smooth2Chain.push f hf d)
      = SmoothChain.push f hf (Smooth2Chain.boundary₂ d) := by
  -- Both sides are ℤ-linear in d. Verify on generators.
  have h_lhs_lhom : Smooth2Chain.boundary₂.comp (Smooth2Chain.push f hf)
      = (SmoothChain.push f hf : SmoothChain I X →ₗ[ℤ] _).comp
          Smooth2Chain.boundary₂ := by
    apply Finsupp.lhom_ext
    intro σ n
    show Smooth2Chain.boundary₂ (Smooth2Chain.push f hf (Finsupp.single σ n))
      = SmoothChain.push f hf (Smooth2Chain.boundary₂ (Finsupp.single σ n))
    -- Unfold push on `Finsupp.single σ n`:
    have h_push : Smooth2Chain.push f hf (Finsupp.single σ n)
        = Finsupp.single (Smooth2Simplex.push f hf σ) n := by
      show Finsupp.lmapDomain ℤ ℤ (Smooth2Simplex.push f hf)
            (Finsupp.single σ n) = _
      rw [Finsupp.lmapDomain_apply]
      simp [Finsupp.mapDomain_single]
    rw [h_push]
    -- Unfold boundary₂ on Finsupp.single σ n: n • boundary σ.
    have h_b1 :
        Smooth2Chain.boundary₂ (Finsupp.single (Smooth2Simplex.push f hf σ) n)
          = n • Smooth2Simplex.boundary (Smooth2Simplex.push f hf σ) := by
      show Finsupp.linearCombination ℤ Smooth2Simplex.boundary
            (Finsupp.single (Smooth2Simplex.push f hf σ) n) = _
      rw [Finsupp.linearCombination_single]
      rfl
    have h_b2 :
        Smooth2Chain.boundary₂ (Finsupp.single σ n)
          = n • Smooth2Simplex.boundary σ := by
      show Finsupp.linearCombination ℤ Smooth2Simplex.boundary
            (Finsupp.single σ n) = _
      rw [Finsupp.linearCombination_single]
      rfl
    rw [h_b1, h_b2]
    rw [show (SmoothChain.push f hf) (n • Smooth2Simplex.boundary σ)
            = n • (SmoothChain.push f hf) (Smooth2Simplex.boundary σ)
          from (SmoothChain.push f hf).map_smul n _]
    congr 1
    exact Smooth2Simplex.boundary_push f hf σ
  exact congrArg (fun L : Smooth2Chain I X →ₗ[ℤ] SmoothChain I Y => L d) h_lhs_lhom

/-! ## boundary₂Cycle commutes with pushforward -/

/-- Pushforward commutes with `Smooth2Chain.boundary₂Cycle`. -/
theorem Smooth2Chain.boundary₂Cycle_push
    (f : X → Y) (hf : ContMDiff I I ∞ f) (d : Smooth2Chain I X) :
    Smooth2Chain.boundary₂Cycle (Smooth2Chain.push f hf d)
      = SmoothCycle.pushHom f hf (Smooth2Chain.boundary₂Cycle d) := by
  apply Subtype.ext
  show ((Smooth2Chain.boundary₂Cycle (Smooth2Chain.push f hf d)
          : SmoothCycle I Y) : SmoothChain I Y)
      = ((SmoothCycle.pushHom f hf (Smooth2Chain.boundary₂Cycle d)
          : SmoothCycle I Y) : SmoothChain I Y)
  rw [Smooth2Chain.boundary₂Cycle_coe]
  show Smooth2Chain.boundary₂ (Smooth2Chain.push f hf d)
      = SmoothChain.push f hf
          (Smooth2Chain.boundary₂Cycle d : SmoothChain I X)
  rw [Smooth2Chain.boundary₂Cycle_coe]
  exact Smooth2Chain.boundary₂_push f hf d

/-! ## stokesBoundaries pushforward -/

/-- **Pushforward sends `stokesBoundaries I X` to `stokesBoundaries I Y`.**

For `f : X → Y` smooth and `c ∈ stokesBoundaries I X`, the pushed cycle
`SmoothCycle.pushHom f hf c ∈ stokesBoundaries I Y`. Witness: push the
2-chain witness of `c` and apply `boundary₂Cycle_push`. -/
theorem stokesBoundaries_push
    (f : X → Y) (hf : ContMDiff I I ∞ f)
    (c : SmoothCycle I X) (hc : c ∈ stokesBoundaries I X) :
    SmoothCycle.pushHom f hf c ∈ stokesBoundaries I Y := by
  obtain ⟨d, hd⟩ := (mem_stokesBoundaries_iff (I := I) (X := X)).mp hc
  refine (mem_stokesBoundaries_iff (I := I) (X := Y)).mpr ?_
  refine ⟨Smooth2Chain.push f hf d, ?_⟩
  rw [Smooth2Chain.boundary₂Cycle_push, hd]

end JacobianChallenge

end
