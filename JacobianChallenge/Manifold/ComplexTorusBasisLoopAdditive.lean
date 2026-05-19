/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusBasisLoop
import JacobianChallenge.Manifold.Smooth2Simplex
import JacobianChallenge.Manifold.Smooth2ChainStokesBoundary
import JacobianChallenge.Manifold.SmoothPathExt
import JacobianChallenge.Manifold.BasedSmoothLoopsBound

set_option linter.unusedSectionVars false

/-! # Homological additivity of torus basis loops

For two lattice elements `a, b ∈ L`, the smooth 2-simplex
`σ_{a,b}(u, v) := mkQ ((u+v) · a + v · b)` on `ℂ ⧸ L` has faces:

* `face0 σ` = `torusBasisLoop b` (since `mkQ(a + t·b) = mkQ(t·b)`),
* `face1 σ` = `torusBasisLoop (a+b)` (since `mkQ(t·a + t·b) = mkQ(t·(a+b))`),
* `face2 σ` = `torusBasisLoop a`.

The boundary chain identity `∂σ = face0 - face1 + face2` translates to

```
single (γ_b) - single (γ_{a+b}) + single (γ_a) ∈ image of boundary₂.
```

Hence as cycles:

```
single γ_{a+b} - single γ_a - single γ_b ∈ stokesBoundaries.
```

This realises **homological additivity** of the torus basis loop
construction on `H₁(ℂ ⧸ L; ℤ)`.

## What this file ships

* `ComplexTorus.basisLoopAddSimplex L a b ha hb` — the 2-simplex.
* `ComplexTorus.basisLoopAdditive_stokesBoundaries` — the headline
  homology identity in `stokesBoundaries`.

No `sorry`, no `axiom`. -/

open Set
open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Smoothness primitives on `Fin 2 → ℝ` -/

private lemma contMDiff_proj_fin2_aux (i : Fin 2) :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞ (fun x : Fin 2 → ℝ => x i) := by
  have h_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Fin 2 → ℝ => x i) :=
    (ContinuousLinearMap.proj i : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff
  exact h_cd.contMDiff

/-! ## Smoothness of the inner map `(u, v) ↦ (u+v)·a + v·b` -/

private lemma contMDiff_basisLoopAdd_inner (a b : ℂ) :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => (x 0 + x 1) • a + (x 1) • b) := by
  have h0 : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun x : Fin 2 → ℝ => x 0) := contMDiff_proj_fin2_aux 0
  have h1 : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun x : Fin 2 → ℝ => x 1) := contMDiff_proj_fin2_aux 1
  have hsum : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun x : Fin 2 → ℝ => x 0 + x 1) := h0.add h1
  have h_lhs : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => (x 0 + x 1) • a) := hsum.smul contMDiff_const
  have h_rhs : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞
      (fun x : Fin 2 → ℝ => (x 1) • b) := h1.smul contMDiff_const
  exact h_lhs.add h_rhs

/-! ## The 2-simplex -/

/-- **`σ_{a, b}` 2-simplex** on `ℂ ⧸ L`: `(u, v) ↦ mkQ((u+v)·a + v·b)`. -/
noncomputable def basisLoopAddSimplex (a b : ℂ) :
    Smooth2Simplex 𝓘(ℝ, ℂ) (ℂ ⧸ L) where
  toFun := fun x : Fin 2 → ℝ => L.mkQ ((x 0 + x 1) • a + (x 1) • b)
  smooth := (mkQ_contMDiff_real L ∞).comp (contMDiff_basisLoopAdd_inner a b)

/-! ## Face identifications

We use `SmoothPath.ext` (extensionality at src/tgt + pointwise toPath).
-/

variable {L}

/-- **`face0 σ_{a,b} = torusBasisLoop b`** (since `mkQ(a + t·b) = mkQ(t·b)`
when `a ∈ L`). -/
theorem face0_basisLoopAddSimplex_eq_torusBasisLoop_right
    (a b : ℂ) (ha : a ∈ L) (hb : b ∈ L) :
    Smooth2Simplex.face0 (basisLoopAddSimplex L a b)
      = torusBasisLoop b hb := by
  apply SmoothPath.ext
  · -- src: σ(v1) = mkQ((1+0)·a + 0·b) = mkQ(a) = 0.
    show (basisLoopAddSimplex L a b).toFun Smooth2Simplex.v1
      = (torusBasisLoop b hb).src
    show L.mkQ (((Smooth2Simplex.v1 : Fin 2 → ℝ) 0
        + (Smooth2Simplex.v1 : Fin 2 → ℝ) 1) • a
        + ((Smooth2Simplex.v1 : Fin 2 → ℝ) 1) • b) = (0 : ℂ ⧸ L)
    have h0 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 = 1 := rfl
    have h1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h0, h1]
    have h_eq : ((1 : ℝ) + 0) • a + (0 : ℝ) • b = a := by
      simp
    rw [h_eq]
    exact (Submodule.Quotient.mk_eq_zero L).mpr ha
  · -- tgt: σ(v2) = mkQ((0+1)·a + 1·b) = mkQ(a+b) = 0.
    show (basisLoopAddSimplex L a b).toFun Smooth2Simplex.v2
      = (torusBasisLoop b hb).tgt
    show L.mkQ (((Smooth2Simplex.v2 : Fin 2 → ℝ) 0
        + (Smooth2Simplex.v2 : Fin 2 → ℝ) 1) • a
        + ((Smooth2Simplex.v2 : Fin 2 → ℝ) 1) • b) = (0 : ℂ ⧸ L)
    have h0 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 = 0 := rfl
    have h1 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 1 = 1 := rfl
    rw [h0, h1]
    have h_eq : ((0 : ℝ) + 1) • a + (1 : ℝ) • b = a + b := by module
    rw [h_eq]
    exact (Submodule.Quotient.mk_eq_zero L).mpr (L.add_mem ha hb)
  · intro t
    -- σ.toFun ![1-t.val, t.val] = mkQ((1-t.val + t.val) • a + t.val • b)
    --                            = mkQ(a + t.val • b)
    --                            = mkQ(a) + mkQ(t.val • b) (mkQ is additive)
    --                            = mkQ(t.val • b)
    --                            = mkQ((t.val : ℂ) * b)
    --                            = γ_b.toPath t.
    show (basisLoopAddSimplex L a b).toFun
        (Smooth2Simplex.face0Param t.val)
      = (torusBasisLoop b hb).toPath t
    show L.mkQ (((Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0
          + (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1) • a
        + ((Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1) • b)
      = L.mkQ (((t.val : ℝ) : ℂ) * b)
    have h0 : (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0 = 1 - t.val := rfl
    have h1 : (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1 = t.val := rfl
    rw [h0, h1]
    have h_eq : (((1 - t.val) + t.val : ℝ)) • a + (t.val : ℝ) • b
        = a + (t.val : ℝ) • b := by module
    rw [h_eq]
    rw [map_add]
    have h_a_zero : L.mkQ a = 0 := (Submodule.Quotient.mk_eq_zero L).mpr ha
    rw [h_a_zero, zero_add]
    congr 1

/-- **`face1 σ_{a,b} = torusBasisLoop (a+b)`** (since `mkQ(t·a + t·b)
= mkQ(t·(a+b))`). -/
theorem face1_basisLoopAddSimplex_eq_torusBasisLoop_sum
    (a b : ℂ) (ha : a ∈ L) (hb : b ∈ L) :
    Smooth2Simplex.face1 (basisLoopAddSimplex L a b)
      = torusBasisLoop (a + b) (L.add_mem ha hb) := by
  apply SmoothPath.ext
  · -- src: σ(v0) = mkQ((0+0)·a + 0·b) = mkQ(0) = 0.
    show (basisLoopAddSimplex L a b).toFun Smooth2Simplex.v0
      = (torusBasisLoop (a + b) _).src
    show L.mkQ (((Smooth2Simplex.v0 : Fin 2 → ℝ) 0
        + (Smooth2Simplex.v0 : Fin 2 → ℝ) 1) • a
        + ((Smooth2Simplex.v0 : Fin 2 → ℝ) 1) • b) = (0 : ℂ ⧸ L)
    have h0 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 0 = 0 := rfl
    have h1 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h0, h1]
    have h_eq : ((0 : ℝ) + 0) • a + (0 : ℝ) • b = (0 : ℂ) := by simp
    rw [h_eq]
    exact map_zero L.mkQ
  · -- tgt: σ(v2) = mkQ((0+1)·a + 1·b) = mkQ(a+b) = 0.
    show (basisLoopAddSimplex L a b).toFun Smooth2Simplex.v2
      = (torusBasisLoop (a + b) _).tgt
    show L.mkQ (((Smooth2Simplex.v2 : Fin 2 → ℝ) 0
        + (Smooth2Simplex.v2 : Fin 2 → ℝ) 1) • a
        + ((Smooth2Simplex.v2 : Fin 2 → ℝ) 1) • b) = (0 : ℂ ⧸ L)
    have h0 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 = 0 := rfl
    have h1 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 1 = 1 := rfl
    rw [h0, h1]
    have h_eq : ((0 : ℝ) + 1) • a + (1 : ℝ) • b = a + b := by module
    rw [h_eq]
    exact (Submodule.Quotient.mk_eq_zero L).mpr (L.add_mem ha hb)
  · intro t
    -- σ.toFun ![0, t.val] = mkQ((0+t.val) • a + t.val • b)
    --                     = mkQ(t.val • a + t.val • b)
    --                     = mkQ(t.val • (a + b))
    --                     = mkQ((t.val : ℂ) * (a+b))
    --                     = γ_{a+b}.toPath t.
    show (basisLoopAddSimplex L a b).toFun
        (Smooth2Simplex.face1Param t.val)
      = (torusBasisLoop (a + b) _).toPath t
    show L.mkQ (((Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 0
          + (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 1) • a
        + ((Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 1) • b)
      = L.mkQ (((t.val : ℝ) : ℂ) * (a + b))
    have h0 : (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 0 = 0 := rfl
    have h1 : (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 1 = t.val := rfl
    rw [h0, h1]
    have h_eq : (((0 : ℝ) + t.val) • a + (t.val : ℝ) • b
        = (t.val : ℝ) • (a + b)) := by module
    rw [h_eq]
    -- mkQ((t.val : ℝ) • (a + b)) = mkQ((t.val : ℂ) * (a + b)) via Complex.real_smul.
    congr 1

/-- **`face2 σ_{a,b} = torusBasisLoop a`**. -/
theorem face2_basisLoopAddSimplex_eq_torusBasisLoop_left
    (a b : ℂ) (ha : a ∈ L) (hb : b ∈ L) :
    Smooth2Simplex.face2 (basisLoopAddSimplex L a b)
      = torusBasisLoop a ha := by
  apply SmoothPath.ext
  · -- src: σ(v0) = mkQ(0) = 0.
    show (basisLoopAddSimplex L a b).toFun Smooth2Simplex.v0
      = (torusBasisLoop a ha).src
    show L.mkQ (((Smooth2Simplex.v0 : Fin 2 → ℝ) 0
        + (Smooth2Simplex.v0 : Fin 2 → ℝ) 1) • a
        + ((Smooth2Simplex.v0 : Fin 2 → ℝ) 1) • b) = (0 : ℂ ⧸ L)
    have h0 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 0 = 0 := rfl
    have h1 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h0, h1]
    have h_eq : ((0 : ℝ) + 0) • a + (0 : ℝ) • b = (0 : ℂ) := by simp
    rw [h_eq]
    exact map_zero L.mkQ
  · -- tgt: σ(v1) = mkQ(a) = 0.
    show (basisLoopAddSimplex L a b).toFun Smooth2Simplex.v1
      = (torusBasisLoop a ha).tgt
    show L.mkQ (((Smooth2Simplex.v1 : Fin 2 → ℝ) 0
        + (Smooth2Simplex.v1 : Fin 2 → ℝ) 1) • a
        + ((Smooth2Simplex.v1 : Fin 2 → ℝ) 1) • b) = (0 : ℂ ⧸ L)
    have h0 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 = 1 := rfl
    have h1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h0, h1]
    have h_eq : ((1 : ℝ) + 0) • a + (0 : ℝ) • b = a := by simp
    rw [h_eq]
    exact (Submodule.Quotient.mk_eq_zero L).mpr ha
  · intro t
    -- σ.toFun ![t.val, 0] = mkQ((t.val + 0) • a + 0 • b) = mkQ(t.val • a)
    show (basisLoopAddSimplex L a b).toFun
        (Smooth2Simplex.face2Param t.val)
      = (torusBasisLoop a ha).toPath t
    show L.mkQ (((Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 0
          + (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 1) • a
        + ((Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 1) • b)
      = L.mkQ (((t.val : ℝ) : ℂ) * a)
    have h0 : (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 0 = t.val := rfl
    have h1 : (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h0, h1]
    have h_eq : ((t.val : ℝ) + 0) • a + (0 : ℝ) • b = (t.val : ℝ) • a := by module
    rw [h_eq]
    congr 1

/-! ## Boundary identity in `SmoothChain` -/

/-- **Boundary chain identity for `basisLoopAddSimplex`**: -/
theorem boundary_basisLoopAddSimplex_eq
    (a b : ℂ) (ha : a ∈ L) (hb : b ∈ L) :
    Smooth2Simplex.boundary (basisLoopAddSimplex L a b)
      = SmoothChain.single (torusBasisLoop b hb)
        - SmoothChain.single (torusBasisLoop (a + b) (L.add_mem ha hb))
        + SmoothChain.single (torusBasisLoop a ha) := by
  unfold Smooth2Simplex.boundary
  rw [face0_basisLoopAddSimplex_eq_torusBasisLoop_right a b ha hb,
      face1_basisLoopAddSimplex_eq_torusBasisLoop_sum a b ha hb,
      face2_basisLoopAddSimplex_eq_torusBasisLoop_left a b ha hb]

/-! ## Stokes-boundary membership: homological additivity -/

/-- **Homological additivity** of the torus basis loop: for any
`a, b ∈ L`,

```
single (γ_{a+b}) - single (γ_a) - single (γ_b) ∈ stokesBoundaries.
```
-/
theorem basisLoopAdditive_stokesBoundaries
    (a b : ℂ) (ha : a ∈ L) (hb : b ∈ L) :
    single_smoothLoop_smoothCycle (torusBasisLoop (a + b) (L.add_mem ha hb))
        ((torusBasisLoop_src (a + b) (L.add_mem ha hb)).trans
          (torusBasisLoop_tgt (a + b) (L.add_mem ha hb)).symm)
      - single_smoothLoop_smoothCycle (torusBasisLoop a ha)
          ((torusBasisLoop_src a ha).trans (torusBasisLoop_tgt a ha).symm)
      - single_smoothLoop_smoothCycle (torusBasisLoop b hb)
          ((torusBasisLoop_src b hb).trans (torusBasisLoop_tgt b hb).symm)
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) (ℂ ⧸ L) := by
  -- Set the 2-chain c := single σ.
  set σ := basisLoopAddSimplex L a b with hσ_def
  set c : Smooth2Chain 𝓘(ℝ, ℂ) (ℂ ⧸ L) := Smooth2Chain.single σ with hc_def
  -- boundary₂Cycle c ∈ stokesBoundaries.
  have h_in : Smooth2Chain.boundary₂Cycle c ∈ stokesBoundaries 𝓘(ℝ, ℂ) (ℂ ⧸ L) :=
    (mem_stokesBoundaries_iff (I := 𝓘(ℝ, ℂ)) (X := ℂ ⧸ L)).mpr ⟨c, rfl⟩
  -- boundary₂Cycle c equals γ_b.cycle - γ_{a+b}.cycle + γ_a.cycle.
  set b_cycle := single_smoothLoop_smoothCycle (torusBasisLoop b hb)
      ((torusBasisLoop_src b hb).trans (torusBasisLoop_tgt b hb).symm)
    with hb_cycle_def
  set sum_cycle := single_smoothLoop_smoothCycle
      (torusBasisLoop (a + b) (L.add_mem ha hb))
      ((torusBasisLoop_src (a + b) (L.add_mem ha hb)).trans
        (torusBasisLoop_tgt (a + b) (L.add_mem ha hb)).symm)
    with hsum_cycle_def
  set a_cycle := single_smoothLoop_smoothCycle (torusBasisLoop a ha)
      ((torusBasisLoop_src a ha).trans (torusBasisLoop_tgt a ha).symm)
    with ha_cycle_def
  have h_eq_cycle :
      Smooth2Chain.boundary₂Cycle c = b_cycle - sum_cycle + a_cycle := by
    apply Subtype.ext
    rw [Smooth2Chain.boundary₂Cycle_coe]
    rw [hc_def, Smooth2Chain.boundary₂_single, boundary_basisLoopAddSimplex_eq a b ha hb]
    rw [SmoothCycle.coe_add, SmoothCycle.coe_sub,
        hb_cycle_def, hsum_cycle_def, ha_cycle_def,
        single_smoothLoop_smoothCycle_coe,
        single_smoothLoop_smoothCycle_coe,
        single_smoothLoop_smoothCycle_coe]
  rw [h_eq_cycle] at h_in
  -- h_in : b_cycle - sum_cycle + a_cycle ∈ stokesBoundaries.
  -- Negate: -(b_cycle - sum_cycle + a_cycle) = sum_cycle - a_cycle - b_cycle.
  have h_neg :
      -(b_cycle - sum_cycle + a_cycle) = sum_cycle - a_cycle - b_cycle := by
    abel
  rw [← h_neg]
  exact (stokesBoundaries 𝓘(ℝ, ℂ) (ℂ ⧸ L)).neg_mem h_in

end ComplexTorus

end JacobianChallenge

end
