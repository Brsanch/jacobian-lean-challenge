/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexConst
import JacobianChallenge.Manifold.SmoothPathConcat
import JacobianChallenge.Manifold.SmoothPathExt

set_option linter.unusedSectionVars false

/-! # Smooth 2-simplex from the concatenation of two smooth paths

Given two smooth paths `γ, δ : SmoothPath I X` with `γ.tgt = δ.src`,
the smooth 2-simplex

```
σ_{γ,δ}(x₀, x₁) := γ.concatAmbient δ (x₀ / 2 + x₁)
```

has the three boundary 1-faces:

* `face0 σ`: a smooth path from `γ.tgt = δ.src` to `δ.tgt`,
  parameterised by `t ↦ γ.concatAmbient δ ((1 + t) / 2)`. This is
  a *reparameterisation* of `δ` (via `concatRepRight ∘ ((1 + ·) / 2)`)
  because `γ.concatAmbient δ` is `δ.ambient ∘ concatRepRight` on
  `[1/2, 1]`.
* `face1 σ = γ.concat δ`: the concatenation itself. **This is the
  load-bearing identity** — `face1` is *literally equal* (via
  `SmoothPath.ext`) to `γ.concat δ h`, because both have the same
  src/tgt and the same underlying `toPath.toFun` (both are
  `t ↦ γ.concatAmbient δ t.val`).
* `face2 σ`: a smooth path from `γ.src` to `γ.tgt`, parameterised by
  `t ↦ γ.concatAmbient δ (t / 2)`. This is a reparameterisation of
  `γ` (via `concatRepLeft ∘ (· / 2)`).

So the boundary chain identity is:

```
boundary σ = single (face0 σ) - single (γ.concat δ h) + single (face2 σ)
           ∈ stokesBoundaries I X.
```

Geometrically: `γ.concat δ` is homologous (mod stokes-boundaries) to
the formal sum `face2 σ + face0 σ` of bump-half reparameterisations of
`γ` and `δ`. Combined with future reparameterisation-invariance chips
(to be added separately), this gives the **concat-additive identity**
`single (γ.concat δ h) - single γ - single δ ∈ stokesBoundaries`, the
foundational building block toward `stokesBoundaries = ⊤` on a
simply-connected smooth manifold (genus-0 case).

## What this file ships

* `Smooth2Simplex.ofSmoothPathConcat γ δ h : Smooth2Simplex I X` — the
  smooth 2-simplex.
* `face1_ofSmoothPathConcat_eq` — `face1 σ = γ.concat δ h` as
  `SmoothPath` terms.
* `boundary_ofSmoothPathConcat_eq` — the boundary chain identity with
  `face1` replaced by `γ.concat δ h`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-! ## The concat 2-simplex -/

/-- **Smooth 2-simplex from the concatenation of two smooth paths.**

Defined by `σ(x₀, x₁) := γ.concatAmbient δ (x₀ / 2 + x₁)`, using
`SmoothPath.concatAmbient` (the bump-flattened piecewise smooth ambient
extension of `γ.concat δ`). Smoothness follows from the C^∞-ness of the
linear map `(x₀, x₁) ↦ x₀ / 2 + x₁` composed with the C^∞ ambient. -/
noncomputable def Smooth2Simplex.ofSmoothPathConcat
    (γ δ : SmoothPath I X) (h : γ.tgt = δ.src) :
    Smooth2Simplex I X where
  toFun := fun x : Fin 2 → ℝ => γ.concatAmbient δ (x 0 / 2 + x 1)
  smooth := by
    -- σ is the composition of the C^∞ ambient `γ.concatAmbient δ`
    -- with the ℝ-linear projection `(x₀, x₁) ↦ x₀ / 2 + x₁`.
    have h_proj :
        ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) ∞
          (fun x : Fin 2 → ℝ => x 0 / 2 + x 1) := by
      -- Express the projection as a continuous linear map and use
      -- `ContinuousLinearMap.contMDiff`.
      have h_clm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : Fin 2 → ℝ => x 0 / 2 + x 1) := by
        have h0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun x : Fin 2 → ℝ => x 0) :=
          (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff
        have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun x : Fin 2 → ℝ => x 1) :=
          (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ).contDiff
        have h0' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun x : Fin 2 → ℝ => x 0 / 2) := by
          have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
              (fun _ : Fin 2 → ℝ => (2 : ℝ)) := contDiff_const
          exact h0.div hc (fun _ => by norm_num)
        exact h0'.add h1
      exact h_clm.contMDiff
    exact (γ.contMDiff_concatAmbient δ h).comp h_proj

variable (γ δ : SmoothPath I X) (h : γ.tgt = δ.src)

@[simp] lemma Smooth2Simplex.ofSmoothPathConcat_toFun
    (x : Fin 2 → ℝ) :
    (Smooth2Simplex.ofSmoothPathConcat γ δ h).toFun x
      = γ.concatAmbient δ (x 0 / 2 + x 1) := rfl

/-! ## Identification `face1 σ = γ.concat δ h` -/

/-- **face1 of the concat 2-simplex equals `γ.concat δ h`.**

Both smooth paths have:
* the same `src` field: `γ.src`,
* the same `tgt` field: `δ.tgt`,
* the same underlying `toPath.toFun`:
  `t : unitInterval ↦ γ.concatAmbient δ t.val`.

Proven via `SmoothPath.ext`. -/
lemma face1_ofSmoothPathConcat_eq :
    Smooth2Simplex.face1 (Smooth2Simplex.ofSmoothPathConcat γ δ h)
      = γ.concat δ h := by
  apply SmoothPath.ext
  · -- src: face1.src = σ.toFun v0 = concatAmbient(0/2 + 0) = γ.src.
    show γ.concatAmbient δ
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 0 / 2
          + (Smooth2Simplex.v0 : Fin 2 → ℝ) 1) = γ.src
    have h_v0_0 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v0_1 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h_v0_0, h_v0_1]
    show γ.concatAmbient δ (0 / 2 + 0) = γ.src
    have h_arg : (0 : ℝ) / 2 + 0 = 0 := by norm_num
    rw [h_arg]
    exact γ.concatAmbient_zero δ
  · -- tgt: face1.tgt = σ.toFun v2 = concatAmbient(0/2 + 1) = δ.tgt.
    show γ.concatAmbient δ
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 0 / 2
          + (Smooth2Simplex.v2 : Fin 2 → ℝ) 1) = δ.tgt
    have h_v2_0 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v2_1 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 1 = 1 := rfl
    rw [h_v2_0, h_v2_1]
    show γ.concatAmbient δ (0 / 2 + 1) = δ.tgt
    have h_arg : (0 : ℝ) / 2 + 1 = 1 := by norm_num
    rw [h_arg]
    exact γ.concatAmbient_one δ
  · -- toPath pointwise:
    --   face1(σ).toPath t = σ.toFun (face1Param t.val) = σ(0, t.val)
    --                    = concatAmbient (0/2 + t.val) = concatAmbient t.val.
    -- (γ.concat δ h).toPath t = γ.concatAmbient δ t.val (from concat's def).
    intro t
    show γ.concatAmbient δ
        ((Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 0 / 2
          + (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 1)
      = (γ.concat δ h).toPath t
    have h_p0 : (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 0 = 0 := rfl
    have h_p1 : (Smooth2Simplex.face1Param t.val : Fin 2 → ℝ) 1 = t.val := rfl
    rw [h_p0, h_p1]
    show γ.concatAmbient δ (0 / 2 + t.val) = (γ.concat δ h).toPath t
    have h_arg : (0 : ℝ) / 2 + t.val = t.val := by ring
    rw [h_arg]
    -- (γ.concat δ h).toPath t = γ.concatAmbient δ t.val by definition.
    rfl

/-! ## Boundary identity with `face1` replaced -/

/-- **Boundary identity from the concat 2-simplex, with face1
identified.** The boundary chain is
`single (face0 σ) - single (γ.concat δ h) + single (face2 σ)`. -/
theorem boundary_ofSmoothPathConcat_eq :
    Smooth2Simplex.boundary (Smooth2Simplex.ofSmoothPathConcat γ δ h)
      = SmoothChain.single
          (Smooth2Simplex.face0 (Smooth2Simplex.ofSmoothPathConcat γ δ h))
        - SmoothChain.single (γ.concat δ h)
        + SmoothChain.single
            (Smooth2Simplex.face2 (Smooth2Simplex.ofSmoothPathConcat γ δ h)) := by
  unfold Smooth2Simplex.boundary
  rw [face1_ofSmoothPathConcat_eq]

/-! ## Stokes-boundary membership -/

/-- **The boundary chain `face0 - (γ.concat δ) + face2` lies in
`stokesBoundaries`.** Direct from `d² = 0` and the chain identity. -/
lemma boundary_chain_ofSmoothPathConcat_mem_smoothCycle :
    SmoothChain.single
        (Smooth2Simplex.face0 (Smooth2Simplex.ofSmoothPathConcat γ δ h))
      - SmoothChain.single (γ.concat δ h)
      + SmoothChain.single
          (Smooth2Simplex.face2 (Smooth2Simplex.ofSmoothPathConcat γ δ h))
      ∈ JacobianChallenge.SmoothCycle I X := by
  rw [← boundary_ofSmoothPathConcat_eq]
  rw [SmoothCycle.mem_iff]
  -- d² = 0 on `boundary₂ (single σ)`.
  have h_eq :
      Smooth2Chain.boundary₂
        (Smooth2Chain.single (Smooth2Simplex.ofSmoothPathConcat γ δ h))
      = Smooth2Simplex.boundary (Smooth2Simplex.ofSmoothPathConcat γ δ h) :=
    Smooth2Chain.boundary₂_single _
  rw [← h_eq]
  exact Smooth2Chain.boundary_boundary₂ _

/-- **Packaged SmoothCycle.** -/
noncomputable def boundary_chain_ofSmoothPathConcat_smoothCycle :
    SmoothCycle I X :=
  ⟨SmoothChain.single
      (Smooth2Simplex.face0 (Smooth2Simplex.ofSmoothPathConcat γ δ h))
    - SmoothChain.single (γ.concat δ h)
    + SmoothChain.single
        (Smooth2Simplex.face2 (Smooth2Simplex.ofSmoothPathConcat γ δ h)),
    boundary_chain_ofSmoothPathConcat_mem_smoothCycle γ δ h⟩

/-- **The concat-2-simplex boundary cycle lies in `stokesBoundaries`.**
Witness: `Smooth2Chain.single (ofSmoothPathConcat γ δ h)`. -/
theorem boundary_chain_ofSmoothPathConcat_smoothCycle_mem_stokesBoundaries :
    boundary_chain_ofSmoothPathConcat_smoothCycle γ δ h
      ∈ stokesBoundaries I X := by
  refine (mem_stokesBoundaries_iff (I := I) (X := X)).mpr ?_
  refine ⟨Smooth2Chain.single (Smooth2Simplex.ofSmoothPathConcat γ δ h), ?_⟩
  apply Subtype.ext
  show (Smooth2Chain.boundary₂Cycle
          (Smooth2Chain.single (Smooth2Simplex.ofSmoothPathConcat γ δ h)) :
        SmoothChain I X)
      = SmoothChain.single
          (Smooth2Simplex.face0 (Smooth2Simplex.ofSmoothPathConcat γ δ h))
        - SmoothChain.single (γ.concat δ h)
        + SmoothChain.single
            (Smooth2Simplex.face2 (Smooth2Simplex.ofSmoothPathConcat γ δ h))
  rw [Smooth2Chain.boundary₂Cycle_coe, Smooth2Chain.boundary₂_single]
  exact boundary_ofSmoothPathConcat_eq γ δ h

end JacobianChallenge

end
