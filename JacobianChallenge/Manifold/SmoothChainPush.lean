/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathPush
import JacobianChallenge.Manifold.SmoothCycle

set_option linter.unusedSectionVars false

/-! # Pushforward of `SmoothChain` / `SmoothCycle` along a smooth map

Extends `SmoothPath.push` ℤ-linearly to chains, and shows boundary
respects pushforward (so cycles map to cycles).

## Headlines

* `SmoothChain.push f hf : SmoothChain I X →ₗ[ℤ] SmoothChain I Y` —
  ℤ-linear extension of `SmoothPath.push`.

* `SmoothChain.push_single γ` — pushforward of a single-path chain.

* `SmoothChain.boundary_push c` — boundaries commute with pushforward:
  `boundary (push c) = push_pt (boundary c)`, where `push_pt` is the
  pointwise pushforward `(X →₀ ℤ) → (Y →₀ ℤ)` via `Finsupp.mapDomain f`.

* `SmoothCycle.push f hf c hc : push f hf c ∈ SmoothCycle I Y` — cycles
  are carried to cycles. Pulled out as an `AddSubgroup`-respecting
  `AddMonoidHom SmoothCycle I X → SmoothCycle I Y` in
  `SmoothCycle.pushHom`.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ⊤ Y]

/-- **Pushforward of `SmoothChain` along a smooth map.** ℤ-linear
extension of `SmoothPath.push`. -/
noncomputable def SmoothChain.push
    (f : X → Y) (hf : ContMDiff I I ∞ f) :
    SmoothChain I X →ₗ[ℤ] SmoothChain I Y :=
  Finsupp.lmapDomain ℤ ℤ (SmoothPath.push f hf)

@[simp] theorem SmoothChain.push_single
    (f : X → Y) (hf : ContMDiff I I ∞ f) (γ : SmoothPath I X) :
    SmoothChain.push f hf (SmoothChain.single γ) =
      SmoothChain.single (SmoothPath.push f hf γ) := by
  show Finsupp.lmapDomain ℤ ℤ (SmoothPath.push f hf) (Finsupp.single γ 1) = _
  rw [Finsupp.lmapDomain_apply]
  simp [SmoothChain.single, Finsupp.mapDomain_single]

/-! ### Boundary commutes with pushforward -/

/-- Pointwise pushforward of formal `ℤ`-sums of points. -/
noncomputable def pointPush (f : X → Y) : (X →₀ ℤ) →ₗ[ℤ] (Y →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ f

@[simp] theorem pointPush_single (f : X → Y) (x : X) (n : ℤ) :
    pointPush f (Finsupp.single x n) = Finsupp.single (f x) n := by
  show Finsupp.lmapDomain ℤ ℤ f (Finsupp.single x n) = _
  rw [Finsupp.lmapDomain_apply]
  simp [Finsupp.mapDomain_single]

/-- Auxiliary: `boundary_push` at a single generator `single γ n`. -/
private theorem SmoothChain.boundary_push_single
    (f : X → Y) (hf : ContMDiff I I ∞ f) (γ : SmoothPath I X) (n : ℤ) :
    SmoothChain.boundary (SmoothChain.push f hf (Finsupp.single γ n))
      = pointPush f (SmoothChain.boundary (Finsupp.single γ n)) := by
  -- LHS: push (single γ n) = single (push γ) n; then boundary on this.
  have h_push :
      SmoothChain.push f hf (Finsupp.single γ n)
        = Finsupp.single (SmoothPath.push f hf γ) n := by
    show Finsupp.lmapDomain ℤ ℤ (SmoothPath.push f hf) (Finsupp.single γ n) = _
    rw [Finsupp.lmapDomain_apply]
    simp [Finsupp.mapDomain_single]
  rw [h_push]
  have h_b1 :
      SmoothChain.boundary (Finsupp.single (SmoothPath.push f hf γ) n)
        = n • SmoothChain.boundarySingle (SmoothPath.push f hf γ) := by
    show Finsupp.linearCombination ℤ SmoothChain.boundarySingle
        (Finsupp.single (SmoothPath.push f hf γ) n) = _
    rw [Finsupp.linearCombination_single]
  have h_b2 :
      SmoothChain.boundary (Finsupp.single γ n)
        = n • SmoothChain.boundarySingle γ := by
    show Finsupp.linearCombination ℤ SmoothChain.boundarySingle (Finsupp.single γ n) = _
    rw [Finsupp.linearCombination_single]
  rw [h_b1, h_b2, LinearMap.map_smul]
  congr 1
  show Finsupp.single (f γ.tgt) (1 : ℤ) - Finsupp.single (f γ.src) (1 : ℤ)
    = pointPush f (Finsupp.single γ.tgt (1 : ℤ) - Finsupp.single γ.src (1 : ℤ))
  rw [map_sub, pointPush_single, pointPush_single]

theorem SmoothChain.boundary_push
    (f : X → Y) (hf : ContMDiff I I ∞ f) (c : SmoothChain I X) :
    SmoothChain.boundary (SmoothChain.push f hf c)
      = pointPush f (SmoothChain.boundary c) := by
  -- Both sides are ℤ-linear maps in `c`. Set up an extensionality argument.
  have h_eq :
      SmoothChain.boundary.comp (SmoothChain.push f hf)
        = (pointPush f).comp SmoothChain.boundary := by
    apply Finsupp.lhom_ext
    intro γ n
    -- Goal at the generator `Finsupp.single γ n`: same as boundary_push_single.
    show SmoothChain.boundary (SmoothChain.push f hf (Finsupp.single γ n))
      = pointPush f (SmoothChain.boundary (Finsupp.single γ n))
    exact SmoothChain.boundary_push_single f hf γ n
  -- Apply the equality of LinearMaps to `c`.
  exact congrArg (fun L : SmoothChain I X →ₗ[ℤ] (Y →₀ ℤ) => L c) h_eq

/-! ### `SmoothCycle.push` -/

/-- A cycle has zero boundary, so its pushforward also has zero boundary
(by `boundary_push`), hence is a cycle. -/
theorem SmoothCycle.push_mem
    (f : X → Y) (hf : ContMDiff I I ∞ f) (c : SmoothChain I X)
    (hc : c ∈ SmoothCycle I X) :
    SmoothChain.push f hf c ∈ SmoothCycle I Y := by
  rw [SmoothCycle.mem_iff] at hc ⊢
  rw [SmoothChain.boundary_push, hc, map_zero]

/-- **Pushforward of cycles** as an `AddMonoidHom`. -/
noncomputable def SmoothCycle.pushHom
    (f : X → Y) (hf : ContMDiff I I ∞ f) :
    SmoothCycle I X →+ SmoothCycle I Y where
  toFun c := ⟨SmoothChain.push f hf (c : SmoothChain I X),
              SmoothCycle.push_mem f hf _ c.2⟩
  map_zero' := by
    apply Subtype.ext
    show SmoothChain.push f hf 0 = (0 : SmoothChain I Y)
    simp [map_zero]
  map_add' c₁ c₂ := by
    apply Subtype.ext
    show SmoothChain.push f hf ((c₁ + c₂ : SmoothCycle I X) : SmoothChain I X)
      = SmoothChain.push f hf (c₁ : SmoothChain I X)
        + SmoothChain.push f hf (c₂ : SmoothChain I X)
    rw [show ((c₁ + c₂ : SmoothCycle I X) : SmoothChain I X)
          = (c₁ : SmoothChain I X) + (c₂ : SmoothChain I X) from rfl]
    exact map_add _ _ _

end JacobianChallenge

end
