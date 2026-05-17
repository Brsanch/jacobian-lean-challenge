/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothChainPush

set_option linter.unusedSectionVars false

/-! # Identity functoriality of `SmoothPath`/`Chain`/`Cycle` pushforward

Sister to `SmoothCyclePushComp` on the composition side. For the
identity map `id : X → X`:

* `SmoothPath.push_id` — `push id γ = γ` (via `Path.map_id`).
* `SmoothChain.push_id` — `ℤ`-linear-map equality with `LinearMap.id`.
* `SmoothCycle.pushHom_id` — `AddMonoidHom` equality with the identity.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

/-- **Identity functoriality of `SmoothPath.push`.** -/
theorem SmoothPath.push_id (γ : SmoothPath I X) :
    SmoothPath.push (id : X → X) contMDiff_id γ = γ := by
  -- `src`, `tgt` match definitionally; `toPath` via `Path.map_id`;
  -- `smooth` is a `Prop`.
  have h_path : γ.toPath.map continuous_id = γ.toPath := Path.map_id γ.toPath
  show (⟨id γ.src, id γ.tgt, γ.toPath.map continuous_id, _⟩
          : SmoothPath I X) = γ
  -- The target is `γ` itself; rebuild it from its fields.
  cases γ with
  | mk src tgt p smooth =>
    show (⟨id src, id tgt, p.map continuous_id, _⟩ : SmoothPath I X)
      = ⟨src, tgt, p, smooth⟩
    -- `congr 1` reduces to per-field equality. `src`/`tgt` agree
    -- definitionally; `Path.map_id` is `@[simp]` and `congr` closes it
    -- automatically. `smooth` is `Prop`.
    congr 1

/-- **Identity functoriality of `SmoothChain.push`.** -/
theorem SmoothChain.push_id :
    SmoothChain.push (id : X → X) contMDiff_id
      = (LinearMap.id : SmoothChain I X →ₗ[ℤ] SmoothChain I X) := by
  apply Finsupp.lhom_ext
  intro γ n
  show SmoothChain.push (id : X → X) contMDiff_id (Finsupp.single γ n)
    = Finsupp.single γ n
  show Finsupp.lmapDomain ℤ ℤ (SmoothPath.push (id : X → X) contMDiff_id)
        (Finsupp.single γ n) = Finsupp.single γ n
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      SmoothPath.push_id γ]

/-- **Identity functoriality of `SmoothCycle.pushHom`.** -/
theorem SmoothCycle.pushHom_id :
    SmoothCycle.pushHom (id : X → X) contMDiff_id
      = AddMonoidHom.id (SmoothCycle I X) := by
  ext c
  change SmoothChain.push (id : X → X) contMDiff_id (c : SmoothChain I X)
    = (c : SmoothChain I X)
  rw [show SmoothChain.push (id : X → X) contMDiff_id (c : SmoothChain I X)
        = (LinearMap.id : SmoothChain I X →ₗ[ℤ] SmoothChain I X)
            (c : SmoothChain I X)
      from by rw [SmoothChain.push_id]]
  rfl

end JacobianChallenge

end
