/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothChainPush

set_option linter.unusedSectionVars false

/-! # Composition functoriality of `SmoothPath`/`Chain`/`Cycle` pushforward

Sister to `HolomorphicOneFormPullbackComp` on the dual side. For smooth
maps `f : X → Y` and `g : Y → Z`, the pushforward of paths/chains/cycles
along `g ∘ f` factors through pushforward along `f` then along `g`.

* `SmoothPath.push_comp` — `push (g ∘ f) γ = push g (push f γ)`.
* `SmoothChain.push_comp` — `ℤ`-linear-map equality.
* `SmoothCycle.pushHom_comp` — `AddMonoidHom` equality on cycles.

These are the building blocks for `PeriodPairingMorphism.comp_ofSmoothCycle`
(the composition functoriality of the period-pairing-morphism bundle).
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ⊤ Y]
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ⊤ Z]

/-- **Composition functoriality of `SmoothPath.push`.** For smooth maps
`f : X → Y` and `g : Y → Z`, `(g ∘ f)_* γ = g_* (f_* γ)`.

The proof reduces to:
* `src`/`tgt` match definitionally via `Function.comp`;
* `toPath` matches via `Path.map_map`;
* `smooth` is a `Prop` (`∃`), so proof-irrelevance applies.
-/
theorem SmoothPath.push_comp
    (g : Y → Z) (hg : ContMDiff I I ∞ g)
    (f : X → Y) (hf : ContMDiff I I ∞ f) (γ : SmoothPath I X) :
    SmoothPath.push (g ∘ f) (hg.comp hf) γ
      = SmoothPath.push g hg (SmoothPath.push f hf γ) := by
  -- Unfold the two `push` applications by `cases`-ing `γ`; both sides
  -- become explicit `SmoothPath.mk` terms with definitionally-equal
  -- `src`/`tgt` (via `Function.comp`) and `toPath` values differing by
  -- `Path.map_map`.
  have h_path :
      γ.toPath.map (hg.comp hf).continuous
        = (γ.toPath.map hf.continuous).map hg.continuous :=
    (Path.map_map γ.toPath hf.continuous hg.continuous).symm
  -- Structure equality via `congr` after the path equality is in scope.
  show (⟨(g ∘ f) γ.src, (g ∘ f) γ.tgt,
          γ.toPath.map (hg.comp hf).continuous, _⟩ : SmoothPath I Z)
    = ⟨(g ∘ f) γ.src, (g ∘ f) γ.tgt,
       (γ.toPath.map hf.continuous).map hg.continuous, _⟩
  congr 1

/-- **Composition functoriality of `SmoothChain.push`.** -/
theorem SmoothChain.push_comp
    (g : Y → Z) (hg : ContMDiff I I ∞ g)
    (f : X → Y) (hf : ContMDiff I I ∞ f) :
    SmoothChain.push (g ∘ f) (hg.comp hf)
      = (SmoothChain.push g hg).comp (SmoothChain.push f hf) := by
  apply Finsupp.lhom_ext
  intro γ n
  show SmoothChain.push (g ∘ f) (hg.comp hf) (Finsupp.single γ n)
    = SmoothChain.push g hg (SmoothChain.push f hf (Finsupp.single γ n))
  show Finsupp.lmapDomain ℤ ℤ (SmoothPath.push (g ∘ f) (hg.comp hf))
        (Finsupp.single γ n)
    = Finsupp.lmapDomain ℤ ℤ (SmoothPath.push g hg)
        (Finsupp.lmapDomain ℤ ℤ (SmoothPath.push f hf)
          (Finsupp.single γ n))
  rw [Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      Finsupp.mapDomain_single, Finsupp.mapDomain_single,
      SmoothPath.push_comp g hg f hf γ]

/-- **Composition functoriality of `SmoothCycle.pushHom`.** -/
theorem SmoothCycle.pushHom_comp
    (g : Y → Z) (hg : ContMDiff I I ∞ g)
    (f : X → Y) (hf : ContMDiff I I ∞ f) :
    SmoothCycle.pushHom (g ∘ f) (hg.comp hf)
      = (SmoothCycle.pushHom g hg).comp (SmoothCycle.pushHom f hf) := by
  ext c
  change SmoothChain.push (g ∘ f) (hg.comp hf) (c : SmoothChain I X)
    = SmoothChain.push g hg
        (SmoothChain.push f hf (c : SmoothChain I X))
  rw [show SmoothChain.push (g ∘ f) (hg.comp hf) (c : SmoothChain I X)
        = ((SmoothChain.push g hg).comp (SmoothChain.push f hf))
            (c : SmoothChain I X)
      from by rw [SmoothChain.push_comp g hg f hf]]
  rfl

end JacobianChallenge

end
