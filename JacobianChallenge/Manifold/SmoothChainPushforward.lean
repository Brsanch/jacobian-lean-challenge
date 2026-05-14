/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothChain
import JacobianChallenge.Manifold.SmoothPathCompSmooth

set_option linter.unusedSectionVars false

/-! # `SmoothChain` pushforward by a smooth map

Extends `ContMDiff.compSmoothPath` from single paths to chains. The
`ℤ`-linear pushforward `SmoothChain.compSmoothMap hf c` of a chain
`c : SmoothChain I X` along a C^∞ map `f : X → Y` is the
generator-wise pushforward `Σ c(γ) • single (compSmoothPath hf γ)`.

Equivalently: `Finsupp.lmapDomain` applied to the function
`γ ↦ compSmoothPath hf γ : SmoothPath I X → SmoothPath I' Y`.

The pushforward commutes with the boundary operator: for the
0-chain side, the pushforward is `Finsupp.lmapDomain` applied to the
point map `f : X → Y`.

## What this file delivers

* `SmoothChain.compSmoothMap : ContMDiff I I' ∞ f → (SmoothChain I X
   →ₗ[ℤ] SmoothChain I' Y)` — the linear pushforward.
* `SmoothChain.compSmoothMap_single` — `single γ` pushes to
  `single (compSmoothPath hf γ)`.
* `SmoothChain.boundary_compSmoothMap` — pushforward commutes with
  boundary: `boundary (compSmoothMap hf c) = Finsupp.mapDomain f
  (boundary c)`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology
open Finsupp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ⊤ Y]

namespace SmoothChain

/-- **Linear pushforward of a smooth 1-chain.** The function
`γ ↦ compSmoothPath hf γ : SmoothPath I X → SmoothPath I' Y` lifts to
a `ℤ`-linear map `SmoothChain I X →ₗ[ℤ] SmoothChain I' Y` via
`Finsupp.lmapDomain`. -/
noncomputable def compSmoothMap {f : X → Y}
    (hf : ContMDiff I I' ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    SmoothChain I X →ₗ[ℤ] SmoothChain I' Y :=
  Finsupp.lmapDomain ℤ ℤ (fun γ : SmoothPath I X => hf.compSmoothPath γ)

@[simp] lemma compSmoothMap_single {f : X → Y}
    (hf : ContMDiff I I' ((⊤ : ℕ∞) : WithTop ℕ∞) f) (γ : SmoothPath I X) :
    compSmoothMap hf (single γ) = single (hf.compSmoothPath γ) := by
  show (Finsupp.lmapDomain ℤ ℤ (fun γ => hf.compSmoothPath γ))
        (Finsupp.single γ (1 : ℤ)) = Finsupp.single (hf.compSmoothPath γ) 1
  simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

@[simp] lemma compSmoothMap_zero {f : X → Y}
    (hf : ContMDiff I I' ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    compSmoothMap hf (0 : SmoothChain I X) = 0 :=
  map_zero _

@[simp] lemma compSmoothMap_add {f : X → Y}
    (hf : ContMDiff I I' ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (c₁ c₂ : SmoothChain I X) :
    compSmoothMap hf (c₁ + c₂) = compSmoothMap hf c₁ + compSmoothMap hf c₂ :=
  map_add _ _ _

@[simp] lemma compSmoothMap_neg {f : X → Y}
    (hf : ContMDiff I I' ((⊤ : ℕ∞) : WithTop ℕ∞) f) (c : SmoothChain I X) :
    compSmoothMap hf (-c) = -compSmoothMap hf c :=
  map_neg _ _

/-! ## Compatibility with the boundary operator

The smooth-chain pushforward commutes with the boundary operator:
for a single path `γ`, `boundary (compSmoothPath hf γ) = δ_{f(γ.tgt)}
- δ_{f(γ.src)} = pushforward of (δ_{γ.tgt} - δ_{γ.src})`. Extending
linearly gives the chain-level identity. -/

/-- **Boundary commutes with pushforward.** For a single path `γ`:
`boundarySingle (compSmoothPath hf γ) = Finsupp.mapDomain f
(boundarySingle γ)`. -/
@[simp] lemma boundarySingle_compSmoothPath {f : X → Y}
    (hf : ContMDiff I I' ((⊤ : ℕ∞) : WithTop ℕ∞) f) (γ : SmoothPath I X) :
    boundarySingle (hf.compSmoothPath γ)
      = Finsupp.mapDomain f (boundarySingle γ) := by
  unfold boundarySingle
  rw [ContMDiff.compSmoothPath_src, ContMDiff.compSmoothPath_tgt,
      Finsupp.mapDomain_sub, Finsupp.mapDomain_single,
      Finsupp.mapDomain_single]

/-- **Auxiliary identity.** `boundary (Finsupp.single δ m) = m • boundarySingle δ`
on the X-side. -/
private lemma boundary_single_eq_smul_X
    (δ : SmoothPath I X) (m : ℤ) :
    boundary (Finsupp.single δ m : SmoothChain I X)
      = m • boundarySingle δ := by
  show Finsupp.linearCombination ℤ boundarySingle (Finsupp.single δ m) = _
  rw [Finsupp.linearCombination_apply, Finsupp.sum_single_index]
  simp

/-- Y-side variant of the same. -/
private lemma boundary_single_eq_smul_Y
    (δ : SmoothPath I' Y) (m : ℤ) :
    boundary (Finsupp.single δ m : SmoothChain I' Y)
      = m • boundarySingle δ := by
  show Finsupp.linearCombination ℤ boundarySingle (Finsupp.single δ m) = _
  rw [Finsupp.linearCombination_apply, Finsupp.sum_single_index]
  simp

/-- **Boundary commutes with pushforward, as `LinearMap` equation.**
`boundary ∘ compSmoothMap hf = lmapDomain f ∘ boundary`. -/
theorem boundary_comp_compSmoothMap {f : X → Y}
    (hf : ContMDiff I I' ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    boundary.comp (compSmoothMap hf)
      = (Finsupp.lmapDomain ℤ ℤ f).comp boundary := by
  refine Finsupp.lhom_ext (fun γ n => ?_)
  -- Goal at single generator (γ : SmoothPath I X, n : ℤ):
  --   boundary (compSmoothMap hf (Finsupp.single γ n))
  --     = Finsupp.lmapDomain ℤ ℤ f (boundary (Finsupp.single γ n)).
  show boundary (compSmoothMap hf (Finsupp.single γ n))
        = Finsupp.lmapDomain ℤ ℤ f (boundary (Finsupp.single γ n))
  -- LHS: pushforward of `Finsupp.single γ n` is
  -- `Finsupp.single (hf.compSmoothPath γ) n`.
  have h_lhs : compSmoothMap hf (Finsupp.single γ n)
      = Finsupp.single (hf.compSmoothPath γ) n := by
    show (Finsupp.lmapDomain ℤ ℤ (fun γ => hf.compSmoothPath γ))
          (Finsupp.single γ n) = Finsupp.single (hf.compSmoothPath γ) n
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [h_lhs, boundary_single_eq_smul_Y (hf.compSmoothPath γ) n,
      boundary_single_eq_smul_X γ n,
      boundarySingle_compSmoothPath,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_smul]

/-- **Boundary commutes with pushforward, chain-level.**
`boundary (compSmoothMap hf c) = Finsupp.mapDomain f (boundary c)`. -/
theorem boundary_compSmoothMap {f : X → Y}
    (hf : ContMDiff I I' ((⊤ : ℕ∞) : WithTop ℕ∞) f) (c : SmoothChain I X) :
    boundary (compSmoothMap hf c)
      = Finsupp.mapDomain f (boundary c) := by
  have h := LinearMap.congr_fun (boundary_comp_compSmoothMap hf) c
  simpa [LinearMap.comp_apply] using h

end SmoothChain

end
