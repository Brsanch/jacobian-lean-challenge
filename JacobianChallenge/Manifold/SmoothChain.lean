/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Data.Finsupp.Defs
import JacobianChallenge.Manifold.SmoothOneForm

/-! # Smooth singular 1-chains on a smooth manifold

This file introduces the foundational types for the chain side of the
partition-of-unity-Stokes infrastructure (R5 route): smooth 1-paths and
smooth singular 1-chains as finite formal `ℤ`-linear combinations of
smooth paths.

## Main definitions

* `SmoothPath I X` — a wrapper around mathlib's `Path src tgt` carrying
  a `C^∞` smoothness proof of the underlying continuous map
  `unitInterval → X`. Smoothness is phrased as `ContMDiff` between the
  trivial model `𝓘(ℝ, ℝ)` on `unitInterval` (viewed as a topological
  subspace of `ℝ`) and the manifold model `I` on `X`.

* `SmoothChain I X` — finite formal `ℤ`-linear combinations of
  `SmoothPath I X`, modelled as `SmoothPath I X →₀ ℤ`. This inherits
  `Zero`, `Add`, `Neg`, `AddCommGroup`, and `Module ℤ` structure from
  `Finsupp` for free.

* `SmoothChain.boundary` — the `ℤ`-linear boundary operator
  `SmoothChain I X →ₗ[ℤ] (X →₀ ℤ)` sending a path `γ` to
  `δ_{γ.tgt} - δ_{γ.src}` and extending linearly.

## Design notes

The smoothness condition is recorded against the trivial model
`𝓘(ℝ, ℝ)` on `unitInterval` (the chart for the `Subtype` is the
inclusion into `ℝ`) and the model `I` on `X`. The target regularity is
`⊤` (= `C^∞`), matching `SmoothOneForm`.

We deliberately do *not* define integration here: that requires
`SmoothOneForm` pullback and `intervalIntegral`, which is the next
infrastructure layer. Likewise, equality / equivalence of paths up to
reparametrisation is left to a later chip.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (X : Type*) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

/-- A smooth singular 1-simplex on `X`: a continuous path `[0,1] → X`
between two endpoints together with a `C^∞` smoothness proof for the
underlying map `unitInterval → X`. -/
structure SmoothPath where
  /-- Source point of the path. -/
  src : X
  /-- Target point of the path. -/
  tgt : X
  /-- Underlying continuous path from mathlib's `Path` type. -/
  toPath : Path src tgt
  /-- Smoothness witness: there exists a smooth ambient map
  `ℝ → X` (against the trivial model `𝓘(ℝ, ℝ)` on `ℝ` and the manifold
  model `I` on `X`) which agrees with the underlying path on
  `unitInterval`. Avoiding a direct `ChartedSpace` instance on
  `unitInterval` keeps the typeclass picture trivial and lets later
  chips work on the ambient `ℝ`. -/
  smooth : ∃ f : ℝ → X,
    ContMDiff (𝓘(ℝ, ℝ)) I ⊤ f ∧
      ∀ t : unitInterval, f t.val = toPath t

namespace SmoothPath

variable {I X}

/-- The endpoint of a smooth path at parameter `0`. -/
def source (γ : SmoothPath I X) : X := γ.src

/-- The endpoint of a smooth path at parameter `1`. -/
def target (γ : SmoothPath I X) : X := γ.tgt

end SmoothPath

/-- A smooth singular 1-chain on `X` is a finite formal `ℤ`-linear
combination of smooth paths. We model it as a `Finsupp` from
`SmoothPath I X` to `ℤ`; the ambient algebraic structure (zero, add,
neg, scalar action of `ℤ`) is inherited from `Finsupp`. -/
def SmoothChain : Type _ := SmoothPath I X →₀ ℤ

namespace SmoothChain

variable {I X}

instance : Zero (SmoothChain I X) := inferInstanceAs <| Zero (SmoothPath I X →₀ ℤ)
instance : Add (SmoothChain I X) := inferInstanceAs <| Add (SmoothPath I X →₀ ℤ)
instance : Neg (SmoothChain I X) := inferInstanceAs <| Neg (SmoothPath I X →₀ ℤ)
instance : Sub (SmoothChain I X) := inferInstanceAs <| Sub (SmoothPath I X →₀ ℤ)
instance : AddCommGroup (SmoothChain I X) :=
  inferInstanceAs <| AddCommGroup (SmoothPath I X →₀ ℤ)
instance : SMul ℤ (SmoothChain I X) := inferInstanceAs <| SMul ℤ (SmoothPath I X →₀ ℤ)
instance : Module ℤ (SmoothChain I X) := inferInstanceAs <| Module ℤ (SmoothPath I X →₀ ℤ)

/-- The single-generator smooth chain associated to a smooth path `γ`
with coefficient `1`. -/
def single (γ : SmoothPath I X) : SmoothChain I X :=
  Finsupp.single γ 1

/-- The boundary of a single smooth path `γ`, viewed as a formal
`ℤ`-linear combination of points: `∂γ = δ_{γ.tgt} - δ_{γ.src}`. -/
def boundarySingle (γ : SmoothPath I X) : X →₀ ℤ :=
  Finsupp.single γ.tgt 1 - Finsupp.single γ.src 1

/-- The boundary operator on smooth 1-chains, sending a path `γ` to
`δ_{γ.tgt} - δ_{γ.src}` and extending `ℤ`-linearly. We define it
through `Finsupp.linearCombination` to inherit additivity for free. -/
def boundary : SmoothChain I X →ₗ[ℤ] (X →₀ ℤ) :=
  Finsupp.linearCombination ℤ boundarySingle

@[simp] lemma boundary_single (γ : SmoothPath I X) :
    boundary (single γ) = boundarySingle γ := by
  show Finsupp.linearCombination ℤ boundarySingle (Finsupp.single γ 1) = _
  rw [Finsupp.linearCombination_apply, Finsupp.sum_single_index]
  · simp
  · simp

@[simp] lemma boundary_zero : boundary (0 : SmoothChain I X) = 0 :=
  map_zero _

@[simp] lemma boundary_add (c₁ c₂ : SmoothChain I X) :
    boundary (c₁ + c₂) = boundary c₁ + boundary c₂ :=
  map_add _ _ _

@[simp] lemma boundary_neg (c : SmoothChain I X) :
    boundary (-c) = -boundary c :=
  map_neg _ _

end SmoothChain

end
