/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothChain
import JacobianChallenge.Manifold.SmoothChainBoundary

set_option linter.unusedSectionVars false

/-! # Smooth singular 2-simplices on a smooth manifold

Sister type to `SmoothPath` (the smooth singular 1-simplices). A smooth
2-simplex is a `C^∞` map from the standard topological 2-simplex Δ²
into the manifold `X`. We carry an ambient extension `ℝ² → X` (using
`Fin 2 → ℝ` for the pi-manifold model) together with the C^∞
smoothness witness, mirroring `SmoothPath`'s ambient-extension
convention.

## Standard 2-simplex

Vertices `v₀, v₁, v₂ ∈ Fin 2 → ℝ`:
* `v₀ = (0, 0)`
* `v₁ = (1, 0)`
* `v₂ = (0, 1)`

The three boundary 1-faces (opposite each vertex), each a
`SmoothPath I X` derived from the ambient extension of the 2-simplex:

* `face₀` (opposite `v₀`): parameterised `t ↦ σ(1-t, t)`, from `v₁` to `v₂`.
* `face₁` (opposite `v₁`): parameterised `t ↦ σ(0, t)`, from `v₀` to `v₂`.
* `face₂` (opposite `v₂`): parameterised `t ↦ σ(t, 0)`, from `v₀` to `v₁`.

## The 2-chain boundary

`Smooth2Chain I X := Smooth2Simplex I X →₀ ℤ`. The boundary operator

  `boundary₂ : Smooth2Chain I X →ₗ[ℤ] SmoothChain I X`

extends the single-simplex boundary `∂σ = face₀ - face₁ + face₂`
linearly. The alternating signs are the standard simplicial convention;
they make `SmoothChain.boundary ∘ boundary₂ = 0` (the **d² = 0**
identity proved in this file).

## What this file ships

* `Smooth2Simplex I X` — the type.
* `Smooth2Simplex.face₀ / face₁ / face₂ : Smooth2Simplex I X → SmoothPath I X`.
* `Smooth2Simplex.boundary : Smooth2Simplex I X → SmoothChain I X` —
  signed sum of the three faces.
* `Smooth2Chain I X := Smooth2Simplex I X →₀ ℤ` with `AddCommGroup` /
  `Module ℤ` instances.
* `Smooth2Chain.boundary₂ : Smooth2Chain I X →ₗ[ℤ] SmoothChain I X` —
  the `ℤ`-linear extension of the per-simplex boundary.
* `Smooth2Chain.boundary_squared` — the **d² = 0** identity:
  `SmoothChain.boundary ∘ boundary₂ = 0`.

This is **pure algebraic infrastructure**. The integration-side Stokes'
theorem (`∫_{∂σ} ω = ∫∫_σ dω`) remains a named hypothesis (genuine
analytic content not at the mathlib pin).

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (X : Type*) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

/-- A smooth singular 2-simplex on `X`: a `C^∞` map `(Fin 2 → ℝ) → X`,
intended to model `σ : Δ² → X` via its ambient extension to the full
plane. -/
structure Smooth2Simplex where
  /-- Ambient smooth extension: a `C^∞` map from `Fin 2 → ℝ` (a
  pi-manifold model on `ℝ²`) into the manifold `X`. -/
  toFun : (Fin 2 → ℝ) → X
  /-- The smoothness witness, at `C^∞` regularity (`∞ : WithTop ℕ∞`). -/
  smooth : ContMDiff (𝓘(ℝ, Fin 2 → ℝ)) I ∞ toFun

namespace Smooth2Simplex

variable {I X}

/-! ## Vertices and face parameterisations -/

/-- Vertex `v₀ = (0, 0)` of the standard 2-simplex. -/
def v0 : Fin 2 → ℝ := ![0, 0]

/-- Vertex `v₁ = (1, 0)`. -/
def v1 : Fin 2 → ℝ := ![1, 0]

/-- Vertex `v₂ = (0, 1)`. -/
def v2 : Fin 2 → ℝ := ![0, 1]

/-- Parameter map for `face₀` (opposite `v₀`): `t ↦ (1-t, t)`.
Sends `0 ↦ v₁ = (1, 0)`, `1 ↦ v₂ = (0, 1)`. -/
def face0Param (t : ℝ) : Fin 2 → ℝ := ![1 - t, t]

/-- Parameter map for `face₁` (opposite `v₁`): `t ↦ (0, t)`.
Sends `0 ↦ v₀ = (0, 0)`, `1 ↦ v₂ = (0, 1)`. -/
def face1Param (t : ℝ) : Fin 2 → ℝ := ![0, t]

/-- Parameter map for `face₂` (opposite `v₂`): `t ↦ (t, 0)`.
Sends `0 ↦ v₀ = (0, 0)`, `1 ↦ v₁ = (1, 0)`. -/
def face2Param (t : ℝ) : Fin 2 → ℝ := ![t, 0]

@[simp] lemma face0Param_zero : face0Param 0 = v1 := by
  funext i; fin_cases i <;> simp [face0Param, v1]

@[simp] lemma face0Param_one : face0Param 1 = v2 := by
  funext i; fin_cases i <;> simp [face0Param, v2]

@[simp] lemma face1Param_zero : face1Param 0 = v0 := by
  funext i; fin_cases i <;> simp [face1Param, v0]

@[simp] lemma face1Param_one : face1Param 1 = v2 := by
  funext i; fin_cases i <;> simp [face1Param, v2]

@[simp] lemma face2Param_zero : face2Param 0 = v0 := by
  funext i; fin_cases i <;> simp [face2Param, v0]

@[simp] lemma face2Param_one : face2Param 1 = v1 := by
  funext i; fin_cases i <;> simp [face2Param, v1]

/-! ## Smoothness of face parameter maps

The face parameter maps `ℝ → Fin 2 → ℝ` are affine in `t`, hence
`C^∞`. -/

lemma contMDiff_face0Param :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin 2 → ℝ)) ∞ face0Param := by
  -- A function `ℝ → Fin n → ℝ` is `ContMDiff` iff each component is.
  rw [contMDiff_pi_space]
  intro i
  fin_cases i
  · -- component 0: t ↦ 1 - t. Affine, hence C^∞.
    show ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => face0Param t 0)
    have h_eq : (fun t : ℝ => face0Param t 0) = fun t => 1 - t := by
      funext t; simp [face0Param]
    rw [h_eq]
    have : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => 1 - t) := by
      have h1 : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun _ : ℝ => (1 : ℝ)) :=
        contMDiff_const
      have h2 : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => t) := contMDiff_id
      exact h1.sub h2
    exact this
  · -- component 1: t ↦ t. Identity, hence C^∞.
    show ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => face0Param t 1)
    have h_eq : (fun t : ℝ => face0Param t 1) = fun t : ℝ => t := by
      funext t; simp [face0Param]
    rw [h_eq]; exact contMDiff_id

lemma contMDiff_face1Param :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin 2 → ℝ)) ∞ face1Param := by
  rw [contMDiff_pi_space]
  intro i
  fin_cases i
  · show ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => face1Param t 0)
    have h_eq : (fun t : ℝ => face1Param t 0) = fun _ : ℝ => (0 : ℝ) := by
      funext t; simp [face1Param]
    rw [h_eq]; exact contMDiff_const
  · show ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => face1Param t 1)
    have h_eq : (fun t : ℝ => face1Param t 1) = fun t : ℝ => t := by
      funext t; simp [face1Param]
    rw [h_eq]; exact contMDiff_id

lemma contMDiff_face2Param :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin 2 → ℝ)) ∞ face2Param := by
  rw [contMDiff_pi_space]
  intro i
  fin_cases i
  · show ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => face2Param t 0)
    have h_eq : (fun t : ℝ => face2Param t 0) = fun t : ℝ => t := by
      funext t; simp [face2Param]
    rw [h_eq]; exact contMDiff_id
  · show ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => face2Param t 1)
    have h_eq : (fun t : ℝ => face2Param t 1) = fun _ : ℝ => (0 : ℝ) := by
      funext t; simp [face2Param]
    rw [h_eq]; exact contMDiff_const

/-! ## The three faces of a smooth 2-simplex as `SmoothPath`s -/

/-- Helper: a continuous path between two endpoints from a continuous
function on `unitInterval`. -/
private def pathOfUnitIntervalMap {Y : Type*} [TopologicalSpace Y]
    (f : unitInterval → Y) (hf : Continuous f) (a b : Y)
    (ha : f 0 = a) (hb : f 1 = b) : Path a b where
  toFun := f
  continuous_toFun := hf
  source' := ha
  target' := hb

/-- The face opposite `v₀` of a smooth 2-simplex: the path from
`σ(v₁)` to `σ(v₂)` parameterised by `t ↦ σ(1 - t, t)`. -/
def face0 (σ : Smooth2Simplex I X) : SmoothPath I X where
  src := σ.toFun v1
  tgt := σ.toFun v2
  toPath :=
    pathOfUnitIntervalMap
      (fun t => σ.toFun (face0Param t.val))
      ((σ.smooth.continuous.comp (contMDiff_face0Param.continuous)).comp
        continuous_subtype_val)
      (σ.toFun v1) (σ.toFun v2)
      (by simp [face0Param_zero])
      (by simp [face0Param_one])
  smooth := by
    refine ⟨fun t : ℝ => σ.toFun (face0Param t), ?_, ?_⟩
    · -- ContMDiff of σ ∘ face0Param.
      exact σ.smooth.comp contMDiff_face0Param
    · intro t
      rfl

/-- The face opposite `v₁` of a smooth 2-simplex: the path from
`σ(v₀)` to `σ(v₂)` parameterised by `t ↦ σ(0, t)`. -/
def face1 (σ : Smooth2Simplex I X) : SmoothPath I X where
  src := σ.toFun v0
  tgt := σ.toFun v2
  toPath :=
    pathOfUnitIntervalMap
      (fun t => σ.toFun (face1Param t.val))
      ((σ.smooth.continuous.comp (contMDiff_face1Param.continuous)).comp
        continuous_subtype_val)
      (σ.toFun v0) (σ.toFun v2)
      (by simp [face1Param_zero])
      (by simp [face1Param_one])
  smooth := by
    refine ⟨fun t : ℝ => σ.toFun (face1Param t), ?_, ?_⟩
    · exact σ.smooth.comp contMDiff_face1Param
    · intro t; rfl

/-- The face opposite `v₂` of a smooth 2-simplex: the path from
`σ(v₀)` to `σ(v₁)` parameterised by `t ↦ σ(t, 0)`. -/
def face2 (σ : Smooth2Simplex I X) : SmoothPath I X where
  src := σ.toFun v0
  tgt := σ.toFun v1
  toPath :=
    pathOfUnitIntervalMap
      (fun t => σ.toFun (face2Param t.val))
      ((σ.smooth.continuous.comp (contMDiff_face2Param.continuous)).comp
        continuous_subtype_val)
      (σ.toFun v0) (σ.toFun v1)
      (by simp [face2Param_zero])
      (by simp [face2Param_one])
  smooth := by
    refine ⟨fun t : ℝ => σ.toFun (face2Param t), ?_, ?_⟩
    · exact σ.smooth.comp contMDiff_face2Param
    · intro t; rfl

@[simp] lemma face0_src (σ : Smooth2Simplex I X) : (face0 σ).src = σ.toFun v1 := rfl
@[simp] lemma face0_tgt (σ : Smooth2Simplex I X) : (face0 σ).tgt = σ.toFun v2 := rfl
@[simp] lemma face1_src (σ : Smooth2Simplex I X) : (face1 σ).src = σ.toFun v0 := rfl
@[simp] lemma face1_tgt (σ : Smooth2Simplex I X) : (face1 σ).tgt = σ.toFun v2 := rfl
@[simp] lemma face2_src (σ : Smooth2Simplex I X) : (face2 σ).src = σ.toFun v0 := rfl
@[simp] lemma face2_tgt (σ : Smooth2Simplex I X) : (face2 σ).tgt = σ.toFun v1 := rfl

/-! ## Boundary of a single 2-simplex as a 1-chain -/

/-- The boundary of a smooth 2-simplex `σ`, as a smooth 1-chain
`face₀ - face₁ + face₂` (with alternating simplicial signs). -/
def boundary (σ : Smooth2Simplex I X) : SmoothChain I X :=
  SmoothChain.single (face0 σ) - SmoothChain.single (face1 σ) +
    SmoothChain.single (face2 σ)

end Smooth2Simplex

/-- A smooth singular 2-chain on `X` is a finite formal `ℤ`-linear
combination of smooth 2-simplices. -/
def Smooth2Chain : Type _ := Smooth2Simplex I X →₀ ℤ

namespace Smooth2Chain

variable {I X}

instance : Zero (Smooth2Chain I X) := inferInstanceAs <| Zero (Smooth2Simplex I X →₀ ℤ)
instance : Add (Smooth2Chain I X) := inferInstanceAs <| Add (Smooth2Simplex I X →₀ ℤ)
instance : Neg (Smooth2Chain I X) := inferInstanceAs <| Neg (Smooth2Simplex I X →₀ ℤ)
instance : Sub (Smooth2Chain I X) := inferInstanceAs <| Sub (Smooth2Simplex I X →₀ ℤ)
instance : AddCommGroup (Smooth2Chain I X) :=
  inferInstanceAs <| AddCommGroup (Smooth2Simplex I X →₀ ℤ)
instance : SMul ℤ (Smooth2Chain I X) := inferInstanceAs <| SMul ℤ (Smooth2Simplex I X →₀ ℤ)
instance : Module ℤ (Smooth2Chain I X) :=
  inferInstanceAs <| Module ℤ (Smooth2Simplex I X →₀ ℤ)

/-- The single-generator 2-chain with coefficient `1`. -/
def single (σ : Smooth2Simplex I X) : Smooth2Chain I X :=
  Finsupp.single σ 1

/-- The boundary operator on smooth 2-chains. Sends a single 2-simplex
`σ` to its boundary `face₀ - face₁ + face₂` and extends `ℤ`-linearly. -/
def boundary₂ : Smooth2Chain I X →ₗ[ℤ] SmoothChain I X :=
  Finsupp.linearCombination ℤ Smooth2Simplex.boundary

@[simp] lemma boundary₂_single (σ : Smooth2Simplex I X) :
    boundary₂ (single σ) = Smooth2Simplex.boundary σ := by
  show Finsupp.linearCombination ℤ Smooth2Simplex.boundary (Finsupp.single σ 1) = _
  rw [Finsupp.linearCombination_apply, Finsupp.sum_single_index]
  · simp
  · simp

@[simp] lemma boundary₂_zero : boundary₂ (0 : Smooth2Chain I X) = 0 :=
  map_zero _

@[simp] lemma boundary₂_add (c₁ c₂ : Smooth2Chain I X) :
    boundary₂ (c₁ + c₂) = boundary₂ c₁ + boundary₂ c₂ :=
  map_add _ _ _

@[simp] lemma boundary₂_neg (c : Smooth2Chain I X) :
    boundary₂ (-c) = -boundary₂ c :=
  map_neg _ _

/-! ## The d² = 0 identity

The boundary of the boundary of a smooth 2-simplex is zero as a formal
combination of points (`X →₀ ℤ`). This is the standard simplicial
cancellation: each vertex appears exactly once positively and once
negatively in `∂² σ`. -/

/-- **d² = 0 for a single 2-simplex.** -/
theorem boundary_squared_single (σ : Smooth2Simplex I X) :
    SmoothChain.boundary (Smooth2Simplex.boundary σ) = 0 := by
  -- Unfold the boundary chain.
  unfold Smooth2Simplex.boundary
  -- Linearity of SmoothChain.boundary on the sum/difference.
  rw [map_add, map_sub, SmoothChain.boundary_single, SmoothChain.boundary_single,
    SmoothChain.boundary_single]
  -- Each `boundarySingle` is `δ_tgt - δ_src` of the corresponding face.
  -- face₀: tgt = v₂, src = v₁.
  -- face₁: tgt = v₂, src = v₀.
  -- face₂: tgt = v₁, src = v₀.
  -- ∂(face₀) - ∂(face₁) + ∂(face₂)
  --   = (δ_{σ v₂} - δ_{σ v₁}) - (δ_{σ v₂} - δ_{σ v₀}) + (δ_{σ v₁} - δ_{σ v₀})
  --   = 0.
  simp only [SmoothChain.boundarySingle, Smooth2Simplex.face0_src,
    Smooth2Simplex.face0_tgt, Smooth2Simplex.face1_src,
    Smooth2Simplex.face1_tgt, Smooth2Simplex.face2_src,
    Smooth2Simplex.face2_tgt]
  abel

/-- **d² = 0 for a single-generator 2-chain.** -/
@[simp] theorem boundary_squared_singleChain (σ : Smooth2Simplex I X) :
    SmoothChain.boundary (boundary₂ (single σ)) = 0 := by
  rw [boundary₂_single]
  exact boundary_squared_single σ

/-- **d² = 0 globally**, as a `ℤ`-linear-map identity. -/
theorem boundary_squared :
    SmoothChain.boundary.comp (boundary₂ : Smooth2Chain I X →ₗ[ℤ] _) = 0 := by
  -- Two ℤ-linear maps out of `Smooth2Chain = Smooth2Simplex →₀ ℤ`
  -- agree iff they agree on single generators (`Finsupp.lhom_ext`).
  refine Finsupp.lhom_ext (fun σ k => ?_)
  -- LHS: `SmoothChain.boundary (boundary₂ (Finsupp.single σ k))`.
  -- Rewrite `Finsupp.single σ k = k • single σ` via the Finsupp smul rule.
  show SmoothChain.boundary (boundary₂ (Finsupp.single σ k)) = 0
  have h_single_smul :
      (Finsupp.single σ k : Smooth2Chain I X) = k • single σ := by
    show Finsupp.single σ k = k • Finsupp.single σ (1 : ℤ)
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [h_single_smul, map_smul, map_smul, boundary_squared_singleChain, smul_zero]

/-- **d² = 0 applied pointwise on a 2-chain.** Equivalent reformulation of
`boundary_squared`. -/
theorem boundary_boundary₂ (c : Smooth2Chain I X) :
    SmoothChain.boundary (boundary₂ c) = 0 := by
  have h := boundary_squared (I := I) (X := X)
  exact LinearMap.congr_fun h c

end Smooth2Chain

end
