/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import JacobianChallenge.Manifold.SmoothChain
import JacobianChallenge.Manifold.SmoothOneForm

/-! # Integration of a smooth 1-form over a smooth path / chain

This file introduces the pairing

    `∫_γ ω := ∫_{t ∈ [0,1]} ω(γ t)(γ' t) dt`

between a smooth 1-form `ω : SmoothOneForm I X` and a smooth singular
1-path `γ : SmoothPath I X`, and extends it `ℤ`-linearly to a smooth
1-chain `c : SmoothChain I X`.

## Main definitions

* `SmoothPath.velocity γ t` — the velocity vector `γ' t ∈ E` of a
  smooth path at parameter `t : ℝ`, extracted from the chosen ambient
  smooth extension of `γ`.

* `SmoothPath.integrand γ ω t` — the real-valued integrand
  `ω (γ t) (γ' t)` for the path integral.

* `SmoothPath.integrate γ ω` — the path integral
  `∫_{0}^{1} ω(γ t)(γ' t) dt` as a real number.

* `SmoothChain.integrate c ω` — the `ℤ`-linear extension of
  `SmoothPath.integrate` to a `SmoothChain`.

## Main lemmas

* `SmoothPath.integrate_smul` — scalar linearity of the path integral.
* `SmoothPath.integrate_add` — additivity of the path integral, modulo
  per-form integrability hypotheses.
* `SmoothChain.integrate_zero`, `_single`, `_add` — basic identities of
  the chain integral.

## Design notes

The smoothness hypothesis on a `SmoothPath` provides an ambient smooth
map `f : ℝ → X`. We use `mfderiv (𝓘(ℝ, ℝ)) I f t : ℝ →L[ℝ] TangentSpace
I (f t)` applied to `(1 : ℝ)` as the velocity, and pair it with
`ω (f t) : CotangentSpace I (f t)` via plain continuous-linear-map
application (both fibres reduce to `E →L[ℝ] ℝ` and `E` definitionally).

We deliberately do *not* prove Stokes' theorem or chart-pullback
compatibility here — separate chips.
-/

open scoped Manifold Topology Bundle ContDiff
open MeasureTheory intervalIntegral

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

/-- Smoothness regularity downcast: `IsManifold I ⊤ X` implies
`IsManifold I 1 X`, the hypothesis under which `SmoothOneForm` is
registered. We expose it as an instance so that downstream coercions
typecheck. -/
instance (priority := 100) SmoothPathIntegral.manifold_one :
    IsManifold I 1 X :=
  IsManifold.of_le (le_top : (1 : WithTop ℕ∞) ≤ ⊤)

namespace SmoothPath

/-- An arbitrary but fixed ambient smooth extension `ℝ → X` of `γ`
chosen via `Classical.choose` from `γ.smooth`. -/
def ambient (γ : SmoothPath I X) : ℝ → X := Classical.choose γ.smooth

lemma ambient_contMDiff (γ : SmoothPath I X) :
    ContMDiff (𝓘(ℝ, ℝ)) I ⊤ γ.ambient :=
  (Classical.choose_spec γ.smooth).1

lemma ambient_eq_on_unitInterval (γ : SmoothPath I X) (t : unitInterval) :
    γ.ambient t.val = γ.toPath t :=
  (Classical.choose_spec γ.smooth).2 t

/-- The velocity vector `γ' t ∈ E` of the chosen ambient smooth
extension of `γ` at parameter `t : ℝ`. -/
def velocity (γ : SmoothPath I X) (t : ℝ) : E :=
  (mfderiv (𝓘(ℝ, ℝ)) I γ.ambient t : ℝ →L[ℝ] TangentSpace I (γ.ambient t))
    (1 : ℝ)

/-- Pair a covector at `x` with a tangent vector. Both
`CotangentSpace I x` and `TangentSpace I x` reduce definitionally to
`E →L[ℝ] ℝ` and `E`; the pairing is plain CLM application. -/
def applyCotangent {x : X} (φ : CotangentSpace I x) (v : E) : ℝ :=
  (show E →L[ℝ] ℝ from φ) v

/-- The integrand `t ↦ ω(γ t)(γ' t)` of the path integral. -/
def integrand (γ : SmoothPath I X) (ω : SmoothOneForm I X) (t : ℝ) : ℝ :=
  applyCotangent (ω (γ.ambient t)) (γ.velocity t)

/-- The integral of a smooth 1-form `ω` along a smooth path `γ`,
defined as `∫_{0}^{1} ω(γ t)(γ' t) dt`. -/
def integrate (γ : SmoothPath I X) (ω : SmoothOneForm I X) : ℝ :=
  ∫ t in (0 : ℝ)..1, γ.integrand ω t

end SmoothPath

namespace SmoothPath

@[simp] lemma applyCotangent_zero {x : X} (v : E) :
    applyCotangent (0 : CotangentSpace I x) v = 0 := by
  simp [applyCotangent]

@[simp] lemma applyCotangent_add {x : X} (φ ψ : CotangentSpace I x) (v : E) :
    applyCotangent (φ + ψ) v = applyCotangent φ v + applyCotangent ψ v := by
  simp [applyCotangent, ContinuousLinearMap.add_apply]

@[simp] lemma applyCotangent_smul {x : X} (c : ℝ) (φ : CotangentSpace I x)
    (v : E) :
    applyCotangent (c • φ) v = c * applyCotangent φ v := by
  simp [applyCotangent, ContinuousLinearMap.smul_apply, smul_eq_mul]

variable (γ : SmoothPath I X)

@[simp] lemma integrand_zero (t : ℝ) :
    γ.integrand (0 : SmoothOneForm I X) t = 0 := by
  unfold integrand
  rw [show (0 : SmoothOneForm I X) (γ.ambient t)
        = (0 : CotangentSpace I (γ.ambient t)) from rfl,
      applyCotangent_zero]

@[simp] lemma integrand_add (ω₁ ω₂ : SmoothOneForm I X) (t : ℝ) :
    γ.integrand (ω₁ + ω₂) t = γ.integrand ω₁ t + γ.integrand ω₂ t := by
  unfold integrand
  rw [show (ω₁ + ω₂) (γ.ambient t)
        = ω₁ (γ.ambient t) + ω₂ (γ.ambient t) from rfl,
      applyCotangent_add]

@[simp] lemma integrand_smul (c : ℝ) (ω : SmoothOneForm I X) (t : ℝ) :
    γ.integrand (c • ω) t = c * γ.integrand ω t := by
  unfold integrand
  rw [show (c • ω) (γ.ambient t)
        = c • ω (γ.ambient t) from rfl,
      applyCotangent_smul]

@[simp] theorem integrate_zero :
    γ.integrate (0 : SmoothOneForm I X) = 0 := by
  unfold integrate
  simp_rw [integrand_zero]
  simp

/-- Linearity of the path integral in the 1-form: scalar
multiplication. The integrand becomes `c * (γ.integrand ω t)`, and
`intervalIntegral.integral_const_mul` pulls the constant outside. -/
theorem integrate_smul (c : ℝ) (ω : SmoothOneForm I X) :
    γ.integrate (c • ω) = c * γ.integrate ω := by
  unfold integrate
  simp_rw [integrand_smul]
  exact intervalIntegral.integral_const_mul c _

/-- Linearity of the path integral in the 1-form: addition. We need
each summand to be interval-integrable; this is automatic once a chart
pullback compatibility lemma is proved (separate chip). -/
theorem integrate_add (ω₁ ω₂ : SmoothOneForm I X)
    (h₁ : IntervalIntegrable (γ.integrand ω₁) MeasureTheory.volume 0 1)
    (h₂ : IntervalIntegrable (γ.integrand ω₂) MeasureTheory.volume 0 1) :
    γ.integrate (ω₁ + ω₂) = γ.integrate ω₁ + γ.integrate ω₂ := by
  unfold integrate
  simp_rw [integrand_add]
  exact intervalIntegral.integral_add h₁ h₂

end SmoothPath

namespace SmoothChain

/-- The integral of a smooth 1-form `ω` along a smooth 1-chain `c`,
i.e. `∑_{γ ∈ c.support} (c γ : ℝ) * γ.integrate ω`. -/
def integrate (c : SmoothChain I X) (ω : SmoothOneForm I X) : ℝ :=
  c.support.sum (fun γ => (c γ : ℝ) * γ.integrate ω)

@[simp] theorem integrate_zero (ω : SmoothOneForm I X) :
    integrate (0 : SmoothChain I X) ω = 0 := by
  unfold integrate
  simp

@[simp] theorem integrate_single (γ : SmoothPath I X) (ω : SmoothOneForm I X) :
    integrate (SmoothChain.single γ) ω = γ.integrate ω := by
  unfold integrate single
  have h1 : (1 : ℤ) ≠ 0 := one_ne_zero
  simp [Finsupp.support_single_ne_zero _ h1]

@[simp] theorem integrate_add (c₁ c₂ : SmoothChain I X) (ω : SmoothOneForm I X) :
    integrate (c₁ + c₂) ω = integrate c₁ ω + integrate c₂ ω := by
  classical
  unfold integrate
  -- Push all three sums onto the common index set `c₁.support ∪ c₂.support`
  -- by extending with zeros, then combine pointwise.
  have e₀ : (c₁ + c₂).support.sum
        (fun γ => ((c₁ + c₂) γ : ℝ) * γ.integrate ω) =
      (c₁.support ∪ c₂.support).sum
        (fun γ => ((c₁ + c₂) γ : ℝ) * γ.integrate ω) := by
    apply Finset.sum_subset Finsupp.support_add
    intro γ _ hγ
    have h0 : (c₁ + c₂) γ = 0 := Finsupp.notMem_support_iff.mp hγ
    rw [h0]; push_cast; ring
  have e₁ : c₁.support.sum (fun γ => (c₁ γ : ℝ) * γ.integrate ω) =
      (c₁.support ∪ c₂.support).sum
        (fun γ => (c₁ γ : ℝ) * γ.integrate ω) := by
    apply Finset.sum_subset Finset.subset_union_left
    intro γ _ hγ
    have h0 : c₁ γ = 0 := Finsupp.notMem_support_iff.mp hγ
    rw [h0]; push_cast; ring
  have e₂ : c₂.support.sum (fun γ => (c₂ γ : ℝ) * γ.integrate ω) =
      (c₁.support ∪ c₂.support).sum
        (fun γ => (c₂ γ : ℝ) * γ.integrate ω) := by
    apply Finset.sum_subset Finset.subset_union_right
    intro γ _ hγ
    have h0 : c₂ γ = 0 := Finsupp.notMem_support_iff.mp hγ
    rw [h0]; push_cast; ring
  rw [e₀, e₁, e₂, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro γ _
  have hsum : (c₁ + c₂) γ = c₁ γ + c₂ γ := Finsupp.add_apply _ _ _
  rw [hsum]; push_cast; ring

end SmoothChain

end
