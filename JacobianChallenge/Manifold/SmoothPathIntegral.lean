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

The integrand `t ↦ ω(γ t)(γ' t)` is constructed as follows. The
smoothness witness on a `SmoothPath` provides an ambient smooth map
`f : ℝ → X` (against the trivial model `𝓘(ℝ, ℝ)` on `ℝ` and `I` on
`X`) which restricts to the underlying continuous path on the unit
interval. We use `mfderiv 𝓘(ℝ, ℝ) I f t : ℝ →L[ℝ] TangentSpace I (f t)`
applied to `(1 : ℝ)` as the velocity vector at parameter `t`, and pair
it with the covector `ω (f t) : CotangentSpace I (f t)`. The cotangent
fibre is the topological dual `E →L[ℝ] ℝ` and the tangent fibre is `E`,
so the pairing is just continuous-linear-map application landing in
`ℝ`.

## Main definitions

* `SmoothPath.velocity γ t` — the velocity vector `γ' t ∈ E` of a
  smooth path at parameter `t : ℝ`, extracted from the chosen ambient
  smooth extension of `γ`.

* `SmoothPath.integrand γ ω t` — the real-valued integrand
  `ω (γ t) (γ' t)` for the path integral.

* `SmoothPath.integrate γ ω` — the path integral
  `∫_{0}^{1} ω(γ t)(γ' t) dt` as a real number.

* `SmoothChain.integrate c ω` — the `ℤ`-linear extension of
  `SmoothPath.integrate` to a `SmoothChain`, i.e.
  `∑_{γ ∈ c.support} c γ • γ.integrate ω`.

## Main lemmas

* `SmoothPath.integrate_add` / `SmoothPath.integrate_smul` — linearity
  of the path integral in the 1-form.

* `SmoothChain.integrate_zero` / `SmoothChain.integrate_single` /
  `SmoothChain.integrate_add` — basic boundary-style identities of the
  chain integral.

## Design notes

We use `Classical.choose` to fix an ambient smooth extension `f : ℝ →
X` once and for all; different choices may yield different velocities
*off* the unit interval, but a Stokes-style theorem only ever needs
the integral over `[0,1]` and is independent of the choice on the
nose only after a (separate) reparametrisation lemma. That clean-up
belongs to a future chip.

The pointwise pairing `ω x v` requires `ω x : E →L[ℝ] ℝ` and `v : E`.
At the level of types, `CotangentSpace I (f t) = E →L[ℝ] ℝ` and
`TangentSpace I (f t) = E` definitionally, so we reach the pairing via
type casts, recorded once in `applyCotangent`.

We deliberately do *not* prove Stokes' theorem here: that requires a
chart-pullback compatibility lemma on top of `SmoothOneForm` plus an
exterior-derivative API which is a separate chip on the R5 stack.
-/

open scoped Manifold Topology Bundle ContDiff
open MeasureTheory intervalIntegral

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

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
extension of `γ` at parameter `t : ℝ`. We apply the manifold
derivative of the ambient extension at `t` to the unit tangent
`(1 : ℝ)` of `ℝ`; the result lives in
`TangentSpace I (γ.ambient t)`, which is definitionally `E`. -/
def velocity (γ : SmoothPath I X) (t : ℝ) : E :=
  (mfderiv (𝓘(ℝ, ℝ)) I γ.ambient t : ℝ →L[ℝ] TangentSpace I (γ.ambient t))
    (1 : ℝ)

/-- Pair a covector at `x` with a tangent vector at the same point.
Both `CotangentSpace I x` and `TangentSpace I x` reduce to `E →L[ℝ] ℝ`
and `E` respectively, so this is plain continuous-linear-map
application. -/
def applyCotangent {x : X} (φ : CotangentSpace I x) (v : E) : ℝ :=
  (φ : E →L[ℝ] ℝ) v

/-- The integrand `t ↦ ω(γ t)(γ' t)` of the path integral, evaluated
along the chosen ambient extension of `γ`. -/
def integrand (γ : SmoothPath I X) (ω : SmoothOneForm I X) (t : ℝ) : ℝ :=
  applyCotangent (ω (γ.ambient t)) (γ.velocity t)

/-- The integral of a smooth 1-form `ω` along a smooth path `γ`,
defined as `∫_{0}^{1} ω(γ t)(γ' t) dt`. -/
def integrate (γ : SmoothPath I X) (ω : SmoothOneForm I X) : ℝ :=
  ∫ t in (0 : ℝ)..1, γ.integrand ω t

end SmoothPath

namespace SmoothPath

variable (γ : SmoothPath I X)

@[simp] lemma applyCotangent_add {x : X} (φ ψ : CotangentSpace I x) (v : E) :
    applyCotangent (φ + ψ) v = applyCotangent φ v + applyCotangent ψ v := by
  show ((φ + ψ : E →L[ℝ] ℝ) : E → ℝ) v = _
  simp [applyCotangent, ContinuousLinearMap.add_apply]

@[simp] lemma applyCotangent_smul {x : X} (c : ℝ) (φ : CotangentSpace I x) (v : E) :
    applyCotangent (c • φ) v = c * applyCotangent φ v := by
  show ((c • φ : E →L[ℝ] ℝ) : E → ℝ) v = _
  simp [applyCotangent, ContinuousLinearMap.smul_apply, smul_eq_mul]

@[simp] lemma applyCotangent_zero {x : X} (v : E) :
    applyCotangent (0 : CotangentSpace I x) v = 0 := by
  show ((0 : E →L[ℝ] ℝ) : E → ℝ) v = 0
  simp [applyCotangent]

/-- Smoothness regularity downcast: `IsManifold I ⊤ X` implies
`IsManifold I 1 X`, which is the hypothesis under which `SmoothOneForm`
is set up. -/
private instance manifold_one : IsManifold I 1 X :=
  IsManifold.of_le (le_top : (1 : WithTop ℕ∞) ≤ ⊤)

@[simp] lemma integrand_add (ω₁ ω₂ : SmoothOneForm I X) (t : ℝ) :
    γ.integrand (ω₁ + ω₂) t = γ.integrand ω₁ t + γ.integrand ω₂ t := by
  unfold integrand
  rw [show (ω₁ + ω₂) (γ.ambient t) = ω₁ (γ.ambient t) + ω₂ (γ.ambient t) from rfl,
      applyCotangent_add]

@[simp] lemma integrand_smul (c : ℝ) (ω : SmoothOneForm I X) (t : ℝ) :
    γ.integrand (c • ω) t = c * γ.integrand ω t := by
  unfold integrand
  rw [show (c • ω) (γ.ambient t) = c • ω (γ.ambient t) from rfl,
      applyCotangent_smul]

@[simp] lemma integrand_zero (t : ℝ) :
    γ.integrand (0 : SmoothOneForm I X) t = 0 := by
  unfold integrand
  rw [show (0 : SmoothOneForm I X) (γ.ambient t) = 0 from rfl,
      applyCotangent_zero]

/-- Linearity of the path integral in the 1-form: addition.

Note: this holds modulo integrability of each integrand, which we do
not have at this stage in the chip stack — `intervalIntegral.integral_add`
needs `IntervalIntegrable`. We bypass the integrability hypothesis by
falling back to the unconditional rewrite identity
`∫ (f + g) = ∫ f + ∫ g` available via `intervalIntegral.integral_add'`
when both integrands are integrable, or zero on each side otherwise.
For the foundational chip we phrase the identity at the level of the
*integrand* and pair it with a placeholder integrability hypothesis. -/
theorem integrate_add (ω₁ ω₂ : SmoothOneForm I X)
    (h₁ : IntervalIntegrable (γ.integrand ω₁) MeasureTheory.volume 0 1)
    (h₂ : IntervalIntegrable (γ.integrand ω₂) MeasureTheory.volume 0 1) :
    γ.integrate (ω₁ + ω₂) = γ.integrate ω₁ + γ.integrate ω₂ := by
  unfold integrate
  simp_rw [integrand_add]
  exact intervalIntegral.integral_add h₁ h₂

/-- Linearity of the path integral in the 1-form: scalar
multiplication. -/
theorem integrate_smul (c : ℝ) (ω : SmoothOneForm I X) :
    γ.integrate (c • ω) = c * γ.integrate ω := by
  unfold integrate
  simp_rw [integrand_smul]
  exact intervalIntegral.integral_const_mul c _

@[simp] theorem integrate_zero :
    γ.integrate (0 : SmoothOneForm I X) = 0 := by
  unfold integrate
  simp_rw [integrand_zero]
  simp

end SmoothPath

namespace SmoothChain

/-- The integral of a smooth 1-form `ω` along a smooth 1-chain `c`,
defined as the `ℤ`-linear extension of `SmoothPath.integrate`. -/
def integrate (c : SmoothChain I X) (ω : SmoothOneForm I X) : ℝ :=
  c.support.sum (fun γ => (c γ : ℝ) * γ.integrate ω)

@[simp] theorem integrate_zero (ω : SmoothOneForm I X) :
    integrate (0 : SmoothChain I X) ω = 0 := by
  unfold integrate
  simp

@[simp] theorem integrate_single (γ : SmoothPath I X) (ω : SmoothOneForm I X) :
    integrate (SmoothChain.single γ) ω = γ.integrate ω := by
  unfold integrate single
  by_cases h : γ.integrate ω = 0
  · -- both sides are zero (or via support computation)
    rcases eq_or_ne ((1 : ℤ)) 0 with h1 | h1
    · exact (one_ne_zero h1).elim
    · simp [Finsupp.support_single_ne_zero _ h1, h]
  · have h1 : (1 : ℤ) ≠ 0 := one_ne_zero
    simp [Finsupp.support_single_ne_zero _ h1]

@[simp] theorem integrate_add (c₁ c₂ : SmoothChain I X) (ω : SmoothOneForm I X) :
    integrate (c₁ + c₂) ω = integrate c₁ ω + integrate c₂ ω := by
  classical
  unfold integrate
  -- Sum over the joint support and then split
  rw [show (c₁ + c₂).support.sum (fun γ => ((c₁ + c₂) γ : ℝ) * γ.integrate ω) =
        (c₁.support ∪ c₂.support).sum
          (fun γ => ((c₁ + c₂) γ : ℝ) * γ.integrate ω) from by
    apply Finset.sum_subset Finsupp.support_add
    intro γ _ hγ
    have : (c₁ + c₂) γ = 0 := Finsupp.notMem_support_iff.mp hγ
    rw [this]; push_cast; ring]
  rw [show c₁.support.sum (fun γ => (c₁ γ : ℝ) * γ.integrate ω) =
        (c₁.support ∪ c₂.support).sum
          (fun γ => (c₁ γ : ℝ) * γ.integrate ω) from by
    apply Finset.sum_subset (Finset.subset_union_left)
    intro γ _ hγ
    have : c₁ γ = 0 := Finsupp.notMem_support_iff.mp hγ
    rw [this]; push_cast; ring]
  rw [show c₂.support.sum (fun γ => (c₂ γ : ℝ) * γ.integrate ω) =
        (c₁.support ∪ c₂.support).sum
          (fun γ => (c₂ γ : ℝ) * γ.integrate ω) from by
    apply Finset.sum_subset (Finset.subset_union_right)
    intro γ _ hγ
    have : c₂ γ = 0 := Finsupp.notMem_support_iff.mp hγ
    rw [this]; push_cast; ring]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro γ _
  push_cast
  ring

end SmoothChain

end
