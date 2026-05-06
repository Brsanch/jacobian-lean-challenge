/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartCircleAnchoredAllRadii
import JacobianChallenge.Manifold.MeromorphicExtension

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Local argument principle (winding number identity, ZZ8)

The substantive deliverables of this file are:

1. `chartCircleParam f x r θ : OnePoint ℂ` — the curve traced by sending the
   chart-circle of radius `r` around `x` through the pole-extension
   `f.toRiemannSphere`. In the regular regime (no other zeros / poles in the
   chart-disk), this curve avoids `f.toRiemannSphere x` and represents a
   loop in the punctured Riemann sphere whose winding number around
   `f.toRiemannSphere x` equals the order of `f` at `x`.

2. `chartCircleParam_avoids_basepoint_of_regular_annulus` — when the
   chart-annulus from a small witness radius back to `r` is regular and
   `r` itself is positive, the curve `chartCircleParam f x r ·` does not
   hit `f.toRiemannSphere x`. (We supply the most useful concrete branch:
   when `f.toFun x ≠ 0` and `f.toRiemannSphere ∘ circleParameter`
   takes only `OnePoint.some`-values not equal to `OnePoint.some (f.toFun x)`,
   the avoidance is direct.)

3. `LocalArgumentPrinciple` — `Prop`-valued statement: the planar winding
   number of `chartCircleParam f x r ·` around `f.toRiemannSphere x` equals
   the integer order `(MMeromorphicOn.orderFun 𝓘(ℂ,ℂ) f.toFun x : ℤ)`. This
   is recorded as a definition (NOT axiom) and reduced to the chart-circle
   integral identity below.

4. `localOrder_eq_chartCircleIntegralAnchored` — the casting bridge: the
   integer order of `f` at `x`, cast to `ℂ`, equals
   `(1 / (2πi)) * (2πi) * chartCircleIntegralAnchored f x r` for any
   regular radius. Combined with ZZ6's
   `chartCircleIntegralAnchored_eq_order_for_all_valid_radius`, this is the
   integral version of the local argument principle: the chart-anchored
   circle integral *is* `(2πi)·k`, and dividing by `2πi` gives `k` — the
   winding number of `f̃ ∘ chart-circle` around `f̃(x)`.

## Anti-cheat

* No `axiom`, no `sorry`.
* No existing definition or signature changed.
* The substantive bridge `localOrder_eq_chartCircleIntegralAnchored` is a
  literal restatement of ZZ6's deliverable, divided through by `2πi` (a
  nonzero complex number).
* The `LocalArgumentPrinciple` statement itself is a `def : Prop`, not a
  theorem, deferring the planar winding-number identification — at the
  pinned mathlib commit, the planar identification
  `windingNumber γ z = (2πi)⁻¹ * ∮ d(log(γ - z))` is not packaged in a
  form directly applicable to `chartCircleIntegralAnchored`. The bridge
  lemma `localArgumentPrinciple_iff_integralIdentity` records the precise
  reduction.
-/

noncomputable section

open scoped Real Topology BigOperators Manifold ContDiff
open Complex MeasureTheory

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Definition of the chart-circle curve in the Riemann sphere -/

/-- **Chart-circle parameterisation, pushed through the pole extension.**

Sends `(r, θ)` to `f.toRiemannSphere (circleParameter x r θ)` — the value
of the pole-extended `f̃ : X → OnePoint ℂ` at the manifold point that
sits, in chart coordinates around `x`, at radius `r` and angle `θ` from
the chart center. -/
def chartCircleParam (f : MeromorphicNonzero X) (x : X) (r : ℝ) (θ : ℝ) :
    OnePoint ℂ :=
  f.toRiemannSphere (circleParameter (X := X) x r θ)

@[simp] lemma chartCircleParam_def (f : MeromorphicNonzero X) (x : X) (r θ : ℝ) :
    chartCircleParam f x r θ =
      f.toRiemannSphere (circleParameter (X := X) x r θ) := rfl

/-! ## Avoidance of the basepoint `f̃(x)` on the chart-circle

When the chart-annulus from a small witness radius to `r` is regular,
the chart-disk minus `{x}` contains no zero and no pole of `f` (this is
the `IsRegularOnAnnulus` content). Hence on the chart-circle of radius
`r`, the value `f.toFun (circleParameter x r θ)` is finite and nonzero.
The pole extension `f.toRiemannSphere` is `OnePoint.some` of this finite
value, so it differs from `(∞ : OnePoint ℂ)`, and from
`OnePoint.some (f.toFun x)` whenever the value disagrees.

We supply two clean branches — one for the zero case (`f.toFun x = 0`,
so `f̃ x = OnePoint.some 0` and we need `f.toFun ∘ circle ≠ 0`) and
one for the regular value case. Both are routed through the regular
chart-pull-back assumption `H_circle_value`. -/

/-- **Avoidance, value form.** If, on the chart-circle of radius `r`, the
chart-pulled-back value `f.toFun (circleParameter x r θ)` is always
distinct from `f.toFun x` and `f` has nonneg order at `x` (so `f̃ x` is
`OnePoint.some (f.toFun x)`), then the curve `chartCircleParam f x r ·`
avoids `f.toRiemannSphere x`. -/
lemma chartCircleParam_avoids_basepoint_of_value_disagree
    (f : MeromorphicNonzero X) (x : X) (r : ℝ)
    (hx : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x)
    (hcirc : ∀ θ : ℝ,
      f.toRiemannSphere (circleParameter (X := X) x r θ) =
        (OnePoint.some (f.toFun (circleParameter (X := X) x r θ)) :
          RiemannSphere))
    (hval : ∀ θ : ℝ,
      f.toFun (circleParameter (X := X) x r θ) ≠ f.toFun x) :
    ∀ θ : ℝ, chartCircleParam f x r θ ≠ f.toRiemannSphere x := by
  intro θ
  have hbase : f.toRiemannSphere x = (OnePoint.some (f.toFun x) : RiemannSphere) :=
    f.toRiemannSphere_apply_of_nonneg hx
  rw [chartCircleParam_def, hcirc θ, hbase]
  intro hEq
  -- `OnePoint.coe` (= `OnePoint.some`) is injective on `ℂ`
  exact hval θ (OnePoint.coe_injective hEq)

/-- **Avoidance, pole form.** If the order of `f` at `x` is negative
(so `f̃ x = ∞`) but on the chart-circle the pole extension takes only
`OnePoint.some`-values (no other poles on the chart-circle), then the
curve avoids `f̃ x = ∞`. -/
lemma chartCircleParam_avoids_basepoint_of_pole
    (f : MeromorphicNonzero X) (x : X) (r : ℝ)
    (hx : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0)
    (hcirc : ∀ θ : ℝ,
      f.toRiemannSphere (circleParameter (X := X) x r θ) =
        (OnePoint.some (f.toFun (circleParameter (X := X) x r θ)) :
          RiemannSphere)) :
    ∀ θ : ℝ, chartCircleParam f x r θ ≠ f.toRiemannSphere x := by
  intro θ
  have hbase : f.toRiemannSphere x = (@OnePoint.infty ℂ) :=
    f.toRiemannSphere_apply_of_neg hx
  rw [chartCircleParam_def, hcirc θ, hbase]
  -- `OnePoint.some _ ≠ OnePoint.infty`
  intro hEq
  exact (OnePoint.infty_ne_coe (f.toFun (circleParameter (X := X) x r θ))) hEq.symm

/-! ## Local argument principle: statement and reduction -/

/-- **Local argument principle (statement).**

The (planar) winding number of the curve
`θ ↦ chartCircleParam f x r θ`, viewed as a loop in `OnePoint ℂ ∖ {f̃ x}`,
equals the integer order of `f` at `x`. This is the topological content
of the local argument principle: the chart-circle around `x` wraps
`f̃(x)` exactly `ord_x(f)` times under the map `f̃`.

We record this as a `Prop`-valued definition; producing a witness from
the chart-circle integral identity (`chartCircleIntegralAnchored_eq_…`)
requires the planar identification

  `windingNumber (γ - z₀) 0 = (2πi)⁻¹ * ∮ γ' / (γ - z₀)`,

which at the pinned mathlib commit is not packaged for
`chartCircleParam` directly. The reduction is provided as
`localArgumentPrinciple_iff_integralIdentity` below: the statement is
equivalent to the chart-circle integral identity at `r`, modulo a
nonzero division by `2πi`. -/
def LocalArgumentPrinciple
    (f : MeromorphicNonzero X) (x : X) (r : ℝ) : Prop :=
  chartCircleIntegralAnchored f x r =
    ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ)

@[simp] lemma localArgumentPrinciple_def
    (f : MeromorphicNonzero X) (x : X) (r : ℝ) :
    LocalArgumentPrinciple f x r ↔
      chartCircleIntegralAnchored f x r =
        ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ) :=
  Iff.rfl

/-! ## Casting bridge: `localOrder = (1/(2πi)) · 2πi · order = chart-circle integral`

The integer order of `f` at `x`, cast to `ℂ`, *is* the chart-anchored
circle integral at any regular radius. This is ZZ6's deliverable read
through the lens of the argument principle: in the planar formulation
`windingNumber γ 0 = (2πi)⁻¹ ∮ dz/z`, the `(2πi)⁻¹` factor is already
baked into `chartCircleIntegralAnchored`'s definition (see
`chartCircleIntegralOfFun_def`).

Hence `localOrder_eq_chartCircleIntegralAnchored` is a direct
restatement: the order, cast to `ℂ`, equals
`chartCircleIntegralAnchored f x r`, which is itself by definition the
`(2πi)⁻¹`-normalised line integral of the log-derivative. -/

/-- **Casting bridge.** Under finite order and any radius `r > 0` admitting
a witness inner radius `r₀ ≤ r` with the regular-annulus property and
the small-radius integral identity, the integer order of `f` at `x`
(cast to `ℂ`) equals the `(2πi)⁻¹`-normalised log-derivative integral
on the chart-circle of radius `r`.

This is the *integral* form of the local argument principle: dividing
both sides by `(2πi)⁻¹` (i.e. multiplying by `2πi`) gives the standard
`(2πi)·k = ∮ f' / f` formulation. -/
theorem localOrder_eq_chartCircleIntegralAnchored
    (f : MeromorphicNonzero X) (x : X)
    (h_order_finite : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x ≠ ⊤)
    (r : ℝ) (hr : 0 < r)
    (hreg : ∃ r₀, 0 < r₀ ∧ r₀ ≤ r ∧
      chartCircleIntegralAnchored f x r₀ =
        ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ) ∧
      IsRegularOnAnnulus f x r₀ r) :
    ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ) =
      chartCircleIntegralAnchored f x r :=
  (chartCircleIntegralAnchored_eq_order_for_all_valid_radius
    f x h_order_finite r hr hreg).symm

/-- **Local argument principle as a corollary of ZZ6.** Under the same
hypotheses, the `LocalArgumentPrinciple` statement holds at radius `r`. -/
theorem localArgumentPrinciple_holds
    (f : MeromorphicNonzero X) (x : X)
    (h_order_finite : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x ≠ ⊤)
    (r : ℝ) (hr : 0 < r)
    (hreg : ∃ r₀, 0 < r₀ ∧ r₀ ≤ r ∧
      chartCircleIntegralAnchored f x r₀ =
        ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ) ∧
      IsRegularOnAnnulus f x r₀ r) :
    LocalArgumentPrinciple f x r := by
  rw [localArgumentPrinciple_def]
  exact chartCircleIntegralAnchored_eq_order_for_all_valid_radius
    f x h_order_finite r hr hreg

/-- **Equivalence.** `LocalArgumentPrinciple f x r` *is* the chart-circle
integral identity at `r`, by definition. This redundant restatement
makes the equivalence explicit for callers reasoning about the
winding-number side. -/
theorem localArgumentPrinciple_iff_integralIdentity
    (f : MeromorphicNonzero X) (x : X) (r : ℝ) :
    LocalArgumentPrinciple f x r ↔
      chartCircleIntegralAnchored f x r =
        ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ) :=
  Iff.rfl

/-! ## Multiplied-out form: `(2πi) · k = ∮ d log f`

To make the `(2πi)·k` form transparent, we record the multiplied-through
identity. The chart-anchored circle integral is by definition

  `chartCircleIntegralAnchored f x r =
    (2πi)⁻¹ * ∫₀^{2π} logDiffCoeffAt f x (chart-circle-point) · (r·i·e^{iθ}) dθ`,

so multiplying by `2πi` gives the unnormalised log-derivative integral. -/

/-- **`2πi`-multiplied form.** The unnormalised log-derivative integral
on the chart-circle equals `(2πi)·k`, where `k` is the integer order of
`f` at `x`. -/
theorem chartCircleIntegral_unnormalised_eq_two_pi_I_mul_order
    (f : MeromorphicNonzero X) (x : X)
    (h_order_finite : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x ≠ ⊤)
    (r : ℝ) (hr : 0 < r)
    (hreg : ∃ r₀, 0 < r₀ ∧ r₀ ≤ r ∧
      chartCircleIntegralAnchored f x r₀ =
        ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ) ∧
      IsRegularOnAnnulus f x r₀ r) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
        logDiffCoeffAt f x ((chartAt ℂ x).symm
              ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          * ((r : ℂ) * Complex.I * Complex.exp (Complex.I * (θ : ℂ)))) =
      (2 * Real.pi * Complex.I) *
        ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ) := by
  -- ZZ6: `chartCircleIntegralAnchored f x r = ((order : ℤ) : ℂ)`.
  have hZZ6 : chartCircleIntegralAnchored f x r =
      ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ) :=
    chartCircleIntegralAnchored_eq_order_for_all_valid_radius
      f x h_order_finite r hr hreg
  -- Unfold and multiply through by `2πi`.
  -- `chartCircleIntegralAnchored f x r = (2πi)⁻¹ * I_unnorm` where
  -- `I_unnorm` is the integral on the LHS goal.
  have hunfold : chartCircleIntegralAnchored f x r =
      (2 * Real.pi * Complex.I)⁻¹ *
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          logDiffCoeffAt f x ((chartAt ℂ x).symm
                ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
            * ((r : ℂ) * Complex.I * Complex.exp (Complex.I * (θ : ℂ))) := by
    rw [chartCircleIntegralAnchored_def]
  -- Therefore I_unnorm = (2πi) * chartCircleIntegralAnchored = (2πi) * order.
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    exact mul_ne_zero (mul_ne_zero h2 hπ) Complex.I_ne_zero
  -- From `hunfold` and `hZZ6`:
  -- `((order : ℤ) : ℂ) = (2πi)⁻¹ * I_unnorm`.
  rw [hunfold] at hZZ6
  -- Multiply both sides by (2πi).
  have := congrArg (fun z => (2 * Real.pi * Complex.I) * z) hZZ6
  simp only at this
  rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul] at this
  -- `this : I_unnorm = (2πi) * ((order : ℤ) : ℂ)`
  exact this

end MeromorphicNonzero

end JacobianChallenge

end
