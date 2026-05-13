/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Analytic.Inverse
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

set_option diagnostics.threshold 100

/-! # Analytic reciprocal extension at a simple pole

If `f : ℂ → ℂ` is meromorphic at `z₀` with order exactly `-1`, this
file builds an analytic-at-`z₀` extension `h` of `1/f` characterized
by:

* `h(z₀) = 0`,
* `deriv h z₀ ≠ 0`,
* `h(z) = 1/f(z)` for `z` in a punctured neighbourhood of `z₀`.

The construction is direct from mathlib's
`meromorphicOrderAt_eq_int_iff`: at order `-1` the lemma supplies
analytic `g` with `g(z₀) ≠ 0` and `f(z) = g(z) / (z - z₀)` near
`z₀ ≠ z`. Then `(z - z₀)/g(z)` is the desired analytic-at-`z₀`
extension; mathlib's analytic-quotient lemma gives analyticity since
`g(z₀) ≠ 0`.

This is the *complex-analytic* core of the regularity-at-simple-pole
classical input named `ChartPullback_Deriv_AtSimplePole_NeZero`
(zz340) / `UniformSimplePoleRegularity` (zz342). The chart-pullback
wiring on top is a separate downstream chip.

No `sorry`, no `axiom`.
-/

noncomputable section

open Filter Topology

namespace JacobianChallenge

namespace SimplePole

variable {f : ℂ → ℂ} {z₀ : ℂ}

/-- **Existence of the analytic-witness `g` at a simple pole.** At
order `-1`, `f = g/(z - z₀)` near `z₀`, with `g` analytic and
`g(z₀) ≠ 0`. Pure mathlib re-statement. -/
lemma exists_analytic_witness_at_simple_pole
    (hf : MeromorphicAt f z₀)
    (h_ord : meromorphicOrderAt f z₀ = ((-1 : ℤ) : WithTop ℤ)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] z₀, f z = (z - z₀) ^ (-1 : ℤ) • g z := by
  exact (meromorphicOrderAt_eq_int_iff hf).mp h_ord

/-- **The analytic-reciprocal candidate** at a simple pole, given the
witness `g` from `exists_analytic_witness_at_simple_pole`. -/
def candidate (z₀ : ℂ) (g : ℂ → ℂ) : ℂ → ℂ :=
  fun z => (z - z₀) / g z

/-- **`candidate` is analytic at `z₀`** when `g` is analytic and
`g(z₀) ≠ 0`. -/
lemma candidate_analyticAt {g : ℂ → ℂ}
    (hg_an : AnalyticAt ℂ g z₀) (hg_ne : g z₀ ≠ 0) :
    AnalyticAt ℂ (candidate z₀ g) z₀ := by
  unfold candidate
  refine AnalyticAt.div ?_ hg_an hg_ne
  -- `z ↦ z - z₀` is analytic.
  exact analyticAt_id.sub analyticAt_const

/-- **`candidate z₀` at `z₀` is zero**. -/
@[simp] lemma candidate_at_zero (z₀ : ℂ) (g : ℂ → ℂ) :
    candidate z₀ g z₀ = 0 := by
  unfold candidate
  simp

/-- **Derivative of `candidate` at `z₀`** is `1 / g(z₀)`. -/
lemma deriv_candidate_at_zero {g : ℂ → ℂ}
    (hg_an : AnalyticAt ℂ g z₀) (hg_ne : g z₀ ≠ 0) :
    deriv (candidate z₀ g) z₀ = 1 / g z₀ := by
  unfold candidate
  -- Numerator `z - z₀` has derivative 1 at z₀.
  have h_num_hda : HasDerivAt (fun z : ℂ => z - z₀) 1 z₀ :=
    (hasDerivAt_id z₀).sub_const _
  -- Denominator `g` has its derivative at z₀.
  have h_den_hda : HasDerivAt g (deriv g z₀) z₀ :=
    hg_an.differentiableAt.hasDerivAt
  -- Quotient rule (pointwise form).
  have h_div_hda :
      HasDerivAt (fun z : ℂ => (z - z₀) / g z)
        ((1 * g z₀ - (z₀ - z₀) * deriv g z₀) / g z₀ ^ 2) z₀ :=
    h_num_hda.fun_div h_den_hda hg_ne
  -- Simplify the derivative value.
  have h_simpl :
      (1 * g z₀ - (z₀ - z₀) * deriv g z₀) / g z₀ ^ 2 = 1 / g z₀ := by
    rw [sub_self, zero_mul, sub_zero, one_mul, pow_two]
    field_simp
  rw [h_simpl] at h_div_hda
  exact h_div_hda.deriv

/-- **`deriv (candidate z₀ g) z₀ ≠ 0`** when `g(z₀) ≠ 0`. -/
lemma deriv_candidate_ne_zero {g : ℂ → ℂ}
    (hg_an : AnalyticAt ℂ g z₀) (hg_ne : g z₀ ≠ 0) :
    deriv (candidate z₀ g) z₀ ≠ 0 := by
  rw [deriv_candidate_at_zero hg_an hg_ne]
  exact one_div_ne_zero hg_ne

/-- **Eventually-equal characterization of `1/f` via `candidate`.**
On `𝓝[≠] z₀`, `1/f(z) = (z - z₀)/g(z) = candidate z₀ g z`. -/
lemma one_div_f_eventuallyEq_candidate
    {g : ℂ → ℂ}
    (hg_an : AnalyticAt ℂ g z₀) (hg_ne : g z₀ ≠ 0)
    (hf_eq : ∀ᶠ z in 𝓝[≠] z₀, f z = (z - z₀) ^ (-1 : ℤ) • g z) :
    (fun z => 1 / f z) =ᶠ[𝓝[≠] z₀] candidate z₀ g := by
  -- `g` is continuous at `z₀` and `g z₀ ≠ 0`, so `g z ≠ 0` eventually.
  have hg_ne_nhd : ∀ᶠ z in 𝓝 z₀, g z ≠ 0 :=
    (hg_an.continuousAt).eventually_ne hg_ne
  have hg_ne_punctured : ∀ᶠ z in 𝓝[≠] z₀, g z ≠ 0 :=
    nhdsWithin_le_nhds hg_ne_nhd
  filter_upwards [hf_eq, hg_ne_punctured, self_mem_nhdsWithin]
    with z hf_z hg_z hz_ne
  -- `z ≠ z₀`, so `z - z₀ ≠ 0`.
  have hz_sub_ne : z - z₀ ≠ 0 := sub_ne_zero_of_ne hz_ne
  -- LHS = 1 / f z; substitute hf_z.
  rw [hf_z]
  -- Now: 1 / ((z - z₀)^(-1) • g z) = candidate z₀ g z = (z - z₀)/g z.
  rw [zpow_neg, zpow_one, smul_eq_mul]
  unfold candidate
  field_simp

end SimplePole

end JacobianChallenge

end
