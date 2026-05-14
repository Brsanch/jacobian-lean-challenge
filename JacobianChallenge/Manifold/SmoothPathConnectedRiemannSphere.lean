/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphere
import JacobianChallenge.Manifold.SmoothPathLinearInChart
import JacobianChallenge.Manifold.SmoothPathConcat
import JacobianChallenge.Manifold.SmoothPathConst
import JacobianChallenge.Manifold.SmoothPathConnected
import JacobianChallenge.Manifold.AbelJacobiPoint

set_option linter.unusedSectionVars false

/-! # `SmoothPathConnected 𝓘(ℝ, ℂ) RiemannSphere` — unconditional

The Riemann sphere is smoothly path-connected at the C^∞ regularity
level required by `SmoothPath` (post-2026-05-15 refactor). This is the
first complete-manifold instance of `SmoothPathConnected` discharged
end-to-end via the primitive stack:

* `SmoothPath.const` — diagonal case `p = q`.
* `SmoothPath.linearInChart` — both points in the same chart's source.
  On `RiemannSphere`, both `chartN.target = univ` and
  `chartS.target = univ`, so the "line in target" hypothesis is
  trivially discharged for either chart.
* `SmoothPath.concat` — the only edge case `{p, q} = {∞, (0 : ℂ)}`
  (the two points that no single chart covers): splice via the
  bridge point `(1 : ℂ) : RiemannSphere`, going via `chartS` from
  `∞` to `(1 : ℂ)` and via `chartN` from `(1 : ℂ)` to `(0 : ℂ)`
  (or the reverse).

The case split exhausts:

* `p = ∞ ∧ q = ∞`: constant path.
* `p ≠ ∞ ∧ q ≠ ∞`: both in `chartN.source`.
* (`p = ∞ ∨ q = ∞`) ∧ (`p ≠ (0 : ℂ) ∨ q ≠ (0 : ℂ)`)
  — at least one is ∞ and the other is not 0; use `chartS`.
* otherwise: `{p, q} = {∞, (0 : ℂ)}`. Two sub-cases by which point is
  which, both handled by `concat` via the bridge `(1 : ℂ)`.

## Downstream payoff

Via `AbelJacobiInput.nonempty_of_smoothPathConnected`
(`Manifold/SmoothPathConnected.lean`), this theorem makes the
`AbelJacobiInput α h` bundle **unconditionally nonempty on
`RiemannSphere`** for any `α` and `h` — completing the C1 input of
CLOSURE_MAP §F.3 for `X = RiemannSphere`. The full general-`X`
chart-cover argument remains a separate chip, but the present file
exercises the entire primitive stack on a concrete compact connected
complex 1-manifold.

No `sorry`, no `axiom`. -/

noncomputable section

open OnePoint Set Module
open scoped Manifold

namespace JacobianChallenge

namespace RiemannSphere

/-! ## Atlas membership of the two charts -/

/-- `chartN` is a member of the atlas of `RiemannSphere`. Direct from
the `ChartedSpace ℂ RiemannSphere` instance's `atlas = {chartN, chartS}`. -/
lemma chartN_mem_atlas : chartN ∈ atlas ℂ RiemannSphere :=
  Set.mem_insert _ _

/-- `chartS` is a member of the atlas of `RiemannSphere`. -/
lemma chartS_mem_atlas : chartS ∈ atlas ℂ RiemannSphere :=
  Set.mem_insert_of_mem _ rfl

end RiemannSphere

open RiemannSphere

/-! ## Within-chart smooth-path existence lemmas -/

/-- **Smooth path between any two finite points.** For any two points
`p, q : RiemannSphere` with `p ≠ ∞` and `q ≠ ∞`, there exists a
`SmoothPath 𝓘(ℝ, ℂ) RiemannSphere` from `p` to `q`, constructed via
`linearInChart` with the affine chart `chartN`. The "line in target"
hypothesis is trivially `Set.mem_univ` since `chartN.target = univ`. -/
lemma exists_smoothPath_chartN_source (p q : RiemannSphere)
    (hp : p ≠ ∞) (hq : q ≠ ∞) :
    ∃ γ : SmoothPath 𝓘(ℝ, ℂ) RiemannSphere, γ.src = p ∧ γ.tgt = q := by
  have hp' : p ∈ chartN.source := by rw [chartN_source]; exact hp
  have hq' : q ∈ chartN.source := by rw [chartN_source]; exact hq
  have h_line : ∀ t : ℝ,
      affineSegment (chartN p) (chartN q) t ∈ chartN.target := by
    intro t
    rw [chartN_target]
    exact Set.mem_univ _
  refine ⟨SmoothPath.linearInChart chartN chartN_mem_atlas p q hp' hq' h_line,
    ?_, ?_⟩
  · exact SmoothPath.linearInChart_src chartN chartN_mem_atlas p q hp' hq' h_line
  · exact SmoothPath.linearInChart_tgt chartN chartN_mem_atlas p q hp' hq' h_line

/-- **Smooth path between any two non-zero points.** For any two
points `p, q : RiemannSphere` with `p ≠ (0 : ℂ)` and `q ≠ (0 : ℂ)`
(both in `chartS.source = RS \ {0}`), there exists a `SmoothPath` from
`p` to `q` via `linearInChart` with `chartS`. The "line in target"
hypothesis is again trivial because `chartS.target = univ`. -/
lemma exists_smoothPath_chartS_source (p q : RiemannSphere)
    (hp : p ≠ ((0 : ℂ) : RiemannSphere))
    (hq : q ≠ ((0 : ℂ) : RiemannSphere)) :
    ∃ γ : SmoothPath 𝓘(ℝ, ℂ) RiemannSphere, γ.src = p ∧ γ.tgt = q := by
  have hp' : p ∈ chartS.source := by rw [chartS_source]; exact hp
  have hq' : q ∈ chartS.source := by rw [chartS_source]; exact hq
  have h_line : ∀ t : ℝ,
      affineSegment (chartS p) (chartS q) t ∈ chartS.target := by
    intro t
    rw [chartS_target]
    exact Set.mem_univ _
  refine ⟨SmoothPath.linearInChart chartS chartS_mem_atlas p q hp' hq' h_line,
    ?_, ?_⟩
  · exact SmoothPath.linearInChart_src chartS chartS_mem_atlas p q hp' hq' h_line
  · exact SmoothPath.linearInChart_tgt chartS chartS_mem_atlas p q hp' hq' h_line

/-! ## Auxiliary point disequalities used by the case analysis -/

private lemma one_RS_ne_zero_RS : ((1 : ℂ) : RiemannSphere) ≠ ((0 : ℂ) : RiemannSphere) := by
  intro h
  exact one_ne_zero (OnePoint.coe_injective h)

private lemma zero_RS_ne_infty : ((0 : ℂ) : RiemannSphere) ≠ ∞ :=
  OnePoint.coe_ne_infty (0 : ℂ)

private lemma one_RS_ne_infty : ((1 : ℂ) : RiemannSphere) ≠ ∞ :=
  OnePoint.coe_ne_infty (1 : ℂ)

private lemma infty_ne_zero_RS : (∞ : RiemannSphere) ≠ ((0 : ℂ) : RiemannSphere) :=
  OnePoint.infty_ne_coe (0 : ℂ)

/-! ## Main theorem -/

/-- **The Riemann sphere is smoothly path-connected.** Every two points
of `RiemannSphere` are joined by a `SmoothPath 𝓘(ℝ, ℂ) RiemannSphere`.

Case analysis:

* If `p = q`, use `SmoothPath.const`.
* If both `p, q ≠ ∞`, use `linearInChart` with `chartN`.
* If both `p, q ≠ (0 : ℂ) : RS`, use `linearInChart` with `chartS`.
* Otherwise `{p, q} = {∞, (0 : ℂ) : RS}`: splice two `linearInChart`
  paths through the bridge point `(1 : ℂ) : RS` (in `chartS.source` →
  `chartN.source`) via `SmoothPath.concat`. -/
theorem smoothPathConnected_RiemannSphere :
    SmoothPathConnected 𝓘(ℝ, ℂ) RiemannSphere := by
  intro p q
  by_cases hpN : p ≠ ∞
  · by_cases hqN : q ≠ ∞
    · -- Both ≠ ∞: chartN.
      exact exists_smoothPath_chartN_source p q hpN hqN
    · -- p ≠ ∞, q = ∞.
      push Not at hqN
      subst hqN
      by_cases hpZ : p ≠ ((0 : ℂ) : RiemannSphere)
      · -- chartS handles ∞ and any non-zero point.
        exact exists_smoothPath_chartS_source p ∞ hpZ infty_ne_zero_RS
      · -- p = (0 : ℂ) : RS, q = ∞: concat via (1 : ℂ) : RS.
        push Not at hpZ
        subst hpZ
        obtain ⟨γ, hγ_src, hγ_tgt⟩ := exists_smoothPath_chartN_source
          ((0 : ℂ) : RiemannSphere) ((1 : ℂ) : RiemannSphere)
          zero_RS_ne_infty one_RS_ne_infty
        obtain ⟨δ, hδ_src, hδ_tgt⟩ := exists_smoothPath_chartS_source
          ((1 : ℂ) : RiemannSphere) ∞
          one_RS_ne_zero_RS infty_ne_zero_RS
        have h_eq : γ.tgt = δ.src := by rw [hγ_tgt, hδ_src]
        refine ⟨γ.concat δ h_eq, ?_, ?_⟩
        · rw [SmoothPath.concat_src]; exact hγ_src
        · rw [SmoothPath.concat_tgt]; exact hδ_tgt
  · -- p = ∞.
    push Not at hpN
    subst hpN
    by_cases hq_inf : q = ∞
    · -- p = q = ∞: constant path.
      subst hq_inf
      refine ⟨SmoothPath.const _ _ ∞, ?_, ?_⟩
      · exact SmoothPath.const_src ∞
      · exact SmoothPath.const_tgt ∞
    · by_cases hqZ : q ≠ ((0 : ℂ) : RiemannSphere)
      · -- p = ∞, q ≠ (0 : ℂ) : chartS handles both.
        exact exists_smoothPath_chartS_source ∞ q infty_ne_zero_RS hqZ
      · -- p = ∞, q = (0 : ℂ) : RS: concat via (1 : ℂ) : RS.
        push Not at hqZ
        subst hqZ
        obtain ⟨γ, hγ_src, hγ_tgt⟩ := exists_smoothPath_chartS_source
          ∞ ((1 : ℂ) : RiemannSphere)
          infty_ne_zero_RS one_RS_ne_zero_RS
        obtain ⟨δ, hδ_src, hδ_tgt⟩ := exists_smoothPath_chartN_source
          ((1 : ℂ) : RiemannSphere) ((0 : ℂ) : RiemannSphere)
          one_RS_ne_infty zero_RS_ne_infty
        have h_eq : γ.tgt = δ.src := by rw [hγ_tgt, hδ_src]
        refine ⟨γ.concat δ h_eq, ?_, ?_⟩
        · rw [SmoothPath.concat_src]; exact hγ_src
        · rw [SmoothPath.concat_tgt]; exact hδ_tgt

/-! ## Discharge of `AbelJacobiInput` existence on `RiemannSphere`

Composing `smoothPathConnected_RiemannSphere` with
`AbelJacobiInput.nonempty_of_smoothPathConnected` discharges the
existence of an `AbelJacobiInput α h` bundle on the Riemann sphere
unconditionally, for any basis `α` and discreteness bundle `h`. -/

/-- **Unconditional existence of `AbelJacobiInput` on `RiemannSphere`.**
Combines `smoothPathConnected_RiemannSphere` with
`AbelJacobiInput.nonempty_of_smoothPathConnected`. -/
theorem nonempty_abelJacobiInput_RiemannSphere
    (α : Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
      (HolomorphicOneForm RiemannSphere))
    (h : PeriodLatticeDiscretenessBundle
      (PeriodPairingData.ofSmoothCycle RiemannSphere) α) :
    Nonempty (AbelJacobiInput (X := RiemannSphere) (α := α) (h := h)) :=
  AbelJacobiInput.nonempty_of_smoothPathConnected
    smoothPathConnected_RiemannSphere

end JacobianChallenge

end
