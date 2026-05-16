/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.IntegrandContinuousAlongBetaUnconditional
import JacobianChallenge.Manifold.IntegrateLevelSetChainSigmaReparam
import JacobianChallenge.Manifold.MeromorphicNonzeroConcreteLevelSetChain
import JacobianChallenge.Manifold.AbelLatticeWitnessFromRegular
import JacobianChallenge.Manifold.AbelJacobiPath
import JacobianChallenge.Manifold.HolomorphicOneFormRealComponent
import JacobianChallenge.Manifold.ComplexPeriodPairing

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `RegularLevelSetLatticeClause` from holomorphic-trace vanishing

For `α : HolomorphicOneForm X` on a compact connected Riemann surface,
the trace `f_*α` is a holomorphic 1-form on `ℙ¹`. Since
`Subsingleton (HolomorphicOneForm RiemannSphere)` (genus zero, in
tree), `f_*α = 0`. Equivalently, the pointwise trace
`f.traceAt hnc hv ω` of the realified components of `α` vanishes at
every regular value `v`.

This file ships:

* `TraceAtVanishesOnHolomorphic X` — the named hypothesis: for every
  non-constant `f`, every `α : HolomorphicOneForm X`, and every regular
  value `v`, both `f.traceAt hnc hv (realComponent α)` and
  `f.traceAt hnc hv (imagComponent α)` vanish as cotangent vectors at
  `v`. (This is the irreducible analytic content — the n-th-root
  cancellation + removable singularity at critical values +
  `HolomorphicOneForm ℙ¹ = 0` chain.)

* `regularLevelSetLatticeClause_of_traceVanishing` — conditional
  discharge: given `TraceAtVanishesOnHolomorphic X`,
  `RegularLevelSetLatticeClause X α h` holds.

The discharge composes:
* Today's `integrate_levelSetChain_eq_traceAt_lineIntegral` (σ-1 chip,
  now unconditional via `IntegrandContinuousAlongBeta_holds`).
* `regularBeta_regular`: the canonical path `regularBeta` stays in
  `regularValueSet`.
* `applyCotangent_zero`: `applyCotangent 0 v = 0`.
* Definition of `complexChainPeriod` as a real-imag split.

No `sorry`, no `axiom`. -/

noncomputable section

open Set
open scoped Manifold ContDiff Topology
open Module

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] [PreconnectedSpace X] [Nonempty X]

/-- **Holomorphic-trace vanishing on the regular set.**

For every non-constant `f : MeromorphicNonzero X`, every
`α : HolomorphicOneForm X`, and every regular value `v ∈ f.regularValueSet`,
both the real and imaginary components of `α` have trace zero at `v`:

```
f.traceAt hnc hv (realComponent α) = 0
f.traceAt hnc hv (imagComponent α) = 0
```

This is the *irreducible* analytic content of Abel forward at the
regular-case lattice clause: the trace map
`HolomorphicOneForm X → HolomorphicOneForm RiemannSphere` (defined via
the n-th-root cancellation at critical values + Riemann's removable
singularity theorem) lands in a subsingleton group
(`Subsingleton (HolomorphicOneForm RiemannSphere)`, in tree), so the
trace vanishes globally — in particular, at every regular `v`. -/
def TraceAtVanishesOnHolomorphic (X : Type*)
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] [PreconnectedSpace X] [Nonempty X] : Prop :=
  ∀ (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (α : HolomorphicOneForm X)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet),
      f.traceAt hnc hv (realComponent α) = 0 ∧
      f.traceAt hnc hv (imagComponent α) = 0

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α}

/-- **Helper: the line-integral form of `∫_Z (one-form)` vanishes when
the trace vanishes pointwise along `β`.** -/
private lemma integrate_levelSetChain_realComp_eq_zero
    [DecidableEq X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (h0_reg : (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet)
    (h_inf_reg : (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet)
    (omForm : SmoothOneForm 𝓘(ℝ, ℂ) X)
    (h_vanish :
      ∀ s : ℝ, ∀ hs_reg : f.regularBeta hnc h0_reg h_inf_reg s ∈ f.regularValueSet,
        f.traceAt hnc hs_reg omForm = 0) :
    SmoothChain.integrate (f.regularLevelSetChain hnc h0_reg h_inf_reg) omForm = 0 := by
  classical
  -- Unfold regularLevelSetChain to levelSetChain f β.
  unfold MeromorphicNonzero.regularLevelSetChain
  -- Use today's σ-1 chip, now unconditional via integrandContinuousAlongBeta_holds.
  rw [f.integrate_levelSetChain_eq_traceAt_lineIntegral hnc
        (f.regularBeta_smooth hnc h0_reg h_inf_reg)
        (f.regularBeta_regular hnc h0_reg h_inf_reg)
        omForm
        (f.integrandContinuousAlongBeta_holds hnc
          (f.regularBeta_smooth hnc h0_reg h_inf_reg)
          (f.regularBeta_regular hnc h0_reg h_inf_reg)
          omForm)]
  -- The integrand vanishes pointwise on Icc 0 1.
  rw [show (∫ s in (0 : ℝ)..1,
              (if hs : s ∈ Icc (0 : ℝ) 1 then
                SmoothPath.applyCotangent
                  (f.traceAt hnc
                    (f.regularBeta_regular hnc h0_reg h_inf_reg s hs) omForm)
                  ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
                      (f.regularBeta hnc h0_reg h_inf_reg) s :
                      ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℂ)
                        (f.regularBeta hnc h0_reg h_inf_reg s)) (1 : ℝ))
              else (0 : ℝ)))
        = (∫ s in (0 : ℝ)..1, (0 : ℝ)) from ?_]
  · exact intervalIntegral.integral_zero
  -- Pointwise vanishing.
  apply intervalIntegral.integral_congr
  intro s hs
  by_cases hs_in : s ∈ Icc (0 : ℝ) 1
  · simp only [dif_pos hs_in]
    rw [h_vanish s (f.regularBeta_regular hnc h0_reg h_inf_reg s hs_in)]
    -- applyCotangent 0 _ = 0.
    exact SmoothPath.applyCotangent_zero _
  · simp only [dif_neg hs_in]

/-- **Main reduction.** Given the holomorphic-trace vanishing
hypothesis, the regular-case lattice clause holds. -/
theorem regularLevelSetLatticeClause_of_traceVanishing
    [DecidableEq X]
    (hTrace : TraceAtVanishesOnHolomorphic X) :
    RegularLevelSetLatticeClause X α h := by
  intro f hnc h0_reg h_inf_reg
  -- Show `complexChainPeriodVector α (regularLevelSetChain) = 0`.
  have h_pv_zero : complexChainPeriodVector α
      (f.regularLevelSetChain hnc h0_reg h_inf_reg)
        = (0 : Fin (JacobianChallenge.genus X) → ℂ) := by
    funext i
    show complexChainPeriod (f.regularLevelSetChain hnc h0_reg h_inf_reg) (α i) = 0
    unfold complexChainPeriod
    -- Both real and imag parts of the chain integral vanish.
    have h_real :
        SmoothChain.integrate (f.regularLevelSetChain hnc h0_reg h_inf_reg)
          (realComponent (α i)) = 0 := by
      refine integrate_levelSetChain_realComp_eq_zero f hnc h0_reg h_inf_reg
        (realComponent (α i)) ?_
      intro s hs_reg
      exact (hTrace f hnc (α i) hs_reg).1
    have h_imag :
        SmoothChain.integrate (f.regularLevelSetChain hnc h0_reg h_inf_reg)
          (imagComponent (α i)) = 0 := by
      refine integrate_levelSetChain_realComp_eq_zero f hnc h0_reg h_inf_reg
        (imagComponent (α i)) ?_
      intro s hs_reg
      exact (hTrace f hnc (α i) hs_reg).2
    rw [h_real, h_imag]
    push_cast
    ring
  -- 0 ∈ any subgroup.
  rw [h_pv_zero]
  exact zero_mem _

end JacobianChallenge

end
