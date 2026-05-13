/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LiftDecomposition
import JacobianChallenge.Topology.RRGenusZeroFinrankChain

set_option diagnostics.threshold 100

/-! # Final composition: `RiemannRochGenusZero X` from 6 named inputs

This file ships the **maximally-compressed** closure chain for
`RiemannRochGenusZero X` after the full zz337–zz377 decomposition.

**Six named classical inputs** suffice to discharge it:

1. `RR_DimGE2_GenusZero X` — the Riemann-Roch dimension inequality
   `∃ p, 2 ≤ finrank ℂ (linearSystemDeltaP p)` at genus 0 (zz357).

2. `LiftMMeromorphicOn X` — germLimitLift preserves global meromorphy.

3. `LiftNonvanishingGerm X` — germLimitLift of a non-constant L(δp)
   member has no identically-zero germ (identity theorem content).

4. `LiftRegularContinuousAt X` — germLimitLift is ContinuousAt at
   non-pole points (local-continuity-from-analytic-continuation).

5. `LiftOrderPreserved X` — germLimitLift preserves the L(δp) order
   pattern (germ preservation).

6. `LiftNotConstant X` — germLimitLift preserves non-constancy.

Each sub-hypothesis is a separate classical statement with explicit
textbook content. Discharging all six produces unconditional
`RiemannRochGenusZero X`, which combined with zz325's chain closes
item 14's `RiemannRochGenusZero` input.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **`RiemannRochGenusZero X` from six named classical inputs.** The
maximally-compressed closure chain after the full zz337–zz377
architecture. -/
theorem riemannRochGenusZero_from_six_inputs
    [Nonempty X]
    (hRR : RR_DimGE2_GenusZero X)
    (h_mero : LiftMMeromorphicOn X)
    (h_nonvan : LiftNonvanishingGerm X)
    (h_reg_cts : LiftRegularContinuousAt X)
    (h_ord : LiftOrderPreserved X)
    (h_nc : LiftNotConstant X) :
    RiemannRochGenusZero X :=
  riemannRochGenusZero_from_RR_DimGE2_and_lifting X hRR
    (liftToMeromorphicNonzero_of_five_sub_hypotheses X h_mero h_nonvan
      h_reg_cts h_ord h_nc)

end JacobianChallenge

end
