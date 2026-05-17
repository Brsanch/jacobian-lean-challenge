/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverDensityIdentity

set_option linter.unusedSectionVars false

/-! # Pointwise density bound from the localCoeff transition identity

Direct norm consequence of `localCoeff_transition`:

```
‖localCoeff om x ((chartAt x) q)‖
  ≤ ‖transitionFactor x y q‖ * ‖localCoeff om y ((chartAt y) q)‖
```

for `q ∈ (chartAt ℂ x).source ∩ (chartAt ℂ y).source`, with equality
because the identity is exact (multiplication, not just a bound). This
chip ships both the equation and the inequality (which is the form most
useful for convergence arguments).

For convergence: applied to `om := om_n - om_lim`, the inequality gives
that uniform convergence of `localCoeff om_n y` on the chart-`y` inner
disk transfers to uniform convergence of `localCoeff om_n x` on the
chart-`x` outer disk, provided `‖transitionFactor x y ·‖` is uniformly
bounded on the relevant compact set (the next chip).

No `sorry`, no `axiom`.
-/

open Set Metric

open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **Norm form of `localCoeff_transition`.** -/
theorem norm_localCoeff_eq
    (om : HolomorphicOneForm X) {x y q : X}
    (hq_x : q ∈ (chartAt ℂ x).source)
    (hq_y : q ∈ (chartAt ℂ y).source) :
    ‖HolomorphicOneForm.localCoeff om x ((chartAt ℂ x) q)‖
      = ‖transitionFactor x y q‖
        * ‖HolomorphicOneForm.localCoeff om y ((chartAt ℂ y) q)‖ := by
  rw [localCoeff_transition om hq_x hq_y, norm_mul]

/-- **Pointwise density bound** (inequality form, useful for convergence). -/
theorem norm_localCoeff_le
    (om : HolomorphicOneForm X) {x y q : X}
    (hq_x : q ∈ (chartAt ℂ x).source)
    (hq_y : q ∈ (chartAt ℂ y).source) :
    ‖HolomorphicOneForm.localCoeff om x ((chartAt ℂ x) q)‖
      ≤ ‖transitionFactor x y q‖
        * ‖HolomorphicOneForm.localCoeff om y ((chartAt ℂ y) q)‖ :=
  le_of_eq (norm_localCoeff_eq om hq_x hq_y)

end DiskChartCover

end JacobianChallenge

end
