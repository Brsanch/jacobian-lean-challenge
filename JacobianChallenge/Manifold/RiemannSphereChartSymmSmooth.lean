/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphereRealManifold

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Smoothness of `chartN.symm` and `chartS.symm` in the real model `𝓘(ℝ, ℂ)`

Specializations of mathlib's `contMDiffOn_chart_symm` to the two RS
charts, viewed as smooth manifold maps with model `𝓘(ℝ, ℂ)`.

Since `chartN.target = chartS.target = univ`, the smoothness on the
target is the same as global smoothness:

```
ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤ chartN.symm.
ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤ chartS.symm.
```

These are the prerequisites for chart-based loop factorisation:
every smooth loop on `RS` lying in `chartN.source` (resp. `chartS.source`)
can be pushed via `chartN.symm` (resp. `chartS.symm`) from a smooth
loop in `ℂ`.

## What this file ships

* `chartN_symm_contMDiff` — global C^∞ smoothness of `chartN.symm` at
  real regularity `⊤`.
* `chartS_symm_contMDiff` — symmetric.

No `sorry`, no `axiom`. -/

open Set
open scoped Manifold Topology ContDiff

namespace JacobianChallenge

namespace RiemannSphere

/-! ## `chartN.symm` is C^∞ on all of `ℂ` -/

/-- `chartN.symm : ℂ → RS` is `ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤` globally,
i.e., as a manifold map at real regularity `⊤`.

Proof: `chartN = chartAt ℂ ((0 : ℂ) : RS)` (since `chartAt'` selects
`chartN` for any finite point), so `contMDiffOn_chart_symm` applies on
`chartN.target = univ`, which equals global `ContMDiff` smoothness. -/
theorem chartN_symm_contMDiff :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤ (chartN.symm : ℂ → RiemannSphere) := by
  -- `chartAt ℂ ((0 : ℂ) : RS) = chartN` via `chartAt'_coe`.
  have h_chart_eq : chartAt ℂ ((0 : ℂ) : RiemannSphere) = chartN :=
    chartAt'_coe 0
  -- Mathlib's chart-symm smoothness on the target.
  have h_on : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤
      (chartAt ℂ ((0 : ℂ) : RiemannSphere)).symm
      (chartAt ℂ ((0 : ℂ) : RiemannSphere)).target :=
    contMDiffOn_chart_symm
  rw [h_chart_eq] at h_on
  -- chartN.target = univ.
  rw [chartN_target] at h_on
  -- Smooth on univ ⇔ smooth globally.
  exact contMDiffOn_univ.mp h_on

/-! ## `chartS.symm` is C^∞ on all of `ℂ` -/

/-- `chartS.symm : ℂ → RS` is `ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤` globally. -/
theorem chartS_symm_contMDiff :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤ (chartS.symm : ℂ → RiemannSphere) := by
  -- `chartAt ℂ ∞ = chartS` via `chartAt'_infty`.
  have h_chart_eq :
      chartAt ℂ ((OnePoint.infty : RiemannSphere)) = chartS :=
    chartAt'_infty
  have h_on : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤
      (chartAt ℂ (OnePoint.infty : RiemannSphere)).symm
      (chartAt ℂ (OnePoint.infty : RiemannSphere)).target :=
    contMDiffOn_chart_symm
  rw [h_chart_eq] at h_on
  rw [chartS_target] at h_on
  exact contMDiffOn_univ.mp h_on

end RiemannSphere

end JacobianChallenge
