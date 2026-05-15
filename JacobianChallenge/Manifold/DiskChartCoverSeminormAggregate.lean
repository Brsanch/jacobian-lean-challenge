/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverSeminorm

set_option diagnostics.threshold 100

/-! # Seminorm on `HolomorphicOneForm X` via finset max over a `DiskChartCover`

Aggregating `DiskChartCover.localCoeffMax` over the (finite, nonempty)
base points of a `DiskChartCover X` yields the *disk-cover seminorm*:

```
DiskChartCover.seminormVal cover om := basePoints.sup' h (fun x => localCoeffMax cover x om)
```

This file proves the seminorm axioms:

* `seminormVal_nonneg`
* `seminormVal_zero`
* `seminormVal_neg`
* `seminormVal_add_le` — subadditivity
* `seminormVal_smul` — scalar homogeneity

The *separating* property (`seminormVal_eq_zero_iff_zero` under
`CompactSpace X + Nonempty X`) — which requires unwrapping the
cotangent-bundle coord-change invertibility and the cover totality —
is deferred to the chip that builds the `NormedAddCommGroup` instance
on `HolomorphicOneForm X`.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff
open Set Metric HolomorphicOneForm

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- The *disk-cover seminorm* of a holomorphic 1-form: the maximum of
`localCoeffMax` over the cover's base points (which form a nonempty
finite set whenever `X` is nonempty). -/
def seminormVal (cover : DiskChartCover X) [Nonempty X]
    (om : HolomorphicOneForm X) : ℝ :=
  cover.basePoints.sup' (cover.basePoints_nonempty)
    (fun x => localCoeffMax cover x om)

/-! ## Seminorm axioms -/

theorem seminormVal_nonneg (cover : DiskChartCover X) [Nonempty X]
    (om : HolomorphicOneForm X) :
    0 ≤ seminormVal cover om := by
  unfold seminormVal
  obtain ⟨x, hx⟩ := cover.basePoints_nonempty
  have h_le : localCoeffMax cover x om
      ≤ cover.basePoints.sup' cover.basePoints_nonempty
          (fun y => localCoeffMax cover y om) :=
    Finset.le_sup' (fun y => localCoeffMax cover y om) hx
  exact (localCoeffMax_nonneg cover om hx).trans h_le

@[simp]
theorem seminormVal_zero (cover : DiskChartCover X) [Nonempty X] :
    seminormVal cover (0 : HolomorphicOneForm X) = 0 := by
  unfold seminormVal
  -- Every entry is 0; sup' of constant 0 is 0.
  refine le_antisymm ?_ (seminormVal_nonneg cover 0)
  refine Finset.sup'_le _ _ ?_
  intro x hx
  exact (localCoeffMax_zero cover hx).le

theorem seminormVal_neg (cover : DiskChartCover X) [Nonempty X]
    (om : HolomorphicOneForm X) :
    seminormVal cover (-om) = seminormVal cover om := by
  unfold seminormVal
  exact Finset.sup'_congr cover.basePoints_nonempty rfl
    (fun x hx => localCoeffMax_neg cover om hx)

theorem seminormVal_add_le (cover : DiskChartCover X) [Nonempty X]
    (om₁ om₂ : HolomorphicOneForm X) :
    seminormVal cover (om₁ + om₂)
      ≤ seminormVal cover om₁ + seminormVal cover om₂ := by
  unfold seminormVal
  refine Finset.sup'_le _ _ ?_
  intro x hx
  have h_le := localCoeffMax_add_le cover om₁ om₂ hx
  refine h_le.trans (add_le_add ?_ ?_)
  · exact Finset.le_sup' (fun y => localCoeffMax cover y om₁) hx
  · exact Finset.le_sup' (fun y => localCoeffMax cover y om₂) hx

theorem seminormVal_smul (cover : DiskChartCover X) [Nonempty X]
    (c : ℂ) (om : HolomorphicOneForm X) :
    seminormVal cover (c • om) = ‖c‖ * seminormVal cover om := by
  unfold seminormVal
  -- Step 1: pointwise rewriting of `localCoeffMax cover x (c • om)` to
  -- `‖c‖ * localCoeffMax cover x om` (only for `x ∈ basePoints`).
  rw [show cover.basePoints.sup' cover.basePoints_nonempty
        (fun x => localCoeffMax cover x (c • om))
        = cover.basePoints.sup' cover.basePoints_nonempty
          (fun x => ‖c‖ * localCoeffMax cover x om) from
    Finset.sup'_congr cover.basePoints_nonempty rfl (fun x hx =>
      localCoeffMax_smul cover c om hx)]
  -- Step 2: `sup' (‖c‖ * f) = ‖c‖ * sup' f` via `Finset.mul₀_sup'`.
  exact (Finset.mul₀_sup' (norm_nonneg c)
    (fun x => localCoeffMax cover x om) cover.basePoints
    cover.basePoints_nonempty).symm

end DiskChartCover

end JacobianChallenge

end
