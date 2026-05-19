/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusChartLiftOnSubinterval

set_option linter.unusedSectionVars false

/-! # Two chart-symm values at the same torus point differ by a lattice element

For any two anchors `x_a, x_b : ℂ` and a point `q : ℂ ⧸ L` in **both**
chart sources, the chart-symm values are different complex preimages
of `q`, hence differ by an element of `L`:

  `(localChart L _ x_a).symm q - (localChart L _ x_b).symm q ∈ L`.

This is the seam consistency identity that pieces together the
per-sub-interval chart-symm smooth lifts into a globally consistent
smooth lift via cumulative lattice shifts.

## What this file ships

* `ComplexTorus.chart_symm_diff_mem_L` — the seam lattice-difference
  identity.

* `ComplexTorus.mkQ_chart_symm` — `mkQ ((chart).symm q) = q` for `q`
  in the chart-symm.source (re-exported from the chart's `right_inv`).

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **mkQ-roundtrip**: the chart-symm followed by mkQ gives back the
torus point. -/
theorem mkQ_chart_symm (x : ℂ) {q : ℂ ⧸ L}
    (h_q : q ∈ (localChart L (discRadius_separates L) x).symm.source) :
    L.mkQ ((localChart L (discRadius_separates L) x).symm q) = q :=
  (localChart L (discRadius_separates L) x).right_inv h_q

/-- **Seam lattice-difference identity.** For any `q : ℂ ⧸ L` in both
chart sources at anchors `x_a` and `x_b`, the chart-symm values differ
by a lattice element. -/
theorem chart_symm_diff_mem_L (x_a x_b : ℂ) {q : ℂ ⧸ L}
    (h_a : q ∈ (localChart L (discRadius_separates L) x_a).symm.source)
    (h_b : q ∈ (localChart L (discRadius_separates L) x_b).symm.source) :
    (localChart L (discRadius_separates L) x_a).symm q -
      (localChart L (discRadius_separates L) x_b).symm q ∈ L := by
  -- mkQ ((chart_a).symm q) = q = mkQ ((chart_b).symm q).
  have h_mkQ_a : L.mkQ ((localChart L (discRadius_separates L) x_a).symm q) = q :=
    mkQ_chart_symm L x_a h_a
  have h_mkQ_b : L.mkQ ((localChart L (discRadius_separates L) x_b).symm q) = q :=
    mkQ_chart_symm L x_b h_b
  -- mkQ (a - b) = mkQ a - mkQ b = q - q = 0.
  have h_diff : L.mkQ ((localChart L (discRadius_separates L) x_a).symm q -
      (localChart L (discRadius_separates L) x_b).symm q) = 0 := by
    rw [map_sub, h_mkQ_a, h_mkQ_b, sub_self]
  -- mkQ x = 0 ↔ x ∈ L (kernel of mkQ).
  exact (Submodule.Quotient.mk_eq_zero L).mp h_diff

end ComplexTorus

end JacobianChallenge

end
