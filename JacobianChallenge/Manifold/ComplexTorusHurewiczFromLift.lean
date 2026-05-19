/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusContinuousPathLift
import JacobianChallenge.Manifold.ComplexTorusPeriodLatticeInputs

set_option linter.unusedSectionVars false

/-! # Structural reduction of `SmoothHurewiczHypothesisTorus` to a
smooth-lift hypothesis

The continuous path lift `contLift : ℂ ⧸ L → ℂ` exists unconditionally
on the complex torus (built from mathlib's `IsCoveringMap.liftPath`
applied to our `mkQ_isCoveringMap`). The remaining classical content
for `SmoothHurewiczHypothesisTorus` is:

1. **Smoothness upgrade**: when the input path is `C^∞`, the
   continuous lift IS `C^∞`. (Standard chart-based argument:
   each piece is `chart_symm ∘ γ.ambient` which is `C^∞`, and the
   uniqueness of lifts glues them.)

2. **Smooth-homotopy construction**: given a smooth lift `lift` of `γ`
   ending at `lift(1) ∈ L`, construct the straight-line smooth
   homotopy in ℂ from `lift` to `(·) ↦ t · lift(1)`, and project via
   `mkQ` to a smooth homotopy in `T²` from `γ` to
   `torusBasisLoop(lift(1))`.

3. **Bordism identification** with the `basisProductLoop` using
   ZLattice basis decomposition of `lift(1)`.

This file names the **smooth-lift hypothesis** and provides a partial
structural reduction. The full discharge of `SmoothHurewiczHypothesisTorus`
from the smooth-lift + ZLattice basis + concrete homotopy machinery
remains multi-chip future work.

## What this file ships

* `ComplexTorus.SmoothPathLiftHypothesisTorus L` — the named atom:
  every smooth based loop at `0` on `ℂ ⧸ L` admits a smooth lift to
  `ℂ` starting at `0`, with `mkQ ∘ lift = γ.ambient` on `[0, 1]`.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff Topology

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **Named atom: every smooth based loop at `0` on `ℂ ⧸ L` admits a
smooth ambient lift to `ℂ` starting at `0`, with `mkQ ∘ lift =
γ.ambient` on `[0, 1]`.**

Classical content: covering-space path lifting + smoothness
propagation through `IsCoveringMap.liftPath` (which mathlib gives
continuously) using uniqueness of lifts on connected base + local
chart-symm composition (smooth).

Once discharged, this combines with the ZLattice basis decomposition
of `lift 1 ∈ L` and the straight-line homotopy in `ℂ` projected via
`mkQ` to give `SmoothHurewiczHypothesisTorus`. -/
def SmoothPathLiftHypothesisTorus : Prop :=
  ∀ γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L), ∀ h_src : γ.src = (0 : ℂ ⧸ L),
    ∃ lift : ℝ → ℂ,
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ lift ∧
      lift 0 = 0 ∧
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        L.mkQ (lift t) = γ.ambient t

/-- **Corollary: for any smooth based loop at `0`, the smooth lift's
endpoint lies in `L`.** Destructures the existential. -/
theorem smoothPathLift_endpoint_mem
    (hLift : SmoothPathLiftHypothesisTorus L)
    {γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)}
    (h_src : γ.src = (0 : ℂ ⧸ L)) (h_tgt : γ.tgt = (0 : ℂ ⧸ L)) :
    ∃ x ∈ L, ∃ lift : ℝ → ℂ,
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ lift ∧
      lift 0 = 0 ∧ lift 1 = x ∧
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        L.mkQ (lift t) = γ.ambient t := by
  obtain ⟨lift, h_smooth, h_zero, h_lift⟩ := hLift γ h_src
  have h_at_one : L.mkQ (lift 1) = γ.ambient 1 :=
    h_lift 1 (by constructor <;> norm_num)
  have h_amb_1 : γ.ambient 1 = γ.tgt := by
    have h := γ.ambient_eq_on_unitInterval
      (⟨1, by constructor <;> norm_num⟩ : unitInterval)
    have hval : ((⟨1, by constructor <;> norm_num⟩ : unitInterval).val : ℝ) = 1 := rfl
    rw [hval] at h
    rw [h]
    exact γ.toPath.target
  rw [h_amb_1, h_tgt] at h_at_one
  have h_in_L : lift 1 ∈ L := (Submodule.Quotient.mk_eq_zero L).mp h_at_one
  exact ⟨lift 1, h_in_L, lift, h_smooth, h_zero, rfl, h_lift⟩

end ComplexTorus

end JacobianChallenge

end
