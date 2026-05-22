/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexPeriodAdjunction
import JacobianChallenge.Manifold.PeriodPairingMorphismOfSmoothCycle

set_option linter.unusedSectionVars false

/-! # `PeriodPairingMorphism.ofSmoothCycle_unconditional` (chip 55)

Plugs chip 54's unconditional `complexPeriod` adjunction into
`PeriodPairingMorphism.ofSmoothCycle`, producing a fully unconditional
constructor:

  `PeriodPairingMorphism.ofSmoothCycle_unconditional f hf`
    : PeriodPairingMorphism (PeriodPairingData.ofSmoothCycle X)
                            (PeriodPairingData.ofSmoothCycle Y)`

(only the holomorphic curve map `f` + its ω-smoothness `hf` needed —
the adjunction is no longer a named input).

This is the **F8 closure point**: combined with the in-tree
`PeriodPairingMorphism.lattice_match` + `JacobianAnalyticPushforwardLift.ofMorphism`,
this gives the canonical pushforward lift unconditionally per curve
map, unblocking the lattice-match hypothesis of
`canonicalPushforward_contMDiff` (item 18 of `Basic.lean`).

## Smoothness-level bridge

Chip 54's `complexPeriod_pushHom_eq_pullback` uses
`SmoothCycle.pushHom f ((complex_to_real_omega hf).of_le le_top)`,
while `PeriodPairingMorphism.ofSmoothCycle`'s adjunction input uses
`SmoothCycle.pushHom f (complex_to_real hf)`. Both `(complex_to_real_omega
hf).of_le le_top` and `complex_to_real hf` are terms of
`ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f`, equal by proof irrelevance (`ContMDiff
= ∀ x, ContMDiffAt ...`, a `Prop`).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology Bundle ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]
variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-- **Unconditional `PeriodPairingMorphism` from a holomorphic curve map.**
Discharges the adjunction hypothesis of
`PeriodPairingMorphism.ofSmoothCycle` via chip 54. -/
noncomputable def PeriodPairingMorphism.ofSmoothCycle_unconditional
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) :
    PeriodPairingMorphism (PeriodPairingData.ofSmoothCycle X)
                          (PeriodPairingData.ofSmoothCycle Y) :=
  PeriodPairingMorphism.ofSmoothCycle f hf
    (fun γ τ => by
      -- Chip 54 with `(complex_to_real_omega hf).of_le le_top` matches the
      -- expected `complex_to_real hf` by proof irrelevance on the Prop.
      have h := complexPeriod_pushHom_eq_pullback (X := X) (Y := Y) f hf γ τ
      convert h using 2)

end JacobianChallenge

end
