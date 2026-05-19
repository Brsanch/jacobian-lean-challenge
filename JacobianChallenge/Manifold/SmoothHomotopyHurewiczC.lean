/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothHomotopyHurewiczHypothesis
import JacobianChallenge.Manifold.SmoothHomotopyStraightLineC
import JacobianChallenge.Manifold.WordRepresentativeAnyGenus

set_option linter.unusedSectionVars false

/-! # `SmoothHomotopyHurewiczHypothesis` on `ℂ` via straight-line homotopy

For any basepoint `p₀ : ℂ` and any genus `g`, the all-constant
symplectic basis `constSymplecticBasis p₀ g` (every basis loop equals
`SmoothPath.const ℂ ℂ p₀`) satisfies the **smooth-homotopy Hurewicz
hypothesis**:

> *For every smooth based loop `γ` at `p₀`, there exist integers
> `n : Fin (2g) → ℤ` and a concrete smooth homotopy
> `H : SmoothHomotopyBasedLoop γ (basisProductLoop sb n)`.*

The witness is `n := 0` together with the straight-line homotopy in `ℂ`
(`SmoothHomotopyBasedLoop.straightLineC`), demonstrating the new
geometric abstraction over the algebraic-bordism route used in
`WordRepresentativeAnyGenus.lean`.

Same honest degenerate-basis caveat as `WordRepresentativeAnyGenus.lean`:
every basis loop is the constant loop, so the `cycleGens` are all
null-homologous and the hypothesis says "every loop is smoothly
homotopic to a null-bordant product", which on `ℂ` is true.

## What this file ships

* `smoothHomotopyHurewiczHypothesis_constSymplecticBasis_C_holds` —
  the discharge on `ℂ` via the straight-line homotopy.
* Sanity check: composing with
  `smoothHurewiczHypothesis_of_smoothHomotopyHurewicz` recovers the
  existing `smoothHurewiczHypothesis_constSymplecticBasis_C_holds`
  from `WordRepresentativeAnyGenus.lean`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

/-- **`SmoothHomotopyHurewiczHypothesis (constSymplecticBasis p₀ g)` on
`ℂ` UNCONDITIONAL.** Every smooth based loop `γ` at `p₀ : ℂ` is
smoothly homotopic to `basisProductLoop (constSymplecticBasis p₀ g) 0`
via the straight-line homotopy. -/
theorem smoothHomotopyHurewiczHypothesis_constSymplecticBasis_C_holds
    (p₀ : ℂ) (g : ℕ) :
    SmoothHomotopyHurewiczHypothesis (constSymplecticBasis p₀ g) := by
  intro γ h_src h_tgt
  refine ⟨fun _ => 0, ⟨?_⟩⟩
  exact SmoothHomotopyBasedLoop.straightLineC
    (⟨γ, ⟨h_src, h_tgt⟩⟩ : BasedLoopAt 𝓘(ℝ, ℂ) ℂ p₀)
    (basisProductLoop (constSymplecticBasis p₀ g) (fun _ => 0))

/-- **Sanity composition.** The new smooth-homotopy route on `ℂ`
recovers `SmoothHurewiczHypothesis (constSymplecticBasis p₀ g)`,
matching the existing algebraic-bordism discharge in
`WordRepresentativeAnyGenus.lean`. -/
theorem smoothHurewiczHypothesis_constSymplecticBasis_C_via_homotopy
    (p₀ : ℂ) (g : ℕ) :
    SmoothHurewiczHypothesis (constSymplecticBasis p₀ g) :=
  smoothHurewiczHypothesis_of_smoothHomotopyHurewicz
    (smoothHomotopyHurewiczHypothesis_constSymplecticBasis_C_holds p₀ g)

end JacobianChallenge

end
