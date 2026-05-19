/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothBordantOfSmoothHomotopy
import JacobianChallenge.Manifold.SmoothBordismAndWordRepresentative

set_option linter.unusedSectionVars false

/-! # `SmoothHomotopyHurewiczHypothesis`: every smooth based loop is
smoothly homotopic to a `basisProductLoop`

The `SmoothHurewiczHypothesis sb` arc factors as:

```
SmoothHomotopyHurewiczHypothesis sb           (this file)
   ↓ smoothBordant_of_smoothHomotopy
WordRepresentativeHypothesis sb               (SmoothBordismAndWordRepresentative.lean)
   ↓ smoothHurewiczHypothesis_of_wordRepresentative
SmoothHurewiczHypothesis sb
   ↓ smoothHurewicz_iff_basedLoopHomology  (SmoothHurewiczHypothesis.lean)
BasedLoopHomologyDecompositionHypothesis sb.cycleGens p₀
   ↓ H1_spans_top_canonical_of_basedLoopHomology
H1_spans_top_canonical sb.cycleGens
   ↓ GenericGenusPeriodLatticeInputs.ofSmoothHurewicz (+ riemannBilinear + holomorphicCanonicalClosed)
GenericGenusPeriodLatticeInputs basis
   ↓ nonempty_periodLatticeSymplecticBundle_of_genericGenus
Nonempty (PeriodLatticeSymplecticBundle ...)
```

This file introduces the **top of that chain**: a hypothesis whose
witness is *concrete geometric data* — a smooth map `H : ℝ² → X`
satisfying the four edge conditions of `SmoothHomotopyBasedLoop` —
rather than the *algebraic* "differs by a Stokes-boundary" of bordism.

On a genus-`g` surface the classical content (cellular approximation /
PL approximation + smoothing) produces such homotopies; this file
provides the structural plumbing so that any concrete genus-≥1 construction
can plug a homotopy in and immediately get a period lattice.

## What this file ships

* `SmoothHomotopyHurewiczHypothesis sb` — every smooth based loop at
  `p₀` admits a smooth homotopy to a `basisProductLoop`.
* `wordRepresentativeHypothesis_of_smoothHomotopyHurewicz` — the
  bordism upgrade via `smoothBordant_of_smoothHomotopy`.
* `smoothHurewiczHypothesis_of_smoothHomotopyHurewicz` — composition
  through to `SmoothHurewiczHypothesis sb`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-! ## The smooth-homotopy Hurewicz hypothesis -/

/-- **`SmoothHomotopyHurewiczHypothesis sb`** — every smooth based
loop at `p₀ : X` is connected by a *concrete smooth homotopy* to a
`basisProductLoop sb n` for some integer tuple `n : Fin (2g) → ℤ`.

This is a strengthening of `WordRepresentativeHypothesis sb` whose
witness is an explicit smooth map `H : (Fin 2 → ℝ) → X` satisfying the
edge conditions of `SmoothHomotopyBasedLoop`. The algebraic
"differs-by-Stokes-boundary" downgrade follows from
`smoothBordant_of_smoothHomotopy`. -/
def SmoothHomotopyHurewiczHypothesis {p₀ : X} {g : ℕ}
    (sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ g) : Prop :=
  ∀ γ : SmoothPath 𝓘(ℝ, ℂ) X, ∀ h_src : γ.src = p₀, ∀ h_tgt : γ.tgt = p₀,
    ∃ n : Fin (2 * g) → ℤ,
      Nonempty (SmoothHomotopyBasedLoop
        (⟨γ, ⟨h_src, h_tgt⟩⟩ : BasedLoopAt 𝓘(ℝ, ℂ) X p₀)
        (basisProductLoop sb n))

/-! ## Bordism upgrade -/

/-- **`WordRepresentativeHypothesis sb` from
`SmoothHomotopyHurewiczHypothesis sb`.**

Each per-loop smooth homotopy is downgraded to a `SmoothBordant`
witness via `SmoothHomotopyBasedLoop.smoothBordant_of_smoothHomotopy`. -/
theorem wordRepresentativeHypothesis_of_smoothHomotopyHurewicz
    {p₀ : X} {g : ℕ} {sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ g}
    (h : SmoothHomotopyHurewiczHypothesis sb) :
    WordRepresentativeHypothesis sb := by
  intro γ h_src h_tgt
  obtain ⟨n, ⟨H⟩⟩ := h γ h_src h_tgt
  exact ⟨n, SmoothHomotopyBasedLoop.smoothBordant_of_smoothHomotopy H⟩

/-! ## Composition through to `SmoothHurewiczHypothesis` -/

/-- **`SmoothHurewiczHypothesis sb` from
`SmoothHomotopyHurewiczHypothesis sb`.** Composes the bordism
upgrade with `smoothHurewiczHypothesis_of_wordRepresentative`. -/
theorem smoothHurewiczHypothesis_of_smoothHomotopyHurewicz
    {p₀ : X} {g : ℕ} {sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ g}
    (h : SmoothHomotopyHurewiczHypothesis sb) :
    SmoothHurewiczHypothesis sb :=
  smoothHurewiczHypothesis_of_wordRepresentative
    (wordRepresentativeHypothesis_of_smoothHomotopyHurewicz h)

end JacobianChallenge

end
