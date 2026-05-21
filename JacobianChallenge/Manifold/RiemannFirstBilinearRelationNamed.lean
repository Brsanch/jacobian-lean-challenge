/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannBilinearPeriodForm

set_option linter.unusedSectionVars false

/-! # `RiemannFirstBilinearRelation X` — named-hypothesis form

The Riemann first bilinear relation on a compact connected complex
1-manifold `X` is the statement that the abstract period bilinear form
`Q` from `RiemannBilinearPeriodForm.lean` vanishes identically on
pairs of holomorphic 1-forms, against any antisymmetric integer matrix
`J` over `Fin (2 g) × Fin (2 g)` and any period-pairing data + cycle
generators:

  `∀ ω₀ ω₁ : HolomorphicOneForm X, Q J cycleGens ω₀ ω₁ = 0`.

This is the single classical mathematical statement that, by chip 6's
bridge `periodMatrix_form_eq_riemannBilinearPeriodForm`, discharges
every strict-upper-triangular entry of `pmatᵀ · J.cast · pmat` at
arbitrary genus (and hence every off-diagonal entry by `J`
antisymmetry, and the diagonals from chip 7 / chip 20e).

Classical proof outline (NOT in tree at this pin — listed for
reference, future work to discharge `RiemannFirstBilinearRelation`):

1. Cut `X` along the symplectic basis cycles to obtain the fundamental
   `4g`-gon `Π`, which is simply connected.
2. By the Poincaré lemma on `Π`, the holomorphic 1-form `ω₁` admits a
   smooth primitive `F` on `Π`.
3. Stokes' theorem on `∂Π = (symplectic combination)` :
   `∫_{∂Π} F · ω₀ = ∫_Π d(F · ω₀) = ∫_Π dF ∧ ω₀ = ∫_Π ω₁ ∧ ω₀ = - ∫_Π ω₀ ∧ ω₁`.
4. The wedge `ω₀ ∧ ω₁` has type `(2, 0)` on a 1-complex-dim manifold,
   hence is **identically zero** at every point (chip 5
   `cotangent_wedge_pointwise_zero`). So `∫_Π ω₀ ∧ ω₁ = 0`.
5. The LHS `∫_{∂Π} F · ω₀` expands into the bilinear period sum
   `Q J cycleGens ω₀ ω₁` (via the explicit formula for `∂Π`).
6. Therefore `Q J cycleGens ω₀ ω₁ = 0`.

Steps 1–3 and 5 require integration of differential forms on smooth
2-chains + the Poincaré lemma on simply-connected complex manifolds —
classical content not at the mathlib pin `8e3c989...`.

## What this file ships

* `RiemannFirstBilinearRelation X` — the named hypothesis.
* `strictUpperTriangular_zero_of_RiemannFirstBilinearRelation` —
  discharge of the strict-upper-triangular condition required by chip
  20g/p from the named hypothesis.
* `offDiagonal_zero_of_RiemannFirstBilinearRelation` — discharge of
  the off-diagonal condition required by chip 20f from the named
  hypothesis (subsumes strictUpperTriangular; symmetric form).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`RiemannFirstBilinearRelation`** — the named classical
hypothesis that the period bilinear form `Q` vanishes identically on
holomorphic 1-forms against a fixed `data + cycleGens + J`.

Parameterised over `data, cycleGens, J` (rather than universally
quantified) so the universe level of `data.H1` does not need to be
fixed at the Prop level. Downstream consumers re-parameterise. -/
def RiemannFirstBilinearRelation
    {data : PeriodPairingData X}
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ) : Prop :=
  ∀ ω₀ ω₁ : HolomorphicOneForm X,
    riemannBilinearPeriodForm cycleGens J ω₀ ω₁ = 0

/-- **Discharge of strict-upper-triangular vanishing from
`RiemannFirstBilinearRelation`.**

Compose with chip 6's bridge identity: every strict-upper-triangular
entry of `pmatᵀ · J.cast · pmat` equals `Q J cycleGens (α i) (α j)`
for `i < j`, which by the named hypothesis is `0`. -/
theorem strictUpperTriangular_zero_of_RiemannFirstBilinearRelation
    {data : PeriodPairingData X}
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    (h_relation : RiemannFirstBilinearRelation cycleGens J) :
    ∀ i j : Fin (JacobianChallenge.genus X), i < j →
      ((periodMatrix data α cycleGens)ᵀ
          * J.map ((↑) : ℤ → ℂ)
          * periodMatrix data α cycleGens) i j = 0 := by
  intro i j _hij
  rw [periodMatrix_form_eq_riemannBilinearPeriodForm data α cycleGens J i j]
  exact h_relation (α i) (α j)

/-- **Discharge of the off-diagonal vanishing from
`RiemannFirstBilinearRelation`.**

Stronger than `strictUpperTriangular`: any `i ≠ j` (not just `i < j`)
works since the named hypothesis applies symmetrically. -/
theorem offDiagonal_zero_of_RiemannFirstBilinearRelation
    {data : PeriodPairingData X}
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    (h_relation : RiemannFirstBilinearRelation cycleGens J) :
    ∀ i j : Fin (JacobianChallenge.genus X), i ≠ j →
      ((periodMatrix data α cycleGens)ᵀ
          * J.map ((↑) : ℤ → ℂ)
          * periodMatrix data α cycleGens) i j = 0 := by
  intro i j _hij
  rw [periodMatrix_form_eq_riemannBilinearPeriodForm data α cycleGens J i j]
  exact h_relation (α i) (α j)

end JacobianChallenge

end
