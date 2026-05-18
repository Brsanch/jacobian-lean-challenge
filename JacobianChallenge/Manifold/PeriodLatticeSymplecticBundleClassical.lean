/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodLatticeSymplecticBundle
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option linter.unusedSectionVars false

/-! # `PeriodLatticeSymplecticBundle` constructor from classical inputs

The bundle's `periodBasis` field is an `ℝ`-basis of the ambient
`Fin g → ℂ`. Classically, this basis is obtained from the `2g`
period vectors of a chosen symplectic homology basis via Riemann
bilinear **non-degeneracy** (which guarantees ℝ-linear independence
of the periods).

This file factors the bundle construction through that classical
input: given a tuple of `2g` cycle generators whose period vectors
are ℝ-linearly independent (Riemann bilinear) **and** ℤ-span every
cycle's period vector (homology classes generate H₁), the
`PeriodLatticeSymplecticBundle` is constructed by:

* using `LinearIndependent.span_eq_top_of_card_eq_finrank'` to upgrade
  the ℝ-LI tuple to a full `Basis (Fin (2g)) ℝ (Fin g → ℂ)`
  (cardinality count: `Fin (2g)` has `2g` elements, and `finrank ℝ
  (Fin g → ℂ) = 2 * g` via `Module.finrank_pi_fintype` +
  `Complex.finrank_real_complex`);

* lifting `periodBasis_eq` definitionally (the basis IS the periodVector
  tuple);

* lifting `period_image_spanned` directly from the input hypothesis.

**Significance.** This is the cleanest **named-classical-input
boundary** for the period-lattice side of `C3FullInputSymp X`:
downstream consumers no longer need to traffic with the full
`PeriodLatticeSymplecticBundle` shape — they can supply the two
named classical hypotheses (Riemann bilinear non-degeneracy + H₁
generation) and obtain the bundle.

## What this file ships

* `finrank_real_pi_fin_complex` — `finrank ℝ (Fin g → ℂ) = 2 * g`.
* `PeriodLatticeSymplecticBundle.ofClassicalInputs` — the classical-input
  constructor.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-! ## Ambient dimension count -/

/-- The `ℝ`-dimension of `Fin g → ℂ` is `2 * g`. Via
`Module.finrank_pi_fintype` + `Complex.finrank_real_complex` +
`Fintype.card_fin`. -/
theorem finrank_real_pi_fin_complex (g : ℕ) :
    finrank ℝ (Fin g → ℂ) = 2 * g := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Complex.finrank_real_complex, smul_eq_mul,
    Nat.mul_comm]

/-! ## Classical-input constructor for `PeriodLatticeSymplecticBundle` -/

/-- **`PeriodLatticeSymplecticBundle` from classical inputs.**

Given:
* `cycleGens : Fin (2 * genus X) → data.H1` — a tuple of `2g` cycle
  generators (classically: representatives of a symplectic homology
  basis).
* `h_LI : LinearIndependent ℝ (periodVector data α ∘ cycleGens)` —
  Riemann bilinear non-degeneracy: the `2g` period vectors are
  ℝ-linearly independent in `Fin g → ℂ`.
* `h_span : ∀ γ : data.H1, periodVector data α γ ∈ Submodule.span ℤ
  (Set.range (periodVector data α ∘ cycleGens))` — the chosen tuple's
  period vectors ℤ-span the period image (classically: the chosen
  tuple represents a ℤ-generating set of H₁, plus Stokes for
  boundaries).

Produces a `PeriodLatticeSymplecticBundle data α`. The `periodBasis`
field is built via `Basis.mk` on `h_LI` + the dimension-count argument:
`Fintype.card (Fin (2g)) = 2g = finrank ℝ (Fin g → ℂ)`. -/
noncomputable def PeriodLatticeSymplecticBundle.ofClassicalInputs
    (data : PeriodPairingData X)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (h_LI : LinearIndependent ℝ
              (fun i : Fin (2 * JacobianChallenge.genus X) =>
                periodVector data α (cycleGens i)))
    (h_span : ∀ γ : data.H1,
        periodVector data α γ ∈
          Submodule.span ℤ
            (Set.range
              (fun i : Fin (2 * JacobianChallenge.genus X) =>
                periodVector data α (cycleGens i)))) :
    PeriodLatticeSymplecticBundle data α := by
  -- Cardinality count: `Fintype.card (Fin (2g)) = 2g = finrank ℝ (Fin g → ℂ)`.
  have h_card :
      Fintype.card (Fin (2 * JacobianChallenge.genus X)) =
        finrank ℝ (Fin (JacobianChallenge.genus X) → ℂ) := by
    rw [Fintype.card_fin, finrank_real_pi_fin_complex]
  -- Promote `h_LI` to a full `ℝ`-basis using the `'`-form (which only
  -- requires `FiniteDimensional`, no `Nonempty` on the index).
  have h_span_top :
      Submodule.span ℝ
          (Set.range
            (fun i : Fin (2 * JacobianChallenge.genus X) =>
              periodVector data α (cycleGens i)))
        = ⊤ :=
    h_LI.span_eq_top_of_card_eq_finrank' h_card
  let periodBasis : Basis (Fin (2 * JacobianChallenge.genus X)) ℝ
                          (Fin (JacobianChallenge.genus X) → ℂ) :=
    Basis.mk h_LI h_span_top.ge
  -- Compatibility: `Basis.mk` returns a basis whose `coe` is the input tuple.
  have h_compat :
      ∀ i, periodBasis i = periodVector data α (cycleGens i) := by
    intro i
    simp [periodBasis, Basis.coe_mk]
  -- Spanning: `range periodBasis = range (periodVector ∘ cycleGens)`, so
  -- `h_span` applies directly.
  have h_range_eq :
      Set.range periodBasis =
        Set.range
          (fun i : Fin (2 * JacobianChallenge.genus X) =>
            periodVector data α (cycleGens i)) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i, (h_compat i).symm.trans rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨i, h_compat i⟩
  refine
    { cycleGenerators := cycleGens
      periodBasis := periodBasis
      periodBasis_eq := h_compat
      period_image_spanned := ?_ }
  intro γ
  rw [h_range_eq]
  exact h_span γ

end JacobianChallenge

end
