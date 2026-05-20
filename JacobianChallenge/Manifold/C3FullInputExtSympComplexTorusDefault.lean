/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3FullInputExtSympComplexTorus
import JacobianChallenge.Manifold.PeriodLatticeSymplecticBundleComplexTorus
import JacobianChallenge.Manifold.Pic0EvalSumComplexTorus

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Headline: full T_L closure from the two named classical hypotheses

`Nonempty (PeriodLatticeSymplecticBundle … (ℂ ⧸ L))` on `T_L` is
unconditional (`nonempty_periodLatticeSymplecticBundle_complexTorus`).
Combined with the two named classical hypotheses
(`TLDivSumHypothesis L` + `TLAbelConverseHypothesis L`), the full
`Nonempty (C3FullInputExtSymp (ℂ ⧸ L))` follows without any
PLSB-witness parameter.

This is the cleanest entry point for downstream consumers of the
period-lattice infrastructure on the complex torus.

Includes a parallel `pic0EquivComplexTorus_default` and
`evalSumPic0Equiv_default` that take ONLY the two named hypotheses
(no PLSB witness).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **Default closure of the challenge for T_L from two named hypotheses.**

`Nonempty (C3FullInputExtSymp (ℂ⧸L))` from:
* `TLDivSumHypothesis L` — Abel's theorem on elliptic functions.
* `TLAbelConverseHypothesis L` — Weierstrass σ-function existence.

The required `PeriodLatticeSymplecticBundle` witness is filled in
automatically by `nonempty_periodLatticeSymplecticBundle_complexTorus`
(unconditional on `T_L`). -/
theorem nonempty_C3FullInputExtSymp_complexTorus_from_two_named_hypotheses
    (hTL : TLDivSumHypothesis L)
    (hConverse : TLAbelConverseHypothesis L) :
    Nonempty (JacobianChallenge.C3FullInputExtSymp (ℂ ⧸ L)) := by
  let h := Classical.choice (nonempty_periodLatticeSymplecticBundle_complexTorus L)
  exact nonempty_C3FullInputExtSymp_complexTorus_of_two_named_hypotheses L h hTL hConverse

/-- **Default `Pic⁰ (ℂ⧸L) ≃+ ℂ⧸L`** from two named hypotheses.
PLSB-witness filled in automatically. -/
noncomputable def pic0EquivComplexTorus_default
    (hTL : TLDivSumHypothesis L)
    (hConverse : TLAbelConverseHypothesis L) :
    Pic0 (ℂ ⧸ L) ≃+ (ℂ ⧸ L) :=
  pic0EquivComplexTorus L
    (Classical.choice (nonempty_periodLatticeSymplecticBundle_complexTorus L))
    hTL hConverse

/-- **Closed-form `Pic⁰ (ℂ⧸L) ≃+ ℂ⧸L`** via `evalSumPic0Equiv`.
PLSB-independent on the surface: takes only the two named hypotheses. -/
noncomputable def evalSumPic0Equiv_default
    (hTL : TLDivSumHypothesis L)
    (hConverse : TLAbelConverseHypothesis L) :
    Pic0 (ℂ ⧸ L) ≃+ (ℂ ⧸ L) :=
  evalSumPic0Equiv L hTL hConverse

/-- The closed-form default `evalSumPic0Equiv_default [D]` equals
`∑ x ∈ supp D, D x • x` in `ℂ ⧸ L`. -/
@[simp] lemma evalSumPic0Equiv_default_mk
    (hTL : TLDivSumHypothesis L)
    (hConverse : TLAbelConverseHypothesis L)
    (D : Div0 (ℂ ⧸ L)) :
    evalSumPic0Equiv_default L hTL hConverse (QuotientAddGroup.mk D)
      = Div.evalSum (D : Div (ℂ ⧸ L)) := rfl

/-- On the canonical `[ (Q) − (0) ]` generator, the closed-form default
returns `Q`. -/
@[simp] lemma evalSumPic0Equiv_default_single_sub_single
    (hTL : TLDivSumHypothesis L)
    (hConverse : TLAbelConverseHypothesis L)
    (Q : ℂ ⧸ L) :
    haveI : DecidableEq (ℂ ⧸ L) := Classical.decEq _
    evalSumPic0Equiv_default L hTL hConverse
        (QuotientAddGroup.mk
          (⟨Div.single Q - Div.single (0 : ℂ ⧸ L),
            Div.single_sub_single_mem_Div0 (0 : ℂ ⧸ L) Q⟩ : Div0 (ℂ ⧸ L)))
      = Q :=
  evalSumPic0_single_sub_single L hTL Q

end ComplexTorus

end JacobianChallenge

end
