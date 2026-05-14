/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiPic0

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # PL-4-F: Jacobi inversion (named hypothesis) + `Pic0 X ≃+ AnalyticJacobian`

Final classical step in the Abel-Jacobi arc: under Abel's theorem
(PL-4-E), the descended map `abelJacobi : Pic0 X →+ AnalyticJacobian`
is well-defined. **Jacobi inversion** asserts that this map is in fact
a **bijection** — an isomorphism of additive groups.

Classical statement: the Abel-Jacobi map of degree-zero divisor classes
to the analytic Jacobian is a bijection on a compact connected complex
1-manifold of genus `g`. Injectivity is the converse of Abel's theorem
(a divisor whose AJ class is zero is principal); surjectivity is the
Jacobi inversion theorem (every class in `ℂ^g / Λ` is realized by some
divisor class).

Both directions are classical and multi-thousand-LOC content. We expose
them as named hypotheses and ship the resulting `AddEquiv`
unconditionally.

## What this file delivers

* `JacobiInversion B hAbel : Prop` — the conjunction of injectivity
  and surjectivity of `abelJacobi`.
* `B.abelJacobiEquiv hAbel hJI : Pic0 X ≃+ AnalyticJacobian` — the
  resulting `AddEquiv`, packaged via `AddEquiv.ofBijective`.
* `abelJacobiEquiv_apply` and `abelJacobiEquiv_symm_apply` — the
  underlying-function unfoldings.

Strategic position: once `JacobiInversion` is discharged (multi-thousand
LOC, blocked on the converse of Abel + surjectivity proof), the
`AddEquiv` transports `AnalyticJacobian`'s analytic structure
(TopologicalSpace, ChartedSpace, T2Space, CompactSpace, IsManifold,
LieAddGroup — all already discharged via PL-3-fin-2's
`ofBundle_compactSpace`/`_chartedSpace`) back to `Pic0 X`. Combined
with `Jacobian X := Pic0 X` (the existing definition in `Basic.lean`),
this flips items 4, 5, 10, 11, 12, 13 of OPEN.md.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff
open Submodule Module

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

namespace AbelJacobiInput

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α}

/-- **Jacobi inversion (named-hypothesis form).** The Abel-Jacobi map
`abelJacobi : Pic0 X →+ AnalyticJacobian` is bijective. Classical
content: injectivity = converse of Abel's theorem, surjectivity = Jacobi
inversion theorem on compact Riemann surfaces. -/
structure JacobiInversion (B : AbelJacobiInput α h) (hAbel : AbelHypothesis B) :
    Prop where
  /-- The Abel-Jacobi map is injective on `Pic0 X`. Equivalent to Abel's
  converse: an AJ-trivial divisor class is the class of a principal
  divisor. -/
  injective : Function.Injective (B.abelJacobi hAbel)
  /-- The Abel-Jacobi map is surjective onto `AnalyticJacobian`. The
  Jacobi inversion theorem: every class in `ℂ^g / Λ` is realised by some
  divisor class. -/
  surjective : Function.Surjective (B.abelJacobi hAbel)

/-- **Bijectivity packaging** for `AddEquiv.ofBijective`. -/
lemma JacobiInversion.bijective
    {B : AbelJacobiInput α h} {hAbel : AbelHypothesis B}
    (hJI : JacobiInversion B hAbel) :
    Function.Bijective (B.abelJacobi hAbel) :=
  ⟨hJI.injective, hJI.surjective⟩

/-! ## The Abel-Jacobi `AddEquiv` -/

/-- **The Abel-Jacobi isomorphism `Pic0 X ≃+ AnalyticJacobian`.** Under
Abel's theorem (PL-4-E) and Jacobi inversion (this file's hypothesis),
the descended map `abelJacobi : Pic0 X →+ AnalyticJacobian` upgrades to
an additive-group isomorphism. -/
noncomputable def abelJacobiEquiv (B : AbelJacobiInput α h)
    (hAbel : AbelHypothesis B) (hJI : JacobiInversion B hAbel) :
    Pic0 X ≃+ AnalyticJacobian (PeriodPairingData.ofSmoothCycle X) α h :=
  AddEquiv.ofBijective (B.abelJacobi hAbel) hJI.bijective

@[simp] lemma abelJacobiEquiv_apply
    (B : AbelJacobiInput α h) (hAbel : AbelHypothesis B)
    (hJI : JacobiInversion B hAbel) (c : Pic0 X) :
    B.abelJacobiEquiv hAbel hJI c = B.abelJacobi hAbel c := rfl

@[simp] lemma abelJacobiEquiv_mk
    (B : AbelJacobiInput α h) (hAbel : AbelHypothesis B)
    (hJI : JacobiInversion B hAbel) (D : Div0 X) :
    B.abelJacobiEquiv hAbel hJI (QuotientAddGroup.mk D : Pic0 X)
      = B.abelJacobiDiv (D : Div X) := by
  rw [abelJacobiEquiv_apply, abelJacobi_mk]
  rfl

/-! ## Bidirectional unfoldings -/

/-- The `symm` direction of the equivalence is the inverse map. -/
lemma abelJacobiEquiv_symm_apply_apply
    (B : AbelJacobiInput α h) (hAbel : AbelHypothesis B)
    (hJI : JacobiInversion B hAbel) (c : Pic0 X) :
    (B.abelJacobiEquiv hAbel hJI).symm (B.abelJacobi hAbel c) = c :=
  (B.abelJacobiEquiv hAbel hJI).symm_apply_apply c

/-- The forward direction unfolds to `abelJacobi`. -/
lemma abelJacobi_eq_abelJacobiEquiv
    (B : AbelJacobiInput α h) (hAbel : AbelHypothesis B)
    (hJI : JacobiInversion B hAbel) :
    (B.abelJacobiEquiv hAbel hJI : Pic0 X →+ _) = B.abelJacobi hAbel := by
  rfl

end AbelJacobiInput

end JacobianChallenge

end
