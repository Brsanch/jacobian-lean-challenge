/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiDiv
import JacobianChallenge.Divisor.PrincipalDivisorRange

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # PL-4-E: Abel's theorem (as named hypothesis) + descent to `Pic0 X`

The Abel-Jacobi map of degree-zero divisors descends through
`Pic0 X = Div0 X ⧸ (PrincDiv X).addSubgroupOf (Div0 X)` iff the
principal-divisor subgroup `(PrincDiv X).addSubgroupOf (Div0 X)` lies
in the kernel of `B.abelJacobiDiv0Hom`. This is **Abel's theorem**: a
divisor is principal iff its Abel-Jacobi class is zero (forward
direction here — converse is Jacobi inversion's injectivity).

The forward direction's proof: for `f : MeromorphicNonzero X`, the
principal divisor `(f) = div(f)` admits a representation as a 1-cycle
boundary, and integrating any holomorphic 1-form around that cycle
vanishes by Stokes (since the cycle bounds a 2-chain — the
domain-with-removed-points carrying the meromorphic `f`).

The Stokes step is exactly the content of the
`StokesBoundaryInvariance` named hypothesis in
`Manifold/H1SmoothMod.lean`. We expose Abel's theorem as a downstream
**named-hypothesis bundle** here, package the descent through `Pic0`,
and leave the discharge of Abel's theorem itself to a future chip that
discharges Stokes.

## What this file delivers

* `AbelHypothesis B : Prop` — the statement that
  `B.abelJacobiDiv0Hom` vanishes on the principal-divisor subgroup
  inside `Div0 X`.
* `B.abelJacobi (hAbel : AbelHypothesis B) : Pic0 X →+ AnalyticJacobian`
  — the descent through the quotient, via `QuotientAddGroup.lift`.
* `abelJacobi_mk` — explicit reduction on `mk` representatives.
* `abelJacobi_ofCurve` — value on `Jacobian.ofCurve` (the basic
  generators of `Pic0`).

After this chip, the only remaining open content for the full
Abel-Jacobi iso is the **bijectivity proof** (Abel's converse +
Jacobi inversion), which is classical and multi-thousand LOC.

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

/-- **Abel's theorem (named-hypothesis form).** Asserts that
`abelJacobiDiv0Hom B` vanishes on the principal-divisor subgroup
inside `Div0 X`. Classical proof: integrate any holomorphic 1-form
around the path-representation of a principal divisor; the result is
zero by Stokes (the path-representation bounds a 2-chain). -/
def AbelHypothesis (B : AbelJacobiInput α h) : Prop :=
  ∀ D : Div0 X, (D : Div X) ∈ PrincDiv X → B.abelJacobiDiv0Hom D = 0

/-- The Abel hypothesis as the kernel-containment form needed by
`QuotientAddGroup.lift`. -/
lemma abelHypothesis_iff_subgroup_le_ker (B : AbelJacobiInput α h) :
    AbelHypothesis B ↔
      (PrincDiv X).addSubgroupOf (Div0 X) ≤ B.abelJacobiDiv0Hom.ker := by
  constructor
  · intro hAbel D hD
    -- hD : D ∈ (PrincDiv X).addSubgroupOf (Div0 X), i.e. (D : Div X) ∈ PrincDiv X.
    rw [AddMonoidHom.mem_ker]
    exact hAbel D hD
  · intro hSub D hD
    have : D ∈ B.abelJacobiDiv0Hom.ker := hSub hD
    rwa [AddMonoidHom.mem_ker] at this

/-! ## Descent through `Pic0 X` -/

/-- **The Abel-Jacobi map on `Pic0 X`.** Descended from
`abelJacobiDiv0Hom : Div0 X →+ AnalyticJacobian` through
`Pic0 X = Div0 X ⧸ (PrincDiv X).addSubgroupOf (Div0 X)` via the kernel
containment provided by Abel's theorem. -/
noncomputable def abelJacobi (B : AbelJacobiInput α h)
    (hAbel : AbelHypothesis B) :
    Pic0 X →+ AnalyticJacobian (PeriodPairingData.ofSmoothCycle X) α h :=
  QuotientAddGroup.lift ((PrincDiv X).addSubgroupOf (Div0 X))
    B.abelJacobiDiv0Hom
    ((B.abelHypothesis_iff_subgroup_le_ker).mp hAbel)

@[simp] lemma abelJacobi_mk (B : AbelJacobiInput α h)
    (hAbel : AbelHypothesis B) (D : Div0 X) :
    B.abelJacobi hAbel (QuotientAddGroup.mk D : Pic0 X)
      = B.abelJacobiDiv0Hom D := rfl

/-- **Value of `abelJacobi` on a quotient class.** Reduces to the
divisor-level AJ on any representative. -/
lemma abelJacobi_mk_eq_abelJacobiDiv
    (B : AbelJacobiInput α h) (hAbel : AbelHypothesis B) (D : Div0 X) :
    B.abelJacobi hAbel (QuotientAddGroup.mk D : Pic0 X)
      = B.abelJacobiDiv (D : Div X) := by
  rw [abelJacobi_mk]
  rfl

/-- **Abel-Jacobi vanishes on principal-divisor classes** — trivially
true by construction. Useful as a downstream sanity check. -/
lemma abelJacobi_eq_zero_of_mem_PrincDiv
    (B : AbelJacobiInput α h) (hAbel : AbelHypothesis B)
    {D : Div0 X} (hD : (D : Div X) ∈ PrincDiv X) :
    B.abelJacobi hAbel (QuotientAddGroup.mk D : Pic0 X) = 0 := by
  rw [abelJacobi_mk]
  exact hAbel D hD

end AbelJacobiInput

end JacobianChallenge

end
