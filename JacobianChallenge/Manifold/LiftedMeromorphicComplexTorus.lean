/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.PrincipalDivisor
import JacobianChallenge.Manifold.ComplexTorus
import JacobianChallenge.Manifold.ComplexTorusBasicInstances
import JacobianChallenge.Manifold.ComplexTorusMkQMfderiv

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Lift `f : MeromorphicNonzero (ℂ ⧸ L)` to a periodic function on ℂ

For a non-zero meromorphic-germ function `f` on the complex torus
`ℂ ⧸ L`, the pullback `f.toFun ∘ L.mkQ : ℂ → ℂ` is **automatically
`L`-periodic** by construction. This file packages the lift and its
periodicity, providing the ℂ-side primitive that the classical
contour-integration proof of Abel's theorem on elliptic functions
operates on.

The follow-up work is (i) meromorphy of the lift on `ℂ` (chart-pullback
inversion), (ii) divisor agreement (`orderAt_lift z = orderAt_f
(L.mkQ z)`), and (iii) the contour-integration argument
`∮_∂Π z · (F'/F)(z) dz ≡ 0 mod L` on a fundamental parallelogram `Π`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **The lift** of `f : MeromorphicNonzero (ℂ ⧸ L)` to a function on `ℂ`
via `z ↦ f (L.mkQ z)`. -/
noncomputable def liftedFun (f : MeromorphicNonzero (ℂ ⧸ L)) : ℂ → ℂ :=
  fun z => f.toFun (L.mkQ z)

@[simp] lemma liftedFun_apply (f : MeromorphicNonzero (ℂ ⧸ L)) (z : ℂ) :
    liftedFun L f z = f.toFun (L.mkQ z) := rfl

/-- **`L`-periodicity of the lifted function.** For `om ∈ L`,
`liftedFun L f (z + om) = liftedFun L f z`. -/
theorem liftedFun_periodic (f : MeromorphicNonzero (ℂ ⧸ L))
    {om : ℂ} (hom : om ∈ L) (z : ℂ) :
    liftedFun L f (z + om) = liftedFun L f z := by
  show f.toFun (L.mkQ (z + om)) = f.toFun (L.mkQ z)
  congr 1
  rw [map_add]
  have h0 : L.mkQ om = 0 := (Submodule.Quotient.mk_eq_zero L).mpr hom
  rw [h0, add_zero]

/-- **Negation form.** For `om ∈ L`, `liftedFun L f (z - om) = liftedFun L f z`. -/
theorem liftedFun_periodic_sub (f : MeromorphicNonzero (ℂ ⧸ L))
    {om : ℂ} (hom : om ∈ L) (z : ℂ) :
    liftedFun L f (z - om) = liftedFun L f z := by
  show f.toFun (L.mkQ (z - om)) = f.toFun (L.mkQ z)
  congr 1
  rw [map_sub]
  have h0 : L.mkQ om = 0 := (Submodule.Quotient.mk_eq_zero L).mpr hom
  rw [h0, sub_zero]

/-- **`liftedFun` is invariant under any lattice translation.** For
`om ∈ L` and any integer `n`, `liftedFun L f (z + n • om) = liftedFun L f z`. -/
theorem liftedFun_periodic_zsmul (f : MeromorphicNonzero (ℂ ⧸ L))
    {om : ℂ} (hom : om ∈ L) (n : ℤ) (z : ℂ) :
    liftedFun L f (z + n • om) = liftedFun L f z :=
  liftedFun_periodic L f (L.smul_mem (n : ℤ) hom) z

end ComplexTorus

end JacobianChallenge

end
