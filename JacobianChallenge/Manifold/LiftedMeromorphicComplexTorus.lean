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

/-! ## Order-correspondence: assumed lifting hypothesis -/

/-- **The per-`f` lifting hypothesis.** Asserts that `liftedFun L f` on
`ℂ` has the same chart-pullback order at every `z ∈ ℂ` as `f` has at
`L.mkQ z ∈ ℂ ⧸ L`. This is the analytic content of the statement
"`liftedFun L f` and `f` define the same divisor up to lattice
translation".

It is a **named hypothesis** because the discharge requires careful
local-chart manipulation (the chart at `L.mkQ z` is centered at
`(L.mkQ z).out`, not at `z`, so the equality of orders requires
identifying a lattice translate `δ ∈ L` with `liftedFun = (f ∘
chartAt.symm) ∘ (· - δ)` locally near `z` and invoking translation-
invariance of `MeromorphicAt`). The actual discharge is a follow-up
chip; the current file consumes the named hypothesis. -/
def LiftedOrderCorrespondence (f : MeromorphicNonzero (ℂ ⧸ L)) : Prop :=
  ∀ z : ℂ,
    meromorphicOrderAt (liftedFun L f) z
      = mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun (L.mkQ z)

/-- **Total lift hypothesis on `L`**: every `f` admits an order-
correspondence lift. -/
def LiftedOrderCorrespondenceTotal : Prop :=
  ∀ f : MeromorphicNonzero (ℂ ⧸ L), LiftedOrderCorrespondence L f

end ComplexTorus

end JacobianChallenge

end
