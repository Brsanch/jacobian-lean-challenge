/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelHypothesisFromPeriodCondition

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # The "discharged" set of generators for `AbelGeneratorPeriodCondition`

For a fixed `B : AbelJacobiInput α h`, define

  `dischargedGenerators B :=
     { f : MeromorphicNonzero X |
        complexChainPeriodVector α (B.principalDivisorAJChain (principalDivisorMap f))
          ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α }`

i.e. the set of meromorphic functions for which the period-vector
condition holds.  By construction,

  `AbelGeneratorPeriodCondition B ↔ dischargedGenerators B = Set.univ`.

The point of this file is to show that `dischargedGenerators B` is
*algebraically closed*: it contains `1`, every non-zero constant, and
is closed under multiplication.  Closure follows from

* `principalDivisorMap_mul` (`Divisor/PrincipalDivisor.lean`):
  `principalDivisorMap (f * g) = principalDivisorMap f + principalDivisorMap g`.
* `principalDivisorAJChain_add` (`AbelHypothesisFromPeriodCondition.lean`):
  the AJ-chain is additive in the divisor.
* `complexChainPeriodVector_principalDivisorAJChain_add_mem` (same file):
  the lattice membership is closed under addition.

The substantive C3 work that remains is exhibiting `dischargedGenerators
B = Set.univ` — i.e. discharging the period-vector condition on every
meromorphic function.  Classically this is Abel forward via the
level-set chain Stokes argument.  The algebra-structure layer in this
file lets that discharge proceed on a *multiplicative generating set*
of `MeromorphicNonzero X` rather than every function individually.

No `sorry`, no `axiom`. -/

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

/-- **Discharged-generators set.** Meromorphic functions whose
principal-divisor AJ-chain has period vector in `periodLatticeImage`.
This is the per-generator atomic content of
`AbelGeneratorPeriodCondition`. -/
def dischargedGenerators (B : AbelJacobiInput α h) : Set (MeromorphicNonzero X) :=
  { f | complexChainPeriodVector α (B.principalDivisorAJChain (principalDivisorMap f))
          ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α }

lemma mem_dischargedGenerators_iff (B : AbelJacobiInput α h)
    (f : MeromorphicNonzero X) :
    f ∈ B.dischargedGenerators ↔
      complexChainPeriodVector α (B.principalDivisorAJChain (principalDivisorMap f))
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α := Iff.rfl

/-- **Vacuous discharge by zero principal divisor.** Any `f` with
`principalDivisorMap f = 0` is in `dischargedGenerators`. The AJ chain
of the zero divisor is `0`, whose period vector is `0`, which lies in
every subgroup. -/
theorem mem_dischargedGenerators_of_principalDivisor_zero
    (B : AbelJacobiInput α h) {f : MeromorphicNonzero X}
    (hf : principalDivisorMap f = 0) :
    f ∈ B.dischargedGenerators := by
  show complexChainPeriodVector α
      (B.principalDivisorAJChain (principalDivisorMap f))
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α
  rw [hf, B.principalDivisorAJChain_zero,
      complexChainPeriodVector_zero α]
  exact zero_mem _

/-- **Unit is discharged.** `principalDivisorMap_one` gives
`principalDivisorMap 1 = 0`, then the zero-divisor lemma applies. -/
theorem one_mem_dischargedGenerators (B : AbelJacobiInput α h) :
    (1 : MeromorphicNonzero X) ∈ B.dischargedGenerators :=
  B.mem_dischargedGenerators_of_principalDivisor_zero principalDivisorMap_one

/-- **Constants are discharged.** `principalDivisorMap_const` gives
`principalDivisorMap (const c hc) = 0`. -/
theorem const_mem_dischargedGenerators (B : AbelJacobiInput α h)
    (c : ℂ) (hc : c ≠ 0) :
    MeromorphicNonzero.const (X := X) c hc ∈ B.dischargedGenerators :=
  B.mem_dischargedGenerators_of_principalDivisor_zero (principalDivisorMap_const c hc)

/-- **Multiplicative closure of the discharged set.** Composes
`principalDivisorMap_mul` (additivity of the principal-divisor map on
products) with `complexChainPeriodVector_principalDivisorAJChain_add_mem`
(lattice membership is preserved by chain addition). -/
theorem mul_mem_dischargedGenerators (B : AbelJacobiInput α h)
    {f g : MeromorphicNonzero X}
    (hf : f ∈ B.dischargedGenerators) (hg : g ∈ B.dischargedGenerators) :
    f * g ∈ B.dischargedGenerators := by
  show complexChainPeriodVector α
      (B.principalDivisorAJChain (principalDivisorMap (f * g)))
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α
  rw [principalDivisorMap_mul]
  exact complexChainPeriodVector_principalDivisorAJChain_add_mem B hf hg

/-- **Inversion closure of the discharged set.** Composes
`principalDivisorMap_invMer` (inversion negates the principal divisor)
with `complexChainPeriodVector_principalDivisorAJChain_neg_mem`
(lattice membership is preserved under negation). -/
theorem invMer_mem_dischargedGenerators (B : AbelJacobiInput α h)
    {f : MeromorphicNonzero X}
    (hf : f ∈ B.dischargedGenerators) :
    MeromorphicNonzero.invMer f ∈ B.dischargedGenerators := by
  show complexChainPeriodVector α
      (B.principalDivisorAJChain (principalDivisorMap (MeromorphicNonzero.invMer f)))
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α
  rw [principalDivisorMap_invMer]
  exact complexChainPeriodVector_principalDivisorAJChain_neg_mem B hf

/-- **Quotient closure** (no `Div` instance on `MeromorphicNonzero X`,
so this is stated for the literal product `f * invMer g`). Combines
`mul_mem_dischargedGenerators` and `invMer_mem_dischargedGenerators`. -/
theorem mul_invMer_mem_dischargedGenerators (B : AbelJacobiInput α h)
    {f g : MeromorphicNonzero X}
    (hf : f ∈ B.dischargedGenerators) (hg : g ∈ B.dischargedGenerators) :
    f * MeromorphicNonzero.invMer g ∈ B.dischargedGenerators :=
  B.mul_mem_dischargedGenerators hf (B.invMer_mem_dischargedGenerators hg)

/-! ## Constant-function discharge

If `f.toFun` is a literal constant function `fun _ => c` with `c ≠ 0`,
then `principalDivisorMap f = 0` (by `mmeromorphicOrderAt_const_ne_zero`)
and hence `f` is discharged.  The case `c = 0` cannot occur because
`MeromorphicNonzero.nonvanishing_germ` forbids the identically-zero germ.

These pieces produce the **case-split reduction**
`abelGeneratorPeriodCondition_of_forall_nonconst_toFun`:  closing
`AbelGeneratorPeriodCondition B` reduces to closing it on
`MeromorphicNonzero X` representatives whose underlying function is
*not* a constant.  All actual classical content (level-set chains,
Stokes) lives on that non-constant side. -/

/-- **Constant-function principal divisor is zero.** Any
`f : MeromorphicNonzero X` whose underlying function is the literal
constant `fun _ => c` with `c ≠ 0` has zero principal divisor.

Direct corollary of `mmeromorphicOrderAt_const_ne_zero`. -/
theorem principalDivisorMap_of_toFun_const
    (f : MeromorphicNonzero X) (c : ℂ) (hc : c ≠ 0)
    (hf : f.toFun = fun _ : X => c) :
    principalDivisorMap f = 0 := by
  classical
  ext x
  show JacobianChallenge.MMeromorphicOn.orderFun 𝓘(ℂ, ℂ) f.toFun x
      = (0 : Div X) x
  unfold JacobianChallenge.MMeromorphicOn.orderFun
  rw [hf, mmeromorphicOrderAt_const_ne_zero hc]
  rfl

/-- **Constant-function discharge.** `f.toFun = fun _ => c` with
`c ≠ 0` ⇒ `f ∈ dischargedGenerators`. -/
theorem toFun_const_mem_dischargedGenerators (B : AbelJacobiInput α h)
    {f : MeromorphicNonzero X} {c : ℂ} (hc : c ≠ 0)
    (hf : f.toFun = fun _ : X => c) :
    f ∈ B.dischargedGenerators :=
  B.mem_dischargedGenerators_of_principalDivisor_zero
    (principalDivisorMap_of_toFun_const f c hc hf)

/-- **The zero-germ obstruction.** `f.toFun` cannot equal the literal
constant `fun _ => 0` — by `mmeromorphicOrderAt_const` with `c = 0`
that would force `mmeromorphicOrderAt f.toFun x = ⊤`, violating
`f.nonvanishing_germ`. -/
theorem toFun_ne_const_zero (f : MeromorphicNonzero X) [Nonempty X] :
    f.toFun ≠ fun _ : X => (0 : ℂ) := by
  classical
  intro hf
  obtain ⟨x⟩ := ‹Nonempty X›
  apply f.nonvanishing_germ x
  show mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun x = ⊤
  rw [hf]
  show meromorphicOrderAt ((fun _ : X => (0 : ℂ)) ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) x) = ⊤
  have h_comp : ((fun _ : X => (0 : ℂ)) ∘ (chartAt ℂ x).symm)
      = (fun _ : ℂ => (0 : ℂ)) := rfl
  rw [h_comp, meromorphicOrderAt_const ((chartAt ℂ x) x) (0 : ℂ)]
  simp

/-- **Case-split reduction of `AbelGeneratorPeriodCondition`.** Closing
the per-generator period condition reduces to closing it on those
`f : MeromorphicNonzero X` whose underlying function is *not* a literal
constant — the case where genuine classical content
(level-set chains, Stokes) is required.

The constant-`toFun` case is closed unconditionally above via
`toFun_const_mem_dischargedGenerators`. -/
theorem abelGeneratorPeriodCondition_of_forall_nonconst_toFun
    (B : AbelJacobiInput α h)
    (h_nc : ∀ f : MeromorphicNonzero X,
              (∀ c : ℂ, f.toFun ≠ fun _ : X => c) →
                f ∈ B.dischargedGenerators) :
    AbelGeneratorPeriodCondition B := by
  intro f
  by_cases hexists : ∃ c : ℂ, f.toFun = fun _ : X => c
  · obtain ⟨c, hc⟩ := hexists
    by_cases hc_zero : c = 0
    · -- `c = 0` contradicts `nonvanishing_germ` via `toFun_ne_const_zero`.
      exfalso
      apply toFun_ne_const_zero f
      rw [hc, hc_zero]
    · exact B.toFun_const_mem_dischargedGenerators hc_zero hc
  · push Not at hexists
    exact h_nc f hexists

/-! ## Reduction of `AbelGeneratorPeriodCondition` to the discharged-set form -/

/-- **`AbelGeneratorPeriodCondition` ↔ universal discharge.** The
named-hypothesis content is exactly: every `f : MeromorphicNonzero X`
lies in `dischargedGenerators B`. -/
theorem abelGeneratorPeriodCondition_iff_dischargedGenerators_eq_univ
    (B : AbelJacobiInput α h) :
    AbelGeneratorPeriodCondition B ↔
      B.dischargedGenerators = (Set.univ : Set (MeromorphicNonzero X)) := by
  refine ⟨fun hCond => Set.eq_univ_of_forall fun f => hCond f, fun hUniv f => ?_⟩
  -- `hUniv : dischargedGenerators B = univ`; deduce membership for every `f`.
  have hmem : f ∈ B.dischargedGenerators := by rw [hUniv]; exact Set.mem_univ f
  exact hmem

/-- **One-step `AbelGeneratorPeriodCondition` from the discharged-set
form.** Unfolds the universally-quantified named hypothesis through
`dischargedGenerators`. -/
theorem abelGeneratorPeriodCondition_of_forall_mem_dischargedGenerators
    (B : AbelJacobiInput α h)
    (h_all : ∀ f : MeromorphicNonzero X, f ∈ B.dischargedGenerators) :
    AbelGeneratorPeriodCondition B := h_all

/-- **`AbelHypothesis` from universal discharge.** Composes
`abelGeneratorPeriodCondition_of_forall_mem_dischargedGenerators` with
the per-generator chain reduction
`abelHypothesis_of_abelGeneratorPeriodCondition`. -/
theorem abelHypothesis_of_forall_mem_dischargedGenerators
    (B : AbelJacobiInput α h)
    (h_all : ∀ f : MeromorphicNonzero X, f ∈ B.dischargedGenerators) :
    AbelHypothesis B :=
  abelHypothesis_of_abelGeneratorPeriodCondition B
    (B.abelGeneratorPeriodCondition_of_forall_mem_dischargedGenerators h_all)

end AbelJacobiInput

end JacobianChallenge

end
