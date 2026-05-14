/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiPic0
import JacobianChallenge.Manifold.AbelHypothesisGenusZero

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Reduction of `AbelHypothesis` to a chain-level period condition

`AbelHypothesis B` (Abel forward direction, `Manifold/AbelJacobiPic0.lean`)
asserts that `B.abelJacobiDiv0Hom` vanishes on every principal divisor.
Classically this is the content of Abel's theorem.

This file provides a chain-level reduction. For each divisor `D : Div X`,
we define an explicit `principalDivisorAJChain B D : SmoothChain 𝓘(ℝ, ℂ) X`
— the formal ℤ-linear combination `Σ D(x) • single (B.pathFromBase x)`
indexed by `D.supportFinset`. By linearity of `abelJacobiChain`,

    `abelJacobiChain α h (principalDivisorAJChain B D) = abelJacobiDivHom B D`,

so the question "is `abelJacobiDivHom D` zero in `AnalyticJacobian`?"
reduces to "is `complexChainPeriodVector α (principalDivisorAJChain D)` in
`periodLatticeImage`?". The named-hypothesis version of *that* statement is

    `AbelChainPeriodCondition B : Prop`,

and `abelHypothesis_of_abelChainPeriodCondition` discharges `AbelHypothesis`
from it. This concretely names the remaining classical content of `C3` —
the open work is now stating-and-proving the period condition for all
principal divisors, which is exactly Abel forward via Stokes / level-set
chain tracing.

## What ships

* `AbelJacobiInput.principalDivisorAJChain B D` — the explicit Abel-Jacobi
  chain for any `D : Div X`, built as a formal ℤ-linear combination of
  the base-point paths from `B`. (Boundary behaviour is implicit; on
  `D : Div0 X` the boundary equals `D` viewed as a 0-chain.)
* `abelJacobiChain_principalDivisorAJChain_eq_abelJacobiDivHom` — the
  diagram identity routing the chain through the AJ formalism.
* `AbelChainPeriodCondition B : Prop` — the named reduction
  hypothesis: for every principal divisor `D`, the period vector of its
  AJ chain lies in `periodLatticeImage`.
* `abelHypothesis_of_abelChainPeriodCondition` — the reduction.

After this file, C3's open content is precisely
`AbelChainPeriodCondition B`. The classical Abel proof discharges it via
the level-set chain of a meromorphic representative `f` with `D = div(f)`;
this is a separate sub-chip and remains open at the mathlib pin.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff
open Submodule Module Finset

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

namespace AbelJacobiInput

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α}

/-- **The Abel-Jacobi chain of a divisor.** For `D : Div X`, the formal
ℤ-linear combination `Σ D(x) • single (B.pathFromBase x)` over
`D.supportFinset`. For `D : Div0 X` (deg-zero), the boundary of this
chain is `D` as a 0-chain (Σ D(x) = 0 cancels the `δ_{P₀}` contributions).

The point: by linearity of `abelJacobiChain`, this chain maps under
`abelJacobiChain α h` to `B.abelJacobiDivHom D`. So the question of
whether the AJ-image of `D` is `0` (in `AnalyticJacobian`) reduces to
whether the period vector of this chain lies in `periodLatticeImage`. -/
noncomputable def principalDivisorAJChain (B : AbelJacobiInput α h)
    (D : Div X) : SmoothChain 𝓘(ℝ, ℂ) X :=
  ∑ x ∈ D.supportFinset, ((D : X → ℤ) x) • SmoothChain.single (B.pathFromBase x)

/-- **Compute on any containing finset.** Values outside the support
contribute zero (since `D(x) = 0` ⇒ `0 • _ = 0`). -/
lemma principalDivisorAJChain_eq_sum_of_supportFinset_subset
    (B : AbelJacobiInput α h) {D : Div X} {S : Finset X}
    (hS : D.supportFinset ⊆ S) :
    B.principalDivisorAJChain D
      = ∑ x ∈ S, ((D : X → ℤ) x) • SmoothChain.single (B.pathFromBase x) := by
  classical
  unfold principalDivisorAJChain
  refine Finset.sum_subset hS ?_
  intro x _ hxS
  rw [Div.apply_eq_zero_of_notMem_supportFinset hxS]
  exact zero_smul ℤ (SmoothChain.single (B.pathFromBase x))

@[simp] lemma principalDivisorAJChain_zero (B : AbelJacobiInput α h) :
    B.principalDivisorAJChain (0 : Div X) = 0 := by
  classical
  unfold principalDivisorAJChain
  have hempty : (0 : Div X).supportFinset = (∅ : Finset X) := by
    unfold Div.supportFinset
    apply Finset.eq_empty_iff_forall_notMem.2
    intro x hx
    have hx' : x ∈ ((0 : Div X) : X → ℤ).support :=
      (Set.Finite.mem_toFinset _).1 hx
    have hsupp : ((0 : Div X) : X → ℤ).support = (∅ : Set X) := by
      ext y; simp
    rw [hsupp] at hx'
    exact hx'.elim
  rw [hempty]
  exact Finset.sum_empty

/-! ## Additivity of the principal-divisor AJ chain -/

/-- **Additivity.** `principalDivisorAJChain` is additive in the divisor:
`principalDivisorAJChain (D₁ + D₂) = principalDivisorAJChain D₁ +
principalDivisorAJChain D₂`. Standard `Finset.sum_subset` + `add_smul`
manipulation. -/
lemma principalDivisorAJChain_add (B : AbelJacobiInput α h) (D₁ D₂ : Div X) :
    B.principalDivisorAJChain (D₁ + D₂)
      = B.principalDivisorAJChain D₁ + B.principalDivisorAJChain D₂ := by
  classical
  set S : Finset X :=
    (D₁ + D₂).supportFinset ∪ D₁.supportFinset ∪ D₂.supportFinset with hS_def
  have h12 : (D₁ + D₂).supportFinset ⊆ S := by
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have h1 : D₁.supportFinset ⊆ S := by
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have h2 : D₂.supportFinset ⊆ S := by
    intro x hx
    exact Finset.mem_union_right _ hx
  rw [B.principalDivisorAJChain_eq_sum_of_supportFinset_subset h12,
      B.principalDivisorAJChain_eq_sum_of_supportFinset_subset h1,
      B.principalDivisorAJChain_eq_sum_of_supportFinset_subset h2]
  have hpt : ∀ x : X, ((D₁ + D₂ : Div X) : X → ℤ) x
      = (D₁ : X → ℤ) x + (D₂ : X → ℤ) x := by
    intro x
    simp [Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
  rw [show (∑ x ∈ S,
            ((D₁ + D₂ : Div X) : X → ℤ) x • SmoothChain.single (B.pathFromBase x))
        = ∑ x ∈ S,
            ((D₁ : X → ℤ) x + (D₂ : X → ℤ) x)
              • SmoothChain.single (B.pathFromBase x) from by
        refine Finset.sum_congr rfl ?_
        intro x _; rw [hpt]]
  rw [show (∑ x ∈ S,
            ((D₁ : X → ℤ) x + (D₂ : X → ℤ) x)
              • SmoothChain.single (B.pathFromBase x))
        = ∑ x ∈ S,
            ((D₁ : X → ℤ) x • SmoothChain.single (B.pathFromBase x)
              + (D₂ : X → ℤ) x • SmoothChain.single (B.pathFromBase x)) from by
        refine Finset.sum_congr rfl ?_
        intro x _
        exact _root_.add_smul (D₁ x) (D₂ x) (SmoothChain.single (B.pathFromBase x))]
  exact Finset.sum_add_distrib

/-- **Bundled `AddMonoidHom` form** of `principalDivisorAJChain`. -/
noncomputable def principalDivisorAJChainHom (B : AbelJacobiInput α h) :
    Div X →+ SmoothChain 𝓘(ℝ, ℂ) X where
  toFun := B.principalDivisorAJChain
  map_zero' := B.principalDivisorAJChain_zero
  map_add' := B.principalDivisorAJChain_add

@[simp] lemma principalDivisorAJChainHom_apply (B : AbelJacobiInput α h)
    (D : Div X) :
    B.principalDivisorAJChainHom D = B.principalDivisorAJChain D := rfl

/-! ## Diagram identity: chain → AJ -/

/-- **The diagram identity.** `abelJacobiChain` applied to
`principalDivisorAJChain D` equals `abelJacobiDivHom D`. Both sides
unfold to `Σ D(x) • abelJacobiPoint x`. -/
theorem abelJacobiChain_principalDivisorAJChain_eq_abelJacobiDivHom
    (B : AbelJacobiInput α h) (D : Div X) :
    abelJacobiChain α h (B.principalDivisorAJChain D)
      = B.abelJacobiDivHom D := by
  classical
  show abelJacobiChain α h
      (∑ x ∈ D.supportFinset, ((D : X → ℤ) x) • SmoothChain.single (B.pathFromBase x))
    = B.abelJacobiDiv D
  -- Distribute `abelJacobiChain` through the finite sum.
  rw [map_sum]
  unfold abelJacobiDiv
  refine Finset.sum_congr rfl ?_
  intro x _
  -- ℤ-scalar multiplication on AddMonoidHom: `f (n • a) = n • f a`.
  rw [show (abelJacobiChain α h)
      ((D : X → ℤ) x • SmoothChain.single (B.pathFromBase x))
        = (D : X → ℤ) x • (abelJacobiChain α h) (SmoothChain.single (B.pathFromBase x))
    from AddMonoidHom.map_zsmul (abelJacobiChain α h) _ _]
  -- `abelJacobiChain (single γ_x) = abelJacobiPoint x` via `abelJacobiChain_single`.
  rw [abelJacobiChain_single]
  rfl

/-! ## Period-vector form -/

/-- **Period vector of the AJ chain.** Unfolds the chain through
`complexChainPeriodVectorHom` and the ℤ-linearity over the finite
support. Used as the right-hand side of the named-hypothesis Prop
below. -/
lemma complexChainPeriodVector_principalDivisorAJChain
    (B : AbelJacobiInput α h) (D : Div X) :
    complexChainPeriodVector α (B.principalDivisorAJChain D)
      = ∑ x ∈ D.supportFinset,
          ((D : X → ℤ) x) •
            complexChainPeriodVector α (SmoothChain.single (B.pathFromBase x)) := by
  classical
  show complexChainPeriodVectorHom α (B.principalDivisorAJChain D)
    = ∑ x ∈ D.supportFinset,
        ((D : X → ℤ) x) •
          complexChainPeriodVectorHom α (SmoothChain.single (B.pathFromBase x))
  unfold principalDivisorAJChain
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro x _
  exact AddMonoidHom.map_zsmul (complexChainPeriodVectorHom α) _ _

/-! ## Reduction of `AbelHypothesis` to a chain-level period condition -/

/-- **Named-hypothesis reduction of `AbelHypothesis`.** Asserts that
for every principal divisor `D : Div0 X`, the period vector of its
AJ chain `principalDivisorAJChain B (D : Div X)` lies in the period
lattice image.

Classical content: this is exactly **Abel forward**. For a principal
divisor `D = div(f)`, the period vector decomposes as an integer
combination of basis periods of `α`, hence lies in `periodLatticeImage`.
The decomposition is the level-set-chain construction of `f` (a Stokes
argument on `f : X → RiemannSphere`). -/
def AbelChainPeriodCondition (B : AbelJacobiInput α h) : Prop :=
  ∀ D : Div0 X, (D : Div X) ∈ PrincDiv X →
    complexChainPeriodVector α (B.principalDivisorAJChain (D : Div X))
      ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α

/-- **`AbelHypothesis` from the chain-level period condition.** Given
the named hypothesis `AbelChainPeriodCondition B`, every principal
divisor's AJ-image in `AnalyticJacobian` is `0` (since its period
vector class is `0` in the quotient). -/
theorem abelHypothesis_of_abelChainPeriodCondition
    (B : AbelJacobiInput α h)
    (hPer : AbelChainPeriodCondition B) :
    AbelHypothesis B := by
  intro D hPrinc
  -- Reduce to: abelJacobiDivHom (D : Div X) = 0 in AnalyticJacobian.
  show B.abelJacobiDiv0Hom D = (0 : AnalyticJacobian _ α h)
  rw [abelJacobiDiv0Hom_apply]
  -- `abelJacobiDiv D = abelJacobiDivHom D` (definitional unfold).
  show (B.abelJacobiDivHom (D : Div X) : AnalyticJacobian _ α h) = 0
  -- Replace `abelJacobiDivHom D` by `abelJacobiChain (principalDivisorAJChain D)`.
  rw [← abelJacobiChain_principalDivisorAJChain_eq_abelJacobiDivHom]
  -- Now goal: abelJacobiChain α h (principalDivisorAJChain B (D : Div X)) = 0
  -- Use the same idiom as `abelJacobiChain_cycle_eq_zero`: change to the
  -- explicit `QuotientAddGroup.mk` form, then `QuotientAddGroup.eq_zero_iff`.
  change (QuotientAddGroup.mk
            (complexChainPeriodVector α (B.principalDivisorAJChain (D : Div X))) :
          AnalyticJacobian _ α h) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  rw [PeriodLatticeOfRankTwoG.ofBundle_lattice]
  exact hPer D hPrinc

/-! ## Closure properties of `AbelChainPeriodCondition`

`PrincDiv X` is an `AddSubgroup` of `Div X` via `PrincDivHonestCandidate`.
The lemmas below show that the `complexChainPeriodVector` membership in
`periodLatticeImage` propagates through addition and negation. Combined
with the `AddSubgroup` structure of `PrincDiv X`, this means a future
discharge of `AbelChainPeriodCondition` can proceed by reducing to a
generating set of `PrincDiv X` (the principal divisors of single
meromorphic functions, `div(f)`).
-/

/-- **Closure under addition.** If `AbelChainPeriodCondition` is known
on a Div0-pair `(D₁, D₂)` of principal divisors, it descends to their
sum `D₁ + D₂`. Two ingredients:

* Additivity of the AJ chain (`principalDivisorAJChain_add`),
* `periodLatticeImage` is an `AddSubgroup` (closed under addition).

This is the algebraic skeleton that lets a future discharge of
`AbelChainPeriodCondition` proceed by reducing to a *generating set*
of `PrincDiv X` (the principal divisors of single meromorphic
functions, `div(f)`). -/
theorem complexChainPeriodVector_principalDivisorAJChain_add_mem
    (B : AbelJacobiInput α h)
    {D₁ D₂ : Div X}
    (h₁ : complexChainPeriodVector α (B.principalDivisorAJChain D₁)
            ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α)
    (h₂ : complexChainPeriodVector α (B.principalDivisorAJChain D₂)
            ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α) :
    complexChainPeriodVector α (B.principalDivisorAJChain (D₁ + D₂))
      ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α := by
  rw [B.principalDivisorAJChain_add]
  -- `complexChainPeriodVector` is additive (it's `complexChainPeriodVectorHom`-applied).
  rw [show complexChainPeriodVector α
        (B.principalDivisorAJChain D₁ + B.principalDivisorAJChain D₂)
      = complexChainPeriodVector α (B.principalDivisorAJChain D₁)
        + complexChainPeriodVector α (B.principalDivisorAJChain D₂) from
        complexChainPeriodVector_add α _ _]
  exact AddSubgroup.add_mem _ h₁ h₂

/-- **Closure under negation.** -/
theorem complexChainPeriodVector_principalDivisorAJChain_neg_mem
    (B : AbelJacobiInput α h)
    {D : Div X}
    (hD : complexChainPeriodVector α (B.principalDivisorAJChain D)
            ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α) :
    complexChainPeriodVector α (B.principalDivisorAJChain (-D))
      ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α := by
  -- `principalDivisorAJChain (-D) = -principalDivisorAJChain D` by additivity.
  have h_sum_zero :
      B.principalDivisorAJChain D + B.principalDivisorAJChain (-D) = 0 := by
    rw [← B.principalDivisorAJChain_add, add_neg_cancel,
        B.principalDivisorAJChain_zero]
  have h_neg : B.principalDivisorAJChain (-D) = -B.principalDivisorAJChain D :=
    eq_neg_of_add_eq_zero_right h_sum_zero
  rw [h_neg]
  -- `complexChainPeriodVector α (-c) = -complexChainPeriodVector α c`.
  have h_pv_sum :
      complexChainPeriodVector α (B.principalDivisorAJChain D)
        + complexChainPeriodVector α (-B.principalDivisorAJChain D) = 0 := by
    rw [← complexChainPeriodVector_add α, add_neg_cancel,
        complexChainPeriodVector_zero α]
  have h_neg_pv :
      complexChainPeriodVector α (-B.principalDivisorAJChain D)
        = -complexChainPeriodVector α (B.principalDivisorAJChain D) :=
    eq_neg_of_add_eq_zero_right h_pv_sum
  rw [h_neg_pv]
  exact AddSubgroup.neg_mem _ hD

/-! ## Reduction to single-meromorphic-function generators

`PrincDiv X = AddSubgroup.closure (Set.range principalDivisorMap)`
(see `Divisor/PrincipalDivisorRange.lean`), so every element of
`PrincDiv X` is a finite integer combination of `principalDivisorMap f`
for `f : MeromorphicNonzero X`. Together with the closure of the
period-vector condition under addition and negation, this lets us
reduce `AbelChainPeriodCondition` to a per-generator statement.
-/

/-- **Per-generator period condition.** For every meromorphic nonzero
`f : MeromorphicNonzero X`, the period vector of the AJ chain of the
principal divisor `(f) = principalDivisorMap f` lies in
`periodLatticeImage`.

This is the **atomic** form of Abel forward: closing C3 in full
amounts to discharging this single statement, one meromorphic
function at a time. -/
def AbelGeneratorPeriodCondition (B : AbelJacobiInput α h) : Prop :=
  ∀ f : MeromorphicNonzero X,
    complexChainPeriodVector α (B.principalDivisorAJChain (principalDivisorMap f))
      ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α

/-- **Reduction to generators.** `AbelGeneratorPeriodCondition B` is
strictly weaker than `AbelChainPeriodCondition B`; this proof shows
the implication.

Closure induction on `PrincDiv X = AddSubgroup.closure
(Set.range principalDivisorMap)` uses three steps:

* Generators: by hypothesis.
* Identity (zero divisor): `principalDivisorAJChain 0 = 0`, whose
  period vector is `0 ∈ periodLatticeImage`.
* Closure under negation and addition: the algebra-side lemmas
  above (`complexChainPeriodVector_principalDivisorAJChain_neg_mem`,
  `_add_mem`).

Since `D ∈ PrincDiv X ↔ (D : Div X) ∈ closure (Set.range
principalDivisorMap)`, `AbelChainPeriodCondition` follows.
-/
theorem abelChainPeriodCondition_of_abelGeneratorPeriodCondition
    (B : AbelJacobiInput α h)
    (hGen : AbelGeneratorPeriodCondition B) :
    AbelChainPeriodCondition B := by
  intro D hD
  -- `(D : Div X) ∈ PrincDiv X = AddSubgroup.closure (Set.range principalDivisorMap)`.
  change (D : Div X) ∈ PrincDivHonestCandidate X at hD
  unfold PrincDivHonestCandidate at hD
  -- Induct on the closure. Use a named motive to keep beta-reduction clean.
  let P : (E : Div X) → E ∈ AddSubgroup.closure (Set.range (principalDivisorMap (X := X)))
          → Prop :=
    fun E _ => complexChainPeriodVector α (B.principalDivisorAJChain E)
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α
  change P (D : Div X) hD
  refine AddSubgroup.closure_induction (p := P) ?_ ?_ ?_ ?_ hD
  · -- Generators: `E = principalDivisorMap f` for some `f`.
    rintro E ⟨f, hf⟩
    show complexChainPeriodVector α (B.principalDivisorAJChain E)
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α
    rw [← hf]
    exact hGen f
  · -- Zero case.
    show complexChainPeriodVector α (B.principalDivisorAJChain (0 : Div X))
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α
    rw [B.principalDivisorAJChain_zero, complexChainPeriodVector_zero α]
    exact zero_mem _
  · -- Sum case.
    intro E₁ E₂ _hE₁ _hE₂ hP₁ hP₂
    show complexChainPeriodVector α (B.principalDivisorAJChain (E₁ + E₂))
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α
    exact complexChainPeriodVector_principalDivisorAJChain_add_mem B hP₁ hP₂
  · -- Negation case.
    intro E _hE hP
    show complexChainPeriodVector α (B.principalDivisorAJChain (-E))
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α
    exact complexChainPeriodVector_principalDivisorAJChain_neg_mem B hP

/-- **`AbelHypothesis` from per-generator period condition.** Composes
`abelChainPeriodCondition_of_abelGeneratorPeriodCondition` with the
chain-level reduction. After this lemma, closing C3 fully reduces to
discharging `AbelGeneratorPeriodCondition` for an arbitrary
`f : MeromorphicNonzero X` — the cleanest form of Abel forward. -/
theorem abelHypothesis_of_abelGeneratorPeriodCondition
    (B : AbelJacobiInput α h)
    (hGen : AbelGeneratorPeriodCondition B) :
    AbelHypothesis B :=
  abelHypothesis_of_abelChainPeriodCondition B
    (abelChainPeriodCondition_of_abelGeneratorPeriodCondition B hGen)

/-! ## Verifying the chain-level reduction on the genus-0 corner -/

/-- **Sanity check.** At genus 0 the chain-level condition is trivially
satisfied: `Fin 0 → ℂ` is the zero group, so any element lies in any
subgroup. -/
theorem abelChainPeriodCondition_of_genus_zero
    (B : AbelJacobiInput α h)
    (hgenus : JacobianChallenge.genus X = 0) :
    AbelChainPeriodCondition B := by
  intro D _hPrinc
  -- `complexChainPeriodVector α (...) : Fin (genus X) → ℂ`; at genus 0
  -- this is a subsingleton group, so every element lies in every subgroup.
  haveI : Subsingleton (Fin (JacobianChallenge.genus X) → ℂ) :=
    subsingleton_pi_fin_genus_zero (X := X) hgenus
  -- Show membership by exhibiting `0` as the element (subsingleton ⇒ any = 0).
  have h0 : complexChainPeriodVector α (B.principalDivisorAJChain (D : Div X))
      = 0 := Subsingleton.elim _ _
  rw [h0]
  exact zero_mem _

end AbelJacobiInput

end JacobianChallenge

end
