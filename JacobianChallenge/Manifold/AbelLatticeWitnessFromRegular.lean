/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelHypothesisFromLatticeWitness
import JacobianChallenge.Manifold.MeromorphicNonzeroConcreteLevelSetChain
import JacobianChallenge.Manifold.MeromorphicNonzeroConstantBridge

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Splitting `AbelLatticeWitness` into regular-case lattice + critical perturbation

`AbelLatticeWitness X α h` quantifies over **every** non-constant `f`. The
`regularLevelSetChain f hnc h0 h∞` infrastructure gives a concrete witness
chain (with the boundary clause discharged via
`boundary_regularLevelSetChain`) **only when `0` and `∞` are both regular
values of `f`**. For `f` whose `0` or `∞` is a critical value, the
existing infrastructure doesn't supply a chain directly — the classical
move is a Möbius substitution.

This chip exposes the cleavage: it reduces `AbelLatticeWitness` to two
strictly smaller named hypotheses:

* **`RegularLevelSetLatticeClause X α h`** — for every non-constant `f`
  with `0, ∞` regular, the period vector of `regularLevelSetChain f hnc h0 h∞`
  is in `periodLatticeImage`. This is the pushforward-1-form +
  Stokes/residue content (the substantive analytic core of Abel forward).
* **`AbelLatticeWitnessCriticalCase X α h`** — for every non-constant `f`
  with `0` or `∞` critical, a chain `Z` with the boundary and lattice
  properties exists. Classically dischargeable by a Möbius substitution
  reducing to the regular case.

Together, the two named hypotheses imply `AbelLatticeWitness`, and
therefore via `abelHypothesis_of_AbelLatticeWitness`,
`AbelHypothesis B` for every `B`.

The substantive analytic content is now concentrated in
`RegularLevelSetLatticeClause` — the cleanest single statement of
"period vector of the regular level-set chain is a basis-period sum".

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter Submodule Module
open scoped Manifold ContDiff Topology

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] [PreconnectedSpace X] [Nonempty X]

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α}

/-! ## The two smaller named hypotheses -/

/-- **Regular-case lattice clause.** For every non-constant
`f : MeromorphicNonzero X` with `0` and `∞` both regular values, the
period vector of `regularLevelSetChain f hnc h0 h∞` lies in
`periodLatticeImage`.

This is the **substantive analytic content** of Abel forward, isolated
to the case where the chain construction succeeds directly.

Discharging this is the residue/Stokes argument: the period vector
factors through the pushforward 1-form `f_*ω` on `ℙ¹`, whose integral
along `β : 0 → ∞` (avoiding critical values) is determined by the
residues of `f_*ω` and lifts to a ℤ-combination of basis periods of
`α` on `X`. -/
def RegularLevelSetLatticeClause
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] [PreconnectedSpace X] [Nonempty X]
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (_h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α) :
    Prop :=
  ∀ (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (h0_reg : (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet)
    (h_inf_reg : (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet),
    complexChainPeriodVector α (f.regularLevelSetChain hnc h0_reg h_inf_reg)
      ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α

/-- **Critical-case witness.** For every non-constant
`f : MeromorphicNonzero X` whose `0` or `∞` is a critical value (or
both), a smooth 1-chain `Z` with boundary `-principalDivisorMap f` and
period vector in `periodLatticeImage` exists.

Classically dischargeable via a Möbius substitution that moves a pair
of regular values of `f` to `(0, ∞)` and uses
`regularLevelSetChain` on the transformed function; the lift back is
the small residual analytic content not covered by
`RegularLevelSetLatticeClause`. -/
def AbelLatticeWitnessCriticalCase
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] [PreconnectedSpace X] [Nonempty X]
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (_h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α) :
    Prop :=
  ∀ f : MeromorphicNonzero X,
    ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere →
    (((0 : ℂ) : RiemannSphere)) ∉ f.regularValueSet ∨
      (OnePoint.infty : RiemannSphere) ∉ f.regularValueSet →
    ∃ Z : SmoothChain 𝓘(ℝ, ℂ) X,
      (∀ x : X, (SmoothChain.boundary Z).toFun x
          = -((principalDivisorMap f : X → ℤ) x)) ∧
      complexChainPeriodVector α Z
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α

/-! ## Discharge of the regular case from the lattice clause -/

/-- **Regular-case discharge.** For non-constant `f` with `0` and `∞`
regular, `Z := regularLevelSetChain f hnc h0 h∞` is the witness:

* Boundary: by `boundary_regularLevelSetChain` (step 7d-d composition).
* Lattice clause: by `RegularLevelSetLatticeClause`. -/
theorem MeromorphicNonzero.exists_lattice_witness_of_regular
    (hRL : RegularLevelSetLatticeClause X α h)
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (h0_reg : (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet)
    (h_inf_reg : (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet) :
    ∃ Z : SmoothChain 𝓘(ℝ, ℂ) X,
      (∀ x : X, (SmoothChain.boundary Z).toFun x
          = -((principalDivisorMap f : X → ℤ) x)) ∧
      complexChainPeriodVector α Z
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α := by
  refine ⟨f.regularLevelSetChain hnc h0_reg h_inf_reg, ?_, ?_⟩
  · exact f.boundary_regularLevelSetChain hnc h0_reg h_inf_reg
  · exact hRL f hnc h0_reg h_inf_reg

/-! ## `AbelLatticeWitness` from the split -/

/-- **`AbelLatticeWitness` from the regular + critical split.** For each
non-constant `f` (with `f.toFun` not a literal constant), the regular
case discharges via `RegularLevelSetLatticeClause`; the critical case
discharges via `AbelLatticeWitnessCriticalCase`. The bridge from
`toFun`-nonconstancy to `toRiemannSphere`-nonconstancy is
`not_isConstantMap_toRiemannSphere_of_toFun_nonconst`. -/
theorem AbelLatticeWitness_of_split
    (hRL : RegularLevelSetLatticeClause X α h)
    (hCR : AbelLatticeWitnessCriticalCase X α h) :
    AbelLatticeWitness X α h := by
  intro f hf
  -- Bridge to `toRiemannSphere`-nonconstancy.
  have hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere :=
    f.not_isConstantMap_toRiemannSphere_of_toFun_nonconst hf
  -- Case-split on whether `0` and `∞` are both regular for `f`.
  by_cases h0_reg : (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet
  · by_cases h_inf_reg : (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet
    · -- Regular case: use the lattice clause.
      exact f.exists_lattice_witness_of_regular hRL hnc h0_reg h_inf_reg
    · -- ∞ is critical: critical case.
      exact hCR f hnc (Or.inr h_inf_reg)
  · -- 0 is critical: critical case.
    exact hCR f hnc (Or.inl h0_reg)

/-! ## Final composition: `AbelHypothesis B` from the split -/

/-- **C3 from the split.** For every `B : AbelJacobiInput α h`,
`AbelHypothesis B` follows from the two named hypotheses
`RegularLevelSetLatticeClause` (the substantive analytic core) and
`AbelLatticeWitnessCriticalCase` (the small Möbius-perturbation residual). -/
theorem AbelJacobiInput.abelHypothesis_of_split
    (B : AbelJacobiInput α h)
    (hRL : RegularLevelSetLatticeClause X α h)
    (hCR : AbelLatticeWitnessCriticalCase X α h) :
    AbelHypothesis B :=
  B.abelHypothesis_of_AbelLatticeWitness (AbelLatticeWitness_of_split hRL hCR)

/-- **`B`-invariant C3 from the split.** A single discharge of the
named-hypothesis pair `(RegularLevelSetLatticeClause, AbelLatticeWitnessCriticalCase)`
yields `AbelHypothesis B` for every `B : AbelJacobiInput α h`. -/
theorem AbelJacobiInput.forall_abelHypothesis_of_split
    (hRL : RegularLevelSetLatticeClause X α h)
    (hCR : AbelLatticeWitnessCriticalCase X α h) :
    ∀ B : AbelJacobiInput α h, AbelHypothesis B :=
  fun B => B.abelHypothesis_of_split hRL hCR

end JacobianChallenge

end
