/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelGeneratorInputIndependence
import JacobianChallenge.Manifold.MeromorphicNonzeroAbelGeneratorFromLevelSet

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Final C3 reduction: `AbelHypothesis B ← AbelLatticeWitness X α h`

C3 — `AbelHypothesis B` for an arbitrary `B : AbelJacobiInput α h` — reduces
to a single named classical input: **the Abel-forward existence statement**

```
AbelLatticeWitness X α h :=
  ∀ f : MeromorphicNonzero X, (∀ c : ℂ, f.toFun ≠ fun _ => c) →
    ∃ Z : SmoothChain 𝓘(ℝ, ℂ) X,
      (∀ x : X, (SmoothChain.boundary Z).toFun x
          = -((principalDivisorMap f : X → ℤ) x)) ∧
      complexChainPeriodVector α Z
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α
```

i.e. for every meromorphic function `f` whose underlying `f.toFun`
is not a literal constant, a smooth chain `Z` exists whose boundary
identifies with `-principalDivisorMap f` (Stokes side of Abel forward)
and whose period vector along the basis `α` is a lattice element
(period-quantisation side of Abel forward).

The constant-`toFun` case is handled internally by the chip: if
`f.toFun = fun _ => c`, then `c ≠ 0` (because `toFun_ne_const_zero`),
`principalDivisorMap f = 0` (`principalDivisorMap_of_toFun_const`), and
`Z := 0` discharges both clauses of `h_struct` trivially.

The chip therefore packages **the named classical input for Abel
forward** in the cleanest form: one universally-quantified existence
statement, parametrised only by `X`, `α`, and `h` (NOT by the
`AbelJacobiInput` choice). Per
`AbelGeneratorInputIndependence.lean`, the conclusion `AbelHypothesis B`
holds for every `B` once it holds for one — hence the chip ships the
"any-`B`" variant as well.

## Status against the project map

`CLOSURE_MAP.md §F.0 / OPEN.md §"C3 sub-arc"` describe C3's remaining
content as

> only the global identification (Lebesgue subdivision over
> sheet-domain cover) + Stokes/residue argument for the lattice clause
> remain.

That residual analytical content is exactly `AbelLatticeWitness`.
Discharging `AbelLatticeWitness` is the classical Abel-forward theorem
on a compact connected Riemann surface — pushforward 1-form `f_*ω`
construction + residue/Stokes on `ℙ¹`. The chip below reduces C3 in
full to that single classical input.

`f_*ω` infrastructure is in place pointwise (`MeromorphicNonzeroTraceAt`,
`CotangentPullbackAt`, `SmoothOneFormOn`, `SourceFiberPathSheetEq`, ...).
Sequencing a global integral identity and the residue argument on
ℙ¹ remains future work; this chip's role is to identify that residual
work as the **single** named input and to compose all the upstream
infrastructure into a one-line invocation site.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Submodule Module

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] [PreconnectedSpace X] [Nonempty X]

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α}

/-! ## Named Abel-forward lattice witness -/

/-- **Abel-forward lattice witness.** For every `f : MeromorphicNonzero X`
whose underlying `f.toFun` is not a literal constant, there exists a
smooth 1-chain `Z` with boundary `-principalDivisorMap f` (pointwise)
and period vector in `periodLatticeImage`.

This is the **single named classical input** that C3 reduces to.
Discharging it is the analytic content of Abel forward: build the
level-set chain of `f` (or perturb to a chain compatible with regular
values) and verify the lattice-quantisation of its period vector via
the pushforward-1-form `f_*ω` integral identity + Stokes/residue on
`ℙ¹`. -/
def AbelLatticeWitness
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] [PreconnectedSpace X] [Nonempty X]
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (_h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α) :
    Prop :=
  ∀ f : MeromorphicNonzero X, (∀ c : ℂ, f.toFun ≠ fun _ : X => c) →
    ∃ Z : SmoothChain 𝓘(ℝ, ℂ) X,
      (∀ x : X, (SmoothChain.boundary Z).toFun x
          = -((principalDivisorMap f : X → ℤ) x)) ∧
      complexChainPeriodVector α Z
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α

/-! ## Constant-`toFun` discharge (private workhorse) -/

/-- Internal: for `f` with `f.toFun = fun _ => c`, `Z := 0` discharges
both clauses of `h_struct` in `abelGeneratorPeriodCondition_of_levelSet_lattice`.

Used in `h_struct_of_AbelLatticeWitness` below. -/
private lemma h_struct_summand_of_toFun_const
    (f : MeromorphicNonzero X) {c : ℂ} (hf : f.toFun = fun _ : X => c) :
    ∃ Z : SmoothChain 𝓘(ℝ, ℂ) X,
      (∀ x : X, (SmoothChain.boundary Z).toFun x
          = -((principalDivisorMap f : X → ℤ) x)) ∧
      complexChainPeriodVector α Z
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α := by
  -- Reduce `c = 0` to contradiction via `toFun_ne_const_zero`.
  by_cases hc_zero : c = 0
  · exfalso
    apply AbelJacobiInput.toFun_ne_const_zero f
    rw [hf, hc_zero]
  · -- `c ≠ 0` ⇒ `principalDivisorMap f = 0` ⇒ `Z := 0` works.
    have h_pd_zero : principalDivisorMap f = 0 :=
      AbelJacobiInput.principalDivisorMap_of_toFun_const f c hc_zero hf
    refine ⟨(0 : SmoothChain 𝓘(ℝ, ℂ) X), ?_, ?_⟩
    · intro x
      have hpd : (principalDivisorMap f : X → ℤ) x = 0 := by
        rw [h_pd_zero]; rfl
      rw [hpd, SmoothChain.boundary_zero, neg_zero]
      rfl
    · rw [complexChainPeriodVector_zero α]
      exact zero_mem _

/-! ## Universal `h_struct` discharge from `AbelLatticeWitness` -/

/-- **`h_struct` from `AbelLatticeWitness`.** Combines the named
existence hypothesis on non-constant `f` with the internal
constant-`toFun` discharge. -/
theorem h_struct_of_AbelLatticeWitness
    (hW : AbelLatticeWitness X α h) :
    ∀ f : MeromorphicNonzero X,
      ∃ Z : SmoothChain 𝓘(ℝ, ℂ) X,
        (∀ x : X, (SmoothChain.boundary Z).toFun x
            = -((principalDivisorMap f : X → ℤ) x)) ∧
        complexChainPeriodVector α Z
          ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α := by
  intro f
  by_cases hexists : ∃ c : ℂ, f.toFun = fun _ : X => c
  · obtain ⟨c, hc⟩ := hexists
    exact h_struct_summand_of_toFun_const f hc
  · push Not at hexists
    exact hW f hexists

/-! ## Final C3 reduction -/

/-- **Final C3 reduction: `AbelHypothesis B` follows from
`AbelLatticeWitness X α h`.** Composes
`h_struct_of_AbelLatticeWitness`,
`MeromorphicNonzero.abelGeneratorPeriodCondition_of_levelSet_lattice`,
and `abelHypothesis_of_abelGeneratorPeriodCondition`.

After this theorem, C3 — `AbelHypothesis B` for any
`B : AbelJacobiInput α h` — reduces to the single named classical
input `AbelLatticeWitness X α h` (the Abel-forward existence statement
for non-constant meromorphic functions). -/
theorem AbelJacobiInput.abelHypothesis_of_AbelLatticeWitness
    (B : AbelJacobiInput α h)
    (hW : AbelLatticeWitness X α h) :
    AbelHypothesis B :=
  abelHypothesis_of_abelGeneratorPeriodCondition B
    (MeromorphicNonzero.abelGeneratorPeriodCondition_of_levelSet_lattice B
      (h_struct_of_AbelLatticeWitness hW))

/-- **`B`-invariant C3 reduction.** Combines
`abelHypothesis_of_AbelLatticeWitness` with the `AbelJacobiInput`
invariance of `AbelLatticeWitness` (which has no `B` dependence by
construction): a single discharge of `AbelLatticeWitness X α h`
yields `AbelHypothesis B` for **every** `B : AbelJacobiInput α h`. -/
theorem AbelJacobiInput.forall_abelHypothesis_of_AbelLatticeWitness
    (hW : AbelLatticeWitness X α h) :
    ∀ B : AbelJacobiInput α h, AbelHypothesis B :=
  fun B => B.abelHypothesis_of_AbelLatticeWitness hW

end JacobianChallenge

end
