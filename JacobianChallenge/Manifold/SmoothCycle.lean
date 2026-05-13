/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothChain
import JacobianChallenge.Manifold.SmoothChainBoundary
import JacobianChallenge.Manifold.SmoothPathIntegral
import JacobianChallenge.Manifold.SmoothChainIntegralLinearity
import JacobianChallenge.Manifold.PeriodPairingFromSmoothChain

/-! # Smooth 1-cycles (chip PL-2a)

A *smooth 1-cycle* is a smooth 1-chain with zero boundary, i.e. an element of
`ker(SmoothChain.boundary)`. The cycle group `SmoothCycle I X` is the natural
domain of the period pairing once we want it to descend to homology: the
pairing on the chain side already exists (`SmoothPathIntegral.integrate`, and
its bundled form `smoothChain_realOneForm_pairing` in
`PeriodPairingFromSmoothChain.lean`), and the cycle group is the kernel of
the chain-level boundary the next chips will quotient out by Stokes-boundaries.

## Main definitions

* `SmoothCycle I X : AddSubgroup (SmoothChain I X)` — the kernel of the
  `ℤ`-linear boundary `SmoothChain I X →ₗ[ℤ] (X →₀ ℤ)`.
* `SmoothCycle.integrate : SmoothCycle I X → SmoothOneForm I X → ℝ` — the
  restriction of `SmoothChain.integrate` to cycles, packaged so downstream
  Stokes-invariance and H₁-quotient chips have a stable name.
* `SmoothCycle.integratePairingHom (ω) : SmoothCycle I X →+ ℝ` — the
  additive-group hom in the cycle argument with `ω` held fixed.

This file is pure algebra on `SmoothChain` plus integration linearity; it
does not invoke Stokes' theorem. The Stokes-boundary equivalence and the
H₁ quotient live in the sister files `SmoothCycleClosedFormPairing.lean`,
`StokesBoundaryInvariance.lean`, and `H1SmoothMod.lean`.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

/-- The smooth 1-cycle group on `X` (with model `I`): the kernel of the
`ℤ`-linear boundary map `SmoothChain I X →ₗ[ℤ] (X →₀ ℤ)`. Concretely,
`c ∈ SmoothCycle I X` iff `SmoothChain.boundary c = 0`. -/
def SmoothCycle (I : ModelWithCorners ℝ E H) (X : Type*)
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X] :
    AddSubgroup (SmoothChain I X) :=
  (SmoothChain.boundary (I := I) (X := X)).ker.toAddSubgroup

namespace SmoothCycle

/-- Membership in `SmoothCycle` is exactly `boundary c = 0`. -/
@[simp] lemma mem_iff {c : SmoothChain I X} :
    c ∈ SmoothCycle I X ↔ SmoothChain.boundary c = 0 := by
  unfold SmoothCycle
  rfl

/-- The zero chain is a cycle. -/
lemma zero_mem : (0 : SmoothChain I X) ∈ SmoothCycle I X :=
  (SmoothCycle I X).zero_mem

/-- The sum of two cycles is a cycle. -/
lemma add_mem {c₁ c₂ : SmoothChain I X}
    (h₁ : c₁ ∈ SmoothCycle I X) (h₂ : c₂ ∈ SmoothCycle I X) :
    c₁ + c₂ ∈ SmoothCycle I X :=
  (SmoothCycle I X).add_mem h₁ h₂

/-- The negation of a cycle is a cycle. -/
lemma neg_mem {c : SmoothChain I X} (h : c ∈ SmoothCycle I X) :
    -c ∈ SmoothCycle I X :=
  (SmoothCycle I X).neg_mem h

/-- The difference of two cycles is a cycle. -/
lemma sub_mem {c₁ c₂ : SmoothChain I X}
    (h₁ : c₁ ∈ SmoothCycle I X) (h₂ : c₂ ∈ SmoothCycle I X) :
    c₁ - c₂ ∈ SmoothCycle I X :=
  (SmoothCycle I X).sub_mem h₁ h₂

/-- The `ℤ`-scaling of a cycle is a cycle. -/
lemma zsmul_mem (n : ℤ) {c : SmoothChain I X} (h : c ∈ SmoothCycle I X) :
    n • c ∈ SmoothCycle I X :=
  (SmoothCycle I X).zsmul_mem h n

/-- Coercion `SmoothCycle I X → SmoothChain I X` distributes over zero. -/
@[simp, norm_cast] lemma coe_zero :
    ((0 : SmoothCycle I X) : SmoothChain I X) = 0 := rfl

/-- Coercion distributes over addition. -/
@[simp, norm_cast] lemma coe_add (c₁ c₂ : SmoothCycle I X) :
    ((c₁ + c₂ : SmoothCycle I X) : SmoothChain I X)
      = (c₁ : SmoothChain I X) + (c₂ : SmoothChain I X) := rfl

/-- Coercion distributes over negation. -/
@[simp, norm_cast] lemma coe_neg (c : SmoothCycle I X) :
    ((-c : SmoothCycle I X) : SmoothChain I X) = -(c : SmoothChain I X) := rfl

/-- Coercion distributes over subtraction. -/
@[simp, norm_cast] lemma coe_sub (c₁ c₂ : SmoothCycle I X) :
    ((c₁ - c₂ : SmoothCycle I X) : SmoothChain I X)
      = (c₁ : SmoothChain I X) - (c₂ : SmoothChain I X) :=
  AddSubgroup.coe_sub _ c₁ c₂

/-- The defining property of `SmoothCycle`: the boundary of any cycle's
underlying chain is the zero 0-chain. -/
@[simp] lemma boundary_toChain (c : SmoothCycle I X) :
    SmoothChain.boundary (c : SmoothChain I X) = 0 := by
  have h : (c : SmoothChain I X) ∈ SmoothCycle I X := c.property
  rwa [mem_iff] at h

/-- The pairing of a 0-chain with a function `f : X → ℝ` vanishes on the
boundary of a cycle. Useful when the function is the chart-pullback of a
closed 1-form's "potential" in a Stokes argument. -/
lemma evalPoints_boundary_toChain (c : SmoothCycle I X) (f : X → ℝ) :
    SmoothChain.evalPoints (SmoothChain.boundary (c : SmoothChain I X)) f = 0 := by
  rw [boundary_toChain, SmoothChain.evalPoints_zero]

/-- Real-valued integration of a smooth 1-cycle against a smooth real
1-form: the restriction of `SmoothChain.integrate` to cycles. -/
def integrate (c : SmoothCycle I X) (oneForm : SmoothOneForm I X) : ℝ :=
  SmoothChain.integrate (c : SmoothChain I X) oneForm

@[simp] lemma integrate_eq (c : SmoothCycle I X) (oneForm : SmoothOneForm I X) :
    integrate c oneForm = SmoothChain.integrate (c : SmoothChain I X) oneForm := rfl

@[simp] lemma integrate_zero_left (oneForm : SmoothOneForm I X) :
    integrate (0 : SmoothCycle I X) oneForm = 0 := by
  unfold integrate
  rw [coe_zero, SmoothChain.integrate_zero]

lemma integrate_add_left (c₁ c₂ : SmoothCycle I X) (oneForm : SmoothOneForm I X) :
    integrate (c₁ + c₂) oneForm = integrate c₁ oneForm + integrate c₂ oneForm := by
  unfold integrate
  rw [coe_add, SmoothChain.integrate_add]

@[simp] lemma integrate_zero_right (c : SmoothCycle I X) :
    integrate c (0 : SmoothOneForm I X) = 0 := by
  have := smoothChain_realOneForm_pairing_zero_right (I := I) (X := X) (c : SmoothChain I X)
  unfold smoothChain_realOneForm_pairing at this
  exact this

lemma integrate_smul_right (c : SmoothCycle I X) (a : ℝ)
    (oneForm : SmoothOneForm I X) :
    integrate c (a • oneForm) = a * integrate c oneForm := by
  simp only [integrate]
  have := smoothChain_realOneForm_pairing_smul_right (c : SmoothChain I X) a oneForm
  unfold smoothChain_realOneForm_pairing at this
  exact this

/-- The cycle-side real pairing as an additive hom in the cycle argument,
with the 1-form held fixed. This is the cycle-restricted analogue of
`smoothChain_realOneForm_pairingHom` from
`PeriodPairingFromSmoothChain.lean`. -/
def integratePairingHom (oneForm : SmoothOneForm I X) :
    SmoothCycle I X →+ ℝ where
  toFun c := integrate c oneForm
  map_zero' := integrate_zero_left oneForm
  map_add' c₁ c₂ := integrate_add_left c₁ c₂ oneForm

@[simp] lemma integratePairingHom_apply (oneForm : SmoothOneForm I X)
    (c : SmoothCycle I X) :
    integratePairingHom oneForm c = integrate c oneForm := rfl

end SmoothCycle

end JacobianChallenge

end
