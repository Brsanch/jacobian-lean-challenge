/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodPairingDataFromSmoothCycle
import JacobianChallenge.Manifold.JacobianOfLatticeFromBundle
import JacobianChallenge.Manifold.SmoothChainIntegralLinearity

set_option diagnostics.threshold 100

/-! # PL-4-A: Pathwise Abel-Jacobi class with path-independence

The Abel-Jacobi map sends a point `Q : X` (relative to a base point
`P₀ : X`) to the class

    `[(∫_{P₀}^{Q} α_j)_j ∈ Fin g → ℂ] mod periodLatticeImage`,

where `α : Basis (Fin g) ℂ (HolomorphicOneForm X)` is a chosen basis.
The class is independent of the choice of path from `P₀` to `Q`,
because two such paths differ by a smooth closed cycle whose period
vector lies in `periodLatticeImage` by definition.

This chip provides the **pointwise** AJ map and the **path-independence**
theorem under the canonical smooth-cycle `PeriodPairingData`. Concretely:

* `complexChainPeriod : SmoothChain 𝓘(ℝ, ℂ) X → HolomorphicOneForm X → ℂ`
  — chain-level complex period (generalises `complexPeriod` on cycles to
  arbitrary chains).
* `complexChainPeriodVector data α c : Fin g → ℂ` — vector of complex
  periods of a chain against a ℂ-basis of holomorphic 1-forms.
* `singleDiff_isCycle` — for paths `γ, γ'` with shared endpoints,
  `SmoothChain.single γ - SmoothChain.single γ'` is a smooth 1-cycle
  (boundary cancels exactly).
* `abelJacobiPath` — given a basis bundle and a smooth path `γ : P → Q`,
  produces a class in `AnalyticJacobian data α h`.
* `abelJacobiPath_eq_of_shared_endpoints` — the key path-independence
  theorem: two paths with the same endpoints give the same AJ class.

This is the **first PL-4 chip**. Subsequent PL-4 chips will:

* Extend to chains (`abelJacobiChain : SmoothChain → ...`) by ℤ-linearity.
* Extend to divisors (`abelJacobiDiv : Div X → ...`).
* Restrict to degree-0 divisors and prove Abel's theorem (factoring
  through principal divisors) — requires Stokes on a 2-chain.
* Descend through `Pic0 X` to give the full Abel-Jacobi map.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff
open Submodule Module

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ⊤ X]

/-! ## Chain-level complex period -/

/-- **Chain-level complex period.** The complex period of a holomorphic
1-form along a smooth 1-chain (not necessarily closed). Generalises
`complexPeriod` (which restricts to cycles) by using
`SmoothChain.integrate` directly. -/
def complexChainPeriod (c : SmoothChain 𝓘(ℝ, ℂ) X)
    (om : HolomorphicOneForm X) : ℂ :=
  ((SmoothChain.integrate c (realComponent om) : ℝ) : ℂ)
    + Complex.I * ((SmoothChain.integrate c (imagComponent om) : ℝ) : ℂ)

@[simp] lemma complexChainPeriod_zero_left (om : HolomorphicOneForm X) :
    complexChainPeriod (0 : SmoothChain 𝓘(ℝ, ℂ) X) om = 0 := by
  unfold complexChainPeriod
  rw [SmoothChain.integrate_zero, SmoothChain.integrate_zero]
  push_cast
  ring

lemma complexChainPeriod_add_left
    (c₁ c₂ : SmoothChain 𝓘(ℝ, ℂ) X) (om : HolomorphicOneForm X) :
    complexChainPeriod (c₁ + c₂) om
      = complexChainPeriod c₁ om + complexChainPeriod c₂ om := by
  unfold complexChainPeriod
  rw [SmoothChain.integrate_add, SmoothChain.integrate_add]
  push_cast
  ring

lemma complexChainPeriod_neg_left
    (c : SmoothChain 𝓘(ℝ, ℂ) X) (om : HolomorphicOneForm X) :
    complexChainPeriod (-c) om = -complexChainPeriod c om := by
  unfold complexChainPeriod
  rw [SmoothChain.integrate_neg, SmoothChain.integrate_neg]
  push_cast
  ring

lemma complexChainPeriod_sub_left
    (c₁ c₂ : SmoothChain 𝓘(ℝ, ℂ) X) (om : HolomorphicOneForm X) :
    complexChainPeriod (c₁ - c₂) om
      = complexChainPeriod c₁ om - complexChainPeriod c₂ om := by
  rw [sub_eq_add_neg, complexChainPeriod_add_left,
    complexChainPeriod_neg_left]
  ring

/-- **Restriction to cycles matches `complexPeriod`.** When the chain is
a smooth cycle, the chain-level period equals the existing cycle-level
period `complexPeriod`. -/
lemma complexChainPeriod_of_cycle
    (c : SmoothCycle 𝓘(ℝ, ℂ) X) (om : HolomorphicOneForm X) :
    complexChainPeriod (c : SmoothChain 𝓘(ℝ, ℂ) X) om = complexPeriod c om := by
  show _ = ((SmoothCycle.integrate c (realComponent om) : ℝ) : ℂ)
    + Complex.I * ((SmoothCycle.integrate c (imagComponent om) : ℝ) : ℂ)
  rfl

/-! ## Chain period vector against a basis -/

variable (data : PeriodPairingData X)

/-- **Chain period vector against a ℂ-basis.** For a smooth 1-chain `c`
and a basis `α : Fin g → HolomorphicOneForm X`, produces the vector of
complex periods. -/
def complexChainPeriodVector
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (c : SmoothChain 𝓘(ℝ, ℂ) X) : Fin (JacobianChallenge.genus X) → ℂ :=
  fun j => complexChainPeriod c (α j)

@[simp] lemma complexChainPeriodVector_zero
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)) :
    complexChainPeriodVector α (0 : SmoothChain 𝓘(ℝ, ℂ) X) = 0 := by
  funext j
  show complexChainPeriod (0 : SmoothChain 𝓘(ℝ, ℂ) X) (α j) = 0
  exact complexChainPeriod_zero_left (α j)

lemma complexChainPeriodVector_sub
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (c₁ c₂ : SmoothChain 𝓘(ℝ, ℂ) X) :
    complexChainPeriodVector α (c₁ - c₂)
      = complexChainPeriodVector α c₁ - complexChainPeriodVector α c₂ := by
  funext j
  show complexChainPeriod (c₁ - c₂) (α j)
      = complexChainPeriod c₁ (α j) - complexChainPeriod c₂ (α j)
  exact complexChainPeriod_sub_left c₁ c₂ (α j)

/-- **Cycle-form chain period vector equals `periodVector` through
`ofSmoothCycle`.** When `data = PeriodPairingData.ofSmoothCycle X`, the
chain period vector restricted to a smooth cycle agrees with the
abstract `periodVector` of that cycle. -/
lemma complexChainPeriodVector_of_cycle_eq_periodVector
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (c : SmoothCycle 𝓘(ℝ, ℂ) X) :
    complexChainPeriodVector α (c : SmoothChain 𝓘(ℝ, ℂ) X)
      = periodVector (PeriodPairingData.ofSmoothCycle X) α c := by
  funext j
  show complexChainPeriod (c : SmoothChain 𝓘(ℝ, ℂ) X) (α j)
      = PeriodPairing (PeriodPairingData.ofSmoothCycle X) c (α j)
  rw [complexChainPeriod_of_cycle, PeriodPairing_ofSmoothCycle]

/-! ## Single-chain difference is a cycle when endpoints match -/

/-- **Key boundary identity.** For two smooth paths with shared endpoints,
the difference `single γ - single γ'` has zero boundary, hence is a
smooth 1-cycle.

Proof: `boundary (single γ) = δ_{γ.tgt} - δ_{γ.src}` and similarly for
`γ'`. With matching endpoints, the difference cancels exactly. -/
lemma singleDiff_isCycle
    {γ γ' : SmoothPath 𝓘(ℝ, ℂ) X}
    (hsrc : γ.src = γ'.src) (htgt : γ.tgt = γ'.tgt) :
    SmoothChain.single γ - SmoothChain.single γ' ∈ SmoothCycle 𝓘(ℝ, ℂ) X := by
  rw [SmoothCycle.mem_iff]
  show SmoothChain.boundary
      (SmoothChain.single γ - SmoothChain.single γ') = 0
  rw [map_sub]
  simp only [SmoothChain.boundary_single]
  show (Finsupp.single γ.tgt 1 - Finsupp.single γ.src 1) -
       (Finsupp.single γ'.tgt 1 - Finsupp.single γ'.src 1) = 0
  rw [hsrc, htgt]
  exact sub_self _

/-- **Lift the singleton-difference to a `SmoothCycle`.** Packages
`singleDiff_isCycle` into the dependent-pair form. -/
def smoothCycleOfPathDiff
    {γ γ' : SmoothPath 𝓘(ℝ, ℂ) X}
    (hsrc : γ.src = γ'.src) (htgt : γ.tgt = γ'.tgt) :
    SmoothCycle 𝓘(ℝ, ℂ) X :=
  ⟨SmoothChain.single γ - SmoothChain.single γ', singleDiff_isCycle hsrc htgt⟩

@[simp] lemma smoothCycleOfPathDiff_coe
    {γ γ' : SmoothPath 𝓘(ℝ, ℂ) X}
    (hsrc : γ.src = γ'.src) (htgt : γ.tgt = γ'.tgt) :
    ((smoothCycleOfPathDiff hsrc htgt : SmoothCycle 𝓘(ℝ, ℂ) X) :
      SmoothChain 𝓘(ℝ, ℂ) X)
      = SmoothChain.single γ - SmoothChain.single γ' := rfl

/-! ## Path period vector difference is in the period image -/

/-- **Key Abel-Jacobi well-definedness lemma.** For two smooth paths
with shared endpoints, the difference of their path period vectors
(against any chosen basis) lies in the period image of the
canonical smooth-cycle `PeriodPairingData`. -/
theorem complexChainPeriodVector_single_diff_mem_periodLatticeImage
    {γ γ' : SmoothPath 𝓘(ℝ, ℂ) X}
    (hsrc : γ.src = γ'.src) (htgt : γ.tgt = γ'.tgt)
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)) :
    complexChainPeriodVector α (SmoothChain.single γ)
      - complexChainPeriodVector α (SmoothChain.single γ')
      ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle X) α := by
  -- The difference equals the chain-period of `single γ - single γ'`,
  -- which (by `singleDiff_isCycle`) is a cycle, and its image under
  -- `periodVector` lies in the period image by definition.
  rw [← complexChainPeriodVector_sub]
  -- Goal: complexChainPeriodVector α (single γ - single γ')
  --       ∈ periodLatticeImage (ofSmoothCycle X) α
  -- View the chain as the underlying chain of the cycle witness.
  let c : SmoothCycle 𝓘(ℝ, ℂ) X := smoothCycleOfPathDiff hsrc htgt
  have h_coe : (c : SmoothChain 𝓘(ℝ, ℂ) X)
      = SmoothChain.single γ - SmoothChain.single γ' := rfl
  rw [← h_coe]
  rw [complexChainPeriodVector_of_cycle_eq_periodVector]
  -- Goal: periodVector (ofSmoothCycle X) α c
  --       ∈ periodLatticeImage (ofSmoothCycle X) α
  exact ⟨c, rfl⟩

/-! ## The pathwise Abel-Jacobi class -/

variable {data}

/-- **Pathwise Abel-Jacobi class.** Given a basis `α`, a smooth path
`γ : P₀ → Q`, and a discreteness bundle `h`, this map sends `γ` to its
period vector mod the period lattice. Path-independence (for paths with
shared endpoints) is `abelJacobiPath_eq_of_shared_endpoints` below. -/
def abelJacobiPath
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α)
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) :
    AnalyticJacobian (PeriodPairingData.ofSmoothCycle X) α h :=
  QuotientAddGroup.mk
    (complexChainPeriodVector α (SmoothChain.single γ))

/-- **Path-independence of the Abel-Jacobi class.** Two smooth paths
with shared endpoints determine the same class in the analytic
Jacobian, because their period-vector difference lies in the period
image by `complexChainPeriodVector_single_diff_mem_periodLatticeImage`. -/
theorem abelJacobiPath_eq_of_shared_endpoints
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α)
    {γ γ' : SmoothPath 𝓘(ℝ, ℂ) X}
    (hsrc : γ.src = γ'.src) (htgt : γ.tgt = γ'.tgt) :
    abelJacobiPath α h γ = abelJacobiPath α h γ' := by
  change (QuotientAddGroup.mk (complexChainPeriodVector α (SmoothChain.single γ))
        : AnalyticJacobian _ α h)
      = QuotientAddGroup.mk (complexChainPeriodVector α (SmoothChain.single γ'))
  rw [QuotientAddGroup.eq]
  -- Goal: -v_γ + v_γ' ∈ (PeriodLatticeOfRankTwoG.ofBundle ...).lattice
  -- Rewrite the lattice (via ofBundle_lattice : `.lattice = periodLatticeImage data α`).
  rw [PeriodLatticeOfRankTwoG.ofBundle_lattice]
  -- Goal: -complexChainPeriodVector α (single γ) + complexChainPeriodVector α (single γ')
  --       ∈ periodLatticeImage (ofSmoothCycle X) α
  -- = -(v_γ - v_γ'). The negative-membership identity.
  rw [neg_add_eq_sub]
  -- Goal: complexChainPeriodVector α (single γ') - complexChainPeriodVector α (single γ)
  --       ∈ periodLatticeImage ...
  -- Apply the well-definedness lemma with γ and γ' swapped.
  exact complexChainPeriodVector_single_diff_mem_periodLatticeImage
    (γ := γ') (γ' := γ) hsrc.symm htgt.symm α

/-! ## PL-4-B: chain-level Abel-Jacobi as `AddMonoidHom`

The pathwise class extends ℤ-linearly to a chain-level map, sending
each smooth 1-chain `c` to `[complexChainPeriodVector α c] mod lattice`.
On `single γ` it reduces to `abelJacobiPath α h γ`. -/

/-- **Chain-level period-vector additivity.** -/
lemma complexChainPeriodVector_add
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (c₁ c₂ : SmoothChain 𝓘(ℝ, ℂ) X) :
    complexChainPeriodVector α (c₁ + c₂)
      = complexChainPeriodVector α c₁ + complexChainPeriodVector α c₂ := by
  funext j
  show complexChainPeriod (c₁ + c₂) (α j)
      = complexChainPeriod c₁ (α j) + complexChainPeriod c₂ (α j)
  exact complexChainPeriod_add_left c₁ c₂ (α j)

/-- **Chain period vector as an `AddMonoidHom`.** Bundles
`complexChainPeriodVector` together with the zero and add identities. -/
def complexChainPeriodVectorHom
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)) :
    SmoothChain 𝓘(ℝ, ℂ) X →+ (Fin (JacobianChallenge.genus X) → ℂ) where
  toFun := complexChainPeriodVector α
  map_zero' := complexChainPeriodVector_zero α
  map_add' := complexChainPeriodVector_add α

@[simp] lemma complexChainPeriodVectorHom_apply
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (c : SmoothChain 𝓘(ℝ, ℂ) X) :
    complexChainPeriodVectorHom α c = complexChainPeriodVector α c := rfl

/-- **Chain-level Abel-Jacobi map.** Composes the chain period vector
with the quotient projection
`(Fin g → ℂ) →+ AnalyticJacobian data α h`. Sends a smooth 1-chain to
its period-vector class. -/
def abelJacobiChain
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α) :
    SmoothChain 𝓘(ℝ, ℂ) X →+ AnalyticJacobian (PeriodPairingData.ofSmoothCycle X) α h :=
  (QuotientAddGroup.mk' (PeriodLatticeOfRankTwoG.ofBundle
    (PeriodPairingData.ofSmoothCycle X) α h).lattice).comp
      (complexChainPeriodVectorHom α)

@[simp] lemma abelJacobiChain_apply
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α)
    (c : SmoothChain 𝓘(ℝ, ℂ) X) :
    abelJacobiChain α h c
      = QuotientAddGroup.mk (complexChainPeriodVector α c) := rfl

/-- **`abelJacobiChain` on `single γ` equals `abelJacobiPath`.** -/
@[simp] lemma abelJacobiChain_single
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α)
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) :
    abelJacobiChain α h (SmoothChain.single γ) = abelJacobiPath α h γ := rfl

/-- **`abelJacobiChain` vanishes on cycles whose period vector is in the
lattice** — in particular, vanishes on cycles whose period vector
matches `periodVector` of some cycle (always true via `ofSmoothCycle`,
so every cycle's period image *equals* its lattice image). -/
lemma abelJacobiChain_cycle_eq_zero
    (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α)
    (c : SmoothCycle 𝓘(ℝ, ℂ) X) :
    abelJacobiChain α h (c : SmoothChain 𝓘(ℝ, ℂ) X) = 0 := by
  change (QuotientAddGroup.mk
            (complexChainPeriodVector α (c : SmoothChain 𝓘(ℝ, ℂ) X)) :
          AnalyticJacobian _ α h) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  rw [PeriodLatticeOfRankTwoG.ofBundle_lattice]
  rw [complexChainPeriodVector_of_cycle_eq_periodVector]
  -- Goal: periodVector (ofSmoothCycle X) α c ∈ periodLatticeImage (ofSmoothCycle X) α
  exact ⟨c, rfl⟩

end JacobianChallenge

end
