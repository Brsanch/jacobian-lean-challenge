/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothCycle

/-! # Chain-difference is a cycle when the boundaries agree

Generalises `singleDiff_isCycle` from singleton-paths to arbitrary
smooth chains: if two `SmoothChain`s have the same `boundary`, their
difference lies in `SmoothCycle`.

This is the natural lemma to invoke whenever a chain is constructed
with a prescribed boundary in two different ways and one wants to
identify the resulting periods modulo the lattice. The application in
this repo: the regular-level-set chain
`f.regularLevelSetChain hnc h0 h∞` and the AJ chain
`principalDivisorAJChain (principalDivisorMap f)` have identical
boundaries (both equal `-principalDivisorMap f` viewed as a `Finsupp`),
so their difference is a cycle whose period vector is automatically a
period-lattice element. This is the structural reduction underlying
the residue-theorem step for `f_*ω` (chips `r-3`–`r-7`).

## What ships

* `chainDiff_isCycle` — `boundary c₁ = boundary c₂ ⇒ c₁ - c₂ ∈ SmoothCycle I X`.
* `smoothCycleOfChainDiff` — dependent-pair packaging.
* `smoothCycleOfChainDiff_coe` — coercion `simp`-rewrite.

No `sorry`, no `axiom`. -/

open scoped Manifold ContDiff Topology

noncomputable section

namespace JacobianChallenge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

/-- **Chain difference is a cycle.** If two smooth chains have the same
boundary, their difference is a smooth 1-cycle. -/
lemma chainDiff_isCycle
    {c₁ c₂ : SmoothChain I X}
    (h : SmoothChain.boundary c₁ = SmoothChain.boundary c₂) :
    c₁ - c₂ ∈ SmoothCycle I X := by
  rw [SmoothCycle.mem_iff, map_sub, h, sub_self]

/-- **Lift the chain difference to a `SmoothCycle`.** Packages
`chainDiff_isCycle` into the dependent-pair form. -/
def smoothCycleOfChainDiff
    {c₁ c₂ : SmoothChain I X}
    (h : SmoothChain.boundary c₁ = SmoothChain.boundary c₂) :
    SmoothCycle I X :=
  ⟨c₁ - c₂, chainDiff_isCycle h⟩

@[simp] lemma smoothCycleOfChainDiff_coe
    {c₁ c₂ : SmoothChain I X}
    (h : SmoothChain.boundary c₁ = SmoothChain.boundary c₂) :
    ((smoothCycleOfChainDiff h : SmoothCycle I X) : SmoothChain I X)
      = c₁ - c₂ := rfl

/-! ## Convenience: chain `≡` chain modulo a cycle.

`SmoothCycle.modCycle` is the equivalence relation `c₁ ~ c₂ ↔ c₁ - c₂ ∈
SmoothCycle`. For boundary-equal chains, this reduces to the same
boundary. We do not introduce the relation here — downstream users
prefer to reason directly with `chainDiff_isCycle` and a `let c := …`
binding. -/

end JacobianChallenge

end
