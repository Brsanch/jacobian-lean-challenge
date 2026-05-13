/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothCycle

/-! # `H₁`-style quotient via a named Stokes-boundary-invariance bundle
(chip PL-2bc)

This file packages the **factoring through `H₁`** content of the
period-lattice arc PL-2: given a smooth 1-cycle group `SmoothCycle I X`
and a real-side chain pairing, we want the pairing to descend to a quotient
`SmoothCycle / boundaries`, where `boundaries ≤ SmoothCycle` is the
subgroup of cycles that are "Stokes-boundaries" of higher-dimensional
chains (i.e. bound a 2-chain). On any compact orientable smooth surface
this quotient is `H₁(X; ℤ)`.

## Honest framing

The chip cannot prove `H₁`-invariance from a mathlib formalisation of
Stokes on a surface, because

1. mathlib at the pin (`8e3c989...`) does **not** ship Stokes' theorem
   for smooth chains on a compact manifold, and
2. the repo has **no** `Smooth2Chain` type at present — the natural
   `boundary₂ : Smooth2Chain →ₗ[ℤ] SmoothCycle` operator is unwritten.

We therefore follow the named-hypothesis pattern already used by
`StokesCompactSurfacePartitionOfUnity_hypothesis` in
`Manifold/StokesCompactSurface.lean`: bundle the data + the named gap
into a `structure`, and prove everything downstream of that structure
honestly. A consumer file plugs concrete witnesses in.

## Main definitions

* `StokesBoundaryInvariance I X` — a `structure` bundling
  * a Stokes-boundary subgroup `boundaries : AddSubgroup (SmoothCycle I X)`,
  * a `Submodule ℝ (SmoothOneForm I X)` of "Stokes-closed" 1-forms,
  * the **invariance hypothesis** `∀ c ∈ boundaries, ∀ ω ∈ closedForms,
    SmoothCycle.integrate c ω = 0`.
  No `axiom`, no `sorry`. A consumer file produces (or assumes) such a
  bundle when it has actual Stokes content; this file just records the
  algebraic consequences.

* `StokesBoundaryInvariance.H1` — the quotient
  `SmoothCycle I X ⧸ S.boundaries` as an `AddCommGroup`.

* `StokesBoundaryInvariance.periodPairing` — the factored real pairing
  `S.H1 → S.closedForms →+ ℝ` (additive in the chain argument; the
  ℝ-linearity in the form argument is the next layer).

* `StokesBoundaryInvariance.periodPairing_mk` — the diagram identity
  `periodPairing (mk c) ω = SmoothCycle.integrate c ω`, i.e. the pairing
  on a representative agrees with the chain-level integrate.

The complex-valued period pairing on `HolomorphicOneForm X` (using PL-1's
`realComponent` / `imagComponent`) is built in the sister file
`Manifold/PeriodPairingComplexCandidate.lean`.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

/-- Named-hypothesis bundle for `H₁`-factoring of the real-side period
pairing.

A consumer file that wants to invoke "the period pairing factors through
homology" supplies one of these:

* `boundaries` — a subgroup of cycles that the consumer interprets as
  Stokes-boundaries of 2-chains;
* `closedForms` — a submodule of 1-forms the consumer interprets as
  closed;
* `pairing_vanishes_on_boundaries` — the **invariance gap** : every
  closed form integrates to zero over every boundary cycle.

This file proves the algebraic consequence (the pairing factors through
the quotient) from those three inputs. The interpretation of `boundaries`
and `closedForms` and the proof of `pairing_vanishes_on_boundaries` are
the consumer's responsibility. -/
structure StokesBoundaryInvariance
    (I : ModelWithCorners ℝ E H) (X : Type*)
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X] where
  /-- The Stokes-boundary subgroup of `SmoothCycle I X`. Intended to be
  the image of a 2-chain boundary operator on a compact orientable
  surface; the consumer interprets it. -/
  boundaries : AddSubgroup (SmoothCycle I X)
  /-- The submodule of "Stokes-closed" 1-forms. Intended to be
  `{ω | dω = 0}` once exterior derivatives are wired. -/
  closedForms : Submodule ℝ (SmoothOneForm I X)
  /-- **Invariance hypothesis (the Stokes gap):** every Stokes-closed
  1-form integrates to zero around every Stokes-boundary cycle. This is
  exactly the content of Stokes' theorem applied to a 2-chain whose
  boundary is the given 1-cycle. The consumer file discharges this
  field. -/
  pairing_vanishes_on_boundaries :
    ∀ c ∈ boundaries, ∀ oneForm ∈ closedForms,
      SmoothCycle.integrate c oneForm = 0

namespace StokesBoundaryInvariance

variable (S : StokesBoundaryInvariance I X)

/-- The `H₁`-style quotient: smooth 1-cycles modulo Stokes-boundaries.
On a compact orientable surface and with `boundaries` interpreted as the
image of the 2-chain boundary, this is `H₁(X; ℤ) ⊗ ℝ`-shaped. -/
def H1 : Type _ := SmoothCycle I X ⧸ S.boundaries

instance : AddCommGroup S.H1 :=
  QuotientAddGroup.Quotient.addCommGroup _

/-- The quotient projection from cycles to `H₁`. -/
def proj : SmoothCycle I X →+ S.H1 :=
  QuotientAddGroup.mk' S.boundaries

@[simp] lemma proj_apply (c : SmoothCycle I X) :
    S.proj c = (QuotientAddGroup.mk c : S.H1) := rfl

/-- **Key lemma** — the chain-level pairing vanishes on the boundary
subgroup against any closed form. Direct repackaging of
`pairing_vanishes_on_boundaries`. -/
lemma integrate_eq_zero_of_boundary
    {c : SmoothCycle I X} (hc : c ∈ S.boundaries)
    {oneForm : SmoothOneForm I X} (hClosed : oneForm ∈ S.closedForms) :
    SmoothCycle.integrate c oneForm = 0 :=
  S.pairing_vanishes_on_boundaries c hc oneForm hClosed

/-- If two cycles differ by a Stokes-boundary, their pairing against any
closed form agrees. This is the "factor through `H₁`" content. -/
lemma integrate_eq_of_sub_mem_boundaries
    {c₁ c₂ : SmoothCycle I X}
    (h : c₁ - c₂ ∈ S.boundaries)
    {oneForm : SmoothOneForm I X} (hClosed : oneForm ∈ S.closedForms) :
    SmoothCycle.integrate c₁ oneForm = SmoothCycle.integrate c₂ oneForm := by
  have hzero :
      SmoothCycle.integrate (c₁ - c₂) oneForm = 0 :=
    S.integrate_eq_zero_of_boundary h hClosed
  have hsub :
      SmoothCycle.integrate (c₁ - c₂) oneForm
        = SmoothCycle.integrate c₁ oneForm - SmoothCycle.integrate c₂ oneForm := by
    unfold SmoothCycle.integrate
    rw [SmoothCycle.coe_sub]
    exact SmoothChain.integrate_sub (c₁ : SmoothChain I X)
      (c₂ : SmoothChain I X) oneForm
  linarith [hzero, hsub]

/-- The factored real pairing on `H₁ × closedForms`, expressed first as an
"underlying" `ℝ`-valued function on cycles+closed-forms. The descent to
the quotient is `Quotient.lift` below. -/
def integrateAux (c : SmoothCycle I X) (formCl : S.closedForms) : ℝ :=
  SmoothCycle.integrate c (formCl : SmoothOneForm I X)

lemma integrateAux_well_defined
    (c₁ c₂ : SmoothCycle I X) (hcc : c₁ - c₂ ∈ S.boundaries)
    (formCl : S.closedForms) :
    S.integrateAux c₁ formCl = S.integrateAux c₂ formCl := by
  unfold integrateAux
  exact S.integrate_eq_of_sub_mem_boundaries hcc formCl.property

/-- The factored real pairing `H₁ → closedForms → ℝ`. -/
def periodPairing : S.H1 → S.closedForms → ℝ := by
  intro hclass formCl
  refine Quotient.liftOn' hclass (fun c => S.integrateAux c formCl) ?_
  intro c₁ c₂ hcc
  have hmem : -c₁ + c₂ ∈ S.boundaries :=
    QuotientAddGroup.leftRel_apply.mp hcc
  have hmem' : c₂ - c₁ ∈ S.boundaries := by
    have : (-c₁ + c₂) = c₂ - c₁ := by abel
    rwa [this] at hmem
  symm
  exact S.integrateAux_well_defined c₂ c₁ hmem' formCl

/-- The diagram-commutativity identity: the factored pairing on the
quotient class of `c` equals the chain-level pairing. -/
@[simp] lemma periodPairing_mk
    (c : SmoothCycle I X) (formCl : S.closedForms) :
    S.periodPairing (S.proj c) formCl
      = SmoothCycle.integrate c (formCl : SmoothOneForm I X) := by
  rfl

/-- Linearity of the factored pairing in the form argument: zero. -/
@[simp] lemma periodPairing_zero_right (h : S.H1) :
    S.periodPairing h (0 : S.closedForms) = 0 := by
  refine Quotient.inductionOn' h ?_
  intro c
  show S.periodPairing (S.proj c) (0 : S.closedForms) = 0
  rw [periodPairing_mk]
  show SmoothCycle.integrate c (((0 : S.closedForms) : SmoothOneForm I X)) = 0
  have h0 : ((0 : S.closedForms) : SmoothOneForm I X) = 0 := rfl
  rw [h0, SmoothCycle.integrate_zero_right]

/-- Linearity of the factored pairing in the form argument: scalar.
(Additivity in the form argument requires `intervalIntegrable` witnesses
on `γ.integrand` per `SmoothPath.integrate_add`; that lemma is therefore
deferred to a chip that wires the chart-pullback integrability, and is
not part of PL-2.) -/
lemma periodPairing_smul_right (h : S.H1) (a : ℝ) (formCl : S.closedForms) :
    S.periodPairing h (a • formCl) = a * S.periodPairing h formCl := by
  refine Quotient.inductionOn' h ?_
  intro c
  show S.periodPairing (S.proj c) (a • formCl) = a * S.periodPairing (S.proj c) formCl
  rw [periodPairing_mk, periodPairing_mk]
  show SmoothCycle.integrate c ((a • formCl : S.closedForms) : SmoothOneForm I X)
      = a * SmoothCycle.integrate c (formCl : SmoothOneForm I X)
  have h_smul : ((a • formCl : S.closedForms) : SmoothOneForm I X)
      = a • (formCl : SmoothOneForm I X) := rfl
  rw [h_smul, SmoothCycle.integrate_smul_right]

/-- Linearity of the factored pairing in the chain argument: zero. -/
@[simp] lemma periodPairing_zero_left (formCl : S.closedForms) :
    S.periodPairing (0 : S.H1) formCl = 0 := by
  show S.periodPairing (S.proj 0) formCl = 0
  rw [periodPairing_mk]
  exact SmoothCycle.integrate_zero_left (formCl : SmoothOneForm I X)

/-- Linearity of the factored pairing in the chain argument: addition. -/
lemma periodPairing_add_left (h₁ h₂ : S.H1) (formCl : S.closedForms) :
    S.periodPairing (h₁ + h₂) formCl
      = S.periodPairing h₁ formCl + S.periodPairing h₂ formCl := by
  refine Quotient.inductionOn₂' h₁ h₂ ?_
  intro c₁ c₂
  show S.periodPairing (S.proj c₁ + S.proj c₂) formCl
      = S.periodPairing (S.proj c₁) formCl + S.periodPairing (S.proj c₂) formCl
  have h_add : S.proj c₁ + S.proj c₂ = S.proj (c₁ + c₂) := by
    rw [← map_add S.proj]
  rw [h_add, periodPairing_mk, periodPairing_mk, periodPairing_mk]
  exact SmoothCycle.integrate_add_left c₁ c₂ (formCl : SmoothOneForm I X)

/-- The factored pairing as an `AddMonoidHom` in the chain argument,
with the closed form held fixed. -/
def periodPairingHom (formCl : S.closedForms) : S.H1 →+ ℝ where
  toFun h := S.periodPairing h formCl
  map_zero' := S.periodPairing_zero_left formCl
  map_add' h₁ h₂ := S.periodPairing_add_left h₁ h₂ formCl

@[simp] lemma periodPairingHom_apply (formCl : S.closedForms) (h : S.H1) :
    S.periodPairingHom formCl h = S.periodPairing h formCl := rfl

@[simp] lemma periodPairingHom_mk (formCl : S.closedForms) (c : SmoothCycle I X) :
    S.periodPairingHom formCl (S.proj c)
      = SmoothCycle.integrate c (formCl : SmoothOneForm I X) := by
  rw [periodPairingHom_apply, periodPairing_mk]

end StokesBoundaryInvariance

end JacobianChallenge

end
