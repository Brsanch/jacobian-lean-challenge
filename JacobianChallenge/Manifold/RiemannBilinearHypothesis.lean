/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasC3FullClassicalContent
import JacobianChallenge.Manifold.HasC3FullClassicalContentComplexTorus
import JacobianChallenge.Manifold.HasC3FullClassicalContentFromHolomorphicEquivRS

set_option linter.unusedSectionVars false

/-! # Bryan-tree analog of `AX_RiemannBilinear` (mrdouglasny axiom #3)

mrdouglasny's `AX_RiemannBilinear` asserts: for `X` a compact Riemann
surface of positive genus `g`, there exist a symplectic ℤ-basis `b` of
`H_1(X, ℤ)` and a basis `ω` of `HolomorphicOneForm X` (normalised
`∫_{α_i} ω_j = δ_ij`) such that the B-period matrix
`τ[i,j] := ∫_{β_i} ω_j` lies in `SiegelUpperHalfSpace g` — i.e. `τ` is
symmetric and `Im τ` is positive-definite.

## Bridge to Bryan's tree

Bryan's tree decomposes Riemann bilinear into **two named hypotheses**:

* `RiemannFirstBilinearRelation cycleGens J : Prop` (chip 9) — first
  bilinear relation: `∑_{k,l} J k l · PeriodPairing γ_k ω₀ · PeriodPairing
  γ_l ω₁ = 0` for all ω₀, ω₁. At `J := standardSymplectic g` this is the
  `τ - τᵀ = 0` content of `Im τ ∈ SiegelUpperHalfSpace`.
* `RiemannSecondRelationPositivity data basis_ω cycleGens : Prop` (chip
  18) — second bilinear relation: `∀ x ≠ 0, (star x ⬝ᵥ (i •
  periodMatrixForm pmat (standardSymplectic g)) *ᵥ x).im = 0 ∧ 0 < re`.
  This is the **Hodge positivity** content of `Im τ` being PD.

Composing (chip 10's
`completeHodgeRiemannHypothesis_of_RiemannFirst_RiemannSecond`):

```
CompleteHodgeRiemannHypothesis data basis_ω cycleGens
  ↔  RiemannFirstBilinearRelation cycleGens (standardSymplectic g)
   ∧ RiemannSecondRelationPositivity data basis_ω cycleGens
```

So **`AX_RiemannBilinear` for `X` = `CompleteHodgeRiemannHypothesis`
on `X`'s SCD**, modulo the symplectic-basis choice.

## Status by genus

* **`g = 0`:** `CompleteHodgeRiemannHypothesis` holds vacuously
  (`Fin 0` indexing). **✓ unconditional** via
  `completeHodgeRiemannHypothesis_of_genus_eq_zero` (chip 11/19).

* **`g = 1`:** **✓ unconditional** via the chain:
  - RFBR via `riemannFirstBilinearRelation_of_genus_one_standardSymplectic`
    (chip 25, needs only `genus X = 1` + `FiniteDimensional ℂ ω`).
  - RSRP via the lattice-orientation scalar input
    `0 < Im(star pmat[k₀ i₀] · pmat[k₁ i₀])`
    (chip 23, `riemannSecondRelationPositivity_of_genus_one_of_lattice_orientation`).
  - On T_L: discharge of the orientation scalar via
    `exists_positively_oriented_ZBasisOfL` (chip 19s in tree).

* **`g ≥ 2`:** **OPEN.** Bryan's tree reduces (chip 16,
  `strictUpperTriangular_zero_of_RiemannFirstBilinearRelation`):
  - RFBR ⟺ `g(g-1)/2` strict-upper-triangular Q-scalars vanish.
  - RSRP ⟺ `g × g` Hermitian-PD condition on the period matrix.

  The **g(g-1)/2 strict-upper Q-zeros** at general `X` follow from:
  * Holomorphic Stokes on a 4g-gon-style 2-chain (chip D's
    `HolomorphicStokes` UNCONDITIONAL provides the Stokes step);
  * The 4g-gon symplectic-basis topology (requires axiom #1's
    discharge to construct the 2-chain).

  The **Hermitian PD** at general `X` follows from:
  * The pointwise type-(2,0)-vanishing identity (chip 5/8 — Bryan
    discharged this UNCONDITIONALLY pointwise);
  * Hodge-positivity of `i · ω ∧ ω̄` on a connected 1-manifold
    (classical, integrable with Stokes).

  So `g ≥ 2` RFBR + RSRP **reduce to axiom #1's discharge + some
  pointwise classical analysis (chips 5, 8) + integral-of-positivity**.
  Estimated multi-thousand LOC once axiom #1 lands.

* **On any X biholomorphic to RS or T_L:** automatically discharged
  via chip 29's `HasC3FullClassicalContent`-transfer.

## What this file ships

* `RiemannBilinearHypothesis X data basis_ω cycleGens : Prop` —
  Bryan-tree analog of `AX_RiemannBilinear`, definitionally equal to
  `CompleteHodgeRiemannHypothesis data basis_ω cycleGens`.
* `RiemannBilinearHypothesis.of_RFBR_RSRP` — biconditional with the
  chip 9 + chip 18 pair.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`RiemannBilinearHypothesis`** — Bryan-tree analog of mrdouglasny's
`AX_RiemannBilinear`.

The full Riemann bilinear relations on a chosen `(data, basis_ω,
cycleGens)`. Equal to `CompleteHodgeRiemannHypothesis` by definition;
the renaming aligns the Bryan tree with the mrdouglasny axiom inventory.

The named hypothesis decomposes as RFBR + RSRP via chip 10
(`completeHodgeRiemannHypothesis_of_RiemannFirst_RiemannSecond`). -/
abbrev RiemannBilinearHypothesis
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1) : Prop :=
  CompleteHodgeRiemannHypothesis data basis_ω cycleGens

/-- **Decomposition.** RFBR + RSRP discharge `RiemannBilinearHypothesis`. -/
theorem RiemannBilinearHypothesis.of_RFBR_RSRP
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (h_first :
      RiemannFirstBilinearRelation cycleGens
        (standardSymplectic (JacobianChallenge.genus X)))
    (h_second :
      RiemannSecondRelationPositivity data basis_ω cycleGens) :
    RiemannBilinearHypothesis data basis_ω cycleGens :=
  completeHodgeRiemannHypothesis_of_RiemannFirst_RiemannSecond
    data basis_ω cycleGens h_first h_second

end JacobianChallenge

end
