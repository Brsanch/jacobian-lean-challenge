/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LinearSystemGermDeltaPHolomorphicEquivTransport
import JacobianChallenge.Topology.LinearSystemDivisorSimplePoleRank
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Transport of `LinearSystemGermDeltaPFiniteDim` via `HolomorphicEquiv`

A `HolomorphicEquiv X Y` plus its inverse give a ℂ-linear equivalence
between `linearSystemGermDeltaP (e p)` (in `MFG Y`) and
`linearSystemGermDeltaP p` (in `MFG X`). Module-finiteness transports
through linear equivalences, so

  `LinearSystemGermDeltaPFiniteDim Y` + `HolomorphicEquiv X Y`
    → `LinearSystemGermDeltaPFiniteDim X`.

In particular, `LinearSystemGermDeltaPFiniteDim RiemannSphere` (if
known) would transport to `X` for any `X ≃ RS`.

## Construction

The pullback `compHolomorphicEquiv e` and `compHolomorphicEquiv e.symm`
are inverse on the underlying germ field: the composition unfolds to
`f ∘ e ∘ e.symm = f` (= identity on `Y`-side). Bundling gives a
`LinearEquiv ℂ (MFG Y) (MFG X)`, which restricts to an equivalence
between `L(δ(e p))` and `L(δp)`.

## Contents

* `MeromorphicFunctionGerm.compHolomorphicEquiv_symm_comp` —
  `compHolomorphicEquiv e.symm (compHolomorphicEquiv e φ) = φ`.
* `MeromorphicFunctionGerm.compHolomorphicEquiv_comp_symm` —
  the reverse direction.
* `MeromorphicFunctionGerm.compHolomorphicEquivLinearEquiv` —
  `LinearEquiv ℂ (MFG Y) (MFG X)`.
* `linearSystemGermDeltaPLinearEquiv_via_holomorphicEquiv` —
  `LinearEquiv ℂ (L(δ(e p))) (L(δp))`.
* `LinearSystemGermDeltaPFiniteDim.of_holomorphicEquiv` — the
  finite-dim transport headline.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace JacobianChallenge.MeromorphicFunctionField

universe u v

open JacobianChallenge

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable {Y : Type v}
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-! ## Inverse identities -/

/-- **`compHolomorphicEquiv e.symm ∘ compHolomorphicEquiv e = id`**
on `MeromorphicFunctionGerm Y`. The pullback by `e` then by `e.symm`
restores the original germ. -/
lemma MeromorphicFunctionGerm.compHolomorphicEquiv_symm_comp
    (e : HolomorphicEquiv X Y) (φ : MeromorphicFunctionGerm Y) :
    MeromorphicFunctionGerm.compHolomorphicEquiv e.symm
        (MeromorphicFunctionGerm.compHolomorphicEquiv e φ)
      = φ := by
  rcases φ with ⟨f⟩
  show MeromorphicFunctionGerm.compHolomorphicEquiv e.symm
      (MeromorphicFunctionGerm.compHolomorphicEquiv e (MeromorphicFunctionGerm.mk f))
    = MeromorphicFunctionGerm.mk f
  rw [MeromorphicFunctionGerm.compHolomorphicEquiv_mk,
      MeromorphicFunctionGerm.compHolomorphicEquiv_mk]
  apply Quotient.sound
  intro y
  apply Filter.Eventually.of_forall
  intro z
  show (MMer.compHolomorphicEquiv e.symm
          (MMer.compHolomorphicEquiv e f)).toFun z
      = f.toFun z
  show f.toFun ((e.toEquiv : X → Y) (e.symm.toEquiv z)) = f.toFun z
  -- `e (e.symm z) = z`.
  rw [show (e.toEquiv : X → Y) (e.symm.toEquiv z) = z from
      e.toEquiv.apply_symm_apply z]

/-- **`compHolomorphicEquiv e ∘ compHolomorphicEquiv e.symm = id`** on
`MeromorphicFunctionGerm X`. -/
lemma MeromorphicFunctionGerm.compHolomorphicEquiv_comp_symm
    (e : HolomorphicEquiv X Y) (ψ : MeromorphicFunctionGerm X) :
    MeromorphicFunctionGerm.compHolomorphicEquiv e
        (MeromorphicFunctionGerm.compHolomorphicEquiv e.symm ψ)
      = ψ := by
  rcases ψ with ⟨g⟩
  show MeromorphicFunctionGerm.compHolomorphicEquiv e
      (MeromorphicFunctionGerm.compHolomorphicEquiv e.symm (MeromorphicFunctionGerm.mk g))
    = MeromorphicFunctionGerm.mk g
  rw [MeromorphicFunctionGerm.compHolomorphicEquiv_mk,
      MeromorphicFunctionGerm.compHolomorphicEquiv_mk]
  apply Quotient.sound
  intro x
  apply Filter.Eventually.of_forall
  intro z
  show (MMer.compHolomorphicEquiv e
          (MMer.compHolomorphicEquiv e.symm g)).toFun z
      = g.toFun z
  show g.toFun (e.symm.toEquiv ((e.toEquiv : X → Y) z)) = g.toFun z
  rw [show e.symm.toEquiv ((e.toEquiv : X → Y) z) = z from
      e.toEquiv.symm_apply_apply z]

/-! ## ℂ-linear equivalence on germ field -/

/-- The pullback `compHolomorphicEquiv` as a ℂ-linear equivalence
`MeromorphicFunctionGerm Y ≃ₗ[ℂ] MeromorphicFunctionGerm X`. -/
noncomputable def MeromorphicFunctionGerm.compHolomorphicEquivLinearEquiv
    (e : HolomorphicEquiv X Y) :
    MeromorphicFunctionGerm Y ≃ₗ[ℂ] MeromorphicFunctionGerm X where
  toFun := MeromorphicFunctionGerm.compHolomorphicEquiv e
  invFun := MeromorphicFunctionGerm.compHolomorphicEquiv e.symm
  map_add' := MeromorphicFunctionGerm.compHolomorphicEquiv_add e
  map_smul' c φ := MeromorphicFunctionGerm.compHolomorphicEquiv_smul e c φ
  left_inv φ := MeromorphicFunctionGerm.compHolomorphicEquiv_symm_comp e φ
  right_inv ψ := MeromorphicFunctionGerm.compHolomorphicEquiv_comp_symm e ψ

/-! ## ℂ-linear equivalence on `linearSystemGermDeltaP` -/

/-- The pullback restricts to a ℂ-linear equivalence
`linearSystemGermDeltaP (e p) ≃ₗ[ℂ] linearSystemGermDeltaP p`. -/
noncomputable def linearSystemGermDeltaPLinearEquiv_via_holomorphicEquiv
    (e : HolomorphicEquiv X Y) (p : X) :
    linearSystemGermDeltaP (e p) ≃ₗ[ℂ] linearSystemGermDeltaP p where
  toFun := linearSystemGermDeltaPLinearMap_via_holomorphicEquiv e p
  invFun φ :=
    ⟨MeromorphicFunctionGerm.compHolomorphicEquiv e.symm (φ : MeromorphicFunctionGerm X),
      by
        rw [linearSystemGermDeltaP_compHolomorphicEquiv_iff]
        -- After rw, goal: `φ ∈ linearSystemGermDeltaP (e.symm (e p))`.
        -- `e.symm (e p) = p` by `e.symm_apply_apply`.
        have h_rt : e.symm (e p) = p :=
          e.toEquiv.symm_apply_apply p
        rw [h_rt]
        exact φ.property⟩
  map_add' φ ψ := by
    ext
    show (MeromorphicFunctionGerm.compHolomorphicEquiv e
            ((φ : MeromorphicFunctionGerm Y) + ψ))
        = MeromorphicFunctionGerm.compHolomorphicEquiv e φ
            + MeromorphicFunctionGerm.compHolomorphicEquiv e ψ
    exact MeromorphicFunctionGerm.compHolomorphicEquiv_add e _ _
  map_smul' c φ := by
    ext
    show MeromorphicFunctionGerm.compHolomorphicEquiv e
            (c • (φ : MeromorphicFunctionGerm Y))
        = c • MeromorphicFunctionGerm.compHolomorphicEquiv e φ
    exact MeromorphicFunctionGerm.compHolomorphicEquiv_smul e c φ
  left_inv φ := by
    apply Subtype.ext
    show MeromorphicFunctionGerm.compHolomorphicEquiv e.symm
        (MeromorphicFunctionGerm.compHolomorphicEquiv e
          (φ : MeromorphicFunctionGerm Y))
      = (φ : MeromorphicFunctionGerm Y)
    exact MeromorphicFunctionGerm.compHolomorphicEquiv_symm_comp e _
  right_inv ψ := by
    apply Subtype.ext
    show MeromorphicFunctionGerm.compHolomorphicEquiv e
        (MeromorphicFunctionGerm.compHolomorphicEquiv e.symm
          (ψ : MeromorphicFunctionGerm X))
      = (ψ : MeromorphicFunctionGerm X)
    exact MeromorphicFunctionGerm.compHolomorphicEquiv_comp_symm e _

/-! ## Finite-dimensionality transport -/

/-- **`LinearSystemGermDeltaPFiniteDim` transports through a
`HolomorphicEquiv`**: if `Y`'s linear systems are all finite-dim, then
so are `X`'s (via the linear equivalence). -/
theorem LinearSystemGermDeltaPFiniteDim.of_holomorphicEquiv
    (e : HolomorphicEquiv X Y) (h : LinearSystemGermDeltaPFiniteDim Y) :
    LinearSystemGermDeltaPFiniteDim X := by
  intro p
  -- `linearSystemGermDeltaP (e p)` is finite-dim by hypothesis.
  have h_finite : Module.Finite ℂ (linearSystemGermDeltaP (e p)) := h (e p)
  -- Transport via the linear equiv.
  exact Module.Finite.equiv (linearSystemGermDeltaPLinearEquiv_via_holomorphicEquiv e p)

/-- Nonempty form: `Nonempty (HolomorphicEquiv X Y)` + finite-dim on `Y`
gives finite-dim on `X`. -/
theorem LinearSystemGermDeltaPFiniteDim.of_nonempty_holomorphicEquiv
    (h_equiv : Nonempty (HolomorphicEquiv X Y))
    (h : LinearSystemGermDeltaPFiniteDim Y) :
    LinearSystemGermDeltaPFiniteDim X :=
  h_equiv.elim (fun e => LinearSystemGermDeltaPFiniteDim.of_holomorphicEquiv e h)

end JacobianChallenge.MeromorphicFunctionField

end
