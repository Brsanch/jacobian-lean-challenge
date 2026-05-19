/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorus
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.PathConnected

set_option linter.unusedSectionVars false

/-! # `ConnectedSpace (ℂ ⧸ L)`

`ℂ` is a real normed vector space, hence path-connected (and thus
connected). The quotient projection `L.mkQ : ℂ → ℂ ⧸ L` is continuous
(it is the quotient map) and surjective. Therefore `ℂ ⧸ L` is
connected — the continuous surjective image of a connected space is
connected.

This is the missing typeclass-level instance that lets the
unconditional Liouville theorem
`Topology.LiouvilleForContMDiffOmega.contMDiff_omega_isConstant`
fire on the complex torus.

No `sorry`, no `axiom`. -/

open scoped Manifold

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **`ConnectedSpace (ℂ ⧸ L)`.** The continuous surjective image of a
connected (in fact path-connected) space is connected. -/
instance instConnectedSpace : ConnectedSpace (ℂ ⧸ L) :=
  Function.Surjective.connectedSpace
    (f := (L.mkQ : ℂ → ℂ ⧸ L))
    L.mkQ_surjective
    (L.isOpenQuotientMap_mkQ).continuous

end ComplexTorus

end JacobianChallenge

end
