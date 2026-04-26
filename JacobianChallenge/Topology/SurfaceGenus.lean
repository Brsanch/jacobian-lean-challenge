/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvarianceTopCat
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.ULift
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option diagnostics.threshold 100

/-! # Topological genus of a topological space

Towards challenge item 14 (`genus_eq_zero_iff_homeo`) from `Basic.lean`,
this file defines a *topological* genus for an arbitrary topological space
in terms of the rational singular first homology, and proves
homeomorphism invariance.

## Main definitions

* `TopologicalGenus X` — the `ℚ`-dimension of `H₁(X; ℚ)`, viewed as a
  `ℚ`-module via `singularHomologyFunctor (ModuleCat ℚ) 1`. For a closed
  orientable surface this agrees (modulo a factor of 2) with the classical
  genus, but here we leave the integer rank as the definition; the
  "divide by 2" step is not performed because it would only be honest once
  the relationship to the surface classification is in place.

## Main results

* `Homeomorph.topologicalGenus_eq` — homeomorphism invariance of
  `TopologicalGenus`. This follows from functoriality of singular
  homology together with the fact that an isomorphism of `ModuleCat ℚ`
  yields a `ℚ`-linear equivalence on the underlying carriers, and
  `LinearEquiv.finrank_eq` gives equality of dimensions.

## Open challenge

The third honest target — `TopologicalGenus (S²) = 0` — is *not* proved
here. At this mathlib pin, the singular-homology API exposes only
homotopy invariance and the totally-disconnected-space calculation
(`isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`); there is
no Mayer–Vietoris, excision, Hurewicz isomorphism, nor a CW-to-singular
chain-complex equivalence available to compute `H₁(S²)`. Adding any of
those is a separate research-grade upstream contribution to mathlib.
-/

universe u

open CategoryTheory Limits AlgebraicTopology

namespace JacobianChallenge

/--
The first rational singular homology of `X`, packaged as a `ModuleCat ℚ`.

We use the `singularHomologyFunctor (ModuleCat ℚ) 1` from
`Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`, applied to the
coefficient module `ℚ` and the topological space `X`. Universes are
chosen so that `X : Type u` lives in `TopCat.{u}` and the coefficients
live in `ModuleCat.{u} ℚ`.
-/
noncomputable def H1Rat (X : Type u) [TopologicalSpace X] : ModuleCat.{u} ℚ :=
  ((singularHomologyFunctor (ModuleCat.{u} ℚ) 1).obj
      (ModuleCat.of ℚ (ULift.{u} ℚ))).obj (TopCat.of X)

/--
The **topological genus** of `X`, defined as the rational dimension of
the first singular homology `H₁(X; ℚ)`.

For a closed connected orientable surface this equals `2g_{classical}`;
the factor of two is left in to make this an honest invariant of an
arbitrary topological space without claiming the genus identification.
The relationship to the classical (geometric) genus from
`JacobianChallenge.Basic` is challenge item 14.
-/
noncomputable def TopologicalGenus (X : Type u) [TopologicalSpace X] : ℕ :=
  Module.finrank ℚ (H1Rat X)

end JacobianChallenge

namespace Homeomorph

open JacobianChallenge

/--
**Homeomorphism invariance of `TopologicalGenus`.**

A homeomorphism `e : X ≃ₜ Y` lifts to an isomorphism in `TopCat`
(`TopCat.isoOfHomeo`). The functor
`(singularHomologyFunctor (ModuleCat ℚ) 1).obj (ULift ℚ)` sends this to
an isomorphism in `ModuleCat ℚ`, which (via `Iso.toLinearEquiv`) is a
`ℚ`-linear equivalence on the underlying carriers. The conclusion is
then `LinearEquiv.finrank_eq`.
-/
theorem topologicalGenus_eq {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) : TopologicalGenus X = TopologicalGenus Y := by
  -- Lift the homeomorphism to a `TopCat` isomorphism, then push it through the homology functor.
  let eTop : (TopCat.of X) ≅ (TopCat.of Y) := TopCat.isoOfHomeo e
  let F : TopCat.{u} ⥤ ModuleCat.{u} ℚ :=
    (singularHomologyFunctor (ModuleCat.{u} ℚ) 1).obj
      (ModuleCat.of ℚ (ULift.{u} ℚ))
  have eMod : F.obj (TopCat.of X) ≅ F.obj (TopCat.of Y) := F.mapIso eTop
  -- An iso of `ModuleCat ℚ` is a `ℚ`-linear equivalence on carriers.
  have eLin : (H1Rat X) ≃ₗ[ℚ] (H1Rat Y) := eMod.toLinearEquiv
  -- Finrank is invariant under linear equivalence.
  simpa [TopologicalGenus] using eLin.finrank_eq

end Homeomorph
