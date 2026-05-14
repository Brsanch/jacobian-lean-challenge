/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.SurfaceClassificationGenus
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! # `StandardS2 ∖ {v}` is simply-connected, and loops avoiding a point

Building on `Topology/SurfaceClassificationGenus.lean` (which defines
`StandardS2`), this file performs the **stereographic / contractibility
half** of `S2LoopsNullHomotopic`: it shows that any loop in
`StandardS2` that *avoids some point* `⟨v, hv⟩` is null-homotopic, by
lifting it through the inclusion `StandardS2 ∖ {⟨v, hv⟩} ↪ StandardS2`
into a contractible (hence simply-connected) subspace.

After this chip, the remaining content of "π₁(S²) = 0" is the
classical *general-position / smoothing* step: every continuous loop in
`StandardS2` is path-homotopic to one that misses some point. That step
remains a named gap.

## Strategy

Mathlib provides, at the pinned commit `8e3c989…`:

* `stereographic : OpenPartialHomeomorph (sphere 0 1) ((ℝ ∙ v)ᗮ)`
  with `source = {⟨v, _⟩}ᶜ` and `target = univ`
  (`Mathlib/Geometry/Manifold/Instances/Sphere.lean`),
* `OpenPartialHomeomorph.toHomeomorphSourceTarget : e.source ≃ₜ e.target`
  (`Mathlib/Topology/OpenPartialHomeomorph/Basic.lean`),
* `RealTopologicalVectorSpace.contractibleSpace`
  (`Mathlib/Analysis/Convex/Contractible.lean`),
* `Homeomorph.contractibleSpace` — transport along homeomorphisms,
* `SimplyConnectedSpace.ofContractible`
  (`Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean`).

Chained together, these yield `SimplyConnectedSpace ↥(stereographic hv).source`
unconditionally.

## What is proved

* `JacobianChallenge.S2Punctured v hv` — definitional alias for
  `↥(stereographic hv).source`, i.e. the open subset
  `{p : sphere 0 1 | p ≠ ⟨v, hv⟩}` packaged as a subtype.
* `JacobianChallenge.S2Punctured.instContractibleSpace` —
  `S2Punctured v hv` is a `ContractibleSpace`, via the stereographic
  homeomorphism into the orthogonal complement `(ℝ ∙ v)ᗮ` (a real
  topological vector space).
* `JacobianChallenge.S2Punctured.instSimplyConnectedSpace` — corollary
  via `SimplyConnectedSpace.ofContractible`.
* `JacobianChallenge.s2LoopAvoidingNullHomotopic` — any loop
  `γ : Path x x` in `StandardS2` whose image misses `⟨v, hv⟩` is
  `Path.Homotopic` to `Path.refl x`. Pieced together by lifting the
  loop through the inclusion `S2Punctured v hv ↪ StandardS2`,
  invoking simple-connectedness of the punctured sphere, and mapping
  the resulting homotopy back through the inclusion.

No `sorry`, no `axiom`.
-/

noncomputable section

open Metric Topology Set

namespace JacobianChallenge

variable {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1)

/-! ## `S2Punctured` and its `Homeomorph` into `(ℝ ∙ v)ᗮ` -/

/-- The 2-sphere minus the chosen "north pole" `⟨v, hv⟩` at which the
stereographic chart at `v` is undefined, as a subtype. Definitionally
equal to `↥(stereographic hv).source`. -/
abbrev S2Punctured (v : EuclideanSpace ℝ (Fin 3)) (hv : ‖v‖ = 1) : Type :=
  ↥(stereographic hv).source

/-- Stereographic projection as a `Homeomorph` from `S2Punctured v hv`
to the orthogonal complement `(ℝ ∙ v)ᗮ`. Composes
`OpenPartialHomeomorph.toHomeomorphSourceTarget` with the trivialisation
of the `Set.univ` target. -/
def S2Punctured.stereographicHomeomorph :
    S2Punctured v hv ≃ₜ ((ℝ ∙ v)ᗮ : Submodule ℝ _) := by
  refine ((stereographic hv).toHomeomorphSourceTarget).trans ?_
  rw [stereographic_target hv]
  exact Homeomorph.Set.univ _

/-! ## Contractibility and simple-connectedness of `S2Punctured` -/

/-- The orthogonal complement `(ℝ ∙ v)ᗮ` in `EuclideanSpace ℝ (Fin 3)`
is a real topological vector space, hence a `ContractibleSpace` via
`RealTopologicalVectorSpace.contractibleSpace`. We register this as a
local instance so the transport below can synthesise it. -/
instance instContractibleSpace_orthogonalComplement :
    ContractibleSpace ((ℝ ∙ v)ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) :=
  RealTopologicalVectorSpace.contractibleSpace

/-- `S2Punctured v hv` is a `ContractibleSpace` — transport along the
stereographic homeomorphism into `(ℝ ∙ v)ᗮ`. -/
instance S2Punctured.instContractibleSpace :
    ContractibleSpace (S2Punctured v hv) :=
  (S2Punctured.stereographicHomeomorph hv).contractibleSpace

/-- `S2Punctured v hv` is a `SimplyConnectedSpace`, via mathlib's
`SimplyConnectedSpace.ofContractible`. -/
instance S2Punctured.instSimplyConnectedSpace :
    SimplyConnectedSpace (S2Punctured v hv) :=
  SimplyConnectedSpace.ofContractible _

/-! ## Loops avoiding a point are null-homotopic -/

/-- The continuous subtype-inclusion `S2Punctured v hv ↪ StandardS2`,
packaged as a `C(_, _)` for use with `Path.map`. -/
def S2Punctured.incl : C(S2Punctured v hv, JacobianChallenge.StandardS2) where
  toFun p := p.1
  continuous_toFun := continuous_subtype_val

/-- Lift a `Path x y` in `StandardS2` that avoids the point
`⟨v, hv⟩` to a `Path` in `S2Punctured v hv`. Uses `stereographic_source`
to recast the avoidance hypothesis as subtype membership. -/
def S2Punctured.liftPath {x y : JacobianChallenge.StandardS2}
    (hx : x ∈ (stereographic hv).source)
    (hy : y ∈ (stereographic hv).source)
    (γ : Path x y)
    (h_avoid : ∀ t : unitInterval, γ t ∈ (stereographic hv).source) :
    Path (⟨x, hx⟩ : S2Punctured v hv) ⟨y, hy⟩ where
  toFun t := ⟨γ t, h_avoid t⟩
  continuous_toFun := Continuous.subtype_mk γ.continuous _
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

/-- The lifted path, post-composed with the inclusion, recovers the
original path. -/
theorem S2Punctured.liftPath_map_incl_eq
    {x y : JacobianChallenge.StandardS2}
    (hx : x ∈ (stereographic hv).source)
    (hy : y ∈ (stereographic hv).source)
    (γ : Path x y)
    (h_avoid : ∀ t : unitInterval, γ t ∈ (stereographic hv).source) :
    (S2Punctured.liftPath hv hx hy γ h_avoid).map
      (S2Punctured.incl hv).continuous = γ := by
  ext t; rfl

/-- **Loops avoiding a point are null-homotopic.** A loop
`γ : Path x x` in `StandardS2` whose image misses the north pole
`⟨v, hv⟩` of the stereographic chart at `v` is `Path.Homotopic` to the
constant path `Path.refl x`.

The avoidance hypothesis is stated as `γ t ∈ (stereographic hv).source`,
which by `stereographic_source` is exactly `γ t ≠ ⟨v, hv⟩`.

Proof: lift `γ` to a loop `γ'` in the contractible (hence
simply-connected) subspace `S2Punctured v hv`; conclude
`γ'.Homotopic (Path.refl _)`; map through the inclusion to recover a
homotopy in `StandardS2`. -/
theorem s2LoopAvoidingNullHomotopic
    (x : JacobianChallenge.StandardS2)
    (hx : x ∈ (stereographic hv).source)
    (γ : Path x x)
    (h_avoid : ∀ t : unitInterval, γ t ∈ (stereographic hv).source) :
    Path.Homotopic γ (Path.refl x) := by
  -- Lift γ to the punctured sphere.
  set γ' : Path (⟨x, hx⟩ : S2Punctured v hv) ⟨x, hx⟩ :=
    S2Punctured.liftPath hv hx hx γ h_avoid with hγ'
  -- Simple-connectedness ⇒ γ' homotopic to the constant loop.
  have h_homotopic :
      γ'.Homotopic (Path.refl (⟨x, hx⟩ : S2Punctured v hv)) :=
    SimplyConnectedSpace.paths_homotopic γ' _
  -- Map through the inclusion to recover a homotopy in StandardS2.
  have h_map :
      (γ'.map (S2Punctured.incl hv).continuous).Homotopic
        ((Path.refl (⟨x, hx⟩ : S2Punctured v hv)).map
          (S2Punctured.incl hv).continuous) :=
    h_homotopic.map (S2Punctured.incl hv)
  -- Identify the lifted/mapped objects with the originals.
  have h_lhs : γ'.map (S2Punctured.incl hv).continuous = γ :=
    S2Punctured.liftPath_map_incl_eq hv hx hx γ h_avoid
  have h_rhs :
      (Path.refl (⟨x, hx⟩ : S2Punctured v hv)).map
          (S2Punctured.incl hv).continuous = Path.refl x := by
    ext t; rfl
  rw [h_lhs, h_rhs] at h_map
  exact h_map

end JacobianChallenge

end
