/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.Normed.Module.Dual

/-! # Cotangent bundle of a `C^1` manifold

This file defines the cotangent bundle as a topological vector bundle over a
`C^1` manifold `M` modelled on `(E, H)` with model with corners
`I : ModelWithCorners 𝕜 E H`.

The construction mirrors `Mathlib.Geometry.Manifold.VectorBundle.Tangent`
exactly: we introduce a type synonym `CotangentSpace I` for the dual
`E →L[𝕜] 𝕜`, build a `VectorBundleCore` whose coordinate changes are the
fibrewise transposes of the tangent bundle's coordinate changes, and then
inherit the topology / fibre / vector bundle structure on its total space.

## Main definitions

* `CotangentSpace I (x : M)` — type synonym for `E →L[𝕜] 𝕜`, the cotangent
  space at `x`. Like `TangentSpace`, this is a *non-reducible* abbrev so that
  type class inference does not pick up wrong instances.
* `CotangentBundle I M` — the total space `Bundle.TotalSpace (E →L[𝕜] 𝕜)
  (CotangentSpace I)`.
* `cotangentBundleCore I M` — the `VectorBundleCore` over `M` indexed by
  `atlas H M` whose coordinate change `i → j` at `x : M` is precomposition
  with `tangentBundleCore.coordChange j i x`. Equivalently, it is the
  fibrewise *transpose* of the tangent transition.

## Design notes

For the change-of-coordinates derivation, recall that a covector at a point
of `M` is intrinsic; if `ξ_a` is its representative in chart `a` and `ξ_b` in
chart `b`, and if `T_{ab} : E →L[𝕜] E` denotes the tangent transition `a → b`
(so a tangent vector `v_a` in chart `a` has representative `v_b = T_{ab} v_a`
in chart `b`), then by intrinsicality
`ξ_a(v_a) = ξ_b(v_b) = ξ_b(T_{ab} v_a)`, hence `ξ_a = ξ_b ∘L T_{ab}` and so
`ξ_b = ξ_a ∘L T_{ab}^{-1} = ξ_a ∘L T_{ba}`. Hence
`cotangentBundleCore.coordChange a b x` sends `ξ` to `ξ ∘L T_{ba}`, where
`T_{ba} = tangentBundleCore.coordChange b a x`.

The cocycle condition then reduces directly to the tangent cocycle: writing
`T_{ab} := tangentBundleCore.coordChange a b x`, the tangent cocycle
`T_{jk} ∘L T_{ij} = T_{ik}` (cf. `VectorBundleCore.coordChange_comp`)
relabelled `(i, j, k) ↦ (k, j, i)` reads `T_{ji} ∘L T_{kj} = T_{ki}`, which
is exactly what is needed when one composes the dual coordinate changes
`i → j → k`.

This construction depends only on `M` being `C^1`. The promotion to a
`ContMDiffVectorBundle` for higher regularity follows the same pattern as for
the tangent bundle but is left to a follow-up file.
-/

open Bundle Set IsManifold OpenPartialHomeomorph ContinuousLinearMap

open scoped Manifold Topology Bundle

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section CotangentSpace

set_option linter.unusedVariables false in
/-- The cotangent space at a point `x : M` is the topological dual of `E`,
i.e. `E →L[𝕜] 𝕜`. As with `TangentSpace`, we use a type synonym (kept
non-reducible) so that type class inference does not pick up wrong instances
through the underlying defeq. -/
@[nolint unusedArguments]
def CotangentSpace {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (_x : M) : Type _ :=
  E →L[𝕜] 𝕜

instance : AddCommGroup (CotangentSpace I x) :=
  inferInstanceAs (AddCommGroup (E →L[𝕜] 𝕜))

instance : Module 𝕜 (CotangentSpace I x) :=
  inferInstanceAs (Module 𝕜 (E →L[𝕜] 𝕜))

instance : TopologicalSpace (CotangentSpace I x) :=
  inferInstanceAs (TopologicalSpace (E →L[𝕜] 𝕜))

instance : IsTopologicalAddGroup (CotangentSpace I x) :=
  inferInstanceAs (IsTopologicalAddGroup (E →L[𝕜] 𝕜))

instance : ContinuousSMul 𝕜 (CotangentSpace I x) :=
  inferInstanceAs (ContinuousSMul 𝕜 (E →L[𝕜] 𝕜))

instance : ContinuousConstSMul 𝕜 (CotangentSpace I x) :=
  inferInstanceAs (ContinuousConstSMul 𝕜 (E →L[𝕜] 𝕜))

instance : Inhabited (CotangentSpace I x) := ⟨0⟩

variable (I M) in
/-- The cotangent bundle to a manifold, as a `Bundle.TotalSpace`. Defined in
terms of `Bundle.TotalSpace` so it carries a suitable topology coming from
`cotangentBundleCore`. -/
abbrev CotangentBundle := Bundle.TotalSpace (E →L[𝕜] 𝕜) (CotangentSpace I : M → Type _)

end CotangentSpace

section CotangentBundleCore

variable [IsManifold I 1 M]

variable (I M) in
/-- Let `M` be a `C^1` manifold modelled on `(E, H)` with model with corners
`I`. Then `cotangentBundleCore I M` is the vector bundle core for the
cotangent bundle over `M`, indexed by the atlas of `M` with fibre
`E →L[𝕜] 𝕜`. Its change of coordinates from chart `i` to chart `j` at a
point `x : M` is precomposition with `tangentBundleCore.coordChange j i x`,
which equals the fibrewise transpose of the tangent transition `i → j`.

See the file docstring for the geometric derivation and for the cocycle
reduction to `tangentBundleCore.coordChange_comp`. -/
@[simps indexAt baseSet]
def cotangentBundleCore : VectorBundleCore 𝕜 M (E →L[𝕜] 𝕜) (atlas H M) where
  baseSet i := i.1.source
  isOpen_baseSet i := i.1.open_source
  indexAt := achart H
  mem_baseSet_at := mem_chart_source H
  coordChange i j x :=
    -- Precompose with `tangentBundleCore.coordChange j i x`.
    ((ContinuousLinearMap.compL 𝕜 E E 𝕜).flip
      ((tangentBundleCore I M).coordChange j i x))
  coordChange_self i x hx ξ := by
    -- `tangentBundleCore.coordChange i i x = id`, so precomposition leaves
    -- `ξ : E →L[𝕜] 𝕜` unchanged. We unfold `compL.flip` to a plain
    -- composition of continuous linear maps.
    have hself : ∀ v, (tangentBundleCore I M).coordChange i i x v = v :=
      fun v => (tangentBundleCore I M).coordChange_self i x hx v
    ext v
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply, hself]
  continuousOn_coordChange i j := by
    -- Continuity of `x ↦ ξ ↦ ξ ∘L T_{ji}(x)` follows from continuity of
    -- `x ↦ T_{ji}(x)` (i.e. tangent's `continuousOn_coordChange`) post-composed
    -- with the continuous linear map `compL.flip`.
    have htang :
        ContinuousOn (fun x => (tangentBundleCore I M).coordChange j i x)
          ((tangentBundleCore I M).baseSet i ∩ (tangentBundleCore I M).baseSet j) := by
      have h := (tangentBundleCore I M).continuousOn_coordChange j i
      simpa [Set.inter_comm] using h
    -- Bake this through the bilinear `compL.flip` to get continuity of the
    -- dual coordinate change as a function `M → ((E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜))`.
    refine ((ContinuousLinearMap.compL 𝕜 E E 𝕜).flip).continuous.comp_continuousOn htang
  coordChange_comp := by
    -- Reduce to the tangent cocycle `T_{ji} ∘L T_{kj} = T_{ki}` (i.e.
    -- `tangentBundleCore.coordChange_comp` with indices `k j i`), then chase
    -- the precompositions.
    rintro i j k x ⟨⟨hxi, hxj⟩, hxk⟩ ξ
    -- Underlying tangent cocycle, applied pointwise to give an equality of CLMs.
    have htan : ∀ v,
        (tangentBundleCore I M).coordChange j i x
          ((tangentBundleCore I M).coordChange k j x v) =
        (tangentBundleCore I M).coordChange k i x v := by
      intro v
      exact (tangentBundleCore I M).coordChange_comp k j i x ⟨⟨hxk, hxj⟩, hxi⟩ v
    -- Unfold both sides to plain CLM compositions and reduce to `htan`.
    ext v
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply, htan v]

@[simp]
theorem cotangentBundleCore_coordChange_apply
    (i j : atlas H M) (x : M) (ξ : E →L[𝕜] 𝕜) :
    (cotangentBundleCore I M).coordChange i j x ξ =
      ξ.comp ((tangentBundleCore I M).coordChange j i x) := by
  ext v
  simp [cotangentBundleCore, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply]

theorem cotangentBundleCore_coordChange_self
    (i : atlas H M) {x : M} (hx : x ∈ (cotangentBundleCore I M).baseSet i)
    (ξ : E →L[𝕜] 𝕜) :
    (cotangentBundleCore I M).coordChange i i x ξ = ξ :=
  (cotangentBundleCore I M).coordChange_self i x hx ξ

end CotangentBundleCore

section CotangentBundleInstances

variable [IsManifold I 1 M]

local notation "T*M" => CotangentBundle I M

/-- The total space of the cotangent bundle is a topological space, via
`cotangentBundleCore`. -/
instance : TopologicalSpace T*M :=
  inferInstanceAs <| TopologicalSpace (cotangentBundleCore I M).TotalSpace

/-- The cotangent space, viewed as the assignment `M → Type _`, is a fibre
bundle with model fibre `E →L[𝕜] 𝕜`. -/
instance CotangentSpace.fiberBundle :
    FiberBundle (E →L[𝕜] 𝕜) (CotangentSpace I : M → Type _) :=
  inferInstanceAs <| FiberBundle (E →L[𝕜] 𝕜) (cotangentBundleCore I M).Fiber

/-- The cotangent bundle is a (topological) vector bundle. -/
instance CotangentSpace.vectorBundle :
    VectorBundle 𝕜 (E →L[𝕜] 𝕜) (CotangentSpace I : M → Type _) :=
  inferInstanceAs <| VectorBundle 𝕜 (E →L[𝕜] 𝕜) (cotangentBundleCore I M).Fiber

end CotangentBundleInstances

end
