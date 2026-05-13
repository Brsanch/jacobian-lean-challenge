/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexManifoldRealification
import JacobianChallenge.Manifold.CotangentBundleSmoothness
import JacobianChallenge.Manifold.HolomorphicOneFormRealification
import JacobianChallenge.Manifold.HolomorphicOneFormRealificationLinearity
import JacobianChallenge.Manifold.SmoothOneForm
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # The real and imaginary components of a holomorphic 1-form as `ℝ`-linear maps

This file packages the fibrewise real-part / imaginary-part operation
`φ ↦ reCLM ∘L (φ.restrictScalars ℝ)` from
`HolomorphicOneFormRealification.lean` as continuous **ℝ**-linear maps

```
realPartCLM, imagPartCLM : (ℂ →L[ℂ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℝ)
```

These bundled CLMs are the load-bearing fibrewise object for the bundled
`SmoothOneForm 𝓘(ℝ, ℂ) X` construction — they let downstream chips compose
the holomorphic section `om.eval` with a continuous **ℝ**-linear fibrewise
map and invoke `ContMDiff.clm_apply` to obtain smoothness of the real/imag
component as a manifold map. The bundle-section wrapping (using
`cotangentSection_contMDiffAt_iff` for both the complex and real cotangent
bundles) is then a separate compositional step.

## Implementation notes

The construction `(compL ℝ ℂ ℂ ℝ reCLM).comp restrictScalarsL` hits the
standard `NormedSpace ℝ ℂ` diamond (between `NormedSpace.complexToReal`
and `NormedAlgebra.toNormedSpace`) inside `restrictScalarsL`'s
`[IsScalarTower 𝕜 𝕜' E]` requirement. Pinning the algebra-based
`NormedSpace ℝ ℂ` per def via `letI` breaks the diamond, just as for
`ComplexManifoldRealification.lean`'s
`contDiffOn_real_chart_trans_of_complex`.

The pointwise apply lemmas relating `realPartCLM φ` to the existing
unbundled `Complex.reCLM.comp (φ.restrictScalars ℝ)` require an explicit
`ext` + `simp` of the underlying composition; `rfl` does not suffice once
the `compL` / `restrictScalarsL` bundles are involved.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff
open Bundle

noncomputable section

namespace JacobianChallenge

universe u

/-! ## Fibrewise real-part / imaginary-part `ℝ`-linear maps -/

/-- The fibrewise **real-part** operation on the holomorphic cotangent fibre
`(ℂ →L[ℂ] ℂ)`, packaged as a continuous **ℝ**-linear map into the real
cotangent fibre `(ℂ →L[ℝ] ℝ)`.

Concretely: `φ ↦ reCLM ∘L (φ.restrictScalars ℝ)`. This is the bundled
version of the pointwise `HolomorphicOneForm.realPart x` from
`HolomorphicOneFormRealification.lean`. -/
def realPartCLM : (ℂ →L[ℂ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℝ) := by
  letI : NormedSpace ℝ ℂ := @NormedAlgebra.toNormedSpace ℝ ℂ _ _ _
  exact (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.reCLM).comp
    (ContinuousLinearMap.restrictScalarsL ℂ ℂ ℂ ℝ ℝ)

/-- The fibrewise **imaginary-part** operation, packaged as a continuous
**ℝ**-linear map. Concretely: `φ ↦ imCLM ∘L (φ.restrictScalars ℝ)`. -/
def imagPartCLM : (ℂ →L[ℂ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℝ) := by
  letI : NormedSpace ℝ ℂ := @NormedAlgebra.toNormedSpace ℝ ℂ _ _ _
  exact (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.imCLM).comp
    (ContinuousLinearMap.restrictScalarsL ℂ ℂ ℂ ℝ ℝ)

theorem realPartCLM_apply (φ : ℂ →L[ℂ] ℂ) :
    realPartCLM φ = Complex.reCLM.comp (φ.restrictScalars ℝ) := by
  letI : NormedSpace ℝ ℂ := @NormedAlgebra.toNormedSpace ℝ ℂ _ _ _
  show ((ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.reCLM).comp
          (ContinuousLinearMap.restrictScalarsL ℂ ℂ ℂ ℝ ℝ)) φ
        = Complex.reCLM.comp (φ.restrictScalars ℝ)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply]
  congr 1

theorem imagPartCLM_apply (φ : ℂ →L[ℂ] ℂ) :
    imagPartCLM φ = Complex.imCLM.comp (φ.restrictScalars ℝ) := by
  letI : NormedSpace ℝ ℂ := @NormedAlgebra.toNormedSpace ℝ ℂ _ _ _
  show ((ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.imCLM).comp
          (ContinuousLinearMap.restrictScalarsL ℂ ℂ ℂ ℝ ℝ)) φ
        = Complex.imCLM.comp (φ.restrictScalars ℝ)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply]
  congr 1

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- The pointwise `realPartCLM` applied to `om.eval x` is exactly the
pointwise `om.realPart x` from `HolomorphicOneFormRealification.lean`. -/
theorem realPartCLM_eval (om : HolomorphicOneForm X) (x : X) :
    realPartCLM (om.eval x) = om.realPart x := by
  rw [realPartCLM_apply]
  rfl

/-- The pointwise `imagPartCLM` applied to `om.eval x` is exactly
`om.imagPart x`. -/
theorem imagPartCLM_eval (om : HolomorphicOneForm X) (x : X) :
    imagPartCLM (om.eval x) = om.imagPart x := by
  rw [imagPartCLM_apply]
  rfl

/-! ## Tangent-bundle compatibility between the two manifold structures -/

/-- The chart transition `j.1 ∘ i.1.symm` is **ℂ**-differentiable at `i.1 x`
when `x` is in both chart sources, by the holomorphic atlas compatibility. -/
private theorem chart_change_differentiable_complex
    (i j : atlas ℂ X) {x : X} (hxi : x ∈ i.1.source) (hxj : x ∈ j.1.source) :
    DifferentiableAt ℂ
      ((j.1 : OpenPartialHomeomorph X ℂ) ∘ (i.1.symm : OpenPartialHomeomorph ℂ X))
      (i.1 x) := by
  have h_compat : i.1.symm.trans j.1 ∈ contDiffGroupoid ω 𝓘(ℂ, ℂ) :=
    StructureGroupoid.compatible (contDiffGroupoid ω 𝓘(ℂ, ℂ)) i.2 j.2
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at h_compat
  obtain ⟨h_fwd, _⟩ := h_compat
  -- `h_fwd : (contDiffPregroupoid ω 𝓘(ℂ, ℂ)).property (i.1.symm.trans j.1)
  --             (i.1.symm.trans j.1).source`.
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp,
    Set.preimage_id, Set.range_id, Set.inter_univ] at h_fwd
  -- Now `h_fwd : ContDiffOn ℂ ω (↑(i.1.symm.trans j.1)) (i.1.symm.trans j.1).source`.
  have hmem : i.1 x ∈ (i.1.symm.trans j.1).source := by
    refine ⟨?_, ?_⟩
    · -- `i.1 x ∈ (i.1.symm).source = i.1.target` since `x ∈ i.1.source`.
      exact i.1.map_source hxi
    · -- `i.1.symm (i.1 x) = x ∈ j.1.source`.
      change i.1.symm (i.1 x) ∈ j.1.source
      rw [i.1.left_inv hxi]
      exact hxj
  have hCDA : ContDiffAt ℂ ω _ (i.1 x) :=
    h_fwd.contDiffAt ((i.1.symm.trans j.1).open_source.mem_nhds hmem)
  -- `ω ≠ 0` since `ω = ⊤` in `WithTop ℕ∞`.
  have hω : (ω : WithTop ℕ∞) ≠ 0 := by decide
  exact hCDA.differentiableAt hω

/-- **Tangent-bundle core compatibility**. The chart-transition derivative,
read with model `𝓘(ℝ, ℂ)`, is the restriction-of-scalars of the same
chart-transition derivative read with model `𝓘(ℂ, ℂ)`.

This is the load-bearing concrete fact that lets us relate the two
cotangent bundles' coordinate-change functions via the fibrewise
`realPartCLM` / `imagPartCLM`. -/
theorem tangentBundleCore_coordChange_restrictScalars_eq
    (i j : atlas ℂ X) {x : X} (hxi : x ∈ i.1.source) (hxj : x ∈ j.1.source) :
    (tangentBundleCore 𝓘(ℝ, ℂ) X).coordChange i j x =
      ((tangentBundleCore 𝓘(ℂ, ℂ) X).coordChange i j x).restrictScalars ℝ := by
  -- Differentiability of the chart change over ℂ.
  have h_diffℂ : DifferentiableAt ℂ
      ((j.1 : OpenPartialHomeomorph X ℂ) ∘ (i.1.symm : OpenPartialHomeomorph ℂ X))
      (i.1 x) := chart_change_differentiable_complex i j hxi hxj
  -- Unfold both `tangentBundleCore.coordChange` values and reduce the
  -- `modelWithCornersSelf` decoration.
  show
    fderivWithin ℝ ((j.1 : OpenPartialHomeomorph X ℂ).extend 𝓘(ℝ, ℂ) ∘
        ((i.1 : OpenPartialHomeomorph X ℂ).extend 𝓘(ℝ, ℂ)).symm)
      (Set.range 𝓘(ℝ, ℂ))
      ((i.1 : OpenPartialHomeomorph X ℂ).extend 𝓘(ℝ, ℂ) x)
    = (fderivWithin ℂ ((j.1 : OpenPartialHomeomorph X ℂ).extend 𝓘(ℂ, ℂ) ∘
        ((i.1 : OpenPartialHomeomorph X ℂ).extend 𝓘(ℂ, ℂ)).symm)
      (Set.range 𝓘(ℂ, ℂ))
      ((i.1 : OpenPartialHomeomorph X ℂ).extend 𝓘(ℂ, ℂ) x)).restrictScalars ℝ
  -- Reduce `i.1.extend 𝓘(...) = i.1` and `range 𝓘(...) = univ`.
  have hExtR : ∀ (f : OpenPartialHomeomorph X ℂ),
      (⇑(f.extend 𝓘(ℝ, ℂ)) : X → ℂ) = ⇑f := by
    intro f; ext; rfl
  have hExtSymmR : ∀ (f : OpenPartialHomeomorph X ℂ),
      (⇑(f.extend 𝓘(ℝ, ℂ)).symm : ℂ → X) = ⇑f.symm := by
    intro f; ext; rfl
  have hExtC : ∀ (f : OpenPartialHomeomorph X ℂ),
      (⇑(f.extend 𝓘(ℂ, ℂ)) : X → ℂ) = ⇑f := by
    intro f; ext; rfl
  have hExtSymmC : ∀ (f : OpenPartialHomeomorph X ℂ),
      (⇑(f.extend 𝓘(ℂ, ℂ)).symm : ℂ → X) = ⇑f.symm := by
    intro f; ext; rfl
  have hRangeR : (Set.range 𝓘(ℝ, ℂ) : Set ℂ) = Set.univ :=
    ModelWithCorners.Boundaryless.range_eq_univ
  have hRangeC : (Set.range 𝓘(ℂ, ℂ) : Set ℂ) = Set.univ :=
    ModelWithCorners.Boundaryless.range_eq_univ
  -- Both fderivWithin reduce to fderivWithin _ (j ∘ i.symm) univ (i x).
  rw [show (⇑((j.1 : OpenPartialHomeomorph X ℂ).extend 𝓘(ℝ, ℂ)) ∘
        ⇑((i.1 : OpenPartialHomeomorph X ℂ).extend 𝓘(ℝ, ℂ)).symm)
      = (⇑j.1 ∘ ⇑i.1.symm) from by rw [hExtR, hExtSymmR],
      show (⇑((j.1 : OpenPartialHomeomorph X ℂ).extend 𝓘(ℂ, ℂ)) ∘
        ⇑((i.1 : OpenPartialHomeomorph X ℂ).extend 𝓘(ℂ, ℂ)).symm)
      = (⇑j.1 ∘ ⇑i.1.symm) from by rw [hExtC, hExtSymmC],
      show ((i.1 : OpenPartialHomeomorph X ℂ).extend 𝓘(ℝ, ℂ) x : ℂ) = i.1 x from rfl,
      show ((i.1 : OpenPartialHomeomorph X ℂ).extend 𝓘(ℂ, ℂ) x : ℂ) = i.1 x from rfl,
      hRangeR, hRangeC]
  letI : NormedSpace ℝ ℂ := @NormedAlgebra.toNormedSpace ℝ ℂ _ _ _
  exact
    (DifferentiableWithinAt.restrictScalars_fderivWithin ℝ
      h_diffℂ.differentiableWithinAt uniqueDiffWithinAt_univ).symm

/-! ## Cotangent-bundle core commutativity with `realPartCLM` / `imagPartCLM` -/

/-- The real **cotangent** bundle's coordinate change commutes with the
fibrewise `realPartCLM`: for any covector `ξ : ℂ →L[ℂ] ℂ`, the ℝ-cotangent
coord change applied to `realPartCLM ξ` equals `realPartCLM` applied to
the ℂ-cotangent coord change applied to `ξ`.

This is the fibrewise compatibility that, when threaded through
`cotangentSection_contMDiffAt_iff`, lets us derive smoothness of the
**real** section `fun x => om.realPart x` from the **holomorphic**
section `om`. -/
theorem cotangentBundleCore_coordChange_realPartCLM
    (i j : atlas ℂ X) {x : X} (hxi : x ∈ i.1.source) (hxj : x ∈ j.1.source)
    (ξ : ℂ →L[ℂ] ℂ) :
    (cotangentBundleCore 𝓘(ℝ, ℂ) X).coordChange i j x (realPartCLM ξ) =
      realPartCLM ((cotangentBundleCore 𝓘(ℂ, ℂ) X).coordChange i j x ξ) := by
  rw [cotangentBundleCore_coordChange_apply, cotangentBundleCore_coordChange_apply,
    tangentBundleCore_coordChange_restrictScalars_eq j i hxj hxi]
  -- Now both sides involve `T_ℂ := (tangentBundleCore 𝓘(ℂ, ℂ) X).coordChange j i x`.
  -- LHS: `(realPartCLM ξ).comp (T_ℂ.restrictScalars ℝ)`
  -- RHS: `realPartCLM (ξ.comp T_ℂ)`
  -- Reduce both to their unbundled form `reCLM.comp (...).restrictScalars ℝ`
  -- and conclude by `ext + rfl`.
  rw [realPartCLM_apply, realPartCLM_apply]
  -- LHS: `(reCLM.comp ξ.restrictScalars ℝ).comp (T_ℂ.restrictScalars ℝ)`
  -- RHS: `reCLM.comp ((ξ.comp T_ℂ).restrictScalars ℝ)`
  ext v
  rfl

/-- Analogue of `cotangentBundleCore_coordChange_realPartCLM` for the
imaginary component. -/
theorem cotangentBundleCore_coordChange_imagPartCLM
    (i j : atlas ℂ X) {x : X} (hxi : x ∈ i.1.source) (hxj : x ∈ j.1.source)
    (ξ : ℂ →L[ℂ] ℂ) :
    (cotangentBundleCore 𝓘(ℝ, ℂ) X).coordChange i j x (imagPartCLM ξ) =
      imagPartCLM ((cotangentBundleCore 𝓘(ℂ, ℂ) X).coordChange i j x ξ) := by
  rw [cotangentBundleCore_coordChange_apply, cotangentBundleCore_coordChange_apply,
    tangentBundleCore_coordChange_restrictScalars_eq j i hxj hxi]
  rw [imagPartCLM_apply, imagPartCLM_apply]
  ext v
  rfl

/-! ## Chart-coord representative compatibility under `realPartCLM` / `imagPartCLM`

For any `om : HolomorphicOneForm X`, the **real cotangent bundle's**
chart-coordinate representative of `fun x => om.realPart x` at a point
`x₀` agrees, on an open neighborhood of `x₀`, with `realPartCLM` applied
to the **complex cotangent bundle's** chart-coordinate representative
of `om.eval` at `x₀`. (Same for `imagPart` / `imagPartCLM`.)

This is the fibrewise commutativity packaged as a `Filter.EventuallyEq`
statement around `x₀`, ready to be combined with `om`'s section smoothness
(via `cotangentSection_contMDiffAt_iff`) to yield the section smoothness
of `realComponent` / `imagComponent`. The final smoothness wrap-up (which
threads a manifold-side scalar-restriction step + `ContMDiff.clm_apply` +
back-translation via `cotangentSection_contMDiffAt_iff` for the real
bundle) is *not* attempted here: it requires reconciling the various
`NormedSpace ℝ ℂ` instance diamonds at the level of `𝓘(ℝ, ℂ).prod
𝓘(ℝ, ℂ →L[ℝ] ℝ)`, which is left as a follow-up chip.
-/

/-- The ℝ-chart-coord representative of `fun x => om.realPart x` at `x₀`
agrees, on a neighborhood of `x₀`, with `realPartCLM ∘ (ℂ-chart-coord rep
of om at x₀)`. -/
theorem realPart_chart_rep_eq_eventually
    (om : HolomorphicOneForm X) (x₀ : X) :
    (fun x => (cotangentBundleCore 𝓘(ℝ, ℂ) X).coordChange
      (achart ℂ x) (achart ℂ x₀) x (om.realPart x))
    =ᶠ[nhds x₀]
    (fun x => realPartCLM ((cotangentBundleCore 𝓘(ℂ, ℂ) X).coordChange
      (achart ℂ x) (achart ℂ x₀) x (om.eval x))) := by
  filter_upwards [(chartAt ℂ x₀).open_source.mem_nhds (mem_chart_source ℂ x₀)] with x hx
  rw [show om.realPart x = realPartCLM (om.eval x) from (realPartCLM_eval om x).symm]
  exact cotangentBundleCore_coordChange_realPartCLM (achart ℂ x) (achart ℂ x₀)
    (mem_chart_source ℂ x) hx (om.eval x)

/-- The ℝ-chart-coord representative of `fun x => om.imagPart x` at `x₀`
agrees, on a neighborhood of `x₀`, with `imagPartCLM ∘ (ℂ-chart-coord rep
of om at x₀)`. -/
theorem imagPart_chart_rep_eq_eventually
    (om : HolomorphicOneForm X) (x₀ : X) :
    (fun x => (cotangentBundleCore 𝓘(ℝ, ℂ) X).coordChange
      (achart ℂ x) (achart ℂ x₀) x (om.imagPart x))
    =ᶠ[nhds x₀]
    (fun x => imagPartCLM ((cotangentBundleCore 𝓘(ℂ, ℂ) X).coordChange
      (achart ℂ x) (achart ℂ x₀) x (om.eval x))) := by
  filter_upwards [(chartAt ℂ x₀).open_source.mem_nhds (mem_chart_source ℂ x₀)] with x hx
  rw [show om.imagPart x = imagPartCLM (om.eval x) from (imagPartCLM_eval om x).symm]
  exact cotangentBundleCore_coordChange_imagPartCLM (achart ℂ x) (achart ℂ x₀)
    (mem_chart_source ℂ x) hx (om.eval x)

/-! ## Manifold-level scalar-restriction bridge -/

/-- The ℂ-chart-coord representative of `om : HolomorphicOneForm X` at a
point `x₀` is `ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω` at `x₀`. -/
theorem om_chart_rep_contMDiffAt_complex
    (om : HolomorphicOneForm X) (x₀ : X) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun x => (cotangentBundleCore 𝓘(ℂ, ℂ) X).coordChange
        (achart ℂ x) (achart ℂ x₀) x (om.eval x)) x₀ :=
  (cotangentSection_contMDiffAt_iff (fun x => om.eval x)).mp (om.contMDiff x₀)

/-- **Manifold-restricted-scalars at a point.** A function `f : X → F` that
is `C^n`-smooth as a map between manifolds with source model `𝓘(ℂ, ℂ)`
and target model `𝓘(ℂ, F)` is also `C^n`-smooth with source `𝓘(ℝ, ℂ)`
and target `𝓘(ℝ, F)`. -/
theorem ContMDiffAt_restrictScalars_to_real
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ F]
    {f : X → F} {x₀ : X} {n : WithTop ℕ∞}
    (h : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, F) n f x₀) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, F) n f x₀ := by
  rw [contMDiffAt_iff] at h ⊢
  refine ⟨h.1, ?_⟩
  obtain ⟨_, h2⟩ := h
  letI : NormedSpace ℝ ℂ := @NormedAlgebra.toNormedSpace ℝ ℂ _ _ _
  simp only [mfld_simps] at h2 ⊢
  exact h2.restrict_scalars ℝ

/-! ## Section smoothness — `realComponent` and `imagComponent` building blocks -/

/-- **Section smoothness — real part**. `fun x => om.realPart x` is a
`C^∞` section of the real cotangent bundle. -/
theorem realPart_section_contMDiff (om : HolomorphicOneForm X) :
    ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] ℝ)) ⊤
      (fun x => (TotalSpace.mk' (ℂ →L[ℝ] ℝ) x
          (om.realPart x : CotangentSpace 𝓘(ℝ, ℂ) x) :
        TotalSpace (ℂ →L[ℝ] ℝ) (CotangentSpace 𝓘(ℝ, ℂ)))) := by
  intro x₀
  refine (cotangentSection_contMDiffAt_iff
    (I := 𝓘(ℝ, ℂ)) (fun x => (om.realPart x : CotangentSpace 𝓘(ℝ, ℂ) x))).mpr ?_
  refine ContMDiffAt.congr_of_eventuallyEq ?_ (realPart_chart_rep_eq_eventually om x₀)
  -- Goal: smoothness of `realPartCLM ∘ (ℂ-chart-rep of om)` as a map
  -- `X → ℂ →L[ℝ] ℝ` with X carrying the real manifold structure.
  have h_complex := om_chart_rep_contMDiffAt_complex om x₀
  letI : NormedSpace ℝ (ℂ →L[ℂ] ℂ) := @NormedSpace.complexToReal (ℂ →L[ℂ] ℂ) _ _
  haveI : IsScalarTower ℝ ℂ (ℂ →L[ℂ] ℂ) := by
    constructor
    intro r c φ
    apply ContinuousLinearMap.ext
    intro v
    show (r • c) • φ v = r • c • φ v
    exact smul_assoc r c (φ v)
  have h_real : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℂ] ℂ) ⊤ _ x₀ :=
    (ContMDiffAt_restrictScalars_to_real h_complex).of_le le_top
  have h_clm : ContMDiff 𝓘(ℝ, ℂ →L[ℂ] ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℝ) ⊤ realPartCLM :=
    ContinuousLinearMap.contMDiff realPartCLM
  exact h_clm.contMDiffAt.comp x₀ h_real

/-- **Section smoothness — imaginary part**. `fun x => om.imagPart x` is a
`C^∞` section of the real cotangent bundle. -/
theorem imagPart_section_contMDiff (om : HolomorphicOneForm X) :
    ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] ℝ)) ⊤
      (fun x => (TotalSpace.mk' (ℂ →L[ℝ] ℝ) x
          (om.imagPart x : CotangentSpace 𝓘(ℝ, ℂ) x) :
        TotalSpace (ℂ →L[ℝ] ℝ) (CotangentSpace 𝓘(ℝ, ℂ)))) := by
  intro x₀
  refine (cotangentSection_contMDiffAt_iff
    (I := 𝓘(ℝ, ℂ)) (fun x => (om.imagPart x : CotangentSpace 𝓘(ℝ, ℂ) x))).mpr ?_
  refine ContMDiffAt.congr_of_eventuallyEq ?_ (imagPart_chart_rep_eq_eventually om x₀)
  have h_complex := om_chart_rep_contMDiffAt_complex om x₀
  letI : NormedSpace ℝ (ℂ →L[ℂ] ℂ) := @NormedSpace.complexToReal (ℂ →L[ℂ] ℂ) _ _
  haveI : IsScalarTower ℝ ℂ (ℂ →L[ℂ] ℂ) := by
    constructor
    intro r c φ
    apply ContinuousLinearMap.ext
    intro v
    show (r • c) • φ v = r • c • φ v
    exact smul_assoc r c (φ v)
  have h_real : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℂ] ℂ) ⊤ _ x₀ :=
    (ContMDiffAt_restrictScalars_to_real h_complex).of_le le_top
  have h_clm : ContMDiff 𝓘(ℝ, ℂ →L[ℂ] ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℝ) ⊤ imagPartCLM :=
    ContinuousLinearMap.contMDiff imagPartCLM
  exact h_clm.contMDiffAt.comp x₀ h_real

/-! ## Bundled `realComponent` / `imagComponent` -/

/-- The **real component** of a holomorphic 1-form, packaged as a bundled
smooth real 1-form. -/
def realComponent (om : HolomorphicOneForm X) : SmoothOneForm 𝓘(ℝ, ℂ) X where
  toFun := fun x => om.realPart x
  contMDiff_toFun := realPart_section_contMDiff om

/-- The **imaginary component** of a holomorphic 1-form, packaged as a
bundled smooth real 1-form. -/
def imagComponent (om : HolomorphicOneForm X) : SmoothOneForm 𝓘(ℝ, ℂ) X where
  toFun := fun x => om.imagPart x
  contMDiff_toFun := imagPart_section_contMDiff om

end JacobianChallenge

end
