/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PullbackHolomorphicOneForm
import JacobianChallenge.Manifold.HolomorphicEquivSubsingletonTransfer
import JacobianChallenge.Topology.S2ImpliesGenus0Discharge
import JacobianChallenge.Topology.Genus0ImpliesS2Reduction
import JacobianChallenge.Topology.Item14FromUniformization

set_option diagnostics.threshold 100
set_option maxHeartbeats 1600000

/-! # `HolomorphicEquiv` → `ℂ`-linear equivalence of holomorphic-1-form spaces

zz307 ships `HolomorphicEquiv.pullbackForm` as a genuine
`HolomorphicOneForm`, with `pullbackForm_eval = pullbackPointwise`. This
file upgrades it to a `ℂ`-LinearEquiv between holomorphic-1-form
spaces, using:

* zz303's `pullbackPointwise_add` and `pullbackPointwise_smul` (linearity),
* zz295's `mfderiv_symm_comp_mfderiv_self` (chain rule on
  `HolomorphicEquiv`),
* `HolomorphicOneForm` extensionality.

The headline output is:

`HolomorphicEquiv.pullbackLinearEquiv e : HolomorphicOneForm Y ≃ₗ[ℂ] HolomorphicOneForm X`

Specialised at `Y = RiemannSphere` (and inverted to match the
`HolomorphicOneFormEquivRiemannSphere` convention `X ≃ₗ RS`), this
discharges
`HolomorphicOneFormEquivRiemannSphere X` from
`HolomorphicEquiv X RiemannSphere`.

Combined with zz307's `Subsingleton`-route and the existing
`Genus0ImpliesS2_of_homeoRiemannSphere` reduction, both reduction
lemmas in the item-14 biconditional are now closed from a single
`HolomorphicEquiv X RiemannSphere` hypothesis — i.e., item 14 holds
unconditionally for any `X` biholomorphic to the Riemann sphere.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff
open ContinuousLinearMap

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-! ## ℂ-linearity of `pullbackForm` -/

theorem HolomorphicEquiv.pullbackForm_add
    (e : HolomorphicEquiv X Y) (α β : HolomorphicOneForm Y) :
    e.pullbackForm (α + β) = e.pullbackForm α + e.pullbackForm β := by
  refine ContMDiffSection.coe_injective ?_
  funext x
  show e.pullbackPointwise (α + β) x
    = e.pullbackPointwise α x + e.pullbackPointwise β x
  exact congrFun (HolomorphicEquiv.pullbackPointwise_add e α β) x

theorem HolomorphicEquiv.pullbackForm_smul
    (e : HolomorphicEquiv X Y) (c : ℂ) (α : HolomorphicOneForm Y) :
    e.pullbackForm (c • α) = c • e.pullbackForm α := by
  refine ContMDiffSection.coe_injective ?_
  funext x
  show e.pullbackPointwise (c • α) x = c • e.pullbackPointwise α x
  exact congrFun (HolomorphicEquiv.pullbackPointwise_smul e c α) x

/-- **Pullback as a ℂ-linear map.** (Direct, no smoothness obligation.) -/
def HolomorphicEquiv.pullbackLinearMap_direct
    (e : HolomorphicEquiv X Y) :
    HolomorphicOneForm Y →ₗ[ℂ] HolomorphicOneForm X where
  toFun := e.pullbackForm
  map_add' := e.pullbackForm_add
  map_smul' c α := e.pullbackForm_smul c α

@[simp]
theorem HolomorphicEquiv.pullbackLinearMap_direct_apply
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm Y) :
    e.pullbackLinearMap_direct α = e.pullbackForm α := rfl

/-! ## The inverse relation `e.pullbackForm ∘ e.symm.pullbackForm = id`

Pointwise: for `α : HolomorphicOneForm X` and `x : X`,
```
(e.pullbackForm (e.symm.pullbackForm α)).eval x
  = (e.symm.pullbackForm α).eval (e x) ∘L mfderiv e x
  = ((α.eval (e.symm (e x))) ∘L mfderiv e.symm (e x)) ∘L mfderiv e x
  = (α.eval x) ∘L (mfderiv e.symm (e x) ∘L mfderiv e x)
  = (α.eval x) ∘L id
  = α.eval x
```

The chain-rule identity in the third-to-last line is zz295's
`HolomorphicEquiv.mfderiv_symm_comp_mfderiv_self`. -/

theorem HolomorphicEquiv.pullbackForm_pullbackForm_symm
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm X) :
    e.pullbackForm (e.symm.pullbackForm α) = α := by
  refine ContMDiffSection.coe_injective ?_
  funext x
  -- Unfold both sides to CLM compositions.
  show ContinuousLinearMap.comp
      (HolomorphicOneForm.eval (e.symm.pullbackForm α) ((e : X → Y) x))
      (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (e : X → Y) x)
    = α.toFun x
  -- e.symm.pullbackForm α eval at (e x).
  have h_inner :
      HolomorphicOneForm.eval (e.symm.pullbackForm α) ((e : X → Y) x)
        = ContinuousLinearMap.comp (HolomorphicOneForm.eval α x)
            (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
              (e.toEquiv.symm : Y → X) ((e : X → Y) x)) := by
    show ContinuousLinearMap.comp
        (HolomorphicOneForm.eval α
          ((e.toEquiv.symm : Y → X) ((e : X → Y) x)))
        (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
          (e.toEquiv.symm : Y → X) ((e : X → Y) x))
      = _
    congr 1
    · congr 1
      show e.toEquiv.symm (e.toEquiv x) = x
      exact e.toEquiv.symm_apply_apply x
  rw [h_inner]
  -- Now: (α.eval x ∘L mfderiv e.symm (e x)) ∘L mfderiv e x = α.toFun x.
  -- Use chain rule from zz295.
  have h_chain := e.mfderiv_symm_comp_mfderiv_self x
  -- h_chain: mfderiv e.symm (e x) .comp (mfderiv e x) = id
  apply ContinuousLinearMap.ext
  intro v
  -- Reduce inner expression `mfderiv e.symm (e x) (mfderiv e x v) = v`.
  have h_inner_apply : (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
            (e.toEquiv.symm : Y → X) ((e : X → Y) x))
            ((mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (e : X → Y) x) v) = v := by
    have := congrArg (fun f : TangentSpace (𝓘(ℂ, ℂ)) x →L[ℂ]
        TangentSpace (𝓘(ℂ, ℂ)) x => f v) h_chain
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      using this
  show HolomorphicOneForm.eval α x
      ((mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (e.toEquiv.symm : Y → X) ((e : X → Y) x))
        ((mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (e : X → Y) x) v))
    = HolomorphicOneForm.eval α x v
  rw [h_inner_apply]

theorem HolomorphicEquiv.pullbackForm_symm_pullbackForm
    (e : HolomorphicEquiv X Y) (β : HolomorphicOneForm Y) :
    e.symm.pullbackForm (e.pullbackForm β) = β := by
  -- Apply the previous lemma to e.symm. e.symm.symm = e (up to defeq).
  refine ContMDiffSection.coe_injective ?_
  funext y
  show ContinuousLinearMap.comp
      (HolomorphicOneForm.eval (e.pullbackForm β)
        ((e.toEquiv.symm : Y → X) y))
      (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (e.toEquiv.symm : Y → X) y)
    = β.toFun y
  have h_inner :
      HolomorphicOneForm.eval (e.pullbackForm β)
        ((e.toEquiv.symm : Y → X) y)
        = ContinuousLinearMap.comp (HolomorphicOneForm.eval β y)
            (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
              (e : X → Y) ((e.toEquiv.symm : Y → X) y)) := by
    show ContinuousLinearMap.comp
        (HolomorphicOneForm.eval β
          ((e : X → Y) ((e.toEquiv.symm : Y → X) y)))
        (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
          (e : X → Y) ((e.toEquiv.symm : Y → X) y))
      = _
    congr 1
    · congr 1
      show e.toEquiv (e.toEquiv.symm y) = y
      exact e.toEquiv.apply_symm_apply y
  rw [h_inner]
  -- Chain rule on e.symm: mfderiv e (e.symm y) .comp (mfderiv e.symm y) = id.
  have h_chain := e.symm.mfderiv_symm_comp_mfderiv_self y
  -- Note: e.symm.toEquiv.symm = e.toEquiv (Equiv.symm_symm).
  apply ContinuousLinearMap.ext
  intro v
  have h_chain' : (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (e : X → Y) ((e.toEquiv.symm : Y → X) y)).comp
        (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
          (e.toEquiv.symm : Y → X) y) =
      ContinuousLinearMap.id ℂ (TangentSpace (𝓘(ℂ, ℂ)) y) := by
    convert h_chain using 2
  have h_apply : (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (e : X → Y) ((e.toEquiv.symm : Y → X) y))
        ((mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
          (e.toEquiv.symm : Y → X) y) v) = v := by
    have := congrArg (fun f : TangentSpace (𝓘(ℂ, ℂ)) y →L[ℂ]
        TangentSpace (𝓘(ℂ, ℂ)) y => f v) h_chain'
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      using this
  show HolomorphicOneForm.eval β y
      ((mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (e : X → Y) ((e.toEquiv.symm : Y → X) y))
        ((mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
          (e.toEquiv.symm : Y → X) y) v))
    = HolomorphicOneForm.eval β y v
  rw [h_apply]

/-! ## `LinearEquiv` packaging -/

/-- **Pullback as a ℂ-linear equivalence.** For any biholomorphism
`e : HolomorphicEquiv X Y`, the pullback `e.pullbackForm` is a
`ℂ`-linear equivalence between the spaces of holomorphic 1-forms, with
inverse `e.symm.pullbackForm`. -/
def HolomorphicEquiv.pullbackLinearEquiv
    (e : HolomorphicEquiv X Y) :
    HolomorphicOneForm Y ≃ₗ[ℂ] HolomorphicOneForm X where
  toFun := e.pullbackForm
  invFun := e.symm.pullbackForm
  map_add' := HolomorphicEquiv.pullbackForm_add e
  map_smul' c α := HolomorphicEquiv.pullbackForm_smul e c α
  left_inv β := HolomorphicEquiv.pullbackForm_symm_pullbackForm e β
  right_inv α := HolomorphicEquiv.pullbackForm_pullbackForm_symm e α

@[simp]
theorem HolomorphicEquiv.pullbackLinearEquiv_apply
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm Y) :
    e.pullbackLinearEquiv α = e.pullbackForm α := rfl

@[simp]
theorem HolomorphicEquiv.pullbackLinearEquiv_symm_apply
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm X) :
    e.pullbackLinearEquiv.symm α = e.symm.pullbackForm α := rfl

/-! ## Specialisation to `RiemannSphere`

Note the direction reversal: `HolomorphicOneFormEquivRiemannSphere X`
is `Nonempty (HolomorphicOneForm X ≃ₗ[ℂ] HolomorphicOneForm RS)` —
i.e., `X → RS`. From `e : HolomorphicEquiv X RS` we get the
linear equivalence `HolomorphicOneForm RS ≃ₗ HolomorphicOneForm X`
via `e.pullbackLinearEquiv`; the symm version gives `X ≃ₗ RS`. -/

/-- **`HolomorphicOneFormEquivRiemannSphere` from a biholomorphism with
the Riemann sphere.** This discharges the open hypothesis of zz...'s
`s2ImpliesGenus0_of_linearEquiv`. -/
theorem HolomorphicEquiv.holomorphicOneFormEquivRiemannSphere_of_HolomorphicEquiv
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere) :
    HolomorphicOneFormEquivRiemannSphere X :=
  ⟨e.pullbackLinearEquiv.symm⟩

/-! ## `UniformizationGenus0` from a biholomorphism with the Riemann sphere -/

/-- **`UniformizationGenus0` from a biholomorphism.** A
`HolomorphicEquiv X RS` immediately downcasts to a homeomorphism, so
`UniformizationGenus0 X` (which only uses the homeomorphism) is
discharged. The `genus X = 0` hypothesis is unused — the conclusion
follows directly from the biholomorphism, regardless of the genus. -/
theorem HolomorphicEquiv.uniformizationGenus0_of_HolomorphicEquiv
    [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere) :
    UniformizationGenus0 X :=
  fun _ => ⟨e.toHomeomorph⟩

/-! ## Full item-14 closure for `X` biholomorphic to the Riemann sphere

Both reduction lemmas are now closed from a single
`HolomorphicEquiv X RS` hypothesis:

* `Genus0ImpliesS2 X` via `genus0ImpliesS2_of_homeoRiemannSphere` +
  `uniformizationGenus0_of_HolomorphicEquiv` (this file).
* `S2ImpliesGenus0 X` via `s2ImpliesGenus0_of_linearEquiv` +
  `holomorphicOneFormEquivRiemannSphere_of_HolomorphicEquiv` (this file)
  + `genus_RiemannSphere_statement_holds` (zz274, unconditional).

Composed, this proves `genus_eq_zero_iff_homeo` (the statement of
challenge item 14) for any `X` biholomorphic to the Riemann sphere. -/

/-- **Item 14 closure for `X` biholomorphic to the Riemann sphere.**
Given `e : HolomorphicEquiv X RiemannSphere`, the biconditional
`genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2)` holds unconditionally.

Note: the biholomorphism with the Riemann sphere is genuinely classical
input — uniformization is the bridge between "topologically a sphere"
and "biholomorphic to RS". Within mathlib, item 14 STILL requires
uniformization (or surface classification) for general `X`; this
theorem closes the specific case where the uniformization hypothesis
is already supplied. -/
theorem genus_eq_zero_iff_homeo_of_HolomorphicEquiv_RiemannSphere
    [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere) :
    JacobianChallenge.genus X = 0
      ↔ Nonempty (X ≃ₜ StandardS2) := by
  refine genus_eq_zero_iff_homeo_of_uniformization_inputs
    (e.uniformizationGenus0_of_HolomorphicEquiv)
    (e.holomorphicOneFormEquivRiemannSphere_of_HolomorphicEquiv)

end JacobianChallenge

end
