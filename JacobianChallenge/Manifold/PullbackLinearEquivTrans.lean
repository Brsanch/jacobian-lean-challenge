/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PullbackLinearEquiv
import JacobianChallenge.Manifold.HolomorphicEquivSubsingletonTransfer

set_option diagnostics.threshold 100
set_option maxHeartbeats 1000000

/-! # Functoriality of `pullbackLinearEquiv` under `.trans`

This file ships the chain-rule companion to zz311's
`pullbackLinearEquiv_symm_eq` and zz312's `pullbackLinearEquiv_refl`:

  pullbackForm_trans :
    (e₁.trans e₂).pullbackForm α
      = e₁.pullbackForm (e₂.pullbackForm α)

  pullbackLinearEquiv_trans :
    (e₁.trans e₂).pullbackLinearEquiv
      = e₂.pullbackLinearEquiv.trans e₁.pullbackLinearEquiv

Both lemmas reduce to the pointwise chain-rule identity

  mfderiv (e₁.trans e₂) x = (mfderiv e₂ (e₁ x)).comp (mfderiv e₁ x)

(`mfderiv_comp` for two `MDifferentiableAt` maps) plus
`ContinuousLinearMap.comp_assoc` to align the resulting
`α.eval (e₂ (e₁ x)) ∘ mfderiv e₂ ∘ mfderiv e₁` against the iterated
pullback shape.

No `sorry`, no `axiom`. Together with zz311/zz312, this completes the
`refl`/`symm`/`trans` functorial trio for `pullbackLinearEquiv`.
-/

open scoped Manifold ContDiff
open ContinuousLinearMap

noncomputable section

namespace JacobianChallenge

variable {X Y Z : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
  [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ, ℂ) ω Z]

/-! ## Pointwise pullback under `.trans` -/

/-- **Chain-rule for `pullbackPointwise` under `.trans`.** Pointwise
pullback along `e₁.trans e₂` factors as the iterated pullback first
along `e₂`, then along `e₁`. -/
theorem HolomorphicEquiv.pullbackPointwise_trans
    (e₁ : HolomorphicEquiv X Y) (e₂ : HolomorphicEquiv Y Z)
    (α : HolomorphicOneForm Z) (x : X) :
    (e₁.trans e₂).pullbackPointwise α x
      = e₁.pullbackPointwise (e₂.pullbackForm α) x := by
  -- Unfold both sides via `pullbackPointwise_apply`.
  -- LHS: (α.eval ((e₁.trans e₂) x)).comp (mfderiv 𝓘 𝓘 (e₁.trans e₂) x)
  -- RHS: ((e₂.pullbackForm α).eval (e₁ x)).comp (mfderiv 𝓘 𝓘 e₁ x)
  --    = (e₂.pullbackPointwise α (e₁ x)).comp (mfderiv 𝓘 𝓘 e₁ x)
  --    = ((α.eval (e₂ (e₁ x))).comp (mfderiv e₂ (e₁ x))).comp (mfderiv e₁ x)
  rw [HolomorphicEquiv.pullbackPointwise_apply,
      HolomorphicEquiv.pullbackPointwise_apply]
  -- Goal:
  --   (α.eval ((e₁.trans e₂) x)).comp (mfderiv 𝓘 𝓘 (e₁.trans e₂ : X → Z) x)
  --     = ((e₂.pullbackForm α).eval (e₁ x)).comp (mfderiv 𝓘 𝓘 (e₁ : X → Y) x)
  -- Step 1: rewrite (e₂.pullbackForm α).eval (e₁ x) as
  --   e₂.pullbackPointwise α (e₁ x)
  -- by definition of pullbackForm.
  have h_eval :
      HolomorphicOneForm.eval (e₂.pullbackForm α) (e₁ x)
        = e₂.pullbackPointwise α (e₁ x) := rfl
  rw [h_eval, HolomorphicEquiv.pullbackPointwise_apply]
  -- Goal:
  --   (α.eval ((e₁.trans e₂) x)).comp (mfderiv 𝓘 𝓘 (e₁.trans e₂ : X → Z) x)
  --     = ((α.eval (e₂ (e₁ x))).comp (mfderiv 𝓘 𝓘 (e₂ : Y → Z) (e₁ x))).comp
  --         (mfderiv 𝓘 𝓘 (e₁ : X → Y) x)
  -- Step 2: align (e₁.trans e₂) x with e₂ (e₁ x).
  have h_apply : ((e₁.trans e₂ : HolomorphicEquiv X Z) : X → Z) x = e₂ (e₁ x) := by
    show (e₂ ∘ e₁) x = e₂ (e₁ x)
    rfl
  rw [h_apply]
  -- Goal:
  --   (α.eval (e₂ (e₁ x))).comp (mfderiv 𝓘 𝓘 (e₁.trans e₂ : X → Z) x)
  --     = ((α.eval (e₂ (e₁ x))).comp (mfderiv 𝓘 𝓘 (e₂ : Y → Z) (e₁ x))).comp
  --         (mfderiv 𝓘 𝓘 (e₁ : X → Y) x)
  -- Step 3: rewrite mfderiv (e₁.trans e₂) via chain rule.
  have h_coe : ((e₁.trans e₂ : HolomorphicEquiv X Z) : X → Z)
        = (e₂ : Y → Z) ∘ (e₁ : X → Y) := rfl
  rw [h_coe]
  rw [mfderiv_comp x (e₂.mdifferentiableAt (e₁ x)) (e₁.mdifferentiableAt x)]
  -- Goal:
  --   (α.eval (e₂ (e₁ x))).comp
  --     ((mfderiv 𝓘 𝓘 (e₂ : Y → Z) (e₁ x)).comp (mfderiv 𝓘 𝓘 (e₁ : X → Y) x))
  --     = ((α.eval (e₂ (e₁ x))).comp (mfderiv 𝓘 𝓘 (e₂ : Y → Z) (e₁ x))).comp
  --         (mfderiv 𝓘 𝓘 (e₁ : X → Y) x)
  -- Step 4: associativity of composition (rfl, exposed via `comp_assoc`).
  exact (ContinuousLinearMap.comp_assoc _ _ _).symm

/-! ## Form-level pullback under `.trans` -/

/-- **Chain-rule for `pullbackForm` under `.trans`.** -/
theorem HolomorphicEquiv.pullbackForm_trans
    (e₁ : HolomorphicEquiv X Y) (e₂ : HolomorphicEquiv Y Z)
    (α : HolomorphicOneForm Z) :
    (e₁.trans e₂).pullbackForm α = e₁.pullbackForm (e₂.pullbackForm α) := by
  refine
    (show (((e₁.trans e₂).pullbackForm α :
              ContMDiffSection (𝕜 := ℂ) (E := ℂ) (H := ℂ) (M := X)
                𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω (CotangentSpace 𝓘(ℂ) : X → Type _))
            = e₁.pullbackForm (e₂.pullbackForm α))
        from ContMDiffSection.ext (fun x => ?_))
  exact HolomorphicEquiv.pullbackPointwise_trans e₁ e₂ α x

/-! ## `LinearEquiv` level -/

/-- **`pullbackLinearEquiv` is functorial under `.trans`.** -/
theorem HolomorphicEquiv.pullbackLinearEquiv_trans
    (e₁ : HolomorphicEquiv X Y) (e₂ : HolomorphicEquiv Y Z) :
    (e₁.trans e₂).pullbackLinearEquiv
      = e₂.pullbackLinearEquiv.trans e₁.pullbackLinearEquiv := by
  refine LinearEquiv.ext fun α => ?_
  -- LHS via pullbackLinearEquiv_apply: (e₁.trans e₂).pullbackForm α
  -- RHS via LinearEquiv.trans_apply + pullbackLinearEquiv_apply twice:
  --   e₁.pullbackForm (e₂.pullbackForm α)
  exact HolomorphicEquiv.pullbackForm_trans e₁ e₂ α

end JacobianChallenge

end
