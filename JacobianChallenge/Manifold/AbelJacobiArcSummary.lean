/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiIso

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # PL-4-G: Arc summary — total composition under all named hypotheses

This is the **documentation capstone** of the period-lattice +
Abel-Jacobi arc. It collects every named hypothesis introduced across
PL-3-fin and PL-4 into a single dependent-input theorem, exhibiting
the full transport from the Abel-Jacobi map to a structured
isomorphism on `Pic0 X`.

## The full input set

For a compact connected complex 1-manifold `X`, the following classical
inputs together determine an additive-group isomorphism
`Pic0 X ≃+ AnalyticJacobian` together with the transport of all
analytic-Jacobian instances (TopologicalSpace, ChartedSpace, T2Space,
CompactSpace, IsManifold, LieAddGroup) back to `Pic0 X`:

1. `α : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)` — a ℂ-basis of
   holomorphic 1-forms. Existence depends on
   `[FiniteDimensional ℂ (HolomorphicOneForm X)]` (the
   `HolomorphicOneFormFiniteDim` named hypothesis, the Hodge gap).

2. `h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α`
   — a Riemann-bilinear bundle (PL-3-fin chip 1) consisting of:
   * `h.h1Basis : Basis (Fin (2 * genus X)) ℤ (SmoothCycle 𝓘(ℝ, ℂ) X)`
     — H₁(X; ℤ) free of rank 2g.
   * `h.periodBasis : Basis (Fin (2 * genus X)) ℝ (Fin (genus X) → ℂ)`
     — the period vectors form an ℝ-basis (Riemann bilinear non-degeneracy).
   * compatibility constraint.

3. `B : AbelJacobiInput α h` (PL-4-C) — a base point and smooth-path-picker.
   Existence depends on smooth-path-connectedness, a small mathlib gap.

4. `hAbel : B.AbelHypothesis` (PL-4-E) — Abel's theorem for `X`: the
   AJ map vanishes on principal divisors. Classical, requires Stokes
   on 2-chains.

5. `hJI : B.JacobiInversion hAbel` (PL-4-F) — Jacobi inversion: the AJ
   map is bijective. Classical, requires Abel's converse + Jacobi
   inversion theorem proper.

## What this file delivers

* `AbelJacobiHypothesisBundle X` — a single structure aggregating all
  five inputs above.

* `bundleEquiv H : Pic0 X ≃+ AnalyticJacobian ...` — the resulting
  Abel-Jacobi isomorphism, built from the bundle's components.

* Convenience reductions: `bundleEquiv_apply` and
  `bundleEquiv_mk` to unfold the equiv on representatives.

This file does **not** produce typeclass instances on `Pic0 X` (or
`Jacobian X := Pic0 X`) because the discharge depends on five named
hypotheses that are not typeclass-resolvable. Once individual
hypotheses land as unconditional theorems, downstream files can
substitute them and derive global instances.

After this chip, the period-lattice arc's structural shape is
complete: every step from `complexPeriodBilinear` to
`Pic0 X ≃+ AnalyticJacobian` exists in the repo. The remaining work
is **discharging the named hypotheses** (1)–(5) above, each of which
is multi-thousand-LOC classical content.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff
open Submodule Module

namespace JacobianChallenge

variable (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **The full Abel-Jacobi hypothesis bundle.** Aggregates the five
classical inputs `(α, h, B, hAbel, hJI)` that together pin down the
Abel-Jacobi isomorphism on a compact connected complex 1-manifold. -/
structure AbelJacobiHypothesisBundle where
  /-- ℂ-basis of holomorphic 1-forms. Existence: `HolomorphicOneFormFiniteDim`. -/
  formBasis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)
  /-- Riemann-bilinear discreteness bundle on smooth cycles. -/
  discreteness :
    PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) formBasis
  /-- Base point + smooth-path-picker. -/
  basePoint : AbelJacobiInput formBasis discreteness
  /-- Abel's theorem: AJ vanishes on principal divisors. -/
  abelHyp : basePoint.AbelHypothesis
  /-- Jacobi inversion: AJ is bijective on Pic0. -/
  jacobiInv : basePoint.JacobiInversion abelHyp

namespace AbelJacobiHypothesisBundle

variable {X}

/-- **The Abel-Jacobi isomorphism from the bundle.** -/
noncomputable def bundleEquiv (H : AbelJacobiHypothesisBundle X) :
    Pic0 X ≃+ AnalyticJacobian
      (PeriodPairingData.ofSmoothCycle X) H.formBasis H.discreteness :=
  H.basePoint.abelJacobiEquiv H.abelHyp H.jacobiInv

@[simp] lemma bundleEquiv_apply (H : AbelJacobiHypothesisBundle X) (c : Pic0 X) :
    H.bundleEquiv c = H.basePoint.abelJacobi H.abelHyp c := rfl

lemma bundleEquiv_mk (H : AbelJacobiHypothesisBundle X) (D : Div0 X) :
    H.bundleEquiv (QuotientAddGroup.mk D : Pic0 X)
      = H.basePoint.abelJacobiDiv (D : Div X) := by
  show H.basePoint.abelJacobiEquiv H.abelHyp H.jacobiInv
      (QuotientAddGroup.mk D : Pic0 X) = _
  exact AbelJacobiInput.abelJacobiEquiv_mk H.basePoint H.abelHyp H.jacobiInv D

/-! ## Transported analytic structure (existence statements)

These theorems witness that under the full bundle, `Pic0 X` carries
the analytic-Jacobian structures (transported across `bundleEquiv`).
They are stated as `∃` because the literal typeclass instances on
`Pic0 X` already exist (currently as stubs); to *replace* those would
require touching `Basic.lean` (frozen as verbatim Buzzard spec).
The witnesses below are usable as alternative-topology theorems. -/

/-- **Witness:** under the bundle, `Pic0 X` admits a `TopologicalSpace`
making `bundleEquiv` a homeomorphism. -/
theorem exists_topologicalSpace_pic0_compatible
    (H : AbelJacobiHypothesisBundle X) :
    ∃ τ : TopologicalSpace (Pic0 X),
      @Continuous _ _ τ
        (inferInstance : TopologicalSpace
          (AnalyticJacobian _ H.formBasis H.discreteness))
        H.bundleEquiv ∧
      @Continuous _ _ (inferInstance : TopologicalSpace
          (AnalyticJacobian _ H.formBasis H.discreteness)) τ
        H.bundleEquiv.symm := by
  -- The induced topology (along `bundleEquiv`) makes the equiv a homeomorphism.
  refine ⟨TopologicalSpace.induced H.bundleEquiv inferInstance, ?_, ?_⟩
  · exact continuous_induced_dom
  · -- `bundleEquiv.symm` is continuous from the codomain (with its own topology)
    -- to the domain (with the induced topology). Standard `Equiv.coinduced` /
    -- `induced` API.
    refine continuous_induced_rng.mpr ?_
    -- bundleEquiv ∘ bundleEquiv.symm = id, which is continuous.
    have h_id : (H.bundleEquiv : Pic0 X → _) ∘ (H.bundleEquiv.symm : _ → Pic0 X)
        = id := by
      funext y; exact H.bundleEquiv.apply_symm_apply y
    rw [h_id]
    exact continuous_id

end AbelJacobiHypothesisBundle

end JacobianChallenge

end
