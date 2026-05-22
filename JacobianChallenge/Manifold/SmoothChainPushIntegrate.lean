/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothChainPush
import JacobianChallenge.Manifold.SmoothPathPushIntegrate

set_option linter.unusedSectionVars false

/-! # Chain-level change-of-variables: `SmoothChain.integrate_push`

Lifts chip 52's path-level identity to ℤ-linear smooth 1-chains via
`Finsupp.sum_mapDomain_index`:

  `SmoothChain.integrate (SmoothChain.push f hf c) om
    = SmoothChain.integrate c (SmoothOneForm.pullback f hf om)`.

And the immediate corollary for cycles (since `SmoothCycle ⊆ SmoothChain`).

This is the lift of OneForm functoriality from individual paths to the
ℤ-linear combinations they generate — the bridge between the geometric
change-of-variables (chip 52) and the abstract period-pairing
adjunction (chip 54).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Finsupp SmoothChain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ⊤ Y]

namespace JacobianChallenge.SmoothChain

/-- **Chain-level change-of-variables for `SmoothChain.push`.**
`integrate (push f hf c) om = integrate c (SmoothOneForm.pullback f hf om)`.

Proof: rewrite both sides as `Finsupp.sum`s; on the LHS, push commutes
with sum via `Finsupp.sum_mapDomain_index` (`SmoothChain.push = lmapDomain`);
on the resulting sum, apply chip 52 (`SmoothPath.integrate_push`)
pointwise. -/
theorem integrate_push {f : X → Y}
    (hf : ContMDiff I I ω f)
    (c : _root_.SmoothChain I X) (om : SmoothOneForm I Y) :
    _root_.SmoothChain.integrate
        (JacobianChallenge.SmoothChain.push f
          (hf.of_le (le_top : (∞ : WithTop ℕ∞) ≤ ω)) c) om
      = _root_.SmoothChain.integrate c
          (SmoothOneForm.pullback (I := I) (I' := I) f hf om) := by
  classical
  set hf_smooth : ContMDiff I I ∞ f := hf.of_le (le_top : (∞ : WithTop ℕ∞) ≤ ω)
  -- Step 1: Rewrite `integrate` as `Finsupp.sum`.
  have h_int_eq : ∀ (c' : _root_.SmoothPath I Y →₀ ℤ) (ω' : SmoothOneForm I Y),
      _root_.SmoothChain.integrate (c' : _root_.SmoothChain I Y) ω'
        = c'.sum (fun γ n => (n : ℝ) * γ.integrate ω') := fun _ _ => rfl
  have h_int_eq_X : ∀ (c' : _root_.SmoothPath I X →₀ ℤ) (ω' : SmoothOneForm I X),
      _root_.SmoothChain.integrate (c' : _root_.SmoothChain I X) ω'
        = c'.sum (fun γ n => (n : ℝ) * γ.integrate ω') := fun _ _ => rfl
  rw [h_int_eq, h_int_eq_X]
  -- Step 2: `push c = mapDomain (SmoothPath.push f hf_smooth) c`.
  have h_push : JacobianChallenge.SmoothChain.push f hf_smooth c
      = Finsupp.mapDomain (JacobianChallenge.SmoothPath.push f hf_smooth) c := by
    change Finsupp.lmapDomain ℤ ℤ (JacobianChallenge.SmoothPath.push f hf_smooth) c
      = Finsupp.mapDomain (JacobianChallenge.SmoothPath.push f hf_smooth) c
    rw [Finsupp.lmapDomain_apply]
  rw [h_push]
  -- Step 3: Apply Finsupp.sum_mapDomain_index.
  rw [Finsupp.sum_mapDomain_index
    (h_zero := by
      intro δ
      push_cast
      ring)
    (h_add := by
      intro δ n m
      push_cast
      ring)]
  -- Step 4: Pointwise chip 52.
  apply Finsupp.sum_congr
  intro γ _
  rw [JacobianChallenge.SmoothPath.integrate_push hf γ om]

end JacobianChallenge.SmoothChain

namespace JacobianChallenge.SmoothCycle

/-- **Cycle-level change-of-variables for `SmoothCycle.pushHom`.** -/
theorem integrate_pushHom {f : X → Y}
    (hf : ContMDiff I I ω f)
    (c : JacobianChallenge.SmoothCycle I X) (om : SmoothOneForm I Y) :
    JacobianChallenge.SmoothCycle.integrate
        (JacobianChallenge.SmoothCycle.pushHom f
          (hf.of_le (le_top : (∞ : WithTop ℕ∞) ≤ ω)) c) om
      = JacobianChallenge.SmoothCycle.integrate c
          (SmoothOneForm.pullback (I := I) (I' := I) f hf om) := by
  -- Unfold cycle.integrate = chain.integrate on coerced underlying chain.
  change _root_.SmoothChain.integrate
        (JacobianChallenge.SmoothChain.push f
          (hf.of_le (le_top : (∞ : WithTop ℕ∞) ≤ ω)) (c : _root_.SmoothChain I X)) om
      = _root_.SmoothChain.integrate ((c : _root_.SmoothChain I X))
          (SmoothOneForm.pullback (I := I) (I' := I) f hf om)
  exact JacobianChallenge.SmoothChain.integrate_push hf
    (c : _root_.SmoothChain I X) om

end JacobianChallenge.SmoothCycle

end
