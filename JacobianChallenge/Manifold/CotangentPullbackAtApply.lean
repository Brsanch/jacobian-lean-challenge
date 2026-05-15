/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CotangentPullbackAt
import JacobianChallenge.Manifold.SmoothPathIntegral
import JacobianChallenge.Manifold.MeromorphicNonzeroTraceAt

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Scalar evaluation of cotangent pullback and trace

Bridging lemmas relating `applyCotangent` to `cotangentPullbackAt` and
`traceAt`. These are the scaffolding for the eventual Stokes-type
integral identity

  `(levelSetChain f β).integrate om
     = ∫ t in 0..1, applyCotangent (traceAt f hnc (hβ_reg t) om) (β.velocity t)`

which expresses the X-chain integral as a ℙ¹-line integral against the
trace 1-form `f_*ω`. This file ships the per-step **scalar identities**;
the smoothness/integrability story for the trace-along-β integrand is
a separate downstream chip.

* `applyCotangent_cotangentPullbackAt` — the cotangent pullback's value
  on a tangent vector unfolds to `om(g y)` paired with the
  `mfderiv g y`-pushforward of that tangent vector. The pure definitional
  identity.

* `applyCotangent_finset_sum` — `applyCotangent (Σ_i c_i) v = Σ_i
  applyCotangent (c_i) v`. The pairing is linear in the cotangent.

* `MeromorphicNonzero.applyCotangent_traceAt` — at a regular value `v`,
  `applyCotangent (traceAt f hnc hv om) w = Σ_{p ∈ fiberFinset} applyCotangent
  (cotangentPullbackAt sheet_p.g v om) w`. The trace pairs as a sum of
  per-sheet pullback contributions.

No `sorry`, no `axiom`. -/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace JacobianChallenge

/-! ## Scalar identity for the cotangent pullback -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ⊤ Y]

/-- **Cotangent pullback unfolds under `applyCotangent`.** Pure
definitional identity: `applyCotangent (cotangentPullbackAt g y om) v
= applyCotangent (om(g y)) (mfderiv g y v)`. -/
lemma applyCotangent_cotangentPullbackAt
    (g : Y → X) (y : Y) (om : SmoothOneForm I X) (v : E') :
    SmoothPath.applyCotangent
      (cotangentPullbackAt (I := I) (I' := I') g y om) v
      = SmoothPath.applyCotangent (om (g y))
          (mfderiv I' I g y v) := by
  unfold cotangentPullbackAt SmoothPath.applyCotangent
  rfl

/-! ## Linearity of `applyCotangent` in the cotangent argument -/

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ⊤ Y]

@[simp] lemma applyCotangent_finset_sum
    {ι : Type*} (S : Finset ι) {y : Y}
    (φ : ι → CotangentSpace I' y) (v : E') :
    SmoothPath.applyCotangent (∑ i ∈ S, φ i) v
      = ∑ i ∈ S, SmoothPath.applyCotangent (φ i) v := by
  classical
  unfold SmoothPath.applyCotangent
  rw [show (SmoothPath.cotangentEquiv (I := I') (X := Y) (x := y) (∑ i ∈ S, φ i))
      = ∑ i ∈ S, SmoothPath.cotangentEquiv (I := I') (X := Y) (x := y) (φ i) from
        map_sum (SmoothPath.cotangentEquiv (I := I') (X := Y) (x := y)) φ S]
  exact ContinuousLinearMap.sum_apply _ _ _

/-! ## Scalar identity for `traceAt` -/

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Scalar pairing of `traceAt` with a tangent vector.** The trace at
a regular value `v` paired with a tangent `w : ℂ` equals the Finset
sum of the per-sheet cotangent-pullback pairings. Direct corollary of
`applyCotangent_finset_sum` applied to the definition of `traceAt`. -/
lemma applyCotangent_traceAt
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X) (w : ℂ) :
    SmoothPath.applyCotangent (f.traceAt hnc hv om) w
      = ∑ p ∈ (f.fiberFinset hv).attach,
          SmoothPath.applyCotangent
            (cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
              (f.localSheetData_at_regular hnc
                (f.mem_regularSet_of_preimage_regularValue hv
                  ((f.mem_fiberFinset_iff hv p.val).mp p.property))).g
              v om) w := by
  classical
  unfold traceAt
  exact applyCotangent_finset_sum (I' := 𝓘(ℝ, ℂ)) _ _ _

end MeromorphicNonzero

end JacobianChallenge

end
