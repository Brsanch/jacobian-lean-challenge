/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasC3FullClassicalContent
import JacobianChallenge.Manifold.SurfaceClassificationDataGenusZero
import JacobianChallenge.Manifold.BasedSmoothLoopsBoundTransport
import JacobianChallenge.Manifold.HolomorphicEquivGenusInvariance
import JacobianChallenge.Manifold.StokesBoundariesTopRiemannSphere
import JacobianChallenge.Manifold.RiemannSphereGenusFromVanishing

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # `HasC3FullClassicalContent X` from a biholomorphism `X ≃ RS`

Composes four in-tree pieces to discharge the C3 umbrella class on
any X biholomorphic to `RiemannSphere`:

* **Genus invariance** (`HolomorphicEquiv.genus_eq`) — transports
  `genus RS = 0` to `genus X = 0`.
* **BSLB transport** (chip 28
  `basedSmoothLoopsBoundHypothesis_pushforward_biholomorphism`) —
  transports `BSLB RS q₀` to `BSLB X (φ.symm q₀)`.
* **HSCD from genus 0 + BSLB** (chip 26
  `SurfaceClassificationData.ofGenusZero`) — builds the SCD on X.
* **RFBR + RSRP polymorphic at g=0** (chips 11 + 19) — both Riemann
  relations hold trivially at g=0 for any cycleGens.

Net contribution: substantive uniformization-adjacent content. The
remaining open named atom at g=0 is the **uniformization theorem**:
any compact connected complex 1-manifold of genus 0 is biholomorphic
to RS. This chip factors that single classical statement as the
*only* missing piece between `genus X = 0` and unconditional C3
umbrella on X.

## What this file ships

* `hasC3FullClassicalContent_of_nonemptyHolomorphicEquiv_RiemannSphere` —
  HasC3FullClassicalContent X from `Nonempty (HolomorphicEquiv X RS)`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

/-- **C3 umbrella from biholomorphism to `RiemannSphere`.**

For any compact connected complex 1-manifold `X` biholomorphic to
`RiemannSphere`, the C3 umbrella class `HasC3FullClassicalContent X`
holds unconditionally.

Strategy: transport BSLB along the biholomorphism (chip 28), bundle
into HSCD via the genus-0 specialization (chip 26), then discharge
RFBR + RSRP trivially at g=0. -/
theorem hasC3FullClassicalContent_of_nonemptyHolomorphicEquiv_RiemannSphere
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (h : Nonempty (HolomorphicEquiv X RiemannSphere)) :
    HasC3FullClassicalContent X := by
  obtain ⟨φ⟩ := h
  -- Genus X = 0 via genus invariance + genus RS = 0.
  have h_genus : JacobianChallenge.genus X = 0 := by
    rw [HolomorphicEquiv.genus_eq φ]
    exact RiemannSphere.genus_RiemannSphere_eq_zero
  -- Pick a basepoint p₀ : X via the RS basepoint pulled back through φ.symm.
  set q₀ : RiemannSphere := Classical.arbitrary _ with hq₀_def
  set p₀ : X := φ.toEquiv.symm q₀ with hp₀_def
  -- BSLB on X at p₀ via chip 28 + BSLB on RS at q₀.
  have h_bslb : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X p₀ := by
    have h_RS : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) RiemannSphere q₀ :=
      RiemannSphere.basedSmoothLoopsBoundHypothesis_RS_holds q₀
    -- Apply chip 28 with `φ.symm : HolomorphicEquiv RS X`.
    exact basedSmoothLoopsBoundHypothesis_pushforward_biholomorphism
      φ.symm q₀ h_RS
  -- Build the SCD on X via chip 26.
  refine ⟨?_, defaultHolomorphicOneFormBasis X, ?_, ?_⟩
  · exact SurfaceClassificationData.ofGenusZero p₀ h_genus h_bslb
  · -- RFBR at g=0 (polymorphic in cycleGens).
    exact riemannFirstBilinearRelation_of_genus_zero h_genus _ _
  · -- RSRP at g=0 (polymorphic in cycleGens).
    exact riemannSecondRelationPositivity_of_genus_zero h_genus _ _ _

end JacobianChallenge

end
