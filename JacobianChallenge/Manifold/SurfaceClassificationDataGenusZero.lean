/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SurfaceClassificationData
import JacobianChallenge.Manifold.BasedSmoothLoopsBound

set_option linter.unusedSectionVars false

/-! # `SurfaceClassificationData X` from genus 0 + BasedSmoothLoopsBound

Generalizes chip 1's RS-specific `surfaceClassificationData_RiemannSphere`
to any compact connected complex 1-manifold `X` with:

* `genus X = 0` (equivalently, `Subsingleton (HolomorphicOneForm X)`
  + the in-tree `FiniteDimensional` discharge from `DiskChartCover`).
* `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X p₀` for some base point.

At genus 0:
* `Fin (2 * genus X) = Fin 0` is empty, so the symplectic basis is
  trivially data of `Fin.elim0`.
* `SmoothHurewiczHypothesis` on the empty basis reduces to
  `∀ γ, single γ ∈ stokesBoundaries` — i.e., BSLB.

So HSCD at g=0 is discharged from a single named topological hypothesis
(BSLB), which is unconditional on RS via the in-tree chain.

This factors the SCD topological side at genus 0 into a single named
classical atom (BSLB).

## What this file ships

* `SurfaceClassificationData.ofGenusZero` — HSCD from
  `genus X = 0 + BasedSmoothLoopsBoundHypothesis I X p₀`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`SurfaceClassificationData X` from `genus X = 0` + `BSLB`.**

At genus 0 the symplectic basis is empty (`Fin 0`), so the entire SCD
content reduces to a single named topological hypothesis: every smooth
based loop at `p₀` lies in `stokesBoundaries`.

This generalizes chip 1's RS-specific instance (which used the in-tree
unconditional `basedSmoothLoopsBoundHypothesis_RS_holds`). For any
X with `genus X = 0` and a BSLB witness, HSCD is discharged. -/
noncomputable def SurfaceClassificationData.ofGenusZero
    (p₀ : X) (h_genus : JacobianChallenge.genus X = 0)
    (h_bslb : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X p₀) :
    SurfaceClassificationData X :=
  let hEmpty : IsEmpty (Fin (2 * JacobianChallenge.genus X)) := by
    rw [h_genus, Nat.mul_zero]; infer_instance
  let sb : SmoothSymplecticBasis 𝓘(ℝ, ℂ) X p₀ (JacobianChallenge.genus X) :=
    { basis := (fun (i : Fin (2 * JacobianChallenge.genus X)) => (hEmpty.false i).elim)
      basis_src := fun i => hEmpty.elim i
      basis_tgt := fun i => hEmpty.elim i }
  { basePoint := p₀
    symplecticBasis := sb
    hurewicz := by
      intro γ h_src h_tgt
      refine ⟨(fun (i : Fin (2 * JacobianChallenge.genus X)) => (hEmpty.false i).elim), ?_⟩
      have h_sum_zero :
          (∑ i : Fin (2 * JacobianChallenge.genus X),
            ((fun (i : Fin (2 * JacobianChallenge.genus X)) => (hEmpty.false i).elim) i : ℤ) • sb.cycleGens i)
            = (0 : SmoothCycle 𝓘(ℝ, ℂ) X) :=
        Finset.sum_of_isEmpty _
      rw [h_sum_zero, sub_zero]
      exact h_bslb γ h_src h_tgt }

end JacobianChallenge

end
