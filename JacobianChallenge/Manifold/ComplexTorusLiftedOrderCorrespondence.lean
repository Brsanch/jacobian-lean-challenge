/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusDescendPeriodic
import JacobianChallenge.Manifold.LiftedMeromorphicComplexTorus

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # `LiftedOrderCorrespondence` is unconditional

Discharges the named hypothesis `LiftedOrderCorrespondence L f` (and its
total form `LiftedOrderCorrespondenceTotal L`) deferred in
`LiftedMeromorphicComplexTorus.lean`: for every
`f : MeromorphicNonzero (ℂ ⧸ L)`, the lift `liftedFun L f = f ∘ L.mkQ`
has, at every `z : ℂ`, the same meromorphic order as `f` has at
`L.mkQ z`. We also supply the companion fact named as follow-up (i)
there: the lift is meromorphic on all of `ℂ`.

The proof is the lift-direction shadow of the descent machinery in
`ComplexTorusDescendPeriodic.lean`: the bare-function coercion of the
inverse torus chart at `q` is the *total* quotient map `L.mkQ`
(`chartAt_symm_coe_apply`), so the chart-pullback representative of `f`
at `q` is **literally** `liftedFun L f` as a function, evaluated at the
chart image `q.out`. The discrepancy between an arbitrary lift `z` and
the out-representative `(L.mkQ z).out` is a lattice translation, handled
by `meromorphicOrderAt_of_LPeriodic` (for orders) and
`meromorphicAt_comp_iff_of_deriv_ne_zero` at `(· + δ)` (for meromorphy).

This closes the entry-gate of the `TLDivSumHypothesis` contour arc:
steps (i) "meromorphy of the lift on ℂ" and (ii) "divisor agreement"
from the follow-up list in `LiftedMeromorphicComplexTorus.lean`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Set

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The lift of `f` is the chart-pullback representative of `f` at every
base point `q` (a global `funext` identity, since the inverse chart is
the total `mkQ`). -/
lemma liftedFun_eq_comp_chartAt_symm (f : MeromorphicNonzero (ℂ ⧸ L))
    (q : ℂ ⧸ L) :
    liftedFun L f = f.toFun ∘ ((chartAt ℂ q).symm : ℂ → ℂ ⧸ L) := by
  funext z
  show f.toFun (L.mkQ z) = f.toFun (((chartAt ℂ q).symm : ℂ → ℂ ⧸ L) z)
  rw [chartAt_symm_coe_apply L q z]

/-- The lift is `L`-periodic in the `LPeriodic` packaging. -/
lemma lperiodic_liftedFun (f : MeromorphicNonzero (ℂ ⧸ L)) :
    LPeriodic L (liftedFun L f) :=
  fun _l hl z => liftedFun_periodic L f hl z

/-- **Order correspondence at out-representatives**: the meromorphic order
of the lift at `q.out` is the chart-pullback order of `f` at `q`. -/
lemma meromorphicOrderAt_liftedFun_out (f : MeromorphicNonzero (ℂ ⧸ L))
    (q : ℂ ⧸ L) :
    meromorphicOrderAt (liftedFun L f) q.out
      = mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun q := by
  show meromorphicOrderAt (liftedFun L f) q.out
      = meromorphicOrderAt (f.toFun ∘ ((chartAt ℂ q).symm : ℂ → ℂ ⧸ L))
          ((chartAt ℂ q) q)
  rw [chartAt_apply_self L q, ← liftedFun_eq_comp_chartAt_symm L f q]

/-- **The named hypothesis `LiftedOrderCorrespondence L f` holds
unconditionally.** -/
theorem liftedOrderCorrespondence_holds (f : MeromorphicNonzero (ℂ ⧸ L)) :
    LiftedOrderCorrespondence L f := by
  intro z
  have hδ : (L.mkQ z).out - z ∈ L := out_mkQ_sub_mem L z
  have htrans := meromorphicOrderAt_of_LPeriodic L
    (lperiodic_liftedFun L f) hδ z
  have hcollect : z + ((L.mkQ z).out - z) = (L.mkQ z).out := by ring
  rw [hcollect] at htrans
  rw [← htrans]
  exact meromorphicOrderAt_liftedFun_out L f (L.mkQ z)

/-- **The total form `LiftedOrderCorrespondenceTotal L` holds
unconditionally.** -/
theorem liftedOrderCorrespondenceTotal_holds :
    LiftedOrderCorrespondenceTotal L :=
  fun f => liftedOrderCorrespondence_holds L f

/-- **Follow-up (i) of `LiftedMeromorphicComplexTorus.lean`**: the lift of
`f` is meromorphic on all of `ℂ`. -/
theorem meromorphic_liftedFun (f : MeromorphicNonzero (ℂ ⧸ L)) :
    Meromorphic (liftedFun L f) := by
  intro z
  -- Meromorphy at the out-representative, from `f`'s chart-pullback
  -- meromorphy.
  have h1 : MeromorphicAt (liftedFun L f) ((L.mkQ z).out) := by
    have hf := f.meromorphic (L.mkQ z) (Set.mem_univ _)
    have hfun := liftedFun_eq_comp_chartAt_symm L f (L.mkQ z)
    have hpt : (chartAt ℂ (L.mkQ z)) (L.mkQ z) = (L.mkQ z).out :=
      chartAt_apply_self L (L.mkQ z)
    show MeromorphicAt (liftedFun L f) ((L.mkQ z).out)
    rw [hfun]
    rw [← hpt]
    exact hf
  -- Translate from the out-representative to `z` via `(· + δ)`.
  have hδ : (L.mkQ z).out - z ∈ L := out_mkQ_sub_mem L z
  set δ : ℂ := (L.mkQ z).out - z with hδ_def
  have hg : AnalyticAt ℂ (fun w : ℂ => w + δ) z := by fun_prop
  have hg1 : HasDerivAt (fun w : ℂ => w + δ) 1 z :=
    (hasDerivAt_id z).add_const δ
  have hg' : deriv (fun w : ℂ => w + δ) z ≠ 0 := by
    rw [hg1.deriv]; exact one_ne_zero
  have hcollect : z + δ = (L.mkQ z).out := by rw [hδ_def]; ring
  have h2 : MeromorphicAt (liftedFun L f) (z + δ) := by
    rw [hcollect]; exact h1
  have h3 : MeromorphicAt ((liftedFun L f) ∘ (fun w : ℂ => w + δ)) z :=
    (meromorphicAt_comp_iff_of_deriv_ne_zero hg hg').mpr h2
  have hFc : (liftedFun L f) ∘ (fun w : ℂ => w + δ) = liftedFun L f := by
    funext w
    exact lperiodic_liftedFun L f δ hδ w
  rwa [hFc] at h3

/-- **Divisor agreement** (follow-up (ii)): the principal divisor of `f`
at `L.mkQ z` is the untopped order of the lift at `z`. -/
lemma principalDivisorMap_apply_mkQ_eq_liftedFun_order
    (f : MeromorphicNonzero (ℂ ⧸ L)) (z : ℂ) :
    (principalDivisorMap f : (ℂ ⧸ L) → ℤ) (L.mkQ z)
      = (meromorphicOrderAt (liftedFun L f) z).untop₀ := by
  rw [principalDivisorMap_apply]
  show (mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun (L.mkQ z)).untop₀ = _
  rw [← liftedOrderCorrespondence_holds L f z]

end ComplexTorus

end JacobianChallenge

end
