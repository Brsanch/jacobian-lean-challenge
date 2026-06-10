/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorus
import JacobianChallenge.Manifold.ComplexTorusBasicInstances
import JacobianChallenge.Divisor.PrincipalDivisor

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Descending `L`-periodic meromorphic functions to the complex torus

For a discrete full-rank ℤ-lattice `L ≤ ℂ`, an `L`-periodic meromorphic
function `F : ℂ → ℂ` (with non-vanishing germs and continuity at regular
points) **descends** to a `MeromorphicNonzero (ℂ ⧸ L)`, with the
chart-pullback meromorphic order at `L.mkQ z` equal to
`meromorphicOrderAt F z`.

This is the converse-direction companion of
`LiftedMeromorphicComplexTorus.lean` (which lifts a torus function to a
periodic function on `ℂ`). The descent direction is what the classical
Weierstrass-℘ constructions need: `℘`, `℘'` and their affine combinations
are `L`-periodic meromorphic functions on `ℂ`, and this file is the bridge
that turns each of them into a `MeromorphicNonzero (ℂ ⧸ L)` whose principal
divisor is computable from the orders of the function on `ℂ`.

## Why the chart bookkeeping is light

The torus charts are `chartAt ℂ q = (localChart L _ q.out).symm`, where
`localChart` is built from `Set.InjOn.toPartialEquiv L.mkQ (ball q.out (r/2))`.
Since `InjOn.toPartialEquiv` installs the *total* function `L.mkQ` as its
`toFun`, the bare-function coercion `((chartAt ℂ q).symm : ℂ → ℂ ⧸ L)`
is `L.mkQ` *everywhere* — so the chart pullback of the descended function
is literally `F` (by `L`-periodicity), as a `funext` equality, not merely
a germ statement.

The only genuinely analytic input is translation-invariance of
`meromorphicOrderAt` for periodic functions, supplied by mathlib's
`meromorphicOrderAt_comp_of_deriv_ne_zero` at `g := (· + l)`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Set

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## `L`-periodicity and the descended function -/

/-- `F : ℂ → ℂ` is **`L`-periodic**: `F (z + l) = F z` for every `l ∈ L`. -/
def LPeriodic (F : ℂ → ℂ) : Prop :=
  ∀ l ∈ L, ∀ z : ℂ, F (z + l) = F z

/-- The **descended function** of `F : ℂ → ℂ` on the torus, via the
out-representative. For `L`-periodic `F` this is the unique function with
`descendFun L F ∘ L.mkQ = F` (see `descendFun_mkQ`). -/
def descendFun (F : ℂ → ℂ) : ℂ ⧸ L → ℂ :=
  fun q => F q.out

/-- `L.mkQ q.out = q`. -/
lemma mkQ_out (q : ℂ ⧸ L) : L.mkQ q.out = q := by
  have hq : (Quotient.mk'' (Quotient.out q) : ℂ ⧸ L) = q := Quotient.out_eq q
  have h1 : (Submodule.Quotient.mk (Quotient.out q) : ℂ ⧸ L) = q := hq
  rw [Submodule.mkQ_apply]
  exact h1

/-- The out-representative of `L.mkQ z` differs from `z` by a lattice
element. -/
lemma out_mkQ_sub_mem (z : ℂ) : (L.mkQ z).out - z ∈ L := by
  have h : L.mkQ ((L.mkQ z).out) = L.mkQ z := mkQ_out L (L.mkQ z)
  have h' : (Submodule.Quotient.mk ((L.mkQ z).out) : ℂ ⧸ L)
      = Submodule.Quotient.mk z := by
    simp only [← Submodule.mkQ_apply]
    exact h
  exact (Submodule.Quotient.eq L).mp h'

/-- **Descent identity**: for `L`-periodic `F`,
`descendFun L F (L.mkQ z) = F z`. -/
lemma descendFun_mkQ {F : ℂ → ℂ} (hF : LPeriodic L F) (z : ℂ) :
    descendFun L F (L.mkQ z) = F z := by
  have hδ : (L.mkQ z).out - z ∈ L := out_mkQ_sub_mem L z
  have h2 : z + ((L.mkQ z).out - z) = (L.mkQ z).out := by ring
  have h3 : F (z + ((L.mkQ z).out - z)) = F z := hF _ hδ z
  rw [h2] at h3
  exact h3

/-! ## Chart bookkeeping -/

/-- The bare-function coercion of the inverse chart at any `q : ℂ ⧸ L` is the
quotient projection `L.mkQ` (globally — `InjOn.toPartialEquiv` installs the
total function as `toFun`). -/
lemma chartAt_symm_coe_apply (q : ℂ ⧸ L) (y : ℂ) :
    ((chartAt ℂ q).symm : ℂ → ℂ ⧸ L) y = L.mkQ y := rfl

/-- The base point `q.out` lies in the source of the underlying local chart. -/
lemma out_mem_localChart_source (q : ℂ ⧸ L) :
    q.out ∈ (localChart L (discRadius_separates L) q.out).source := by
  have hr2 : (0 : ℝ) < discRadius L / 2 := by
    have := discRadius_pos L; linarith
  change q.out ∈ Metric.ball q.out (discRadius L / 2)
  simp [Metric.mem_ball, dist_self, hr2]

/-- **The chart at `q` sends `q` to `q.out`.** -/
lemma chartAt_apply_self (q : ℂ ⧸ L) : (chartAt ℂ q) q = q.out := by
  have hsrc : q.out ∈ (localChart L (discRadius_separates L) q.out).source :=
    out_mem_localChart_source L q
  have hleft :
      (localChart L (discRadius_separates L) q.out).symm
        ((localChart L (discRadius_separates L) q.out) q.out) = q.out :=
    (localChart L (discRadius_separates L) q.out).left_inv hsrc
  have happ : (localChart L (discRadius_separates L) q.out) q.out = q := by
    show L.mkQ q.out = q
    exact mkQ_out L q
  calc (chartAt ℂ q) q
      = (localChart L (discRadius_separates L) q.out).symm q := rfl
    _ = (localChart L (discRadius_separates L) q.out).symm
          ((localChart L (discRadius_separates L) q.out) q.out) := by rw [happ]
    _ = q.out := hleft

/-- **The chart pullback of the descended function is `F` itself** (a global
`funext` equality, thanks to `L`-periodicity and the total-`mkQ` chart
inverse). -/
lemma descendFun_comp_chartAt_symm {F : ℂ → ℂ} (hF : LPeriodic L F)
    (q : ℂ ⧸ L) :
    (descendFun L F) ∘ ((chartAt ℂ q).symm : ℂ → ℂ ⧸ L) = F := by
  funext y
  show descendFun L F (((chartAt ℂ q).symm : ℂ → ℂ ⧸ L) y) = F y
  rw [chartAt_symm_coe_apply L q y, descendFun_mkQ L hF y]

/-! ## Translation-invariance of the meromorphic order -/

/-- For `L`-periodic `F`, the meromorphic order is `L`-translation-invariant:
`meromorphicOrderAt F (z + l) = meromorphicOrderAt F z` for `l ∈ L`. -/
lemma meromorphicOrderAt_of_LPeriodic {F : ℂ → ℂ} (hF : LPeriodic L F)
    {l : ℂ} (hl : l ∈ L) (z : ℂ) :
    meromorphicOrderAt F (z + l) = meromorphicOrderAt F z := by
  have hg : AnalyticAt ℂ (fun w : ℂ => w + l) z := by fun_prop
  have h1 : HasDerivAt (fun w : ℂ => w + l) 1 z :=
    (hasDerivAt_id z).add_const l
  have hg' : deriv (fun w : ℂ => w + l) z ≠ 0 := by
    rw [h1.deriv]; exact one_ne_zero
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero (f := F) hg hg'
  have hFc : F ∘ (fun w : ℂ => w + l) = F := by
    funext w; exact hF l hl w
  rw [hFc] at hcomp
  exact hcomp.symm

/-! ## The descended meromorphic order -/

/-- **Order correspondence at the out-representative**: the chart-pullback
meromorphic order of `descendFun L F` at `q` is the meromorphic order of `F`
at `q.out`. -/
lemma mmeromorphicOrderAt_descendFun {F : ℂ → ℂ} (hF : LPeriodic L F)
    (q : ℂ ⧸ L) :
    mmeromorphicOrderAt 𝓘(ℂ, ℂ) (descendFun L F) q
      = meromorphicOrderAt F q.out := by
  show meromorphicOrderAt
      ((descendFun L F) ∘ ((chartAt ℂ q).symm : ℂ → ℂ ⧸ L)) ((chartAt ℂ q) q)
    = meromorphicOrderAt F q.out
  rw [descendFun_comp_chartAt_symm L hF q, chartAt_apply_self L q]

/-- **Order correspondence at an arbitrary lift**: the chart-pullback
meromorphic order of `descendFun L F` at `L.mkQ z` is the meromorphic order
of `F` at `z`. -/
lemma mmeromorphicOrderAt_descendFun_mkQ {F : ℂ → ℂ} (hF : LPeriodic L F)
    (z : ℂ) :
    mmeromorphicOrderAt 𝓘(ℂ, ℂ) (descendFun L F) (L.mkQ z)
      = meromorphicOrderAt F z := by
  rw [mmeromorphicOrderAt_descendFun L hF (L.mkQ z)]
  have hδ : (L.mkQ z).out - z ∈ L := out_mkQ_sub_mem L z
  have h2 : z + ((L.mkQ z).out - z) = (L.mkQ z).out := by ring
  rw [← h2]
  exact meromorphicOrderAt_of_LPeriodic L hF hδ z

/-! ## Meromorphy and continuity of the descended function -/

/-- The descended function is `MMeromorphicAt` at every point of the torus. -/
lemma mMeromorphicAt_descendFun {F : ℂ → ℂ} (hF : LPeriodic L F)
    (hFm : Meromorphic F) (q : ℂ ⧸ L) :
    MMeromorphicAt 𝓘(ℂ, ℂ) (descendFun L F) q := by
  show MeromorphicAt
      ((descendFun L F) ∘ ((chartAt ℂ q).symm : ℂ → ℂ ⧸ L)) ((chartAt ℂ q) q)
  rw [descendFun_comp_chartAt_symm L hF q]
  exact hFm _

/-- On the chart source around `q`, the descended function agrees with
`F ∘ chartAt ℂ q`. -/
lemma descendFun_eq_comp_chartAt_on_source {F : ℂ → ℂ} (hF : LPeriodic L F)
    (q : ℂ ⧸ L) :
    ∀ q' ∈ (chartAt ℂ q).source,
      descendFun L F q' = (F ∘ (chartAt ℂ q)) q' := by
  intro q' hq'
  -- `chartAt ℂ q = (localChart L _ q.out).symm`, so `q' ∈ (localChart _).target`
  -- and the right inverse gives `L.mkQ ((chartAt ℂ q) q') = q'`.
  have hq'_tgt : q' ∈ (localChart L (discRadius_separates L) q.out).target := hq'
  have hright :
      (localChart L (discRadius_separates L) q.out)
        ((localChart L (discRadius_separates L) q.out).symm q') = q' :=
    (localChart L (discRadius_separates L) q.out).right_inv hq'_tgt
  have hmkQ : L.mkQ ((chartAt ℂ q) q') = q' := hright
  calc descendFun L F q'
      = descendFun L F (L.mkQ ((chartAt ℂ q) q')) := by rw [hmkQ]
    _ = F ((chartAt ℂ q) q') := descendFun_mkQ L hF _

/-- **Continuity of the descended function** at any point where `F` is
continuous at the out-representative. -/
lemma continuousAt_descendFun {F : ℂ → ℂ} (hF : LPeriodic L F) (q : ℂ ⧸ L)
    (hc : ContinuousAt F q.out) : ContinuousAt (descendFun L F) q := by
  have hsrc : q ∈ (chartAt ℂ q).source := mem_chart_source ℂ q
  have hopen : IsOpen (chartAt ℂ q).source := (chartAt ℂ q).open_source
  have hchart_cont : ContinuousAt (chartAt ℂ q) q :=
    (chartAt ℂ q).continuousAt hsrc
  have hcomp : ContinuousAt (F ∘ (chartAt ℂ q)) q := by
    apply ContinuousAt.comp ?_ hchart_cont
    rw [chartAt_apply_self L q]
    exact hc
  have hEq : (descendFun L F) =ᶠ[nhds q] (F ∘ (chartAt ℂ q)) :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hsrc)
      (descendFun_eq_comp_chartAt_on_source L hF q)
  exact hcomp.congr hEq.symm

/-! ## The descent constructor -/

/-- **Descend an `L`-periodic meromorphic function to the torus.** Given
`F : ℂ → ℂ` that is `L`-periodic, meromorphic, with no identically-zero germ
(`meromorphicOrderAt F z ≠ ⊤` everywhere) and continuous at regular points,
the descended function is a `MeromorphicNonzero (ℂ ⧸ L)`. -/
def descend (F : ℂ → ℂ) (hF : LPeriodic L F) (hFm : Meromorphic F)
    (h_top : ∀ z : ℂ, meromorphicOrderAt F z ≠ ⊤)
    (h_cont : ∀ z : ℂ, 0 ≤ meromorphicOrderAt F z → ContinuousAt F z) :
    MeromorphicNonzero (ℂ ⧸ L) where
  toFun := descendFun L F
  meromorphic := fun q _ => mMeromorphicAt_descendFun L hF hFm q
  nonvanishing_germ := fun q => by
    rw [mmeromorphicOrderAt_descendFun L hF q]
    exact h_top q.out
  regular_continuousAt := fun q hq => by
    rw [mmeromorphicOrderAt_descendFun L hF q] at hq
    exact continuousAt_descendFun L hF q (h_cont q.out hq)

@[simp] lemma descend_toFun (F : ℂ → ℂ) (hF : LPeriodic L F)
    (hFm : Meromorphic F)
    (h_top : ∀ z : ℂ, meromorphicOrderAt F z ≠ ⊤)
    (h_cont : ∀ z : ℂ, 0 ≤ meromorphicOrderAt F z → ContinuousAt F z) :
    (descend L F hF hFm h_top h_cont).toFun = descendFun L F := rfl

/-! ## The principal divisor of a descended function -/

/-- **Divisor correspondence**: the principal divisor of the descended
function, evaluated at `L.mkQ z`, is the (untopped) meromorphic order of `F`
at `z`. -/
lemma principalDivisorMap_descend_apply_mkQ (F : ℂ → ℂ) (hF : LPeriodic L F)
    (hFm : Meromorphic F)
    (h_top : ∀ z : ℂ, meromorphicOrderAt F z ≠ ⊤)
    (h_cont : ∀ z : ℂ, 0 ≤ meromorphicOrderAt F z → ContinuousAt F z)
    (z : ℂ) :
    (principalDivisorMap (descend L F hF hFm h_top h_cont) : (ℂ ⧸ L) → ℤ)
        (L.mkQ z)
      = (meromorphicOrderAt F z).untop₀ := by
  rw [principalDivisorMap_apply]
  show (mmeromorphicOrderAt 𝓘(ℂ, ℂ) (descendFun L F) (L.mkQ z)).untop₀ = _
  rw [mmeromorphicOrderAt_descendFun_mkQ L hF z]

/-- **Divisor correspondence at the out-representative**: the principal
divisor of the descended function, evaluated at any `q`, is the (untopped)
meromorphic order of `F` at `q.out`. -/
lemma principalDivisorMap_descend_apply (F : ℂ → ℂ) (hF : LPeriodic L F)
    (hFm : Meromorphic F)
    (h_top : ∀ z : ℂ, meromorphicOrderAt F z ≠ ⊤)
    (h_cont : ∀ z : ℂ, 0 ≤ meromorphicOrderAt F z → ContinuousAt F z)
    (q : ℂ ⧸ L) :
    (principalDivisorMap (descend L F hF hFm h_top h_cont) : (ℂ ⧸ L) → ℤ) q
      = (meromorphicOrderAt F q.out).untop₀ := by
  rw [principalDivisorMap_apply]
  show (mmeromorphicOrderAt 𝓘(ℂ, ℂ) (descendFun L F) q).untop₀ = _
  rw [mmeromorphicOrderAt_descendFun L hF q]

end ComplexTorus

end JacobianChallenge

end
