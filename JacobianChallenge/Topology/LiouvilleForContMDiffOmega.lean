/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.HolomorphicLocallyConstantDischarge
import JacobianChallenge.Topology.MeromorphicNonzeroBuilder
import JacobianChallenge.Manifold.ContMDiffOmegaAnalytic
import JacobianChallenge.Manifold.IsConstantMapAux
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order

/-! # Liouville constancy for `ContMDiff … ω` functions on compact connected `X`

This file ships a Liouville-style constancy theorem for functions
`F : X → ℂ` of regularity `ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω` on a compact
connected complex 1-manifold `X`, working through the existing
`MeromorphicNonzero` + `liouvilleOnCompactConnected_holds` chain.

The bridge has three steps:

1. **Holomorphicity ⇒ meromorphicity on `Set.univ`.** Using
   `Manifold/ContMDiffOmegaAnalytic.lean`'s
   `contMDiff_omega_analyticAt_chart_pullback`, the chart pullback of `F`
   is `AnalyticAt ℂ` at every chart-image point. Mathlib's
   `AnalyticAt.meromorphicAt` then upgrades each chart pullback to
   `MeromorphicAt`, giving `MMeromorphicOn 𝓘(ℂ, ℂ) F Set.univ`.

2. **Holomorphicity ⇒ order ≥ 0 everywhere.** Mathlib's
   `AnalyticAt.meromorphicOrderAt_nonneg` says the meromorphic order of
   an analytic chart pullback is non-negative; unwrapping the
   `mmeromorphicOrderAt` definition gives `0 ≤ mmeromorphicOrderAt _ F x`
   for every `x : X`.

3. **`MeromorphicNonzero` wrap + Liouville.** From the meromorphicity
   plus a `nonvanishing_germ` hypothesis (taken as an input here — the
   manifold-level analytic-continuation argument that would discharge it
   from `¬ IsConstantMap F` is owed in
   `Manifold/AnalyticContinuationGlobalization.lean` and is not at the
   mathlib pin), assemble a `MeromorphicNonzero X` and feed it to
   `liouvilleOnCompactConnected_holds` (already unconditional in
   `Topology/HolomorphicLocallyConstantDischarge.lean`).

## What the named hypothesis means

`(∀ x : X, mmeromorphicOrderAt 𝓘(ℂ, ℂ) F x ≠ ⊤)` says that at no point
is the chart pullback of `F` identically zero on a punctured chart
neighborhood — equivalently, `F` is not "germ-zero" anywhere. For a
holomorphic function on a *connected* manifold, this is automatic
whenever `F` is not the zero function, by analytic continuation. But
that analytic-continuation argument walks paths through chart overlaps,
and the chart-overlap analyticity bridge across the boundary of one
chart into another is documented as owed in the repo
(`Manifold/AnalyticContinuationGlobalization.lean`'s within-one-chart
limitation, line 60–79). So we take it as a hypothesis here.

## What this file proves (no `sorry`, no `axiom`)

* `mmeromorphicOn_univ_of_contMDiff_omega` — `MMeromorphicOn` from
  `ContMDiff … ω`.

* `mmeromorphicOrderAt_nonneg_of_contMDiff_omega` — `0 ≤ mmeromorphicOrderAt _ F x`
  pointwise from analyticity.

* `MeromorphicNonzero.ofContMDiffOmega` — the builder that consumes
  the `nonvanishing_germ` hypothesis.

* `contMDiff_omega_isConstant_of_nonvanishGerm` — the headline
  Liouville-style constancy.
-/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Step 1: `ContMDiff … ω` ⇒ `MMeromorphicOn _ univ` -/

/-- A function `F : X → ℂ` of regularity `ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω` is
meromorphic on the entire manifold, in the chart-pulled-back sense
(`MMeromorphicOn 𝓘(ℂ, ℂ) F Set.univ`).

Proof: `contMDiff_omega_analyticAt_chart_pullback` gives `AnalyticAt ℂ`
of the chart pullback at every chart-image point. `AnalyticAt.meromorphicAt`
upgrades to `MeromorphicAt`, which is the definition of `MMeromorphicAt`. -/
theorem mmeromorphicOn_univ_of_contMDiff_omega
    {F : X → ℂ}
    (hF : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F) :
    MMeromorphicOn (𝓘(ℂ, ℂ)) F Set.univ := by
  intro x _
  -- chart pullback: `F ∘ (chartAt ℂ x).symm`. For F : X → ℂ the target chart
  -- is the identity on ℂ, so the bridge collapses to this.
  -- `contMDiff_omega_analyticAt_chart_pullback hF x` gives
  -- `AnalyticAt ℂ ((chartAt ℂ (F x)) ∘ F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)`.
  -- For ℂ with the trivial chart structure, `chartAt ℂ (F x) = PartialHomeomorph.refl ℂ`,
  -- so this is `AnalyticAt ℂ (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)`.
  have h_analytic :
      AnalyticAt ℂ ((chartAt ℂ (F x)) ∘ F ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) :=
    JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback hF x
  -- The chart on ℂ is the identity (PartialHomeomorph.refl ℂ), so the composition
  -- simplifies. `chartAt ℂ y = PartialHomeomorph.refl ℂ` for any `y : ℂ`.
  have h_chart_eq :
      (chartAt ℂ (F x)) ∘ F ∘ (chartAt ℂ x).symm = F ∘ (chartAt ℂ x).symm := by
    funext z
    -- chartAt ℂ (F x) on ℂ is PartialHomeomorph.refl ℂ which has identity coe.
    rfl
  rw [h_chart_eq] at h_analytic
  -- Now `AnalyticAt ℂ (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)` ⇒ MeromorphicAt.
  -- `MMeromorphicAt 𝓘(ℂ, ℂ) F x` unfolds to `MeromorphicAt (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)`.
  exact h_analytic.meromorphicAt

/-! ## Step 2: `ContMDiff … ω` ⇒ order ≥ 0 -/

/-- A function `F : X → ℂ` of regularity `ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω` has
non-negative `mmeromorphicOrderAt` at every point. -/
theorem mmeromorphicOrderAt_nonneg_of_contMDiff_omega
    {F : X → ℂ}
    (hF : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F) (x : X) :
    0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) F x := by
  -- Same chart-pullback bridge as in step 1.
  have h_analytic :
      AnalyticAt ℂ ((chartAt ℂ (F x)) ∘ F ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) :=
    JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback hF x
  have h_chart_eq :
      (chartAt ℂ (F x)) ∘ F ∘ (chartAt ℂ x).symm = F ∘ (chartAt ℂ x).symm := by
    funext z; rfl
  rw [h_chart_eq] at h_analytic
  -- `mmeromorphicOrderAt 𝓘(ℂ,ℂ) F x = meromorphicOrderAt (F ∘ chart.symm) (chart x)`.
  show 0 ≤ meromorphicOrderAt (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  exact h_analytic.meromorphicOrderAt_nonneg

/-! ## Step 3: `MeromorphicNonzero` builder + Liouville -/

/-- **Builder: `MeromorphicNonzero X` from `ContMDiff … ω` and
`nonvanishing_germ`.** The `nonvanishing_germ` hypothesis is taken as
input — it is the analytic-continuation content owed in
`Manifold/AnalyticContinuationGlobalization.lean`. -/
def MeromorphicNonzero.ofContMDiffOmega
    (F : X → ℂ)
    (h_smooth : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F)
    (h_nonvanish : ∀ x : X, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) F x ≠ ⊤) :
    MeromorphicNonzero X :=
  JacobianChallenge.MeromorphicNonzero.ofContinuousMeromorphic
    F
    (mmeromorphicOn_univ_of_contMDiff_omega h_smooth)
    h_nonvanish
    h_smooth.continuous

@[simp]
lemma MeromorphicNonzero.ofContMDiffOmega_toFun
    (F : X → ℂ)
    (h_smooth : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F)
    (h_nonvanish : ∀ x : X, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) F x ≠ ⊤) :
    (MeromorphicNonzero.ofContMDiffOmega F h_smooth h_nonvanish).toFun = F := rfl

/-- **Liouville for `ContMDiff … ω` functions.** A holomorphic
`F : X → ℂ` on a compact connected complex 1-manifold with no germ-zero
point is constant.

The "no germ-zero" hypothesis is automatic for an `F` that is not
identically zero on a connected `X` (by manifold-level analytic
continuation), but the analytic-continuation argument is owed in
`Manifold/AnalyticContinuationGlobalization.lean` and is therefore
taken as an explicit hypothesis here. -/
theorem contMDiff_omega_isConstant_of_nonvanishGerm
    (F : X → ℂ)
    (h_smooth : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω F)
    (h_nonvanish : ∀ x : X, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) F x ≠ ⊤) :
    IsConstantMap F := by
  -- Wrap F as MeromorphicNonzero.
  let f : MeromorphicNonzero X :=
    MeromorphicNonzero.ofContMDiffOmega F h_smooth h_nonvanish
  -- f.toFun = F, with order ≥ 0 everywhere.
  have h_order : ∀ x, 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x := by
    intro x
    show 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) F x
    exact mmeromorphicOrderAt_nonneg_of_contMDiff_omega h_smooth x
  -- Apply the unconditional Liouville for MeromorphicNonzero.
  have h_const : JacobianChallenge.IsConstantMap f.toFun :=
    liouvilleOnCompactConnected_holds X f h_order
  -- f.toFun = F, so IsConstantMap F.
  exact h_const

end JacobianChallenge

end
