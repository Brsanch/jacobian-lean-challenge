/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import JacobianChallenge.Divisor.PrincipalDivisor
import JacobianChallenge.Manifold.FibresFiniteUnconditional
import JacobianChallenge.Manifold.MeromorphicAt
import JacobianChallenge.Manifold.NormPushforwardManifold
import JacobianChallenge.Manifold.RamificationIndex

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Global manifold-level norm pushforward (Phase 1 chip P1.2a, ZZ206)

For a non-constant `ContMDiff ω` map `f : X → Y` between compact connected
complex 1-manifolds and a `MeromorphicNonzero X` representative `g`, this
file ships the **global** norm pushforward `NormFM f hf hf_nc g : Y → ℂ`
defined as the finite product over the (finite!) fibre `f ⁻¹ {y}` of
`g.toFun` raised to the manifold ramification index, plus a generic
finite-product closure lemma for `MMeromorphicAt`, and a *conditional*
`MMeromorphicOn` headline assembling pointwise meromorphy at every
`y₀ : Y`.

## What is shipped

* `mmeromorphicAt_finset_prod` — generic finite-product closure for
  `MMeromorphicAt I`. Works on any charted space `M`, not chip-specific.

* `NormFM` — the global definition. Uses the unconditional fibre
  finiteness from `fibres_finite_statement_holds_unconditional`
  (`Manifold/FibresFiniteUnconditional.lean`), so the `Finset X` index
  set is genuinely available, not stubbed.

* `NormFM_apply` — unfold lemma giving the explicit Finset-product form.

* `NormFM_mmeromorphicOn_univ_of_pointwise` — the **conditional** global
  headline: given pointwise `MMeromorphicAt` for the moving-fibre product
  at every `y₀ : Y`, the `MMeromorphicOn univ` conclusion follows. This
  is the form the residual chip (P1.2b) will discharge unconditionally.

## Residual

The unconditional discharge of the per-point `MMeromorphicAt` hypothesis
is split off as follow-up chip P1.2b. It will combine
* `analytic_local_normal_form` to put `f` in Hurwitz form
  `t = w₀ + ψ_x^{k_x}` near each preimage `x ∈ f ⁻¹ {y₀}`;
* `manifoldRamificationIndex_eq_localKFoldMultiplicityChartPullback` to
  identify `k_x` with `manifoldRamificationIndex f x`;
* the chart-pullback wrapper `normPow_mmeromorphicAt_chartPullback_zero`
  (ZZ205) to push each local contribution to `MMeromorphicAt y₀`;
* fibre stability of `(f ⁻¹ {y}).toFinset` on a chart neighbourhood of
  `y₀` (covered by `localKFoldMultiplicityOnManifold_genuine_with_radius`
  in `NearbyRegularWitnessUnconditional.lean`); and
* the chart-translation gluing identifying the abstract per-fibre product
  with the chart-local `normPow` factor.

## Anti-cheat

* No `axiom`, no `sorry`.
* No `ω` binder anywhere (Lean 4.30 reserved).
* No signature change to any pre-existing definition or theorem.
* Only one new file plus an alphabetical insertion in the
  `JacobianChallenge.lean` import manifest.
-/

@[expose] public section

noncomputable section

open scoped Manifold Topology
open Filter Set

namespace JacobianChallenge
namespace Manifold

universe u v

/-! ### Generic finite-product closure for `MMeromorphicAt` -/

/-- **Finite-product closure.** A pointwise-meromorphic family of functions,
indexed by a `Finset`, has a meromorphic finite product. Pure consequence
of `MMeromorphicAt.mul` and `MMeromorphicAt.const 1`. -/
theorem mmeromorphicAt_finset_prod
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {I : ModelWithCorners ℂ ℂ ℂ} {x : M}
    {ι : Type*} (s : Finset ι) (F : ι → M → ℂ)
    (hF : ∀ i ∈ s, MMeromorphicAt I (F i) x) :
    MMeromorphicAt I (fun y : M => ∏ i ∈ s, F i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h_eq : (fun y : M => ∏ i ∈ (∅ : Finset ι), F i y)
          = (fun _ : M => (1 : ℂ)) := by
        funext y; simp
      rw [h_eq]
      exact MMeromorphicAt.const 1
  | insert _ a t ha_notin ih =>
      have h_eq :
          (fun y : M => ∏ i ∈ insert a t, F i y)
            = (F a) * (fun y : M => ∏ i ∈ t, F i y) := by
        funext y
        simp [Finset.prod_insert ha_notin]
      rw [h_eq]
      have h_a : MMeromorphicAt I (F a) x :=
        hF a (Finset.mem_insert_self a t)
      have h_tail : MMeromorphicAt I (fun y : M => ∏ i ∈ t, F i y) x :=
        ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
      exact h_a.mul h_tail

/-! ### The global norm pushforward `NormFM` -/

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable {Y : Type v}
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-- **Global norm pushforward.** For a non-constant `ContMDiff ω` map
`f : X → Y` between compact connected complex 1-manifolds and a
`MeromorphicNonzero X` representative `g`, define
`NormFM f hf hf_nc g : Y → ℂ` by
```
y ↦ ∏ x ∈ (f ⁻¹ {y}).toFinset, g x ^ manifoldRamificationIndex f x
```
where `(f ⁻¹ {y}).toFinset` is the canonical `Finset` extracted from
the unconditional fibre-finiteness witness
`fibres_finite_statement_holds_unconditional`. -/
noncomputable def NormFM
    (f : X → Y) (hf : ContMDiff (𝓘(ℂ)) (𝓘(ℂ)) ω f)
    (hf_nc : ¬ JacobianChallenge.IsConstantMap f)
    (g : MeromorphicNonzero X) : Y → ℂ :=
  fun y =>
    (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional
      f hf hf_nc y).toFinset.prod
      (fun x => g.toFun x ^ manifoldRamificationIndex f x)

/-- Unfold lemma: `NormFM f hf hf_nc g y` equals the explicit Finset
product over the fibre at `y`. -/
lemma NormFM_apply
    (f : X → Y) (hf : ContMDiff (𝓘(ℂ)) (𝓘(ℂ)) ω f)
    (hf_nc : ¬ JacobianChallenge.IsConstantMap f)
    (g : MeromorphicNonzero X) (y : Y) :
    NormFM f hf hf_nc g y =
      (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional
        f hf hf_nc y).toFinset.prod
        (fun x => g.toFun x ^ manifoldRamificationIndex f x) := rfl

/-! ### Conditional global meromorphy of `NormFM`

The conditional theorem ships the global `MMeromorphicOn univ` conclusion
once a per-point `MMeromorphicAt` witness is supplied. The pointwise
hypothesis is precisely the moving-fibre form of `NormFM`, the natural
shape that the residual chip P1.2b will discharge via the chart-pullback
wrapper `normPow_mmeromorphicAt_chartPullback_zero` plus the Hurwitz
local form. -/

/-- **Conditional global meromorphy of `NormFM`.**

Given a per-point meromorphy hypothesis on the moving-fibre product
itself, the global `MMeromorphicOn univ` conclusion is the trivial
unfolding of the `MMeromorphicOn` predicate. -/
theorem NormFM_mmeromorphicOn_univ_of_pointwise
    (f : X → Y) (hf : ContMDiff (𝓘(ℂ)) (𝓘(ℂ)) ω f)
    (hf_nc : ¬ JacobianChallenge.IsConstantMap f)
    (g : MeromorphicNonzero X)
    (h_pw : ∀ y₀ : Y, MMeromorphicAt (𝓘(ℂ, ℂ)) (NormFM f hf hf_nc g) y₀) :
    MMeromorphicOn (𝓘(ℂ, ℂ)) (NormFM f hf hf_nc g) Set.univ :=
  fun y₀ _ => h_pw y₀

end Manifold
end JacobianChallenge

end
