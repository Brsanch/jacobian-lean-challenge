/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroRegularPath
import JacobianChallenge.Manifold.MeromorphicNonzeroLevelSetPrincipalDivisorIdentification

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Concrete level-set chain using the regular β: 0 → ∞

This file wires the β-existence chip (`MeromorphicNonzeroRegularPath.lean`)
into the level-set chain construction
(`MeromorphicNonzeroLevelSetChain.lean`).

For `f : MeromorphicNonzero X` non-constant with `0` and `∞` both regular
values, we:

* Extract `regularBeta f hnc h0_reg h_inf_reg : ℝ → RiemannSphere` from
  `exists_regular_path_zero_to_infty` via `Classical.choose`.
* Re-export its four properties: smooth, `β 0 = 0`, `β 1 = ∞`,
  regularity on `[0, 1]`.
* Define `regularLevelSetChain` as the level-set chain on this β.
* Discharge `boundary (regularLevelSetChain) = -principalDivisorMap f`
  pointwise by composing with step 7d-d's
  `boundary_levelSetChain_eq_neg_principalDivisorMap_pointwise`.

This makes the boundary clause of `h_struct` in
`abelGeneratorPeriodCondition_of_levelSet_lattice` mechanical for the
concrete witness `Z := regularLevelSetChain f hnc h0_reg h_inf_reg`,
leaving only the **lattice-period clause** (the analytical residual:
`f_*ω` + Stokes/residue) for a future chip.

No `sorry`, no `axiom`. -/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Extracted regular β -/

/-- The regular smooth path `0 → ∞` on `RiemannSphere`, extracted from
`exists_regular_path_zero_to_infty` via `Classical.choose`. -/
def regularBeta (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (h0_reg : (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet)
    (h_inf_reg : (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet) :
    ℝ → RiemannSphere :=
  Classical.choose (f.exists_regular_path_zero_to_infty hnc h0_reg h_inf_reg)

private lemma regularBeta_spec (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (h0_reg : (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet)
    (h_inf_reg : (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (f.regularBeta hnc h0_reg h_inf_reg) ∧
    f.regularBeta hnc h0_reg h_inf_reg 0 = (((0 : ℂ) : RiemannSphere)) ∧
    f.regularBeta hnc h0_reg h_inf_reg 1 = (OnePoint.infty : RiemannSphere) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      f.regularBeta hnc h0_reg h_inf_reg t ∈ f.regularValueSet :=
  Classical.choose_spec
    (f.exists_regular_path_zero_to_infty hnc h0_reg h_inf_reg)

lemma regularBeta_smooth (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (h0_reg : (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet)
    (h_inf_reg : (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (f.regularBeta hnc h0_reg h_inf_reg) :=
  (f.regularBeta_spec hnc h0_reg h_inf_reg).1

@[simp] lemma regularBeta_zero (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (h0_reg : (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet)
    (h_inf_reg : (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet) :
    f.regularBeta hnc h0_reg h_inf_reg 0 = (((0 : ℂ) : RiemannSphere)) :=
  (f.regularBeta_spec hnc h0_reg h_inf_reg).2.1

@[simp] lemma regularBeta_one (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (h0_reg : (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet)
    (h_inf_reg : (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet) :
    f.regularBeta hnc h0_reg h_inf_reg 1 = (OnePoint.infty : RiemannSphere) :=
  (f.regularBeta_spec hnc h0_reg h_inf_reg).2.2.1

lemma regularBeta_regular (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (h0_reg : (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet)
    (h_inf_reg : (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      f.regularBeta hnc h0_reg h_inf_reg t ∈ f.regularValueSet :=
  (f.regularBeta_spec hnc h0_reg h_inf_reg).2.2.2

/-! ## Concrete level-set chain -/

/-- The level-set chain of `f` along the concrete regular `β` from
`regularBeta`. Built from `f.levelSetChain` with the smooth + regular
witnesses from `regularBeta`. -/
noncomputable def regularLevelSetChain
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (h0_reg : (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet)
    (h_inf_reg : (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet) :
    SmoothChain 𝓘(ℝ, ℂ) X :=
  f.levelSetChain hnc
    (f.regularBeta_smooth hnc h0_reg h_inf_reg)
    (f.regularBeta_regular hnc h0_reg h_inf_reg)

/-! ## Boundary identification: pointwise = `-principalDivisorMap f` -/

/-- **Boundary of the concrete regular level-set chain.** Composes
step 7d-d's `boundary_levelSetChain_eq_neg_principalDivisorMap_pointwise`
with the endpoint properties of `regularBeta` (`β 0 = 0` and `β 1 = ∞`). -/
theorem boundary_regularLevelSetChain
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (h0_reg : (((0 : ℂ) : RiemannSphere)) ∈ f.regularValueSet)
    (h_inf_reg : (OnePoint.infty : RiemannSphere) ∈ f.regularValueSet) :
    ∀ x : X,
      (SmoothChain.boundary (f.regularLevelSetChain hnc h0_reg h_inf_reg)).toFun x
        = -((principalDivisorMap f : X → ℤ) x) := by
  intro x
  unfold regularLevelSetChain
  exact f.boundary_levelSetChain_eq_neg_principalDivisorMap_pointwise
    hnc (f.regularBeta_smooth hnc h0_reg h_inf_reg)
    (f.regularBeta_regular hnc h0_reg h_inf_reg)
    (f.regularBeta_zero hnc h0_reg h_inf_reg)
    (f.regularBeta_one hnc h0_reg h_inf_reg)
    x

end MeromorphicNonzero

end JacobianChallenge

end
