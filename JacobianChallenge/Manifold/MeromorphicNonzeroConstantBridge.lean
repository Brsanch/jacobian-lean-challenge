/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.R4FibreSumBalance

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Public bridge: `IsConstantMap f.toRiemannSphere` ↔ `IsConstantMap f.toFun`

The internal lemmas `isConst_toFun_of_toRS_const` and
`not_isConstantMap_toRS_infty` (in `R4FibreSumBalance.lean`) are
`private`. This file re-derives the necessary direction publicly for use
in the C3 chain (`AbelLatticeWitness` discharge):

* The pole-set is finite by `MMeromorphicOn.poles_finite`. Together
  with `ChartedSpace ℂ X`, this forces the conclusion that
  `f.toRiemannSphere` cannot be constantly `∞`.
* Combined with the some-case argument
  (`toRiemannSphere_apply_of_nonneg` + `OnePoint.coe_injective`), this
  bridges `IsConstantMap f.toRiemannSphere → IsConstantMap f.toFun`.

The chart-ball argument is the same as the private proof; it's
small enough that replicating it once in a public chip is preferable to
exposing the original via signature changes upstream.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter Metric
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Constant `toRiemannSphere = ∞` is impossible -/

/-- **No `MeromorphicNonzero` has `toRiemannSphere ≡ ∞`.** If every point
of `X` is a pole, then `Set.univ : Set X` equals the pole set, which is
finite by `MMeromorphicOn.poles_finite`. But the chart at any point
embeds an open ball of `ℂ` injectively into `X`, contradicting
finiteness. -/
theorem not_toRiemannSphere_const_infty
    (f : MeromorphicNonzero X)
    (hRS : ∀ x : X, f.toRiemannSphere x = (OnePoint.infty : RiemannSphere)) :
    False := by
  classical
  -- All points are poles.
  have h_poles : ∀ x, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < (0 : WithTop ℤ) :=
    fun x => (toRiemannSphere_eq_infty_iff_neg f x).mp (hRS x)
  -- R2 (poles_finite): the pole set is finite.
  have hP_fin : {x : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x <
      (0 : WithTop ℤ)}.Finite :=
    JacobianChallenge.MMeromorphicOn.poles_finite (X := X)
      (𝓘(ℂ, ℂ)) f.toFun f.meromorphic f.nonvanishing_germ
  -- All of X is poles, so univ is finite.
  have h_univ_fin : (Set.univ : Set X).Finite :=
    hP_fin.subset (fun x _ => h_poles x)
  -- Pick a point (exists by `ConnectedSpace.toNonempty`).
  have hX_nonempty : Nonempty X := inferInstance
  obtain ⟨x₀⟩ := hX_nonempty
  -- Chart x₀.
  set e : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀
  have hx₀_src : x₀ ∈ e.source := mem_chart_source ℂ x₀
  have h_target_open : IsOpen e.target := e.open_target
  have h_ex0_target : e x₀ ∈ e.target := e.map_source hx₀_src
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp h_target_open _ h_ex0_target
  -- A ball in ℂ is infinite: inject `ℕ ↪ ball` via `n ↦ e x₀ + r/(n+2)`.
  have h_ball_inf : (Metric.ball (e x₀) r).Infinite := by
    let g : ℕ → ℂ := fun n => e x₀ + (((r / ((n : ℝ) + 2)) : ℝ) : ℂ)
    have h_inj : Function.Injective g := by
      intro m n h_eq
      simp only [g, add_right_inj] at h_eq
      have h_real : (r / ((m : ℝ) + 2)) = (r / ((n : ℝ) + 2)) := by
        exact_mod_cast h_eq
      have hr_ne : r ≠ 0 := ne_of_gt hr_pos
      have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
      have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
      rw [div_eq_div_iff hm2 hn2] at h_real
      have h_eq2 : ((m : ℝ) + 2) = ((n : ℝ) + 2) := by
        have := mul_left_cancel₀ hr_ne h_real.symm
        linarith
      have h_eq3 : (m : ℝ) = (n : ℝ) := by linarith
      exact_mod_cast h_eq3
    have h_mem : ∀ n, g n ∈ Metric.ball (e x₀) r := by
      intro n
      simp only [g]
      rw [Metric.mem_ball]
      have h_dist : dist (e x₀ + (((r / ((n : ℝ) + 2)) : ℝ) : ℂ)) (e x₀)
          = r / ((n : ℝ) + 2) := by
        rw [dist_eq_norm]
        have h_simp : e x₀ + (((r / ((n : ℝ) + 2)) : ℝ) : ℂ) - e x₀
            = (((r / ((n : ℝ) + 2)) : ℝ) : ℂ) := by ring
        rw [h_simp, Complex.norm_real]
        have h_pos : 0 < r / ((n : ℝ) + 2) := by positivity
        exact abs_of_pos h_pos
      rw [h_dist]
      have h_n_pos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      rw [div_lt_iff₀ h_n_pos]
      nlinarith [hr_pos]
    exact Set.infinite_of_injective_forall_mem h_inj h_mem
  -- Pull back to `e.source` via `e.symm`. `e.symm` is injective on `e.target`.
  have h_inj : Set.InjOn e.symm e.target := by
    intro a ha b hb hab
    have hsa : e (e.symm a) = a := e.right_inv ha
    have hsb : e (e.symm b) = b := e.right_inv hb
    rw [← hsa, ← hsb, hab]
  have h_inj_on_ball : Set.InjOn e.symm (Metric.ball (e x₀) r) :=
    h_inj.mono hr_sub
  have h_image_inf : (e.symm '' Metric.ball (e x₀) r).Infinite :=
    h_ball_inf.image h_inj_on_ball
  -- But `e.symm '' ball ⊆ X = univ`, which is finite. Contradiction.
  exact h_image_inf (h_univ_fin.subset (fun _ _ => Set.mem_univ _))

/-! ## Constant `toRiemannSphere ≡ some w` ⇒ constant `toFun ≡ w` -/

/-- **If `f.toRiemannSphere` is constantly `OnePoint.some w`, then
`f.toFun` is constantly `w`.** Each `f.toRiemannSphere x = some w`
forces the meromorphic order at `x` to be `≥ 0`, then the
`toRiemannSphere_apply_of_nonneg` identity translates to
`f.toFun x = w`. -/
theorem toFun_const_of_toRiemannSphere_const_some
    (f : MeromorphicNonzero X) {w : ℂ}
    (hRS : ∀ x, f.toRiemannSphere x = (OnePoint.some w : RiemannSphere)) :
    ∀ x, f.toFun x = w := by
  intro x
  have h_ne_infty : f.toRiemannSphere x ≠ (OnePoint.infty : RiemannSphere) := by
    rw [hRS x]; exact OnePoint.coe_ne_infty w
  have h_nonneg : (0 : WithTop ℤ) ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x := by
    by_contra hneg
    rw [not_le] at hneg
    apply h_ne_infty
    exact toRiemannSphere_apply_of_neg f hneg
  have h_some : f.toRiemannSphere x =
      (OnePoint.some (f.toFun x) : RiemannSphere) :=
    toRiemannSphere_apply_of_nonneg f h_nonneg
  have h_eq : (OnePoint.some (f.toFun x) : RiemannSphere) =
      (OnePoint.some w : RiemannSphere) := by
    rw [← h_some, hRS x]
  exact OnePoint.coe_injective h_eq

/-! ## Forward bridge: `IsConstantMap toRS → IsConstantMap toFun` -/

/-- **Bridge: `IsConstantMap f.toRiemannSphere → IsConstantMap f.toFun`.**
The `OnePoint.some` case uses `toFun_const_of_toRiemannSphere_const_some`;
the `OnePoint.infty` case is forbidden by `not_toRiemannSphere_const_infty`. -/
theorem isConstantMap_toFun_of_isConstantMap_toRiemannSphere
    (f : MeromorphicNonzero X)
    (h : JacobianChallenge.IsConstantMap f.toRiemannSphere) :
    JacobianChallenge.IsConstantMap f.toFun := by
  obtain ⟨c, hc⟩ := h
  cases c with
  | none => exact (f.not_toRiemannSphere_const_infty hc).elim
  | some w =>
    refine ⟨w, ?_⟩
    exact f.toFun_const_of_toRiemannSphere_const_some (fun x => hc x)

/-! ## Contrapositive bridge: `toFun nonconst → toRS nonconst` -/

/-- **Contrapositive bridge.** If `f.toFun` is not a literal constant,
then `f.toRiemannSphere` is not `IsConstantMap`. -/
theorem not_isConstantMap_toRiemannSphere_of_toFun_nonconst
    (f : MeromorphicNonzero X)
    (hf : ∀ c : ℂ, f.toFun ≠ fun _ : X => c) :
    ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere := by
  intro hRS_const
  obtain ⟨w, hw⟩ := f.isConstantMap_toFun_of_isConstantMap_toRiemannSphere hRS_const
  apply hf w
  funext x
  exact hw x

end MeromorphicNonzero

end JacobianChallenge

end
