/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.LogDerivPrincipalPart

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # Decomposition data for the Abel integrand

Piece-3 item (ii) of the forward-Abel contour argument
(`HANDOFF_TLDIVSUM.md`): if `F` is meromorphic at the finitely many
points of `Z` with finite order `n x` there, and analytic and
nonvanishing elsewhere on a ball, then the Abel integrand `z·F′/F`
decomposes on the ball as

  `z·F′/F = H z + ∑ x ∈ Z, (n x · x)/(z − x)`

with `H` differentiable on the whole ball — the removable-singularity
gluing of the local principal-part subtractions
(`LogDerivPrincipalPart.mul_logDeriv_sub_principalPart_eventuallyEq`):
at each `x ∈ Z` the subtracted integrand agrees on a punctured
neighborhood with an analytic function (the cross terms
`∑_{y ≠ x} (n y · y)/(z − y)` are analytic at `x`), so the glued
function `glueAcross` (defined by punctured limits on `Z`) is analytic
at every point of the ball.

This is exactly the decomposition input of
`boundaryIntegral_eq_sum_winding` (`ParallelogramResidue.lean`) with
`coeff x = n x · x`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter Metric
open scoped Topology

namespace JacobianChallenge

namespace LogDerivPrincipalPart

open Classical in
/-- Glue a function across a finite exceptional set by its punctured
limits. -/
def glueAcross (Z : Finset ℂ) (f₀ : ℂ → ℂ) : ℂ → ℂ :=
  fun z => if z ∈ Z then limUnder (𝓝[≠] z) f₀ else f₀ z

lemma glueAcross_of_notMem {Z : Finset ℂ} {f₀ : ℂ → ℂ} {z : ℂ}
    (hz : z ∉ Z) : glueAcross Z f₀ z = f₀ z := by
  rw [glueAcross]
  exact if_neg hz

lemma glueAcross_of_mem {Z : Finset ℂ} {f₀ : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ Z) : glueAcross Z f₀ z = limUnder (𝓝[≠] z) f₀ := by
  rw [glueAcross]
  exact if_pos hz

variable {F : ℂ → ℂ} {c : ℂ} {R : ℝ} {Z : Finset ℂ} {n : ℂ → ℤ}

/-- **Decomposition data for the Abel integrand** (piece 3, item (ii)):
if `F` is meromorphic of finite order `n x` at each point of the finite
set `Z` and analytic nonvanishing elsewhere on a ball, then `z·F′/F`
splits on the ball into a function differentiable on the whole ball
plus the principal-part sum `∑ (n x · x)/(z − x)` — the decomposition
consumed by `boundaryIntegral_eq_sum_winding`. -/
theorem abelIntegrand_decomposition
    (hmero : ∀ x ∈ Z, MeromorphicAt F x)
    (hord : ∀ x ∈ Z, meromorphicOrderAt F x = n x)
    (hreg : ∀ z ∈ ball c R, z ∉ (Z : Set ℂ) →
      AnalyticAt ℂ F z ∧ F z ≠ 0) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball c R) ∧
      ∀ z ∈ ball c R, z ∉ (Z : Set ℂ) →
        z * (deriv F z / F z)
          = H z + ∑ x ∈ Z, ((n x : ℂ) * x) / (z - x) := by
  classical
  refine ⟨glueAcross Z (fun w =>
    w * (deriv F w / F w) - ∑ x ∈ Z, ((n x : ℂ) * x) / (w - x)),
    ?_, ?_⟩
  · -- Differentiability on the ball, via pointwise analyticity.
    intro z hz
    suffices h : AnalyticAt ℂ (glueAcross Z (fun w =>
        w * (deriv F w / F w) - ∑ x ∈ Z, ((n x : ℂ) * x) / (w - x))) z from
      h.differentiableAt.differentiableWithinAt
    by_cases hzZ : z ∈ Z
    · -- A removable point: the local principal-part normal form glues.
      obtain ⟨A, hA, hAev⟩ :=
        mul_logDeriv_sub_principalPart_eventuallyEq (hmero z hzZ)
          (hord z hzZ)
      -- The cross terms are analytic at `z`.
      have hcross : AnalyticAt ℂ
          (fun w => ∑ x ∈ Z.erase z, ((n x : ℂ) * x) / (w - x)) z := by
        apply Finset.analyticAt_fun_sum
        intro x hx
        have hzx : z ≠ x := fun h => (Finset.mem_erase.mp hx).1 h.symm
        exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
          (sub_ne_zero.mpr hzx)
      have hBan : AnalyticAt ℂ (fun w =>
          A w - ∑ x ∈ Z.erase z, ((n x : ℂ) * x) / (w - x)) z :=
        hA.sub hcross
      -- Eventually on the punctured neighborhood, the path avoids the
      -- other exceptional points.
      have hevZ : ∀ᶠ w in 𝓝[≠] z, ∀ x ∈ Z.erase z, w ≠ x := by
        have hcl : IsClosed (↑(Z.erase z) : Set ℂ) :=
          (Z.erase z).finite_toSet.isClosed
        have hzc : z ∈ (↑(Z.erase z) : Set ℂ)ᶜ := by simp
        have h1 : ∀ᶠ w in 𝓝 z, w ∉ (↑(Z.erase z) : Set ℂ) := by
          filter_upwards [hcl.isOpen_compl.mem_nhds hzc] with w hw using hw
        filter_upwards [mem_nhdsWithin_of_mem_nhds h1] with w hw
        intro x hx h
        exact hw (by rw [h]; exact Finset.mem_coe.mpr hx)
      -- The subtracted integrand agrees with the analytic candidate on
      -- the punctured neighborhood.
      have hf₀B : (fun w => w * (deriv F w / F w)
            - ∑ x ∈ Z, ((n x : ℂ) * x) / (w - x))
          =ᶠ[𝓝[≠] z] (fun w =>
            A w - ∑ x ∈ Z.erase z, ((n x : ℂ) * x) / (w - x)) := by
        filter_upwards [hAev, hevZ] with w hw hwav
        obtain ⟨heq, -⟩ := hw
        show w * (deriv F w / F w) - ∑ x ∈ Z, ((n x : ℂ) * x) / (w - x)
          = A w - ∑ x ∈ Z.erase z, ((n x : ℂ) * x) / (w - x)
        have hsplit : (∑ x ∈ Z, ((n x : ℂ) * x) / (w - x))
            = ((n z : ℂ) * z) / (w - z)
              + ∑ x ∈ Z.erase z, ((n x : ℂ) * x) / (w - x) :=
          (Finset.add_sum_erase Z _ hzZ).symm
        rw [hsplit]
        linear_combination heq
      -- The punctured limit of the glued function is the candidate's
      -- value.
      haveI : (𝓝[≠] z).NeBot := inferInstance
      have hlim : limUnder (𝓝[≠] z) (fun w => w * (deriv F w / F w)
            - ∑ x ∈ Z, ((n x : ℂ) * x) / (w - x))
          = A z - ∑ x ∈ Z.erase z, ((n x : ℂ) * x) / (z - x) := by
        apply Filter.Tendsto.limUnder_eq
        apply Filter.Tendsto.congr' hf₀B.symm
        exact hBan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      -- The glued function agrees with the candidate on a full
      -- neighborhood.
      have hglueB : (glueAcross Z (fun w => w * (deriv F w / F w)
            - ∑ x ∈ Z, ((n x : ℂ) * x) / (w - x)))
          =ᶠ[𝓝 z] (fun w =>
            A w - ∑ x ∈ Z.erase z, ((n x : ℂ) * x) / (w - x)) := by
        have hpunct : ∀ᶠ w in 𝓝[≠] z,
            glueAcross Z (fun w => w * (deriv F w / F w)
                - ∑ x ∈ Z, ((n x : ℂ) * x) / (w - x)) w
              = A w - ∑ x ∈ Z.erase z, ((n x : ℂ) * x) / (w - x) := by
          filter_upwards [hf₀B, hevZ, self_mem_nhdsWithin]
            with w hfb hwav hwne
          have hwZ : w ∉ Z := by
            intro hmem
            exact hwav w (Finset.mem_erase.mpr ⟨hwne, hmem⟩) rfl
          rw [glueAcross_of_notMem hwZ]
          exact hfb
        have h3 := eventually_nhdsWithin_iff.mp hpunct
        filter_upwards [h3] with w hw
        by_cases hwz : w = z
        · subst hwz
          show glueAcross Z (fun w => w * (deriv F w / F w)
              - ∑ x ∈ Z, ((n x : ℂ) * x) / (w - x)) w
            = A w - ∑ x ∈ Z.erase w, ((n x : ℂ) * x) / (w - x)
          rw [glueAcross_of_mem hzZ, hlim]
        · exact hw (Set.mem_compl_singleton_iff.mpr hwz)
      exact hBan.congr hglueB.symm
    · -- A regular point: the subtracted integrand itself is analytic
      -- and the glued function agrees with it nearby.
      have hzZ' : z ∉ (Z : Set ℂ) := fun h => hzZ (Finset.mem_coe.mp h)
      obtain ⟨hFan, hFne⟩ := hreg z hz hzZ'
      have h1 : AnalyticAt ℂ (fun w => w * (deriv F w / F w)) z :=
        analyticAt_id.mul ((hFan.deriv).div hFan hFne)
      have h2 : AnalyticAt ℂ
          (fun w => ∑ x ∈ Z, ((n x : ℂ) * x) / (w - x)) z := by
        apply Finset.analyticAt_fun_sum
        intro x hx
        have hzx : z ≠ x := fun h => hzZ (by rw [h]; exact hx)
        exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
          (sub_ne_zero.mpr hzx)
      apply (h1.sub h2).congr
      have hev : ∀ᶠ w in 𝓝 z, w ∉ Z := by
        have hcl : IsClosed (Z : Set ℂ) := Z.finite_toSet.isClosed
        filter_upwards [hcl.isOpen_compl.mem_nhds hzZ'] with w hw
        exact fun hmem => hw (Finset.mem_coe.mpr hmem)
      filter_upwards [hev] with w hw
      exact (glueAcross_of_notMem hw).symm
  · -- The decomposition identity off the exceptional set.
    intro z hz hzZ
    have hzZ' : z ∉ Z := fun h => hzZ (Finset.mem_coe.mpr h)
    rw [glueAcross_of_notMem hzZ']
    show z * (deriv F z / F z)
      = (z * (deriv F z / F z) - ∑ x ∈ Z, ((n x : ℂ) * x) / (z - x))
        + ∑ x ∈ Z, ((n x : ℂ) * x) / (z - x)
    ring

end LogDerivPrincipalPart

end JacobianChallenge

end
