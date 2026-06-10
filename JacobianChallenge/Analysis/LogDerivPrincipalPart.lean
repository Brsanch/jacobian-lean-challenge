/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic

set_option linter.unusedSectionVars false

/-! # The principal part of a logarithmic derivative

At a point `x₀` where `F` is meromorphic of order `n`, the logarithmic
derivative has a **simple pole with residue `n`**:

* `logDeriv_eventuallyEq_principalPart` — on a punctured neighborhood,
  `F'/F = n/(z − x₀) + G'/G` for the unit `G` of the local normal form
  `F = (z−x₀)ⁿ·G` (`G` analytic, `G x₀ ≠ 0`), and `F` is nonvanishing
  there;
* `mul_logDeriv_sub_principalPart_eventuallyEq` — consequently
  `z·F'/F − n·x₀/(z − x₀)` agrees near `x₀` with the analytic function
  `n + z·G'/G`: the singularity of the Abel integrand `z·F'/F` at `x₀`
  is removable after subtracting the principal part `n·x₀/(z − x₀)`.

This is the local input of the residue side of the forward-Abel contour
argument (`HANDOFF_TLDIVSUM.md`, piece 3, item (i)).

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Topology

namespace JacobianChallenge

namespace LogDerivPrincipalPart

variable {F : ℂ → ℂ} {x₀ : ℂ} {n : ℤ}

/-- **Local normal form of the logarithmic derivative**: at a point of
meromorphic order `n`, on a punctured neighborhood `F` is nonvanishing
and `F'/F = n/(z−x₀) + G'/G` with `G` the analytic nonvanishing unit. -/
theorem logDeriv_eventuallyEq_principalPart
    (hF : MeromorphicAt F x₀)
    (hord : meromorphicOrderAt F x₀ = n) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G x₀ ∧ G x₀ ≠ 0 ∧
      (∀ᶠ z in 𝓝[≠] x₀,
        deriv F z / F z = (n : ℂ) / (z - x₀) + deriv G z / G z
          ∧ F z ≠ 0) := by
  obtain ⟨G, hG, hG0, hFeq⟩ := (meromorphicOrderAt_eq_int_iff hF).mp hord
  refine ⟨G, hG, hG0, ?_⟩
  -- Open set on which the normal form holds pointwise.
  obtain ⟨U, hUopen, hx₀U, hUsub⟩ :
      ∃ U : Set ℂ, IsOpen U ∧ x₀ ∈ U ∧
        ∀ z ∈ U \ {x₀}, F z = (z - x₀) ^ n • G z := by
    have hmem : ∀ᶠ z in 𝓝 x₀, z ∈ ({x₀}ᶜ : Set ℂ) →
        F z = (z - x₀) ^ n • G z :=
      eventually_nhdsWithin_iff.mp hFeq
    obtain ⟨V, hVsub, hVopen, hx₀V⟩ := eventually_nhds_iff.mp hmem
    exact ⟨V, hVopen, hx₀V, fun z hz => hVsub z hz.1 hz.2⟩
  -- Open set on which `G` is analytic.
  obtain ⟨W₁, hW₁sub, hW₁open, hx₀W₁⟩ :=
    eventually_nhds_iff.mp hG.eventually_analyticAt
  -- Open set on which `G` is nonvanishing.
  obtain ⟨W₂, hW₂sub, hW₂open, hx₀W₂⟩ :=
    eventually_nhds_iff.mp (hG.continuousAt.eventually_ne hG0)
  -- The combined open neighborhood.
  set V : Set ℂ := U ∩ W₁ ∩ W₂ with hV_def
  have hVopen : IsOpen V := (hUopen.inter hW₁open).inter hW₂open
  have hx₀V : x₀ ∈ V := ⟨⟨hx₀U, hx₀W₁⟩, hx₀W₂⟩
  have hVmem : V ∩ {x₀}ᶜ ∈ 𝓝[≠] x₀ :=
    Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (hVopen.mem_nhds hx₀V))
      self_mem_nhdsWithin
  filter_upwards [hVmem] with z hz
  obtain ⟨⟨⟨hzU, hzW₁⟩, hzW₂⟩, hzne'⟩ := hz
  have hzne : z ≠ x₀ := hzne'
  have hsub : z - x₀ ≠ 0 := sub_ne_zero.mpr hzne
  have hGz : G z ≠ 0 := hW₂sub z hzW₂
  have hGz_an : AnalyticAt ℂ G z := hW₁sub z hzW₁
  have hpow_ne : (z - x₀) ^ n ≠ 0 := zpow_ne_zero n hsub
  -- Pointwise normal form and nonvanishing.
  have hFz : F z = (z - x₀) ^ n * G z := by
    have h := hUsub z ⟨hzU, hzne⟩
    rw [h, smul_eq_mul]
  have hFz_ne : F z ≠ 0 := by
    rw [hFz]
    exact mul_ne_zero hpow_ne hGz
  refine ⟨?_, hFz_ne⟩
  -- `F` agrees with the normal form on a neighborhood of `z`, so the
  -- derivatives agree.
  have hFφ : F =ᶠ[𝓝 z] fun w => (w - x₀) ^ n * G w := by
    have hopen : IsOpen ((U ∩ W₁ ∩ W₂) ∩ {x₀}ᶜ) :=
      hVopen.inter (isOpen_compl_singleton)
    filter_upwards [hopen.mem_nhds ⟨⟨⟨hzU, hzW₁⟩, hzW₂⟩, hzne⟩] with w hw
    have h := hUsub w ⟨hw.1.1.1, hw.2⟩
    rw [h, smul_eq_mul]
  -- The derivative of the normal form at `z`.
  have hpow_deriv : HasDerivAt (fun w : ℂ => (w - x₀) ^ n)
      ((n : ℂ) * (z - x₀) ^ (n - 1)) z := by
    have hz' := hasDerivAt_zpow n (z - x₀) (Or.inl hsub)
    have hcomp := hz'.comp z ((hasDerivAt_id z).sub_const x₀)
    simpa using hcomp
  have hG_deriv : HasDerivAt G (deriv G z) z :=
    hGz_an.differentiableAt.hasDerivAt
  have hφ_deriv : HasDerivAt (fun w : ℂ => (w - x₀) ^ n * G w)
      ((n : ℂ) * (z - x₀) ^ (n - 1) * G z
        + (z - x₀) ^ n * deriv G z) z :=
    hpow_deriv.mul hG_deriv
  have hderivF : deriv F z
      = (n : ℂ) * (z - x₀) ^ (n - 1) * G z + (z - x₀) ^ n * deriv G z := by
    rw [hFφ.deriv_eq]
    exact hφ_deriv.deriv
  -- The quotient computation.
  rw [hderivF, hFz]
  have hzpow : (z - x₀) ^ (n - 1) = (z - x₀) ^ n * (z - x₀)⁻¹ :=
    zpow_sub_one₀ hsub n
  rw [hzpow]
  field_simp

/-- **Removability of the Abel integrand after principal-part
subtraction**: near `x₀`, `z·F'/F − n·x₀/(z−x₀)` agrees with the
analytic function `n + z·G'/G`. -/
theorem mul_logDeriv_sub_principalPart_eventuallyEq
    (hF : MeromorphicAt F x₀)
    (hord : meromorphicOrderAt F x₀ = n) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A x₀ ∧
      (∀ᶠ z in 𝓝[≠] x₀,
        z * (deriv F z / F z) - (n : ℂ) * x₀ / (z - x₀) = A z
          ∧ F z ≠ 0) := by
  obtain ⟨G, hG, hG0, hev⟩ := logDeriv_eventuallyEq_principalPart hF hord
  refine ⟨fun z => (n : ℂ) + z * (deriv G z / G z), ?_, ?_⟩
  · -- Analyticity of `n + z·G'/G` at `x₀`.
    apply AnalyticAt.add analyticAt_const
    apply AnalyticAt.mul analyticAt_id
    exact (hG.deriv).div hG hG0
  · filter_upwards [hev, self_mem_nhdsWithin] with z hz hzne
    obtain ⟨heq, hFne⟩ := hz
    have hzne' : z ≠ x₀ := hzne
    have hsub : z - x₀ ≠ 0 := sub_ne_zero.mpr hzne'
    refine ⟨?_, hFne⟩
    rw [heq]
    field_simp
    ring

end LogDerivPrincipalPart

end JacobianChallenge

end
