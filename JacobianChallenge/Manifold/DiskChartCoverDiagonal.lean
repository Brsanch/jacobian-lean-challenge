/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverArzela

set_option diagnostics.threshold 100

/-! # Diagonal subsequence: uniform convergence on every inner disk

Iterating chip 5b's per-chart Arzelà-Ascoli across the (finite) base
points of a `DiskChartCover` gives a *single* strictly monotone
subsequence `ψ : ℕ → ℕ` such that for *every* base point `x ∈ basePoints`,
the restricted `localCoeff (om_n (ψ k)) x` sequence converges in the
`BoundedContinuousFunction` metric on the inner closed disk to some
limit `g_lim_x`.

The proof is `Finset.induction` on a subset `S ⊆ basePoints`: at each
step we apply chip 5b to extract a further subsequence convergent at
the new base point, then compose with the already-built subsequence
for the previous base points.

## Main result

* `DiskChartCover.extract_diagonal_subseq` — diagonal subsequence
  convergent at every base point.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff Pointwise
open Set Metric HolomorphicOneForm Filter

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- **Iterative extraction**: for any `S ⊆ basePoints`, extract a single
strictly monotone subsequence convergent at every base point in `S`. -/
private lemma extract_diagonal_aux (cover : DiskChartCover X) [Nonempty X]
    (M : ℝ) (hM : 0 ≤ M)
    (om_n : ℕ → HolomorphicOneForm X)
    (h_bound : ∀ n, seminormVal cover (om_n n) ≤ M) :
    ∀ (S : Finset X), S ⊆ cover.basePoints →
    ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧
    ∀ (x : X), x ∈ S → ∀ (hx_base : x ∈ cover.basePoints),
      ∃ g_lim : BoundedContinuousFunction
            ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ,
        Tendsto (fun k => localCoeffBcf cover (om_n (ψ k)) hx_base) atTop (𝓝 g_lim) := by
  haveI : DecidableEq X := Classical.decEq X
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨id, strictMono_id, ?_⟩
    intro x hx _
    exact absurd hx (Finset.notMem_empty _)
  | insert x S' hx_ni IH =>
    intro hS
    have hS' : S' ⊆ cover.basePoints := fun y hy =>
      hS (Finset.mem_insert_of_mem hy)
    obtain ⟨ψ_S', hψ_S'_mono, hS'_conv⟩ := IH hS'
    have hx_base_x : x ∈ cover.basePoints := hS (Finset.mem_insert_self x S')
    have h_subseq_bound :
        ∀ k, seminormVal cover (om_n (ψ_S' k)) ≤ M := fun k => h_bound _
    obtain ⟨φ, g_lim_x, hφ_mono, h_tendsto_x⟩ :=
      arzela_localCoeff_innerDisk cover M hM (fun k => om_n (ψ_S' k))
        h_subseq_bound hx_base_x
    refine ⟨ψ_S' ∘ φ, hψ_S'_mono.comp hφ_mono, ?_⟩
    intro y hy hy_base
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hy_S'
    · exact ⟨g_lim_x, h_tendsto_x⟩
    · obtain ⟨g_lim_y, h_tendsto_y⟩ := hS'_conv y hy_S' hy_base
      refine ⟨g_lim_y, ?_⟩
      have h_comp :
          (fun k => localCoeffBcf cover (om_n ((ψ_S' ∘ φ) k)) hy_base)
            = (fun k => localCoeffBcf cover (om_n (ψ_S' k)) hy_base) ∘ φ := by
        funext k
        rfl
      rw [h_comp]
      exact h_tendsto_y.comp hφ_mono.tendsto_atTop

/-- **Diagonal subsequence**: a single strictly monotone subsequence
`ψ : ℕ → ℕ` such that `localCoeff (om_n (ψ k)) x` converges in the
`BoundedContinuousFunction` metric on the inner closed disk for every
base point `x ∈ basePoints`. -/
theorem extract_diagonal_subseq (cover : DiskChartCover X) [Nonempty X]
    (M : ℝ) (hM : 0 ≤ M)
    (om_n : ℕ → HolomorphicOneForm X)
    (h_bound : ∀ n, seminormVal cover (om_n n) ≤ M) :
    ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧
    ∀ (x : X) (hx : x ∈ cover.basePoints),
      ∃ g_lim : BoundedContinuousFunction
            ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ,
        Tendsto (fun k => localCoeffBcf cover (om_n (ψ k)) hx) atTop (𝓝 g_lim) := by
  obtain ⟨ψ, hψ_mono, h_conv⟩ :=
    extract_diagonal_aux cover M hM om_n h_bound cover.basePoints
      (Finset.Subset.refl _)
  refine ⟨ψ, hψ_mono, ?_⟩
  intro x hx
  exact h_conv x hx hx

end DiskChartCover

end JacobianChallenge

end
