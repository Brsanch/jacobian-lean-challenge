/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathLoopRebasing

set_option linter.unusedSectionVars false

/-! # The `BasedSmoothLoopsBoundHypothesis` predicate

This file names the **remaining classical-content hypothesis** for the
period-lattice closure on a simply-connected smooth manifold (e.g.,
the Riemann sphere): every based smooth loop at a chosen basepoint
`p₀` is a smooth 2-chain boundary.

With concat-additivity, reverse-cancellation, const-membership,
rebasing, and loop-rebasing all structural in `stokesBoundaries`
(landed in previous chips), the load-bearing classical input for
`stokesBoundaries 𝓘(ℝ, ℂ) X = ⊤` reduces to this single named
predicate. Discharging it on the Riemann sphere is the remaining
genuinely-new classical content (smooth Hurewicz at genus 0, e.g.,
via chart-based linear contraction in `ℂ` after a missed point).

## What this file ships

* `BasedSmoothLoopsBoundHypothesis I X p₀ : Prop` — the named
  hypothesis: every smooth loop `γ` at the basepoint `p₀` (i.e.,
  `γ.src = γ.tgt = p₀`) has `single γ` (packaged as a SmoothCycle) in
  `stokesBoundaries`.

* `single_smoothLoop_smoothCycle γ h_loop` — packaged SmoothCycle of
  a smooth loop's single.

* `single_smoothLoop_in_stokesBoundaries_of_basedLoopsBoundHypothesis` —
  combine the hypothesis with `loop_rebasing_in_stokesBoundaries`:
  for any smooth loop `γ` (not necessarily based at `p₀`) and any
  smooth based path `α : p₀ → γ.src`, `single γ ∈ stokesBoundaries`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-! ## A SmoothCycle from a smooth loop -/

/-- A smooth loop `γ : SmoothPath I X` (with `γ.src = γ.tgt`) has its
`single` automatically a smooth 1-cycle. -/
lemma single_smoothLoop_mem_smoothCycle (γ : SmoothPath I X)
    (h_loop : γ.src = γ.tgt) :
    SmoothChain.single γ ∈ JacobianChallenge.SmoothCycle I X := by
  rw [SmoothCycle.mem_iff, SmoothChain.boundary_single,
      SmoothChain.boundarySingle]
  simp [h_loop]

/-- Packaged SmoothCycle of a smooth loop's `single`. -/
noncomputable def single_smoothLoop_smoothCycle (γ : SmoothPath I X)
    (h_loop : γ.src = γ.tgt) : SmoothCycle I X :=
  ⟨SmoothChain.single γ, single_smoothLoop_mem_smoothCycle γ h_loop⟩

@[simp] lemma single_smoothLoop_smoothCycle_coe (γ : SmoothPath I X)
    (h_loop : γ.src = γ.tgt) :
    (single_smoothLoop_smoothCycle γ h_loop : SmoothChain I X)
      = SmoothChain.single γ := rfl

/-! ## The named hypothesis -/

/-- **`BasedSmoothLoopsBoundHypothesis I X p₀`**.

Says: every smooth loop `γ : SmoothPath I X` with `γ.src = γ.tgt = p₀`
has `single γ` (packaged as a SmoothCycle) in `stokesBoundaries I X`.

This is the **load-bearing classical input** for `stokesBoundaries = ⊤`
at genus 0 on a simply-connected smooth manifold (e.g., the Riemann
sphere). Discharging it requires the smooth-Hurewicz step: smoothing
the continuous null-homotopy delivered by `SimplyConnectedSpace` into
a smooth 2-chain bounding the loop. On the Riemann sphere this is
constructive via chart-based linear contraction in `ℂ` after a
missed point.

With this hypothesis + loop-rebasing + smooth-path-connectedness,
every smooth 1-cycle on `X` lies in `stokesBoundaries I X`, hence
`stokesBoundaries = ⊤`. -/
def BasedSmoothLoopsBoundHypothesis (I : ModelWithCorners ℝ E H)
    (X : Type*) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]
    (p₀ : X) : Prop :=
  ∀ γ : SmoothPath I X, ∀ h_src : γ.src = p₀, ∀ h_tgt : γ.tgt = p₀,
    single_smoothLoop_smoothCycle γ (h_src.trans h_tgt.symm)
      ∈ stokesBoundaries I X

/-! ## Headline: every smooth loop bounds, under the hypothesis -/

/-- **From `BasedSmoothLoopsBoundHypothesis I X p₀` + a smooth based
path `α : p₀ → γ.src`, every smooth loop `γ : SmoothPath I X` has
`single γ ∈ stokesBoundaries`.**

Proof: combine loop-rebasing (which says
`single γ - single (α ⋆ γ ⋆ α.reverse) ∈ stokesBoundaries`) with the
hypothesis applied to the based loop `α ⋆ γ ⋆ α.reverse` at `p₀`. -/
theorem single_smoothLoop_in_stokesBoundaries_of_basedLoopsBoundHypothesis
    (p₀ : X) (h_hyp : BasedSmoothLoopsBoundHypothesis I X p₀)
    (γ : SmoothPath I X) (h_loop : γ.src = γ.tgt)
    (α : SmoothPath I X) (h_α_src : α.src = p₀) (h_αγ : α.tgt = γ.src) :
    single_smoothLoop_smoothCycle γ h_loop ∈ stokesBoundaries I X := by
  -- Step 1: loop_rebasing says single γ - single (α ⋆ γ ⋆ α.reverse) ∈ stokesBoundaries.
  have h_rebasing :=
    loop_rebasing_in_stokesBoundaries (I := I) (X := X) γ α h_loop h_αγ
  -- Step 2: α ⋆ γ ⋆ α.reverse is a based loop at p₀.
  set based_loop := α.concat (γ.concat α.reverse
        (by rw [SmoothPath.reverse_src]; exact h_αγ ▸ h_loop.symm))
      (by rw [SmoothPath.concat_src]; exact h_αγ)
    with h_based_loop_def
  have h_based_loop_src : based_loop.src = p₀ := by
    simp [based_loop, SmoothPath.concat_src, h_α_src]
  have h_based_loop_tgt : based_loop.tgt = p₀ := by
    simp [based_loop, SmoothPath.concat_tgt, SmoothPath.reverse_tgt, h_α_src]
  have h_based_loop_loop : based_loop.src = based_loop.tgt :=
    h_based_loop_src.trans h_based_loop_tgt.symm
  -- Step 3: apply hypothesis to based_loop.
  have h_based_loop_in :=
    h_hyp based_loop h_based_loop_src h_based_loop_tgt
  -- Step 4: add the two stokes-boundary memberships.
  -- loop_rebasing_smoothCycle has underlying chain
  --   single γ - single based_loop.
  -- h_based_loop_in has underlying chain
  --   single based_loop.
  -- Sum: single γ - single based_loop + single based_loop = single γ.
  have h_sum :
      loop_rebasing_smoothCycle γ α h_loop h_αγ
        + single_smoothLoop_smoothCycle based_loop h_based_loop_loop
        ∈ stokesBoundaries I X :=
    AddSubgroup.add_mem _ h_rebasing h_based_loop_in
  -- Establish the cycle-level equality.
  have h_eq :
      loop_rebasing_smoothCycle γ α h_loop h_αγ
        + single_smoothLoop_smoothCycle based_loop h_based_loop_loop
      = single_smoothLoop_smoothCycle γ h_loop := by
    apply Subtype.ext
    rw [SmoothCycle.coe_add,
        single_smoothLoop_smoothCycle_coe,
        single_smoothLoop_smoothCycle_coe]
    -- LHS underlying chain: (single γ - single based_loop) + single based_loop.
    -- RHS underlying chain: single γ.
    show (loop_rebasing_smoothCycle γ α h_loop h_αγ : SmoothChain I X)
          + SmoothChain.single based_loop
        = SmoothChain.single γ
    show (SmoothChain.single γ - SmoothChain.single based_loop)
          + SmoothChain.single based_loop
        = SmoothChain.single γ
    abel
  rw [← h_eq]
  exact h_sum

end JacobianChallenge

end
