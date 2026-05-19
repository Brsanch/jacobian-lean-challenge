/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusBumpMultiplier
import JacobianChallenge.Manifold.ComplexTorusHurewiczFromLift

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # `SmoothPathLiftHypothesisTorus L` holds unconditionally on `ℂ ⧸ L`

Combines all twelve building chips into the closing discharge:

  `theorem smoothPathLiftHypothesisTorus_holds (L) : SmoothPathLiftHypothesisTorus L`

For every smooth based loop `γ` on `ℂ ⧸ L` with `γ.src = 0`:

1. Lebesgue chart-anchor partition gives `N : ℕ` with `0 < N` and
   `xs_Fin : Fin N → ℂ` (`exists_chartAnchor_partition`).
2. Pad to `xs : ℕ → ℂ`.
3. Cumulative seam-shift in `L` (`cumulativeShift_mem_L`).
4. Per-piece smooth lift `pwLiftPiece` with lift identity + zero-at-zero.
5. Global piecewise `pwLiftGlobal` with lift identity on `Icc 0 1`
   (`mkQ_pwLiftGlobal_on_Icc01`) and ContMDiffOn `Ioo (-δ) (1 + δ)`
   for some `δ > 0` (`exists_extended_smooth_radius`).
6. Multiply by `smoothBump δ` to extend smoothly to all of `ℝ`.
7. Verify ContMDiff, lift_zero, lift identity.

## What this file ships

* `ComplexTorus.smoothPathLiftHypothesisTorus_holds` — the unconditional
  discharge of `SmoothPathLiftHypothesisTorus L` on the complex torus.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff Topology

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **`SmoothPathLiftHypothesisTorus L` holds unconditionally** on the
complex torus. Builds the smooth lift via the chart-anchor partition +
cumulative shift + bump multiplier. -/
theorem smoothPathLiftHypothesisTorus_holds :
    SmoothPathLiftHypothesisTorus L := by
  intro γ h_src
  -- Step 1: chart-anchor partition.
  obtain ⟨N, hN, xs_Fin, h_partition_Fin⟩ := exists_chartAnchor_partition L γ
  -- Step 2: pad xs_Fin to ℕ → ℂ.
  let xs : ℕ → ℂ := fun k => if h : k < N then xs_Fin ⟨k, h⟩ else 0
  -- Express the partition in terms of xs.
  have h_partition : ∀ k : ℕ, k < N → ∀ s : ℝ,
      (k : ℝ) / N ≤ s → s ≤ ((k : ℝ) + 1) / N →
      γ.ambient s ∈ (localChart L (discRadius_separates L) (xs k)).symm.source := by
    intro k hk s hs_low hs_hi
    have h_xs_eq : xs k = xs_Fin ⟨k, hk⟩ := by simp [xs, dif_pos hk]
    rw [h_xs_eq]
    apply h_partition_Fin ⟨k, hk⟩ s
    · convert hs_low using 1
    · convert hs_hi using 1
  -- Step 3: extended smoothness radius.
  obtain ⟨δ, hδ_pos, h_global_smooth⟩ :=
    exists_extended_smooth_radius L xs γ h_src N hN h_partition
  -- Step 4: define lift := smoothBump δ • pwLiftGlobal.
  let lift : ℝ → ℂ := fun t => (smoothBump δ t : ℂ) * pwLiftGlobal L xs γ N t
  -- Step 5: prove the four conditions.
  refine ⟨lift, ?_, ?_, ?_⟩
  · -- ContMDiff lift via local covering.
    apply contMDiff_of_locally_contMDiffOn
    intro x
    -- Cases: x ∈ Ioo (-δ) (1+δ), or x ≤ -δ/2, or x ≥ 1+δ/2.
    -- The first contains the support of bump; outside the bump support, lift = 0.
    by_cases h_in_open : x ∈ Set.Ioo (-δ) (1 + δ)
    · -- x in open Ioo. ContMDiffOn lift on this set via smul/mul.
      refine ⟨Set.Ioo (-δ) (1 + δ), isOpen_Ioo, h_in_open, ?_⟩
      -- lift = bump • pwLiftGlobal on Ioo. Both smooth.
      have h_bump_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (smoothBump δ) :=
        smoothBump_contMDiff δ
      have h_bump_smooth_on : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (smoothBump δ)
          (Set.Ioo (-δ) (1 + δ)) := h_bump_smooth.contMDiffOn
      -- Product as smul: lift t = (smoothBump δ t) • pwLiftGlobal t.
      -- For ℂ valued via ℝ-scalar action: (smoothBump δ t : ℂ) * pwLiftGlobal t
      -- = (smoothBump δ t : ℝ) • pwLiftGlobal t (since ℝ acts on ℂ as a ℝ-vector space).
      have h_eq : lift = fun t => smoothBump δ t • pwLiftGlobal L xs γ N t := by
        funext t
        show (smoothBump δ t : ℂ) * pwLiftGlobal L xs γ N t
          = smoothBump δ t • pwLiftGlobal L xs γ N t
        -- ℝ-scalar smul on ℂ = (·: ℂ) *.
        simp [Complex.real_smul]
      rw [h_eq]
      exact h_bump_smooth_on.smul h_global_smooth
    · -- x outside Ioo (-δ) (1+δ). Either x ≤ -δ or x ≥ 1+δ.
      -- For x ≤ -δ/2, bump = 0 in a nbhd, lift = 0 in a nbhd.
      -- For x ≥ 1+δ/2, similarly.
      have h_outside : x ≤ -δ ∨ 1 + δ ≤ x := by
        by_contra h_neither
        push_neg at h_neither
        exact h_in_open ⟨h_neither.1, h_neither.2⟩
      rcases h_outside with h_x_le | h_x_ge
      · -- Use the open nbhd Iio (-δ/2). On this set, bump = 0.
        refine ⟨Set.Iio (-δ / 2), isOpen_Iio, ?_, ?_⟩
        · simp only [Set.mem_Iio]
          linarith
        · have h_zero : Set.EqOn lift (fun _ => (0 : ℂ)) (Set.Iio (-δ / 2)) := by
            intro t ht
            show (smoothBump δ t : ℂ) * pwLiftGlobal L xs γ N t = 0
            have h_bump_zero : smoothBump δ t = 0 :=
              smoothBump_eq_zero_left hδ_pos (le_of_lt ht)
            rw [h_bump_zero, Complex.ofReal_zero, zero_mul]
          have h_const_smooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (fun _ : ℝ => (0 : ℂ))
              (Set.Iio (-δ / 2)) := contMDiffOn_const
          exact h_const_smooth.congr (fun y hy => h_zero hy)
      · -- Right side: use Ioi (1 + δ/2).
        refine ⟨Set.Ioi (1 + δ / 2), isOpen_Ioi, ?_, ?_⟩
        · simp only [Set.mem_Ioi]; linarith
        · have h_zero : Set.EqOn lift (fun _ => (0 : ℂ)) (Set.Ioi (1 + δ / 2)) := by
            intro t ht
            show (smoothBump δ t : ℂ) * pwLiftGlobal L xs γ N t = 0
            have h_bump_zero : smoothBump δ t = 0 :=
              smoothBump_eq_zero_right hδ_pos (le_of_lt ht)
            rw [h_bump_zero, Complex.ofReal_zero, zero_mul]
          have h_const_smooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (fun _ : ℝ => (0 : ℂ))
              (Set.Ioi (1 + δ / 2)) := contMDiffOn_const
          exact h_const_smooth.congr (fun y hy => h_zero hy)
  · -- lift 0 = 0.
    show (smoothBump δ 0 : ℂ) * pwLiftGlobal L xs γ N 0 = 0
    rw [pwLiftGlobal_at_zero L xs γ N, mul_zero]
  · -- mkQ ∘ lift = γ.ambient on Icc 0 1.
    intro t ht
    show L.mkQ ((smoothBump δ t : ℂ) * pwLiftGlobal L xs γ N t) = γ.ambient t
    have h_bump_one : smoothBump δ t = 1 := smoothBump_eq_one_on_Icc01 hδ_pos ht
    rw [h_bump_one, Complex.ofReal_one, one_mul]
    exact mkQ_pwLiftGlobal_on_Icc01 L xs γ h_src N hN h_partition t ht

end ComplexTorus

end JacobianChallenge

end
