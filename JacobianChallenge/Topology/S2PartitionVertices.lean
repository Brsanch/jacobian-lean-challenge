/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.S2LoopChartPartition

/-! # Equidistant partition vertices in `unitInterval`

A small `Fin (N+1) → unitInterval` helper for the polygonal-
approximation assembly. Given `0 < N`, the equidistant partition
`k ↦ ⟨k/N, _⟩` has the expected zero/one endpoints and the expected
real-valued coordinates, providing the discrete index for
`Path.concat` over `chip 4c`'s chart-indexed partition.

## What is proved

* `partitionVertex N hN_pos k : unitInterval` — the vertex at
  `k/N`.
* `partitionVertex_zero`, `partitionVertex_last` — the first and
  last vertices equal `(0 : I)` and `(1 : I)` respectively.
* `partitionVertex_castSucc_val`, `partitionVertex_succ_val` — the
  real-valued coordinates of consecutive vertices, matching the
  endpoints of the `[k/N, (k+1)/N]` sub-interval.

These feed into the polygonal-loop construction
`Path.concat (γ ∘ partitionVertex) (stereographicStraightLine_k)`.

No `sorry`, no `axiom`.
-/

noncomputable section

open Metric Set

namespace JacobianChallenge

/-- Equidistant partition vertex in `unitInterval`. -/
def partitionVertex (N : ℕ) (hN_pos : 0 < N) (k : Fin (N + 1)) :
    unitInterval :=
  ⟨(k : ℝ) / N, by
    refine ⟨?_, ?_⟩
    · positivity
    · rw [div_le_one (by exact_mod_cast hN_pos)]
      exact_mod_cast (Fin.is_le k)⟩

@[simp]
theorem partitionVertex_zero (N : ℕ) (hN_pos : 0 < N) :
    partitionVertex N hN_pos 0 = 0 := by
  apply Subtype.ext
  simp [partitionVertex]

@[simp]
theorem partitionVertex_last (N : ℕ) (hN_pos : 0 < N) :
    partitionVertex N hN_pos (Fin.last N) = 1 := by
  apply Subtype.ext
  simp [partitionVertex, Fin.last,
    div_self (by exact_mod_cast hN_pos.ne' : (N : ℝ) ≠ 0)]

theorem partitionVertex_castSucc_val (N : ℕ) (hN_pos : 0 < N) (k : Fin N) :
    ((partitionVertex N hN_pos k.castSucc : unitInterval) : ℝ) =
      (k : ℝ) / N := rfl

theorem partitionVertex_succ_val (N : ℕ) (hN_pos : 0 < N) (k : Fin N) :
    ((partitionVertex N hN_pos k.succ : unitInterval) : ℝ) =
      ((k : ℝ) + 1) / N := by
  simp [partitionVertex, Fin.val_succ]

end JacobianChallenge

end
