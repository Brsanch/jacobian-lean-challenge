/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MidpointSubdivisionTelescopingHolds

set_option linter.unusedSectionVars false

/-! # Iterated midpoint subdivision + period-sum identity

Recursively iterate the 4-way midpoint subdivision `n` times, producing
a list of `4^n` smooth 2-simplices whose boundary periods sum to the
boundary period of the original σ.

## Construction

```
iteratedMidpointList σ 0 := [σ]
iteratedMidpointList σ (n+1) := (iteratedMidpointList σ n).flatMap
  (fun T => List.ofFn (midpointSubdivision T))
```

## Key identity

```
complexChainPeriod (boundary σ) α
  = ((iteratedMidpointList σ n).map
        (fun T => complexChainPeriod (boundary T) α)).sum
```

Proof: induction on `n`. The base case is trivial (single-element
list). The inductive step combines the inductive hypothesis with the
unconditional `MidpointSubdivisionTelescoping σ α`
(`midpointSubdivisionTelescoping_holds_unconditional`).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace Smooth2Simplex

/-- **Iterated midpoint subdivision** of a `Smooth2Simplex`. Returns a
list of `4^n` smooth 2-simplices at depth `n`. -/
def iteratedMidpointList (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X) : ℕ → List (Smooth2Simplex 𝓘(ℝ, ℂ) X)
  | 0 => [σ]
  | n + 1 =>
      (iteratedMidpointList σ n).flatMap
        (fun T => List.ofFn (Smooth2Simplex.midpointSubdivision T))

@[simp] lemma iteratedMidpointList_zero (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X) :
    iteratedMidpointList σ 0 = [σ] := rfl

lemma iteratedMidpointList_succ (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X) (n : ℕ) :
    iteratedMidpointList σ (n + 1)
      = (iteratedMidpointList σ n).flatMap
          (fun T => List.ofFn (Smooth2Simplex.midpointSubdivision T)) := rfl

/-! ## Per-element midpoint-subdivision sum equals telescoping RHS -/

/-- **The midpoint subdivision sum equals the Fin-4 sum.** -/
private lemma midpointSubdivision_period_list_sum_eq
    (T : Smooth2Simplex 𝓘(ℝ, ℂ) X) (α : HolomorphicOneForm X) :
    ((List.ofFn (Smooth2Simplex.midpointSubdivision T)).map
        (fun T' => complexChainPeriod (Smooth2Simplex.boundary T') α)).sum
      = ∑ i : Fin 4,
          complexChainPeriod
            (Smooth2Simplex.boundary (Smooth2Simplex.midpointSubdivision T i)) α := by
  rw [List.map_ofFn]
  rw [List.sum_ofFn]
  rfl

/-! ## Period-sum identity for iteratedMidpointList -/

/-- **Boundary period equals the sum over the iterated midpoint list.**

For any `n ≥ 0`:

```
complexChainPeriod (boundary σ) α
  = ((iteratedMidpointList σ n).map
        (fun T => complexChainPeriod (boundary T) α)).sum
```

Proof: induction on `n`, using
`midpointSubdivisionTelescoping_holds_unconditional` in the inductive
step (which says one step of midpoint subdivision preserves the sum
of boundary periods). -/
theorem complexChainPeriod_boundary_eq_iteratedMidpointList_sum
    (σ : Smooth2Simplex 𝓘(ℝ, ℂ) X) (α : HolomorphicOneForm X) (n : ℕ) :
    complexChainPeriod (Smooth2Simplex.boundary σ) α
      = ((iteratedMidpointList σ n).map
            (fun T => complexChainPeriod (Smooth2Simplex.boundary T) α)).sum := by
  induction n with
  | zero =>
    -- Base: depth-0 list is `[σ]`, sum is `complexChainPeriod (∂σ) α`.
    rw [iteratedMidpointList_zero]
    simp
  | succ n ih =>
    -- Step: depth-(n+1) list = bind midpoint over depth-n list.
    rw [iteratedMidpointList_succ]
    -- Reduce flatMap to flatten ∘ map and use `List.sum_flatten`.
    rw [List.flatMap_def, List.map_flatten, List.sum_flatten]
    rw [List.map_map]
    -- Goal:
    -- ChainPeriod (∂σ) α = ∑ T ∈ depth-n list,
    --   ∑ T' ∈ midpoint(T), ChainPeriod (∂T') α
    -- By ih and `midpointSubdivision_period_list_sum_eq`:
    rw [ih]
    -- Consolidate the RHS nested maps into a single map via `List.map_map`.
    rw [List.map_map]
    -- Both sides are now `List.map _ (depth-n list) |>.sum`. Equate via per-element identity.
    congr 1
    apply List.map_inj_left.mpr
    intro T _
    -- Goal: ChainPeriod (∂T) α
    --   = (List.sum ∘ List.map (fun T' => ChainPeriod (∂T') α)) (List.ofFn (midpoint T)).
    show complexChainPeriod (Smooth2Simplex.boundary T) α
        = (List.sum ∘ List.map (fun T' => complexChainPeriod (Smooth2Simplex.boundary T') α))
            (List.ofFn (Smooth2Simplex.midpointSubdivision T))
    simp only [Function.comp_apply]
    rw [midpointSubdivision_period_list_sum_eq]
    exact midpointSubdivisionTelescoping_holds_unconditional T α

end Smooth2Simplex

end JacobianChallenge

end
