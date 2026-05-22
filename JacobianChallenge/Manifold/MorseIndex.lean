/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MorseHessian

set_option linter.unusedSectionVars false

/-! # Morse index of a critical point on a real 2-manifold (Phase D-2)

The **Morse index** at a non-degenerate critical point of a smooth
function `f : X → ℝ` is the dimension of the maximal subspace on which
the Hessian is negative definite. On a real 2-manifold (our complex
1-manifold viewed via `𝓘(ℝ, ℂ)`), the Hessian is a 2x2 symmetric real
matrix, so the Morse index is `0`, `1`, or `2`:

* **index 0** — Hessian positive definite, the critical point is a
  *local minimum*.
* **index 1** — Hessian indefinite (one positive, one negative
  eigenvalue), a *saddle point*.
* **index 2** — Hessian negative definite, a *local maximum*.

The Morse inequalities on a compact connected oriented real 2-manifold
of genus `g` give: `#(index 0) + #(index 2) ≥ 2` and `#(index 1) ≥
2g`, with equality (the "perfect Morse function" case) yielding a CW
structure with `1 + 2g + 1 = 2g + 2` cells.

This file shapes the Morse-index predicate abstractly. The classical
identification of indices via Hessian eigenvalue signs is concrete
linear algebra; we encode it as `Prop`-level predicates parameterised
by the chart-local Hessian.

## What this file ships

* `MorseIndexAt f x k : Prop` — the chart-local Hessian at `x` has
  Morse index `k` (i.e., the maximal subspace on which it's negative
  definite has dimension `k`).
* `IsLocalMin / IsSaddle / IsLocalMax` — specialisations for k = 0, 1,
  2 on a real 2-manifold.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℝ, ℂ) ⊤ X]

/-- **The Morse index at a critical point.** Defined as the existence
of a real ℝ-subspace `V ⊆ ℂ` of dimension `k` on which the chart-local
Hessian `H(v, v)` is strictly negative for all nonzero `v ∈ V`, AND no
larger such subspace exists.

This packages the classical "Morse index" notion (= dimension of
the maximal negative-definite subspace of the Hessian) as a Prop. -/
def MorseIndexAt (f : X → ℝ) (x : X) (k : ℕ) : Prop :=
  ∃ V : Submodule ℝ ℂ,
    Module.finrank ℝ V = k ∧
    (∀ v : V, v ≠ 0 → chartLocalHessianAt f x ![v.val, v.val] < 0) ∧
    (∀ W : Submodule ℝ ℂ,
      (∀ w : W, w ≠ 0 → chartLocalHessianAt f x ![w.val, w.val] < 0) →
      Module.finrank ℝ W ≤ k)

/-- **Local minimum**: Morse index `0` (Hessian positive definite on
all of `ℂ` viewed as ℝ²). -/
def IsLocalMinAt (f : X → ℝ) (x : X) : Prop :=
  MorseIndexAt f x 0 ∧
    ∀ v : ℂ, v ≠ 0 → 0 < chartLocalHessianAt f x ![v, v]

/-- **Saddle point**: Morse index `1` (Hessian indefinite with one
positive and one negative eigenvalue). -/
def IsSaddleAt (f : X → ℝ) (x : X) : Prop :=
  MorseIndexAt f x 1

/-- **Local maximum**: Morse index `2` (Hessian negative definite on
all of `ℂ` viewed as ℝ²). -/
def IsLocalMaxAt (f : X → ℝ) (x : X) : Prop :=
  MorseIndexAt f x 2 ∧
    ∀ v : ℂ, v ≠ 0 → chartLocalHessianAt f x ![v, v] < 0

/-- **Compatibility:** `IsLocalMaxAt` implies Hessian non-degeneracy at
`x`. (Negative definite ⇒ non-degenerate.) -/
theorem IsLocalMaxAt.isHessianNonDegenerateAt {f : X → ℝ} {x : X}
    (h : IsLocalMaxAt f x) : IsHessianNonDegenerateAt f x := by
  intro v hv
  by_contra hv_ne
  -- v ≠ 0 but H(v, w) = 0 for all w. In particular H(v, v) = 0,
  -- contradicting strict negativity at v.
  have h_self : chartLocalHessianAt f x ![v, v] = 0 := hv v
  have h_neg : chartLocalHessianAt f x ![v, v] < 0 := h.2 v hv_ne
  linarith

/-- **Compatibility:** `IsLocalMinAt` implies Hessian non-degeneracy.
(Positive definite ⇒ non-degenerate.) -/
theorem IsLocalMinAt.isHessianNonDegenerateAt {f : X → ℝ} {x : X}
    (h : IsLocalMinAt f x) : IsHessianNonDegenerateAt f x := by
  intro v hv
  by_contra hv_ne
  have h_self : chartLocalHessianAt f x ![v, v] = 0 := hv v
  have h_pos : 0 < chartLocalHessianAt f x ![v, v] := h.2 v hv_ne
  linarith

/-- **`MorseIndicesPerfect f X g`** — for a Morse function `f` on a
genus-`g` surface, the perfect-Morse-function condition: exactly
`1 + 2g + 1 = 2g + 2` critical points, with one local min, `2g`
saddles, and one local max.

This is the named-hypothesis form of the **Morse inequality equality
case**, which holds for any Morse function on a compact connected
oriented real 2-manifold whose critical-point count is minimal. -/
def IsPerfectMorseAtGenus (f : X → ℝ) (g : ℕ) : Prop :=
  ∃ (mn : X) (mx : X) (sd : Fin (2 * g) → X),
    IsLocalMinAt f mn ∧
    IsLocalMaxAt f mx ∧
    (∀ k, IsSaddleAt f (sd k)) ∧
    {x : X | mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) f x = 0} =
      ({mn, mx} : Set X) ∪ Set.range sd

end JacobianChallenge

end
