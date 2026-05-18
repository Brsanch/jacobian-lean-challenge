/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.GenericGenusH1SpansTopFromLoopHomology

set_option linter.unusedSectionVars false

/-! # Smooth symplectic basis on a compact Riemann surface

A `SmoothSymplecticBasis I X p₀ g` is a tuple of `2g` smooth based
loops at `p₀ : X` intended to represent the standard symplectic
homology basis `a₁, b₁, …, a_g, b_g` on a compact orientable
2-manifold of genus `g`.

This is *pure data* — no homological / topological constraints are
asserted here; those go in downstream "hypothesis" predicates
(`SmoothHurewiczHypothesis` in `SmoothHurewiczHypothesis.lean`).

## What this file ships

* `SmoothSymplecticBasis I X p₀ g` — bundle of `2g` based loops.
* `SmoothSymplecticBasis.cycleGens` — extract the corresponding
  `Fin (2g) → SmoothCycle I X` tuple via
  `single_smoothLoop_smoothCycle`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

/-- **`SmoothSymplecticBasis I X p₀ g`** — data of `2g` smooth based
loops at `p₀`.

For a compact orientable smooth 2-manifold of genus `g`, the classical
content (surface classification + π₁ presentation + abelianization)
provides such a tuple representing the symplectic basis of
`H₁(X; ℤ) ≅ ℤ^{2g}`. This structure carries only the loops, not the
homological-spanning property; the latter is a separate Prop
(`SmoothHurewiczHypothesis`). -/
structure SmoothSymplecticBasis
    (I : ModelWithCorners ℝ E H) (X : Type*)
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]
    (p₀ : X) (g : ℕ) where
  /-- The tuple of `2g` smooth paths. -/
  basis : Fin (2 * g) → SmoothPath I X
  /-- Each basis path has source at `p₀`. -/
  basis_src : ∀ i, (basis i).src = p₀
  /-- Each basis path has target at `p₀` (so each is a based loop). -/
  basis_tgt : ∀ i, (basis i).tgt = p₀

namespace SmoothSymplecticBasis

variable {p₀ : X} {g : ℕ}

/-- Each basis path is a loop (`src = tgt`). -/
lemma basis_is_loop (sb : SmoothSymplecticBasis I X p₀ g) (i : Fin (2 * g)) :
    (sb.basis i).src = (sb.basis i).tgt :=
  (sb.basis_src i).trans (sb.basis_tgt i).symm

/-- **The `Fin (2g) → SmoothCycle I X` tuple induced by the symplectic
basis.** Wraps each based loop with `single_smoothLoop_smoothCycle`. -/
noncomputable def cycleGens (sb : SmoothSymplecticBasis I X p₀ g) :
    Fin (2 * g) → SmoothCycle I X :=
  fun i => single_smoothLoop_smoothCycle (sb.basis i) (sb.basis_is_loop i)

@[simp] lemma cycleGens_coe
    (sb : SmoothSymplecticBasis I X p₀ g) (i : Fin (2 * g)) :
    (sb.cycleGens i : SmoothChain I X) = SmoothChain.single (sb.basis i) :=
  single_smoothLoop_smoothCycle_coe (sb.basis i) (sb.basis_is_loop i)

end SmoothSymplecticBasis

end JacobianChallenge

end
