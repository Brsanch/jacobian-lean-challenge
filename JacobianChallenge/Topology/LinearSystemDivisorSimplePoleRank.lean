/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LinearSystemDivisorZeroLiouville
import JacobianChallenge.Topology.RRStrictLtFromSimplePole
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Basic

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `2 ≤ Module.rank ℂ (linearSystemGermDeltaP p)` from a simple-pole germ

This file ships the explicit `rank ≥ 2` content of genus-zero
Riemann–Roch at `δp` on the germ field, **unconditionally** from the
existence of a meromorphic germ with `orderAt p = -1`.

The path is direct: given a simple-pole germ `ψ` at `p`, the pair
`![1, ψ]` is linearly independent in `MeromorphicFunctionGerm X` (no
nontrivial complex linear combination vanishes — order arithmetic at
`p` rules it out). Both `1` and `ψ` sit in `linearSystemGermDeltaP p`
(`1` by `one_mem_linearSystemGermDeltaP`, `ψ` by hypothesis), so the
span `Submodule.span ℂ {1, ψ}` is a 2-dim sub-Submodule of `L(δp)`,
delivering `2 ≤ Module.rank ℂ (linearSystemGermDeltaP p)` via
`LinearIndependent.cardinal_le_rank`.

The `Module.finrank ℂ (linearSystemGermDeltaP p) ≥ 2` shape (matching
`RR_DimGE2_GenusZero_Germ`) follows downstream if `linearSystemGermDeltaP
p` is known to be finite-dimensional — that finite-dim content is the
remaining `dim L(δp) ≤ deg D + 1 - g + dim L(K - D)` upper-bound side
of Riemann-Roch, which is **not** in this chip.

## Contents

* `algebraMapC_smul_one` — `a • 1 = algebraMapC a` (rephrase of
  `algebraMapC_eq_smul_one`).
* `linearIndependent_one_simplePoleGerm` — `LinearIndependent ℂ ![1, ψ]`
  for `ψ.orderAt p = -1`.
* `rank_linearSystemGermDeltaP_ge_two_of_existsSimplePole` —
  `2 ≤ Module.rank ℂ (linearSystemGermDeltaP p)` from
  `ExistsSimplePoleGermAtSomePoint X`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Set Filter

namespace JacobianChallenge.MeromorphicFunctionField

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Identifying `a • 1 = algebraMapC a` -/

/-- `a • 1 = algebraMapC a` (just `algebraMapC_eq_smul_one.symm`). -/
lemma algebraMapC_smul_one (a : ℂ) :
    a • (1 : MeromorphicFunctionGerm X) = algebraMapC a :=
  (algebraMapC_eq_smul_one a).symm

/-! ## Linear independence -/

/-- **`{1, ψ}` is linearly independent** whenever `ψ` has a true simple
pole (order exactly `-1`) at some point `p`. Order arithmetic at `p`
rules out `ψ = a • 1 = algebraMapC a`: a constant germ has order `⊤`
(if `a = 0`) or `0` (if `a ≠ 0`), neither of which is `-1`. -/
theorem linearIndependent_one_simplePoleGerm
    {p : X} {ψ : MeromorphicFunctionGerm X}
    (hψ_ord : ψ.orderAt p = ((-1 : ℤ) : WithTop ℤ)) :
    LinearIndependent ℂ ![(1 : MeromorphicFunctionGerm X), ψ] := by
  -- Use `LinearIndependent.pair_iff'`: with `1 ≠ 0`, reduces to
  -- `∀ a : ℂ, a • 1 ≠ ψ`.
  apply (LinearIndependent.pair_iff' (one_ne_zero_germ X)).mpr
  intro a h_eq
  -- `h_eq : a • 1 = ψ`. Compose with `algebraMapC_smul_one : a • 1 = algebraMapC a`
  -- to get `ψ = algebraMapC a`.
  have hψ_eq : ψ = algebraMapC a :=
    h_eq.symm.trans (algebraMapC_smul_one (X := X) a)
  -- Apply `orderAt p` both sides.
  have h_ord_eq : ψ.orderAt p
      = MeromorphicFunctionGerm.orderAt p (algebraMapC a) := by
    rw [hψ_eq]
  rw [hψ_ord, orderAt_algebraMapC] at h_ord_eq
  -- `h_ord_eq : (-1 : WithTop ℤ) = (if a = 0 then ⊤ else 0)`.
  by_cases ha : a = 0
  · rw [if_pos ha] at h_ord_eq
    -- `-1 = ⊤` in WithTop ℤ: impossible.
    exact WithTop.coe_ne_top h_ord_eq
  · rw [if_neg ha] at h_ord_eq
    -- `(-1 : WithTop ℤ) = (0 : WithTop ℤ)`: impossible.
    have h_int : ((-1 : ℤ) : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) := by
      have h0 : (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) := by norm_cast
      rw [← h0]; exact h_ord_eq
    have h_eq_int : (-1 : ℤ) = (0 : ℤ) := WithTop.coe_injective h_int
    omega

/-! ## `rank ≥ 2` of `linearSystemGermDeltaP p` -/

/-- The pair `![1, ψ]` lies inside `linearSystemGermDeltaP p`. The
constant `1` is there by `one_mem_linearSystemGermDeltaP`; `ψ` is by
hypothesis. -/
lemma one_simplePoleGerm_range_le_linearSystemGermDeltaP
    {p : X} {ψ : MeromorphicFunctionGerm X}
    (hψ_in : ψ ∈ linearSystemGermDeltaP p) :
    Set.range (![(1 : MeromorphicFunctionGerm X), ψ])
        ⊆ (linearSystemGermDeltaP p : Set (MeromorphicFunctionGerm X)) := by
  rw [Set.range_subset_iff]
  intro i
  fin_cases i
  · -- `![1, ψ] 0 = 1`.
    show (1 : MeromorphicFunctionGerm X) ∈ linearSystemGermDeltaP p
    exact one_mem_linearSystemGermDeltaP p
  · -- `![1, ψ] 1 = ψ`.
    exact hψ_in

/-- **`2 ≤ Module.rank ℂ (linearSystemGermDeltaP p)` from a simple-pole
germ at `p`.** -/
theorem rank_linearSystemGermDeltaP_ge_two_of_simplePoleGerm
    {p : X} {ψ : MeromorphicFunctionGerm X}
    (hψ_in : ψ ∈ linearSystemGermDeltaP p)
    (hψ_ord : ψ.orderAt p = ((-1 : ℤ) : WithTop ℤ)) :
    2 ≤ Module.rank ℂ (linearSystemGermDeltaP p) := by
  -- Linear independence in the ambient.
  have h_li : LinearIndependent ℂ
      ![(1 : MeromorphicFunctionGerm X), ψ] :=
    linearIndependent_one_simplePoleGerm hψ_ord
  -- The family lifts into the Submodule.
  have h_range : Set.range (![(1 : MeromorphicFunctionGerm X), ψ])
      ⊆ (linearSystemGermDeltaP p : Set (MeromorphicFunctionGerm X)) :=
    one_simplePoleGerm_range_le_linearSystemGermDeltaP hψ_in
  -- Bundle into a `Fin 2 → linearSystemGermDeltaP p` family.
  let v : Fin 2 → linearSystemGermDeltaP p := fun i =>
    ⟨![(1 : MeromorphicFunctionGerm X), ψ] i, h_range ⟨i, rfl⟩⟩
  -- Linear independence transfers via `LinearMap.linearIndependent_iff` applied
  -- to the (injective) inclusion `Submodule.subtype`.
  have h_subtype_inj :
      LinearMap.ker (Submodule.subtype (linearSystemGermDeltaP p)) = ⊥ :=
    Submodule.ker_subtype _
  have h_v_li : LinearIndependent ℂ v := by
    have h_comp :
        (Submodule.subtype (linearSystemGermDeltaP p)) ∘ v
          = ![(1 : MeromorphicFunctionGerm X), ψ] := by
      funext i
      fin_cases i <;> rfl
    rw [← (Submodule.subtype (linearSystemGermDeltaP p)).linearIndependent_iff
            h_subtype_inj, h_comp]
    exact h_li
  -- Apply universe-polymorphic `cardinal_lift_le_rank`, then simplify.
  have h_card := h_v_li.cardinal_lift_le_rank
  -- `lift #(Fin 2) = 2`, `lift (Module.rank …) = Module.rank …`.
  simpa using h_card

/-- **`2 ≤ Module.rank ℂ (linearSystemGermDeltaP p)` from
`ExistsSimplePoleGermAtSomePoint X`.** -/
theorem rank_linearSystemGermDeltaP_ge_two_of_existsSimplePole
    (hSP : JacobianChallenge.MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X) :
    ∃ p : X, 2 ≤ Module.rank ℂ (linearSystemGermDeltaP p) := by
  obtain ⟨p, ψ, hψ_in, hψ_ord⟩ := hSP
  exact ⟨p, rank_linearSystemGermDeltaP_ge_two_of_simplePoleGerm hψ_in hψ_ord⟩

end JacobianChallenge.MeromorphicFunctionField

end
