/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathConcatAdditivityStokes
import JacobianChallenge.Manifold.SmoothPathConstFromFace0
import JacobianChallenge.Manifold.BasedSmoothLoopsBound

set_option linter.unusedSectionVars false

/-! # List-concat of based loops sums in `H₁`

For a list `loops : List (BasedLoopAt I p₀)` of smooth based loops at
`p₀`, the **concatenation** `concatList p₀ loops`
(with `nil` mapped to `SmoothPath.const I X p₀` and `cons γ rest` to
`γ.concat (concatList p₀ rest)`) is itself a smooth based loop at
`p₀`, and its `single` satisfies

```
single (concatList p₀ loops) -
  (loops.map (fun γ => single γ.val)).sum ∈ stokesBoundaries.
```

Equivalently, in the canonical Stokes `H₁` quotient,
`[γ₁ ⋆ γ₂ ⋆ ⋯ ⋆ γₖ] = [γ₁] + [γ₂] + ⋯ + [γₖ]`.

This is the **list-additivity of concatenation in H₁**, the
foundation for the smooth-Hurewicz proper (every smooth based loop is
ℤ-combination of basis loops modulo `stokesBoundaries`).

The proof is a clean induction on the list:
* Base (nil): `single (const p₀) - 0 = single (const p₀) ∈
  stokesBoundaries` (existing).
* Step (cons γ rest): `single (γ ⋆ concatList rest) ≡ single γ +
  single (concatList rest) (mod stokes)` by concat additivity, and
  `single (concatList rest) ≡ sum (rest.map single) (mod stokes)` by
  the inductive hypothesis. Combine.

## What this file ships

* `BasedLoopAt I p₀` — subtype of `SmoothPath I X` with `src = tgt =
  p₀`.
* `concatList p₀ loops` — the iterated concat as a `BasedLoopAt`.
* `single_concatList_sub_sum_singles_mem_stokesBoundaries` —
  the headline homology identity.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-! ## `BasedLoopAt`: subtype of smooth paths based at `p₀` -/

/-- **A smooth based loop at `p₀`** — a smooth path with `src = p₀`
and `tgt = p₀`. -/
def BasedLoopAt (I : ModelWithCorners ℝ E H) (X : Type*)
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X] (p₀ : X) :
    Type _ :=
  { γ : SmoothPath I X // γ.src = p₀ ∧ γ.tgt = p₀ }

namespace BasedLoopAt

variable {p₀ : X}

/-- The underlying `SmoothPath`. -/
def toPath (γ : BasedLoopAt I X p₀) : SmoothPath I X := γ.val

/-- The loop property (`src = tgt`). -/
lemma is_loop (γ : BasedLoopAt I X p₀) : γ.toPath.src = γ.toPath.tgt :=
  γ.prop.1.trans γ.prop.2.symm

@[simp] lemma toPath_src (γ : BasedLoopAt I X p₀) : γ.toPath.src = p₀ := γ.prop.1

@[simp] lemma toPath_tgt (γ : BasedLoopAt I X p₀) : γ.toPath.tgt = p₀ := γ.prop.2

/-- **The packaged `SmoothCycle` of a `BasedLoopAt`.** -/
noncomputable def singleCycle (γ : BasedLoopAt I X p₀) : SmoothCycle I X :=
  single_smoothLoop_smoothCycle γ.toPath γ.is_loop

@[simp] lemma singleCycle_coe (γ : BasedLoopAt I X p₀) :
    (γ.singleCycle : SmoothChain I X) = SmoothChain.single γ.toPath :=
  single_smoothLoop_smoothCycle_coe γ.toPath γ.is_loop

end BasedLoopAt

/-! ## List-concat -/

/-- **Iterated concatenation of based loops.** `nil` maps to
`SmoothPath.const I X p₀`; `cons γ rest` to `γ.concat (concatList p₀
rest)`. Both source and target are `p₀`, packaged in the subtype. -/
noncomputable def concatList (p₀ : X) :
    List (BasedLoopAt I X p₀) → BasedLoopAt I X p₀
  | [] => ⟨SmoothPath.const I X p₀, by
      refine ⟨?_, ?_⟩
      · exact SmoothPath.const_src p₀
      · exact SmoothPath.const_tgt p₀⟩
  | γ :: rest =>
    let rest_concat := concatList p₀ rest
    ⟨γ.toPath.concat rest_concat.toPath (by
      rw [γ.toPath_tgt, rest_concat.toPath_src]), by
      refine ⟨?_, ?_⟩
      · rw [SmoothPath.concat_src]; exact γ.toPath_src
      · rw [SmoothPath.concat_tgt]; exact rest_concat.toPath_tgt⟩

@[simp] lemma concatList_nil (p₀ : X) :
    concatList p₀ ([] : List (BasedLoopAt I X p₀))
      = ⟨SmoothPath.const I X p₀, by
          refine ⟨?_, ?_⟩
          · exact SmoothPath.const_src p₀
          · exact SmoothPath.const_tgt p₀⟩ := rfl

lemma concatList_cons_toPath (p₀ : X) (γ : BasedLoopAt I X p₀)
    (rest : List (BasedLoopAt I X p₀)) :
    (concatList p₀ (γ :: rest)).toPath
      = γ.toPath.concat (concatList p₀ rest).toPath (by
          rw [γ.toPath_tgt, (concatList p₀ rest).toPath_src]) := rfl

/-! ## Headline: list-additivity in `H₁` -/

/-- **List-additivity of concatenation in `H₁`.** For any list of
based loops at `p₀`,

```
single (concatList p₀ loops) -
  (loops.map BasedLoopAt.singleCycle).sum ∈ stokesBoundaries.
```

Equivalently, `[γ₁ ⋆ ⋯ ⋆ γₖ] = [γ₁] + ⋯ + [γₖ]` in the canonical
Stokes H₁ quotient.

Proof by list induction:
* Base (nil): `single (const p₀) - 0 = single (const p₀) ∈
  stokesBoundaries` (existing).
* Step (cons γ rest): combine `concat_additive_in_stokesBoundaries`
  with the inductive hypothesis on `rest`. -/
theorem single_concatList_sub_sum_singles_mem_stokesBoundaries
    (p₀ : X) (loops : List (BasedLoopAt I X p₀)) :
    (concatList p₀ loops).singleCycle
      - (loops.map BasedLoopAt.singleCycle).sum
    ∈ stokesBoundaries I X := by
  induction loops with
  | nil =>
    -- Base: `single (const p₀) - 0 ∈ stokesBoundaries`.
    simp only [List.map_nil, List.sum_nil, sub_zero]
    -- Show `(concatList p₀ []).singleCycle =
    -- single_smoothPath_const_smoothCycle p₀`.
    have h_eq :
        (concatList p₀ ([] : List (BasedLoopAt I X p₀))).singleCycle
          = single_smoothPath_const_smoothCycle (I := I) (X := X) p₀ := by
      apply Subtype.ext
      rw [BasedLoopAt.singleCycle_coe,
          single_smoothPath_const_smoothCycle_coe]
      rfl
    rw [h_eq]
    exact single_smoothPath_const_smoothCycle_mem_stokesBoundaries p₀
  | cons γ rest IH =>
    -- Step: combine concat additivity with IH.
    have h_concat_compat :
        γ.toPath.tgt = (concatList p₀ rest).toPath.src := by
      rw [γ.toPath_tgt, (concatList p₀ rest).toPath_src]
    have h_concat_add :=
      concat_additive_in_stokesBoundaries (I := I) (X := X) γ.toPath
        (concatList p₀ rest).toPath h_concat_compat
    -- Sum: h_concat_add + IH ∈ stokesBoundaries.
    have h_sum :
        (concat_additive_smoothCycle (I := I) (X := X) γ.toPath
            (concatList p₀ rest).toPath h_concat_compat)
          + ((concatList p₀ rest).singleCycle
              - (rest.map BasedLoopAt.singleCycle).sum)
        ∈ stokesBoundaries I X :=
      AddSubgroup.add_mem _ h_concat_add IH
    -- Show this equals the target via Subtype.ext + abel.
    have h_eq :
        (concat_additive_smoothCycle (I := I) (X := X) γ.toPath
            (concatList p₀ rest).toPath h_concat_compat)
          + ((concatList p₀ rest).singleCycle
              - (rest.map BasedLoopAt.singleCycle).sum)
        = (concatList p₀ (γ :: rest)).singleCycle
          - ((γ :: rest).map BasedLoopAt.singleCycle).sum := by
      apply Subtype.ext
      rw [SmoothCycle.coe_add, SmoothCycle.coe_sub, SmoothCycle.coe_sub]
      rw [concat_additive_smoothCycle_coe,
          BasedLoopAt.singleCycle_coe,
          BasedLoopAt.singleCycle_coe]
      -- LHS: single (γ ⋆ rest_concat) - single γ - single rest_concat
      --      + (single rest_concat - sum rest.map single)
      --   = single (γ ⋆ rest_concat) - single γ - sum rest.map single
      -- RHS: single (concatList (γ :: rest)) - sum ((γ :: rest).map single)
      --   = single (γ ⋆ rest_concat) - (single γ + sum rest.map single)
      -- Equal via abel.
      simp only [List.map_cons, List.sum_cons]
      -- The (concatList p₀ (γ :: rest)) on the RHS unfolds via
      -- `concatList_cons_toPath` to `γ.toPath.concat (concatList p₀ rest).toPath`.
      rw [concatList_cons_toPath]
      -- Push the SmoothCycle coercion through addition.
      have h_add_coe :
          (((γ.singleCycle
              + (rest.map BasedLoopAt.singleCycle).sum : SmoothCycle I X)
              : SmoothChain I X))
            = γ.singleCycle.val
              + ((rest.map BasedLoopAt.singleCycle).sum : SmoothChain I X) := by
        rw [SmoothCycle.coe_add]
      rw [h_add_coe]
      rw [BasedLoopAt.singleCycle_coe]
      abel
    rw [← h_eq]
    exact h_sum

end JacobianChallenge

end
