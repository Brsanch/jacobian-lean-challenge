/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ConcatListBasedLoopHomology
import JacobianChallenge.Manifold.ZPowerBasedLoopHomology

set_option linter.unusedSectionVars false

/-! # Signed-multiplicity word loops sum in `H₁`

For a **word** `word : List (ℤ × BasedLoopAt I X p₀)` of based loops
with integer multiplicities, the **iterated signed concatenation**

```
wordLoop p₀ word := γ₁ⁿ¹ ⋆ γ₂ⁿ² ⋆ ⋯ ⋆ γₖⁿᵏ
```

is itself a smooth based loop at `p₀`, and its `single` satisfies

```
single (wordLoop p₀ word)
  - (word.map (fun (n, γ) => n • γ.singleCycle)).sum ∈ stokesBoundaries.
```

Equivalently, `[γ₁ⁿ¹ ⋆ ⋯ ⋆ γₖⁿᵏ] = n₁ • [γ₁] + ⋯ + nₖ • [γₖ]` in the
canonical Stokes `H₁` quotient: any ℤ-linear combination of based-loop
classes in `H₁` is realised by a smooth based loop. Geometrically,
this is the surjective part of the abelianisation `π₁(X, p₀) → H₁(X;
ℤ)` on any finite set of loops, mechanically verified at the
smooth-singular-homology level.

The chip is built around a `BasedLoopAt.concat` op (smooth concat of
two based loops at `p₀`, both endpoints `p₀`) and a per-element-step
identity, with the final theorem proved by direct list induction.

## What this file ships

* `BasedLoopAt.zpow γ n` — ℤ-power on the `BasedLoopAt` subtype.
* `BasedLoopAt.concat γ δ` — concat of two based loops at the same
  basepoint.
* `wordLoop p₀ word` — iterated signed concat, by direct recursion.
* `single_wordLoop_sub_sum_zsmul_singles_mem_stokesBoundaries` —
  the signed-multiplicity headline.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-! ## `BasedLoopAt.zpow`: ℤ-power on the subtype -/

namespace BasedLoopAt

variable {p₀ : X}

/-- **ℤ-power on the `BasedLoopAt` subtype.** Wraps `zpowerBasedLoop`
applied to the underlying path. -/
noncomputable def zpow (γ : BasedLoopAt I X p₀) (n : ℤ) : BasedLoopAt I X p₀ :=
  ⟨zpowerBasedLoop γ.toPath γ.is_loop n, by
    refine ⟨?_, ?_⟩
    · rw [zpowerBasedLoop_src γ.toPath γ.is_loop n]; exact γ.toPath_src
    · rw [zpowerBasedLoop_tgt γ.toPath γ.is_loop n]; exact γ.toPath_src⟩

@[simp] lemma zpow_toPath (γ : BasedLoopAt I X p₀) (n : ℤ) :
    (γ.zpow n).toPath = zpowerBasedLoop γ.toPath γ.is_loop n := rfl

/-- **ℤ-power identity at the `BasedLoopAt` level.** -/
lemma singleCycle_zpow_sub_zsmul_mem_stokesBoundaries
    (γ : BasedLoopAt I X p₀) (n : ℤ) :
    (γ.zpow n).singleCycle - n • γ.singleCycle ∈ stokesBoundaries I X := by
  -- Unfold both .singleCycles to `single_smoothLoop_smoothCycle` of the path.
  have h_zp_eq :
      (γ.zpow n).singleCycle
        = single_smoothLoop_smoothCycle (zpowerBasedLoop γ.toPath γ.is_loop n)
            (zpowerBasedLoop_is_loop γ.toPath γ.is_loop n) := by
    apply Subtype.ext
    rw [singleCycle_coe, zpow_toPath, single_smoothLoop_smoothCycle_coe]
  have h_γ_eq :
      γ.singleCycle = single_smoothLoop_smoothCycle γ.toPath γ.is_loop := by
    apply Subtype.ext
    rw [singleCycle_coe, single_smoothLoop_smoothCycle_coe]
  rw [h_zp_eq, h_γ_eq]
  exact single_zpowerBasedLoop_sub_zsmul_mem_stokesBoundaries
    γ.toPath γ.is_loop n

/-! ## `BasedLoopAt.concat`: concat of two based loops at `p₀` -/

/-- **Concat of two based loops at `p₀`.** Both inputs have `src = tgt
= p₀`, so the concat is defined (with the endpoint-matching hypothesis
discharged from the subtype invariants), and the result is again based
at `p₀`. -/
noncomputable def concat (γ δ : BasedLoopAt I X p₀) : BasedLoopAt I X p₀ :=
  ⟨γ.toPath.concat δ.toPath (by rw [γ.toPath_tgt, δ.toPath_src]), by
    refine ⟨?_, ?_⟩
    · rw [SmoothPath.concat_src]; exact γ.toPath_src
    · rw [SmoothPath.concat_tgt]; exact δ.toPath_tgt⟩

@[simp] lemma concat_toPath (γ δ : BasedLoopAt I X p₀) :
    (γ.concat δ).toPath
      = γ.toPath.concat δ.toPath (by rw [γ.toPath_tgt, δ.toPath_src]) := rfl

/-- **Concat additivity in `H₁` at the `BasedLoopAt` level.** Same
content as `concat_additive_in_stokesBoundaries` packaged for
`BasedLoopAt`. -/
lemma singleCycle_concat_sub_singleCycle_sub_singleCycle_mem_stokesBoundaries
    (γ δ : BasedLoopAt I X p₀) :
    (γ.concat δ).singleCycle - γ.singleCycle - δ.singleCycle
      ∈ stokesBoundaries I X := by
  -- The underlying chain identity matches `concat_additive_in_stokesBoundaries`.
  have h_compat : γ.toPath.tgt = δ.toPath.src := by
    rw [γ.toPath_tgt, δ.toPath_src]
  have h :=
    concat_additive_in_stokesBoundaries (I := I) (X := X)
      γ.toPath δ.toPath h_compat
  -- The packaged `concat_additive_smoothCycle` has the same underlying chain
  -- as `(γ.concat δ).singleCycle - γ.singleCycle - δ.singleCycle`.
  have h_eq :
      concat_additive_smoothCycle (I := I) (X := X) γ.toPath δ.toPath h_compat
        = (γ.concat δ).singleCycle - γ.singleCycle - δ.singleCycle := by
    apply Subtype.ext
    rw [concat_additive_smoothCycle_coe, SmoothCycle.coe_sub, SmoothCycle.coe_sub,
        singleCycle_coe, singleCycle_coe, singleCycle_coe, concat_toPath]
  rw [← h_eq]
  exact h

end BasedLoopAt

/-! ## `wordLoop`: iterated signed concat by direct recursion -/

/-- **Iterated signed concatenation of based loops.** Recursively
defined: `nil` maps to the constant loop at `p₀`; `cons (n, γ) rest`
to `(γ.zpow n).concat (wordLoop p₀ rest)`. -/
noncomputable def wordLoop (p₀ : X) :
    List (ℤ × BasedLoopAt I X p₀) → BasedLoopAt I X p₀
  | [] => ⟨SmoothPath.const I X p₀, by
      refine ⟨?_, ?_⟩
      · exact SmoothPath.const_src p₀
      · exact SmoothPath.const_tgt p₀⟩
  | (n, γ) :: rest => (γ.zpow n).concat (wordLoop p₀ rest)

@[simp] lemma wordLoop_nil (p₀ : X) :
    (wordLoop p₀ ([] : List (ℤ × BasedLoopAt I X p₀))).toPath
      = SmoothPath.const I X p₀ := rfl

@[simp] lemma wordLoop_cons (p₀ : X) (n : ℤ) (γ : BasedLoopAt I X p₀)
    (rest : List (ℤ × BasedLoopAt I X p₀)) :
    wordLoop p₀ ((n, γ) :: rest) = (γ.zpow n).concat (wordLoop p₀ rest) := rfl

/-! ## Headline: signed-multiplicity sum identity in `H₁` -/

/-- **Signed-multiplicity word-loop homology identity.** For any word
`word : List (ℤ × BasedLoopAt I X p₀)`,

```
single (wordLoop p₀ word)
  - (word.map (fun (n, γ) => n • γ.singleCycle)).sum
  ∈ stokesBoundaries.
```

Proof by direct list induction:
* Base (nil): `single (const p₀) - 0 ∈ stokes` (existing).
* Step (cons (n, γ) rest):
  - `BasedLoopAt.singleCycle_concat_sub_..._mem_stokes` gives
    `single ((γ.zpow n).concat (wordLoop rest)) - single (γ.zpow n)
    - single (wordLoop rest) ∈ stokes`.
  - `BasedLoopAt.singleCycle_zpow_sub_zsmul_mem_stokes` gives
    `single (γ.zpow n) - n • single γ ∈ stokes`.
  - IH gives `single (wordLoop rest) - sum (rest.map ...) ∈ stokes`.
  - Sum the three, then `abel` collapses to the target identity. -/
theorem single_wordLoop_sub_sum_zsmul_singles_mem_stokesBoundaries
    (p₀ : X) (word : List (ℤ × BasedLoopAt I X p₀)) :
    (wordLoop p₀ word).singleCycle
      - (word.map (fun w => w.1 • w.2.singleCycle)).sum
    ∈ stokesBoundaries I X := by
  induction word with
  | nil =>
    -- (wordLoop p₀ []).singleCycle = single_smoothPath_const_smoothCycle p₀.
    simp only [List.map_nil, List.sum_nil, sub_zero]
    have h_eq :
        (wordLoop p₀ ([] : List (ℤ × BasedLoopAt I X p₀))).singleCycle
          = single_smoothPath_const_smoothCycle (I := I) (X := X) p₀ := by
      apply Subtype.ext
      rw [BasedLoopAt.singleCycle_coe, single_smoothPath_const_smoothCycle_coe]
      rfl
    rw [h_eq]
    exact single_smoothPath_const_smoothCycle_mem_stokesBoundaries p₀
  | cons head rest IH =>
    obtain ⟨n, γ⟩ := head
    -- wordLoop ((n, γ) :: rest) = (γ.zpow n).concat (wordLoop rest).
    -- Use the three ingredients combined by abel on a small set of opaque vars.
    have h_concat :=
      BasedLoopAt.singleCycle_concat_sub_singleCycle_sub_singleCycle_mem_stokesBoundaries
        (γ.zpow n) (wordLoop p₀ rest)
    have h_zpow :=
      BasedLoopAt.singleCycle_zpow_sub_zsmul_mem_stokesBoundaries γ n
    -- Sum the three memberships.
    have h_sum :
        ((γ.zpow n).concat (wordLoop p₀ rest)).singleCycle
            - (γ.zpow n).singleCycle - (wordLoop p₀ rest).singleCycle
          + ((γ.zpow n).singleCycle - n • γ.singleCycle)
          + ((wordLoop p₀ rest).singleCycle
              - (rest.map (fun w => w.1 • w.2.singleCycle)).sum)
        ∈ stokesBoundaries I X :=
      AddSubgroup.add_mem _ (AddSubgroup.add_mem _ h_concat h_zpow) IH
    -- Show this equals the target using set-abbrevs to keep abel fast.
    set A := ((γ.zpow n).concat (wordLoop p₀ rest)).singleCycle with hA_def
    set B := (γ.zpow n).singleCycle with hB_def
    set D := (wordLoop p₀ rest).singleCycle with hD_def
    set E := n • γ.singleCycle with hE_def
    set F := (rest.map (fun w => w.1 • w.2.singleCycle)).sum with hF_def
    have h_eq : (A - B - D) + (B - E) + (D - F) = A - (E + F) := by abel
    rw [h_eq] at h_sum
    -- The target unfolds: (wordLoop p₀ ((n, γ) :: rest)).singleCycle = A
    -- and ((n, γ) :: rest).map (...) = (n • γ.singleCycle) :: rest.map (...).
    simp only [List.map_cons, List.sum_cons]
    -- Goal: (wordLoop p₀ ((n, γ) :: rest)).singleCycle - (n • γ.singleCycle + F) ∈ stokes.
    -- (wordLoop p₀ ((n, γ) :: rest)).singleCycle = A by definition.
    change A - (E + F) ∈ stokesBoundaries I X
    exact h_sum

end JacobianChallenge

end
