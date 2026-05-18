/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PowerBasedLoopHomology

set_option linter.unusedSectionVars false

/-! # ℤ-power of a based loop is `n` times the basis class in `H₁`

Extends the ℕ-version `powerBasedLoop` to all `n : ℤ` by defining

```
γⁿ := γ ⋆ γ ⋆ ⋯ ⋆ γ    for n > 0   (n copies),
γ⁰ := const p₀,
γ⁻ⁿ := (γ.reverse)ⁿ    for n > 0.
```

The headline identity

```
single (γⁿ) - n • single γ ∈ stokesBoundaries
```

now holds for all `n : ℤ`. The negative case combines

* `single_powerBasedLoop_sub_nsmul_mem_stokesBoundaries` on `γ.reverse`
  (giving `single (γ.reverse)ⁿ - n • single γ.reverse ∈ stokes`), and
* `single_smoothPath_plus_reverse_mem_stokesBoundaries` on `γ`
  (giving `single γ + single γ.reverse ∈ stokes`, hence
  `single γ.reverse ≡ -single γ (mod stokes)`).

Together: `single (γ.reverse)ⁿ ≡ n • (-single γ) = -n • single γ ≡
((-n : ℤ)) • single γ (mod stokes)`, i.e., `γ⁻ⁿ` has class `-n • [γ]`,
which is exactly `(negSucc n)` interpretation.

## What this file ships

* `zpowerBasedLoop γ h_loop n` — the ℤ-power, with negative-index case
  via `powerBasedLoop γ.reverse _ |n|`.
* `zpowerBasedLoop_src` / `_tgt` / `_is_loop` — endpoint identities.
* `single_zpowerBasedLoop_sub_zsmul_mem_stokesBoundaries` —
  the ℤ-headline: `single γⁿ - n • single γ ∈ stokesBoundaries`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-! ## Reverse-loop helper -/

/-- If `γ` is a based loop, so is `γ.reverse` (with src/tgt swapped). -/
lemma reverse_is_loop_of_loop {γ : SmoothPath I X} (h_loop : γ.src = γ.tgt) :
    γ.reverse.src = γ.reverse.tgt := by
  rw [SmoothPath.reverse_src, SmoothPath.reverse_tgt]
  exact h_loop.symm

/-! ## Definition: ℤ-power -/

/-- **ℤ-power of a based loop.** For `n ≥ 0`, defined as `powerBasedLoop
γ h_loop n.toNat`; for `n < 0`, defined as `powerBasedLoop γ.reverse _
|n|.toNat`. -/
noncomputable def zpowerBasedLoop (γ : SmoothPath I X) (h_loop : γ.src = γ.tgt) :
    ℤ → SmoothPath I X
  | Int.ofNat n => powerBasedLoop γ h_loop n
  | Int.negSucc n => powerBasedLoop γ.reverse (reverse_is_loop_of_loop h_loop) (n + 1)

@[simp] lemma zpowerBasedLoop_ofNat (γ : SmoothPath I X)
    (h_loop : γ.src = γ.tgt) (n : ℕ) :
    zpowerBasedLoop γ h_loop (Int.ofNat n)
      = powerBasedLoop γ h_loop n := rfl

@[simp] lemma zpowerBasedLoop_negSucc (γ : SmoothPath I X)
    (h_loop : γ.src = γ.tgt) (n : ℕ) :
    zpowerBasedLoop γ h_loop (Int.negSucc n)
      = powerBasedLoop γ.reverse (reverse_is_loop_of_loop h_loop) (n + 1) := rfl

/-! ## Endpoint lemmas -/

lemma zpowerBasedLoop_src (γ : SmoothPath I X)
    (h_loop : γ.src = γ.tgt) (n : ℤ) :
    (zpowerBasedLoop γ h_loop n).src = γ.src := by
  cases n with
  | ofNat n =>
    change (powerBasedLoop γ h_loop n).src = γ.src
    exact powerBasedLoop_src γ h_loop n
  | negSucc n =>
    change (powerBasedLoop γ.reverse (reverse_is_loop_of_loop h_loop) (n + 1)).src
        = γ.src
    rw [powerBasedLoop_src γ.reverse (reverse_is_loop_of_loop h_loop) (n + 1)]
    rw [SmoothPath.reverse_src]
    exact h_loop.symm

lemma zpowerBasedLoop_tgt (γ : SmoothPath I X)
    (h_loop : γ.src = γ.tgt) (n : ℤ) :
    (zpowerBasedLoop γ h_loop n).tgt = γ.src := by
  cases n with
  | ofNat n =>
    change (powerBasedLoop γ h_loop n).tgt = γ.src
    exact powerBasedLoop_tgt γ h_loop n
  | negSucc n =>
    change (powerBasedLoop γ.reverse (reverse_is_loop_of_loop h_loop) (n + 1)).tgt
        = γ.src
    rw [powerBasedLoop_tgt γ.reverse (reverse_is_loop_of_loop h_loop) (n + 1)]
    rw [SmoothPath.reverse_src]
    exact h_loop.symm

lemma zpowerBasedLoop_is_loop (γ : SmoothPath I X)
    (h_loop : γ.src = γ.tgt) (n : ℤ) :
    (zpowerBasedLoop γ h_loop n).src = (zpowerBasedLoop γ h_loop n).tgt := by
  rw [zpowerBasedLoop_src, zpowerBasedLoop_tgt]

/-! ## Auxiliary: `single γ.reverse ≡ -single γ (mod stokes)` -/

/-- **The reverse of a based loop has H₁-class `-[γ]`.** From the
existing reverse-cancellation `single γ + single γ.reverse ∈ stokes`,
deduce `single γ.reverse - (-1 : ℤ) • single γ ∈ stokes`, i.e.,
`[γ.reverse] = -[γ]` in the canonical H₁ quotient. -/
lemma single_reverse_sub_neg_one_zsmul_mem_stokesBoundaries
    (γ : SmoothPath I X) (h_loop : γ.src = γ.tgt) :
    single_smoothLoop_smoothCycle γ.reverse (reverse_is_loop_of_loop h_loop)
        - ((-1 : ℤ) • single_smoothLoop_smoothCycle γ h_loop)
      ∈ stokesBoundaries I X := by
  have h_pair :=
    single_smoothPath_plus_reverse_mem_stokesBoundaries (I := I) (X := X) γ
  -- `single γ + single γ.reverse ∈ stokes`.
  -- Rewriting: `single γ.reverse - (-1) • single γ = single γ.reverse + single γ`.
  have h_eq :
      single_smoothLoop_smoothCycle γ.reverse (reverse_is_loop_of_loop h_loop)
          - ((-1 : ℤ) • single_smoothLoop_smoothCycle γ h_loop)
        = single_smoothPath_plus_reverse_smoothCycle (I := I) (X := X) γ := by
    apply Subtype.ext
    have h_zsmul_coe : ∀ (m : ℤ) (c : SmoothCycle I X),
        (((m • c) : SmoothCycle I X) : SmoothChain I X)
          = m • (c : SmoothChain I X) :=
      fun m c => (AddSubgroup.subtype (SmoothCycle I X)).map_zsmul c m
    simp only [SmoothCycle.coe_sub, single_smoothLoop_smoothCycle_coe, h_zsmul_coe,
               single_smoothPath_plus_reverse_smoothCycle_coe]
    module
  rw [h_eq]
  exact h_pair

/-- **`n • single γ.reverse ≡ n • (-single γ) = -n • single γ (mod stokes)`.** -/
lemma nsmul_single_reverse_add_nsmul_single_mem_stokesBoundaries
    (γ : SmoothPath I X) (h_loop : γ.src = γ.tgt) (n : ℕ) :
    (n : ℤ) • single_smoothLoop_smoothCycle γ.reverse (reverse_is_loop_of_loop h_loop)
        + (n : ℤ) • single_smoothLoop_smoothCycle γ h_loop
      ∈ stokesBoundaries I X := by
  -- Smul-closure of stokesBoundaries: from `single γ + single γ.reverse ∈ stokes`,
  -- `n • (single γ + single γ.reverse) = n • single γ + n • single γ.reverse ∈ stokes`.
  have h_pair :=
    single_smoothPath_plus_reverse_mem_stokesBoundaries (I := I) (X := X) γ
  have h_scaled :
      ((n : ℤ)) • single_smoothPath_plus_reverse_smoothCycle (I := I) (X := X) γ
        ∈ stokesBoundaries I X :=
    AddSubgroup.zsmul_mem _ h_pair (n : ℤ)
  -- Show this equals `n • single γ.reverse + n • single γ` at the cycle level.
  have h_eq :
      (n : ℤ) • single_smoothPath_plus_reverse_smoothCycle (I := I) (X := X) γ
      = (n : ℤ) • single_smoothLoop_smoothCycle γ.reverse
            (reverse_is_loop_of_loop h_loop)
        + (n : ℤ) • single_smoothLoop_smoothCycle γ h_loop := by
    apply Subtype.ext
    have h_zsmul_coe : ∀ (m : ℤ) (c : SmoothCycle I X),
        (((m • c) : SmoothCycle I X) : SmoothChain I X)
          = m • (c : SmoothChain I X) :=
      fun m c => (AddSubgroup.subtype (SmoothCycle I X)).map_zsmul c m
    simp only [SmoothCycle.coe_add, h_zsmul_coe,
               single_smoothPath_plus_reverse_smoothCycle_coe,
               single_smoothLoop_smoothCycle_coe]
    -- (n : ℤ) • (single γ + single γ.reverse) = (n : ℤ) • single γ.reverse + (n : ℤ) • single γ
    module
  rw [h_eq] at h_scaled
  exact h_scaled

/-! ## Headline: ℤ-power identity in `H₁` -/

/-- **ℤ-power-of-loop homological identity.** For any smooth based
loop `γ` at `p₀` (with `γ.src = γ.tgt`) and any `n : ℤ`,

```
single γⁿ - n • single γ ∈ stokesBoundaries.
```

Equivalently, in the canonical Stokes `H₁` quotient, `[γⁿ] = n • [γ]`.

Proof: case-split on `n`. For `n = Int.ofNat k ≥ 0`, directly from
`single_powerBasedLoop_sub_nsmul_mem_stokesBoundaries`. For
`n = Int.negSucc k = -(k+1)`, combine the ℕ-version applied to
`γ.reverse` with the reverse-pair scaling
`nsmul_single_reverse_add_nsmul_single_mem_stokesBoundaries`. -/
theorem single_zpowerBasedLoop_sub_zsmul_mem_stokesBoundaries
    (γ : SmoothPath I X) (h_loop : γ.src = γ.tgt) (n : ℤ) :
    single_smoothLoop_smoothCycle (zpowerBasedLoop γ h_loop n)
        (zpowerBasedLoop_is_loop γ h_loop n)
      - n • single_smoothLoop_smoothCycle γ h_loop
    ∈ stokesBoundaries I X := by
  cases n with
  | ofNat k =>
    -- single (γ^k) - k • single γ ∈ stokes  (ℕ-version applied).
    have h := single_powerBasedLoop_sub_nsmul_mem_stokesBoundaries
      γ h_loop k
    -- The zpowerBasedLoop at ofNat k unfolds to powerBasedLoop γ h_loop k.
    -- Likewise `(Int.ofNat k : ℤ) • c = (k : ℤ) • c = (k : ℕ).cast • c`.
    -- Convert by reassociating the proof term.
    have h_eq :
        single_smoothLoop_smoothCycle (zpowerBasedLoop γ h_loop (Int.ofNat k))
            (zpowerBasedLoop_is_loop γ h_loop (Int.ofNat k))
          - (Int.ofNat k : ℤ) • single_smoothLoop_smoothCycle γ h_loop
        = single_smoothLoop_smoothCycle (powerBasedLoop γ h_loop k)
            (powerBasedLoop_is_loop γ h_loop k)
          - (k : ℤ) • single_smoothLoop_smoothCycle γ h_loop := rfl
    rw [h_eq]
    exact h
  | negSucc k =>
    -- single (γ.reverse^(k+1)) - (k+1) • single γ.reverse ∈ stokes.
    have h_pow :=
      single_powerBasedLoop_sub_nsmul_mem_stokesBoundaries
        γ.reverse (reverse_is_loop_of_loop h_loop) (k + 1)
    -- (k+1) • single γ.reverse + (k+1) • single γ ∈ stokes.
    have h_pair :=
      nsmul_single_reverse_add_nsmul_single_mem_stokesBoundaries
        γ h_loop (k + 1)
    -- Sum gives: single (γ.reverse^(k+1)) + (k+1) • single γ ∈ stokes.
    have h_sum := AddSubgroup.add_mem _ h_pow h_pair
    -- Reshape: this is exactly `single (zpowerBasedLoop γ h_loop (negSucc k))
    --   - (negSucc k) • single γ ∈ stokes`, since (negSucc k : ℤ) = -(k+1).
    have h_eq :
        (single_smoothLoop_smoothCycle (powerBasedLoop γ.reverse
              (reverse_is_loop_of_loop h_loop) (k + 1))
              (powerBasedLoop_is_loop γ.reverse
                (reverse_is_loop_of_loop h_loop) (k + 1))
            - ((k + 1 : ℕ) : ℤ) • single_smoothLoop_smoothCycle γ.reverse
                (reverse_is_loop_of_loop h_loop))
          + (((k + 1 : ℕ) : ℤ) • single_smoothLoop_smoothCycle γ.reverse
                (reverse_is_loop_of_loop h_loop)
            + ((k + 1 : ℕ) : ℤ) • single_smoothLoop_smoothCycle γ h_loop)
        = single_smoothLoop_smoothCycle
            (zpowerBasedLoop γ h_loop (Int.negSucc k))
            (zpowerBasedLoop_is_loop γ h_loop (Int.negSucc k))
          - (Int.negSucc k : ℤ) • single_smoothLoop_smoothCycle γ h_loop := by
      apply Subtype.ext
      have h_zsmul_coe : ∀ (m : ℤ) (c : SmoothCycle I X),
          (((m • c) : SmoothCycle I X) : SmoothChain I X)
            = m • (c : SmoothChain I X) :=
        fun m c => (AddSubgroup.subtype (SmoothCycle I X)).map_zsmul c m
      simp only [SmoothCycle.coe_add, SmoothCycle.coe_sub, h_zsmul_coe,
                 single_smoothLoop_smoothCycle_coe]
      -- The two zpowerBasedLoop unfolds match up; the (negSucc k : ℤ) =
      -- -(k+1 : ℕ) cast is what `module` needs to close.
      change SmoothChain.single (powerBasedLoop γ.reverse
            (reverse_is_loop_of_loop h_loop) (k + 1))
          - ((k + 1 : ℕ) : ℤ) • SmoothChain.single γ.reverse
          + (((k + 1 : ℕ) : ℤ) • SmoothChain.single γ.reverse
              + ((k + 1 : ℕ) : ℤ) • SmoothChain.single γ)
        = SmoothChain.single (powerBasedLoop γ.reverse
            (reverse_is_loop_of_loop h_loop) (k + 1))
          - (Int.negSucc k : ℤ) • SmoothChain.single γ
      have h_negSucc_cast : (Int.negSucc k : ℤ) = -((k + 1 : ℕ) : ℤ) := rfl
      rw [h_negSucc_cast]
      module
    rw [← h_eq]
    exact h_sum

end JacobianChallenge

end
