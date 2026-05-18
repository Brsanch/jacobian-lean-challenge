/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathConcatAdditivityStokes
import JacobianChallenge.Manifold.SmoothPathConstFromFace0
import JacobianChallenge.Manifold.SmoothPathReverseStokesBoundary
import JacobianChallenge.Manifold.BasedSmoothLoopsBound

set_option linter.unusedSectionVars false

/-! # Power of a based loop is `n` times the basis class in `H₁`

For any smooth based loop `γ` at a point `p₀ : X` (i.e.
`γ.src = γ.tgt`) and any `n : ℕ`, the **`n`-fold concatenation**

```
γⁿ := γ ⋆ γ ⋆ ⋯ ⋆ γ    (n copies, γ⁰ := const p₀)
```

is again a based loop at `p₀`, and its `single` (packaged as a
SmoothCycle) satisfies

```
single γⁿ - n • single γ ∈ stokesBoundaries.
```

Geometrically: powers of a loop multiply by the integer in `H₁`.
This is the **abelianisation framework on a single loop**, and the
proof is a clean induction on `n` using two existing chips:

1. `single_smoothPath_const_smoothCycle_mem_stokesBoundaries` —
   the base case (`γ⁰ = const p₀`, single is null-homologous).
2. `concat_additive_in_stokesBoundaries` — the inductive step
   (concat additivity in `H₁`).

Combined with the inverse-pair identity
`single_smoothPath_plus_reverse_mem_stokesBoundaries`, the same
proof scheme extends to `ℤ`-powers via `γ.reverse` (`γ⁻ⁿ` defined as
`(γ.reverse)ⁿ`).

## What this file ships

* `powerBasedLoop γ h_loop n` — the `n`-fold concat for a based loop.
* `powerBasedLoop_src` / `_tgt` / `_is_loop` — endpoint identities.
* `single_powerBasedLoop_eq_zsmul_mod_stokesBoundaries` — the
  homological identity (ℕ-version): `single γⁿ - n • single γ ∈
  stokesBoundaries`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-! ## Definition: `n`-fold concat of a based loop -/

/-- **Subtype-packaged `n`-fold power of a based loop.** Defined
recursively with the `src = γ.src` invariant carried in the subtype, to
avoid a chicken-and-egg between the definition and the endpoint lemma. -/
noncomputable def powerBasedLoopWithSrc (γ : SmoothPath I X)
    (h_loop : γ.src = γ.tgt) :
    ℕ → { δ : SmoothPath I X // δ.src = γ.src ∧ δ.tgt = γ.src }
  | 0 => ⟨SmoothPath.const I X γ.src, by
      refine ⟨?_, ?_⟩
      · exact SmoothPath.const_src γ.src
      · exact SmoothPath.const_tgt γ.src⟩
  | n + 1 =>
    let prev := powerBasedLoopWithSrc γ h_loop n
    ⟨γ.concat prev.1 (by rw [prev.2.1]; exact h_loop.symm), by
      refine ⟨?_, ?_⟩
      · rw [SmoothPath.concat_src]
      · rw [SmoothPath.concat_tgt]
        exact prev.2.2⟩

/-- **`n`-fold concatenation of a based loop with itself.** For a based
loop `γ` at `p₀` (with `γ.src = γ.tgt`), the `n`-th power
`powerBasedLoop γ h_loop n` is `γ ⋆ γ ⋆ ⋯ ⋆ γ` (`n` copies). The
`n = 0` case is the constant path at `γ.src`. -/
noncomputable def powerBasedLoop (γ : SmoothPath I X) (h_loop : γ.src = γ.tgt)
    (n : ℕ) : SmoothPath I X :=
  (powerBasedLoopWithSrc γ h_loop n).1

/-- The source of `powerBasedLoop γ h_loop n` is always `γ.src`. -/
@[simp] lemma powerBasedLoop_src (γ : SmoothPath I X)
    (h_loop : γ.src = γ.tgt) (n : ℕ) :
    (powerBasedLoop γ h_loop n).src = γ.src :=
  (powerBasedLoopWithSrc γ h_loop n).2.1

/-- The target of `powerBasedLoop γ h_loop n` is always `γ.src` (=
`γ.tgt` since `γ` is a loop). -/
@[simp] lemma powerBasedLoop_tgt (γ : SmoothPath I X)
    (h_loop : γ.src = γ.tgt) (n : ℕ) :
    (powerBasedLoop γ h_loop n).tgt = γ.src :=
  (powerBasedLoopWithSrc γ h_loop n).2.2

/-- `powerBasedLoop γ h_loop n` is a based loop at `γ.src`. -/
lemma powerBasedLoop_is_loop (γ : SmoothPath I X)
    (h_loop : γ.src = γ.tgt) (n : ℕ) :
    (powerBasedLoop γ h_loop n).src = (powerBasedLoop γ h_loop n).tgt := by
  rw [powerBasedLoop_src, powerBasedLoop_tgt]

/-! ## Headline: powers in `H₁` are `n` times the basis class -/

/-- **Power-of-loop homological identity (ℕ-version).** For any smooth
based loop `γ` at `p₀` (with `γ.src = γ.tgt`) and any `n : ℕ`,

```
single γⁿ - n • single γ ∈ stokesBoundaries.
```

Equivalently, in the canonical Stokes `H₁` quotient, `[γⁿ] = n • [γ]`.

Proof by induction on `n`:
* Base (`n = 0`): `γ⁰ = const p₀`; its single is null-homologous via
  `single_smoothPath_const_smoothCycle_mem_stokesBoundaries`.
* Step (`n → n + 1`): `single γⁿ⁺¹ ≡ single γ + single γⁿ (mod stokes)`
  by `concat_additive_in_stokesBoundaries`, and `single γⁿ ≡ n • single
  γ (mod stokes)` by the inductive hypothesis. Summing the two gives
  `single γⁿ⁺¹ ≡ (n + 1) • single γ (mod stokes)`. -/
theorem single_powerBasedLoop_sub_nsmul_mem_stokesBoundaries
    (γ : SmoothPath I X) (h_loop : γ.src = γ.tgt) (n : ℕ) :
    single_smoothLoop_smoothCycle (powerBasedLoop γ h_loop n)
        (powerBasedLoop_is_loop γ h_loop n)
      - (n : ℤ) • single_smoothLoop_smoothCycle γ h_loop
    ∈ stokesBoundaries I X := by
  induction n with
  | zero =>
    -- Base case: `single γ⁰ - 0 • single γ = single (const γ.src) ∈ stokesBoundaries`.
    simp only [Nat.cast_zero, zero_smul, sub_zero]
    -- Show `single_smoothLoop_smoothCycle (powerBasedLoop γ h_loop 0) _`
    -- equals `single_smoothPath_const_smoothCycle γ.src` as SmoothCycles.
    have h_eq :
        single_smoothLoop_smoothCycle (powerBasedLoop γ h_loop 0)
            (powerBasedLoop_is_loop γ h_loop 0)
          = single_smoothPath_const_smoothCycle (I := I) (X := X) γ.src := by
      apply Subtype.ext
      rw [single_smoothLoop_smoothCycle_coe,
          single_smoothPath_const_smoothCycle_coe]
      rfl
    rw [h_eq]
    exact single_smoothPath_const_smoothCycle_mem_stokesBoundaries γ.src
  | succ k IH =>
    -- Inductive step: combine concat additivity with IH.
    -- Endpoint compat for the concat.
    have h_concat : γ.tgt = (powerBasedLoop γ h_loop k).src := by
      rw [powerBasedLoop_src]; exact h_loop.symm
    -- concat_additive: `single (γ.concat γᵏ) - single γ - single γᵏ ∈ stokes`.
    have h_concat_add :=
      concat_additive_in_stokesBoundaries (I := I) (X := X) γ
        (powerBasedLoop γ h_loop k) h_concat
    -- Sum h_concat_add + IH gives:
    -- `single γᵏ⁺¹ - single γ - single γᵏ + single γᵏ - k • single γ ∈ stokes`,
    -- i.e., `single γᵏ⁺¹ - (k + 1) • single γ ∈ stokes`.
    have h_sum :
        (concat_additive_smoothCycle (I := I) (X := X) γ
            (powerBasedLoop γ h_loop k) h_concat)
          + (single_smoothLoop_smoothCycle (powerBasedLoop γ h_loop k)
                (powerBasedLoop_is_loop γ h_loop k)
              - (k : ℤ) • single_smoothLoop_smoothCycle γ h_loop)
        ∈ stokesBoundaries I X :=
      AddSubgroup.add_mem _ h_concat_add IH
    -- Show that the sum equals the target SmoothCycle at the cycle level.
    have h_eq :
        (concat_additive_smoothCycle (I := I) (X := X) γ
            (powerBasedLoop γ h_loop k) h_concat)
          + (single_smoothLoop_smoothCycle (powerBasedLoop γ h_loop k)
                (powerBasedLoop_is_loop γ h_loop k)
              - (k : ℤ) • single_smoothLoop_smoothCycle γ h_loop)
        = single_smoothLoop_smoothCycle (powerBasedLoop γ h_loop (k + 1))
            (powerBasedLoop_is_loop γ h_loop (k + 1))
          - ((k + 1 : ℕ) : ℤ) • single_smoothLoop_smoothCycle γ h_loop := by
      apply Subtype.ext
      -- Unfold the zsmul coercion using `(AddSubgroup.subtype _).map_zsmul`.
      have h_zsmul_coe : ∀ (m : ℤ) (c : SmoothCycle I X),
          (((m • c) : SmoothCycle I X) : SmoothChain I X)
            = m • (c : SmoothChain I X) :=
        fun m c => (AddSubgroup.subtype (SmoothCycle I X)).map_zsmul c m
      simp only [SmoothCycle.coe_add, SmoothCycle.coe_sub,
                 concat_additive_smoothCycle_coe,
                 single_smoothLoop_smoothCycle_coe, h_zsmul_coe]
      -- The (k+1)-th power reduces to γ.concat (powerBasedLoop γ h_loop k).
      -- Push the Nat-cast of (k+1) through and let `abel` handle the ℤ-arith.
      have h_cast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
      rw [h_cast]
      change SmoothChain.single (γ.concat (powerBasedLoop γ h_loop k) h_concat)
            - SmoothChain.single γ
            - SmoothChain.single (powerBasedLoop γ h_loop k)
          + (SmoothChain.single (powerBasedLoop γ h_loop k)
              - (k : ℤ) • SmoothChain.single γ)
        = SmoothChain.single (γ.concat (powerBasedLoop γ h_loop k) h_concat)
          - ((k : ℤ) + 1) • SmoothChain.single γ
      -- `abel` understands ℤ-action and the (k+1) split.
      module
    rw [← h_eq]
    exact h_sum

end JacobianChallenge

end
