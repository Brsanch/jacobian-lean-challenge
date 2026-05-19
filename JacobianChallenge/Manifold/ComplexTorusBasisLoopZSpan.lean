/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusBasisLoopAdditive
import JacobianChallenge.Manifold.SmoothPathConstFromFace0

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

/-! # Homological homogeneity of torus basis loops over ℤ

For any `a ∈ L`, the torus basis loop construction is ℤ-linear in `H₁`:

```
single γ_{n·a} - n • single γ_a ∈ stokesBoundaries   for every n : ℤ.
```

Proved by induction on `n` using:

* the additivity bordism from `ComplexTorusBasisLoopAdditive.lean`
  (`γ_{x + y}.cycle - γ_x.cycle - γ_y.cycle ∈ S` for `x, y ∈ L`),
* the constant-loop identification `γ_0 = SmoothPath.const _ _ 0`
  (so `γ_0.cycle ∈ stokesBoundaries`).

## What this file ships

* `ComplexTorus.basisLoopZSpan_stokesBoundaries` — the headline
  homogeneity identity.

* `ComplexTorus.torusBasisLoop_zero_eq_const` — the constant-loop
  identification at `x = 0`.

No `sorry`, no `axiom`. -/

open Set
open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## `torusBasisLoop 0 _ = SmoothPath.const _ _ 0` -/

/-- **The torus basis loop at `0 ∈ L` equals the constant loop.** -/
theorem torusBasisLoop_zero_eq_const :
    torusBasisLoop (0 : ℂ) (L.zero_mem)
      = SmoothPath.const 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L) := by
  apply SmoothPath.ext
  · rfl
  · rfl
  · intro t
    -- torusBasisLoop 0 _.toPath t = mkQ((t.val : ℂ) * 0) = mkQ 0 = 0
    -- SmoothPath.const _ _ 0.toPath t = 0
    show L.mkQ ((t.val : ℂ) * (0 : ℂ)) = (0 : ℂ ⧸ L)
    simp

/-! ## Auxiliary: `n • a` membership in `L` -/

variable {L} in
private lemma zsmul_mem_L (a : ℂ) (ha : a ∈ L) (n : ℤ) : n • a ∈ L :=
  L.smul_mem n ha

/-! ## SmoothCycle abbreviation -/

variable {L} in
/-- The smooth cycle of `torusBasisLoop x hx`. -/
noncomputable def torusBasisLoop_cycle (x : ℂ) (hx : x ∈ L) :
    SmoothCycle 𝓘(ℝ, ℂ) (ℂ ⧸ L) :=
  single_smoothLoop_smoothCycle (torusBasisLoop x hx)
    ((torusBasisLoop_src x hx).trans (torusBasisLoop_tgt x hx).symm)

/-! ## Reformulating additivity in terms of `torusBasisLoop_cycle` -/

variable {L} in
/-- **Additivity, restated**: `γ_{a+b}.cycle - γ_a.cycle - γ_b.cycle ∈ S`. -/
theorem torusBasisLoop_cycle_add_sub_mem_stokesBoundaries
    (a b : ℂ) (ha : a ∈ L) (hb : b ∈ L) :
    torusBasisLoop_cycle (a + b) (L.add_mem ha hb)
        - torusBasisLoop_cycle a ha - torusBasisLoop_cycle b hb
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) (ℂ ⧸ L) :=
  basisLoopAdditive_stokesBoundaries a b ha hb

/-! ## Path equality `torusBasisLoop x hx = torusBasisLoop y hy` when `x = y` -/

variable {L} in
/-- **`torusBasisLoop` depends only on the value, not the membership proof.** -/
theorem torusBasisLoop_eq_of_eq
    {x y : ℂ} (h_eq : x = y) (hx : x ∈ L) (hy : y ∈ L) :
    torusBasisLoop x hx = torusBasisLoop y hy := by
  subst h_eq
  rfl

variable {L} in
/-- Cycle version. -/
theorem torusBasisLoop_cycle_eq_of_eq
    {x y : ℂ} (h_eq : x = y) (hx : x ∈ L) (hy : y ∈ L) :
    torusBasisLoop_cycle x hx = torusBasisLoop_cycle y hy := by
  subst h_eq
  rfl

/-! ## Base: `γ_0.cycle ∈ stokesBoundaries` -/

variable {L} in
/-- **`γ_0.cycle ∈ stokesBoundaries`** (via `γ_0 = const` and the
fact that const-singles are in stokesBoundaries). -/
theorem torusBasisLoop_zero_cycle_mem_stokesBoundaries :
    torusBasisLoop_cycle (0 : ℂ) L.zero_mem ∈ stokesBoundaries 𝓘(ℝ, ℂ) (ℂ ⧸ L) := by
  -- γ_0.cycle = const_cycle (via SmoothPath.ext + cycle equality from path equality)
  have h_const_in :
      single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := ℂ ⧸ L)
          (0 : ℂ ⧸ L)
        ∈ stokesBoundaries 𝓘(ℝ, ℂ) (ℂ ⧸ L) :=
    single_smoothPath_const_smoothCycle_mem_stokesBoundaries (0 : ℂ ⧸ L)
  -- torusBasisLoop_cycle 0 _ = single_smoothPath_const_smoothCycle 0
  have h_eq : torusBasisLoop_cycle (0 : ℂ) L.zero_mem
      = single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := ℂ ⧸ L)
          (0 : ℂ ⧸ L) := by
    apply Subtype.ext
    unfold torusBasisLoop_cycle
    rw [single_smoothLoop_smoothCycle_coe]
    show SmoothChain.single (torusBasisLoop (0 : ℂ) L.zero_mem)
      = SmoothChain.single (SmoothPath.const 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L))
    rw [torusBasisLoop_zero_eq_const L]
  rw [h_eq]
  exact h_const_in

/-! ## Helper: γ_{x+y}.cycle = γ_x.cycle + γ_y.cycle modulo stokesBoundaries -/

variable {L} in
/-- **Telescoping form of additivity.**
`γ_{x + y}.cycle - (γ_x.cycle + γ_y.cycle) ∈ stokesBoundaries`. -/
theorem torusBasisLoop_cycle_add_eq_mod_S
    (x y : ℂ) (hx : x ∈ L) (hy : y ∈ L) :
    torusBasisLoop_cycle (x + y) (L.add_mem hx hy)
        - (torusBasisLoop_cycle x hx + torusBasisLoop_cycle y hy)
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) (ℂ ⧸ L) := by
  have h := torusBasisLoop_cycle_add_sub_mem_stokesBoundaries x y hx hy
  have h_eq : torusBasisLoop_cycle (x + y) (L.add_mem hx hy)
        - torusBasisLoop_cycle x hx - torusBasisLoop_cycle y hy
      = torusBasisLoop_cycle (x + y) (L.add_mem hx hy)
        - (torusBasisLoop_cycle x hx + torusBasisLoop_cycle y hy) := by abel
  rw [h_eq] at h
  exact h

/-! ## Headline: `γ_{n·a}.cycle - n • γ_a.cycle ∈ stokesBoundaries` -/

variable {L} in
/-- **Homological homogeneity of torus basis loops over ℤ.** -/
theorem basisLoopZSpan_stokesBoundaries
    (a : ℂ) (ha : a ∈ L) (n : ℤ) :
    torusBasisLoop_cycle (n • a) (L.smul_mem n ha)
      - n • torusBasisLoop_cycle a ha
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) (ℂ ⧸ L) := by
  induction n using Int.induction_on with
  | zero =>
    -- n = 0: γ_{0•a}.cycle - 0 • γ_a.cycle = γ_0.cycle - 0 = γ_0.cycle.
    -- We need to rewrite γ_{0•a} to γ_0 first.
    have h_zero_smul : (0 : ℤ) • a = (0 : ℂ) := zero_smul ℤ a
    rw [show (0 : ℤ) • torusBasisLoop_cycle a ha = 0 from zero_smul ℤ _]
    rw [sub_zero]
    rw [torusBasisLoop_cycle_eq_of_eq h_zero_smul (L.smul_mem 0 ha) L.zero_mem]
    exact torusBasisLoop_zero_cycle_mem_stokesBoundaries
  | succ m IH =>
    -- n = m+1: γ_{(m+1)•a}.cycle - (m+1) • γ_a.cycle.
    -- Strategy:
    -- diff_{m+1} - diff_m
    --   = γ_{(m+1)•a}.cycle - (m+1) • γ_a.cycle
    --     - γ_{m•a}.cycle + m • γ_a.cycle
    --   = γ_{(m+1)•a}.cycle - γ_{m•a}.cycle - γ_a.cycle
    --     (using (m+1) • x - m • x = x).
    -- Via the path-equality γ_{(m+1)•a} = γ_{m•a + a}, this is the
    -- additivity bordism, hence in S.
    -- So diff_{m+1} = diff_m + (something in S), and diff_m ∈ S by IH.
    have h_smul_succ : ((m : ℤ) + 1) • a = (m : ℤ) • a + a := by
      rw [add_smul, one_smul]
    have h_add_mem : (m : ℤ) • a + a ∈ L := L.add_mem (L.smul_mem _ ha) ha
    -- Additivity bordism for `m • a` and `a`:
    have h_add := torusBasisLoop_cycle_add_sub_mem_stokesBoundaries
      ((m : ℤ) • a) a (L.smul_mem _ ha) ha
    -- Rewrite γ_{(m•a) + a} as γ_{(m+1)•a} via h_smul_succ.symm.
    have h_rewrite_loop :
        torusBasisLoop_cycle ((m : ℤ) • a + a) h_add_mem
        = torusBasisLoop_cycle (((m : ℤ) + 1) • a)
            (L.smul_mem ((m : ℤ) + 1) ha) :=
      torusBasisLoop_cycle_eq_of_eq h_smul_succ.symm h_add_mem _
    rw [h_rewrite_loop] at h_add
    -- h_add : γ_{(m+1)•a}.cycle - γ_{m•a}.cycle - γ_a.cycle ∈ S.
    -- Goal: γ_{(m+1)•a}.cycle - (m+1) • γ_a.cycle ∈ S.
    -- Subtract IH from goal:
    --   (γ_{(m+1)•a}.cycle - (m+1) • γ_a.cycle) - IH
    --   = (γ_{(m+1)•a}.cycle - (m+1) • γ_a.cycle)
    --     - (γ_{m•a}.cycle - m • γ_a.cycle)
    --   = γ_{(m+1)•a}.cycle - γ_{m•a}.cycle - ((m+1) - m) • γ_a.cycle
    --   = γ_{(m+1)•a}.cycle - γ_{m•a}.cycle - γ_a.cycle
    --   = h_add.
    have h_sum := AddSubgroup.add_mem _ IH h_add
    -- h_sum : IH + h_add ∈ S, i.e.,
    --   (γ_{m•a}.cycle - m • γ_a.cycle) + (γ_{(m+1)•a}.cycle - γ_{m•a}.cycle - γ_a.cycle) ∈ S.
    -- Simplify: γ_{(m+1)•a}.cycle - m • γ_a.cycle - γ_a.cycle
    --        = γ_{(m+1)•a}.cycle - (m+1) • γ_a.cycle.
    have h_smul_chain : ((m : ℤ) + 1) • torusBasisLoop_cycle a ha
        = (m : ℤ) • torusBasisLoop_cycle a ha + torusBasisLoop_cycle a ha := by
      rw [add_smul, one_smul]
    have h_simp :
        (torusBasisLoop_cycle ((m : ℤ) • a) (L.smul_mem _ ha)
            - (m : ℤ) • torusBasisLoop_cycle a ha)
          + (torusBasisLoop_cycle (((m : ℤ) + 1) • a) (L.smul_mem _ ha)
              - torusBasisLoop_cycle ((m : ℤ) • a) (L.smul_mem _ ha)
              - torusBasisLoop_cycle a ha)
        = torusBasisLoop_cycle (((m : ℤ) + 1) • a) (L.smul_mem _ ha)
          - ((m : ℤ) + 1) • torusBasisLoop_cycle a ha := by
      rw [h_smul_chain]
      abel
    rw [h_simp] at h_sum
    exact h_sum
  | pred m IH =>
    -- n = -(m+1): γ_{-(m+1)•a}.cycle - (-(m+1)) • γ_a.cycle.
    -- Strategy: from IH at -m, plus additivity for -m•a + (-(1)•a) = -(m+1)•a.
    have h_smul_neg : (-((m : ℤ) + 1)) • a = (-(m : ℤ)) • a + (-1 : ℤ) • a := by
      rw [neg_add, add_smul]
    have h_neg_a_mem : (-1 : ℤ) • a ∈ L := L.smul_mem _ ha
    have h_neg_m_a_mem : (-(m : ℤ)) • a ∈ L := L.smul_mem _ ha
    have h_sum_mem : (-(m : ℤ)) • a + (-1 : ℤ) • a ∈ L :=
      L.add_mem h_neg_m_a_mem h_neg_a_mem
    -- Additivity for -m•a and -a:
    have h_add := torusBasisLoop_cycle_add_sub_mem_stokesBoundaries
      ((-(m : ℤ)) • a) ((-1 : ℤ) • a) h_neg_m_a_mem h_neg_a_mem
    -- Rewrite γ_{-m•a + -a} = γ_{-(m+1)•a}.
    have h_rewrite_loop :
        torusBasisLoop_cycle ((-(m : ℤ)) • a + (-1 : ℤ) • a) h_sum_mem
        = torusBasisLoop_cycle ((-((m : ℤ) + 1)) • a)
            (L.smul_mem (-((m : ℤ) + 1)) ha) :=
      torusBasisLoop_cycle_eq_of_eq h_smul_neg.symm h_sum_mem _
    rw [h_rewrite_loop] at h_add
    -- h_add : γ_{-(m+1)•a}.cycle - γ_{-m•a}.cycle - γ_{-a}.cycle ∈ S.
    -- Need to relate γ_{-a}.cycle to -γ_a.cycle.
    -- Additivity for a and -a: γ_{a + -a}.cycle - γ_a.cycle - γ_{-a}.cycle ∈ S.
    -- γ_{a + -a} = γ_0 has cycle ∈ S. So -γ_a.cycle - γ_{-a}.cycle ∈ S,
    -- i.e., γ_{-a}.cycle + γ_a.cycle ∈ S.
    have h_neg_one_a_mem : ((-1 : ℤ)) • a ∈ L := h_neg_a_mem
    have h_add_neg := torusBasisLoop_cycle_add_sub_mem_stokesBoundaries
      a ((-1 : ℤ) • a) ha h_neg_one_a_mem
    have h_a_plus_neg_eq_zero : a + (-1 : ℤ) • a = (0 : ℂ) := by
      rw [show ((-1 : ℤ)) • a = -a from neg_one_zsmul a]
      ring
    have h_rewrite_zero :
        torusBasisLoop_cycle (a + (-1 : ℤ) • a) (L.add_mem ha h_neg_one_a_mem)
        = torusBasisLoop_cycle (0 : ℂ) L.zero_mem :=
      torusBasisLoop_cycle_eq_of_eq h_a_plus_neg_eq_zero _ _
    rw [h_rewrite_zero] at h_add_neg
    -- h_add_neg : γ_0.cycle - γ_a.cycle - γ_{-a}.cycle ∈ S.
    have h_zero_in : torusBasisLoop_cycle (0 : ℂ) L.zero_mem
        ∈ stokesBoundaries 𝓘(ℝ, ℂ) (ℂ ⧸ L) :=
      torusBasisLoop_zero_cycle_mem_stokesBoundaries
    -- (γ_0.cycle - γ_a.cycle - γ_{-a}.cycle) - γ_0.cycle ∈ S, i.e.,
    -- -γ_a.cycle - γ_{-a}.cycle ∈ S.
    have h_combine := AddSubgroup.sub_mem _ h_add_neg h_zero_in
    have h_simp_combine :
        torusBasisLoop_cycle (0 : ℂ) L.zero_mem
          - torusBasisLoop_cycle a ha
          - torusBasisLoop_cycle ((-1 : ℤ) • a) h_neg_one_a_mem
          - torusBasisLoop_cycle (0 : ℂ) L.zero_mem
        = -(torusBasisLoop_cycle a ha
            + torusBasisLoop_cycle ((-1 : ℤ) • a) h_neg_one_a_mem) := by abel
    rw [h_simp_combine] at h_combine
    -- h_combine : -(γ_a.cycle + γ_{-a}.cycle) ∈ S.
    have h_neg_combine := (stokesBoundaries 𝓘(ℝ, ℂ) (ℂ ⧸ L)).neg_mem h_combine
    have h_simp_neg : -(-(torusBasisLoop_cycle a ha
            + torusBasisLoop_cycle ((-1 : ℤ) • a) h_neg_one_a_mem))
        = torusBasisLoop_cycle a ha
          + torusBasisLoop_cycle ((-1 : ℤ) • a) h_neg_one_a_mem := by abel
    rw [h_simp_neg] at h_neg_combine
    -- h_neg_combine : γ_a.cycle + γ_{-a}.cycle ∈ S.
    -- Goal: γ_{-(m+1)•a}.cycle - (-(m+1)) • γ_a.cycle ∈ S.
    -- i.e., γ_{-(m+1)•a}.cycle + (m+1) • γ_a.cycle ∈ S.
    -- From IH: γ_{-m•a}.cycle - (-m) • γ_a.cycle ∈ S,
    --       i.e., γ_{-m•a}.cycle + m • γ_a.cycle ∈ S.
    -- From h_add: γ_{-(m+1)•a}.cycle - γ_{-m•a}.cycle - γ_{-a}.cycle ∈ S.
    -- From h_neg_combine: γ_a.cycle + γ_{-a}.cycle ∈ S.
    -- Sum IH + h_add + h_neg_combine:
    --   (γ_{-m•a}.cycle + m • γ_a.cycle)
    --   + (γ_{-(m+1)•a}.cycle - γ_{-m•a}.cycle - γ_{-a}.cycle)
    --   + (γ_a.cycle + γ_{-a}.cycle)
    --   = γ_{-(m+1)•a}.cycle + m • γ_a.cycle + γ_a.cycle
    --   = γ_{-(m+1)•a}.cycle + (m+1) • γ_a.cycle.
    have h_sum := AddSubgroup.add_mem _ (AddSubgroup.add_mem _ IH h_add) h_neg_combine
    have h_smul_chain : ((m : ℤ) + 1) • torusBasisLoop_cycle a ha
        = (m : ℤ) • torusBasisLoop_cycle a ha + torusBasisLoop_cycle a ha := by
      rw [add_smul, one_smul]
    have h_simp :
        ((torusBasisLoop_cycle ((-(m : ℤ)) • a) h_neg_m_a_mem
            - (-(m : ℤ)) • torusBasisLoop_cycle a ha)
          + (torusBasisLoop_cycle ((-((m : ℤ) + 1)) • a)
              (L.smul_mem _ ha)
            - torusBasisLoop_cycle ((-(m : ℤ)) • a) h_neg_m_a_mem
            - torusBasisLoop_cycle ((-1 : ℤ) • a) h_neg_one_a_mem))
          + (torusBasisLoop_cycle a ha
            + torusBasisLoop_cycle ((-1 : ℤ) • a) h_neg_one_a_mem)
        = torusBasisLoop_cycle ((-((m : ℤ) + 1)) • a) (L.smul_mem _ ha)
          - (-((m : ℤ) + 1)) • torusBasisLoop_cycle a ha := by
      rw [show (-((m : ℤ) + 1)) • torusBasisLoop_cycle a ha
            = -(((m : ℤ) + 1) • torusBasisLoop_cycle a ha) from neg_smul _ _]
      rw [show (-(m : ℤ)) • torusBasisLoop_cycle a ha
            = -((m : ℤ) • torusBasisLoop_cycle a ha) from neg_smul _ _]
      rw [h_smul_chain]
      abel
    rw [h_simp] at h_sum
    -- Bridge `-↑m - 1 = -(↑m + 1)` arithmetic.
    have h_neg_eq : (-(m : ℤ) - 1 : ℤ) = -((m : ℤ) + 1) := by ring
    rw [h_neg_eq]
    exact h_sum

end ComplexTorus

end JacobianChallenge

end
