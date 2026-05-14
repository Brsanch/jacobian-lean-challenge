/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LinearSystemDivisorConstants
import JacobianChallenge.Topology.RRDimensionFormGerm
import JacobianChallenge.Topology.ExistsMeroSimplePoleSplit
import JacobianChallenge.Topology.HolomorphicLocallyConstantDischarge
import JacobianChallenge.Manifold.MeromorphicFunctionGermCanonicalize

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `linearSystemDivisor 0 = constantsGerm` under Liouville

The unconditional `Liouville on a compact connected complex 1-manifold`
hypothesis (`JacobianChallenge.LiouvilleOnCompactConnected X` — every
holomorphic-everywhere `MeromorphicNonzero X` is constant; classical
max-modulus content in reach of mathlib's
`Complex.norm_eventually_eq_of_isLocalMax` and the open-mapping theorem)
collapses `L(0)` — the subspace of globally holomorphic germs — to the
constants subspace.

The bridge is the canonicalize machinery from
`Manifold/MeromorphicFunctionGermCanonicalize.lean`: given a non-zero
germ `φ ∈ L(0)`, pick a representative `f : MMer X` (whose every order
is `≠ ⊤` by the identity theorem), canonicalize to
`MeromorphicNonzero X` with the same germ, apply Liouville to conclude
the canonicalised function is the constant `c`, hence the germ is
`algebraMapC c`.

## Contents

* `algebraMapC_eq_smul_one` — for any `c : ℂ`, `algebraMapC c = c • 1`
  in `MeromorphicFunctionGerm X`. (Standard ℂ-algebra fact.)
* `algebraMapC_mem_constantsGerm` — every constant germ lies in
  `constantsGerm X`.
* `constantsGerm_le_linearSystemDivisor_zero` — constants embed into
  `L(0)` (trivial, no Liouville).
* `linearSystemDivisor_zero_le_constantsGerm` — every germ in `L(0)` is
  a constant germ, **conditional on `LiouvilleOnCompactConnected X`**.
* `linearSystemDivisor_zero_eq_constantsGerm` — equality.
* `finrank_linearSystemDivisor_zero_eq_one` — `dim_ℂ L(0) = 1`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace JacobianChallenge.MeromorphicFunctionField

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## `algebraMapC c = c • 1` in the germ field -/

/-- `algebraMapC c = c • 1` in `MeromorphicFunctionGerm X`. -/
lemma algebraMapC_eq_smul_one (c : ℂ) :
    (algebraMapC c : MeromorphicFunctionGerm X)
      = c • (1 : MeromorphicFunctionGerm X) :=
  Algebra.algebraMap_eq_smul_one c


/-- Every constant germ lies in the `constantsGerm` subspace. -/
lemma algebraMapC_mem_constantsGerm (c : ℂ) :
    (algebraMapC c : MeromorphicFunctionGerm X) ∈ constantsGerm X := by
  rw [algebraMapC_eq_smul_one]
  exact Submodule.smul_mem _ c (one_mem_constantsGerm X)

/-! ## Constants ⊆ `L(0)` (trivial direction) -/

/-- `(1 : MeromorphicFunctionGerm X) ∈ linearSystemDivisor 0`. -/
lemma one_mem_linearSystemDivisor_zero :
    (1 : MeromorphicFunctionGerm X)
      ∈ linearSystemDivisor (0 : JacobianChallenge.Div X) := by
  -- `1 = algebraMapC 1` from `RingHom.map_one`.
  have h_one : (1 : MeromorphicFunctionGerm X) = algebraMapC 1 :=
    (algebraMapC (X := X)).map_one.symm
  rw [h_one]
  exact IsBoundedByDivisor.const_of_effective
    (D := (0 : JacobianChallenge.Div X)) (fun _ => le_refl 0) 1

/-- **`constantsGerm X ≤ linearSystemDivisor (0 : Div X)`.** Constants
are holomorphic everywhere, so trivially they sit in `L(0)`. -/
lemma constantsGerm_le_linearSystemDivisor_zero :
    constantsGerm X ≤ linearSystemDivisor (0 : JacobianChallenge.Div X) := by
  rw [constantsGerm, Submodule.span_le, Set.singleton_subset_iff]
  exact one_mem_linearSystemDivisor_zero

/-! ## `L(0) ⊆ constants` under `LiouvilleOnCompactConnected` -/

/-- **`linearSystemDivisor 0 ≤ constantsGerm X`** under
`LiouvilleOnCompactConnected X`. Every globally-holomorphic germ is a
constant germ.

Proof: pick a representative `f : MMer X`. If `mk f = 0`, then `0 ∈
constantsGerm`. Otherwise `f` has `AllOrdersNeTop` by the identity
theorem (`allOrdersNeTop_of_mk_ne_zero`); canonicalise to
`g : MeromorphicNonzero X` via `MMer.toMeromorphicNonzero`, holomorphic
everywhere (order is preserved). Liouville delivers `IsConstantMap
g.toFun = ∃ c, ∀ x, g.toFun x = c`. The germ of `g` equals the original
germ (`canonicalize_mk_eq`), so the original germ is the constant germ
`algebraMapC c ∈ constantsGerm`. -/
theorem linearSystemDivisor_zero_le_constantsGerm
    (hLiou : JacobianChallenge.LiouvilleOnCompactConnected X) :
    linearSystemDivisor (0 : JacobianChallenge.Div X) ≤ constantsGerm X := by
  intro φ hφ
  rcases φ with ⟨f⟩
  by_cases h_zero : (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm X) = 0
  · -- φ = 0 case: 0 is in every Submodule.
    show (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm X) ∈ constantsGerm X
    rw [h_zero]
    exact Submodule.zero_mem _
  · -- φ ≠ 0 case: canonicalise + apply Liouville.
    have hf_all : MMer.AllOrdersNeTop f :=
      MMer.allOrdersNeTop_of_mk_ne_zero h_zero
    -- Extract the L(0) condition into a chart-pullback form via `IsBoundedByDivisor_mk_iff`.
    have h_in : IsBoundedByDivisor (0 : JacobianChallenge.Div X)
        (MeromorphicFunctionGerm.mk f) := hφ
    rw [IsBoundedByDivisor_mk_iff] at h_in
    -- For all y, `0 ≤ mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun y` (since `-D y = 0`).
    have h_f_holo : ∀ y, 0 ≤ mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y := by
      intro y
      have h_y := h_in y
      -- `(0 : Div X) y = 0`, so `-(0 : ℤ) = 0`.
      simpa using h_y
    -- Canonicalise to `MeromorphicNonzero`.
    set g := MMer.toMeromorphicNonzero f hf_all with hg_def
    -- `g.toFun` is holomorphic everywhere (order preserved).
    have h_g_holo : ∀ x, 0 ≤ mmeromorphicOrderAt 𝓘(ℂ, ℂ) g.toFun x := by
      intro x
      rw [hg_def, MMer.toMeromorphicNonzero_order_eq f hf_all x]
      exact h_f_holo x
    -- Apply Liouville: `g.toFun` is constant.
    obtain ⟨c, hg_const⟩ := hLiou g h_g_holo
    -- `g.toFun = fun _ => c`.
    have h_g_eq_const : g.toFun = (fun _ : X => c) := funext hg_const
    -- `mk f = mk (canonicalize f hf_all) = mk (MMer.const c)`.
    have h_mk_eq : (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm X)
        = MeromorphicFunctionGerm.mk (MMer.const c) := by
      rw [← MMer.canonicalize_mk_eq f hf_all]
      apply Quotient.sound
      intro y
      apply Filter.Eventually.of_forall
      intro z
      show (MMer.canonicalize f hf_all).toFun z = (MMer.const c).toFun z
      -- `(canonicalize f hf_all).toFun = g.toFun` by `toMeromorphicNonzero` def.
      have h1 : (MMer.canonicalize f hf_all).toFun z = g.toFun z := rfl
      rw [h1, h_g_eq_const]
      rfl
    -- `mk (MMer.const c) = algebraMapC c ∈ constantsGerm`.
    show (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm X) ∈ constantsGerm X
    rw [h_mk_eq]
    -- `algebraMapC c = MeromorphicFunctionGerm.mk (MMer.const c)` by defn of `algebraMapC`.
    have h_alg : (algebraMapC c : MeromorphicFunctionGerm X)
        = MeromorphicFunctionGerm.mk (MMer.const c) := rfl
    rw [← h_alg]
    exact algebraMapC_mem_constantsGerm c

/-! ## Equality and `dim = 1` -/

/-- **`linearSystemDivisor (0 : Div X) = constantsGerm X`** under
`LiouvilleOnCompactConnected X`. The L(0) subspace equals the constants
subspace on a compact connected complex 1-manifold. -/
theorem linearSystemDivisor_zero_eq_constantsGerm
    (hLiou : JacobianChallenge.LiouvilleOnCompactConnected X) :
    linearSystemDivisor (0 : JacobianChallenge.Div X) = constantsGerm X :=
  le_antisymm (linearSystemDivisor_zero_le_constantsGerm hLiou)
              constantsGerm_le_linearSystemDivisor_zero

/-- **`dim_ℂ L(0) = 1`** under `LiouvilleOnCompactConnected X`. The
canonical genus-0 Riemann-Roch instance at the zero divisor. -/
theorem finrank_linearSystemDivisor_zero_eq_one
    (hLiou : JacobianChallenge.LiouvilleOnCompactConnected X) :
    Module.finrank ℂ
        (linearSystemDivisor (0 : JacobianChallenge.Div X)) = 1 := by
  rw [linearSystemDivisor_zero_eq_constantsGerm hLiou]
  exact finrank_constantsGerm_eq_one X

/-! ## Unconditional versions

The Liouville hypothesis `LiouvilleOnCompactConnected X` is **discharged
unconditionally** in `Topology/HolomorphicLocallyConstantDischarge.lean`
via the clopen globalisation of the chart-level max-modulus principle
(`MaxModLocalConstancy.eventually_eq_const_at_max` + compactness
+ connectedness of `X`). Composing gives unconditional analogues of the
above. -/

/-- **`linearSystemDivisor 0 = constantsGerm X`** — unconditional on a
compact connected complex 1-manifold modeled on `ℂ`. -/
theorem linearSystemDivisor_zero_eq_constantsGerm_unconditional :
    linearSystemDivisor (0 : JacobianChallenge.Div X) = constantsGerm X :=
  linearSystemDivisor_zero_eq_constantsGerm
    (JacobianChallenge.liouvilleOnCompactConnected_holds X)

/-- **`dim_ℂ L(0) = 1`** — unconditional canonical genus-0 Riemann-Roch
instance at the zero divisor on a compact connected complex 1-manifold. -/
theorem finrank_linearSystemDivisor_zero_eq_one_unconditional :
    Module.finrank ℂ
        (linearSystemDivisor (0 : JacobianChallenge.Div X)) = 1 :=
  finrank_linearSystemDivisor_zero_eq_one
    (JacobianChallenge.liouvilleOnCompactConnected_holds X)

end JacobianChallenge.MeromorphicFunctionField

end
