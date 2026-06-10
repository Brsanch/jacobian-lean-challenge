/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.WeierstrassPDescend
import JacobianChallenge.Divisor.EffectiveExtraction
import JacobianChallenge.Manifold.ComplexTorusConnected
import JacobianChallenge.Manifold.ResidueTheoremUnconditional

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Divisor shapes of the descended Weierstrass functions

The counting argument: for a descended `L`-periodic meromorphic function
whose only pole on the torus is at `0` with order exactly `-k`, the
residue theorem (`degree = 0`, unconditional in tree) and effectivity off
the pole force the principal divisor into the exact shape

  `div f = ∑ i : Fin k, [g i] - k·[0]`,

and any zero of the function places its image among the `g i`.

Instantiated for `℘ − c` (`k = 2`) and the chord function
`℘' − (a·℘ + b)` (`k = 3`). These shapes are the entire analytic input
of the chord-and-tangent proof of Abel's converse: the *locations* of the
unknown decomposition points are pinned downstream by `TLDivSumHypothesis`
(the forward Abel theorem), not by additional function theory.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open scoped PeriodPair
open Set

namespace JacobianChallenge

namespace ComplexTorus

/-! ## Order helpers -/

/-- An analytic function vanishing at a point has meromorphic order `≥ 1`
there. -/
lemma one_le_meromorphicOrderAt_of_eq_zero {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (h0 : f x = 0) :
    1 ≤ meromorphicOrderAt f x := by
  rw [hf.meromorphicOrderAt_eq]
  have hne : analyticOrderAt f x ≠ 0 := hf.analyticOrderAt_ne_zero.mpr h0
  cases h : analyticOrderAt f x with
  | top => simp
  | coe n =>
    rw [h] at hne
    have hn : 1 ≤ n := by
      by_contra hcon
      apply hne
      have : n = 0 := by omega
      rw [this]
      rfl
    rw [ENat.map_coe]
    exact_mod_cast hn

/-- `1 ≤ untop₀ o` from `1 ≤ o` and `o ≠ ⊤` in `WithTop ℤ`. -/
lemma one_le_untop₀_of_one_le {o : WithTop ℤ} (htop : o ≠ ⊤) (h1 : 1 ≤ o) :
    1 ≤ o.untop₀ := by
  have h1' : ((1 : ℤ) : WithTop ℤ) ≤ o := by
    simpa using h1
  have := WithTop.untop₀_le_untop₀ htop h1'
  simpa using this

variable (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- We fix the `DecidableEq (ℂ ⧸ L)` instance to `Classical.decEq` (the
repo-standard choice, cf. `Jacobian.lean`) so `Div.single` statements
elaborate. -/
noncomputable local instance : DecidableEq (ℂ ⧸ L) := Classical.decEq _

/-- A nonzero point of the torus has out-representative outside `L`. -/
lemma out_notMem_of_ne_zero {q : ℂ ⧸ L} (hq : q ≠ 0) : q.out ∉ L := by
  intro hmem
  apply hq
  have h1 : L.mkQ q.out = 0 := by
    rw [Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero L).mpr hmem
  rw [← mkQ_out L q, h1]

/-- The out-representative of `0 : ℂ ⧸ L` lies in `L`. -/
lemma out_zero_mem : ((0 : ℂ ⧸ L)).out ∈ L := by
  have h1 : L.mkQ ((0 : ℂ ⧸ L)).out = 0 := mkQ_out L 0
  rw [Submodule.mkQ_apply] at h1
  exact (Submodule.Quotient.mk_eq_zero L).mp h1

/-- `L.mkQ ũ ≠ 0` for `ũ ∉ L`. -/
lemma mkQ_ne_zero_of_notMem {ũ : ℂ} (hu : ũ ∉ L) : L.mkQ ũ ≠ 0 := by
  intro h
  apply hu
  rw [Submodule.mkQ_apply] at h
  exact (Submodule.Quotient.mk_eq_zero L).mp h

/-! ## The generic divisor-shape engine -/

/-- **Divisor shape of a descended function with a single pole of order
`k` at `0`.** If `F` is `L`-periodic, meromorphic, with order exactly
`-k` at every lattice point and analytic off the lattice, then the
principal divisor of its descent is `∑ i : Fin k, [g i] - k·[0]` with all
`g i ≠ 0`. -/
theorem exists_divisor_singles_descend
    (F : ℂ → ℂ) (hF : LPeriodic L F) (hFm : Meromorphic F)
    (h_top : ∀ z : ℂ, meromorphicOrderAt F z ≠ ⊤)
    (h_cont : ∀ z : ℂ, 0 ≤ meromorphicOrderAt F z → ContinuousAt F z)
    (k : ℕ)
    (h_lat : ∀ l₀ : ℂ, l₀ ∈ L → meromorphicOrderAt F l₀ = -(k : ℤ))
    (h_an : ∀ z : ℂ, z ∉ L → AnalyticAt ℂ F z) :
    ∃ g : Fin k → ℂ ⧸ L, (∀ i, g i ≠ 0) ∧
      principalDivisorMap (descend L F hF hFm h_top h_cont)
        = (∑ i, Div.single (g i)) - (k : ℤ) • Div.single 0 := by
  classical
  set D : Div (ℂ ⧸ L) :=
    principalDivisorMap (descend L F hF hFm h_top h_cont) with hD
  -- Value at 0: the pole.
  have h0 : (D : (ℂ ⧸ L) → ℤ) 0 = -(k : ℤ) := by
    rw [hD, principalDivisorMap_descend_apply]
    rw [h_lat _ (out_zero_mem L)]
    simp [WithTop.untop₀_neg]
  -- Effectivity off 0.
  have hpos : ∀ q : ℂ ⧸ L, q ≠ 0 → 0 ≤ (D : (ℂ ⧸ L) → ℤ) q := by
    intro q hq
    rw [hD, principalDivisorMap_descend_apply]
    rw [WithTop.untop₀_nonneg]
    exact (h_an q.out (out_notMem_of_ne_zero L hq)).meromorphicOrderAt_nonneg
  -- Degree 0: the residue theorem.
  have hdeg : D.degree = 0 := residue_theorem _
  exact Div.exists_singles_decomposition D 0 k h0 hdeg hpos

/-- **Zero placement.** If additionally `F ũ = 0` for some `ũ ∉ L`, then
`L.mkQ ũ` appears among the decomposition points. -/
theorem exists_index_eq_mkQ_of_zero
    (F : ℂ → ℂ) (hF : LPeriodic L F) (hFm : Meromorphic F)
    (h_top : ∀ z : ℂ, meromorphicOrderAt F z ≠ ⊤)
    (h_cont : ∀ z : ℂ, 0 ≤ meromorphicOrderAt F z → ContinuousAt F z)
    {k : ℕ} {g : Fin k → ℂ ⧸ L}
    (hdecomp : principalDivisorMap (descend L F hF hFm h_top h_cont)
        = (∑ i, Div.single (g i)) - (k : ℤ) • Div.single 0)
    {ũ : ℂ} (hu : ũ ∉ L)
    (h_an : AnalyticAt ℂ F ũ) (hzero : F ũ = 0) :
    ∃ i, g i = L.mkQ ũ := by
  apply Div.exists_index_of_one_le_apply hdecomp (mkQ_ne_zero_of_notMem L hu)
  rw [principalDivisorMap_descend_apply_mkQ]
  exact one_le_untop₀_of_one_le (h_top ũ)
    (one_le_meromorphicOrderAt_of_eq_zero h_an hzero)

/-! ## Instantiation: `℘ − c` -/

/-- **Divisor shape of the descended `℘ − c`**: two zeros against the
double pole at `0`. -/
theorem exists_divisor_shape_pSubC (c : ℂ) :
    ∃ g : Fin 2 → ℂ ⧸ L, (∀ i, g i ≠ 0) ∧
      principalDivisorMap (pSubCDescend L c)
        = (∑ i, Div.single (g i)) - (2 : ℤ) • Div.single 0 := by
  have h := exists_divisor_singles_descend L
    (pSubC (periodPairOfL L) c)
    (lperiodic_pSubC L c)
    (meromorphic_pSubC (periodPairOfL L) c)
    (meromorphicOrderAt_pSubC_ne_top (periodPairOfL L) c)
    (continuousAt_pSubC_of_nonneg_order (periodPairOfL L) c)
    2
    (fun l₀ hl₀ => by
      rw [meromorphicOrderAt_pSubC_lattice (periodPairOfL L) c
        (mem_periodPairOfL_lattice L hl₀)]
      norm_num)
    (fun z hz => analyticAt_pSubC (periodPairOfL L) c
      (fun hmem => hz (by rwa [periodPairOfL_lattice] at hmem)))
  simpa using h

/-- **Zero placement for `℘ − ℘(ũ)`**: the point `L.mkQ ũ` appears among
the two decomposition points. -/
theorem exists_index_eq_mkQ_pSubC {ũ : ℂ} (hu : ũ ∉ L)
    {g : Fin 2 → ℂ ⧸ L}
    (hdecomp : principalDivisorMap (pSubCDescend L (℘[periodPairOfL L] ũ))
        = (∑ i, Div.single (g i)) - (2 : ℤ) • Div.single 0) :
    ∃ i, g i = L.mkQ ũ := by
  have hu' : ũ ∉ (periodPairOfL L).lattice := by
    rw [periodPairOfL_lattice]; exact hu
  exact exists_index_eq_mkQ_of_zero L _ _ _ _ _ (by simpa using hdecomp) hu
    (analyticAt_pSubC (periodPairOfL L) _ hu')
    (by simp [pSubC_apply])

/-! ## Instantiation: the chord function -/

/-- **Divisor shape of the descended chord function**: three zeros against
the triple pole at `0`. -/
theorem exists_divisor_shape_chord (a b : ℂ) :
    ∃ g : Fin 3 → ℂ ⧸ L, (∀ i, g i ≠ 0) ∧
      principalDivisorMap (chordDescend L a b)
        = (∑ i, Div.single (g i)) - (3 : ℤ) • Div.single 0 := by
  have h := exists_divisor_singles_descend L
    (chordFun (periodPairOfL L) a b)
    (lperiodic_chordFun L a b)
    (meromorphic_chordFun (periodPairOfL L) a b)
    (meromorphicOrderAt_chordFun_ne_top (periodPairOfL L) a b)
    (continuousAt_chordFun_of_nonneg_order (periodPairOfL L) a b)
    3
    (fun l₀ hl₀ => by
      rw [meromorphicOrderAt_chordFun_lattice (periodPairOfL L) a b
        (mem_periodPairOfL_lattice L hl₀)]
      norm_num)
    (fun z hz => analyticAt_chordFun (periodPairOfL L) a b
      (fun hmem => hz (by rwa [periodPairOfL_lattice] at hmem)))
  simpa using h

/-- **Zero placement for the chord function**: any off-lattice zero of
`℘' − (a·℘ + b)` appears among the three decomposition points. -/
theorem exists_index_eq_mkQ_chord (a b : ℂ) {ũ : ℂ} (hu : ũ ∉ L)
    (hzero : ℘'[periodPairOfL L] ũ = a * ℘[periodPairOfL L] ũ + b)
    {g : Fin 3 → ℂ ⧸ L}
    (hdecomp : principalDivisorMap (chordDescend L a b)
        = (∑ i, Div.single (g i)) - (3 : ℤ) • Div.single 0) :
    ∃ i, g i = L.mkQ ũ := by
  have hu' : ũ ∉ (periodPairOfL L).lattice := by
    rw [periodPairOfL_lattice]; exact hu
  exact exists_index_eq_mkQ_of_zero L _ _ _ _ _ (by simpa using hdecomp) hu
    (analyticAt_chordFun (periodPairOfL L) a b hu')
    (by rw [chordFun_apply, hzero]; ring)

end ComplexTorus

end JacobianChallenge

end
