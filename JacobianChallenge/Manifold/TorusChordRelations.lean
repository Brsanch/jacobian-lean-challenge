/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.WeierstrassDivisorShapes
import JacobianChallenge.Divisor.PrincipalDivisorRange
import JacobianChallenge.Manifold.AbelHypothesisReductionComplexTorus

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # The chord relations: the torus group law inside `PrincDiv (ℂ ⧸ L)`

The classical chord-and-tangent argument, with `TLDivSumHypothesis`
(forward Abel) locating the third intersection point. Headline:

  `chord_relation : [u] + [v] − [u+v] − [0] ∈ PrincDiv (ℂ ⧸ L)`

for **all** `u v : ℂ ⧸ L`, conditional only on `TLDivSumHypothesis L`.

Ingredients, all conditional on `TLDivSumHypothesis L` alone:

* `eq_neg_of_weierstrassP_eq` — `℘` separates points up to sign: two
  distinct nonzero torus points with equal `℘`-values are negatives
  (from the divisor shape of `℘ − c`, whose two zeros sum to `0`).
* `single_add_single_neg_mem_princDiv` — `[x] + [−x] − 2[0] ∈ PrincDiv`
  (the divisor of the descended `℘ − ℘(x̃)`).
* `chord_relation_of_ne` — the generic chord: for `u, v, u+v ≠ 0` and
  `u ≠ v`, the line through `(℘(ũ), ℘'(ũ))` and `(℘(ṽ), ℘'(ṽ))` gives
  a chord function whose three zeros are `u, v, −(u+v)`.
* `tangent_relation` — the diagonal `u = v`, handled **without** any
  second-derivative/tangency analysis via an auxiliary point `t`
  (quarter-period combinations supply three candidates, of which at
  most two can collide with `{u, −u}`):
  `2[u] − [2u] − [0] = κ(u+t, u−t) + κ(u,t) + κ(u,−t) − ([t]+[−t]−2[0])`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open scoped PeriodPair
open Set

namespace JacobianChallenge

namespace ComplexTorus

/-! ## Finite-sum helpers -/

/-- Sum over `Fin 2` split at two distinct indices. -/
lemma fin_two_sum_decomp (i j : Fin 2) (hij : i ≠ j)
    {M : Type*} [AddCommMonoid M] (h : Fin 2 → M) :
    (∑ m, h m) = h i + h j := by
  have hcases : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
  rcases hcases with ⟨hi, hj⟩ | ⟨hi, hj⟩ <;> subst hi <;> subst hj
  · rw [Fin.sum_univ_two]
  · rw [Fin.sum_univ_two, add_comm]

/-- Sum over `Fin 3` split at two distinct indices plus the third. -/
lemma fin_three_sum_decomp (i j : Fin 3) (hij : i ≠ j) :
    ∃ k : Fin 3, k ≠ i ∧ k ≠ j ∧
      ∀ {M : Type*} [AddCommMonoid M] (h : Fin 3 → M),
        (∑ m, h m) = h i + h j + h k := by
  have hcases : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 0)
      ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 2 ∧ j = 1) := by omega
  rcases hcases with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
    | ⟨hi, hj⟩ | ⟨hi, hj⟩ <;> subst hi <;> subst hj
  · exact ⟨2, by omega, by omega, fun h => by rw [Fin.sum_univ_three]⟩
  · exact ⟨1, by omega, by omega, fun h => by rw [Fin.sum_univ_three]; abel⟩
  · exact ⟨2, by omega, by omega, fun h => by rw [Fin.sum_univ_three]; abel⟩
  · exact ⟨0, by omega, by omega, fun h => by rw [Fin.sum_univ_three]; abel⟩
  · exact ⟨1, by omega, by omega, fun h => by rw [Fin.sum_univ_three]; abel⟩
  · exact ⟨0, by omega, by omega, fun h => by rw [Fin.sum_univ_three]; abel⟩

variable (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- We fix the `DecidableEq (ℂ ⧸ L)` instance to `Classical.decEq` (the
repo-standard choice) so `Div.single` statements elaborate. -/
noncomputable local instance : DecidableEq (ℂ ⧸ L) := Classical.decEq _

/-! ## The `TLDivSumHypothesis` as an `evalSum` vanishing -/

/-- `TLDivSumHypothesis` says exactly that the evaluation sum of every
principal divisor vanishes. -/
lemma evalSum_principalDivisorMap_eq_zero (hTL : TLDivSumHypothesis L)
    (f : MeromorphicNonzero (ℂ ⧸ L)) :
    Div.evalSum (principalDivisorMap f) = 0 :=
  hTL f

/-- `evalSum` of a two-singles decomposition (numeral-literal form). -/
private lemma evalSum_decomp_two (g : Fin 2 → ℂ ⧸ L) :
    Div.evalSum ((∑ i, Div.single (g i)) - (2 : ℤ) • Div.single (0 : ℂ ⧸ L))
      = ∑ m, g m := by
  have h := Div.evalSum_singles_decomposition (k := 2) g (0 : ℂ ⧸ L)
  have hcast : ((2 : ℕ) : ℤ) = (2 : ℤ) := by norm_num
  rw [hcast] at h
  rw [h, sub_eq_self]
  exact smul_zero _

/-- `evalSum` of a three-singles decomposition (numeral-literal form). -/
private lemma evalSum_decomp_three (g : Fin 3 → ℂ ⧸ L) :
    Div.evalSum ((∑ i, Div.single (g i)) - (3 : ℤ) • Div.single (0 : ℂ ⧸ L))
      = ∑ m, g m := by
  have h := Div.evalSum_singles_decomposition (k := 3) g (0 : ℂ ⧸ L)
  have hcast : ((3 : ℕ) : ℤ) = (3 : ℤ) := by norm_num
  rw [hcast] at h
  rw [h, sub_eq_self]
  exact smul_zero _

/-! ## `℘` separates points up to sign -/

/-- **`℘` fibers are `{x, −x}`**: two distinct nonzero torus points with
equal `℘`-values at their out-representatives are negatives of each other.
-/
lemma eq_neg_of_weierstrassP_eq (hTL : TLDivSumHypothesis L)
    {x y : ℂ ⧸ L} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    (h℘ : ℘[periodPairOfL L] x.out = ℘[periodPairOfL L] y.out) :
    y = -x := by
  obtain ⟨g, hg0, hdecomp⟩ :=
    exists_divisor_shape_pSubC L (℘[periodPairOfL L] x.out)
  -- `x` is among the two zeros.
  have hx_pl : ∃ i, g i = x := by
    have h := exists_index_eq_mkQ_pSubC L
      (out_notMem_of_ne_zero L hx) hdecomp
    rwa [mkQ_out] at h
  -- `y` is among the two zeros (its `℘`-value matches).
  have hy_pl : ∃ i, g i = y := by
    have hy' : y.out ∉ (periodPairOfL L).lattice := by
      rw [periodPairOfL_lattice]
      exact out_notMem_of_ne_zero L hy
    have h := exists_index_eq_mkQ_of_zero L
      (pSubC (periodPairOfL L) (℘[periodPairOfL L] x.out))
      (lperiodic_pSubC L _)
      (meromorphic_pSubC (periodPairOfL L) _)
      (meromorphicOrderAt_pSubC_ne_top (periodPairOfL L) _)
      (continuousAt_pSubC_of_nonneg_order (periodPairOfL L) _)
      (k := 2) (g := g)
      (by simpa using hdecomp)
      (out_notMem_of_ne_zero L hy)
      (analyticAt_pSubC (periodPairOfL L) _ hy')
      (by rw [pSubC_apply, h℘, sub_self])
    rwa [mkQ_out] at h
  obtain ⟨i, hi⟩ := hx_pl
  obtain ⟨j, hj⟩ := hy_pl
  have hij : i ≠ j := by
    intro h
    exact hxy (by rw [← hi, h, hj])
  -- The two zeros sum to zero.
  have hes : Div.evalSum
      (principalDivisorMap (pSubCDescend L (℘[periodPairOfL L] x.out))) = 0 :=
    evalSum_principalDivisorMap_eq_zero L hTL _
  rw [hdecomp, evalSum_decomp_two L g,
    fin_two_sum_decomp i j hij g, hi, hj] at hes
  -- hes : x + y = 0
  exact eq_neg_of_add_eq_zero_right hes

/-! ## The pair relation `[x] + [−x] − 2[0] ∈ PrincDiv` -/

/-- **Pair relation**: for `x ≠ 0`,
`[x] + [−x] − 2[0]` is the divisor of the descended `℘ − ℘(x̃)`,
hence principal. -/
lemma single_add_single_neg_mem_princDiv (hTL : TLDivSumHypothesis L)
    {x : ℂ ⧸ L} (hx : x ≠ 0) :
    Div.single x + Div.single (-x) - (2 : ℤ) • Div.single 0
      ∈ PrincDiv (ℂ ⧸ L) := by
  obtain ⟨g, hg0, hdecomp⟩ :=
    exists_divisor_shape_pSubC L (℘[periodPairOfL L] x.out)
  have hx_pl : ∃ i, g i = x := by
    have h := exists_index_eq_mkQ_pSubC L
      (out_notMem_of_ne_zero L hx) hdecomp
    rwa [mkQ_out] at h
  obtain ⟨i, hi⟩ := hx_pl
  -- The two zeros sum to zero, so the other zero is `-x`.
  have hes : Div.evalSum
      (principalDivisorMap (pSubCDescend L (℘[periodPairOfL L] x.out))) = 0 :=
    evalSum_principalDivisorMap_eq_zero L hTL _
  rw [hdecomp, evalSum_decomp_two L g, Fin.sum_univ_two] at hes
  have hmem : principalDivisorMap (pSubCDescend L (℘[periodPairOfL L] x.out))
      ∈ PrincDiv (ℂ ⧸ L) := principalDivisorMap_mem_PrincDiv _
  rw [hdecomp, Fin.sum_univ_two] at hmem
  have hi01 : i = 0 ∨ i = 1 := by omega
  rcases hi01 with hi0 | hi1
  · -- g 0 = x, so g 1 = -x.
    subst hi0
    rw [hi] at hes hmem
    have hg1 : g 1 = -x := eq_neg_of_add_eq_zero_right hes
    rwa [hg1] at hmem
  · -- g 1 = x, so g 0 = -x.
    subst hi1
    rw [hi] at hes hmem
    have hg0' : g 0 = -x := eq_neg_of_add_eq_zero_left hes
    rw [hg0'] at hmem
    have hcomm : Div.single (-x) + Div.single x
        = Div.single x + Div.single (-x) := add_comm _ _
    rwa [hcomm] at hmem

/-! ## The generic chord relation -/

/-- **Generic chord relation**: for `u, v` distinct, nonzero, with
`u + v ≠ 0`, the relation `[u] + [v] − [u+v] − [0] ∈ PrincDiv` holds via
the chord through the two points of the cubic and the pair relation at
`u + v`. -/
lemma chord_relation_of_ne (hTL : TLDivSumHypothesis L)
    {u v : ℂ ⧸ L} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (hsum : u + v ≠ 0) :
    Div.single u + Div.single v - Div.single (u + v) - Div.single 0
      ∈ PrincDiv (ℂ ⧸ L) := by
  -- `℘` separates `u` and `v`.
  have hpne : ℘[periodPairOfL L] u.out ≠ ℘[periodPairOfL L] v.out := by
    intro he
    apply hsum
    rw [eq_neg_of_weierstrassP_eq L hTL hu hv huv he]
    exact add_neg_cancel u
  -- The line through the two cubic points.
  set p₁ := ℘[periodPairOfL L] u.out with hp₁
  set q₁ := ℘'[periodPairOfL L] u.out with hq₁
  set p₂ := ℘[periodPairOfL L] v.out with hp₂
  set q₂ := ℘'[periodPairOfL L] v.out with hq₂
  set a := (q₁ - q₂) / (p₁ - p₂) with ha
  set b := q₁ - a * p₁ with hb
  have hz_u : q₁ = a * p₁ + b := by rw [hb]; ring
  have hz_v : q₂ = a * p₂ + b := by
    rw [hb, ha]
    field_simp [sub_ne_zero.mpr hpne]
    ring
  obtain ⟨g, hg0, hdecomp⟩ := exists_divisor_shape_chord L a b
  -- Placements of `u` and `v` among the three zeros.
  have hu_pl : ∃ i, g i = u := by
    have h := exists_index_eq_mkQ_chord L a b
      (out_notMem_of_ne_zero L hu) hz_u hdecomp
    rwa [mkQ_out] at h
  have hv_pl : ∃ i, g i = v := by
    have h := exists_index_eq_mkQ_chord L a b
      (out_notMem_of_ne_zero L hv) hz_v hdecomp
    rwa [mkQ_out] at h
  obtain ⟨i, hi⟩ := hu_pl
  obtain ⟨j, hj⟩ := hv_pl
  have hij : i ≠ j := by
    intro h
    exact huv (by rw [← hi, h, hj])
  obtain ⟨k, _, _, hk_sum⟩ := fin_three_sum_decomp i j hij
  -- The three zeros sum to zero; the third is `-(u+v)`.
  have hes : Div.evalSum (principalDivisorMap (chordDescend L a b)) = 0 :=
    evalSum_principalDivisorMap_eq_zero L hTL _
  rw [hdecomp, evalSum_decomp_three L g, hk_sum g, hi, hj] at hes
  -- hes : u + v + g k = 0
  have hgk : g k = -(u + v) := by
    have h' : (u + v) + g k = 0 := by rw [← hes]
    exact eq_neg_of_add_eq_zero_right h'
  -- The chord divisor in closed form.
  have hA : principalDivisorMap (chordDescend L a b) ∈ PrincDiv (ℂ ⧸ L) :=
    principalDivisorMap_mem_PrincDiv _
  rw [hdecomp, hk_sum (fun m => Div.single (g m)), hi, hj, hgk] at hA
  -- The pair relation at `u + v`.
  have hB := single_add_single_neg_mem_princDiv L hTL hsum
  -- Assemble.
  have hkey : Div.single u + Div.single v - Div.single (u + v) - Div.single 0
      = (Div.single u + Div.single v + Div.single (-(u + v))
          - (3 : ℤ) • Div.single 0)
        - (Div.single (u + v) + Div.single (-(u + v))
          - (2 : ℤ) • Div.single 0) := by
    abel
  rw [hkey]
  exact sub_mem hA hB

/-! ## The auxiliary point -/

/-- Non-membership of a rational combination of the periods with a
non-integral coefficient. -/
private lemma qcomb_notMem (α β : ℚ) (h : ¬(α.den = 1 ∧ β.den = 1)) :
    (α : ℂ) * (periodPairOfL L).ω₁ + (β : ℂ) * (periodPairOfL L).ω₂ ∉ L := by
  intro hmem
  apply h
  apply (PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice (L := periodPairOfL L)).mp
  rw [periodPairOfL_lattice]
  exact hmem

/-- A rational with an integer multiple `n·q = 1`, `|n| ≥ 2`, is not an
integer. (Robust replacement for kernel-reducing `Rat.den` of literals.) -/
private lemma den_ne_one_of_mul_eq_one (n : ℤ) (q : ℚ) (hn : 2 ≤ n.natAbs)
    (h : (n : ℚ) * q = 1) : q.den ≠ 1 := by
  intro hden
  have hq : ((q.num : ℤ) : ℚ) = q := (Rat.den_eq_one_iff q).mp hden
  rw [← hq] at h
  have habs : n * q.num = 1 := by exact_mod_cast h
  have hdvd : n ∣ 1 := ⟨q.num, habs.symm⟩
  have hnat : n.natAbs ∣ 1 := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using this
  have := Nat.le_of_dvd one_pos hnat
  omega

/-- **Auxiliary-point existence**: for every `u` there is `t` with
`t ≠ 0`, `t + t ≠ 0`, `t ∉ {u, −u}`. Three quarter-period combinations
are pairwise distinct with nonzero doubles; at most two can lie in
`{u, −u}`. -/
lemma exists_aux_point (u : ℂ ⧸ L) :
    ∃ t : ℂ ⧸ L, t ≠ 0 ∧ t + t ≠ 0 ∧ t ≠ u ∧ t ≠ -u := by
  classical
  set om₁ := (periodPairOfL L).ω₁ with hom₁
  set om₂ := (periodPairOfL L).ω₂ with hom₂
  set c₁ : ℂ := ((1/4 : ℚ) : ℂ) * om₁ + ((0 : ℚ) : ℂ) * om₂ with hc₁
  set c₂ : ℂ := ((0 : ℚ) : ℂ) * om₁ + ((1/4 : ℚ) : ℂ) * om₂ with hc₂
  set c₃ : ℂ := ((1/4 : ℚ) : ℂ) * om₁ + ((1/4 : ℚ) : ℂ) * om₂ with hc₃
  have hden : (1/4 : ℚ).den ≠ 1 :=
    den_ne_one_of_mul_eq_one 4 _ (by norm_num) (by norm_num)
  have hden2 : (1/2 : ℚ).den ≠ 1 :=
    den_ne_one_of_mul_eq_one 2 _ (by norm_num) (by norm_num)
  have hdenneg : (-(1/4) : ℚ).den ≠ 1 :=
    den_ne_one_of_mul_eq_one (-4) _ (by norm_num) (by norm_num)
  -- Each candidate is a nonzero torus point.
  have hne₁ : L.mkQ c₁ ≠ 0 :=
    mkQ_ne_zero_of_notMem L (qcomb_notMem L _ _ (fun hc => hden hc.1))
  have hne₂ : L.mkQ c₂ ≠ 0 :=
    mkQ_ne_zero_of_notMem L (qcomb_notMem L _ _ (fun hc => hden hc.2))
  have hne₃ : L.mkQ c₃ ≠ 0 :=
    mkQ_ne_zero_of_notMem L (qcomb_notMem L _ _ (fun hc => hden hc.1))
  -- Each candidate has nonzero double.
  have hdouble : ∀ c : ℂ, c + c ∉ L → L.mkQ c + L.mkQ c ≠ 0 := by
    intro c hc h0
    apply hc
    have : L.mkQ (c + c) = 0 := by rw [map_add]; exact h0
    rw [Submodule.mkQ_apply] at this
    exact (Submodule.Quotient.mk_eq_zero L).mp this
  have hd₁ : L.mkQ c₁ + L.mkQ c₁ ≠ 0 := by
    apply hdouble
    have he : c₁ + c₁ = ((1/2 : ℚ) : ℂ) * om₁ + ((0 : ℚ) : ℂ) * om₂ := by
      rw [hc₁]; push_cast; ring
    rw [he]
    exact qcomb_notMem L _ _ (fun hc => hden2 hc.1)
  have hd₂ : L.mkQ c₂ + L.mkQ c₂ ≠ 0 := by
    apply hdouble
    have he : c₂ + c₂ = ((0 : ℚ) : ℂ) * om₁ + ((1/2 : ℚ) : ℂ) * om₂ := by
      rw [hc₂]; push_cast; ring
    rw [he]
    exact qcomb_notMem L _ _ (fun hc => hden2 hc.2)
  have hd₃ : L.mkQ c₃ + L.mkQ c₃ ≠ 0 := by
    apply hdouble
    have he : c₃ + c₃ = ((1/2 : ℚ) : ℂ) * om₁ + ((1/2 : ℚ) : ℂ) * om₂ := by
      rw [hc₃]; push_cast; ring
    rw [he]
    exact qcomb_notMem L _ _ (fun hc => hden2 hc.1)
  -- Pairwise distinct.
  have hne_of_diff : ∀ c c' : ℂ, c - c' ∉ L → L.mkQ c ≠ L.mkQ c' := by
    intro c c' hcc' h
    apply hcc'
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at h
    exact (Submodule.Quotient.eq L).mp h
  have h12 : L.mkQ c₁ ≠ L.mkQ c₂ := by
    apply hne_of_diff
    have he : c₁ - c₂ = ((1/4 : ℚ) : ℂ) * om₁ + ((-(1/4) : ℚ) : ℂ) * om₂ := by
      rw [hc₁, hc₂]; push_cast; ring
    rw [he]
    exact qcomb_notMem L _ _ (fun hc => hden hc.1)
  have h13 : L.mkQ c₁ ≠ L.mkQ c₃ := by
    apply hne_of_diff
    have he : c₁ - c₃ = ((0 : ℚ) : ℂ) * om₁ + ((-(1/4) : ℚ) : ℂ) * om₂ := by
      rw [hc₁, hc₃]; push_cast; ring
    rw [he]
    exact qcomb_notMem L _ _ (fun hc => hdenneg hc.2)
  have h23 : L.mkQ c₂ ≠ L.mkQ c₃ := by
    apply hne_of_diff
    have he : c₂ - c₃ = ((-(1/4) : ℚ) : ℂ) * om₁ + ((0 : ℚ) : ℂ) * om₂ := by
      rw [hc₂, hc₃]; push_cast; ring
    rw [he]
    exact qcomb_notMem L _ _ (fun hc => hdenneg hc.1)
  -- Pigeonhole: one of the three avoids `{u, -u}`.
  by_cases h1 : L.mkQ c₁ ≠ u ∧ L.mkQ c₁ ≠ -u
  · exact ⟨L.mkQ c₁, hne₁, hd₁, h1.1, h1.2⟩
  by_cases h2 : L.mkQ c₂ ≠ u ∧ L.mkQ c₂ ≠ -u
  · exact ⟨L.mkQ c₂, hne₂, hd₂, h2.1, h2.2⟩
  by_cases h3 : L.mkQ c₃ ≠ u ∧ L.mkQ c₃ ≠ -u
  · exact ⟨L.mkQ c₃, hne₃, hd₃, h3.1, h3.2⟩
  exfalso
  push Not at h1 h2 h3
  have h1' : L.mkQ c₁ = u ∨ L.mkQ c₁ = -u := by
    by_cases h : L.mkQ c₁ = u
    · exact Or.inl h
    · exact Or.inr (h1 h)
  have h2' : L.mkQ c₂ = u ∨ L.mkQ c₂ = -u := by
    by_cases h : L.mkQ c₂ = u
    · exact Or.inl h
    · exact Or.inr (h2 h)
  have h3' : L.mkQ c₃ = u ∨ L.mkQ c₃ = -u := by
    by_cases h : L.mkQ c₃ = u
    · exact Or.inl h
    · exact Or.inr (h3 h)
  rcases h1' with h1' | h1' <;> rcases h2' with h2' | h2' <;>
    rcases h3' with h3' | h3'
  · exact h12 (h1'.trans h2'.symm)
  · exact h12 (h1'.trans h2'.symm)
  · exact h13 (h1'.trans h3'.symm)
  · exact h23 (h2'.trans h3'.symm)
  · exact h23 (h2'.trans h3'.symm)
  · exact h13 (h1'.trans h3'.symm)
  · exact h12 (h1'.trans h2'.symm)
  · exact h12 (h1'.trans h2'.symm)

/-! ## The tangent relation via the auxiliary point -/

/-- **Tangent relation**: `2[u] − [2u] − [0] ∈ PrincDiv` for `u ≠ 0`,
`u + u ≠ 0`, with no tangency analysis: writing `2u = (u+t) + (u−t)` for
an auxiliary `t` reduces everything to generic chords and pair relations.
-/
lemma tangent_relation (hTL : TLDivSumHypothesis L)
    {u : ℂ ⧸ L} (hu : u ≠ 0) (h2u : u + u ≠ 0) :
    Div.single u + Div.single u - Div.single (u + u) - Div.single 0
      ∈ PrincDiv (ℂ ⧸ L) := by
  obtain ⟨t, ht0, ht2, htu, htnu⟩ := exists_aux_point L u
  -- Point conditions.
  have hut_ne : u + t ≠ 0 := by
    intro h
    exact htnu (eq_neg_of_add_eq_zero_right h)
  have hunt_ne : u + -t ≠ 0 := by
    intro h
    apply htu
    have hneg : -t = -u := eq_neg_of_add_eq_zero_right h
    exact neg_injective hneg
  have hsum_ne : (u + t) + (u + -t) ≠ 0 := by
    intro h
    apply h2u
    have hcollect : (u + t) + (u + -t) = u + u := by abel
    rw [← hcollect]
    exact h
  have hchord_ne : u + t ≠ u + -t := by
    intro h
    apply ht2
    have htt : t = -t := add_left_cancel h
    have hgoal : t + t = t + -t := by rw [← htt]
    rw [hgoal]
    exact add_neg_cancel t
  -- X = κ(u+t, u−t)
  have hX := chord_relation_of_ne L hTL hut_ne hunt_ne hchord_ne hsum_ne
  -- Y = κ(u, t)
  have hY := chord_relation_of_ne L hTL hu ht0
    (fun h => htu h.symm) hut_ne
  -- Z = κ(u, −t)
  have hZ := chord_relation_of_ne L hTL hu (neg_ne_zero.mpr ht0)
    (fun h => htnu (by rw [h, neg_neg])) hunt_ne
  -- W = pair relation at t
  have hW := single_add_single_neg_mem_princDiv L hTL ht0
  -- Assemble: target = X + Y + Z − W (after rewriting the two composite
  -- sums).
  have huu : (u + t) + (u + -t) = u + u := by abel
  rw [huu] at hX
  have hkey : Div.single u + Div.single u - Div.single (u + u) - Div.single 0
      = ((Div.single (u + t) + Div.single (u + -t)
            - Div.single (u + u) - Div.single 0)
          + (Div.single u + Div.single t
            - Div.single (u + t) - Div.single 0)
          + (Div.single u + Div.single (-t)
            - Div.single (u + -t) - Div.single 0))
        - (Div.single t + Div.single (-t) - (2 : ℤ) • Div.single 0) := by
    abel
  rw [hkey]
  exact sub_mem (add_mem (add_mem hX hY) hZ) hW

/-! ## The full chord relation -/

/-- **The chord relation**, all cases: for every `u v : ℂ ⧸ L`,
`[u] + [v] − [u+v] − [0] ∈ PrincDiv (ℂ ⧸ L)`, conditional only on
`TLDivSumHypothesis L`. This is exactly the statement that
`u ↦ [u] − [0]` descends to a group homomorphism
`(ℂ ⧸ L) → Div (ℂ ⧸ L) ⧸ PrincDiv`. -/
theorem chord_relation (hTL : TLDivSumHypothesis L) (u v : ℂ ⧸ L) :
    Div.single u + Div.single v - Div.single (u + v) - Div.single 0
      ∈ PrincDiv (ℂ ⧸ L) := by
  by_cases hu : u = 0
  · -- [0] + [v] − [v] − [0] = 0.
    have h : Div.single u + Div.single v - Div.single (u + v) - Div.single 0
        = 0 := by
      rw [hu, zero_add]
      abel
    rw [h]
    exact zero_mem _
  by_cases hv : v = 0
  · have h : Div.single u + Div.single v - Div.single (u + v) - Div.single 0
        = 0 := by
      rw [hv, add_zero]
      abel
    rw [h]
    exact zero_mem _
  by_cases hsum : u + v = 0
  · -- v = −u: the pair relation.
    have hv_eq : v = -u := eq_neg_of_add_eq_zero_right hsum
    have h : Div.single u + Div.single v - Div.single (u + v) - Div.single 0
        = Div.single u + Div.single (-u) - (2 : ℤ) • Div.single 0 := by
      rw [hsum, hv_eq]
      abel
    rw [h]
    exact single_add_single_neg_mem_princDiv L hTL hu
  by_cases huv : u = v
  · -- The tangent case.
    rw [huv] at hsum ⊢
    exact tangent_relation L hTL hv hsum
  · -- The generic chord.
    exact chord_relation_of_ne L hTL hu hv huv hsum

end ComplexTorus

end JacobianChallenge

end
