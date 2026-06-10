/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusDescendPeriodic
import JacobianChallenge.Manifold.GenericGenusPeriodLatticeInputsComplexTorus
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Weierstrass `℘`-family functions descended to the complex torus

Bridges the repo's lattice presentation (`L : Submodule ℤ ℂ` with
`[DiscreteTopology L] [IsZLattice ℝ L]`) to mathlib's `PeriodPair`
(`Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`) and
descends the two function families that the chord-and-tangent proof of
Abel's converse needs:

* `pSubC P c = ℘ − c` — pole of order exactly 2 at lattice points;
* `chordFun P a b = ℘' − (a·℘ + b)` — pole of order exactly 3 at lattice
  points.

Both are `L`-periodic meromorphic functions with no identically-zero germ
(non-⊤ order propagates from the pole over the connected plane), hence
descend to `MeromorphicNonzero (ℂ ⧸ L)` via
`ComplexTorusDescendPeriodic.lean`.

New analytic content over mathlib: the pole order of `℘'` at lattice
points is exactly `-3` (`meromorphicOrderAt_derivWeierstrassP`), proven by
the same `derivWeierstrassPExcept` decomposition mathlib uses for `℘`
(`order_weierstrassP`).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open scoped PeriodPair
open Set

namespace JacobianChallenge

namespace ComplexTorus

/-! ## The pole order of `℘'` at lattice points -/

/-- **The pole order of `℘'` at a lattice point is exactly `-3`.**
Mathlib (at this pin) provides `order_weierstrassP : order ℘ = -2`; this is
the `℘'` analog, by the same `derivWeierstrassPExcept` decomposition
`℘'[P - l₀] z = ℘'[P] z + 2 / (z - l₀)^3`. -/
lemma meromorphicOrderAt_derivWeierstrassP (P : PeriodPair) (l₀ : ℂ)
    (h : l₀ ∈ P.lattice) :
    meromorphicOrderAt ℘'[P] l₀ = -3 := by
  trans ((-3 : ℤ) : WithTop ℤ)
  · rw [meromorphicOrderAt_eq_int_iff (P.meromorphic_derivWeierstrassP l₀)]
    refine ⟨fun z => (z - l₀) ^ 3 * ℘'[P - l₀] z - 2, ?_, ?_, ?_⟩
    · have hopen : IsOpen ((P.lattice : Set ℂ) \ {l₀})ᶜ :=
        P.isOpen_compl_lattice_diff
      have hmem : l₀ ∈ ((P.lattice : Set ℂ) \ {l₀})ᶜ := by simp
      have hE : AnalyticAt ℂ ℘'[P - l₀] l₀ :=
        ((P.differentiableOn_derivWeierstrassPExcept l₀).analyticOnNhd hopen)
          l₀ hmem
      fun_prop
    · simp
    · filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ l₀)
      have hz0 : z - l₀ ≠ 0 := sub_ne_zero.mpr hz
      have hdef : ℘'[P - l₀] z = ℘'[P] z + 2 / (z - l₀) ^ 3 :=
        P.derivWeierstrassPExcept_def ⟨l₀, h⟩ z
      have hz3 : (z - l₀) ^ 3 ≠ 0 := pow_ne_zero _ hz0
      show ℘'[P] z = (z - l₀) ^ (-3 : ℤ) • ((z - l₀) ^ 3 * ℘'[P - l₀] z - 2)
      rw [hdef, smul_eq_mul, zpow_neg, ← Nat.cast_ofNat (n := 3),
        zpow_natCast]
      field_simp
      ring
  · norm_num

/-! ## The `PeriodPair` of a repo lattice -/

variable (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- **The mathlib `PeriodPair` attached to a repo lattice `L`**, built from
the explicit ℤ-basis `basisFin2OfL L`. -/
noncomputable def periodPairOfL : PeriodPair where
  ω₁ := lam₁_complexTorus L
  ω₂ := lam₂_complexTorus L
  indep := basisFin2OfL_realLinearIndependent L

@[simp] lemma periodPairOfL_omega₁ : (periodPairOfL L).ω₁ = lam₁_complexTorus L := rfl

@[simp] lemma periodPairOfL_omega₂ : (periodPairOfL L).ω₂ = lam₂_complexTorus L := rfl

/-- **The `PeriodPair` lattice recovers `L`.** -/
lemma periodPairOfL_lattice : (periodPairOfL L).lattice = L := by
  apply le_antisymm
  · -- `span ℤ {ω₁, ω₂} ≤ L`: both generators lie in `L`.
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with hx | hx
    · rw [hx]
      exact lam₁_complexTorus_mem L
    · rw [Set.mem_singleton_iff.mp hx]
      exact lam₂_complexTorus_mem L
  · -- `L ≤ span ℤ {ω₁, ω₂}`: by the basis decomposition.
    intro z hz
    obtain ⟨m₁, m₂, hm⟩ := basisFin2OfL_isZBasisOfL (L := L) z hz
    rw [hm]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_insert _ _))
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))

/-- Transport a lattice element of `L` into `(periodPairOfL L).lattice`. -/
lemma mem_periodPairOfL_lattice {l : ℂ} (hl : l ∈ L) :
    l ∈ (periodPairOfL L).lattice := by
  rw [periodPairOfL_lattice]; exact hl

/-! ## Periodicity of the `℘`-family w.r.t. `L` -/

/-- `℘` is `L`-periodic. -/
lemma lperiodic_weierstrassP : LPeriodic L ℘[periodPairOfL L] := by
  intro l hl z
  exact (periodPairOfL L).weierstrassP_add_coe z
    ⟨l, mem_periodPairOfL_lattice L hl⟩

/-- `℘'` is `L`-periodic. -/
lemma lperiodic_derivWeierstrassP : LPeriodic L ℘'[periodPairOfL L] := by
  intro l hl z
  exact (periodPairOfL L).derivWeierstrassP_add_coe z
    ⟨l, mem_periodPairOfL_lattice L hl⟩

/-! ## The two function families -/

/-- The function `℘ − c` on `ℂ`. -/
def pSubC (P : PeriodPair) (c : ℂ) : ℂ → ℂ :=
  fun z => ℘[P] z - c

/-- The **chord function** `℘' − (a·℘ + b)` on `ℂ`. For suitable `(a, b)`
this is the line through two points of the cubic; its descended divisor
implements the group law on the torus. -/
def chordFun (P : PeriodPair) (a b : ℂ) : ℂ → ℂ :=
  fun z => ℘'[P] z - (a * ℘[P] z + b)

lemma pSubC_apply (P : PeriodPair) (c z : ℂ) :
    pSubC P c z = ℘[P] z - c := rfl

lemma chordFun_apply (P : PeriodPair) (a b z : ℂ) :
    chordFun P a b z = ℘'[P] z - (a * ℘[P] z + b) := rfl

/-- `℘ − c` is `L`-periodic. -/
lemma lperiodic_pSubC (c : ℂ) : LPeriodic L (pSubC (periodPairOfL L) c) := by
  intro l hl z
  show ℘[periodPairOfL L] (z + l) - c = ℘[periodPairOfL L] z - c
  rw [lperiodic_weierstrassP L l hl z]

/-- The chord function is `L`-periodic. -/
lemma lperiodic_chordFun (a b : ℂ) :
    LPeriodic L (chordFun (periodPairOfL L) a b) := by
  intro l hl z
  show ℘'[periodPairOfL L] (z + l) - (a * ℘[periodPairOfL L] (z + l) + b)
    = ℘'[periodPairOfL L] z - (a * ℘[periodPairOfL L] z + b)
  rw [lperiodic_weierstrassP L l hl z, lperiodic_derivWeierstrassP L l hl z]

/-- `℘ − c` is meromorphic on `ℂ`. -/
lemma meromorphic_pSubC (P : PeriodPair) (c : ℂ) : Meromorphic (pSubC P c) := by
  intro x
  unfold pSubC
  fun_prop

/-- The chord function is meromorphic on `ℂ`. -/
lemma meromorphic_chordFun (P : PeriodPair) (a b : ℂ) :
    Meromorphic (chordFun P a b) := by
  intro x
  unfold chordFun
  fun_prop

/-! ## Analyticity and order off the lattice -/

/-- `℘ − c` is analytic off the lattice. -/
lemma analyticAt_pSubC (P : PeriodPair) (c : ℂ) {z : ℂ}
    (hz : z ∉ P.lattice) : AnalyticAt ℂ (pSubC P c) z := by
  have h℘ : AnalyticAt ℂ ℘[P] z := P.analyticOnNhd_weierstrassP z hz
  unfold pSubC
  fun_prop

/-- `℘'` is analytic off the lattice. -/
lemma analyticAt_derivWeierstrassP (P : PeriodPair) {z : ℂ}
    (hz : z ∉ P.lattice) : AnalyticAt ℂ ℘'[P] z := by
  have h : AnalyticOnNhd ℂ ℘'[P] (P.lattice : Set ℂ)ᶜ :=
    P.differentiableOn_derivWeierstrassP.analyticOnNhd
      P.isClosed_lattice.isOpen_compl
  exact h z hz

/-- The chord function is analytic off the lattice. -/
lemma analyticAt_chordFun (P : PeriodPair) (a b : ℂ) {z : ℂ}
    (hz : z ∉ P.lattice) : AnalyticAt ℂ (chordFun P a b) z := by
  have h℘ : AnalyticAt ℂ ℘[P] z := P.analyticOnNhd_weierstrassP z hz
  have h℘' : AnalyticAt ℂ ℘'[P] z := analyticAt_derivWeierstrassP P hz
  unfold chordFun
  fun_prop

/-! ## Order at lattice points -/

/-- **The order of `℘ − c` at a lattice point is exactly `-2`** (the
constant cannot interfere with the pole). -/
lemma meromorphicOrderAt_pSubC_lattice (P : PeriodPair) (c : ℂ) {l₀ : ℂ}
    (h : l₀ ∈ P.lattice) :
    meromorphicOrderAt (pSubC P c) l₀ = -2 := by
  classical
  have h℘ : meromorphicOrderAt ℘[P] l₀ = -2 := P.order_weierstrassP l₀ h
  have hfun : pSubC P c = ℘[P] + (fun _ : ℂ => -c) := by
    funext z
    simp [pSubC, sub_eq_add_neg]
  have hconst : meromorphicOrderAt (fun _ : ℂ => -c) l₀
      = if -c = 0 then ⊤ else 0 := meromorphicOrderAt_const l₀ (-c)
  have hlt : meromorphicOrderAt ℘[P] l₀
      < meromorphicOrderAt (fun _ : ℂ => -c) l₀ := by
    rw [h℘, hconst]
    by_cases hc : -c = 0
    · rw [if_pos hc]
      exact lt_of_le_of_ne le_top (by simp)
    · rw [if_neg hc]
      have h2 : ((-2 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ) := by
        rw [WithTop.coe_lt_coe]; norm_num
      simpa using h2
  have hadd := meromorphicOrderAt_add_eq_left_of_lt
    (analyticAt_const.meromorphicAt) hlt
  rw [hfun, hadd, h℘]

/-- **The order of the chord function at a lattice point is exactly `-3`**
(the `℘'` pole dominates the `a·℘ + b` part). -/
lemma meromorphicOrderAt_chordFun_lattice (P : PeriodPair) (a b : ℂ) {l₀ : ℂ}
    (h : l₀ ∈ P.lattice) :
    meromorphicOrderAt (chordFun P a b) l₀ = -3 := by
  classical
  have h℘' : meromorphicOrderAt ℘'[P] l₀ = -3 :=
    meromorphicOrderAt_derivWeierstrassP P l₀ h
  have h℘ : meromorphicOrderAt ℘[P] l₀ = -2 := P.order_weierstrassP l₀ h
  have hfun : chordFun P a b
      = ℘'[P] + (fun z : ℂ => -(a * ℘[P] z + b)) := by
    funext z
    simp [chordFun, sub_eq_add_neg]
  -- The subtracted part has order ≥ -2 > -3.
  have hrest_ge : (((-2 : ℤ) : WithTop ℤ))
      ≤ meromorphicOrderAt (fun z : ℂ => -(a * ℘[P] z + b)) l₀ := by
    have hsplit : (fun z : ℂ => -(a * ℘[P] z + b))
        = (fun z : ℂ => -a * ℘[P] z) + (fun _ : ℂ => -b) := by
      funext z
      show -(a * ℘[P] z + b) = -a * ℘[P] z + -b
      ring
    rw [hsplit]
    -- order of (-a)·℘ is -2 (a ≠ 0) or ⊤ (a = 0); order of const is 0 or ⊤.
    have h₁ : (((-2 : ℤ) : WithTop ℤ))
        ≤ meromorphicOrderAt (fun z : ℂ => -a * ℘[P] z) l₀ := by
      by_cases ha : a = 0
      · have : (fun z : ℂ => -a * ℘[P] z) = (fun _ : ℂ => (0 : ℂ)) := by
          funext z; rw [ha]; ring
        rw [this]
        rw [meromorphicOrderAt_const l₀ (0 : ℂ), if_pos rfl]
        exact le_top
      · have hsm : (fun z : ℂ => -a * ℘[P] z)
            = (fun _ : ℂ => -a) • ℘[P] := by
          funext z; simp [smul_eq_mul]
        rw [hsm, meromorphicOrderAt_smul_of_ne_zero analyticAt_const
          (by simpa using ha), h℘]
        exact le_refl _
      -- (closes h₁)
    have h₂ : (((-2 : ℤ) : WithTop ℤ))
        ≤ meromorphicOrderAt (fun _ : ℂ => -b) l₀ := by
      rw [meromorphicOrderAt_const l₀ (-b)]
      by_cases hb : -b = 0
      · rw [if_pos hb]; exact le_top
      · rw [if_neg hb]
        exact_mod_cast (by norm_num : (-2 : ℤ) ≤ 0)
    calc (((-2 : ℤ) : WithTop ℤ))
        = min (((-2 : ℤ) : WithTop ℤ)) (((-2 : ℤ) : WithTop ℤ)) := by
          rw [min_self]
      _ ≤ min (meromorphicOrderAt (fun z : ℂ => -a * ℘[P] z) l₀)
            (meromorphicOrderAt (fun _ : ℂ => -b) l₀) :=
          min_le_min h₁ h₂
      _ ≤ meromorphicOrderAt
            ((fun z : ℂ => -a * ℘[P] z) + (fun _ : ℂ => -b)) l₀ := by
          apply meromorphicOrderAt_add
          · exact (analyticAt_const.meromorphicAt).mul
              (P.meromorphic_weierstrassP l₀)
          · exact analyticAt_const.meromorphicAt
  have hlt : meromorphicOrderAt ℘'[P] l₀
      < meromorphicOrderAt (fun z : ℂ => -(a * ℘[P] z + b)) l₀ := by
    rw [h℘']
    calc (((-3 : ℤ) : WithTop ℤ)) < (((-2 : ℤ) : WithTop ℤ)) := by
          exact_mod_cast (by norm_num : (-3 : ℤ) < (-2 : ℤ))
      _ ≤ _ := hrest_ge
  have hmero_rest : MeromorphicAt (fun z : ℂ => -(a * ℘[P] z + b)) l₀ := by
    fun_prop
  have hadd := meromorphicOrderAt_add_eq_left_of_lt hmero_rest hlt
  rw [hfun, hadd, h℘']

/-! ## Non-⊤ order everywhere (connectedness propagation from the pole) -/

/-- `℘ − c` has no identically-zero germ anywhere. -/
lemma meromorphicOrderAt_pSubC_ne_top (P : PeriodPair) (c : ℂ) (z : ℂ) :
    meromorphicOrderAt (pSubC P c) z ≠ ⊤ := by
  have hmero : MeromorphicOn (pSubC P c) Set.univ :=
    fun x _ => meromorphic_pSubC P c x
  have h0 : meromorphicOrderAt (pSubC P c) 0 ≠ ⊤ := by
    rw [meromorphicOrderAt_pSubC_lattice P c P.lattice.zero_mem]
    exact ne_of_beq_false rfl
  exact hmero.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ 0) (Set.mem_univ z) h0

/-- The chord function has no identically-zero germ anywhere. -/
lemma meromorphicOrderAt_chordFun_ne_top (P : PeriodPair) (a b : ℂ) (z : ℂ) :
    meromorphicOrderAt (chordFun P a b) z ≠ ⊤ := by
  have hmero : MeromorphicOn (chordFun P a b) Set.univ :=
    fun x _ => meromorphic_chordFun P a b x
  have h0 : meromorphicOrderAt (chordFun P a b) 0 ≠ ⊤ := by
    rw [meromorphicOrderAt_chordFun_lattice P a b P.lattice.zero_mem]
    exact ne_of_beq_false rfl
  exact hmero.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ 0) (Set.mem_univ z) h0

/-! ## Continuity at regular points -/

/-- `℘ − c` is continuous at every point of non-negative order (such points
are off the lattice, where the function is analytic). -/
lemma continuousAt_pSubC_of_nonneg_order (P : PeriodPair) (c : ℂ) (z : ℂ)
    (hz : 0 ≤ meromorphicOrderAt (pSubC P c) z) :
    ContinuousAt (pSubC P c) z := by
  by_cases hzL : z ∈ P.lattice
  · exfalso
    rw [meromorphicOrderAt_pSubC_lattice P c hzL] at hz
    have h2 : ((0 : ℤ) : WithTop ℤ) ≤ (((-2 : ℤ) : WithTop ℤ)) := by
      simpa using hz
    rw [WithTop.coe_le_coe] at h2
    norm_num at h2
  · exact (analyticAt_pSubC P c hzL).continuousAt

/-- The chord function is continuous at every point of non-negative order. -/
lemma continuousAt_chordFun_of_nonneg_order (P : PeriodPair) (a b : ℂ) (z : ℂ)
    (hz : 0 ≤ meromorphicOrderAt (chordFun P a b) z) :
    ContinuousAt (chordFun P a b) z := by
  by_cases hzL : z ∈ P.lattice
  · exfalso
    rw [meromorphicOrderAt_chordFun_lattice P a b hzL] at hz
    have h3 : ((0 : ℤ) : WithTop ℤ) ≤ (((-3 : ℤ) : WithTop ℤ)) := by
      simpa using hz
    rw [WithTop.coe_le_coe] at h3
    norm_num at h3
  · exact (analyticAt_chordFun P a b hzL).continuousAt

/-! ## The descended `MeromorphicNonzero` functions on the torus -/

/-- **`℘ − c` descended to the torus** as a `MeromorphicNonzero (ℂ ⧸ L)`. -/
noncomputable def pSubCDescend (c : ℂ) : MeromorphicNonzero (ℂ ⧸ L) :=
  descend L (pSubC (periodPairOfL L) c)
    (lperiodic_pSubC L c)
    (meromorphic_pSubC (periodPairOfL L) c)
    (meromorphicOrderAt_pSubC_ne_top (periodPairOfL L) c)
    (continuousAt_pSubC_of_nonneg_order (periodPairOfL L) c)

/-- **The chord function descended to the torus** as a
`MeromorphicNonzero (ℂ ⧸ L)`. -/
noncomputable def chordDescend (a b : ℂ) : MeromorphicNonzero (ℂ ⧸ L) :=
  descend L (chordFun (periodPairOfL L) a b)
    (lperiodic_chordFun L a b)
    (meromorphic_chordFun (periodPairOfL L) a b)
    (meromorphicOrderAt_chordFun_ne_top (periodPairOfL L) a b)
    (continuousAt_chordFun_of_nonneg_order (periodPairOfL L) a b)

/-- The divisor of the descended `℘ − c` at a point `L.mkQ z` is the
order of `℘ − c` at `z`. -/
lemma principalDivisorMap_pSubCDescend_apply_mkQ (c : ℂ) (z : ℂ) :
    (principalDivisorMap (pSubCDescend L c) : (ℂ ⧸ L) → ℤ) (L.mkQ z)
      = (meromorphicOrderAt (pSubC (periodPairOfL L) c) z).untop₀ :=
  principalDivisorMap_descend_apply_mkQ L _ _ _ _ _ z

/-- The divisor of the descended chord function at a point `L.mkQ z` is the
order of the chord function at `z`. -/
lemma principalDivisorMap_chordDescend_apply_mkQ (a b : ℂ) (z : ℂ) :
    (principalDivisorMap (chordDescend L a b) : (ℂ ⧸ L) → ℤ) (L.mkQ z)
      = (meromorphicOrderAt (chordFun (periodPairOfL L) a b) z).untop₀ :=
  principalDivisorMap_descend_apply_mkQ L _ _ _ _ _ z

/-- The divisor of the descended `℘ − c` at any point `q` is the order of
`℘ − c` at `q.out`. -/
lemma principalDivisorMap_pSubCDescend_apply (c : ℂ) (q : ℂ ⧸ L) :
    (principalDivisorMap (pSubCDescend L c) : (ℂ ⧸ L) → ℤ) q
      = (meromorphicOrderAt (pSubC (periodPairOfL L) c) q.out).untop₀ :=
  principalDivisorMap_descend_apply L _ _ _ _ _ q

/-- The divisor of the descended chord function at any point `q` is the
order of the chord function at `q.out`. -/
lemma principalDivisorMap_chordDescend_apply (a b : ℂ) (q : ℂ ⧸ L) :
    (principalDivisorMap (chordDescend L a b) : (ℂ ⧸ L) → ℤ) q
      = (meromorphicOrderAt (chordFun (periodPairOfL L) a b) q.out).untop₀ :=
  principalDivisorMap_descend_apply L _ _ _ _ _ q

end ComplexTorus

end JacobianChallenge

end
