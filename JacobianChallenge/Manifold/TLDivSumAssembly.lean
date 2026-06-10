/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelHypothesisReductionComplexTorus
import JacobianChallenge.Manifold.TLAbelConverseFromTLDivSum
import JacobianChallenge.Manifold.LiftedFunRegularPoints
import JacobianChallenge.Manifold.MkQPreimageFinite
import JacobianChallenge.Manifold.GenericGenusPeriodLatticeInputsComplexTorus
import JacobianChallenge.Manifold.PeriodLatticeSymplecticBundleComplexTorus
import JacobianChallenge.Analysis.ParallelogramResidue
import JacobianChallenge.Analysis.ParallelogramRegularPosition
import JacobianChallenge.Analysis.ParallelogramInteriorTranslate
import JacobianChallenge.Analysis.PeriodSideWinding
import JacobianChallenge.Analysis.LatticeCrossNeZero
import JacobianChallenge.Analysis.AbelIntegrandDecomposition

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! # Abel's theorem on elliptic functions: `TLDivSumHypothesis L` holds

**The piece-5 assembly** (`HANDOFF_TLDIVSUM.md`): for every meromorphic
nonvanishing-germ function `f` on the complex torus `T_L = ℂ ⧸ L`,

  `∑ x ∈ supp(div f), ord_x(f) • x = 0` in `ℂ ⧸ L`.

Proof: lift `f` to the doubly periodic `F = f ∘ mkQ`, choose a
regular-position base point `a` (all lattice translates of the divisor
lifts have Cramer coordinates off `{0,1}`), and evaluate the Abel
integral `I(a) = ∮_{∂Π(a)} z·F′/F dz` twice:

* **residue side** — `abelIntegrand_decomposition` +
  `boundaryIntegral_eq_sum_winding` + the winding evaluator:
  `I(a) = ε·2πi·∑_{x interior} ord_x·x`;
* **pairing side** — `boundaryIntegral_mul_logDeriv_mem`:
  `I(a) = 2πi·(k₁ω₁ + k₂ω₂) ∈ 2πi·L`.

Cancelling `±2πi` puts `∑_{interior} ord·x̃` in `L`, so it dies in the
quotient; the interior translates form a complete set of
representatives of `supp(div f)` (existence + uniqueness of the
interior translate at a regular-position base point), so the quotient
sum is exactly `∑ ord_x(f) • x`.

**Consequence**: the full T_L C3 closure
(`nonempty_C3FullInputExtSymp_complexTorus`) now holds from ZERO named
hypotheses.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace JacobianChallenge

open ParallelogramWinding LogDerivPrincipalPart

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **Abel's theorem on elliptic functions**: the T_L divisor-sum
hypothesis holds unconditionally. -/
theorem tlDivSumHypothesis_holds : TLDivSumHypothesis L := by
  classical
  intro f
  -- ## Periods, orientation, lattice basis
  set w1 : ℂ := lam₁_complexTorus L with hw1_def
  set w2 : ℂ := lam₂_complexTorus L with hw2_def
  have hw1_mem : w1 ∈ L := by
    rw [hw1_def]
    exact lam₁_complexTorus_mem L
  have hw2_mem : w2 ∈ L := by
    rw [hw2_def]
    exact lam₂_complexTorus_mem L
  have hcross : latticeCross w1 w2 ≠ 0 := by
    rw [hw1_def, hw2_def]
    apply latticeCross_ne_zero_of_linearIndependent
    have h := basisFin2OfL_realLinearIndependent L
    rw [lam₁_complexTorus, lam₂_complexTorus]
    exact h
  have hbasis : ∀ z : ℂ, z ∈ L →
      ∃ m₁ m₂ : ℤ, z = (m₁ : ℂ) * w1 + (m₂ : ℂ) * w2 := by
    intro z hz
    obtain ⟨m₁, m₂, hm⟩ := basisFin2OfL_isZBasisOfL z hz
    refine ⟨m₁, m₂, ?_⟩
    rw [hw1_def, hw2_def, lam₁_complexTorus, lam₂_complexTorus, hm]
    simp [zsmul_eq_mul]
  -- ## The lift and its standing properties
  set F : ℂ → ℂ := liftedFun L f with hF_def
  have hper1 : ∀ z, F (z + w1) = F z := by
    intro z
    rw [hF_def]
    exact liftedFun_periodic L f hw1_mem z
  have hper2 : ∀ z, F (z + w2) = F z := by
    intro z
    rw [hF_def]
    exact liftedFun_periodic L f hw2_mem z
  have hmero_all : ∀ x : ℂ, MeromorphicAt F x := by
    intro x
    rw [hF_def]
    exact meromorphic_liftedFun L f x
  have hordcorr : ∀ x : ℂ, meromorphicOrderAt F x
      = mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun (L.mkQ x) := by
    intro x
    rw [hF_def]
    exact liftedOrderCorrespondence_holds L f x
  have hregF : ∀ z : ℂ,
      mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun (L.mkQ z) = 0 →
      AnalyticAt ℂ F z ∧ F z ≠ 0 := by
    intro z h0
    rw [hF_def]
    exact liftedFun_analyticAt_nonzero_of_order_zero L f h0
  -- ## Divisor bookkeeping
  set S : Finset (ℂ ⧸ L) := (principalDivisorMap f).supportFinset
    with hS_def
  have hdiv_val : ∀ q : ℂ ⧸ L,
      ((principalDivisorMap f : Div (ℂ ⧸ L)) : (ℂ ⧸ L) → ℤ) q
        = (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun q).untop₀ := fun q => rfl
  have hoff : ∀ q : ℂ ⧸ L, q ∉ S →
      mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun q = 0 := by
    intro q hq
    have hval : ((principalDivisorMap f : Div (ℂ ⧸ L)) : (ℂ ⧸ L) → ℤ) q
        = 0 := by
      by_contra hne
      apply hq
      rw [hS_def]
      exact Div.mem_supportFinset.mpr hne
    rw [hdiv_val] at hval
    rcases WithTop.untop₀_eq_zero.mp hval with h | h
    · exact h
    · exact absurd h (f.nonvanishing_germ q)
  -- ## Lattice translation kills `mkQ`
  have hmkQ_translate : ∀ (z : ℂ) (m₁ m₂ : ℤ),
      L.mkQ (z + (m₁ : ℂ) * w1 + (m₂ : ℂ) * w2) = L.mkQ z := by
    intro z m₁ m₂
    have h1 : L.mkQ ((m₁ : ℂ) * w1) = 0 := by
      rw [← zsmul_eq_mul, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem L m₁ hw1_mem
    have h2 : L.mkQ ((m₂ : ℂ) * w2) = 0 := by
      rw [← zsmul_eq_mul, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem L m₂ hw2_mem
    rw [map_add, map_add, h1, h2, add_zero, add_zero]
  -- ## Regular position
  set P : Finset ℂ := S.image Quotient.out with hP_def
  obtain ⟨a, ha⟩ := exists_regular_position w1 w2 hcross P
  -- Every divisor-lift point has coordinates off `{0,1}`.
  have hcoord_ne : ∀ z : ℂ, L.mkQ z ∈ S →
      coordS a w1 w2 z ≠ 0 ∧ coordS a w1 w2 z ≠ 1 ∧
      coordR a w1 w2 z ≠ 0 ∧ coordR a w1 w2 z ≠ 1 := by
    intro z hz
    obtain ⟨m₁, m₂, hm⟩ := hbasis ((L.mkQ z).out - z) (out_mkQ_sub_mem L z)
    have hz_eq : z = (L.mkQ z).out + ((-m₁ : ℤ) : ℂ) * w1
        + ((-m₂ : ℤ) : ℂ) * w2 := by
      push_cast
      linear_combination -hm
    have h4 := ha ((L.mkQ z).out)
      (by rw [hP_def]; exact Finset.mem_image_of_mem _ hz) (-m₁) (-m₂)
    rw [← hz_eq] at h4
    exact h4
  -- ## The exceptional set in the standard ball
  have hZfin : {z : ℂ | L.mkQ z ∈ S ∧
      z ∈ Metric.ball a (‖w1‖ + ‖w2‖ + 1)}.Finite :=
    finite_mkQ_preimage_inter_isBounded L S Metric.isBounded_ball
  set Z : Finset ℂ := hZfin.toFinset with hZ_def
  have hZ_mem : ∀ z : ℂ, z ∈ Z ↔ L.mkQ z ∈ S ∧
      z ∈ Metric.ball a (‖w1‖ + ‖w2‖ + 1) := by
    intro z
    rw [hZ_def, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  -- ## Orders along the lift
  set n : ℂ → ℤ := fun z =>
    (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun (L.mkQ z)).untop₀ with hn_def
  have hordZ : ∀ x ∈ Z, meromorphicOrderAt F x = n x := by
    intro x hx
    rw [hordcorr x]
    simp only [hn_def]
    exact (WithTop.coe_untop₀_of_ne_top
      (f.nonvanishing_germ (L.mkQ x))).symm
  have hmeroZ : ∀ x ∈ Z, MeromorphicAt F x := fun x _ => hmero_all x
  have hregdec : ∀ z ∈ Metric.ball a (‖w1‖ + ‖w2‖ + 1),
      z ∉ (Z : Set ℂ) → AnalyticAt ℂ F z ∧ F z ≠ 0 := by
    intro z hz hzZ
    apply hregF
    apply hoff
    intro hmem
    exact hzZ (Finset.mem_coe.mpr ((hZ_mem z).mpr ⟨hmem, hz⟩))
  -- ## The decomposition
  obtain ⟨H, hHdiff, hHdec⟩ := abelIntegrand_decomposition hmeroZ hordZ
    hregdec
  -- ## Contour geometry
  have hmem₀ := side₀_mem_ball a w1 w2
  have hmem₁ := side₁_mem_ball a w1 w2
  have hmem₂ := side₂_mem_ball a w1 w2
  have hmem₃ := side₃_mem_ball a w1 w2
  have havoid₀ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ Z, side₀ a w1 w2 t ≠ x := by
    intro t ht x hx
    have hcn := hcoord_ne x ((hZ_mem x).mp hx).1
    exact side₀_ne_of_coordR_ne_zero a w1 w2 hcross hcn.2.2.1 t ht
  have havoid₁ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ Z, side₁ a w1 w2 t ≠ x := by
    intro t ht x hx
    have hcn := hcoord_ne x ((hZ_mem x).mp hx).1
    exact side₁_ne_of_coordS_ne_one a w1 w2 hcross hcn.2.1 t ht
  have havoid₂ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ Z, side₂ a w1 w2 t ≠ x := by
    intro t ht x hx
    have hcn := hcoord_ne x ((hZ_mem x).mp hx).1
    exact side₂_ne_of_coordR_ne_one a w1 w2 hcross hcn.2.2.2 t ht
  have havoid₃ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ Z, side₃ a w1 w2 t ≠ x := by
    intro t ht x hx
    have hcn := hcoord_ne x ((hZ_mem x).mp hx).1
    exact side₃_ne_of_coordS_ne_zero a w1 w2 hcross hcn.1 t ht
  -- ## Residue-side evaluation
  have hres := boundaryIntegral_eq_sum_winding a w1 w2
    (f := fun z => z * (deriv F z / F z)) (H := H)
    (coeff := fun x => (n x : ℂ) * x) hHdiff
    (fun z hz hz2 => hHdec z hz hz2)
    (fun t ht => hmem₀ t ht) (fun t ht => hmem₁ t ht)
    (fun t ht => hmem₂ t ht) (fun t ht => hmem₃ t ht)
    havoid₀ havoid₁ havoid₂ havoid₃
  set Zin : Finset ℂ := Z.filter (fun x =>
    coordS a w1 w2 x ∈ Ioo (0 : ℝ) 1 ∧
    coordR a w1 w2 x ∈ Ioo (0 : ℝ) 1) with hZin_def
  have hres2 : boundaryIntegral a w1 w2
      (fun z => z * (deriv F z / F z))
      = ((if 0 < latticeCross w1 w2 then (1 : ℂ) else -1)
          * (2 * Real.pi * Complex.I)) * ∑ x ∈ Zin, (n x : ℂ) * x := by
    calc boundaryIntegral a w1 w2 (fun z => z * (deriv F z / F z))
        = ∑ x ∈ Z, ((n x : ℂ) * x)
            * boundaryIntegral a w1 w2 (fun w => (w - x)⁻¹) := hres
      _ = ∑ x ∈ Z, (if coordS a w1 w2 x ∈ Ioo (0 : ℝ) 1
            ∧ coordR a w1 w2 x ∈ Ioo (0 : ℝ) 1
          then ((n x : ℂ) * x)
            * ((if 0 < latticeCross w1 w2 then (1 : ℂ) else -1)
              * (2 * Real.pi * Complex.I))
          else 0) := by
          refine Finset.sum_congr rfl fun x hx => ?_
          have hcn := hcoord_ne x ((hZ_mem x).mp hx).1
          rw [boundaryIntegral_inv_sub_of_coord_ne a w1 w2 hcross
            hcn.1 hcn.2.1 hcn.2.2.1 hcn.2.2.2, mul_ite, mul_zero]
      _ = ∑ x ∈ Zin, ((n x : ℂ) * x)
            * ((if 0 < latticeCross w1 w2 then (1 : ℂ) else -1)
              * (2 * Real.pi * Complex.I)) := by
          rw [hZin_def]
          exact (Finset.sum_filter _ _).symm
      _ = ((if 0 < latticeCross w1 w2 then (1 : ℂ) else -1)
            * (2 * Real.pi * Complex.I)) * ∑ x ∈ Zin, (n x : ℂ) * x := by
          rw [← Finset.sum_mul]
          ring
  -- ## Pairing-side evaluation
  have hside_reg₁ : ∀ t ∈ Icc (0 : ℝ) 1,
      AnalyticAt ℂ F (a + t • w1) ∧ F (a + t • w1) ≠ 0 := by
    intro t ht
    have hmem : a + t • w1 ∈ Metric.ball a (‖w1‖ + ‖w2‖ + 1) := by
      have h := hmem₀ t ht
      rwa [side₀] at h
    apply hregdec _ hmem
    intro hmem'
    apply havoid₀ t ht _ (Finset.mem_coe.mp hmem')
    rw [side₀]
  have hside_reg₂ : ∀ t ∈ Icc (0 : ℝ) 1,
      AnalyticAt ℂ F (a + t • w2) ∧ F (a + t • w2) ≠ 0 := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := Set.mem_Icc.mp ht
    have ht' : (1 - t) ∈ Icc (0 : ℝ) 1 :=
      Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    have hpt : side₃ a w1 w2 (1 - t) = a + t • w2 := by
      rw [side₃]
      module
    have hmem : a + t • w2 ∈ Metric.ball a (‖w1‖ + ‖w2‖ + 1) := by
      have h := hmem₃ (1 - t) ht'
      rwa [hpt] at h
    apply hregdec _ hmem
    intro hmem'
    apply havoid₃ (1 - t) ht' _ (Finset.mem_coe.mp hmem')
    rw [hpt]
  obtain ⟨k₁, k₂, hk⟩ := boundaryIntegral_mul_logDeriv_mem a w1 w2
    hper1 hper2
    (fun t ht => (hside_reg₁ t ht).1) (fun t ht => (hside_reg₁ t ht).2)
    (fun t ht => (hside_reg₂ t ht).1) (fun t ht => (hside_reg₂ t ht).2)
  -- ## Equate and cancel `±2πi`
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hcomboL : (k₁ : ℂ) * w1 + (k₂ : ℂ) * w2 ∈ L := by
    apply Submodule.add_mem
    · have h := Submodule.smul_mem L k₁ hw1_mem
      rwa [zsmul_eq_mul] at h
    · have h := Submodule.smul_mem L k₂ hw2_mem
      rwa [zsmul_eq_mul] at h
  have hEq : ((if 0 < latticeCross w1 w2 then (1 : ℂ) else -1)
        * (2 * Real.pi * Complex.I)) * ∑ x ∈ Zin, (n x : ℂ) * x
      = (2 * Real.pi * Complex.I)
        * ((k₁ : ℂ) * w1 + (k₂ : ℂ) * w2) := by
    rw [← hres2]
    exact hk
  have hsum_mem : ∑ x ∈ Zin, (n x : ℂ) * x ∈ L := by
    by_cases hpos : 0 < latticeCross w1 w2
    · rw [if_pos hpos, one_mul] at hEq
      rw [mul_left_cancel₀ h2pi hEq]
      exact hcomboL
    · rw [if_neg hpos] at hEq
      have hEq2 : (2 * Real.pi * Complex.I)
          * (∑ x ∈ Zin, (n x : ℂ) * x)
          = (2 * Real.pi * Complex.I)
            * (-((k₁ : ℂ) * w1 + (k₂ : ℂ) * w2)) := by
        linear_combination -hEq
      rw [mul_left_cancel₀ h2pi hEq2]
      exact Submodule.neg_mem L hcomboL
  -- ## Push to the quotient
  have hq0 : L.mkQ (∑ x ∈ Zin, (n x : ℂ) * x) = 0 := by
    rw [Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero L).mpr hsum_mem
  have hqsum : L.mkQ (∑ x ∈ Zin, (n x : ℂ) * x)
      = ∑ x ∈ Zin, n x • L.mkQ x := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← zsmul_eq_mul, map_zsmul]
  -- ## The interior translates are a complete set of representatives
  have hkey : ∑ x ∈ Zin, n x • L.mkQ x
      = ∑ q ∈ S,
          ((principalDivisorMap f : Div (ℂ ⧸ L)) : (ℂ ⧸ L) → ℤ) q • q := by
    refine Finset.sum_bij (i := fun x _ => L.mkQ x) ?_ ?_ ?_ ?_
    · -- maps into the support
      intro x hx
      rw [hZin_def] at hx
      have := ((hZ_mem x).mp (Finset.mem_filter.mp hx).1).1
      rw [hS_def] at this
      exact this
    · -- injective: uniqueness of the interior translate
      intro x₁ hx₁ x₂ hx₂ hmkQeq
      rw [hZin_def] at hx₁ hx₂
      have hmkQeq' : L.mkQ x₁ = L.mkQ x₂ := hmkQeq
      have hd : x₂ - x₁ ∈ L := by
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at hmkQeq'
        exact (Submodule.Quotient.eq L).mp hmkQeq'.symm
      obtain ⟨m₁, m₂, hm⟩ := hbasis _ hd
      have hx₂eq : x₂ = x₁ + (m₁ : ℂ) * w1 + (m₂ : ℂ) * w2 := by
        linear_combination hm
      have hint₁ := (Finset.mem_filter.mp hx₁).2
      have hint₂ := (Finset.mem_filter.mp hx₂).2
      have heq := eq_of_interior_translate a w1 w2 hcross m₁ m₂
        hint₁.1 hint₁.2
        (by rw [← hx₂eq]; exact hint₂.1)
        (by rw [← hx₂eq]; exact hint₂.2)
      rw [hx₂eq, heq]
    · -- surjective: existence of the interior translate
      intro q hq
      have hpcoord : ∀ m₁ m₂ : ℤ,
          coordS a w1 w2 (q.out + (m₁ : ℂ) * w1 + (m₂ : ℂ) * w2) ≠ 0 ∧
          coordS a w1 w2 (q.out + (m₁ : ℂ) * w1 + (m₂ : ℂ) * w2) ≠ 1 ∧
          coordR a w1 w2 (q.out + (m₁ : ℂ) * w1 + (m₂ : ℂ) * w2) ≠ 0 ∧
          coordR a w1 w2 (q.out + (m₁ : ℂ) * w1 + (m₂ : ℂ) * w2) ≠ 1 := by
        intro m₁ m₂
        apply hcoord_ne
        rw [hmkQ_translate, mkQ_out]
        rw [hS_def] at hq
        exact hq
      obtain ⟨m₁, m₂, hint_s, hint_r⟩ :=
        exists_interior_translate a w1 w2 hcross hpcoord
      have hmkw : L.mkQ (q.out + (m₁ : ℂ) * w1 + (m₂ : ℂ) * w2) = q := by
        rw [hmkQ_translate, mkQ_out]
      have hwZ : (q.out + (m₁ : ℂ) * w1 + (m₂ : ℂ) * w2) ∈ Z := by
        apply (hZ_mem _).mpr
        constructor
        · rw [hmkw]
          rw [hS_def] at hq
          exact hq
        · exact mem_ball_of_coord_interior a w1 w2 hcross hint_s hint_r
      refine ⟨q.out + (m₁ : ℂ) * w1 + (m₂ : ℂ) * w2, ?_, hmkw⟩
      rw [hZin_def]
      exact Finset.mem_filter.mpr ⟨hwZ, hint_s, hint_r⟩
    · -- values: the order of the lift is the divisor value
      intro x hx
      congr 1
  -- ## Conclusion
  rw [hS_def] at hkey
  calc ∑ x ∈ (principalDivisorMap f).supportFinset,
        ((principalDivisorMap f : Div (ℂ ⧸ L)) : ℂ ⧸ L → ℤ) x • x
      = ∑ x ∈ Zin, n x • L.mkQ x := hkey.symm
    _ = L.mkQ (∑ x ∈ Zin, (n x : ℂ) * x) := hqsum.symm
    _ = 0 := hq0

/-- **Full closure of the challenge for `T_L` from ZERO named
hypotheses**: the C3 input on the complex torus, unconditionally. -/
theorem nonempty_C3FullInputExtSymp_complexTorus_unconditional
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L)) :
    Nonempty (JacobianChallenge.C3FullInputExtSymp (ℂ ⧸ L)) :=
  nonempty_C3FullInputExtSymp_complexTorus_of_TLDivSum L h
    (tlDivSumHypothesis_holds L)

end ComplexTorus

end JacobianChallenge

end
