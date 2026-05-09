/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ResidueTheorem
import JacobianChallenge.Manifold.MeromorphicExtension
import JacobianChallenge.Manifold.MeromorphicDivisor
import JacobianChallenge.Manifold.PrincipalDivisorDegreeZero
import JacobianChallenge.Manifold.ResidueViaTopologicalDegree
import JacobianChallenge.Divisor

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Discharge of the residue-theorem ingredients R1–R5 from in-tree material

This file is the "Residue chip": for each of the five named owed
statements R1–R5 in `Manifold/ResidueTheorem.lean`, we either ship an
unconditional discharge built out of in-tree material, or — for the one
ingredient (R4) that requires a not-yet-in-mathlib classical input — we
record the precise residual and ship a clean conditional composer for
the headline residue theorem.

The four pieces that compose unconditionally at this pin are:

* **R1 — pole-extension to `RiemannSphere`.** Proved by routing through
  `MeromorphicNonzero.toRiemannSphere`
  (`Manifold/MeromorphicExtension.lean`) plus the unconditional
  `toRiemannSphere_contMDiff` smoothness theorem already in main. The
  three Prop-level fields of `R1_poleExtension_statement` (existence,
  iff for `∞`, equality for non-poles) translate into the three known
  `toRiemannSphere_*` lemmas after exchanging the
  `untop₀`-flavoured `WithTop ℤ` quantifiers in R1's statement for the
  `WithTop ℤ`-valued ones used in `toRiemannSphere_apply_*`. Both are
  the same condition under `MeromorphicNonzero.nonvanishing_germ` (which
  rules out `order = ⊤`), so the `untop₀ < 0 ↔ order < 0` and
  `untop₀ ≥ 0 ↔ order ≥ 0` rewrites are exact.

* **R2 — zero & pole fibres are finite.** Direct application of
  `JacobianChallenge.MMeromorphicOn.zeros_finite` and `poles_finite`
  (`Manifold/MeromorphicDivisor.lean`) to `f.toFun`, using
  `f.meromorphic` and `f.nonvanishing_germ`. The `untop₀` form of R2's
  statement matches the `WithTop ℤ` form of those lemmas under
  `f.nonvanishing_germ` (which rules out `order = ⊤`).

* **R3 — local multiplicity ≥ 1.** Pure integer arithmetic: if
  `(order x).untop₀ ≠ 0` then this `untop₀` is a nonzero integer and
  hence has `natAbs ≥ 1`.

* **R5 — principal divisor has degree zero — given R4.** Composer
  routing from R4 through the in-tree decomposition lemma
  `signedMult_eq_zeroCount_sub_poleCount`
  (`Manifold/ResidueViaTopologicalDegree.lean`) and the fact that the
  zero / pole sums in R4's statement are exactly `zeroCount f` and
  `-poleCount f` (after a partition-of-support lemma).

The remaining ingredient — **R4 (∑ over zeros + ∑ over poles = 0)** —
is the *single* analytic input whose discharge would require
identifying the manifold ramification index `manifoldRamificationIndex
f.toRiemannSphere` with the meromorphic order `(mmeromorphicOrderAt I
f.toFun x).untop₀.natAbs` at every order-nonzero point, and then
applying `ramificationSumEqualsDegree_holds_unconditional` to
`f.toRiemannSphere` at the two values `0` and `∞`. The named bridge
`manifoldRamificationIndex_eq_localKFoldMultiplicityChartPullback` is
in main (`Manifold/RamificationIndexEqLocalKFold.lean`) but the further
identification with `(mmeromorphicOrderAt I f.toFun).untop₀.natAbs`
(plus the sign bookkeeping at poles via `chartS`) is the residual.

We therefore ship:

* **R1 / R2 / R3:** unconditional discharges, named
  `R1_poleExtension_statement_holds`,
  `R2_fibres_finite_statement_holds`,
  `R3_localMultiplicity_statement_holds`.
* **R5 from R4:** a real composer
  `R5_principal_degree_zero_statement_of_R4` that takes only R4 and
  returns R5.
* **Residue theorem from R4:** the headline conditional theorem
  `residue_theorem_of_R4` ships `(principalDivisorMap f).degree = 0`
  for every `f` from R4 alone (R1 / R2 / R3 already discharged).

No `sorry`, no `axiom`. -/

@[expose] public section

noncomputable section

open scoped Manifold Topology ContDiff BigOperators
open Filter Set

namespace JacobianChallenge

namespace ResidueTheoremFromRsum

universe u

variable (X : Type u)
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Bridging lemmas: `untop₀`-form versus `WithTop ℤ` form -/

/-- Under the hypothesis `order ≠ ⊤` (which is `f.nonvanishing_germ` in
the `MeromorphicNonzero` setting), the `untop₀ < 0` form and the
`(order : WithTop ℤ) < 0` form coincide. -/
lemma untop₀_lt_zero_iff_lt_zero {n : WithTop ℤ} (hn : n ≠ ⊤) :
    n.untop₀ < (0 : ℤ) ↔ n < (0 : WithTop ℤ) := by
  -- `n ≠ ⊤` lets us replace `n` by `(n.untop hn : ℤ)`. Cast nicely.
  classical
  set k : ℤ := n.untop hn with hk_def
  have hn_eq : n = (k : WithTop ℤ) := by
    show n = ((n.untop hn : ℤ) : WithTop ℤ)
    exact (WithTop.coe_untop n hn).symm
  -- `n.untop₀ = k` since `n.untop₀ = (n.untop hn) = k` here.
  have h_untop₀ : n.untop₀ = k := by
    rw [hn_eq]; rfl
  rw [h_untop₀, hn_eq]
  exact_mod_cast (Iff.refl (k < 0))

/-- Under `order ≠ ⊤`, the `untop₀ ≥ 0` form and the
`(order : WithTop ℤ) ≥ 0` form coincide. -/
lemma untop₀_nonneg_iff_nonneg {n : WithTop ℤ} (hn : n ≠ ⊤) :
    (0 : ℤ) ≤ n.untop₀ ↔ (0 : WithTop ℤ) ≤ n := by
  classical
  set k : ℤ := n.untop hn with hk_def
  have hn_eq : n = (k : WithTop ℤ) := by
    show n = ((n.untop hn : ℤ) : WithTop ℤ)
    exact (WithTop.coe_untop n hn).symm
  have h_untop₀ : n.untop₀ = k := by
    rw [hn_eq]; rfl
  rw [h_untop₀, hn_eq]
  exact_mod_cast (Iff.refl ((0 : ℤ) ≤ k))

/-- Under `order ≠ ⊤`, the `untop₀ > 0` form and the
`(order : WithTop ℤ) > 0` form coincide. -/
lemma untop₀_pos_iff_pos {n : WithTop ℤ} (hn : n ≠ ⊤) :
    (0 : ℤ) < n.untop₀ ↔ (0 : WithTop ℤ) < n := by
  classical
  set k : ℤ := n.untop hn with hk_def
  have hn_eq : n = (k : WithTop ℤ) := by
    show n = ((n.untop hn : ℤ) : WithTop ℤ)
    exact (WithTop.coe_untop n hn).symm
  have h_untop₀ : n.untop₀ = k := by
    rw [hn_eq]; rfl
  rw [h_untop₀, hn_eq]
  exact_mod_cast (Iff.refl ((0 : ℤ) < k))

/-! ## R1 — pole-extension to `RiemannSphere` -/

/-- **Discharge of `R1_poleExtension_statement X`.**

Builds the canonical extension `f.toRiemannSphere : X → RiemannSphere`,
inherits its smoothness from
`MeromorphicNonzero.toRiemannSphere_contMDiff`, and verifies the two
branch-defining equations using `toRiemannSphere_apply_of_neg`,
`toRiemannSphere_apply_of_nonneg`, and the
`untop₀`-vs-`WithTop ℤ` bridges above (under
`f.nonvanishing_germ`). -/
theorem R1_poleExtension_statement_holds :
    JacobianChallenge.ResidueTheorem.R1_poleExtension_statement X := by
  intro f
  refine ⟨f.toRiemannSphere, f.toRiemannSphere_contMDiff, ?_, ?_⟩
  · -- `f.toRiemannSphere x = ∞ ↔ (order x).untop₀ < 0`.
    intro x
    have hne : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x ≠ ⊤ :=
      f.nonvanishing_germ x
    rw [JacobianChallenge.MeromorphicNonzero.toRiemannSphere_eq_infty_iff_neg]
    exact (untop₀_lt_zero_iff_lt_zero hne).symm
  · -- `(order x).untop₀ ≥ 0 → f.toRiemannSphere x = some (f.toFun x)`.
    intro x hx
    have hne : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x ≠ ⊤ :=
      f.nonvanishing_germ x
    have h_order_nonneg :
        (0 : WithTop ℤ) ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x :=
      (untop₀_nonneg_iff_nonneg hne).mp hx
    exact JacobianChallenge.MeromorphicNonzero.toRiemannSphere_apply_of_nonneg
      f h_order_nonneg

/-! ## R2 — zero and pole fibres are finite -/

/-- **Discharge of `R2_fibres_finite_statement X`.**

Direct application of `JacobianChallenge.MMeromorphicOn.zeros_finite`
and `JacobianChallenge.MMeromorphicOn.poles_finite` to `f.toFun`,
using `f.meromorphic` and `f.nonvanishing_germ`. The statement uses
the `untop₀ > 0` and `untop₀ < 0` forms; we prove finiteness via the
`WithTop ℤ`-form lemmas in `MeromorphicDivisor.lean` and route the
two equivalences via `untop₀_pos_iff_pos` and
`untop₀_lt_zero_iff_lt_zero`. -/
theorem R2_fibres_finite_statement_holds :
    JacobianChallenge.ResidueTheorem.R2_fibres_finite_statement X := by
  intro f
  refine ⟨?_, ?_⟩
  · -- Zeros: `{x | (order x).untop₀ > 0}.Finite`.
    have h_zeros_WithTop :
        {x : X | (0 : WithTop ℤ) <
            mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x}.Finite :=
      JacobianChallenge.MMeromorphicOn.zeros_finite (X := X)
        (𝓘(ℂ, ℂ)) f.toFun f.meromorphic f.nonvanishing_germ
    apply h_zeros_WithTop.subset
    intro x hx
    -- `hx : (0 : ℤ) < (order x).untop₀`. Translate to `WithTop ℤ`-form using `untop₀_pos_iff_pos`.
    simp only [Set.mem_setOf_eq] at hx ⊢
    exact (untop₀_pos_iff_pos (f.nonvanishing_germ x)).mp hx
  · -- Poles: `{x | (order x).untop₀ < 0}.Finite`.
    have h_poles_WithTop :
        {x : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x <
            (0 : WithTop ℤ)}.Finite :=
      JacobianChallenge.MMeromorphicOn.poles_finite (X := X)
        (𝓘(ℂ, ℂ)) f.toFun f.meromorphic f.nonvanishing_germ
    apply h_poles_WithTop.subset
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    exact (untop₀_lt_zero_iff_lt_zero (f.nonvanishing_germ x)).mp hx

/-! ## R3 — local multiplicity ≥ 1 at order-nonzero points -/

/-- **Discharge of `R3_localMultiplicity_statement X`.**

Pure integer arithmetic: at any `x` with `(order x).untop₀ ≠ 0`,
the integer `(order x).untop₀` is nonzero, hence its `natAbs` is at
least `1`. -/
theorem R3_localMultiplicity_statement_holds :
    JacobianChallenge.ResidueTheorem.R3_localMultiplicity_statement X := by
  intro f x hx
  -- `hx : (order x).untop₀ ≠ 0`. So the integer is nonzero ⇒ `natAbs ≥ 1`.
  exact Int.one_le_iff_ne_zero.mpr fun h => hx (Int.natAbs_eq_zero.mp h)

/-! ## R5 from R4: principal divisor has degree zero -/

/-- **Composer: R5 from R4 alone (R1, R2, R3 already discharged).**

Given the named hypothesis `R4_fibreSum_balance_statement X`, every
non-zero meromorphic function on `X` has principal-divisor degree zero.

Proof: For each `f`, R4 produces an integer balance equation between
the sum of `(order x).untop₀` over the zeros and the sum over the
poles. The principal divisor's `degree` is the sum of `orderFun` over
its (finite) `supportFinset`, and `orderFun = (order x).untop₀`. The
`supportFinset` decomposes (under `f.nonvanishing_germ`) as the
disjoint union of the zero set (R2's `hZ`) and the pole set (R2's
`hP`); the `orderFun = 0` points outside contribute nothing. Hence

  `(principalDivisorMap f).degree
     = ∑ x ∈ hZ.toFinset, orderFun + ∑ x ∈ hP.toFinset, orderFun`
     `= 0`  (by R4).

The bookkeeping is: `Finset.sum_of_injOn`-style decomposition
through `Set.Finite.toFinset` plus the trivial cancellation that
support points have `orderFun ≠ 0`. -/
theorem R5_principal_degree_zero_statement_of_R4
    (hR4 : JacobianChallenge.ResidueTheorem.R4_fibreSum_balance_statement X) :
    JacobianChallenge.ResidueTheorem.R5_principal_degree_zero_statement X := by
  intro f
  classical
  -- Extract R2's two finiteness witnesses for this `f`.
  obtain ⟨hZ, hP⟩ := R2_fibres_finite_statement_holds X f
  -- R4 specialised to `f` and the two finiteness witnesses.
  have hR4f := hR4 f hZ hP
  -- Now we just need:
  --   `(principalDivisorMap f).degree
  --      = ∑ x ∈ hZ.toFinset, (order x).untop₀
  --        + ∑ x ∈ hP.toFinset, (order x).untop₀`.
  -- Use the in-tree `signedMult_eq_zeroCount_sub_poleCount` decomposition
  -- and recognise the two summands as `zeroCount f` and `-poleCount f`.
  rw [JacobianChallenge.ResidueViaTopologicalDegree.signedMult_eq_zeroCount_sub_poleCount f]
  -- Goal: `zeroCount f - poleCount f = 0`. Equivalently `zeroCount f = poleCount f`.
  -- We show both `zeroCount f = ∑ over hZ, ord` and
  -- `poleCount f = - ∑ over hP, ord`; then `R4` says their sum is `0`,
  -- which rearranges to `zeroCount f - poleCount f = 0`.
  -- First, compute `zeroCount f` as a sum over `hZ.toFinset`.
  have h_zeroCount_eq :
      JacobianChallenge.ResidueViaTopologicalDegree.zeroCount f
        = ∑ x ∈ hZ.toFinset,
            (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ := by
    -- `zeroCount f` is a sum over `supportFinset.filter (0 < principalDivisorMap f x)`.
    -- We'll show that this filter Finset equals `hZ.toFinset` as Finsets.
    unfold JacobianChallenge.ResidueViaTopologicalDegree.zeroCount
    -- The summand `principalDivisorMap f x = orderFun = (order x).untop₀`.
    -- Show the filter Finset equals `hZ.toFinset`.
    have hfilt :
        ((principalDivisorMap f).supportFinset).filter
            (fun x => (0 : ℤ) < (principalDivisorMap f : X → ℤ) x)
          = hZ.toFinset := by
      ext x
      simp only [Finset.mem_filter,
        JacobianChallenge.Div.mem_supportFinset,
        Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      -- Goal: `(D x ≠ 0) ∧ (0 < D x) ↔ 0 < (order x).untop₀`.
      -- The summand `D x = orderFun = (order x).untop₀` (rfl from `principalDivisorMap_apply`).
      constructor
      · intro hx
        -- `hx.2 : 0 < D x = (order x).untop₀`.
        have h2 : (0 : ℤ) < (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ := by
          have := hx.2
          show (0 : ℤ) < (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀
          simpa using this
        exact h2
      · intro hx
        -- Need `(D x ≠ 0) ∧ (0 < D x)`.
        have hgt : (0 : ℤ) < (principalDivisorMap f : X → ℤ) x := by
          show (0 : ℤ) < (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀
          exact hx
        refine ⟨?_, hgt⟩
        -- `D x ≠ 0` follows from `0 < D x`.
        exact ne_of_gt hgt
    rw [hfilt]
    refine Finset.sum_congr rfl ?_
    intro x _
    -- Summand: `(principalDivisorMap f : X → ℤ) x = (order x).untop₀`.
    rfl
  -- Now compute `poleCount f` as `- ∑ over hP, ord`.
  have h_poleCount_eq :
      JacobianChallenge.ResidueViaTopologicalDegree.poleCount f
        = - ∑ x ∈ hP.toFinset,
            (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ := by
    unfold JacobianChallenge.ResidueViaTopologicalDegree.poleCount
    -- `poleCount f` is `∑ over supportFinset.filter (¬ 0 < D x), -D x`.
    -- The filter Finset equals `hP.toFinset`.
    have hfilt :
        ((principalDivisorMap f).supportFinset).filter
            (fun x => ¬ (0 : ℤ) < (principalDivisorMap f : X → ℤ) x)
          = hP.toFinset := by
      ext x
      simp only [Finset.mem_filter,
        JacobianChallenge.Div.mem_supportFinset,
        Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hne, hnpos⟩
        -- `hne : D x ≠ 0`, `hnpos : ¬ 0 < D x`. So `D x < 0`, i.e. order.untop₀ < 0.
        have h_D_eq : (principalDivisorMap f : X → ℤ) x
            = (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ := rfl
        have hne' : (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ ≠ 0 := by
          rw [h_D_eq] at hne; exact hne
        have hnpos' : ¬ (0 : ℤ) <
            (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ := by
          rw [h_D_eq] at hnpos; exact hnpos
        -- `not 0 < a ∧ a ≠ 0 ↔ a < 0` for integers.
        exact lt_of_le_of_ne (not_lt.mp hnpos') hne'
      · intro hlt
        -- `hlt : (order x).untop₀ < 0`. Both fields hold.
        have h_D_eq : (principalDivisorMap f : X → ℤ) x
            = (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀ := rfl
        refine ⟨?_, ?_⟩
        · -- D x ≠ 0.
          rw [h_D_eq]; exact ne_of_lt hlt
        · -- ¬ 0 < D x.
          rw [h_D_eq]; exact not_lt.mpr (le_of_lt hlt)
    rw [hfilt]
    -- ∑ x ∈ hP.toFinset, -((D x : ℤ)) = -∑ x ∈ hP.toFinset, (order x).untop₀.
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro x _
    -- summand `- (D x) = - (order x).untop₀`.
    rfl
  rw [h_zeroCount_eq, h_poleCount_eq]
  -- Goal:
  --   `(∑ over hZ, ord) - ( - ∑ over hP, ord) = 0`,
  -- i.e. `(∑ over hZ, ord) + (∑ over hP, ord) = 0`, which is exactly `hR4f`.
  have : (∑ x ∈ hZ.toFinset,
            (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀)
          - (- ∑ x ∈ hP.toFinset,
                (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀)
        = (∑ x ∈ hZ.toFinset,
              (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀)
          + (∑ x ∈ hP.toFinset,
                (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x).untop₀) := by
    ring
  rw [this]
  exact hR4f

/-! ## Headline conditional residue theorem from R4 -/

/-- **Headline theorem from R4 alone.** For every non-zero meromorphic
function `f : MeromorphicNonzero X` and every witness of R4
(`R4_fibreSum_balance_statement X`), the principal divisor `(f)` has
degree zero. R1, R2, R3 are discharged unconditionally above. -/
theorem residue_theorem_of_R4
    (hR4 : JacobianChallenge.ResidueTheorem.R4_fibreSum_balance_statement X)
    (f : JacobianChallenge.MeromorphicNonzero X) :
    (JacobianChallenge.principalDivisorMap f).degree = 0 :=
  R5_principal_degree_zero_statement_of_R4 X hR4 f

/-! ## Routing R5 ↔ `JacobianChallenge.ResidueTheorem` (the other named bundle)

`R5_principal_degree_zero_statement X` and
`JacobianChallenge.ResidueTheorem X` are the same `Prop` definitionally
(both unfold to `∀ f, (principalDivisorMap f).degree = 0`). The
in-main lemma `R5_iff_residueTheorem`
(`Manifold/PrincipalDivisorDegreeZero.lean`) is the identity-Iff
between them. We re-export it here so the chip's reader has every
named target in one place. -/

/-- The named `R5` statement is the same as `JacobianChallenge.ResidueTheorem X`. -/
lemma R5_iff_ResidueTheorem :
    JacobianChallenge.ResidueTheorem.R5_principal_degree_zero_statement X
      ↔ JacobianChallenge.ResidueTheorem X :=
  JacobianChallenge.R5_iff_residueTheorem (X := X)

/-- The named `R5` and the topological-degree-fibre-balance bundle (per
`f`, with single named gap `zeroCount f = poleCount f`) are equivalent
*as global statements*, by the in-main proven equivalence
`R5_iff_zeroCount_eq_poleCount`. -/
lemma R5_iff_forall_zeroCount_eq_poleCount :
    JacobianChallenge.ResidueTheorem.R5_principal_degree_zero_statement X
      ↔ ∀ f : JacobianChallenge.MeromorphicNonzero X,
          JacobianChallenge.ResidueViaTopologicalDegree.zeroCount f
            = JacobianChallenge.ResidueViaTopologicalDegree.poleCount f :=
  JacobianChallenge.R5_iff_zeroCount_eq_poleCount (X := X)

end ResidueTheoremFromRsum

end JacobianChallenge

end

end
